(** * Systèmes de calcul

    Un système de calcul sur une signature est une relation [~] entre termes
    de même sorte dans le même contexte, qui est :
    - une relation d'équivalence ;
    - stable par substitution, au sens fort : si [t ~ t'] et si les vecteurs
      [v] et [v'] sont reliés composante par composante, alors
      [t[v] ~ t'[v']].

    Cette seconde condition contient à la fois la stabilité par
    substitution (avec [v = v']) et la congruence vis-à-vis des symboles et
    des variables ([conv_tsym], [conv_tvar] ci-dessous), qui en découlent.
    La décidabilité est une propriété à part ([decidable]). *)

From Stdlib Require Import List.
Import ListNotations.
From SF.Syntax Require Import Spec Terms Renaming Traversal Eta Composition Vectors.

Section Rel.

Context {Srt : Type} {Sym : spec Srt -> Type}.
Implicit Types (Λ Θ Γ Δ Ξ D : ctx Srt) (σ τ ρ : spec Srt).

Local Notation tm := (Terms.tm Sym).
Local Notation args := (Terms.args Sym).
Local Notation tms := (Terms.tms Sym).

(** Une relation entre termes de même sorte, dans le même contexte. *)
Definition trel : Type := forall Γ s, tm Γ s -> tm Γ s -> Prop.

(** Son extension aux listes d'arguments (donc aux vecteurs), composante par
    composante, chaque composante sous ses propres lieurs. *)
Fixpoint arel (R : trel) Γ Θ : args Γ Θ -> args Γ Θ -> Prop :=
  match Θ return args Γ Θ -> args Γ Θ -> Prop with
  | [] => fun _ _ => True
  | σ :: Θ' => fun a a' => R _ _ (ahd a) (ahd a') /\ arel R Γ Θ' (atl a) (atl a')
  end.

Lemma arel_aget (R : trel) Γ Θ (a a' : args Γ Θ) :
  arel R Γ Θ a a' <-> forall σ (z : var Θ σ), R _ _ (aget z a) (aget z a').
Proof.
  induction Θ as [|τ Θ IH]; cbn.
  - split; [intros _ σ z; destruct (var_nil z)|trivial].
  - split.
    + intros [H1 H2]. refine (var_inv _ _ _); [exact H1|].
      intros σ y; apply (proj1 (IH (atl a) (atl a')) H2).
    + intros H; split; [exact (H τ vz)|].
      apply IH; intros σ z; exact (H σ (vs z)).
Qed.

End Rel.

Arguments trel {Srt} Sym.
Arguments arel {Srt Sym} R {Γ Θ} a a'.

(** ** La notion de système de calcul *)

Record system {Srt : Type} (Sym : spec Srt -> Type) := {
  conv : trel Sym;
  conv_refl : forall Γ s (t : Terms.tm Sym Γ s), conv Γ s t t;
  conv_sym : forall Γ s (t u : Terms.tm Sym Γ s), conv Γ s t u -> conv Γ s u t;
  conv_trans : forall Γ s (t u w : Terms.tm Sym Γ s),
      conv Γ s t u -> conv Γ s u w -> conv Γ s t w;
  conv_subst : forall Γ Δ s (t t' : Terms.tm Sym Γ s) (v v' : vec Sym Γ Δ),
      conv Γ s t t' -> arel conv v v' -> conv Δ s (vsubst t v) (vsubst t' v')
}.

Arguments conv {Srt Sym} s [Γ s0] t u : rename.
Arguments conv_refl {Srt Sym} s {Γ s0} t : rename.
Arguments conv_sym {Srt Sym} s {Γ s0 t u} _ : rename.
Arguments conv_trans {Srt Sym} s {Γ s0 t u w} _ _ : rename.
Arguments conv_subst {Srt Sym} s {Γ Δ s0 t t' v v'} _ _ : rename.

(** Un système est décidable si sa relation l'est. *)
Definition decidable {Srt : Type} {Sym : spec Srt -> Type} (S : system Sym) : Type :=
  forall Γ s (t u : Terms.tm Sym Γ s), {conv S t u} + {~ conv S t u}.

(** ** Propriétés dérivées *)

Section Derived.

Context {Srt : Type} {Sym : spec Srt -> Type} (S : system Sym).
Implicit Types (Λ Θ Γ Δ Ξ D : ctx Srt) (σ τ ρ : spec Srt).

Local Notation tm := (Terms.tm Sym).
Local Notation args := (Terms.args Sym).
Local Notation tms := (Terms.tms Sym).
Local Notation "t ~ u" := (conv S t u) (at level 70).
Local Notation "a ≃ b" := (arel (conv S) a b) (at level 70).

Lemma arel_refl {Γ Θ} (a : args Γ Θ) : a ≃ a.
Proof. apply arel_aget; intros; apply conv_refl. Qed.

Lemma arel_sym {Γ Θ} (a b : args Γ Θ) : a ≃ b -> b ≃ a.
Proof. rewrite !arel_aget; intros H σ z; apply conv_sym, H. Qed.

Lemma arel_trans {Γ Θ} (a b c : args Γ Θ) : a ≃ b -> b ≃ c -> a ≃ c.
Proof. rewrite !arel_aget; intros H1 H2 σ z; eapply conv_trans; [apply H1|apply H2]. Qed.

Lemma arel_eq {Γ Θ} (a b : args Γ Θ) : a = b -> a ≃ b.
Proof. intros ->; apply arel_refl. Qed.

(** Stabilité par renommage : un renommage est une substitution. *)
Lemma conv_ren {Γ s} (t t' : tm Γ s) {Δ} (ρ : ren Γ Δ) :
  t ~ t' -> ren_tm t ρ ~ ren_tm t' ρ.
Proof. intros H; rewrite !ren_as_vsubst; apply conv_subst; [exact H|apply arel_refl]. Qed.

Lemma conv_ren_tms {Γ σ} (u u' : tms Γ σ) {Δ} (ρ : ren Γ Δ) :
  u ~ u' -> ren_tms u ρ ~ ren_tms u' ρ.
Proof. apply conv_ren. Qed.

Lemma arel_vcat Θ {Γ Ξ} (a a' : args Ξ Θ) (b b' : args Ξ Γ) :
  a ≃ a' -> b ≃ b' -> vcat Θ a b ≃ vcat Θ a' b'.
Proof.
  rewrite !arel_aget; intros Ha Hb σ x.
  vcase x; rewrite ?aget_vcat_l, ?aget_vcat_r; [apply Ha|apply Hb].
Qed.

Lemma arel_vren {Γ Δ Ξ} (v v' : vec Sym Γ Δ) (ξ : ren Δ Ξ) :
  v ≃ v' -> vren v ξ ≃ vren v' ξ.
Proof.
  rewrite !arel_aget; intros H σ x; unfold vren; rewrite !aget_vmap.
  apply conv_ren_tms, H.
Qed.

Lemma arel_vup D {Γ Δ} (v v' : vec Sym Γ Δ) : v ≃ v' -> vup D v ≃ vup D v'.
Proof. intros H; unfold vup; apply arel_vcat; [apply arel_refl|apply arel_vren, H]. Qed.

Lemma conv_vsubst {Γ Δ s} (t t' : tm Γ s) (v v' : vec Sym Γ Δ) :
  t ~ t' -> v ≃ v' -> vsubst t v ~ vsubst t' v'.
Proof. apply conv_subst. Qed.

Lemma conv_vsubst_tms {Γ Δ σ} (u u' : tms Γ σ) (v v' : vec Sym Γ Δ) :
  u ~ u' -> v ≃ v' -> vsubst_tms u v ~ vsubst_tms u' v'.
Proof.
  intros Hu Hv; rewrite !vsubst_tms_vup; apply conv_subst; [exact Hu|apply arel_vup, Hv].
Qed.

Lemma arel_vsubst_args {Γ Δ Θ} (a a' : args Γ Θ) (v v' : vec Sym Γ Δ) :
  a ≃ a' -> v ≃ v' -> vsubst_args a v ≃ vsubst_args a' v'.
Proof.
  rewrite (arel_aget _ _ _ a a'); intros Ha Hv; apply arel_aget; intros σ z.
  unfold vsubst_args; rewrite !aget_subst_args.
  apply (conv_vsubst_tms _ _ v v'); [apply Ha|exact Hv].
Qed.

(** La composition des vecteurs respecte [≃]. *)
Lemma arel_vcomp {Γ Δ Ξ} (f f' : vec Sym Γ Δ) (g g' : vec Sym Δ Ξ) :
  f ≃ f' -> g ≃ g' -> vcomp f g ≃ vcomp f' g'.
Proof.
  rewrite (arel_aget _ _ _ f f'); intros Hf Hg; apply arel_aget; intros σ x.
  rewrite !aget_vcomp; apply conv_vsubst_tms; [apply Hf|exact Hg].
Qed.

(** L'application héréditaire respecte [~]. *)
Lemma conv_happ σ {Ξ} (u u' : tms Ξ σ) (a a' : args Ξ (dom σ)) :
  u ~ u' -> a ≃ a' -> happ σ u a ~ happ σ u' a'.
Proof.
  intros Hu Ha; rewrite !happ_vsubst; apply conv_subst; [exact Hu|].
  apply arel_vcat; [exact Ha|apply arel_refl].
Qed.

(** Congruence : variables et symboles. *)
Lemma conv_tvar {Γ σ} (x : var Γ σ) (a a' : args Γ (dom σ)) :
  a ≃ a' -> tvar x a ~ tvar x a'.
Proof.
  intros Ha; rewrite <- !(happ_eta σ x); apply conv_happ; [apply conv_refl|exact Ha].
Qed.

Lemma vsubst_args_vid {Γ Θ} (a : args Γ Θ) : vsubst_args (vid Θ) a = a.
Proof.
  apply args_ext; intros σ z; unfold vsubst_args.
  rewrite aget_subst_args, aget_vid; apply (vsubst_eta z a).
Qed.

Lemma tsym_vsubst {Γ σ} (c : Sym σ) (a : args Γ (dom σ)) :
  tsym c a = vsubst (tsym c (vid (dom σ))) a.
Proof.
  unfold vsubst, subst; simpl. f_equal. symmetry; apply vsubst_args_vid.
Qed.

Lemma conv_tsym {Γ σ} (c : Sym σ) (a a' : args Γ (dom σ)) :
  a ≃ a' -> tsym c a ~ tsym c a'.
Proof.
  intros Ha; rewrite (tsym_vsubst c a), (tsym_vsubst c a').
  apply conv_subst; [apply conv_refl|exact Ha].
Qed.

End Derived.
