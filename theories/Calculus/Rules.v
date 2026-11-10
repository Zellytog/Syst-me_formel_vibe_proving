(** * Systèmes de calcul engendrés par des règles

    Une règle est un couple de termes de même sorte dans un même contexte de
    métavariables. Une famille de règles (indexée par un type quelconque,
    pour couvrir les schémas comme β à toutes les sortes) engendre le plus
    petit système de calcul qui la contient : la clôture par équivalence et
    par substitution. *)

From Stdlib Require Import List.
Import ListNotations.
From SF.Syntax Require Import Spec Terms Renaming Traversal Eta Composition Vectors.
From SF.Calculus Require Import System.

Record rule {Srt : Type} (Sym : spec Srt -> Type) := {
  r_ctx : ctx Srt;
  r_sort : Srt;
  r_lhs : Terms.tm Sym r_ctx r_sort;
  r_rhs : Terms.tm Sym r_ctx r_sort
}.

Arguments r_ctx {Srt Sym} r.
Arguments r_sort {Srt Sym} r.
Arguments r_lhs {Srt Sym} r.
Arguments r_rhs {Srt Sym} r.

Section Generated.

Context {Srt : Type} {Sym : spec Srt -> Type}.
Context {I : Type} (rules : I -> rule Sym).

Local Notation tm := (Terms.tm Sym).
Local Notation args := (Terms.args Sym).

Inductive gconv : forall Γ s, tm Γ s -> tm Γ s -> Prop :=
| g_rule (i : I) : gconv _ _ (r_lhs (rules i)) (r_rhs (rules i))
| g_refl Γ s (t : tm Γ s) : gconv Γ s t t
| g_sym Γ s (t u : tm Γ s) : gconv Γ s t u -> gconv Γ s u t
| g_trans Γ s (t u w : tm Γ s) : gconv Γ s t u -> gconv Γ s u w -> gconv Γ s t w
| g_subst Γ Δ s (t t' : tm Γ s) (v v' : args Δ Γ) :
    gconv Γ s t t' -> gargs Δ Γ v v' -> gconv Δ s (vsubst t v) (vsubst t' v')
with gargs : forall Γ Θ, args Γ Θ -> args Γ Θ -> Prop :=
| ga_nil Γ : gargs Γ [] anil anil
| ga_cons Γ σ Θ (u u' : Terms.tms Sym Γ σ) (a a' : args Γ Θ) :
    gconv _ _ u u' -> gargs Γ Θ a a' -> gargs Γ (σ :: Θ) (acons u a) (acons u' a').

Scheme gconv_ind' := Induction for gconv Sort Prop
  with gargs_ind' := Induction for gargs Sort Prop.
Combined Scheme gconv_gargs_ind from gconv_ind', gargs_ind'.

Lemma gargs_arel Γ Θ (a a' : args Γ Θ) : gargs Γ Θ a a' <-> arel gconv a a'.
Proof.
  split.
  - induction 1; cbn; auto.
  - revert a a'; induction Θ as [|σ Θ IH]; intros a a'.
    + rewrite (args_nil a), (args_nil a'); intros _; constructor.
    + rewrite (args_eta a), (args_eta a'); intros [H1 H2]; constructor; auto.
Qed.

(** Le système engendré. *)
Definition generated : system Sym := {|
  conv := gconv;
  conv_refl := g_refl;
  conv_sym := g_sym;
  conv_trans := g_trans;
  conv_subst := fun Γ Δ s t t' v v' H Hv => g_subst Γ Δ s t t' v v' H (proj2 (gargs_arel _ _ _ _) Hv)
|}.

Lemma generated_rule (i : I) : conv generated (r_lhs (rules i)) (r_rhs (rules i)).
Proof. apply g_rule. Qed.

(** Instance d'une règle par un vecteur. *)
Lemma generated_instance (i : I) {Δ} (v : vec Sym (r_ctx (rules i)) Δ) :
  conv generated (vsubst (r_lhs (rules i)) v) (vsubst (r_rhs (rules i)) v).
Proof. apply (conv_subst generated); [apply g_rule|apply arel_refl]. Qed.

(** C'est le plus petit système contenant les règles. *)
Theorem generated_least (S : system Sym) :
  (forall i, conv S (r_lhs (rules i)) (r_rhs (rules i))) ->
  forall Γ s (t u : tm Γ s), conv generated t u -> conv S t u.
Proof.
  intros Hr.
  enough (H : (forall Γ s t u, gconv Γ s t u -> conv S t u) /\
              (forall Γ Θ a a', gargs Γ Θ a a' -> arel (conv S) a a'))
    by (exact (proj1 H)).
  apply gconv_gargs_ind; intros; cbn.
  - apply Hr.
  - apply conv_refl.
  - apply conv_sym; assumption.
  - eapply conv_trans; eassumption.
  - apply conv_subst; assumption.
  - exact Logic.I.
  - split; assumption.
Qed.

End Generated.

Arguments generated {Srt Sym I} rules.

(** ** Combinaison de familles de règles de calcul *)

Section Combine.

Context {Srt : Type} {Sym : spec Srt -> Type}.

Definition crsum {I J} (R1 : I -> rule Sym) (R2 : J -> rule Sym) : I + J -> rule Sym :=
  fun k => match k with inl i => R1 i | inr j => R2 j end.

(** [R] contient la famille [R']. *)
Class CIncludes {I J} (R : I -> rule Sym) (R' : J -> rule Sym) := {
  cinc : J -> I;
  cinc_eq : forall j, R (cinc j) = R' j
}.

#[export] Instance CIncludes_refl {I} (R : I -> rule Sym) : CIncludes R R :=
  {| cinc := fun j => j; cinc_eq := fun j => eq_refl |}.

#[export] Instance CIncludes_l {I J K} (R1 : I -> rule Sym) (R2 : K -> rule Sym)
  (R' : J -> rule Sym) `{CIncludes I J R1 R'} : CIncludes (crsum R1 R2) R' :=
  {| cinc := fun j => inl (cinc j); cinc_eq := fun j => cinc_eq j |}.

#[export] Instance CIncludes_r {I J K} (R1 : I -> rule Sym) (R2 : K -> rule Sym)
  (R' : J -> rule Sym) `{CIncludes K J R2 R'} : CIncludes (crsum R1 R2) R' :=
  {| cinc := fun j => inr (cinc j); cinc_eq := fun j => cinc_eq j |}.

(** Instance d'une règle donnée par une égalité [R i = r]. *)
Lemma generated_rule_eq {I} (R : I -> rule Sym) (i : I) (r : rule Sym) {Δ}
  (v : vec Sym (r_ctx r) Δ) :
  R i = r -> conv (generated R) (vsubst (r_lhs r) v) (vsubst (r_rhs r) v).
Proof. intros <-; apply generated_instance. Qed.

(** Instance d'une règle d'une famille incluse. *)
Lemma generated_included {I J} (R : I -> rule Sym) (R' : J -> rule Sym) `{CIncludes I J R R'}
  (j : J) {Δ} (v : vec Sym (r_ctx (R' j)) Δ) :
  conv (generated R) (vsubst (r_lhs (R' j)) v) (vsubst (r_rhs (R' j)) v).
Proof. apply (generated_rule_eq R (cinc j)), cinc_eq. Qed.

End Combine.

Arguments crsum {Srt Sym I J} R1 R2 k.
Arguments CIncludes {Srt Sym I J} R R'.
