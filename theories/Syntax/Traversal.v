(** * Traversées par kits : extensionnalité, renommage, naturalité de [happ] *)

From Stdlib Require Import List.
Import ListNotations.
From SF.Syntax Require Import Spec Terms Renaming.

Section Traversal.

Context {Srt : Type} {Sym : spec Srt -> Type}.
Implicit Types (Λ Θ Γ Δ Ξ Ω D : ctx Srt) (σ τ ρ : spec Srt).

Local Notation tm := (tm Sym).
Local Notation args := (args Sym).
Local Notation tms := (tms Sym).
Local Notation kit := (kit Sym).
Local Notation entry := (entry Sym).
Local Notation applier := (applier Sym).

(** Égalité point par point des kits. *)
Definition keq {Γ Δ} (K K' : kit Γ Δ) : Prop := forall σ x, K σ x = K' σ x.

Lemma kup_ext Λ {Γ Δ} (K K' : kit Γ Δ) : keq K K' -> keq (kup Λ K) (kup Λ K').
Proof. intros H σ x; vcase x; autorewrite with vsimpl; [reflexivity|now rewrite H]. Qed.

Lemma trav_ext_mut :
  (forall Γ s (t : tm Γ s) Δ (K K' : kit Γ Δ), keq K K' -> trav t K = trav t K') /\
  (forall Γ Θ (a : args Γ Θ) Δ (K K' : kit Γ Δ), keq K K' -> trav_args a K = trav_args a K').
Proof.
  apply tm_args_ind; intros; simpl; try reflexivity.
  - rewrite (H Δ K K' H0), (H0 σ v); reflexivity.
  - f_equal; auto.
  - f_equal; auto. apply H. apply kup_ext; assumption.
Qed.

Lemma trav_ext {Γ s} (t : tm Γ s) {Δ} (K K' : kit Γ Δ) : keq K K' -> trav t K = trav t K'.
Proof. apply trav_ext_mut. Qed.

Lemma trav_args_ext {Γ Θ} (a : args Γ Θ) {Δ} (K K' : kit Γ Δ) :
  keq K K' -> trav_args a K = trav_args a K'.
Proof. apply trav_ext_mut. Qed.

(** ** Kits de renommage *)

Definition rkit {Γ Δ} (ρ : ren Γ Δ) : kit Γ Δ := fun σ x => inl (ρ σ x).

Lemma kup_rkit Λ {Γ Δ} (ρ : ren Γ Δ) : keq (kup Λ (rkit ρ)) (rkit (upr Λ ρ)).
Proof. intros σ x; unfold rkit; vcase x; vsimp; reflexivity. Qed.

Lemma trav_rkit_mut :
  (forall Γ s (t : tm Γ s) Δ (ρ : ren Γ Δ), trav t (rkit ρ) = ren_tm t ρ) /\
  (forall Γ Θ (a : args Γ Θ) Δ (ρ : ren Γ Δ), trav_args a (rkit ρ) = ren_args a ρ).
Proof.
  apply tm_args_ind; intros; simpl; try reflexivity.
  - f_equal; auto.
  - f_equal; auto.
  - f_equal; auto. rewrite <- H. apply trav_ext, kup_rkit.
Qed.

Lemma trav_rkit {Γ s} (t : tm Γ s) {Δ} (ρ : ren Γ Δ) : trav t (rkit ρ) = ren_tm t ρ.
Proof. apply trav_rkit_mut. Qed.

Lemma trav_rid {Γ s} (t : tm Γ s) : trav t (rkit rid) = t.
Proof. rewrite trav_rkit; apply ren_id. Qed.

(** ** Renommer avant de traverser *)

Definition rk_comp {Γ Δ Ξ} (ρ : ren Γ Δ) (K : kit Δ Ξ) : kit Γ Ξ := fun σ x => K σ (ρ σ x).

Lemma kup_rk Λ {Γ Δ Ξ} (ρ : ren Γ Δ) (K : kit Δ Ξ) :
  keq (kup Λ (rk_comp ρ K)) (rk_comp (upr Λ ρ) (kup Λ K)).
Proof. intros σ x; unfold rk_comp; vcase x; autorewrite with vsimpl; reflexivity. Qed.

Lemma trav_ren_mut :
  (forall Γ s (t : tm Γ s) Δ Ξ (ρ : ren Γ Δ) (K : kit Δ Ξ),
      trav (ren_tm t ρ) K = trav t (rk_comp ρ K)) /\
  (forall Γ Θ (a : args Γ Θ) Δ Ξ (ρ : ren Γ Δ) (K : kit Δ Ξ),
      trav_args (ren_args a ρ) K = trav_args a (rk_comp ρ K)).
Proof.
  apply tm_args_ind; intros; simpl; try reflexivity.
  - rewrite H; reflexivity.
  - f_equal; auto.
  - f_equal; auto. rewrite H. symmetry; apply trav_ext, kup_rk.
Qed.

Lemma trav_ren {Γ s} (t : tm Γ s) {Δ Ξ} (ρ : ren Γ Δ) (K : kit Δ Ξ) :
  trav (ren_tm t ρ) K = trav t (rk_comp ρ K).
Proof. apply trav_ren_mut. Qed.

Lemma trav_args_ren {Γ Θ} (a : args Γ Θ) {Δ Ξ} (ρ : ren Γ Δ) (K : kit Δ Ξ) :
  trav_args (ren_args a ρ) K = trav_args a (rk_comp ρ K).
Proof. apply trav_ren_mut. Qed.

(** ** Renommer après avoir traversé *)

Definition eren {Δ Ξ σ} (ξ : ren Δ Ξ) (e : entry Δ σ) : entry Ξ σ :=
  match e with
  | inl y => inl (ξ σ y)
  | inr (u, f) => inr (ren_tms u ξ, f)
  end.

Definition kren {Γ Δ Ξ} (K : kit Γ Δ) (ξ : ren Δ Ξ) : kit Γ Ξ := fun σ x => eren ξ (K σ x).

(** Une fonction d'application est naturelle si elle commute aux renommages. *)
Definition natural {σ} (f : applier σ) : Prop :=
  forall Ξ Ξ' (ξ : ren Ξ Ξ') (u : tms Ξ σ) (a : args Ξ (dom σ)),
    ren_tm (f Ξ u a) ξ = f Ξ' (ren_tms u ξ) (ren_args a ξ).

Definition knat {Γ Δ} (K : kit Γ Δ) : Prop :=
  forall σ x u f, K σ x = inr (u, f) -> natural f.

Lemma kup_inr Λ {Γ Δ} (K : kit Γ Δ) σ x u f :
  kup Λ K σ x = inr (u, f) -> exists y u0, K σ y = inr (u0, f).
Proof.
  vcase x; autorewrite with vsimpl; [intros Hc; discriminate Hc|].
  unfold eshift; destruct (K σ z) as [w|[u0 f0]] eqn:Ek; [intros Hc; discriminate Hc|].
  intros [=]; subst; eauto.
Qed.

Lemma knat_kup Λ {Γ Δ} (K : kit Γ Δ) : knat K -> knat (kup Λ K).
Proof. intros H σ x u f E; destruct (kup_inr Λ K σ x u f E) as [y [u0 E0]]; eauto. Qed.

Lemma wk_upr Λ {Γ Δ} (ξ : ren Γ Δ) σ (y : var Γ σ) :
  rcomp ξ (wk Λ) σ y = rcomp (wk Λ) (upr Λ ξ) σ y.
Proof. unfold rcomp, wk; autorewrite with vsimpl; reflexivity. Qed.

Lemma kup_kren Λ {Γ Δ Ξ} (K : kit Γ Δ) (ξ : ren Δ Ξ) :
  keq (kup Λ (kren K ξ)) (kren (kup Λ K) (upr Λ ξ)).
Proof.
  intros σ x; unfold kren; vcase x; vsimp; cbn [eren]; vsimp; [reflexivity|].
  destruct (K σ z) as [w|[u f]]; cbn [eren eshift]; vsimp; [reflexivity|].
  f_equal; f_equal. rewrite !ren_tms_ren. apply ren_tms_ext; intros; apply wk_upr.
Qed.

Lemma ren_trav_mut :
  (forall Γ s (t : tm Γ s) Δ Ξ (K : kit Γ Δ) (ξ : ren Δ Ξ),
      knat K -> ren_tm (trav t K) ξ = trav t (kren K ξ)) /\
  (forall Γ Θ (a : args Γ Θ) Δ Ξ (K : kit Γ Δ) (ξ : ren Δ Ξ),
      knat K -> ren_args (trav_args a K) ξ = trav_args a (kren K ξ)).
Proof.
  apply tm_args_ind; intros; simpl; try reflexivity.
  - destruct (K σ v) as [y|[u f]] eqn:E; unfold kren; rewrite E; simpl.
    + f_equal; auto.
    + pose proof (H0 _ _ _ _ E) as Hn; unfold natural in Hn; rewrite Hn. f_equal; auto.
  - f_equal; auto.
  - f_equal; auto. rewrite H by (apply knat_kup; assumption).
    symmetry; apply trav_ext, kup_kren.
Qed.

Lemma ren_trav {Γ s} (t : tm Γ s) {Δ Ξ} (K : kit Γ Δ) (ξ : ren Δ Ξ) :
  knat K -> ren_tm (trav t K) ξ = trav t (kren K ξ).
Proof. apply ren_trav_mut. Qed.

Lemma ren_trav_args {Γ Θ} (a : args Γ Θ) {Δ Ξ} (K : kit Γ Δ) (ξ : ren Δ Ξ) :
  knat K -> ren_args (trav_args a K) ξ = trav_args a (kren K ξ).
Proof. apply ren_trav_mut. Qed.

Lemma aget_trav {Γ Θ σ} (z : var Θ σ) (a : args Γ Θ) {Δ} (K : kit Γ Δ) :
  aget z (trav_args a K) = trav (aget z a) (kup (dom σ) K).
Proof.
  revert a; induction z as [Θ0 σ0|Θ0 σ0 τ0 z IH]; intros a;
    rewrite (args_eta a); cbn; [reflexivity|apply IH].
Qed.

(** ** Naturalité de l'application héréditaire *)

Lemma happ_natural (σ : spec Srt) : natural (happ (Sym:=Sym) σ).
Proof.
  induction σ as [Θ b IH] using spec_rect'.
  intros Ξ Ξ' ξ u a. cbn [dom cod] in *. rewrite !happ_Spec.
  rewrite ren_trav.
  2:{ intros σ' x u' f E. unfold inst_kit in E.
      destruct (vsplit Θ x) as [z|y]; [|discriminate].
      injection E as <- <-. rewrite all_get_happs. exact (IH σ' z). }
  unfold ren_tms; rewrite trav_ren. apply trav_ext.
  intros σ' x; unfold kren, rk_comp; vcase x; vsimp; cbn [eren]; [|reflexivity].
  rewrite aget_ren; reflexivity.
Qed.

Lemma knat_happ {Γ Δ} (K : kit Γ Δ) :
  (forall σ x u f, K σ x = inr (u, f) -> f = happ σ) -> knat K.
Proof. intros H σ x u f E; rewrite (H _ _ _ _ E); apply happ_natural. Qed.

End Traversal.
