(** * η-expansion : lois β/η de l'application héréditaire et substitution identité *)

From Stdlib Require Import List.
Import ListNotations.
From SF.Syntax Require Import Spec Terms Renaming Traversal.

Section Eta.

Context {Srt : Type} {Sym : spec Srt -> Type}.
Implicit Types (Λ Θ Γ Δ Ξ Ω D : ctx Srt) (σ τ ρ : spec Srt).

Local Notation tm := (tm Sym).
Local Notation args := (args Sym).
Local Notation tms := (tms Sym).
Local Notation kit := (kit Sym).
Local Notation sub := (sub Sym).

Lemma etas_ext Θ {Ξ} (f g : forall ρ, var Θ ρ -> var Ξ ρ) :
  (forall ρ z, f ρ z = g ρ z) -> etas (Sym:=Sym) Θ f = etas Θ g.
Proof.
  revert Ξ f g; induction Θ as [|ρ Θ IH]; intros Ξ f g H; cbn; [reflexivity|].
  rewrite H; f_equal; apply IH; intros; apply H.
Qed.

Lemma aget_etas {Θ σ} (z : var Θ σ) {Ξ} (f : forall ρ, var Θ ρ -> var Ξ ρ) :
  aget z (etas (Sym:=Sym) Θ f) = eta σ (f σ z).
Proof.
  revert Ξ f; induction z as [Θ0 σ0|Θ0 σ0 τ0 z IH]; intros Ξ f; cbn; [reflexivity|].
  apply (IH Ξ (fun ρ y => f ρ (vs y))).
Qed.

(** ** Renommage d'un η-expansé *)

Lemma etas_ren Θ :
  (forall ρ, var Θ ρ -> forall Γ Δ (ξ : ren Γ Δ) (x : var Γ ρ),
       ren_tms (eta (Sym:=Sym) ρ x) ξ = eta ρ (ξ ρ x)) ->
  forall Ξ Ξ' (f : forall ρ, var Θ ρ -> var Ξ ρ) (ξ : ren Ξ Ξ'),
    ren_args (etas (Sym:=Sym) Θ f) ξ = etas Θ (fun ρ z => ξ ρ (f ρ z)).
Proof.
  induction Θ as [|ρ Θ IH]; intros H Ξ Ξ' f ξ; cbn; [reflexivity|].
  f_equal.
  - apply (H ρ vz).
  - apply (IH (fun ρ' z => H ρ' (vs z))).
Qed.

Lemma eta_ren (ρ : spec Srt) {Γ Δ} (ξ : ren Γ Δ) (x : var Γ ρ) :
  ren_tms (eta (Sym:=Sym) ρ x) ξ = eta ρ (ξ ρ x).
Proof.
  revert Γ Δ ξ x; induction ρ as [Θ b IH] using spec_rect'; intros Γ Δ ξ x.
  rewrite !eta_Spec; unfold ren_tms; simpl. rewrite upr_vr.
  f_equal. rewrite (etas_ren Θ IH). apply etas_ext; intros; apply upr_vl.
Qed.

(** ** Traverser un η-expansé *)

Definition trav_eta_inl_prop (ρ : spec Srt) : Prop :=
  forall Γ Δ (K : kit Γ Δ) (x : var Γ ρ) (y : var Δ ρ),
    K ρ x = inl y -> trav (eta ρ x) (kup (dom ρ) K) = eta ρ y.

Lemma etas_trav_inl Θ :
  (forall ρ, var Θ ρ -> trav_eta_inl_prop ρ) ->
  forall Ξ Ξ' (f : forall ρ, var Θ ρ -> var Ξ ρ) (g : forall ρ, var Θ ρ -> var Ξ' ρ) (K : kit Ξ Ξ'),
    (forall ρ z, K ρ (f ρ z) = inl (g ρ z)) ->
    trav_args (etas Θ f) K = etas Θ g.
Proof.
  induction Θ as [|ρ Θ IH]; intros H Ξ Ξ' f g K Hk; cbn; [reflexivity|].
  f_equal.
  - apply (H ρ vz), Hk.
  - apply (IH (fun ρ' z => H ρ' (vs z))). intros; apply Hk.
Qed.

Lemma trav_eta_inl (ρ : spec Srt) : trav_eta_inl_prop ρ.
Proof.
  induction ρ as [Θ b IH] using spec_rect'; intros Γ Δ K x y E.
  rewrite !eta_Spec; simpl. rewrite kup_vr, E; cbn [eshift].
  f_equal. apply (etas_trav_inl Θ IH). intros; apply kup_vl.
Qed.

Lemma trav_eta_inr (ρ : spec Srt) {Γ Δ} (K : kit Γ Δ) (x : var Γ ρ) u f :
  K ρ x = inr (u, f) ->
  trav (eta ρ x) (kup (dom ρ) K) =
    f (dom ρ ++ Δ) (ren_tms u (wk (dom ρ))) (etas (dom ρ) (fun τ z => vl Δ z)).
Proof.
  intros E; destruct ρ as [Θ b]. rewrite eta_Spec; simpl.
  rewrite kup_vr, E; cbn [eshift]. f_equal.
  apply (etas_trav_inl Θ (fun τ _ => trav_eta_inl τ)). intros; apply kup_vl.
Qed.

(** ** Kits η-équivalents

    Remplacer, dans un kit, une variable [y] par son η-expansé [eta y]
    (accompagné de [happ]) ne change pas le résultat de la traversée,
    pourvu que la loi η soit connue pour la spécification concernée. *)

Definition good (ρ : spec Srt) : Prop :=
  forall Ξ (x : var Ξ ρ) (a : args Ξ (dom ρ)), happ ρ (eta ρ x) a = tvar x a.

Definition krel {Γ Δ} (K K' : kit Γ Δ) : Prop :=
  forall σ x, K σ x = K' σ x \/
         (good σ /\ exists y, K σ x = inl y /\ K' σ x = inr (eta σ y, happ σ)).

Lemma krel_kup Λ {Γ Δ} (K K' : kit Γ Δ) : krel K K' -> krel (kup Λ K) (kup Λ K').
Proof.
  intros H σ x; vcase x; autorewrite with vsimpl; [now left|].
  destruct (H σ z) as [E|[G [y [E1 E2]]]]; [left; now rewrite E|].
  right; split; [assumption|]. exists (vr Λ y). rewrite E1, E2; cbn [eshift].
  split; [reflexivity|]. rewrite eta_ren; reflexivity.
Qed.

Lemma trav_krel_mut :
  (forall Γ s (t : tm Γ s) Δ (K K' : kit Γ Δ), krel K K' -> trav t K = trav t K') /\
  (forall Γ Θ (a : args Γ Θ) Δ (K K' : kit Γ Δ), krel K K' -> trav_args a K = trav_args a K').
Proof.
  apply tm_args_ind; intros; simpl; try reflexivity.
  - rewrite (H Δ K K' H0).
    destruct (H0 σ v) as [E|[G [y [E1 E2]]]]; [now rewrite E|].
    rewrite E1, E2. symmetry; apply G.
  - f_equal; auto.
  - f_equal; auto. apply H, krel_kup; assumption.
Qed.

Lemma trav_krel {Γ s} (t : tm Γ s) {Δ} (K K' : kit Γ Δ) : krel K K' -> trav t K = trav t K'.
Proof. apply trav_krel_mut. Qed.

Lemma trav_args_krel {Γ Θ} (a : args Γ Θ) {Δ} (K K' : kit Γ Δ) :
  krel K K' -> trav_args a K = trav_args a K'.
Proof. apply trav_krel_mut. Qed.

(** ** Les deux lois, par récurrence simultanée sur les spécifications

    - [good ρ] : appliquer l'η-expansé de [x] à des arguments redonne [x(a)] ;
    - [eta_unit ρ] : appliquer un corps aux η-expansés de ses propres
      variables liées redonne le corps. *)

Definition eta_unit (ρ : spec Srt) : Prop :=
  forall Ξ (u : tms Ξ ρ),
    happ ρ (ren_tms u (wk (dom ρ))) (etas (dom ρ) (fun τ z => vl Ξ z)) = u.

Lemma good_eta_unit (ρ : spec Srt) : good ρ /\ eta_unit ρ.
Proof.
  induction ρ as [Θ b IH] using spec_rect'. split.
  - intros Ξ x a. rewrite happ_Spec, eta_Spec; simpl.
    rewrite inst_kit_vr; cbn beta iota. f_equal. apply args_ext; intros τ z.
    rewrite aget_trav, aget_etas.
    rewrite (trav_eta_inr τ _ (vl Ξ z) (aget z a) (happ τ)).
    + apply (proj2 (IH τ z)).
    + rewrite inst_kit_vl, all_get_happs; reflexivity.
  - intros Ξ u. rewrite happ_Spec; cbn [dom]. unfold ren_tms; rewrite trav_ren.
    rewrite <- (trav_rid u) at 2. symmetry; apply trav_krel.
    intros σ x; unfold rk_comp, rkit, rid; vcase x; autorewrite with vsimpl.
    + right. split; [apply (proj1 (IH σ z))|]. exists (vl Ξ z). split; [reflexivity|].
      rewrite aget_etas, all_get_happs; reflexivity.
    + left; unfold wk; autorewrite with vsimpl; reflexivity.
Qed.

Lemma happ_eta (ρ : spec Srt) {Ξ} (x : var Ξ ρ) (a : args Ξ (dom ρ)) :
  happ ρ (eta ρ x) a = tvar x a.
Proof. apply good_eta_unit. Qed.

Lemma happ_eta_unit (ρ : spec Srt) {Ξ} (u : tms Ξ ρ) :
  happ ρ (ren_tms u (wk (dom ρ))) (etas (dom ρ) (fun τ z => vl Ξ z)) = u.
Proof. apply good_eta_unit. Qed.

(** ** Substitution identité *)

Lemma krel_ids {Γ} : krel (rkit (@rid _ Γ)) (sub_kit (Sym:=Sym) ids).
Proof.
  intros σ x; right; split; [intros ? ? ?; apply happ_eta|]. exists x; split; reflexivity.
Qed.

Lemma subst_id {Γ s} (t : tm Γ s) : subst t ids = t.
Proof. unfold subst; rewrite <- (trav_krel t _ _ krel_ids); apply trav_rid. Qed.

Lemma subst_args_id {Γ Θ} (a : args Γ Θ) : subst_args a ids = a.
Proof.
  unfold subst_args; rewrite <- (trav_args_krel a _ _ krel_ids).
  rewrite (proj2 trav_rkit_mut); apply ren_args_id.
Qed.

Lemma subst_tms_id {Γ σ} (u : tms Γ σ) : subst_tms u ids = u.
Proof.
  unfold subst_tms. rewrite <- (trav_krel u _ _ (krel_kup (dom σ) _ _ krel_ids)).
  rewrite (trav_ext u _ _ (kup_rkit _ _)), trav_rkit.
  rewrite (ren_ext u _ rid); [apply ren_id|apply upr_id].
Qed.

(** Substituer dans l'η-expansé d'une variable redonne l'image de la variable. *)
Lemma eta_subst {Γ Δ σ} (x : var Γ σ) (τ : sub Γ Δ) : subst_tms (eta σ x) τ = τ σ x.
Proof.
  unfold subst_tms. rewrite (trav_eta_inr σ _ x (τ σ x) (happ σ)) by reflexivity.
  apply happ_eta_unit.
Qed.

(** L'application héréditaire est une substitution. *)
Lemma happ_subst (σ : spec Srt) {Ξ} (u : tms Ξ σ) (a : args Ξ (dom σ)) :
  happ σ u a = subst u (sapp a ids).
Proof.
  destruct σ as [Θ b]. rewrite happ_Spec; unfold subst; cbn [dom] in *.
  apply trav_krel. intros σ x; unfold sub_kit; vcase x; autorewrite with vsimpl.
  - left; rewrite all_get_happs; reflexivity.
  - right; split; [intros ? ? ?; apply happ_eta|]. exists z; split; reflexivity.
Qed.

(** Un renommage est une substitution. *)
Lemma ren_as_subst {Γ s} (t : tm Γ s) {Δ} (ρ : ren Γ Δ) :
  ren_tm t ρ = subst t (rs_comp ρ ids).
Proof.
  rewrite <- trav_rkit; apply trav_krel. intros σ x; right.
  split; [intros ? ? ?; apply happ_eta|]. exists (ρ σ x); split; reflexivity.
Qed.

End Eta.
