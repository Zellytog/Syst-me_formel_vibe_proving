(** * Composition des substitutions et lemme de substitution héréditaire

    Le résultat central est [happ_commutes] : l'application héréditaire
    commute à toute traversée dont les fonctions d'application sont des
    [happ]. On le prouve par récurrence sur [depth σ + m], où [m] majore
    les profondeurs des spécifications substituées par le kit. On en déduit
    l'associativité de la substitution parallèle. *)

From Stdlib Require Import List Arith Lia.
Import ListNotations.
From SF.Syntax Require Import Spec Terms Renaming Traversal Eta.

Section Composition.

Context {Srt : Type} {Sym : spec Srt -> Type}.
Implicit Types (Λ Θ Γ Δ Ξ Ω D : ctx Srt) (σ τ ρ : spec Srt).

Local Notation tm := (tm Sym).
Local Notation args := (args Sym).
Local Notation tms := (tms Sym).
Local Notation kit := (kit Sym).
Local Notation applier := (applier Sym).
Local Notation sub := (sub Sym).

(** ** Composition de kits *)

Definition kcomp {Γ Δ Ξ} (K1 : kit Γ Δ) (K2 : kit Δ Ξ) : kit Γ Ξ :=
  fun σ x => match K1 σ x with
             | inl y => K2 σ y
             | inr (u, f) => inr (trav u (kup (dom σ) K2), f)
             end.

Lemma wk_wk Λ D {Γ} σ (y : var Γ σ) :
  rcomp (wk Λ) (wk D) σ y = rcomp (wk D) (upr D (wk Λ)) σ y.
Proof. unfold rcomp, wk; autorewrite with vsimpl; reflexivity. Qed.

Lemma kcomp_inl {Γ Δ Ξ} (K1 : kit Γ Δ) (K2 : kit Δ Ξ) σ x y :
  K1 σ x = inl y -> kcomp K1 K2 σ x = K2 σ y.
Proof. intros E; unfold kcomp; rewrite E; reflexivity. Qed.

Lemma kcomp_inr {Γ Δ Ξ} (K1 : kit Γ Δ) (K2 : kit Δ Ξ) σ x u f :
  K1 σ x = inr (u, f) -> kcomp K1 K2 σ x = inr (trav u (kup (dom σ) K2), f).
Proof. intros E; unfold kcomp; rewrite E; reflexivity. Qed.

Lemma kcomp_kup Λ {Γ Δ Ξ} (K1 : kit Γ Δ) (K2 : kit Δ Ξ) :
  knat K2 -> keq (kcomp (kup Λ K1) (kup Λ K2)) (kup Λ (kcomp K1 K2)).
Proof.
  intros HK σ x; unfold kcomp; vcase x; vsimp; [reflexivity|].
  destruct (K1 σ z) as [y|[u f]]; vsimp; [reflexivity|].
  f_equal; f_equal. unfold ren_tms.
  rewrite trav_ren, ren_trav by (apply knat_kup; assumption).
  apply trav_ext; intros σ' x'; unfold rk_comp, kren.
  vcase x'; vsimp; cbn [eren]; vsimp; [reflexivity|].
  unfold wk at 1; vsimp.
  destruct (K2 σ' z0) as [w|[u' f']]; cbn [eren eshift]; vsimp; [reflexivity|].
  f_equal; f_equal.
  rewrite !ren_tms_ren. apply ren_tms_ext; intros; apply wk_wk.
Qed.

(** ** Kits bornés : fonctions d'application [happ], profondeurs < m *)

Definition bounded (m : nat) {Γ Δ} (K : kit Γ Δ) : Prop :=
  forall σ x u f, K σ x = inr (u, f) -> f = happ σ /\ depth σ < m.

Lemma bounded_kup m Λ {Γ Δ} (K : kit Γ Δ) : bounded m K -> bounded m (kup Λ K).
Proof.
  intros H σ x u f; vcase x; autorewrite with vsimpl; [intros Hc; discriminate Hc|].
  unfold eshift; destruct (K σ z) as [w|[u0 f0]] eqn:E; [intros Hc; discriminate Hc|].
  intros [=]; subst; eapply H; eauto.
Qed.

Lemma bounded_knat m {Γ Δ} (K : kit Γ Δ) : bounded m K -> knat K.
Proof. intros H; apply knat_happ; intros σ x u f E; exact (proj1 (H σ x u f E)). Qed.

Definition commutes {σ} (f : applier σ) (m : nat) : Prop :=
  forall Ξ Ξ' (K : kit Ξ Ξ'), bounded m K ->
  forall (u : tms Ξ σ) (a : args Ξ (dom σ)),
    trav (f Ξ u a) K = f Ξ' (trav u (kup (dom σ) K)) (trav_args a K).

(** ** Composition de traversées *)

Lemma trav_comp_mut :
  (forall Γ s (t : tm Γ s) Δ Ξ (K1 : kit Γ Δ) (K2 : kit Δ Ξ) m,
      (forall σ x u f, K1 σ x = inr (u, f) -> commutes f m) -> bounded m K2 ->
      trav (trav t K1) K2 = trav t (kcomp K1 K2)) /\
  (forall Γ Θ (a : args Γ Θ) Δ Ξ (K1 : kit Γ Δ) (K2 : kit Δ Ξ) m,
      (forall σ x u f, K1 σ x = inr (u, f) -> commutes f m) -> bounded m K2 ->
      trav_args (trav_args a K1) K2 = trav_args a (kcomp K1 K2)).
Proof.
  apply tm_args_ind; intros; simpl; try reflexivity.
  - destruct (K1 σ v) as [y|[u f]] eqn:E.
    + rewrite (kcomp_inl K1 K2 _ _ _ E); simpl.
      rewrite (H _ _ K1 K2 m H0 H1). reflexivity.
    + rewrite (kcomp_inr K1 K2 _ _ _ _ E); simpl.
      rewrite (H0 _ _ _ _ E _ _ K2 H1). f_equal. apply (H _ _ K1 K2 m H0 H1).
  - f_equal; eauto.
  - f_equal; eauto.
    rewrite (H _ _ (kup (dom σ) K1) (kup (dom σ) K2) m).
    + apply trav_ext; apply kcomp_kup; apply (bounded_knat m); exact H2.
    + intros σ' x u f E. destruct (kup_inr _ _ _ _ _ _ E) as [y [u0 E0]]. eauto.
    + apply bounded_kup, H2.
Qed.

Lemma trav_comp {Γ s} (t : tm Γ s) {Δ Ξ} (K1 : kit Γ Δ) (K2 : kit Δ Ξ) m :
  (forall σ x u f, K1 σ x = inr (u, f) -> commutes f m) -> bounded m K2 ->
  trav (trav t K1) K2 = trav t (kcomp K1 K2).
Proof. apply trav_comp_mut. Qed.

Lemma trav_args_comp {Γ Θ} (a : args Γ Θ) {Δ Ξ} (K1 : kit Γ Δ) (K2 : kit Δ Ξ) m :
  (forall σ x u f, K1 σ x = inr (u, f) -> commutes f m) -> bounded m K2 ->
  trav_args (trav_args a K1) K2 = trav_args a (kcomp K1 K2).
Proof. apply trav_comp_mut. Qed.

(** Traverser un terme affaibli par un kit d'instanciation ne fait rien. *)
Lemma trav_wk_inst D Θ {Ξ} (fs : All applier Θ) (a : args Ξ Θ) b (u : tm (D ++ Ξ) b) :
  trav (ren_tm u (upr D (wk Θ))) (kup D (inst_kit Θ a fs)) = u.
Proof.
  rewrite trav_ren. rewrite <- (trav_rid u) at 2. apply trav_ext.
  intros σ x; unfold rk_comp, rkit, rid, wk; vcase x; vsimp; reflexivity.
Qed.

(** ** Le lemme de substitution héréditaire *)

Lemma happ_commutes_aux n : forall (σ : spec Srt) m, depth σ + m < n -> commutes (happ σ) m.
Proof.
  induction n as [|n IH]; intros σ m Hn; [lia|].
  destruct σ as [Θ b]. intros Ξ Ξ' K HK u a. rewrite !happ_Spec. cbn [dom].
  erewrite (trav_comp u _ K m).
  2:{ intros σ' x u' f E. unfold inst_kit in E.
      destruct (vsplit Θ x) as [z|y]; [|discriminate].
      injection E as <- <-. rewrite all_get_happs. apply IH.
      pose proof (depth_dom b z); lia. }
  2:{ exact HK. }
  erewrite (trav_comp u (kup Θ K) _ (depth (Spec Θ b))).
  2:{ intros σ' x u' f E. destruct (kup_inr _ _ _ _ _ _ E) as [y [u0 E0]].
      destruct (HK _ _ _ _ E0) as [-> Hd]. apply IH; lia. }
  2:{ intros σ' x u' f E. unfold inst_kit in E.
      destruct (vsplit Θ x) as [z|y]; [|discriminate].
      injection E as <- <-. rewrite all_get_happs. split; [reflexivity|exact (depth_dom b z)]. }
  apply trav_ext; intros σ' x; unfold kcomp. vcase x; vsimp.
  - rewrite aget_trav; reflexivity.
  - destruct (K σ' z) as [w|[u' f']]; vsimp; [reflexivity|].
    unfold ren_tms; rewrite trav_wk_inst; reflexivity.
Qed.

Theorem happ_commutes (σ : spec Srt) m : commutes (happ (Sym:=Sym) σ) m.
Proof. apply (happ_commutes_aux (S (depth σ + m))); lia. Qed.

(** ** Conséquences pour les substitutions parallèles *)

Lemma bounded_sub_kit {Γ Δ} (τ : sub Γ Δ) : bounded (S (depths Γ)) (sub_kit τ).
Proof.
  intros σ x u f E; injection E as <- <-. split; [reflexivity|].
  pose proof (depth_var x); lia.
Qed.

Lemma sub_kit_commutes {Γ Δ} (τ : sub Γ Δ) m :
  forall σ x u f, sub_kit τ σ x = inr (u, f) -> commutes f m.
Proof. intros σ x u f E; injection E as <- <-; apply happ_commutes. Qed.

Lemma kup_sub_kit_commutes Λ {Γ Δ} (τ : sub Γ Δ) m :
  forall σ x u f, kup Λ (sub_kit τ) σ x = inr (u, f) -> commutes f m.
Proof.
  intros σ x u f E. destruct (kup_inr _ _ _ _ _ _ E) as [y [u0 E0]].
  eapply sub_kit_commutes; eauto.
Qed.

(** Substitution dans une application héréditaire. *)
Theorem subst_happ (σ : spec Srt) {Ξ Ξ'} (u : tms Ξ σ) (a : args Ξ (dom σ)) (θ : sub Ξ Ξ') :
  subst (happ σ u a) θ = happ σ (subst_tms u θ) (subst_args a θ).
Proof. exact (happ_commutes σ _ _ _ (sub_kit θ) (bounded_sub_kit θ) u a). Qed.

Theorem subst_subst {Γ s} (t : tm Γ s) {Δ Ξ} (τ : sub Γ Δ) (θ : sub Δ Ξ) :
  subst (subst t τ) θ = subst t (ss_comp τ θ).
Proof.
  unfold subst. rewrite (trav_comp t _ _ (S (depths Δ))).
  - apply trav_ext; intros σ x; reflexivity.
  - apply sub_kit_commutes.
  - apply bounded_sub_kit.
Qed.

Theorem subst_args_subst {Γ Θ} (a : args Γ Θ) {Δ Ξ} (τ : sub Γ Δ) (θ : sub Δ Ξ) :
  subst_args (subst_args a τ) θ = subst_args a (ss_comp τ θ).
Proof.
  unfold subst_args. rewrite (trav_args_comp a _ _ (S (depths Δ))).
  - apply trav_args_ext; intros σ x; reflexivity.
  - apply sub_kit_commutes.
  - apply bounded_sub_kit.
Qed.

Theorem subst_tms_subst {Γ σ} (u : tms Γ σ) {Δ Ξ} (τ : sub Γ Δ) (θ : sub Δ Ξ) :
  subst_tms (subst_tms u τ) θ = subst_tms u (ss_comp τ θ).
Proof.
  unfold subst_tms. rewrite (trav_comp u _ _ (S (depths Δ))).
  - rewrite (trav_ext u _ _ (kcomp_kup _ _ _ (bounded_knat _ _ (bounded_sub_kit θ)))).
    apply trav_ext; apply kup_ext; intros σ' x; reflexivity.
  - apply kup_sub_kit_commutes.
  - apply bounded_kup, bounded_sub_kit.
Qed.

(** Interactions avec les renommages. *)
Lemma subst_ren {Γ s} (t : tm Γ s) {Δ Ξ} (ρ : ren Γ Δ) (τ : sub Δ Ξ) :
  subst (ren_tm t ρ) τ = subst t (rs_comp ρ τ).
Proof. unfold subst; rewrite trav_ren; apply trav_ext; intros σ x; reflexivity. Qed.

Lemma subst_args_ren {Γ Θ} (a : args Γ Θ) {Δ Ξ} (ρ : ren Γ Δ) (τ : sub Δ Ξ) :
  subst_args (ren_args a ρ) τ = subst_args a (rs_comp ρ τ).
Proof. unfold subst_args; rewrite trav_args_ren; apply trav_args_ext; intros σ x; reflexivity. Qed.

Lemma ren_subst {Γ s} (t : tm Γ s) {Δ Ξ} (τ : sub Γ Δ) (ξ : ren Δ Ξ) :
  ren_tm (subst t τ) ξ = subst t (sr_comp τ ξ).
Proof.
  unfold subst; rewrite ren_trav by (apply (bounded_knat _ _ (bounded_sub_kit τ))).
  apply trav_ext; intros σ x; reflexivity.
Qed.

Lemma ren_subst_args {Γ Θ} (a : args Γ Θ) {Δ Ξ} (τ : sub Γ Δ) (ξ : ren Δ Ξ) :
  ren_args (subst_args a τ) ξ = subst_args a (sr_comp τ ξ).
Proof.
  unfold subst_args; rewrite ren_trav_args by (apply (bounded_knat _ _ (bounded_sub_kit τ))).
  apply trav_args_ext; intros σ x; reflexivity.
Qed.

Lemma subst_tms_ren {Γ σ} (u : tms Γ σ) {Δ Ξ} (ρ : ren Γ Δ) (τ : sub Δ Ξ) :
  subst_tms (ren_tms u ρ) τ = subst_tms u (rs_comp ρ τ).
Proof.
  unfold subst_tms, ren_tms. rewrite trav_ren.
  rewrite <- (trav_ext u _ _ (kup_rk (dom σ) ρ (sub_kit τ))).
  apply trav_ext; apply kup_ext; intros σ' x; reflexivity.
Qed.

Lemma ren_subst_tms {Γ σ} (u : tms Γ σ) {Δ Ξ} (τ : sub Γ Δ) (ξ : ren Δ Ξ) :
  ren_tms (subst_tms u τ) ξ = subst_tms u (sr_comp τ ξ).
Proof.
  unfold subst_tms, ren_tms.
  rewrite ren_trav by (apply knat_kup, (bounded_knat _ _ (bounded_sub_kit τ))).
  rewrite <- (trav_ext u _ _ (kup_kren (dom σ) (sub_kit τ) ξ)).
  apply trav_ext; apply kup_ext; intros σ' x; reflexivity.
Qed.

(** [subst_tms] est la substitution relevée sous les lieurs. *)
Lemma subst_tms_up {Γ σ} (u : tms Γ σ) {Δ} (τ : sub Γ Δ) :
  subst_tms u τ = subst u (up_sub (dom σ) τ).
Proof.
  unfold subst_tms, subst. apply trav_krel.
  intros σ' x; unfold sub_kit, up_sub; vcase x; autorewrite with vsimpl.
  - right; split; [intros ? ? ?; apply happ_eta|]. exists (vl Δ z); split; [reflexivity|].
    rewrite aget_etas; reflexivity.
  - left; reflexivity.
Qed.

End Composition.
