(** * Interprétations qui ne changent pas les sortes

    Variante des interprétations ([Interpretation.v] à [Admissible.v]) pour
    deux signatures sur le **même** type de sortes, avec l'identité sur les
    sortes. Les spécifications et les contextes ne sont alors pas traduits du
    tout : un symbole f : σ s'interprète par un terme de spécification σ
    elle-même, et la traduction d'un terme de Γ est un terme de Γ.

    C'est le cas des relativisations (HA dans le système libre). La
    traduction générale, qui passe par [smap] et [cmap], ne se réduit pas
    lorsque les spécifications des symboles sont elles-mêmes génériques (les
    constructeurs d'un type inductif décrit par une liste quelconque) ; ici,
    il n'y a rien à réduire.

    Contenu, dans l'ordre des fichiers dont il est la variante :
    - la traduction [tr] et sa commutation avec la substitution
      ([tr_vsubst]) et l'application héréditaire ([itm_happ]) ;
    - la préservation des conversions sur les règles génératrices
      ([interp_conv]) ;
    - les interprétations de logiques avec relativisation, la traduction des
      règles ([tr_rule]) et la correction par admissibilité
      ([interp_sound_on]) ;
    - un critère pour les termes dont tous les symboles sont interprétés par
      eux-mêmes : leur traduction est l'identité ([tr_pure]). *)

From Stdlib Require Import List Lia.
Import ListNotations.
From SF.Syntax Require Import Spec Terms Renaming Traversal Eta Composition Vectors.
From SF.Calculus Require Import System Rules.
From SF.Logic Require Import Judgment.
From SF.Extensions Require Import Conservativity Commute.

(** ** Interprétations et traduction des termes *)

Section Interp.
Context {Srt : Type} (Sym1 Sym2 : spec Srt -> Type).

Record sinterp := {
  s_sym : forall σ, Sym1 σ -> Terms.tm Sym2 (dom σ) (cod σ)
}.

Context (F : sinterp).

Fixpoint itm {Γ s} (t : Terms.tm Sym1 Γ s) {struct t} : forall Γ', ren Γ Γ' -> Terms.tm Sym2 Γ' s :=
  match t in Terms.tm _ Γ0 s0 return forall Γ', ren Γ0 Γ' -> Terms.tm Sym2 Γ' s0 with
  | @tvar _ _ Γ0 σ x a => fun Γ' ρ => @tvar _ Sym2 Γ' σ (ρ σ x) (iargs a Γ' ρ)
  | tsym c a => fun Γ' ρ => vsubst (s_sym F _ c) (iargs a Γ' ρ)
  end
with iargs {Γ Θ} (a : args Sym1 Γ Θ) {struct a} : forall Γ', ren Γ Γ' -> args Sym2 Γ' Θ :=
  match a in args _ Γ0 Θ0 return forall Γ', ren Γ0 Γ' -> args Sym2 Γ' Θ0 with
  | anil => fun Γ' ρ => anil
  | @acons _ _ Γ0 σ _ u a' => fun Γ' ρ =>
      @acons _ Sym2 Γ' σ _ (itm u (dom σ ++ Γ') (upr (dom σ) ρ)) (iargs a' Γ' ρ)
  end.

Definition tr {Γ s} (t : Terms.tm Sym1 Γ s) : Terms.tm Sym2 Γ s := itm t Γ rid.

End Interp.

Arguments s_sym {Srt Sym1 Sym2} s {σ} c : rename.
Arguments itm {Srt Sym1 Sym2} F {Γ s} t Γ' ρ.
Arguments iargs {Srt Sym1 Sym2} F {Γ Θ} a Γ' ρ.
Arguments tr {Srt Sym1 Sym2} F {Γ s} t.

(** ** Commutation avec la substitution *)

Section Commute.
Context {Srt : Type} {Sym1 Sym2 : spec Srt -> Type} (F : sinterp Sym1 Sym2).

Local Notation tm1 := (Terms.tm Sym1).
Local Notation tm2 := (Terms.tm Sym2).

Definition itms {Γ σ} (u : tms Sym1 Γ σ) Γ' (ρ : ren Γ Γ') : tms Sym2 Γ' σ :=
  itm F u (dom σ ++ Γ') (upr (dom σ) ρ).

Lemma itm_tvar {Γ σ} (x : var Γ σ) (a : args Sym1 Γ (dom σ)) Γ' (ρ : ren Γ Γ') :
  itm F (tvar x a) Γ' ρ = tvar (ρ σ x) (iargs F a Γ' ρ).
Proof. reflexivity. Qed.

Lemma itm_tsym {Γ σ} (c : Sym1 σ) (a : args Sym1 Γ (dom σ)) Γ' (ρ : ren Γ Γ') :
  itm F (tsym c a) Γ' ρ = vsubst (s_sym F c) (iargs F a Γ' ρ).
Proof. reflexivity. Qed.

Lemma iargs_acons {Γ σ Θ} (u : tms Sym1 Γ σ) (a : args Sym1 Γ Θ) Γ' (ρ : ren Γ Γ') :
  iargs F (acons u a) Γ' ρ = @acons _ Sym2 Γ' σ _ (itms u Γ' ρ) (iargs F a Γ' ρ).
Proof. reflexivity. Qed.

Lemma aget_iargs {Θ σ} (z : var Θ σ) {Γ} (b : args Sym1 Γ Θ) Γ' (ρ : ren Γ Γ') :
  aget z (iargs F b Γ' ρ) = itms (aget z b) Γ' ρ.
Proof.
  revert b; induction z as [Θ0 σ0|Θ0 σ0 τ0 z IH]; intros b;
    rewrite (args_eta b), iargs_acons; cbn [aget ahd atl]; [reflexivity|apply IH].
Qed.

Lemma upr_ext (D : ctx Srt) {Γ Γ' : ctx Srt} (ρ ρ' : ren Γ Γ') :
  (forall σ x, ρ σ x = ρ' σ x) -> forall σ x, upr D ρ σ x = upr D ρ' σ x.
Proof. intros H σ x; vcase x; vsimp; [reflexivity|rewrite H; reflexivity]. Qed.

Lemma itm_ext_mut :
  (forall Γ s (t : tm1 Γ s) Γ' (ρ ρ' : ren Γ Γ'),
      (forall σ x, ρ σ x = ρ' σ x) -> itm F t Γ' ρ = itm F t Γ' ρ') /\
  (forall Γ Θ (a : args Sym1 Γ Θ) Γ' (ρ ρ' : ren Γ Γ'),
      (forall σ x, ρ σ x = ρ' σ x) -> iargs F a Γ' ρ = iargs F a Γ' ρ').
Proof.
  apply tm_args_ind.
  - intros Γ σ x a IH Γ' ρ ρ' H. rewrite !itm_tvar, H. f_equal. apply IH, H.
  - intros Γ σ c a IH Γ' ρ ρ' H. rewrite !itm_tsym. f_equal. apply IH, H.
  - reflexivity.
  - intros Γ σ Θ u IHu a IHa Γ' ρ ρ' H. rewrite !iargs_acons. f_equal; [|apply IHa, H].
    unfold itms. apply IHu, upr_ext, H.
Qed.

Lemma itm_ext {Γ s} (t : tm1 Γ s) Γ' (ρ ρ' : ren Γ Γ') :
  (forall σ x, ρ σ x = ρ' σ x) -> itm F t Γ' ρ = itm F t Γ' ρ'.
Proof. apply itm_ext_mut. Qed.

Lemma iargs_ext {Γ Θ} (a : args Sym1 Γ Θ) Γ' (ρ ρ' : ren Γ Γ') :
  (forall σ x, ρ σ x = ρ' σ x) -> iargs F a Γ' ρ = iargs F a Γ' ρ'.
Proof. apply itm_ext_mut. Qed.

Lemma itms_ext {Γ σ} (u : tms Sym1 Γ σ) Γ' (ρ ρ' : ren Γ Γ') :
  (forall σ x, ρ σ x = ρ' σ x) -> itms u Γ' ρ = itms u Γ' ρ'.
Proof. intros H; unfold itms; apply itm_ext, upr_ext, H. Qed.

Lemma itm_ren_mut :
  (forall Γ s (t : tm1 Γ s) Δ (ξ : ren Γ Δ) Γ' (ρ : ren Δ Γ'),
      itm F (ren_tm t ξ) Γ' ρ = itm F t Γ' (rcomp ξ ρ)) /\
  (forall Γ Θ (a : args Sym1 Γ Θ) Δ (ξ : ren Γ Δ) Γ' (ρ : ren Δ Γ'),
      iargs F (ren_args a ξ) Γ' ρ = iargs F a Γ' (rcomp ξ ρ)).
Proof.
  apply tm_args_ind.
  - intros Γ σ x a IH Δ ξ Γ' ρ. rewrite ren_tvar, !itm_tvar. f_equal. apply IH.
  - intros Γ σ c a IH Δ ξ Γ' ρ. rewrite ren_tsym, !itm_tsym. f_equal. apply IH.
  - reflexivity.
  - intros Γ σ Θ u IHu a IHa Δ ξ Γ' ρ. rewrite ren_args_acons, !iargs_acons. f_equal; [|apply IHa].
    unfold itms. rewrite IHu. apply itm_ext; intros τ x. unfold rcomp. vcase x; vsimp; reflexivity.
Qed.

Lemma ren_itm_mut :
  (forall Γ s (t : tm1 Γ s) Γ' (ρ : ren Γ Γ') Δ' (ξ : ren Γ' Δ'),
      ren_tm (itm F t Γ' ρ) ξ = itm F t Δ' (rcomp ρ ξ)) /\
  (forall Γ Θ (a : args Sym1 Γ Θ) Γ' (ρ : ren Γ Γ') Δ' (ξ : ren Γ' Δ'),
      ren_args (iargs F a Γ' ρ) ξ = iargs F a Δ' (rcomp ρ ξ)).
Proof.
  apply tm_args_ind.
  - intros Γ σ x a IH Γ' ρ Δ' ξ. rewrite !itm_tvar, ren_tvar. f_equal. apply IH.
  - intros Γ σ c a IH Γ' ρ Δ' ξ. rewrite !itm_tsym, ren_vsubst, <- ren_args_vren. f_equal. apply IH.
  - reflexivity.
  - intros Γ σ Θ u IHu a IHa Γ' ρ Δ' ξ. rewrite !iargs_acons, ren_args_acons.
    f_equal; [|apply IHa].
    unfold itms. rewrite IHu. apply itm_ext; intros τ x. unfold rcomp. vcase x; vsimp; reflexivity.
Qed.

Lemma itms_ren {Γ σ} (u : tms Sym1 Γ σ) {Δ} (ξ : ren Γ Δ) Γ' (ρ : ren Δ Γ') :
  itms (ren_tms u ξ) Γ' ρ = itms u Γ' (rcomp ξ ρ).
Proof.
  unfold itms, ren_tms. rewrite (proj1 itm_ren_mut). apply itm_ext; intros τ x.
  unfold rcomp. vcase x; vsimp; reflexivity.
Qed.

Lemma ren_itms {Γ σ} (u : tms Sym1 Γ σ) Γ' (ρ : ren Γ Γ') {Δ'} (ξ : ren Γ' Δ') :
  ren_tms (itms u Γ' ρ) ξ = itms u Δ' (rcomp ρ ξ).
Proof.
  unfold itms, ren_tms. rewrite (proj1 ren_itm_mut). apply itm_ext; intros τ x.
  unfold rcomp. vcase x; vsimp; reflexivity.
Qed.

Lemma itms_wk (D : ctx Srt) {Δ σ} (u : tms Sym1 Δ σ) Δ' (ρ : ren Δ Δ') :
  itms (ren_tms u (wk D)) (D ++ Δ') (upr D ρ) = ren_tms (itms u Δ' ρ) (wk D).
Proof.
  rewrite itms_ren, ren_itms. apply itms_ext; intros τ x. unfold rcomp, wk. vsimp. reflexivity.
Qed.

(** Kits reliés par la traduction. *)
Definition ktr (m : nat) {Γ Δ Γ' Δ'} (ρΓ : ren Γ Γ') (ρΔ : ren Δ Δ')
  (K : kit Sym1 Γ Δ) (K' : kit Sym2 Γ' Δ') : Prop :=
  forall σ x,
    match K σ x with
    | inl y => K' σ (ρΓ σ x) = inl (ρΔ σ y)
    | inr (u, f) => f = happ σ /\ depth σ < m /\ K' σ (ρΓ σ x) = inr (itms u Δ' ρΔ, happ σ)
    end.

Lemma ktr_kup m (D : ctx Srt) {Γ Δ Γ' Δ' : ctx Srt} (ρΓ : ren Γ Γ') (ρΔ : ren Δ Δ') K K' :
  ktr m ρΓ ρΔ K K' -> ktr m (upr D ρΓ) (upr D ρΔ) (kup D K) (kup D K').
Proof.
  intros H σ x. vcase x; vsimp; [reflexivity|].
  specialize (H σ z). destruct (K σ z) as [w|[u f]]; cbn [eshift]; vsimp.
  - rewrite H; cbn [eshift]. reflexivity.
  - destruct H as (-> & Hd & H). split; [reflexivity|split; [exact Hd|]].
    rewrite H; cbn [eshift]. rewrite itms_wk. reflexivity.
Qed.

Definition happ_tr (d : nat) : Prop :=
  forall D c, depth (Spec D c) < d ->
  forall Δ Δ' (ρ : ren Δ Δ') (u : tm1 (D ++ Δ) c) (b : args Sym1 Δ D),
    itm F (happ (Spec D c) u b) Δ' ρ = happ (Spec D c) (itm F u (D ++ Δ') (upr D ρ)) (iargs F b Δ' ρ).

Lemma itm_trav_mut m (HC : happ_tr m) :
  (forall Γ s (t : tm1 Γ s) Δ Γ' Δ' (ρΓ : ren Γ Γ') (ρΔ : ren Δ Δ') K K' n,
      ktr m ρΓ ρΔ K K' -> bounded n K' ->
      itm F (trav t K) Δ' ρΔ = trav (itm F t Γ' ρΓ) K') /\
  (forall Γ Θ (a : args Sym1 Γ Θ) Δ Γ' Δ' (ρΓ : ren Γ Γ') (ρΔ : ren Δ Δ') K K' n,
      ktr m ρΓ ρΔ K K' -> bounded n K' ->
      iargs F (trav_args a K) Δ' ρΔ = trav_args (iargs F a Γ' ρΓ) K').
Proof.
  apply tm_args_ind.
  - intros Γ σ x a IH Δ Γ' Δ' ρΓ ρΔ K K' n HK Hn. destruct σ as [D c].
    pose proof (HK _ x) as Hx.
    rewrite itm_tvar, !trav_tvar.
    destruct (K _ x) as [y|[u f]].
    + rewrite Hx, itm_tvar. f_equal. apply (IH _ _ _ _ _ _ _ _ HK Hn).
    + destruct Hx as (-> & Hd & Hx). rewrite Hx.
      rewrite (HC D c Hd). f_equal. apply (IH _ _ _ _ _ _ _ _ HK Hn).
  - intros Γ σ c a IH Δ Γ' Δ' ρΓ ρΔ K K' n HK Hn.
    rewrite trav_tsym, !itm_tsym, (trav_vsubst n _ _ K' Hn). f_equal. apply (IH _ _ _ _ _ _ _ _ HK Hn).
  - reflexivity.
  - intros Γ σ Θ u IHu a IHa Δ Γ' Δ' ρΓ ρΔ K K' n HK Hn.
    rewrite trav_args_acons, !iargs_acons, trav_args_acons.
    f_equal; [|apply (IHa _ _ _ _ _ _ _ _ HK Hn)].
    unfold itms.
    apply (IHu _ _ _ _ _ (kup (dom σ) K) (kup (dom σ) K') n); [apply ktr_kup, HK|apply bounded_kup, Hn].
Qed.

Theorem itm_happ_all d : happ_tr d.
Proof.
  induction d as [|d IHd]; intros D c Hd; [lia|].
  intros Δ Δ' ρ u b. rewrite !happ_Spec.
  assert (HC : happ_tr (depth (Spec D c))) by (intros D' c' H'; apply IHd; lia).
  apply (proj1 (itm_trav_mut _ HC) _ _ u Δ (D ++ Δ') Δ' (upr D ρ) ρ _ _ (depth (Spec D c))).
  - intros σ x. vcase x; vsimp.
    + rewrite !all_get_happs, aget_iargs. split; [reflexivity|split; [exact (depth_dom c z)|reflexivity]].
    + reflexivity.
  - intros σ' x u' f E. unfold inst_kit in E. destruct (vsplit D x) as [z|y]; [|discriminate].
    injection E as <- <-. split; [apply all_get_happs|exact (depth_dom c z)].
Qed.

Corollary itm_happ {D c Δ} (u : tm1 (D ++ Δ) c) (b : args Sym1 Δ D) Δ' (ρ : ren Δ Δ') :
  itm F (happ (Spec D c) u b) Δ' ρ = happ (Spec D c) (itm F u (D ++ Δ') (upr D ρ)) (iargs F b Δ' ρ).
Proof. apply (itm_happ_all (S (depth (Spec D c)))); lia. Qed.

Definition trv {Θ Γ} (v : vec Sym1 Θ Γ) : vec Sym2 Θ Γ := iargs F v Γ rid.

Theorem itm_vsubst {Θ Γ s} (t : tm1 Θ s) (v : vec Sym1 Θ Γ) Γ' (ρ : ren Γ Γ') Θ' (ρΘ : ren Θ Θ')
  (v' : vec Sym2 Θ' Γ') :
  (forall σ x, aget (ρΘ σ x) v' = itms (aget x v) Γ' ρ) ->
  itm F (vsubst t v) Γ' ρ = vsubst (itm F t Θ' ρΘ) v'.
Proof.
  intros Hv. unfold vsubst at 1, subst.
  apply (proj1 (itm_trav_mut (S (depths Θ)) (itm_happ_all _)) _ _ t Γ Θ' Γ' ρΘ ρ _ _ (S (depths Θ'))).
  - intros σ x. cbn [sub_kit]. unfold vget, sub_kit. rewrite Hv.
    split; [reflexivity|split; [pose proof (depth_var x); lia|reflexivity]].
  - apply bounded_sub_kit.
Qed.

Theorem tr_vsubst {Θ Γ s} (t : tm1 Θ s) (v : vec Sym1 Θ Γ) :
  tr F (vsubst t v) = vsubst (tr F t) (trv v).
Proof. apply itm_vsubst; intros σ x; unfold trv; apply aget_iargs. Qed.

(** Un corps traduit sous ses lieurs, c'est la traduction du corps. *)
Lemma itms_rid {Γ σ} (u : tms Sym1 Γ σ) : itms u Γ rid = tr F u.
Proof. unfold itms, tr. apply itm_ext; intros τ x. vcase x; vsimp; reflexivity. Qed.

Lemma tr_ren {Γ Δ s} (t : tm1 Γ s) (ξ : ren Γ Δ) : tr F (ren_tm t ξ) = ren_tm (tr F t) ξ.
Proof.
  unfold tr. rewrite (proj1 itm_ren_mut), (proj1 ren_itm_mut). apply itm_ext; intros; reflexivity.
Qed.

(** Traduire un η-expansé. *)
Lemma iargs_etas (D : ctx Srt) (IH : forall σ, var D σ ->
    forall Γ Γ' (ρ : ren Γ Γ') (x : var Γ σ), itms (eta σ x) Γ' ρ = eta σ (ρ σ x)) :
  forall Ξ Ξ' (f : forall τ, var D τ -> var Ξ τ) (ρ' : ren Ξ Ξ'),
    iargs F (etas D f) Ξ' ρ' = etas D (fun τ z => ρ' τ (f τ z)).
Proof.
  induction D as [|τ D IHD]; intros Ξ Ξ' f ρ'; [reflexivity|].
  cbn [etas]. rewrite iargs_acons. rewrite (IH τ vz). f_equal.
  apply IHD. intros σ z; exact (IH σ (vs z)).
Qed.

Lemma itms_eta σ : forall Γ Γ' (ρ : ren Γ Γ') (x : var Γ σ), itms (eta σ x) Γ' ρ = eta σ (ρ σ x).
Proof.
  induction σ as [D c IH] using spec_rect'. intros Γ Γ' ρ x.
  rewrite eta_Spec. unfold itms. cbn [dom]. rewrite itm_tvar, upr_vr, eta_Spec. f_equal.
  rewrite (iargs_etas D IH). apply etas_ext. intros τ z. apply upr_vl.
Qed.

Lemma trv_vup Λ {Θ Γ} (v : vec Sym1 Θ Γ) : trv (vup Λ v) = vup Λ (trv v).
Proof.
  apply vec_ext; intros σ x; unfold vget, trv. rewrite aget_iargs. vcase x.
  - unfold vup. rewrite !aget_vcat_l, !aget_etas, itms_eta. reflexivity.
  - unfold vup. rewrite !aget_vcat_r. unfold vren. rewrite !aget_vmap, aget_iargs.
    rewrite itms_ren, ren_itms. apply itms_ext; intros; reflexivity.
Qed.

End Commute.

Arguments itms {Srt Sym1 Sym2} F {Γ σ} u Γ' ρ.
Arguments trv {Srt Sym1 Sym2} F {Θ Γ} v.

(** ** Préservation des conversions *)

Section Pullback.
Context {Srt : Type} {Sym1 Sym2 : spec Srt -> Type} (F : sinterp Sym1 Sym2) (C2 : system Sym2).
Local Notation tm1 := (Terms.tm Sym1).

Definition pconv : trel Sym1 := fun Γ s t u => conv C2 (tr F t) (tr F u).

Lemma arel_trv {Θ Γ} (v v' : vec Sym1 Θ Γ) : arel pconv v v' -> arel (conv C2) (trv F v) (trv F v').
Proof.
  revert v v'; induction Θ as [|σ Θ IH]; intros v v' H; [exact Logic.I|].
  destruct H as [H1 H2]. rewrite (args_eta v), (args_eta v'). unfold trv. rewrite !iargs_acons.
  split; [|apply IH, H2]. cbn [ahd]. rewrite !itms_rid. exact H1.
Qed.

Definition pullback : system Sym1.
Proof.
  refine {| conv := pconv |}.
  - intros Γ s t; apply conv_refl.
  - intros Γ s t u H; apply conv_sym, H.
  - intros Γ s t u w H1 H2; eapply conv_trans; [exact H1|exact H2].
  - intros Γ Δ s t t' v v' Ht Hv. unfold pconv. rewrite !tr_vsubst.
    apply conv_subst; [exact Ht|apply arel_trv, Hv].
Defined.

Theorem interp_conv {I} (R : I -> rule Sym1) :
  (forall i, conv C2 (tr F (r_lhs (R i))) (tr F (r_rhs (R i)))) ->
  forall Γ s (t u : tm1 Γ s), conv (generated R) t u -> conv C2 (tr F t) (tr F u).
Proof. intros H Γ s t u Htu. exact (generated_least R pullback H Γ s t u Htu). Qed.

End Pullback.

(** ** Termes purs : traduction identité *)

Lemma aget_vsubst_args' {Srt} {Sym : spec Srt -> Type} {Γ Θ σ} (z : var Θ σ) (a : args Sym Γ Θ) {Δ} (v : vec Sym Γ Δ) :
  aget z (vsubst_args a v) = vsubst_tms (aget z a) v.
Proof. unfold vsubst_args, vsubst_tms. apply aget_subst_args. Qed.

Section Pure.
Context {Srt : Type} {Sym : spec Srt -> Type} (F : sinterp Sym Sym) (keep : forall σ, Sym σ -> bool).
Context (Hkeep : forall σ (c : Sym σ), keep σ c = true -> s_sym F c = tsym c (vid (dom σ))).

(** Un terme dont tous les symboles sont « gardés ». *)
Fixpoint pure {Γ s} (t : Terms.tm Sym Γ s) : Prop :=
  match t with
  | tvar _ a => pure_args a
  | tsym c a => keep _ c = true /\ pure_args a
  end
with pure_args {Γ Θ} (a : args Sym Γ Θ) : Prop :=
  match a with
  | anil => True
  | acons u a' => pure u /\ pure_args a'
  end.

Lemma itm_pure_mut :
  (forall Γ s (t : Terms.tm Sym Γ s), pure t -> forall Γ' (ρ : ren Γ Γ'), itm F t Γ' ρ = ren_tm t ρ) /\
  (forall Γ Θ (a : args Sym Γ Θ), pure_args a -> forall Γ' (ρ : ren Γ Γ'), iargs F a Γ' ρ = ren_args a ρ).
Proof.
  apply tm_args_ind.
  - intros Γ σ x a IH Hp Γ' ρ. rewrite itm_tvar, ren_tvar, IH by exact Hp. reflexivity.
  - intros Γ σ c a IH [Hc Hp] Γ' ρ. rewrite itm_tsym, Hkeep by exact Hc. rewrite vsubst_tsym, ren_tsym, IH by exact Hp.
    f_equal. apply vec_ext; intros τ x; unfold vget.
    rewrite aget_vsubst_args', aget_vid, vsubst_eta. reflexivity.
  - reflexivity.
  - intros Γ σ Θ u IHu a IHa [Hu Ha] Γ' ρ. rewrite iargs_acons, ren_args_acons, IHa by exact Ha.
    unfold itms. rewrite IHu by exact Hu. reflexivity.
Qed.

Lemma tr_pure {Γ s} (t : Terms.tm Sym Γ s) : pure t -> tr F t = t.
Proof. intros H. unfold tr. rewrite (proj1 itm_pure_mut _ _ t H). apply ren_id. Qed.

End Pure.

(** ** Interprétations de logiques *)

Section Logics.
Context {Srt : Type} {Sym1 Sym2 : spec Srt -> Type} (L1 : logic Sym1) (L2 : logic Sym2).
Local Notation P1 := (l_prop Sym1 L1).
Local Notation P2 := (l_prop Sym2 L2).

(** Une interprétation de L1 dans L2, avec un prédicat de relativisation
    D_σ par spécification. *)
Record slinterp := {
  sl_sig : sinterp Sym1 Sym2;
  sl_prop : P1 = P2;
  sl_rel : forall σ, form Sym2 P2 [σ]
}.

Context (F : slinterp).
Local Notation G := (sl_sig F).
Local Notation form1 := (form Sym1 P1).
Local Notation form2 := (form Sym2 P2).

Definition pcast {Γ} (t : Terms.tm Sym2 Γ P1) : form2 Γ :=
  match sl_prop F in _ = Q return Terms.tm Sym2 Γ Q with eq_refl => t end.

Definition ltr {Γ} (φ : form1 Γ) : form2 Γ := pcast (tr G φ).

(** D_σ(x) pour chaque variable x : σ de Λ, dans Λ ++ X. *)
Fixpoint rel_ext (Λ : ctx Srt) (X : ctx Srt) : list (form2 (Λ ++ X)) :=
  match Λ return list (form2 (Λ ++ X)) with
  | [] => []
  | σ :: Λ' => ren_tm (sl_rel F σ) (fun τ (z : var [σ] τ) => vl (Λ' ++ X) z) :: wk_list [σ] (rel_ext Λ' X)
  end.

Fixpoint rel_hyps (Γ : ctx Srt) : list (form2 Γ) :=
  match Γ return list (form2 Γ) with
  | [] => []
  | σ :: Γ0 => ren_tm (sl_rel F σ) (fun τ (z : var [σ] τ) => vl Γ0 z) :: wk_list [σ] (rel_hyps Γ0)
  end.

Definition jtr : translation L1 L2 := strans (fun Γ => Γ) (fun Γ => ltr) rel_hyps.

Definition slinterp_sound := sound jtr.

(** ** Traduction des règles *)

Definition tr_prem {Θ} (p : premise Sym1 P1 Θ) : premise Sym2 P2 Θ :=
  premx (P := P2) (p_ext p) (rel_ext (p_ext p) Θ ++ map ltr (p_hyps p)) (ltr (p_goal p)).

Definition tr_rule (r : drule Sym1 P1) : drule Sym2 P2 :=
  {| d_ctx := d_ctx r; d_prems := map tr_prem (d_prems r); d_concl := ltr (d_concl r) |}.

Lemma vsubst_cast {Q Q'} (e : Q = Q') {Θ Γ} (t : Terms.tm Sym2 Θ Q) (w : vec Sym2 Θ Γ) :
  match e in _ = R return Terms.tm Sym2 Γ R with eq_refl => vsubst t w end
  = vsubst (match e in _ = R return Terms.tm Sym2 Θ R with eq_refl => t end) w.
Proof. destruct e; reflexivity. Qed.

Lemma ren_cast {Q Q'} (e : Q = Q') {Γ Δ} (t : Terms.tm Sym2 Γ Q) (ξ : ren Γ Δ) :
  ren_tm (match e in _ = R return Terms.tm Sym2 Γ R with eq_refl => t end) ξ
  = match e in _ = R return Terms.tm Sym2 Δ R with eq_refl => ren_tm t ξ end.
Proof. destruct e; reflexivity. Qed.

Lemma conv_cast {Q Q'} (e : Q = Q') {Γ} (t u : Terms.tm Sym2 Γ Q) :
  conv (l_calc Sym2 L2) t u ->
  conv (l_calc Sym2 L2) (match e in _ = R return Terms.tm Sym2 Γ R with eq_refl => t end)
                        (match e in _ = R return Terms.tm Sym2 Γ R with eq_refl => u end).
Proof. destruct e; exact (fun H => H). Qed.

Lemma ltr_vsubst {Θ Γ} (φ : form1 Θ) (v : vec Sym1 Θ Γ) : ltr (vsubst φ v) = vsubst (ltr φ) (trv G v).
Proof. unfold ltr, pcast. rewrite tr_vsubst. apply vsubst_cast. Qed.

Lemma ltr_ren {Γ Δ} (φ : form1 Γ) (ξ : ren Γ Δ) : ltr (ren_tm φ ξ) = ren_tm (ltr φ) ξ.
Proof. unfold ltr, pcast. rewrite tr_ren, ren_cast. reflexivity. Qed.

Lemma wk_list_cons τ (Λ : ctx Srt) {X} (L : list (form2 X)) :
  wk_list [τ] (wk_list Λ L) = wk_list (τ :: Λ) L.
Proof.
  unfold wk_list; rewrite map_map; apply map_ext; intros χ.
  rewrite ren_ren; apply ren_ext; intros; reflexivity.
Qed.

Lemma rel_hyps_app Λ Γ : rel_hyps (Λ ++ Γ) = rel_ext Λ Γ ++ wk_list Λ (rel_hyps Γ).
Proof.
  induction Λ as [|σ Λ IH].
  - cbn [app rel_ext]. unfold wk_list. rewrite (map_ext _ (fun h => h)); [symmetry; apply map_id|].
    intros h. apply ren_id.
  - cbn [app rel_hyps rel_ext]. rewrite IH. unfold wk_list at 1. rewrite map_app.
    rewrite <- (wk_list_cons σ Λ (rel_hyps Γ)). reflexivity.
Qed.

Lemma rel_ext_vup Λ {A B} (w : vec Sym2 A B) :
  vsubst_list (rel_ext Λ A) (vup Λ w) = rel_ext Λ B.
Proof.
  induction Λ as [|σ Λ IH]; [reflexivity|]. cbn [rel_ext]. unfold vsubst_list; cbn [map]. f_equal.
  - etransitivity; [apply vsubst_ren|]. etransitivity; [|symmetry; apply ren_as_vsubst].
    reflexivity.
  - unfold wk_list. rewrite map_map. rewrite <- IH. unfold vsubst_list. rewrite map_map.
    apply map_ext; intros r. rewrite vsubst_ren, ren_vsubst. f_equal. apply vec_ext; intros τ x. unfold vget.
    rewrite aget_vpre. unfold vren at 1. rewrite aget_vmap. unfold wk at 1. cbn [vr].
    vcase x.
    + change (vs (vl A z)) with (vl A (vs (σ := τ) (τ := σ) z)). unfold vup.
      etransitivity; [exact (aget_vcat_l (Θ := σ :: Λ) (vs z) _ _)|]. rewrite aget_etas.
      rewrite aget_vcat_l, aget_etas, eta_ren. reflexivity.
    + change (vs (vr Λ z)) with (vr (σ :: Λ) z). unfold vup.
      etransitivity; [exact (aget_vcat_r (σ :: Λ) z _ _)|].
      rewrite aget_vcat_r. unfold vren. rewrite !aget_vmap, ren_tms_ren.
      apply ren_tms_ext; intros; reflexivity.
Qed.

Lemma deriv_ren2 {Γ Ξ φ} Δ (ξ : ren Γ Δ) :
  deriv (l_calc Sym2 L2) P2 (l_rules Sym2 L2) Γ Ξ φ ->
  deriv (l_calc Sym2 L2) P2 (l_rules Sym2 L2) Δ (map (fun χ => ren_tm χ ξ) Ξ) (ren_tm φ ξ).
Proof.
  intros H. rewrite ren_as_vsubst.
  replace (map (fun χ => ren_tm χ ξ) Ξ) with (vsubst_list Ξ (vpre ξ (vid Δ))).
  - apply deriv_subst, H.
  - unfold vsubst_list; apply map_ext; intros; symmetry; apply ren_as_vsubst.
Qed.

Local Notation "Γ ; Ξ ⊢₂ φ" := (provable L2 Γ Ξ φ) (at level 70).

(** La règle traduite de r est admissible dans L2, pour les contextes de Q. *)
Definition tr_rule_adm (Q : ctx Srt -> Prop) (r : drule Sym1 P1) : Prop :=
  forall Γ, Q Γ -> forall (Ξ : list (form2 Γ)) (w : vec Sym2 (d_ctx r) Γ),
    (forall p, In p (d_prems (tr_rule r)) ->
       (p_ext p ++ Γ) ; inst_hyps p w (rel_hyps Γ ++ Ξ) ⊢₂ inst_goal p w) ->
    Γ ; rel_hyps Γ ++ Ξ ⊢₂ vsubst (d_concl (tr_rule r)) w.

Lemma tr_rule_adm_rule Q r : (exists j, l_rules Sym2 L2 j = tr_rule r) -> tr_rule_adm Q r.
Proof. intros [j Hj] Γ _ Ξ w Hp. eapply d_rule_eq; [exact Hj|exact Hp]. Qed.

Lemma incl_reorder {A} (R W V X : list A) : incl ((R ++ W) ++ (V ++ X)) ((R ++ V) ++ (W ++ X)).
Proof. intros a Ha; rewrite !in_app_iff in *; tauto. Qed.

Theorem interp_sound_on (Q : ctx Srt -> Prop) :
  (forall Γ s (t u : Terms.tm Sym1 Γ s), conv (l_calc Sym1 L1) t u -> conv (l_calc Sym2 L2) (tr G t) (tr G u)) ->
  (forall i p Γ, In p (d_prems (l_rules Sym1 L1 i)) -> Q Γ -> Q (p_ext p ++ Γ)) ->
  (forall i, tr_rule_adm Q (l_rules Sym1 L1 i)) ->
  forall Γ Ξ φ, Q Γ -> provable L1 Γ Ξ φ -> valid L2 (jtr (mkJ Γ Ξ φ)).
Proof.
  intros HC HQ HR Γ Ξ φ HΓ H. unfold valid, provable in *; cbn [j_ctx j_hyps j_goal] in *.
  revert HΓ. induction H as [Γ Ξ φ Hin|Γ Ξ φ ψ Hc H IH|Γ Ξ i v Hp IH]; intros HΓ.
  - apply d_ax. apply in_or_app; right. exact (in_map ltr _ _ Hin).
  - eapply d_conv; [|exact (IH HΓ)]. unfold ltr, pcast. apply conv_cast, HC, Hc.
  - unfold jtr, strans; cbn [j_ctx j_hyps j_goal].
    rewrite ltr_vsubst.
    change (vsubst (ltr (d_concl (l_rules Sym1 L1 i))) (trv G v))
      with (vsubst (d_concl (tr_rule (l_rules Sym1 L1 i))) (trv G v)).
    apply (HR i Γ HΓ (map ltr Ξ) (trv G v)).
    intros p' Hp'. cbn [tr_rule d_prems] in Hp'. apply in_map_iff in Hp' as (p & <- & Hin).
    specialize (IH p Hin (HQ i p Γ Hin HΓ)).
    unfold valid, provable, jtr, strans, inst_hyps, inst_goal in IH |- *.
    cbn [j_ctx j_hyps j_goal tr_prem premx p_ext p_hyps p_goal] in IH |- *.
    rewrite ltr_vsubst, trv_vup in IH.
    eapply deriv_weaken; [exact IH|].
    rewrite rel_hyps_app, !map_app. unfold vsubst_list, wk_list. rewrite !map_app, !map_map.
    intros x Hx. rewrite !in_app_iff in Hx |- *.
    destruct Hx as [[Hx|Hx]|[Hx|Hx]].
    + left; left. rewrite <- (rel_ext_vup (p_ext p) (trv G v)) in Hx. exact Hx.
    + right; left. exact Hx.
    + left; right. apply in_map_iff in Hx as (g & <- & Hg). rewrite ltr_vsubst, trv_vup.
      exact (in_map (fun g => vsubst (ltr g) (vup (p_ext p) (trv G v))) _ _ Hg).
    + right; right. apply in_map_iff in Hx as (g & <- & Hg). rewrite ltr_ren.
      exact (in_map (fun g => ren_tm (ltr g) (wk (p_ext p))) _ _ Hg).
Qed.

End Logics.

Arguments sl_sig {Srt Sym1 Sym2 L1 L2} s : rename.
Arguments sl_prop {Srt Sym1 Sym2 L1 L2} s : rename.
Arguments sl_rel {Srt Sym1 Sym2 L1 L2} s σ : rename.
Arguments ltr {Srt Sym1 Sym2 L1 L2} F {Γ} φ.
Arguments rel_ext {Srt Sym1 Sym2 L1 L2} F Λ X.
Arguments rel_hyps {Srt Sym1 Sym2 L1 L2} F Γ.
Arguments jtr {Srt Sym1 Sym2 L1 L2} F j.
Arguments tr_prem {Srt Sym1 Sym2 L1 L2} F {Θ} p.
Arguments tr_rule {Srt Sym1 Sym2 L1 L2} F r.
Arguments tr_rule_adm {Srt Sym1 Sym2 L1 L2} F Q r.
