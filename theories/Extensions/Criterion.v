(** * Critère schématique général de correction

    On étend [srule_sound] (dans [Soundness.v]) aux règles dont les
    prémisses étendent le contexte de termes (∀I, ∃E, récurrence…), avec
    les hypothèses de relativisation.

    La **traduction d'une règle** r de L1 ([tr_rule]) est la règle de L2
    de contexte ⟦Θ⟧ dont :
    - chaque prémisse d'extension Λ devient une prémisse d'extension ⟦Λ⟧ ;
      ses hypothèses sont D(x) pour les nouvelles variables x de Λ
      ([rel_ext]), suivies des hypothèses traduites ; son but est le but
      traduit ;
    - la conclusion est la conclusion traduite.

    Les formules d'une prémisse vivent dans Λ ++ Θ ; on les traduit dans
    ⟦Λ⟧ ++ ⟦Θ⟧ ([trx]). Les dérivations sont transportées de ⟦Λ ++ Γ⟧ à
    ⟦Λ⟧ ++ ⟦Γ⟧ par le renommage [capp].

    Théorème [rule_tr_sound] : si la traduction d'une règle de L1 est une
    règle de L2, ses instances traduites sont admissibles dans L2. *)

From Stdlib Require Import List.
Import ListNotations.
From SF.Syntax Require Import Spec Terms Renaming Traversal Eta Composition Vectors.
From SF.Calculus Require Import System Rules.
From SF.Logic Require Import Judgment.
From SF.Extensions Require Import Conservativity Interpretation Commute Soundness.

(** ** Traduction des η-expansés *)

Section Eta.
Context {S1 S2 : Type} {Sym1 : spec S1 -> Type} {Sym2 : spec S2 -> Type} (F : interp Sym1 Sym2).

Local Notation fs := (i_srt F).
Local Notation sm := (smap fs).
Local Notation cm := (cmap fs).
Local Notation vmap1 Γ Γ' := (forall σ, var Γ σ -> var Γ' (sm σ)).

Definition eta_tr_prop (σ : spec S1) : Prop :=
  forall Γ Γ' (ρ : vmap1 Γ Γ') (x : var Γ σ), itms F (eta σ x) Γ' ρ = eta (sm σ) (ρ σ x).

Lemma iargs_etas D (IH : forall σ, var D σ -> eta_tr_prop σ) :
  forall Ξ Ξ' (f : forall τ, var D τ -> var Ξ τ) (ρ' : vmap1 Ξ Ξ') (g : forall τ, var (cm D) τ -> var Ξ' τ),
    (forall τ (z : var D τ), ρ' τ (f τ z) = g (sm τ) (cvar fs z)) ->
    iargs F (etas D f) Ξ' ρ' = etas (cm D) g.
Proof.
  induction D as [|τ D IHD]; intros Ξ Ξ' f ρ' g H; [reflexivity|].
  cbn [etas]. rewrite iargs_acons. cbn [cmap map].
  rewrite (IH τ vz), (H τ vz). cbn [etas cvar]. f_equal.
  apply IHD; [intros σ z; exact (IH σ (vs z))|]. intros τ' z; exact (H τ' (vs z)).
Qed.

Lemma itms_eta σ : eta_tr_prop σ.
Proof.
  induction σ as [D c IH] using spec_rect'. intros Γ Γ' ρ x.
  rewrite eta_Spec, itms_Spec, itm_tvar, vlift_vr.
  change (eta (Sym := Sym2) (sm (Spec D c)) (ρ _ x)) with (eta (Sym := Sym2) (Spec (cm D) (fs c)) (ρ _ x)).
  rewrite eta_Spec. f_equal.
  apply iargs_etas; [exact IH|]. intros τ z. apply vlift_vl.
Qed.

End Eta.

Section Criterion.
Context {S1 S2 : Type} {Sym1 : spec S1 -> Type} {Sym2 : spec S2 -> Type}.
Context (L1 : logic Sym1) (L2 : logic Sym2) (F : linterp L1 L2).

Local Notation P1 := (l_prop Sym1 L1).
Local Notation P2 := (l_prop Sym2 L2).
Local Notation G := (li_sig F).
Local Notation fs := (i_srt G).
Local Notation sm := (smap fs).
Local Notation cm := (cmap fs).
Local Notation form1 := (form Sym1 P1).
Local Notation form2 := (form Sym2 P2).
Local Notation cv := (fun σ x => cvar fs x).

(** ** Définitions *)

(** Traduction d'une formule de Λ ++ Θ dans ⟦Λ⟧ ++ ⟦Θ⟧. *)
Definition trx (Λ : ctx S1) {Θ} (φ : form1 (Λ ++ Θ)) : form2 (cm Λ ++ cm Θ) :=
  pcast L1 L2 F (itm G φ (cm Λ ++ cm Θ) (vlift fs Λ cv)).

(** Hypothèses de relativisation des variables de Λ, dans ⟦Λ⟧ ++ X. *)
Fixpoint rel_ext (Λ : ctx S1) (X : ctx S2) : list (form2 (cm Λ ++ X)) :=
  match Λ return list (form2 (cm Λ ++ X)) with
  | [] => []
  | σ :: Λ' => ren_tm (li_rel F σ) (fun τ (z : var [sm σ] τ) => vl (cm Λ' ++ X) z)
               :: wk_list [sm σ] (rel_ext Λ' X)
  end.

Definition tr_prem {Θ} (p : premise Sym1 P1 Θ) : premise Sym2 P2 (cm Θ) :=
  premx (P := P2) (cm (p_ext p))
    (rel_ext (p_ext p) (cm Θ) ++ map (trx (p_ext p)) (p_hyps p))
    (trx (p_ext p) (p_goal p)).

Definition tr_rule (r : drule Sym1 P1) : drule Sym2 P2 :=
  {| d_ctx := cm (d_ctx r);
     d_prems := map tr_prem (d_prems r);
     d_concl := ltr F (d_concl r) |}.

(** ** Renommage des dérivations *)

Lemma deriv_ren {Γ Ξ φ} Δ (ξ : ren Γ Δ) :
  deriv (l_calc Sym2 L2) P2 (l_rules Sym2 L2) Γ Ξ φ ->
  deriv (l_calc Sym2 L2) P2 (l_rules Sym2 L2) Δ (map (fun χ => ren_tm χ ξ) Ξ) (ren_tm φ ξ).
Proof.
  intros H. rewrite ren_as_vsubst.
  replace (map (fun χ => ren_tm χ ξ) Ξ) with (vsubst_list Ξ (vpre ξ (vid Δ))).
  - apply deriv_subst, H.
  - unfold vsubst_list; apply map_ext; intros; symmetry; apply ren_as_vsubst.
Qed.

(** ** Lemmes de transport *)

Lemma ren_cast {Q Q'} (e : Q = Q') {Γ Δ} (t : Terms.tm Sym2 Γ Q) (ξ : ren Γ Δ) :
  ren_tm (match e in _ = R return Terms.tm Sym2 Γ R with eq_refl => t end) ξ
  = match e in _ = R return Terms.tm Sym2 Δ R with eq_refl => ren_tm t ξ end.
Proof. destruct e; reflexivity. Qed.

Lemma cast_congr {Q Q'} (e : Q = Q') {Γ} (t u : Terms.tm Sym2 Γ Q) :
  t = u ->
  match e in _ = R return Terms.tm Sym2 Γ R with eq_refl => t end
  = match e in _ = R return Terms.tm Sym2 Γ R with eq_refl => u end.
Proof. intros ->; reflexivity. Qed.

(** Une formule affaiblie, traduite puis renommée. *)
Lemma ltr_wk_capp Λ {Γ} (χ : form1 Γ) :
  ren_tm (ltr F (ren_tm χ (wk Λ))) (capp fs Λ) = ren_tm (ltr F χ) (wk (cm Λ)).
Proof.
  unfold ltr, pcast. rewrite !ren_cast. apply cast_congr. unfold tr.
  rewrite (proj1 (itm_ren_mut G)), !(proj1 (ren_itm_mut G)).
  apply itm_ext; intros σ x. unfold wk. rewrite capp_cvar, vlift_vr. reflexivity.
Qed.

(** Le lemme principal : instancier sous Λ, traduire, renommer, c'est
    traduire sous Λ puis instancier par le vecteur traduit relevé. *)
Lemma ltr_vup_capp Λ {Θ Γ} (g : form1 (Λ ++ Θ)) (v : vec Sym1 Θ Γ) :
  ren_tm (ltr F (vsubst g (vup Λ v))) (capp fs Λ) = vsubst (trx Λ g) (vup (cm Λ) (trv G v)).
Proof.
  unfold ltr, trx, pcast. rewrite ren_cast, <- vsubst_cast. apply cast_congr. unfold tr.
  rewrite (proj1 (ren_itm_mut G)).
  rewrite (itm_ext G _ _ _ (vlift fs Λ cv)) by (intros σ x; apply capp_cvar).
  apply itm_vsubst. intros σ x. vcase x.
  - rewrite vlift_vl. unfold vup. rewrite !aget_vcat_l, !aget_etas, itms_eta, vlift_vl. reflexivity.
  - rewrite vlift_vr. unfold vup. rewrite !aget_vcat_r. unfold vren. rewrite !aget_vmap.
    unfold trv. rewrite aget_iargs, itms_wk. reflexivity.
Qed.

(** Affaiblir par [τ] puis relever sous τ :: Λ. *)
Lemma vsubst_wk_vup τ (Λ : ctx S2) {A B} (r : form2 (Λ ++ A)) (w : vec Sym2 A B) :
  vsubst (ren_tm r (wk [τ])) (vup (τ :: Λ) w) = ren_tm (vsubst r (vup Λ w)) (wk [τ]).
Proof.
  rewrite vsubst_ren, ren_vsubst. f_equal. apply vec_ext; intros σ x. unfold vget.
  rewrite aget_vpre. unfold vren at 1. rewrite aget_vmap. unfold wk at 1. cbn [vr].
  vcase x.
  - change (vs (vl A z)) with (vl A (vs (σ := σ) (τ := τ) z)). unfold vup.
    etransitivity; [exact (aget_vcat_l (Θ := τ :: Λ) (vs z) _ _)|]. rewrite aget_etas.
    rewrite aget_vcat_l, aget_etas, eta_ren. reflexivity.
  - change (vs (vr Λ z)) with (vr (τ :: Λ) z). unfold vup.
    etransitivity; [exact (aget_vcat_r (τ :: Λ) z _ _)|].
    rewrite aget_vcat_r. unfold vren. rewrite !aget_vmap, ren_tms_ren.
    apply ren_tms_ext; intros; reflexivity.
Qed.

(** Les hypothèses de relativisation sont stables par substitution sous Λ. *)
Lemma rel_ext_vup Λ {A B} (w : vec Sym2 A B) :
  vsubst_list (rel_ext Λ A) (vup (cm Λ) w) = rel_ext Λ B.
Proof.
  induction Λ as [|σ Λ IH]; [reflexivity|]. cbn [rel_ext]. unfold vsubst_list; cbn [map]. f_equal.
  - etransitivity; [apply vsubst_ren|]. etransitivity; [|symmetry; apply ren_as_vsubst].
    reflexivity.
  - unfold wk_list. rewrite map_map. rewrite <- IH. unfold vsubst_list. rewrite map_map.
    apply map_ext; intros r. exact (vsubst_wk_vup (sm σ) (cm Λ) r w).
Qed.

Lemma wk_list_cons τ (Λ : ctx S2) {X} (L : list (form2 X)) :
  wk_list [τ] (wk_list Λ L) = wk_list (τ :: Λ) L.
Proof.
  unfold wk_list; rewrite map_map; apply map_ext; intros χ.
  rewrite ren_ren; apply ren_ext; intros; reflexivity.
Qed.

(** Les hypothèses de relativisation de Λ ++ Γ, renommées. *)
Lemma rel_hyps_capp Λ Γ :
  map (fun h : form2 (cm (Λ ++ Γ)) => ren_tm h (capp fs Λ)) (rel_hyps F (Λ ++ Γ))
  = rel_ext Λ (cm Γ) ++ wk_list (cm Λ) (rel_hyps F Γ).
Proof.
  induction Λ as [|σ Λ IH].
  - cbn [app rel_ext]. change (cm []) with (@nil (spec S2)). rewrite wk_list_nil.
    rewrite (map_ext _ (fun h => h)); [apply map_id|]. intros h. apply ren_id.
  - cbn [app rel_hyps rel_ext map]. f_equal.
    + rewrite ren_ren. apply ren_ext. refine (var_inv _ _ _); [reflexivity|].
      try (intros τ y; destruct (var_nil y)).
    + transitivity (wk_list [sm σ] (rel_ext Λ (cm Γ) ++ wk_list (cm Λ) (rel_hyps F Γ)));
        [|unfold wk_list at 1; rewrite map_app; f_equal; apply wk_list_cons].
      rewrite <- IH. unfold wk_list; rewrite !map_map. apply map_ext; intros h.
      rewrite !ren_ren. apply ren_ext; intros; reflexivity.
Qed.

Lemma incl_reorder {A} (R W V X : list A) : incl ((R ++ W) ++ (V ++ X)) ((R ++ V) ++ (W ++ X)).
Proof. intros a Ha; rewrite !in_app_iff in *; tauto. Qed.

(** Les hypothèses de la prémisse instanciée, renommées, sont parmi
    celles de la prémisse traduite instanciée. *)
Lemma hyps_incl Λ {Θ Γ} (hs : list (form1 (Λ ++ Θ))) (v : vec Sym1 Θ Γ) (Ξ : list (form1 Γ)) :
  incl (map (fun χ : form2 (cm (Λ ++ Γ)) => ren_tm χ (capp fs Λ))
            (rel_hyps F (Λ ++ Γ) ++ map (ltr F) (vsubst_list hs (vup Λ v) ++ wk_list Λ Ξ)))
       (vsubst_list (rel_ext Λ (cm Θ) ++ map (trx Λ) hs) (vup (cm Λ) (trv G v))
        ++ wk_list (cm Λ) (rel_hyps F Γ ++ map (ltr F) Ξ)).
Proof.
  rewrite map_app, rel_hyps_capp. intros x Hx. rewrite !in_app_iff in Hx.
  unfold vsubst_list at 1; unfold wk_list at 1. rewrite !map_app.
  destruct Hx as [[H|H]|H]; [| |rewrite !map_app in H; apply in_app_or in H; destruct H as [H|H]].
  - apply in_or_app; left; apply in_or_app; left. rewrite <- (rel_ext_vup Λ (trv G v)) in H. exact H.
  - apply in_or_app; right; apply in_or_app; left. exact H.
  - apply in_map_iff in H as (y & <- & Hy). apply in_map_iff in Hy as (z & <- & Hz).
    unfold vsubst_list in Hz. apply in_map_iff in Hz as (g & <- & Hg).
    rewrite ltr_vup_capp. apply in_or_app; left; apply in_or_app; right. rewrite map_map.
    exact (in_map (fun g => vsubst (trx Λ g) (vup (cm Λ) (trv G v))) _ _ Hg).
  - apply in_map_iff in H as (y & <- & Hy). apply in_map_iff in Hy as (z & <- & Hz).
    unfold wk_list in Hz. apply in_map_iff in Hz as (χ & <- & Hχ).
    rewrite ltr_wk_capp. apply in_or_app; right; apply in_or_app; right. rewrite map_map.
    exact (in_map (fun χ => ren_tm (ltr F χ) (wk (cm Λ))) _ _ Hχ).
Qed.

(** ** Le critère *)

Theorem rule_tr_sound (r : drule Sym1 P1) :
  (exists j, l_rules Sym2 L2 j = tr_rule r) -> rule_sound L1 L2 F r.
Proof.
  intros [j Hj] Γ Ξ v Hp. unfold valid, provable, jtr, strans; cbn [j_ctx j_hyps j_goal].
  rewrite ltr_vsubst.
  change (vsubst (ltr F (d_concl r)) (trv G v)) with (vsubst (d_concl (tr_rule r)) (trv G v)).
  eapply d_rule_eq; [exact Hj|].
  intros p' Hp'. cbn [tr_rule d_prems] in Hp'. apply in_map_iff in Hp' as (p & <- & Hin).
  specialize (Hp p Hin).
  unfold valid, provable, jtr, strans, inst_hyps, inst_goal in Hp |- *.
  cbn [j_ctx j_hyps j_goal tr_prem premx p_ext p_hyps p_goal] in Hp |- *.
  apply (deriv_ren _ (capp fs (p_ext p))) in Hp.
  rewrite ltr_vup_capp in Hp.
  eapply deriv_weaken; [exact Hp|].
  apply hyps_incl.
Qed.

End Criterion.

Arguments trx {S1 S2 Sym1 Sym2 L1 L2} F Λ {Θ} φ.
Arguments rel_ext {S1 S2 Sym1 Sym2 L1 L2} F Λ X.
Arguments tr_prem {S1 S2 Sym1 Sym2 L1 L2} F {Θ} p.
Arguments tr_rule {S1 S2 Sym1 Sym2 L1 L2} F r.
