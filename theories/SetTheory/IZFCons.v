(** * Conservativité de IZF⁻ε sur IZF (étape 1)

    Toute dérivation de IZF⁻ε dans un contexte d'ensembles se traduit en
    une dérivation de IZF ([izfm_sound]), par récurrence sur la
    dérivation : chaque règle traduite est admissible dans IZF. Pour une
    formule de L_IZF, la traduction est équivalente à la lecture directe
    ([pcanon_tr]), d'où la conservativité ([izfm_conservative]). *)

From Stdlib Require Import List.
Import ListNotations.
From SF.Syntax Require Import Spec Terms Renaming Eta Composition Vectors.
From SF.Calculus Require Import System Rules.
From SF.Logic Require Import Judgment Propositional.
From SF.Functional Require Import Arrow Graded.
From SF.Quantifiers Require Import Quant Order.
From SF.SetTheory Require Import Sets IZFe IZF IZFTr IZFLog IZFVal IZFOmega IZFTrSem IZFSound IZFSchema.

Local Notation ι a := (Spec [] a).

(** ** Le système de calcul vide *)

Lemma conv_C_eq : (forall Γ s (t t' : tm Γ s), gconv (fun e : Empty_set => match e with end) Γ s t t' -> t = t') /\
                  (forall Γ Θ (a a' : args isym Γ Θ), gargs (fun e : Empty_set => match e with end) Γ Θ a a' -> a = a').
Proof.
  apply gconv_gargs_ind; intros; subst; try reflexivity; try contradiction; try destruct i.
Qed.

(** ** Prémisses *)

Lemma map_tr_wk D {Γ} (Ξ : list (form Γ)) : map tr (wk_list D Ξ) = wk_list D (map tr Ξ).
Proof. unfold wk_list. rewrite !map_map. apply map_ext; intros χ. apply tr_ren. Qed.

Section Rules.
Context {Γ : ctx isort} (HΓ : vctx Γ) (Ξ : list (form Γ)).

Definition PH {Θ} (ps : list (premise isym Pr Θ)) (v : vec isym Θ Γ) : Prop :=
  forall p, In p ps -> vctx (p_ext p ++ Γ) -> IZF (p_ext p ++ Γ) (map tr (inst_hyps p v Ξ)) (tr (inst_goal p v)).

Lemma prem0 {Θ} (ps : list (premise isym Pr Θ)) (v : vec isym Θ Γ) hs g :
  PH ps v -> In (prem hs g) ps -> IZF Γ (map tr (vsubst_list hs v ++ Ξ)) (tr (vsubst g v)).
Proof.
  intros H Hin. specialize (H _ Hin HΓ). unfold inst_hyps, inst_goal in H.
  cbn [p_ext p_hyps p_goal prem] in H. rewrite vup_nil, wk_list_nil in H. exact H.
Qed.

Lemma prem1 {Θ} (ps : list (premise isym Pr Θ)) (v : vec isym Θ Γ) hs g :
  PH ps v -> In (premx [ι V] hs g) ps ->
  IZF (ι V :: Γ) (map tr (vsubst_list hs (vup [ι V] v)) ++ wk_list [ι V] (map tr Ξ)) (tr (vsubst g (vup [ι V] v))).
Proof.
  intros H Hin. specialize (H _ Hin (vctx_V HΓ)). unfold inst_hyps, inst_goal in H.
  cbn [p_ext p_hyps p_goal premx] in H. rewrite map_app, map_tr_wk in H. exact H.
Qed.

Lemma vI {Θ} (A B : form Θ) (v : vec isym Θ Γ) : vsubst (Imp A B) v = Imp (vsubst A v) (vsubst B v).
Proof. apply vsubst_Bin. Qed.
Lemma vA {Θ} (A B : form Θ) (v : vec isym Θ Γ) : vsubst (And A B) v = And (vsubst A v) (vsubst B v).
Proof. apply vsubst_Bin. Qed.
Lemma vO {Θ} (A B : form Θ) (v : vec isym Θ Γ) : vsubst (Or A B) v = Or (vsubst A v) (vsubst B v).
Proof. apply vsubst_Bin. Qed.

Ltac v2d v := rewrite (args_eta v), (args_eta (atl v)), (args_nil (atl (atl v))) in *.
Ltac v1d v := rewrite (args_eta v), (args_nil (atl v)) in *.
Ltac v3d v := rewrite (args_eta v), (args_eta (atl v)), (args_eta (atl (atl v))), (args_nil (atl (atl (atl v)))) in *.

Ltac psimp := cbn [app vsubst_list map] in *; rewrite ?vI, ?vA, ?vO, ?(vsubst_mvar (Sym := isym) (P := Pr)) in *; cbn [aget ahd atl vsubst_list map app] in *.

Lemma ipc_sound (i : _) (v : vec isym (d_ctx (ipc_rules (Sym := isym) (P := Pr) i)) Γ) :
  PH (d_prems (ipc_rules i)) v -> IZF Γ (map tr Ξ) (tr (vsubst (d_concl (ipc_rules i)) v)).
Proof.
  intros H.
  destruct i as [[|]|[[| |]|[[| |]|[[]|[]]]]]; cbn [ipc_rules rsum imp_rules and_rules or_rules top_rules bot_rules
    d_ctx d_prems d_concl] in v, H |- *.
  - (* ImpI *)
    pose proof (prem0 _ v _ _ H (or_introl eq_refl)) as K. clear H. unfold Θ2 in v. v2d v. psimp.
    zap zimp_I. exact K.
  - (* ImpE *)
    pose proof (prem0 _ v _ _ H (or_introl eq_refl)) as K1.
    pose proof (prem0 _ v _ _ H (or_intror (or_introl eq_refl))) as K2. clear H. unfold Θ2 in v. v2d v. psimp.
    exact (zimp_E _ _ _ K1 K2).
  - (* AndI *)
    pose proof (prem0 _ v _ _ H (or_introl eq_refl)) as K1.
    pose proof (prem0 _ v _ _ H (or_intror (or_introl eq_refl))) as K2. clear H. unfold Θ2 in v. v2d v. psimp.
    exact (zand_I _ _ _ K1 K2).
  - pose proof (prem0 _ v _ _ H (or_introl eq_refl)) as K. clear H. unfold Θ2 in v. v2d v. psimp.
    exact (zand_E1 _ _ _ K).
  - pose proof (prem0 _ v _ _ H (or_introl eq_refl)) as K. clear H. unfold Θ2 in v. v2d v. psimp.
    exact (zand_E2 _ _ _ K).
  - pose proof (prem0 _ v _ _ H (or_introl eq_refl)) as K. clear H. unfold Θ2 in v. v2d v. psimp.
    exact (zor_I1 _ _ _ K).
  - pose proof (prem0 _ v _ _ H (or_introl eq_refl)) as K. clear H. unfold Θ2 in v. v2d v. psimp.
    exact (zor_I2 _ _ _ K).
  - (* OrE *)
    pose proof (prem0 _ v _ _ H (or_introl eq_refl)) as K1.
    pose proof (prem0 _ v _ _ H (or_intror (or_introl eq_refl))) as K2.
    pose proof (prem0 _ v _ _ H (or_intror (or_intror (or_introl eq_refl)))) as K3. clear H. unfold Θ3 in v. v3d v. psimp.
    exact (zor_E _ _ _ _ K1 K2 K3).
  - zap (top_I ZC Pr RIZF).
  - pose proof (prem0 _ v _ _ H (or_introl eq_refl)) as K. clear H. unfold Θ1 in v. v1d v. psimp.
    exact (bot_E ZC Pr RIZF _ _ K).
Qed.

Lemma zex_E_eq {Δ} (Ψ : list (zform Δ)) (φ φ' : zform (ι V :: Δ)) (χ : zform Δ) χ' :
  φ' = φ -> χ' = ren_tm χ (wk [ι V]) ->
  IZF Δ Ψ (zEx φ) -> IZF (ι V :: Δ) (φ' :: wk_list [ι V] Ψ) χ' -> IZF Δ Ψ χ.
Proof. intros -> -> H1 H2. exact (zex_E _ _ _ H1 H2). Qed.

Lemma quant_sound (i : _) (v : vec isym (d_ctx (quant_rules (Sym := isym) (P := Pr) (n := 1) (p := 1) i)) Γ) :
  PH (d_prems (quant_rules i)) v -> IZF Γ (map tr Ξ) (tr (vsubst (d_concl (quant_rules i)) v)).
Proof.
  intros H.
  destruct i as [[[s h] []]|[[[s h] []]|[[s h] []]]]; (destruct s; [|exfalso; exact (Pr_not_q h)]);
    cbn [quant_rules rsum qall_rules qex_rules qeq_rules all_rules ex_rules eq_rules mkr projT1 fst snd
         d_ctx d_prems d_concl] in v, H |- *; unfold Quant.All, Quant.Ex, Quant.Eq in *.
  - (* AllI *)
    pose proof (prem1 _ v _ _ H (or_introl eq_refl)) as K. clear H. cbn [vsubst_list map app] in K.
    refine (eq_rect_r (fun f => IZF Γ (map tr Ξ) (tr f)) _ (vsubst_Qnt_eta _ vz v)). zap zall_I.
    exact (eq_rect _ (fun f => IZF _ _ (tr f)) K _ (vsubst_eta_up [ι V] Pr vz v)).
  - (* AllE *)
    pose proof (prem0 _ v _ _ H (or_introl eq_refl)) as K. clear H. cbn [vsubst_list map app] in K.
    pose proof (eq_rect _ (fun f => IZF Γ (map tr Ξ) (tr f)) K _ (vsubst_Qnt_eta _ vz v)) as K'. clear K.
    rewrite vsubst_app1. v2d v. cbn [aget ahd atl] in *. exact (allE_sound _ _ _ HΓ K').
  - (* ExI *)
    pose proof (prem0 _ v _ _ H (or_introl eq_refl)) as K. clear H. cbn [vsubst_list map app] in K.
    rewrite vsubst_app1 in K.
    refine (eq_rect_r (fun f => IZF Γ (map tr Ξ) (tr f)) _ (vsubst_Qnt_eta _ vz v)). v2d v. cbn [aget ahd atl] in *. exact (exI_sound _ _ _ HΓ K).
  - (* ExE *)
    pose proof (prem0 _ v _ _ H (or_introl eq_refl)) as K1.
    pose proof (prem1 _ v _ _ H (or_intror (or_introl eq_refl))) as K2. clear H.
    cbn [vsubst_list map app] in K1, K2.
    pose proof (eq_rect _ (fun f => IZF Γ (map tr Ξ) (tr f)) K1 _ (vsubst_Qnt_eta _ vz v)) as K1'. clear K1.
    rewrite vsubst_var0.
    refine (zex_E_eq _ _ _ _ _ _ _ K1' K2).
    + exact (f_equal (@tr (ι V :: Γ)) (vsubst_eta_up [ι V] Pr vz v)).
    + transitivity (@tr (ι V :: Γ) (aget (vs (vs vz)) (vup [ι V] v))); [exact (f_equal (@tr (ι V :: Γ)) (vsubst_var0 _ _))|].
      transitivity (@tr (ι V :: Γ) (ren_tms (σ := ι Pr) (aget (vs vz) v) (wk [ι V]))); [exact (f_equal (@tr (ι V :: Γ)) (aget_vup_vs (Sg := isym) (Θ := [σP; ι Pr]) (vs vz) v))|].
      rewrite ren_tms_nil. apply tr_ren.
  - (* EqR *)
    clear H. rewrite vsubst_tsym2, vsubst_var0. exact (eqR_sound _ _ HΓ).
  - (* EqS *)
    pose proof (prem0 _ v _ _ H (or_introl eq_refl)) as K1.
    pose proof (prem0 _ v _ _ H (or_intror (or_introl eq_refl))) as K2. clear H.
    cbn [vsubst_list map app] in K1, K2.
    rewrite vsubst_tsym2, !vsubst_var0 in K1. rewrite vsubst_app1 in K2.
    rewrite vsubst_app1.
    v3d v. cbn [aget ahd atl] in *. exact (eqS_sound _ _ _ _ HΓ K1 K2).
Qed.

Lemma closed_ax n (χ : form (Vn n ++ [])) (ts : vec isym (Vn n) Γ) :
  IZF [] [] (tr (Cl n χ)) -> IZF Γ (map tr Ξ) (tr (vsubst χ (vcat (Vn n) ts anil))).
Proof. intros H. apply (closure_inst n χ ts anil _ HΓ). apply closed_lift, H. Qed.

Lemma ax_sound (a : izfm_idx) (v : vec isym (d_ctx (izfm_rules a)) Γ) :
  IZF Γ (map tr Ξ) (tr (vsubst (d_concl (izfm_rules a)) v)).
Proof.
  destruct a; cbn [izfm_rules ax d_ctx] in v.
  - v2d v. exact (closed_ax 2 _ _ ax_mem0).
  - v2d v. exact (closed_ax 2 _ _ ax_sub0).
  - v2d v. exact (closed_ax 2 _ _ ax_eqv0).
  - v3d v. exact (closed_ax 3 _ _ ax_pair0).
  - v2d v. exact (closed_ax 2 _ _ ax_union0).
  - v2d v. exact (closed_ax 2 _ _ ax_power0).
  - apply coll_sound, HΓ.
  - apply sep_sound, HΓ.
  - v1d v. exact (closed_ax 1 _ _ ax_empty0).
  - v1d v. exact (closed_ax 1 _ _ ax_omega0).
  - apply ind_sound, HΓ.
Qed.

End Rules.

(** ** Le théorème *)

Theorem izfm_sound {Γ} (Ξ : list (form Γ)) (φ : form Γ) :
  IZFm Γ Ξ φ -> vctx Γ -> IZF Γ (map tr Ξ) (tr φ).
Proof.
  induction 1 as [Γ Ξ φ Hin|Γ Ξ φ ψ Hc _ IH|Γ Ξ i v _ IH]; intros HΓ.
  - apply d_ax, in_map, Hin.
  - pose proof (proj1 conv_C_eq _ _ _ _ Hc) as E. subst ψ. exact (IH HΓ).
  - destruct i as [[i|i]|a].
    + exact (ipc_sound HΓ Ξ i v IH).
    + exact (quant_sound HΓ Ξ i v IH).
    + apply ax_sound, HΓ.
Qed.

(** Théorème 1.5.13, pour IZF⁻ε : une formule de L_IZF prouvée dans
    IZF⁻ε, lue dans IZF (∈ pour ε et ∈, = pour ≃ et l'égalité de
    Leibniz, l'inclusion pour ⊆), est prouvée dans IZF. *)
Lemma hyps_tr {Γ} (Ξ : list (form Γ)) (Ξ' : list (zform Γ)) :
  Forall2 (pcanon Γ) Ξ Ξ' -> forall ψ, In ψ Ξ -> IZF Γ Ξ' (tr ψ).
Proof.
  induction 1 as [|ψ1 ψ1' Ξ1 Ξ1' H1 _ IH]; intros ψ Hψ; [destruct Hψ|].
  destruct Hψ as [<-|Hψ].
  - apply (ziff_E2 _ _ ψ1'); [apply pcanon_tr, H1|]. apply d_ax; left; reflexivity.
  - apply (deriv_weaken _ _ _ (IH _ Hψ)). intros x Hx; right; exact Hx.
Qed.

Theorem izfm_conservative {Γ} (Ξ : list (form Γ)) (Ξ' : list (zform Γ)) (φ : form Γ) (φ' : zform Γ) :
  vctx Γ -> Forall2 (pcanon Γ) Ξ Ξ' -> pcanon Γ φ φ' -> IZFm Γ Ξ φ -> IZF Γ Ξ' φ'.
Proof.
  intros HΓ HΞ Hφ H. apply (ziff_E1 _ (tr φ)); [apply pcanon_tr, Hφ|].
  apply (deriv_cut_gen _ _ _ (izfm_sound Ξ φ H HΓ)). intros χ Hχ.
  apply in_map_iff in Hχ. destruct Hχ as [ψ [<- Hψ]]. exact (hyps_tr _ _ HΞ ψ Hψ).
Qed.

Corollary izfm_conservative_closed (φ : form []) (φ' : zform []) :
  pcanon [] φ φ' -> IZFm [] [] φ -> IZF [] [] φ'.
Proof. intros Hφ H. exact (izfm_conservative [] [] φ φ' vctx_nil (Forall2_nil _) Hφ H). Qed.
