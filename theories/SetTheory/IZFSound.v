(** * Correction de la traduction : les règles de IZF⁻ε

    Chaque règle de IZF⁻ε, traduite, est admissible dans IZF (contextes
    d'ensembles). D'où la conservativité ([izfm_conservative]). *)

From Stdlib Require Import List.
Import ListNotations.
From SF.Syntax Require Import Spec Terms Renaming Eta Composition Vectors.
From SF.Calculus Require Import System Rules.
From SF.Logic Require Import Judgment Propositional.
From SF.Functional Require Import Arrow.
From SF.Quantifiers Require Import Quant Order.
From SF.SetTheory Require Import Sets IZFe IZF IZFTr IZFLog IZFVal IZFOmega IZFTrSem.

Local Notation ι a := (Spec [] a).

(** ** Instanciation d'un quantificateur *)

Lemma app1_up_inst {Θ Γ} (x : var Θ σP) (v : vec zsym Θ Γ) :
  vsubst (zap1 (vs x) x0) (vup [ι V] v) = aget x v.
Proof.
  rewrite vsubst_app1. unfold vup, vren. cbn [vcat aget atl ahd]. rewrite aget_vmap. apply zinst_up.
Qed.

Lemma tr_inst1 {Γ} (φ : form (ι V :: Γ)) (t : tm Γ V) (Ξ : list (zform Γ)) : vctx Γ ->
  IZF (ι V :: Γ) (ttm t :: wk_list [ι V] Ξ) (zIff (ren_tm (tr (vsubst φ (inst1 t))) (wk [ι V])) (tr φ)).
Proof.
  intros HΓ.
  set (w := @acons _ isym (ι V :: Γ) (ι V) _ (ren_tm t (wk [ι V])) (vren (vid Γ) (wk [ι V]))).
  assert (E : vsubst φ w = ren_tm (vsubst φ (inst1 t)) (wk [ι V])).
  { rewrite ren_vsubst. reflexivity. }
  assert (Hw0 : Hw (ttm t :: wk_list [ι V] Ξ) w).
  { intros x.
    set (P := fun σ (y : var (ι V :: Γ) σ) =>
      match σ as σ0 return var (ι V :: Γ) σ0 -> Prop with
      | Spec [] V => fun y => IZF (ι V :: Γ) (ttm t :: wk_list [ι V] Ξ) (vsubst (ttm (aget y w)) (inst1 (var0 y)))
      | _ => fun _ => True
      end y).
    refine (var_inv P _ _ (ι V) x); unfold P.
    - change (IZF (ι V :: Γ) (ttm t :: wk_list [ι V] Ξ) (vsubst (ttm (ren_tm t (wk [ι V]))) (inst1 x0))).
      rewrite ttmV_ren. refine (eq_rect _ (fun f => IZF _ _ f) _ _ (eq_sym (zinst_up _))). zhyp.
    - intros [[|? ?] [|]] y; try exact I. unfold w. cbn [aget atl]. unfold vren. rewrite aget_vmap, aget_vid.
      change (IZF (ι V :: Γ) (ttm t :: wk_list [ι V] Ξ) (vsubst (DV (vs y)) (inst1 (var0 (vs y))))).
      rewrite DV_self. zap zeq_refl. }
  pose proof (subst_tr Pr φ w _ (vctx_V HΓ) Hw0) as K. cbn [RelT] in K.
  rewrite E in K. pose proof (tr_ren (vsubst φ (inst1 t)) (wk [ι V])) as E2. unfold tr in E2 |- *. rewrite <- E2. exact K.
Qed.

Lemma tot_w {Γ} (t : tm Γ V) (Ξ : list (zform Γ)) : vctx Γ -> IZF Γ Ξ (zEx (ttm t)).
Proof. intros H. exact (deriv_weaken _ _ _ (proj1 (tf_term t H)) _ (incl_nil_l _)). Qed.

Lemma fun_w {Γ} (t : tm Γ V) (Ξ : list (zform Γ)) : vctx Γ -> IZF Γ Ξ (Fun (ttm t)).
Proof. intros H. exact (deriv_weaken _ _ _ (proj2 (tf_term t H)) _ (incl_nil_l _)). Qed.

(** τ(φ[t]) ↔ ∃y. D_t(y) ∧ τ(φ)(y). *)
Lemma tr_inst_ex {Γ} (φ : form (ι V :: Γ)) (t : tm Γ V) (Ξ : list (zform Γ)) : vctx Γ ->
  IZF Γ Ξ (zIff (tr (vsubst φ (inst1 t))) (zEx (And (ttm t) (tr φ)))).
Proof.
  intros HΓ. apply ziff_I.
  - zap (zex_E _ (ttm t)); [apply tot_w, HΓ|]. apply zex_I0. zap zand_I; [zhyp|].
    apply (ziff_E1 _ (ren_tm (tr (vsubst φ (inst1 t))) (wk [ι V]))); [apply tr_inst1, HΓ|zhyp].
  - zap (zex_E _ (And (ttm t) (tr φ))); [zhyp|]. apply zand_L.
    apply (ziff_E2 _ _ (tr φ)); [|zhyp].
    refine (deriv_weaken _ _ _ (tr_inst1 φ t _ HΓ) _ _).
    intros χ [<-|Hχ]; [left; reflexivity|right; right; exact Hχ].
Qed.

Lemma allE_sound {Γ} (φ : form (ι V :: Γ)) (t : tm Γ V) (Ξ : list (zform Γ)) : vctx Γ ->
  IZF Γ Ξ (zAll (tr φ)) -> IZF Γ Ξ (tr (vsubst φ (inst1 t))).
Proof.
  intros HΓ H. apply (ziff_E2 _ _ (zEx (And (ttm t) (tr φ)))); [apply tr_inst_ex, HΓ|].
  zap (zex_E _ (ttm t)); [apply tot_w, HΓ|]. apply zex_I0. zap zand_I; [zhyp|].
  refine (deriv_weaken _ _ _ (zall_E0 _ _ H) _ (incl_tl _ (incl_refl _))).
Qed.

Lemma exI_sound {Γ} (φ : form (ι V :: Γ)) (t : tm Γ V) (Ξ : list (zform Γ)) : vctx Γ ->
  IZF Γ Ξ (tr (vsubst φ (inst1 t))) -> IZF Γ Ξ (zEx (tr φ)).
Proof.
  intros HΓ H. zap (zex_E _ (And (ttm t) (tr φ))).
  { apply (ziff_E1 _ (tr (vsubst φ (inst1 t)))); [apply tr_inst_ex, HΓ|exact H]. }
  apply zex_I0. zap (zand_E2 _ (ttm t)). zhyp.
Qed.

(** ** L'égalité *)

Lemma vsubst_v2_eta {Θ Γ} (F : zform [σP; σP]) (x y : var Θ σP) (w : vec zsym Θ Γ) :
  vsubst (vsubst F (v2 (eta σP x) (eta σP y))) w = vsubst F (v2 (aget x w) (aget y w)).
Proof.
  rewrite vsubst_vsubst. f_equal. unfold vcomp, v2. cbn [vmap].
  f_equal; [exact (vsubst_eta (σ := σP) x w)|f_equal; exact (vsubst_eta (σ := σP) y w)].
Qed.

Lemma eqR0 : IZF [σP] [Tot (eta σP (Γ := [σP]) vz)]
               (vsubst (Frel (zEq x1 x0)) (v2 (eta σP (Γ := [σP]) vz) (eta σP (Γ := [σP]) vz))).
Proof.
  zap (zex_E _ (zap1 (vs vz) x0)); [zhyp|].
  zap (zex_I _ _ x0). zap zand_I; [zhyp|]. zap (zex_I _ _ x0). zap zand_I; [zhyp|]. zap zeq_refl.
Qed.

Lemma eqR_sound {Γ} (t : tm Γ V) (Ξ : list (zform Γ)) : vctx Γ -> IZF Γ Ξ (tr (EqV t t)).
Proof.
  intros HΓ.
  refine (eq_rect _ (fun f => IZF Γ Ξ f) (zuse eqR0 (v1 (ttm t)) Ξ _) _ (vsubst_v2_eta _ vz vz _)).
  intros χ [<-|[]]. apply tot_eta. apply tot_w, HΓ.
Qed.

Lemma ex_and_inst {Θ Γ} (x y : var Θ σP) (w : vec zsym Θ Γ) :
  vsubst (zEx (And (zap1 (vs x) x0) (zap1 (vs y) x0))) w = zEx (And (aget x w) (aget y w)).
Proof.
  change (zEx (vsubst_tms (σ := σP) (And (zap1 (vs x) x0) (zap1 (vs y) x0)) w) = zEx (And (aget x w) (aget y w))).
  rewrite (vsubst_tms_vup (σ := σP)). cbn [dom]. unfold And. rewrite vsubst_Bin, !app1_up_inst. reflexivity.
Qed.

Definition v3P {Γ} (A B C : zform (ι V :: Γ)) : vec zsym [σP; σP; σP] Γ :=
  @acons _ zsym Γ σP _ A (v2 B C).

Lemma eqS0 : IZF [σP; σP; σP]
  [Fun (eta σP (Γ := [σP; σP; σP]) vz);
   vsubst (Frel (zEq x1 x0)) (v2 (eta σP (Γ := [σP; σP; σP]) vz) (eta σP (Γ := [σP; σP; σP]) (vs vz)));
   zEx (And (zap1 (vs vz) x0) (zap1 φ3 x0))]
  (zEx (And (zap1 φ2 x0) (zap1 φ3 x0))).
Proof.
  zap (zex_E _ (And (zap1 (vs vz) x0) (zap1 φ3 x0))); [zhyp|]. apply zand_L.
  zap (zex_E _ (And (zap1 φ2 x0) (zEx (And (zap1 φ4 x0) (zEq x1 x0))))); [zhyp|]. apply zand_L.
  zap (zex_E _ (And (zap1 φ4 x0) (zEq x1 x0))); [zhyp|]. apply zand_L.
  (* [b; a; y; Dt; Du; Φ] *)
  zap (zex_I _ _ x2). zap zand_I; [|zhyp].
  zap (zeq_subst _ (zap1 φ5 x0) x0 x2); [|zhyp].
  zap (zeq_trans _ x0 x1 x2); [zap zeq_sym; zhyp|].
  zap (zimp_E _ (zap1 φ3 x2)); [|zhyp].
  zinst (Imp (zap1 φ4 x0) (zEq x2 x0)) x2.
  zap (zimp_E _ (zap1 φ3 x1)); [|zhyp].
  zinst (Imp (zap1 φ4 x0) (zAll (Imp (zap1 φ5 x0) (zEq x1 x0)))) x1. zhyp.
Qed.

Lemma eqS_sound {Γ} (φ : form (ι V :: Γ)) (t u : tm Γ V) (Ξ : list (zform Γ)) : vctx Γ ->
  IZF Γ Ξ (tr (EqV t u)) -> IZF Γ Ξ (tr (vsubst φ (inst1 t))) -> IZF Γ Ξ (tr (vsubst φ (inst1 u))).
Proof.
  intros HΓ He Ht. apply (ziff_E2 _ _ (zEx (And (ttm u) (tr φ)))); [apply tr_inst_ex, HΓ|].
  refine (eq_rect _ (fun f => IZF Γ Ξ f) (zuse eqS0 (v3P (ttm t) (ttm u) (tr φ)) Ξ _) _
            (ex_and_inst (vs vz) φ2 (v3P (ttm t) (ttm u) (tr φ)))).
  intros χ Hin; repeat (destruct Hin as [<-|Hin]); try contradiction.
  - apply fun_eta. apply fun_w, HΓ.
  - exact (eq_rect (vsubst (Frel (zEq x1 x0)) (v2 (ttm t) (ttm u))) (fun f => IZF Γ Ξ f) He _
             (eq_sym (vsubst_v2_eta (Frel (zEq x1 x0)) vz (vs vz) (v3P (ttm t) (ttm u) (tr φ))))).
  - refine (eq_rect _ (fun f => IZF Γ Ξ f) _ _ (eq_sym (ex_and_inst vz φ2 (v3P (ttm t) (ttm u) (tr φ))))).
    apply (ziff_E1 _ (tr (vsubst φ (inst1 t)))); [apply tr_inst_ex, HΓ|exact Ht].
Qed.

(** ** Clôture universelle des métavariables d'ensembles *)

Fixpoint Vn (n : nat) : ctx isort := match n with 0 => [] | S n => ι V :: Vn n end.

Fixpoint Cl {Φ} (n : nat) : form (Vn n ++ Φ) -> form Φ :=
  match n as n0 return form (Vn n0 ++ Φ) -> form Φ with
  | 0 => fun χ => χ
  | S n => fun χ => Cl n (All χ)
  end.

Lemma vsubst_tms_wk_cat' Λ {Γ Δ σ} (u : tms isym Γ σ) (a : args isym Δ Λ) (w : vec isym Γ Δ) :
  vsubst_tms (ren_tms u (wk Λ)) (vcat Λ a w) = vsubst_tms u w.
Proof.
  unfold vsubst_tms; rewrite subst_tms_ren; apply subst_tms_ext; intros ρ y.
  unfold rs_comp, vget, wk. rewrite aget_vcat_r. reflexivity.
Qed.

Lemma vup_cat' Λ {Δ Γ Γ'} (w : vec isym Δ Γ) (a : args isym Γ' Λ) (w' : vec isym Γ Γ') :
  vcomp (vup Λ w) (vcat Λ a w') = vcat Λ a (vcomp w w').
Proof.
  apply vec_ext; intros σ x; unfold vget. rewrite aget_vcomp. vcase x.
  - unfold vup. rewrite !aget_vcat_l, aget_etas, vsubst_eta, aget_vcat_l. reflexivity.
  - unfold vup. rewrite !aget_vcat_r. unfold vren. rewrite aget_vmap, vsubst_tms_wk_cat', aget_vcomp.
    reflexivity.
Qed.

Lemma inst_nest {Θ Γ} (χ : form (ι V :: Θ)) (W : vec isym Θ Γ) (t : tm Γ V) :
  vsubst (vsubst χ (vup [ι V] W)) (inst1 t) = vsubst χ (@acons _ isym Γ (ι V) _ t W).
Proof.
  rewrite vsubst_vsubst. f_equal.
  change (vcomp (vup [ι V] W) (vcat [ι V] (@acons _ isym Γ (ι V) _ t anil) (vid Γ))
          = vcat [ι V] (@acons _ isym Γ (ι V) _ t anil) W).
  rewrite vup_cat', vcomp_vid_r. reflexivity.
Qed.

Lemma closure_inst {Φ Γ} (n : nat) (χ : form (Vn n ++ Φ)) (ts : vec isym (Vn n) Γ) (r : vec isym Φ Γ)
  (Ξ : list (zform Γ)) : vctx Γ ->
  IZF Γ Ξ (tr (vsubst (Cl n χ) r)) -> IZF Γ Ξ (tr (vsubst χ (vcat (Vn n) ts r))).
Proof.
  intros HΓ. revert χ ts. induction n as [|n IH]; intros χ ts H.
  - rewrite (args_nil ts). exact H.
  - rewrite (args_eta ts). cbn [Vn vcat ahd atl] in *.
    refine (eq_rect _ (fun f => IZF Γ Ξ (tr f)) _ _ (inst_nest χ (vcat (Vn n) (atl ts) r) (ahd ts))).
    apply allE_sound; [exact HΓ|].
    specialize (IH (All χ) (atl ts) H).
    change (IZF Γ Ξ (zAll (tr (vsubst χ (vup [ι V] (vcat (Vn n) (atl ts) r)))))).
    unfold All in IH. rewrite vsubst_Qnt, (vsubst_tms_vup (σ := σP)) in IH. exact IH.
Qed.

(** Une formule close traduite, prouvée dans IZF, se transporte dans tout contexte. *)
Lemma closed_lift {Γ} (ψ : form []) (Ξ : list (zform Γ)) :
  IZF [] [] (tr ψ) -> IZF Γ Ξ (tr (vsubst ψ (anil (Sym := isym) (Γ := Γ)))).
Proof.
  intros H. set (ρ0 := (fun σ (x : var [] σ) => match var_nil x with end) : ren [] Γ).
  assert (E : vsubst ψ (anil (Sym := isym) (Γ := Γ)) = ren_tm ψ ρ0).
  { rewrite ren_as_vsubst. f_equal. }
  rewrite E, tr_ren. rewrite ren_as_vsubst.
  exact (deriv_weaken _ _ _ (deriv_subst _ _ _ H Γ _) _ (incl_nil_l _)).
Qed.

(** ** Formules pures : leur traduction est la lecture directe *)

Lemma ren_deriv {Γ0 Γ} (ρ : ren Γ0 Γ) (φ : zform Γ0) (Ξ : list (zform Γ)) :
  IZF Γ0 [] φ -> IZF Γ Ξ (ren_tm φ ρ).
Proof. intros H. rewrite ren_as_vsubst. exact (deriv_weaken _ _ _ (deriv_subst _ _ _ H Γ _) _ (incl_nil_l _)). Qed.

Definition rho2 {Γ} (x y : var Γ (ι V)) : ren [ι V; ι V] Γ :=
  fun σ z => var_inv (fun σ _ => var Γ σ) x
               (fun σ' z' => var_inv (fun σ _ => var Γ σ) y (fun σ'' w => match var_nil w with end) σ' z') σ z.

Lemma atom_mem0 : IZF [ι V; ι V] [] (zIff (tr (Mem x0 x1)) (zMem x0 x1)).
Proof.
  apply ziff_I.
  - zap (zex_E _ (And (zEq x0 x1) (zEx (And (zEq x0 x3) (zMem x1 x0))))); [zhyp|]. apply zand_L.
    zap (zex_E _ (And (zEq x0 x3) (zMem x1 x0))); [zhyp|]. apply zand_L.
    (* [b; a; x; y] *)
    zap (zeq_subst _ (zMem x3 x0) x0 x3); [zhyp|].
    zap (zeq_subst _ (zMem x0 x1) x1 x2); [zhyp|zhyp].
  - zap (zex_I _ _ x0). zap zand_I; [zap zeq_refl|].
    zap (zex_I _ _ x1). zap zand_I; [zap zeq_refl|zhyp].
Qed.

Lemma atom_eq0 : IZF [ι V; ι V] [] (zIff (tr (Eqv x0 x1)) (zEq x0 x1)).
Proof.
  apply ziff_I.
  - zap (zex_E _ (And (zEq x0 x1) (zEx (And (zEq x0 x3) (zEq x1 x0))))); [zhyp|]. apply zand_L.
    zap (zex_E _ (And (zEq x0 x3) (zEq x1 x0))); [zhyp|]. apply zand_L.
    zap (zeq_trans _ x2 x1 x3); [zap zeq_sym; zhyp|].
    zap (zeq_trans _ x1 x0 x3); [zhyp|zhyp].
  - zap (zex_I _ _ x0). zap zand_I; [zap zeq_refl|].
    zap (zex_I _ _ x1). zap zand_I; [zap zeq_refl|zhyp].
Qed.

Lemma atom_sub0 : IZF [ι V; ι V] [] (zIff (tr (Sub x0 x1)) (zAll (Imp (zMem x0 x1) (zMem x0 x2)))).
Proof.
  apply ziff_I.
  - zap (zex_E _ (And (zEq x0 x1) (zEx (And (zEq x0 x3) (zAll (Imp (zMem x0 x2) (zMem x0 x1))))))); [zhyp|].
    apply zand_L.
    zap (zex_E _ (And (zEq x0 x3) (zAll (Imp (zMem x0 x2) (zMem x0 x1))))); [zhyp|]. apply zand_L.
    (* [b; a; x; y] *)
    zap zall_I. zap zimp_I.
    (* [z; b; a; x; y] : z ∈ x ⊢ z ∈ y *)
    zap (zeq_subst _ (zMem x1 x0) x1 x4); [zhyp|].
    zap (zimp_E _ (zMem x0 x2)); [zinst (Imp (zMem x0 x3) (zMem x0 x2)) x0; zhyp|].
    zap (zeq_subst _ (zMem x1 x0) x3 x2); [zap zeq_sym; zhyp|zhyp].
  - zap (zex_I _ _ x0). zap zand_I; [zap zeq_refl|].
    zap (zex_I _ _ x1). zap zand_I; [zap zeq_refl|zhyp].
Qed.

Inductive pcanon : forall Γ, form Γ -> zform Γ -> Prop :=
| pc_mem {Γ} (x y : var Γ (ι V)) : pcanon Γ (Mem (var0 x) (var0 y)) (zMem (var0 x) (var0 y))
| pc_eps {Γ} (x y : var Γ (ι V)) : pcanon Γ (Eps (var0 x) (var0 y)) (zMem (var0 x) (var0 y))
| pc_sub {Γ} (x y : var Γ (ι V)) :
    pcanon Γ (Sub (var0 x) (var0 y)) (zAll (Imp (zMem x0 (var0 (vs x))) (zMem x0 (var0 (vs y)))))
| pc_eqv {Γ} (x y : var Γ (ι V)) : pcanon Γ (Eqv (var0 x) (var0 y)) (zEq (var0 x) (var0 y))
| pc_eqV {Γ} (x y : var Γ (ι V)) : pcanon Γ (EqV (var0 x) (var0 y)) (zEq (var0 x) (var0 y))
| pc_top {Γ} : pcanon Γ Top Top
| pc_bot {Γ} : pcanon Γ Bot Bot
| pc_imp {Γ} φ ψ φ' ψ' : pcanon Γ φ φ' -> pcanon Γ ψ ψ' -> pcanon Γ (Imp φ ψ) (Imp φ' ψ')
| pc_and {Γ} φ ψ φ' ψ' : pcanon Γ φ φ' -> pcanon Γ ψ ψ' -> pcanon Γ (And φ ψ) (And φ' ψ')
| pc_or {Γ} φ ψ φ' ψ' : pcanon Γ φ φ' -> pcanon Γ ψ ψ' -> pcanon Γ (Or φ ψ) (Or φ' ψ')
| pc_all {Γ} φ φ' : pcanon (ι V :: Γ) φ φ' -> pcanon Γ (All φ) (zAll φ')
| pc_ex {Γ} φ φ' : pcanon (ι V :: Γ) φ φ' -> pcanon Γ (Ex φ) (zEx φ').

Lemma pcanon_tr {Γ} (φ : form Γ) (φ' : zform Γ) : pcanon Γ φ φ' ->
  forall Ξ, IZF Γ Ξ (zIff (tr φ) φ').
Proof.
  induction 1; intros Ξ.
  - exact (ren_deriv (rho2 x y) _ Ξ atom_mem0).
  - exact (ren_deriv (rho2 x y) _ Ξ atom_mem0).
  - exact (ren_deriv (rho2 x y) _ Ξ atom_sub0).
  - exact (ren_deriv (rho2 x y) _ Ξ atom_eq0).
  - exact (ren_deriv (rho2 x y) _ Ξ atom_eq0).
  - apply ziff_refl.
  - apply ziff_refl.
  - exact (ziff_imp _ _ _ _ _ (IHpcanon1 Ξ) (IHpcanon2 Ξ)).
  - exact (ziff_and _ _ _ _ _ (IHpcanon1 Ξ) (IHpcanon2 Ξ)).
  - exact (ziff_or _ _ _ _ _ (IHpcanon1 Ξ) (IHpcanon2 Ξ)).
  - exact (ziff_all _ _ _ (IHpcanon _)).
  - exact (ziff_ex _ _ _ (IHpcanon _)).
Qed.

(** ** Les axiomes de IZF⁻ε sans métavariable de formule *)

Ltac pcan := repeat econstructor.

Lemma ax_mem0 : IZF [] [] (tr (Cl 2 (d_concl (izfm_rules A_mem)))).
Proof.
  zap zall_I. zap zall_I. cbn [d_concl izfm_rules wk_list map].
  apply (ziff_E2 _ _ (zIff (zMem x0 x1) (zEx (And (zEq x1 x0) (zMem x0 x2))))); [apply pcanon_tr; pcan|].
  apply ziff_I.
  - zap (zex_I _ _ x0). zap zand_I; [zap zeq_refl|zhyp].
  - zap (zex_E _ (And (zEq x1 x0) (zMem x0 x2))); [zhyp|]. apply zand_L.
    zap (zeq_subst _ (zMem x0 x3) x0 x1); [zap zeq_sym; zhyp|zhyp].
Qed.

Lemma ax_sub0 : IZF [] [] (tr (Cl 2 (d_concl (izfm_rules A_sub)))).
Proof.
  zap zall_I. zap zall_I. cbn [d_concl izfm_rules wk_list map].
  apply (ziff_E2 _ _ (zIff (zAll (Imp (zMem x0 x1) (zMem x0 x2))) (zAll (Imp (zMem x0 x1) (zMem x0 x2)))));
    [apply pcanon_tr; pcan|apply ziff_refl].
Qed.

Lemma ax_eqv0 : IZF [] [] (tr (Cl 2 (d_concl (izfm_rules A_eqv)))).
Proof.
  zap zall_I. zap zall_I. cbn [d_concl izfm_rules wk_list map].
  apply (ziff_E2 _ _ (zIff (zEq x0 x1) (And (zAll (Imp (zMem x0 x1) (zMem x0 x2))) (zAll (Imp (zMem x0 x2) (zMem x0 x1))))));
    [apply pcanon_tr; pcan|].
  apply ziff_I.
  - zap zand_I; zap zall_I; zap zimp_I.
    + zap (zeq_subst _ (zMem x1 x0) x1 x2); zhyp.
    + zap (zeq_subst _ (zMem x1 x0) x2 x1); [zap zeq_sym; zhyp|zhyp].
  - apply zand_L. zap (zimp_E _ (zAll (zIff (zMem x0 x1) (zMem x0 x2)))).
    + zinst (Imp (zAll (zIff (zMem x0 x2) (zMem x0 x1))) (zEq x1 x0)) x1.
      zinst (zAll (Imp (zAll (zIff (zMem x0 x2) (zMem x0 x1))) (zEq x1 x0))) x0.
      exact (zaxm Z_ext _ anil).
    + zap zall_I. apply ziff_I.
      * zap (zimp_E _ (zMem x0 x1)); [zinst (Imp (zMem x0 x2) (zMem x0 x3)) x0; zhyp|zhyp].
      * zap (zimp_E _ (zMem x0 x2)); [zinst (Imp (zMem x0 x3) (zMem x0 x2)) x0; zhyp|zhyp].
Qed.

Lemma ax_empty0 : IZF [] [] (tr (Cl 1 (d_concl (izfm_rules A_empty)))).
Proof.
  zap zall_I. cbn [d_concl izfm_rules wk_list map]. zap zimp_I.
  zap (zex_E _ (And (zEq x0 x1) (zEx (And (zAll (Neg (zMem x0 x1))) (zMem x1 x0))))); [zhyp|]. apply zand_L.
  zap (zex_E _ (And (zAll (Neg (zMem x0 x1))) (zMem x1 x0))); [zhyp|]. apply zand_L.
  zap (zimp_E _ (zMem x1 x0)); [|zhyp]. zinst (Neg (zMem x0 x1)) x1. zhyp.
Qed.

(** z = x à partir de sa traduction ∃a. a = z ∧ ∃b. b = x ∧ a = b   (contexte [z; x]). *)
Lemma eqrel_var : IZF [ι V; ι V] [tr (EqV x0 x1)] (zEq x0 x1).
Proof. apply (ziff_E1 _ (tr (EqV x0 x1))); [exact (ren_deriv (fun _ x => x) _ _ atom_eq0)|zhyp]. Qed.

Lemma ax_pair0 : IZF [] [] (tr (Cl 3 (d_concl (izfm_rules A_pair)))).
Proof.
  zap zall_I. zap zall_I. zap zall_I. cbn [d_concl izfm_rules wk_list map].
  (* [z; x; y] *)
  apply ziff_I.
  - zap (zex_E _ (And (zEq x0 x1) (zEx (And (zEx (And (zEq x0 x4) (zEx (And (zEq x0 x6)
           (zAll (zIff (zMem x0 x3) (Or (zEq x0 x2) (zEq x0 x1)))))))) (zMem x1 x0))))); [zhyp|].
    apply zand_L.
    zap (zex_E _ (And (zEx (And (zEq x0 x4) (zEx (And (zEq x0 x6)
           (zAll (zIff (zMem x0 x3) (Or (zEq x0 x2) (zEq x0 x1)))))))) (zMem x1 x0))); [zhyp|].
    apply zand_L.
    zap (zex_E _ (And (zEq x0 x4) (zEx (And (zEq x0 x6) (zAll (zIff (zMem x0 x3) (Or (zEq x0 x2) (zEq x0 x1)))))))); [zhyp|].
    apply zand_L.
    zap (zex_E _ (And (zEq x0 x6) (zAll (zIff (zMem x0 x3) (Or (zEq x0 x2) (zEq x0 x1)))))); [zhyp|].
    apply zand_L.
    (* [b'; a'; p; a; z; x; y] *)
    zap (zor_E _ (zEq x3 x1) (zEq x3 x0)).
    { apply (ziff_E1 _ (zMem x3 x2)); [|zhyp].
      zinst (zIff (zMem x0 x3) (Or (zEq x0 x2) (zEq x0 x1))) x3. zhyp. }
    + zap zor_I1. zap (zex_I _ _ x3). zap zand_I; [zhyp|].
      zap (zex_I _ _ x1). zap zand_I; zhyp.
    + zap zor_I2. zap (zex_I _ _ x3). zap zand_I; [zhyp|].
      zap (zex_I _ _ x0). zap zand_I; zhyp.
  - zap (zex_E _ (zAll (zIff (zMem x0 x1) (Or (zEq x0 x3) (zEq x0 x4))))).
    { zinst (zEx (zAll (zIff (zMem x0 x1) (Or (zEq x0 x4) (zEq x0 x2))))) x2.
      zinst (zAll (zEx (zAll (zIff (zMem x0 x1) (Or (zEq x0 x3) (zEq x0 x2)))))) x1.
      exact (zaxm Z_pair _ anil). }
    (* [p; z; x; y] *)
    zap (zex_I _ _ x1). zap zand_I; [zap zeq_refl|].
    zap (zex_I _ _ x0). zap zand_I.
    + zap (zex_I _ _ x2). zap zand_I; [zap zeq_refl|].
      zap (zex_I _ _ x3). zap zand_I; [zap zeq_refl|zhyp].
    + apply (ziff_E2 _ _ (Or (zEq x1 x2) (zEq x1 x3))).
      { zinst (zIff (zMem x0 x1) (Or (zEq x0 x3) (zEq x0 x4))) x1. zhyp. }
      zap (zor_E _ (tr (EqV x1 x2)) (tr (EqV x1 x3))); [zhyp| |].
      * zap zor_I1. apply (ziff_E1 _ (tr (EqV x1 x2))); [apply pcanon_tr; pcan|zhyp].
      * zap zor_I2. apply (ziff_E1 _ (tr (EqV x1 x3))); [apply pcanon_tr; pcan|zhyp].
Qed.

Local Notation UG := (zEx (And (zEq x0 x4) (zAll (zIff (zMem x0 x2) (zEx (And (zMem x1 x0) (zMem x0 x2))))))).

Lemma ax_union0 : IZF [] [] (tr (Cl 2 (d_concl (izfm_rules A_union)))).
Proof.
  zap zall_I. zap zall_I. cbn [d_concl izfm_rules wk_list map].
  (* [z; x] *)
  apply (ziff_trans _ _ (zEx (And (zMem x1 x0) (zMem x0 x2)))).
  2:{ apply ziff_sym. apply pcanon_tr; pcan. }
  apply ziff_I.
  - zap (zex_E _ (And (zEq x0 x1) (zEx (And UG (zMem x1 x0))))); [zhyp|]. apply zand_L.
    zap (zex_E _ (And UG (zMem x1 x0))); [zhyp|]. apply zand_L.
    zap (zex_E _ (And (zEq x0 x4) (zAll (zIff (zMem x0 x2) (zEx (And (zMem x1 x0) (zMem x0 x2))))))); [zhyp|].
    apply zand_L.
    (* [c; u; a; z; x] *)
    apply (deriv_cut ZC Pr RIZF (φ := zMem x3 x1)).
    { zap (zeq_subst _ (zMem x0 x2) x2 x3); zhyp. }
    zap (zex_E _ (And (zMem x4 x0) (zMem x0 x1))).
    { apply (ziff_E1 _ (zMem x3 x1)); [|zhyp].
      zinst (zIff (zMem x0 x2) (zEx (And (zMem x1 x0) (zMem x0 x2)))) x3. zhyp. }
    apply zand_L.
    (* [d; c; u; a; z; x] *)
    zap (zex_I _ _ x0). zap zand_I; [zhyp|].
    zap (zeq_subst _ (zMem x1 x0) x1 x5); zhyp.
  - zap (zex_E _ (zAll (zIff (zMem x0 x1) (zEx (And (zMem x1 x0) (zMem x0 x4)))))).
    { zinst (zEx (zAll (zIff (zMem x0 x1) (zEx (And (zMem x1 x0) (zMem x0 x3)))))) x1.
      exact (zaxm Z_union _ anil). }
    (* [u; z; x] *)
    zap (zex_I _ _ x1). zap zand_I; [zap zeq_refl|].
    zap (zex_I _ _ x0). zap zand_I.
    + zap (zex_I _ _ x2). zap zand_I; [zap zeq_refl|zhyp].
    + apply (ziff_E2 _ _ (zEx (And (zMem x2 x0) (zMem x0 x3)))); [|zhyp].
      zinst (zIff (zMem x0 x1) (zEx (And (zMem x1 x0) (zMem x0 x4)))) x1. zhyp.
Qed.

Local Notation PwG := (zEx (And (zEq x0 x3) (zAll (zIff (zMem x0 x2) (zAll (Imp (zMem x0 x1) (zMem x0 x2))))))).

Lemma ax_power0 : IZF [] [] (tr (Cl 2 (d_concl (izfm_rules A_power)))).
Proof.
  zap zall_I. zap zall_I. cbn [d_concl izfm_rules wk_list map].
  (* [x; a] : s = x ∩ a *)
  zap (zex_E _ (zAll (zIff (zMem x0 x1) (And (zMem x0 x2) (zMem x0 x3))))).
  { zinst (zEx (zAll (zIff (zMem x0 x1) (And (zMem x0 x2) (zMem x0 x4))))) x0.
    exact (zaxm Z_sep _ (v1 (zMem x0 x2))). }
  (* [s; x; a] : p = P(x) *)
  zap (zex_E _ PwG).
  { refine (zuse tot_power (v1 (DV (vs vz))) _ _). intros χ [<-|[]].
    apply tot_eta. cbn [aget v1]. zap (zex_I _ _ x1). zap zeq_refl. }
  (* [p; s; x; a] *)
  zap (zex_I _ _ x1). zap zand_I.
  - zap (zex_I _ _ x1). zap zand_I; [zap zeq_refl|].
    zap (zex_I _ _ x0). zap zand_I; [zhyp|].
    zap (zex_E _ (And (zEq x0 x3) (zAll (zIff (zMem x0 x2) (zAll (Imp (zMem x0 x1) (zMem x0 x2))))))); [zhyp|].
    apply zand_L.
    (* [c; p; s; x; a] *)
    apply (ziff_E2 _ _ (zAll (Imp (zMem x0 x3) (zMem x0 x1)))).
    { zinst (zIff (zMem x0 x2) (zAll (Imp (zMem x0 x1) (zMem x0 x2)))) x2. zhyp. }
    zap zall_I. zap zimp_I.
    (* [v; c; p; s; x; a] *)
    zap (zeq_subst _ (zMem x1 x0) x4 x1); [zap zeq_sym; zhyp|].
    zap (zand_E1 _ _ (zMem x0 x5)). apply (ziff_E1 _ (zMem x0 x3)); [|zhyp].
    zinst (zIff (zMem x0 x4) (And (zMem x0 x5) (zMem x0 x6))) x0. zhyp.
  - zap zall_I.
    refine (_ : IZF _ _ (tr (Iff (Eps x0 x2) (And (Eps x0 x3) (Eps x0 x4))))).
    apply (ziff_E2 _ _ (zIff (zMem x0 x2) (And (zMem x0 x3) (zMem x0 x4)))); [apply pcanon_tr; pcan|].
    zinst (zIff (zMem x0 x3) (And (zMem x0 x4) (zMem x0 x5))) x0. zhyp.
Qed.

(** Élimination de l'hypothèse de tête ∃x. A ∧ B. *)
Lemma zex_E_raw {Γ} (Ξ : list (zform Γ)) (φ : zform (ι V :: Γ)) χ :
  IZF Γ Ξ (@tsym _ zsym Γ _ z_ex (@acons _ zsym Γ σP _ φ anil)) ->
  IZF (ι V :: Γ) (φ :: wk_list [ι V] Ξ) (ren_tm χ (wk [ι V])) -> IZF Γ Ξ χ.
Proof. intros H1 H2. exact (zex_E Ξ φ χ H1 H2). Qed.

Lemma zand_L_raw {Γ} (Ξ : list (zform Γ)) A B C :
  IZF Γ (A :: B :: Ξ) C ->
  IZF Γ (@tsym _ zsym Γ _ z_and (@acons _ zsym Γ (ι Pr) _ A (@acons _ zsym Γ (ι Pr) _ B anil)) :: Ξ) C.
Proof. apply zand_L. Qed.

Ltac zexh :=
  match goal with |- IZF _ (?h :: _) _ =>
    let h0 := eval cbn in h in let h' := eval cbv beta delta [Quant.Ex Qnt] in h0 in
    match h' with @tsym _ _ _ _ _ (@acons _ _ _ _ _ ?φ _) =>
      refine (zex_E_raw _ φ _ _ _); [apply d_ax; left; reflexivity|]; try apply zand_L_raw end end.
Ltac zexh2 :=
  match goal with |- IZF _ (_ :: ?h :: _) _ =>
    let h0 := eval cbn in h in let h' := eval cbv beta delta [Quant.Ex Qnt] in h0 in
    match h' with @tsym _ _ _ _ _ (@acons _ _ _ _ _ ?φ _) =>
      refine (zex_E_raw _ φ _ _ _); [apply d_ax; right; left; reflexivity|]; try apply zand_L_raw end end.

(** Le graphe de S(b) = ⋃{b, {b, b}} : s = S(b) ↔ ∀w. w ∈ s ↔ w ∈ b ∨ w = b   (contexte [s; b]). *)
Lemma suc_graph : IZF [ι V; ι V] [] (zIff (ttm (Suc (x0 : tm [ι V] V))) (SucAt vz (vs vz))).
Proof.
  apply ziff_I.
  - zexh. zexh. zexh2. zexh. zexh2.
    (* [c''; c'; q; c; u; s; b] *)
    zap zall_I. apply ziff_I.
    + zap (zex_E _ (And (zMem x1 x0) (zMem x0 x6))).
      { apply (ziff_E1 _ (zMem x0 x6)); [|zhyp].
        zinst (zIff (zMem x0 x7) (zEx (And (zMem x1 x0) (zMem x0 x7)))) x0. zhyp. }
      apply zand_L.
      (* [d; w; c''; c'; q; c; u; s; b] *)
      zap (zor_E _ (zEq x0 x5) (zEq x0 x4)).
      { apply (ziff_E1 _ (zMem x0 x6)); [|zhyp].
        zinst (zIff (zMem x0 x7) (Or (zEq x0 x6) (zEq x0 x5))) x0. zhyp. }
      * zap zor_I1. zap (zeq_subst _ (zMem x2 x0) x0 x8); [|zhyp].
        zap (zeq_trans _ x0 x5 x8); zhyp.
      * zap zor_I2.
        zap (zor_E _ (zEq x1 x3) (zEq x1 x2)).
        { apply (ziff_E1 _ (zMem x1 x4)).
          - zinst (zIff (zMem x0 x5) (Or (zEq x0 x4) (zEq x0 x3))) x1. zhyp.
          - zap (zeq_subst _ (zMem x2 x0) x0 x4); zhyp. }
        -- zap (zeq_trans _ x1 x3 x8); zhyp.
        -- zap (zeq_trans _ x1 x2 x8); zhyp.
    + apply (ziff_E2 _ _ (zEx (And (zMem x1 x0) (zMem x0 x6)))).
      { zinst (zIff (zMem x0 x7) (zEx (And (zMem x1 x0) (zMem x0 x7)))) x0. zhyp. }
      zap (zor_E _ (zMem x0 x7) (zEq x0 x7)); [zhyp| |].
      * zap (zex_I _ _ x4). zap zand_I.
        -- zap (zeq_subst _ (zMem x1 x0) x7 x4); [zap zeq_sym; zhyp|zhyp].
        -- apply (ziff_E2 _ _ (Or (zEq x4 x4) (zEq x4 x3))).
           { zinst (zIff (zMem x0 x6) (Or (zEq x0 x5) (zEq x0 x4))) x4. zhyp. }
           zap zor_I1. zap zeq_refl.
      * zap (zex_I _ _ x3). zap zand_I.
        -- apply (ziff_E2 _ _ (Or (zEq x0 x2) (zEq x0 x1))).
           { zinst (zIff (zMem x0 x4) (Or (zEq x0 x3) (zEq x0 x2))) x0. zhyp. }
           zap zor_I1. zap (zeq_trans _ x0 x7 x2); [zhyp|zap zeq_sym; zhyp].
        -- apply (ziff_E2 _ _ (Or (zEq x3 x4) (zEq x3 x3))).
           { zinst (zIff (zMem x0 x6) (Or (zEq x0 x5) (zEq x0 x4))) x3. zhyp. }
           zap zor_I2. zap zeq_refl.
  - (* q = {b, b} *)
    zap (zex_E _ (zAll (zIff (zMem x0 x1) (Or (zEq x0 x3) (zEq x0 x3))))).
    { zinst (zEx (zAll (zIff (zMem x0 x1) (Or (zEq x0 x4) (zEq x0 x2))))) x1.
      zinst (zAll (zEx (zAll (zIff (zMem x0 x1) (Or (zEq x0 x3) (zEq x0 x2)))))) x1.
      exact (zaxm Z_pair _ anil). }
    (* c = {b, q} *)
    zap (zex_E _ (zAll (zIff (zMem x0 x1) (Or (zEq x0 x4) (zEq x0 x2))))).
    { zinst (zEx (zAll (zIff (zMem x0 x1) (Or (zEq x0 x5) (zEq x0 x2))))) x0.
      zinst (zAll (zEx (zAll (zIff (zMem x0 x1) (Or (zEq x0 x3) (zEq x0 x2)))))) x2.
      exact (zaxm Z_pair _ anil). }
    (* [c; q; s; b] *)
    zap (zex_I _ _ x0). zap zand_I.
    + zap (zex_I _ _ x3). zap zand_I; [zap zeq_refl|].
      zap (zex_I _ _ x1). zap zand_I; [|zhyp].
      zap (zex_I _ _ x3). zap zand_I; [zap zeq_refl|].
      zap (zex_I _ _ x3). zap zand_I; [zap zeq_refl|zhyp].
    + zap zall_I. apply ziff_I.
      * (* [w; c; q; s; b] *)
        zap (zor_E _ (zMem x0 x4) (zEq x0 x4)).
        { apply (ziff_E1 _ (zMem x0 x3)); [|zhyp].
          zinst (zIff (zMem x0 x4) (Or (zMem x0 x5) (zEq x0 x5))) x0. zhyp. }
        -- zap (zex_I _ _ x4). zap zand_I; [zhyp|].
           apply (ziff_E2 _ _ (Or (zEq x4 x4) (zEq x4 x2))).
           { zinst (zIff (zMem x0 x2) (Or (zEq x0 x5) (zEq x0 x3))) x4. zhyp. }
           zap zor_I1. zap zeq_refl.
        -- zap (zex_I _ _ x2). zap zand_I.
           ++ apply (ziff_E2 _ _ (Or (zEq x0 x4) (zEq x0 x4))).
              { zinst (zIff (zMem x0 x3) (Or (zEq x0 x5) (zEq x0 x5))) x0. zhyp. }
              zap zor_I1. zhyp.
           ++ apply (ziff_E2 _ _ (Or (zEq x2 x4) (zEq x2 x2))).
              { zinst (zIff (zMem x0 x2) (Or (zEq x0 x5) (zEq x0 x3))) x2. zhyp. }
              zap zor_I2. zap zeq_refl.
      * zap (zex_E _ (And (zMem x1 x0) (zMem x0 x2))); [zhyp|]. apply zand_L.
        (* [d; w; c; q; s; b] *)
        apply (ziff_E2 _ _ (Or (zMem x1 x5) (zEq x1 x5))).
        { zinst (zIff (zMem x0 x5) (Or (zMem x0 x6) (zEq x0 x6))) x1. zhyp. }
        zap (zor_E _ (zEq x0 x5) (zEq x0 x3)).
        { apply (ziff_E1 _ (zMem x0 x2)); [|zhyp].
          zinst (zIff (zMem x0 x3) (Or (zEq x0 x6) (zEq x0 x4))) x0. zhyp. }
        -- zap zor_I1. zap (zeq_subst _ (zMem x2 x0) x0 x5); zhyp.
        -- zap zor_I2. zap (zor_E _ (zEq x1 x5) (zEq x1 x5)); [|zhyp|zhyp].
           apply (ziff_E1 _ (zMem x1 x3)).
           ++ zinst (zIff (zMem x0 x4) (Or (zEq x0 x6) (zEq x0 x6))) x1. zhyp.
           ++ zap (zeq_subst _ (zMem x2 x0) x0 x3); zhyp.
Qed.

Local Notation OmB := (zIff (zMem x0 x1) (Or (zAll (Neg (zMem x0 x1)))
                        (zEx (And (zMem x0 x2) (zAll (zIff (zMem x0 x2) (Or (zMem x0 x1) (zEq x0 x1)))))))).

Lemma ax_omega0 : IZF [] [] (tr (Cl 1 (d_concl (izfm_rules A_omega)))).
Proof.
  zap zall_I. cbn [d_concl izfm_rules wk_list map]. apply ziff_I.
  - zexh. zexh2.
    (* [w; u; a] *)
    apply (deriv_cut ZC Pr RIZF (φ := zMem x2 x0)).
    { zap (zeq_subst _ (zMem x0 x1) x1 x2); zhyp. }
    zap (zor_E _ (zAll (Neg (zMem x0 x3)))
                 (zEx (And (zMem x0 x1) (zAll (zIff (zMem x0 x4) (Or (zMem x0 x1) (zEq x0 x1))))))).
    { apply (ziff_E1 _ (zMem x2 x0)); [|zhyp]. zinst OmB x2. zhyp. }
    + zap zor_I1. zap (zex_I _ _ x2). zap zand_I; [zap zeq_refl|].
      zap (zex_I _ _ x2). zap zand_I; [zhyp|zap zeq_refl].
    + zap (zex_E _ (And (zMem x0 x1) (zAll (zIff (zMem x0 x4) (Or (zMem x0 x1) (zEq x0 x1)))))); [zhyp|].
      apply zand_L.
      (* [b; w; u; a] *)
      zap zor_I2. zap (zex_I _ _ x0). zap zand_I.
      * zap (zex_I _ _ x0). zap zand_I; [zap zeq_refl|].
        zap (zex_I _ _ x1). zap zand_I; zhyp.
      * zap (zex_I _ _ x3). zap zand_I; [zap zeq_refl|].
        zap (zex_I _ _ x3). zap zand_I; [|zap zeq_refl].
        apply (ziff_E2 _ _ _ (ren_deriv (rho2 (vs (vs (vs vz))) vz) _ _ suc_graph)). zhyp.
  - zap (zor_E _ (tr (EqV x0 Empty)) (tr (Ex (And (Eps x0 Omega) (EqV x1 (Suc x0)))))); [zhyp| |].
    + zexh. zexh2.
      (* [e; u; a] *)
      zap (zex_E _ (omegaT (Γ := [ι V; ι V; ι V]))); [apply tot_omega|].
      (* [w; e; u; a] *)
      zap (zex_I _ _ x3). zap zand_I; [zap zeq_refl|].
      zap (zex_I _ _ x0). zap zand_I; [zhyp|].
      apply (ziff_E2 _ _ (Or (zAll (Neg (zMem x0 x4)))
                             (zEx (And (zMem x0 x1) (zAll (zIff (zMem x0 x5) (Or (zMem x0 x1) (zEq x0 x1)))))))).
      { zinst OmB x3. zhyp. }
      zap zor_I1. zap (zeq_subst _ (zAll (Neg (zMem x0 x1))) x1 x3); [|zhyp].
      zap (zeq_trans _ x1 x2 x3); [zap zeq_sym; zhyp|zhyp].
    + zexh. zexh2. zexh2.
      (* [s; u'; b; a] *)
      apply (deriv_cut ZC Pr RIZF (φ := SucAt vz (vs (vs vz)))).
      { apply (ziff_E1 _ _ _ (ren_deriv (rho2 vz (vs (vs vz))) _ _ suc_graph)). zhyp. }
      zap (zex_E _ (And (zEq x0 x3) (zEx (And omegaT (zMem x1 x0))))); [zhyp|]. apply zand_L.
      zap (zex_E _ (And omegaT (zMem x1 x0))); [zhyp|]. apply zand_L.
      (* [w; u; s; u'; b; a] *)
      zap (zex_I _ _ x5). zap zand_I; [zap zeq_refl|].
      zap (zex_I _ _ x0). zap zand_I; [zhyp|].
      zap (zeq_subst _ (zMem x0 x1) x2 x5).
      { zap (zeq_trans _ x2 x3 x5); [zap zeq_sym; zhyp|zhyp]. }
      apply (ziff_E2 _ _ (Or (zAll (Neg (zMem x0 x3)))
                             (zEx (And (zMem x0 x1) (zAll (zIff (zMem x0 x4) (Or (zMem x0 x1) (zEq x0 x1)))))))).
      { zinst OmB x2. zhyp. }
      zap zor_I2. zap (zex_I _ _ x4). zap zand_I; [|zhyp].
      zap (zeq_subst _ (zMem x0 x1) x1 x4); zhyp.
Qed.
