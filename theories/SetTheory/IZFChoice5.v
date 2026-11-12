(** * DC dans IZF : le théorème

    IZFε + DC prouve le choix dépendant de IZF énoncé dans L_IZF
    ([IZF_dc], [IZFChoice4.v]), pour toute formule de L_IZF ([izf_dc_lizf]). *)

From Stdlib Require Import List.
Import ListNotations.
From SF.Syntax Require Import Spec Terms Renaming Vectors.
From SF.Calculus Require Import System Rules.
From SF.Logic Require Import Judgment Propositional.
From SF.Functional Require Import Arrow.
From SF.Quantifiers Require Import Quant Order.
From SF.Extensions Require Import RuleExt.
From SF.SetTheory Require Import IZFe IZFeBasic IZFeExt IZFeIZF IZFeCC IZFeDC IZFChoice IZFChoice2 IZFChoice3 IZFChoice4.

Local Notation ι a := (Spec [] a).
Tactic Notation "qap" uconstr(t) := eapply t; try typeclasses eauto.
Ltac hyp := apply d_ax; simpl; auto 20.
Ltac hypc := apply d_ax; repeat (first [left; reflexivity | right]).

Local Notation x7 := (var0 (vs (vs (vs (vs (vs (vs (vs vz)))))))).
Local Notation φ4 := (vs (vs (vs (vs vz)))).
Local Notation φ5 := (vs (vs (vs (vs (vs vz))))).
Local Notation φ6 := (vs (vs (vs (vs (vs (vs vz)))))).
Local Notation φ8 := (vs (vs (vs (vs (vs (vs (vs (vs vz)))))))).
Local Notation φ9 := (vs (vs (vs (vs (vs (vs (vs (vs (vs vz))))))))).
Local Notation C5 := [ι V; ι V; ι V; ι V; σR].
Local Notation C6 := [ι V; ι V; ι V; ι V; ι V; σR].

(** ** De IZF⁻ε à IZFε + DC *)

Lemma liftD {Γ Ξ φ} : IZFm Γ Ξ φ -> IZFeD Γ Ξ φ.
Proof. apply (deriv_mono _ C C RIZFm RIZFeD); [apply sys_le_refl|typeclasses eauto]. Qed.

Lemma useD {Γ0 Ξ0 φ} (H : IZFeD Γ0 Ξ0 φ) {Γ} (w : vec isym Γ0 Γ) (Ξ : list (form Γ)) :
  (forall χ, In χ Ξ0 -> IZFeD Γ Ξ (vsubst χ w)) -> IZFeD Γ Ξ (vsubst φ w).
Proof.
  intros Hh. apply (deriv_cut_gen _ _ _ (deriv_subst _ _ _ H Γ w)).
  intros χ Hχ. unfold vsubst_list in Hχ. apply in_map_iff in Hχ as (χ0 & <- & Hχ0). apply Hh, Hχ0.
Qed.

Tactic Notation "usesD" constr(H) uconstr(w) :=
  refine (useD (liftD H) w _ _); [intros ? Hin; repeat (destruct Hin as [<-|Hin]); try contradiction].
Tactic Notation "usesD0" constr(H) :=
  refine (deriv_cut_gen _ _ _ (liftD H) _ _); [intros ? Hin; repeat (destruct Hin as [<-|Hin]); try contradiction].

Lemma axmD {Γ} (Ξ : list (form Γ)) (v : vec isym [ι V; σR] Γ) : IZFeD Γ Ξ (vsubst (d_concl A_dc) v).
Proof. apply (rule_inc C Pr RIZFeD (fun _ : unit => A_dc) tt Ξ v _ eq_refl). intros p []. Qed.

Lemma mem_rep : IZFm [ι V; ι V] [Mem x0 x1] (Ex (And (Eqv x1 x0) (Eps x0 x2))).
Proof. qap iff_E1; [exact (axm A_mem _ (vV2 x0 x1))|hyp]. Qed.

(** Les composantes du schéma ε, en [f; e₀; x₀; X; w; φ]. *)
Definition TOT6 : form C6 := All (Imp (Eps x0 Omega) (Ex (And (Eps x0 x5) (Eps (OPair x1 x0) x2)))).
Definition FUN6 : form C6 := All (All (All (Imp (Eps (OPair x2 x1) x3) (Imp (Eps (OPair x2 x0) x3) (EqV x1 x0))))).
Definition SUB6 : form C6 := All (Imp (Eps x0 x1) (Ex (And (Eps x0 Omega) (Ex (And (Eps x0 x6) (EqV x2 (OPair x1 x0))))))).
Definition START6 : form C6 := Eps (OPair Empty x1) x0.
Definition STEP6 : form C6 :=
  All (All (All (Imp (Eps (OPair x2 x1) x3) (Imp (Eps (OPair (Suc x2) x0) x3) (app2 φ8 x1 x0))))).

(** ** IZFε + DC prouve le choix dépendant de IZF *)

Theorem izf_dc : IZFeD [σR] [ExtR; ExtR2] IZF_dc.
Proof.
  unfold IZF_dc. qap (qall_I C RIZFeD V hV). qap (imp_I C Pr RIZFeD).
  qap (qall_I C RIZFeD V hV). qap (imp_I C Pr RIZFeD).
  qap (qall_I C RIZFeD V hV). qap (imp_I C Pr RIZFeD).
  (* [x0; X; w; φ] *)
  qap (qex_E C RIZFeD V hV _ (And (Eqv x1 x0) (Eps x0 x2))).
  { usesD mem_rep (vV2 x0 x1). hyp. }
  (* [e0; x0; X; w; φ] *)
  qap (qex_E C RIZFeD V hV _ (And TOT6 (And FUN6 (And SUB6 (And START6 STEP6))))).
  { qap (imp_E C Pr RIZFeD _ (Eps x0 x2)).
    - qap (qall_E C RIZFeD V hV _
        (Imp (Eps x0 x3) (Ex (And (All (Imp (Eps x0 Omega) (Ex (And (Eps x0 x6) (Eps (OPair x1 x0) x2)))))
          (And (All (All (All (Imp (Eps (OPair x2 x1) x3) (Imp (Eps (OPair x2 x0) x3) (EqV x1 x0))))))
          (And (All (Imp (Eps x0 x1) (Ex (And (Eps x0 Omega) (Ex (And (Eps x0 x7) (EqV x2 (OPair x1 x0))))))))
          (And (Eps (OPair Empty x1) x0)
               (All (All (All (Imp (Eps (OPair x2 x1) x3) (Imp (Eps (OPair (Suc x2) x0) x3) (app2 φ9 x1 x0))))))))))))
        x0).
      qap (imp_E C Pr RIZFeD _ (All (Imp (Eps x0 x3) (Ex (And (Eps x0 x4) (app2 φ6 x1 x0)))))).
      + exact (axmD _ (vVR x2 (eta σR (Γ := C5) φ4))).
      + usesD0 dchyp_l; hypc.
    - qap (and_E2 C Pr RIZFeD _ (Eqv x1 x0)). hyp. }
  (* [f; e0; x0; X; w; φ] *)
  qap (qex_I C RIZFeD V hV _ _ x0).
  qap (and_I C Pr RIZFeD); [|qap (and_I C Pr RIZFeD); [|qap (and_I C Pr RIZFeD); [|qap (and_I C Pr RIZFeD)]]].
  - usesD0 dc_tot_l; [hypc|].
    qap (and_E1 C Pr RIZFeD _ _ (And FUN6 (And SUB6 (And START6 STEP6)))). hypc.
  - usesD cc_fun_l (vVVVR x0 x3 x4 (eta σR (Γ := C6) φ5)).
    + qap (and_E1 C Pr RIZFeD _ _ (And SUB6 (And START6 STEP6))). qap (and_E2 C Pr RIZFeD _ TOT6). hypc.
    + qap (and_E1 C Pr RIZFeD _ _ (And START6 STEP6)). qap (and_E2 C Pr RIZFeD _ FUN6).
      qap (and_E2 C Pr RIZFeD _ TOT6). hypc.
  - usesD cc_sub_l (vVVVR x0 x3 x4 (eta σR (Γ := C6) φ5)); [hypc|].
    qap (and_E1 C Pr RIZFeD _ _ (And START6 STEP6)). qap (and_E2 C Pr RIZFeD _ FUN6).
    qap (and_E2 C Pr RIZFeD _ TOT6). hypc.
  - usesD0 dc_start_l.
    + qap (and_E1 C Pr RIZFeD _ _ STEP6). qap (and_E2 C Pr RIZFeD _ SUB6). qap (and_E2 C Pr RIZFeD _ FUN6).
      qap (and_E2 C Pr RIZFeD _ TOT6). hypc.
    + qap (and_E1 C Pr RIZFeD _ _ (Eps x1 x3)). hyp.
  - usesD0 dc_step_l; [hypc|hypc| |].
    + qap (and_E2 C Pr RIZFeD _ START6). qap (and_E2 C Pr RIZFeD _ SUB6). qap (and_E2 C Pr RIZFeD _ FUN6).
      qap (and_E2 C Pr RIZFeD _ TOT6). hypc.
    + qap (and_E1 C Pr RIZFeD _ _ (And START6 STEP6)). qap (and_E2 C Pr RIZFeD _ FUN6).
      qap (and_E2 C Pr RIZFeD _ TOT6). hypc.
Qed.

(** Pour toute formule φ(x, y) de L_IZF (avec paramètres), le choix
    dépendant de IZF est un théorème de IZFε + DC. *)
Theorem izf_dc_lizf {Γ} (ψ : form (ι V :: ι V :: Γ)) :
  lizf _ ψ -> IZFeD Γ [] (vsubst IZF_dc (vR1 ψ)).
Proof.
  intros Hl. refine (useD izf_dc (vR1 ψ) [] _).
  intros χ [<-|[<-|[]]]; apply liftD; [apply extR_inst, Hl|apply extR2_inst, Hl].
Qed.
