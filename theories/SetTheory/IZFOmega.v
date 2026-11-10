(** * ω dans IZF : existence du plus petit point fixe

    À partir de l'axiome de l'infini (un ensemble w inductif), on sépare
    N ≜ {n ∈ w | n appartient à tout ensemble inductif}. N est inductif,
    et c'est un point fixe de z ∈ y ↔ z vide ∨ ∃b ∈ y. z = S(b) : le sens
    direct passe par la séparation N′ ≜ {z ∈ N | z vide ∨ ∃b ∈ N. z = S(b)},
    inductive elle aussi, donc contenant N. *)

From Stdlib Require Import List.
Import ListNotations.
From SF.Syntax Require Import Spec Terms Renaming Eta Vectors.
From SF.Calculus Require Import System Rules.
From SF.Logic Require Import Judgment Propositional.
From SF.Functional Require Import Arrow.
From SF.Quantifiers Require Import Quant Order.
From SF.SetTheory Require Import Sets IZFe IZF IZFTr IZFLog IZFVal.

Local Notation ι a := (Spec [] a).

(** Les formules utilisées, dans le contexte où elles apparaissent. *)
Local Notation NF := (zAll (zIff (zMem x0 x1) (And (zMem x0 x2) (zAll (Imp (IndAt vz) (zMem x1 x0)))))).
Local Notation PsiN k := (Or (EmpAt vz) (zEx (And (zMem x0 k) (SucAt (vs vz) vz)))).

Lemma tot_omega0 : IZF [] [] (Tot (omegaT (Γ := []))).
Proof.
  zap (zex_E _ (IndAt vz)); [exact (zaxm Z_inf _ anil)|].
  apply zand_L.
  (* [w] *)
  zap (zex_E _ NF).
  { zinst (zEx (zAll (zIff (zMem x0 x1) (And (zMem x0 x2) (zAll (Imp (IndAt vz) (zMem x1 x0))))))) x0.
    exact (zaxm Z_sep _ (v1 (zAll (Imp (IndAt vz) (zMem x1 x0))))). }
  cbn.
  (* [N; w] : N est inductif *)
  apply (deriv_cut ZC Pr RIZF (φ := IndAt vz)).
  { zap zand_I.
    - zap (zex_E _ (And (zMem x0 x2) (EmpAt vz))); [zhyp|]. apply zand_L.
      (* [e; N; w] *)
      zap (zex_I _ _ x0). zap zand_I; [|zhyp].
      apply (ziff_E2 _ _ (And (zMem x0 x2) (zAll (Imp (IndAt vz) (zMem x1 x0))))).
      { zinst (zIff (zMem x0 x2) (And (zMem x0 x3) (zAll (Imp (IndAt vz) (zMem x1 x0))))) x0. zhyp. }
      zap zand_I; [zhyp|].
      zap zall_I. zap zimp_I. apply zand_L.
      (* [W; e; N; w] *)
      zap (zex_E _ (And (zMem x0 x1) (EmpAt vz))); [zhyp|]. apply zand_L.
      (* [e'; W; e; N; w] *)
      zap (zeq_subst _ (zMem x0 x2) x0 x2); [|zhyp].
      zap zeq_sym. zuses emp_eq (zv2 x2 x0); zhyp.
    - zap zall_I. zap zimp_I. cbn.
      (* [n; N; w] *)
      apply (deriv_cut ZC Pr RIZF (φ := And (zMem x0 x2) (zAll (Imp (IndAt vz) (zMem x1 x0))))).
      { apply (ziff_E1 _ (zMem x0 x1)); [|zhyp].
        zinst (zIff (zMem x0 x2) (And (zMem x0 x3) (zAll (Imp (IndAt vz) (zMem x1 x0))))) x0. zhyp. }
      apply zand_L.
      zap (zex_E _ (And (zMem x0 x3) (SucAt vz (vs vz)))).
      { zap (zimp_E _ (zMem x0 x2)); [|zhyp].
        zinst (Imp (zMem x0 x3) (zEx (And (zMem x0 x4) (SucAt vz (vs vz))))) x0. zhyp. }
      apply zand_L.
      (* [m; n; N; w] *)
      zap (zex_I _ _ x0). zap zand_I; [|zhyp].
      apply (ziff_E2 _ _ (And (zMem x0 x3) (zAll (Imp (IndAt vz) (zMem x1 x0))))).
      { zinst (zIff (zMem x0 x3) (And (zMem x0 x4) (zAll (Imp (IndAt vz) (zMem x1 x0))))) x0. zhyp. }
      zap zand_I; [zhyp|].
      zap zall_I. zap zimp_I. cbn.
      (* [W; m; n; N; w] *)
      apply (deriv_cut ZC Pr RIZF (φ := zMem x2 x0)).
      { zap (zimp_E _ (IndAt vz)); [|zhyp].
        zinst (Imp (IndAt vz) (zMem x3 x0)) x0. zhyp. }
      zap (zex_E _ (And (zMem x0 x1) (SucAt vz φ3))).
      { zap (zimp_E _ (zMem x2 x0)); [|zhyp].
        zinst (Imp (zMem x0 x1) (zEx (And (zMem x0 x2) (SucAt vz (vs vz))))) x2.
        zap (zand_E2 _ (zEx (And (zMem x0 x1) (EmpAt vz)))). zhyp. }
      apply zand_L.
      (* [m'; W; m; n; N; w] *)
      zap (zeq_subst _ (zMem x0 x2) x0 x2); [|zhyp].
      zap zeq_sym. zuses suc_eq (zv3 x2 x0 x3); zhyp. }
  apply zand_L.
  (* [N; w] ; séparation N′ ≜ {z ∈ N | z vide ∨ ∃b ∈ N. z = S(b)} *)
  zap (zex_E _ (zAll (zIff (zMem x0 x1) (And (zMem x0 x2) (PsiN x3))))).
  { zinst (zEx (zAll (zIff (zMem x0 x1) (And (zMem x0 x2) (PsiN x4))))) x0.
    exact (zaxm Z_sep _ (v1 (PsiN x2))). }
  (* [N'; N; w] : N′ est inductif *)
  apply (deriv_cut ZC Pr RIZF (φ := IndAt vz)).
  { zap zand_I.
    - zap (zex_E _ (And (zMem x0 x2) (EmpAt vz))); [zhyp|]. apply zand_L.
      (* [e; N'; N; w] *)
      zap (zex_I _ _ x0). zap zand_I; [|zhyp].
      apply (ziff_E2 _ _ (And (zMem x0 x2) (PsiN x3))).
      { zinst (zIff (zMem x0 x2) (And (zMem x0 x3) (PsiN x4))) x0. zhyp. }
      zap zand_I; [zhyp|]. zap zor_I1. zhyp.
    - zap zall_I. zap zimp_I.
      (* [n; N'; N; w] *)
      apply (deriv_cut ZC Pr RIZF (φ := zMem x0 x2)).
      { zap (zand_E1 _ _ (PsiN x3)). apply (ziff_E1 _ (zMem x0 x1)); [|zhyp].
        zinst (zIff (zMem x0 x2) (And (zMem x0 x3) (PsiN x4))) x0. zhyp. }
      zap (zex_E _ (And (zMem x0 x3) (SucAt vz (vs vz)))).
      { zap (zimp_E _ (zMem x0 x2)); [|zhyp].
        zinst (Imp (zMem x0 x3) (zEx (And (zMem x0 x4) (SucAt vz (vs vz))))) x0. zhyp. }
      apply zand_L.
      (* [m; n; N'; N; w] *)
      zap (zex_I _ _ x0). zap zand_I; [|zhyp].
      apply (ziff_E2 _ _ (And (zMem x0 x3) (PsiN x4))).
      { zinst (zIff (zMem x0 x3) (And (zMem x0 x4) (PsiN x5))) x0. zhyp. }
      zap zand_I; [zhyp|]. zap zor_I2. zap (zex_I _ _ x1). zap zand_I; zhyp. }
  (* N est le point fixe *)
  refine (_ : IZF _ _ (zEx (omegaT (Γ := [ι V; ι V; ι V])))).
  zap (zex_I _ _ x1). zap zall_I.
  (* [z; N'; N; w] *)
  apply ziff_I.
  - apply (deriv_cut ZC Pr RIZF (φ := zMem x0 x1)).
    { zap (zimp_E _ (IndAt (vs vz))); [|zhyp].
      zinst (Imp (IndAt vz) (zMem x1 x0)) x1.
      zap (zand_E2 _ (zMem x0 x3)). apply (ziff_E1 _ (zMem x0 x2)); [|zhyp].
      zinst (zIff (zMem x0 x3) (And (zMem x0 x4) (zAll (Imp (IndAt vz) (zMem x1 x0))))) x0. zhyp. }
    zap (zand_E2 _ (zMem x0 x2)). apply (ziff_E1 _ (zMem x0 x1)); [|zhyp].
    zinst (zIff (zMem x0 x2) (And (zMem x0 x3) (PsiN x4))) x0. zhyp.
  - zap (zor_E _ (EmpAt vz) (zEx (And (zMem x0 x3) (SucAt (vs vz) vz)))); [zhyp| |].
    + zap (zex_E _ (And (zMem x0 x3) (EmpAt vz))); [zhyp|]. apply zand_L.
      (* [e; z; N'; N; w] *)
      zap (zeq_subst _ (zMem x0 x4) x0 x1); [|zhyp].
      zuses emp_eq (zv2 x0 x1); zhyp.
    + zap (zex_E _ (And (zMem x0 x3) (SucAt (vs vz) vz))); [zhyp|]. apply zand_L.
      (* [b; z; N'; N; w] *)
      zap (zex_E _ (And (zMem x0 x4) (SucAt vz (vs vz)))).
      { zap (zimp_E _ (zMem x0 x3)); [|zhyp].
        zinst (Imp (zMem x0 x4) (zEx (And (zMem x0 x5) (SucAt vz (vs vz))))) x0. zhyp. }
      apply zand_L.
      (* [m; b; z; N'; N; w] *)
      zap (zeq_subst _ (zMem x0 x5) x0 x2); [|zhyp].
      zuses suc_eq (zv3 x0 x2 x1); zhyp.
Qed.

Lemma tot_omega {Γ} (Ξ : list (zform Γ)) : IZF Γ Ξ (Tot omegaT).
Proof.
  pose proof (deriv_subst _ _ _ tot_omega0 Γ anil) as K.
  exact (deriv_weaken _ _ _ K _ (incl_nil_l _)).
Qed.

Lemma fun_omega {Γ} (Ξ : list (zform Γ)) : IZF Γ Ξ (Fun omegaT).
Proof.
  pose proof (deriv_subst _ _ _ fun_omega0 Γ anil) as K.
  exact (deriv_weaken _ _ _ K _ (incl_nil_l _)).
Qed.
