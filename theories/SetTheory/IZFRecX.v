(** * rec dans IZF : le graphe de rec, lu sur un essai

    Si f est un essai défini en a, de valeur v, le graphe de rec(a) est
    exactement {v} : y = rec(a) ↔ y = v, et β ε rec(a) ↔ β ∈ v. *)

From Stdlib Require Import List.
Import ListNotations.
From SF.Syntax Require Import Spec Terms Renaming Eta Vectors.
From SF.Calculus Require Import System Rules.
From SF.Logic Require Import Judgment Propositional.
From SF.Functional Require Import Arrow.
From SF.Quantifiers Require Import Quant Order.
From SF.SetTheory Require Import Sets IZFe IZF IZFTr IZFLog IZFVal IZFRecV IZFRecW IZFTrSem.

Local Notation ι a := (Spec [] a).
Local Notation φ10 := (vs φ9).
Local Notation φ11 := (vs φ10).
Local Notation φ12 := (vs φ11).
Local Notation x9 := (var0 φ9).
Local Notation x10 := (var0 φ10).

(** Substitution de l'égalité, le but étant d'abord mis sous la forme
    φ[u] (l'unification directe peut être très lente). *)
Tactic Notation "zsubst" uconstr(φ) uconstr(t) uconstr(u) :=
  match goal with |- IZF ?G ?X _ =>
    refine (_ : IZF G X (vsubst (Γ := ι V :: G) φ (inst1 u))); zap (zeq_subst _ φ t u) end.

(** Le graphe de rec_{φ,ψ}(a), les métavariables φ et ψ du contexte. *)
Definition DR {Θ} (xφ : var Θ σP) (xψ : var Θ σR) (a : var Θ (ι V)) : zform (ι V :: Θ) :=
  vsubst Frec (vup [ι V] (vrec (zap1 (vs xφ) x0) (zapp2 (vs (vs xψ)) x0 x1) (DV a))).
(** x ε rec(a) et w = rec(a), traduits. *)
Definition EpsR {Θ} (x : var Θ (ι V)) (xφ : var Θ σP) (xψ : var Θ σR) (a : var Θ (ι V)) : zform Θ :=
  vsubst (Frel (zMem x1 x0)) (v2 (DV x) (DR xφ xψ a)).
Definition EqR {Θ} (w : var Θ (ι V)) (xφ : var Θ σP) (xψ : var Θ σR) (a : var Θ (ι V)) : zform Θ :=
  vsubst (Frel (zEq x1 x0)) (v2 (DV w) (DR xφ xψ a)).

Definition wDR {Γ} (a b c d : ztm Γ V) (φ : var Γ σP) (ψ : var Γ σR) : vec zsym [ι V; ι V; ι V; ι V; σP; σR] Γ :=
  @acons _ zsym Γ (ι V) _ a (@acons _ zsym Γ (ι V) _ b (@acons _ zsym Γ (ι V) _ c (@acons _ zsym Γ (ι V) _ d
    (@acons _ zsym Γ σP _ (eta σP φ) (@acons _ zsym Γ σR _ (eta σR ψ) anil))))).

(** z ∈ v ↔ z ∈ rec(a), lu par RecV   (contexte [z; v; f; a; ψ]). *)
Lemma recv_iff : IZF [ι V; ι V; ι V; ι V; σR] [Att φ2 φ4; InF φ2 φ3 (vs vz)] (zIff (zMem x0 x1) (RecV φ3 φ4 vz)).
Proof.
  apply ziff_I.
  - refine (_ : IZF _ _ (zEx (And (Att vz φ5) (zEx (And (InF (vs vz) φ5 vz) (zMem x2 x0)))))).
    zap (zex_I _ _ x2).
    refine (_ : IZF _ _ (And (Att φ2 φ4) (zEx (And (InF φ3 φ4 vz) (zMem x1 x0))))). zap zand_I; [zhyp|].
    zap (zex_I _ _ x1). refine (_ : IZF _ _ (And (InF φ2 φ3 (vs vz)) (zMem x0 x1))). zap zand_I; zhyp.
  - zdes. zdes2.
    (* [v'; f'; z; v; f; a; ψ] *)
    refine (_ : IZF _ _ (zMem x2 x3)).
    zap (zeq_subst _ (zMem x3 x0) x0 x3); [|refine (_ : IZF _ _ (zMem x2 x0)); zhyp].
    zap (zimp_E _ (InF φ4 φ5 φ3)); [|zhyp]. zap (zimp_E _ (InF (vs vz) φ5 vz)); [|zhyp].
    zinst (Imp (InF φ2 φ6 (vs vz)) (Imp (InF φ5 φ6 vz) (zEq x1 x0))) x3.
    zinst (zAll (Imp (InF φ3 φ7 (vs vz)) (Imp (InF φ6 φ7 vz) (zEq x1 x0)))) x0.
    zinst (Pu vz φ2 φ5) x5.
    zuses att_uniq (wVVR x1 x4 φ6).
    + zuses att_dc (wVR x1 φ6). zhyp.
    + zuses att_cr (wVR x1 φ6). zhyp.
    + zuses att_dc (wVR x4 φ6). zhyp.
    + zuses att_cr (wVR x4 φ6). zhyp.
Qed.

(** Contexte [y; v; f; a; φ; ψ] : rec(a) = y → y = v. *)
Lemma dr_val1 : IZF [ι V; ι V; ι V; ι V; σP; σR] [DR φ3 φ4 (vs (vs vz)); Att φ2 φ5; InF φ2 φ3 (vs vz)] (zEq x0 x1).
Proof.
  zap (zex_E _ (And (zEq x0 x4) (zAll (zIff (zMem x0 x2) (RecV (vs vz) φ7 vz))))); [zhyp|]. apply zand_L.
  (* [a'; y; v; f; a; φ; ψ] *)
  refine (_ : IZF _ _ (zEq x1 x2)).
  zap (zimp_E _ (zAll (zIff (zMem x0 x2) (zMem x0 x3)))).
  { zinst (Imp (zAll (zIff (zMem x0 x3) (zMem x0 x1))) (zEq x2 x0)) x2.
    zinst (zAll (Imp (zAll (zIff (zMem x0 x2) (zMem x0 x1))) (zEq x1 x0))) x1.
    exact (zaxm Z_ext _ anil). }
  zap zall_I.
  (* [z; a'; y; v; f; a; φ; ψ] *)
  apply (ziff_trans _ _ (RecV φ5 φ7 vz)).
  - apply (ziff_trans _ _ (RecV (vs vz) φ7 vz)).
    + zinst (zIff (zMem x0 x3) (RecV φ2 φ8 vz)) x0. zhyp.
    + zsubst (zIff (RecV φ2 φ8 (vs vz)) (RecV vz φ8 (vs vz))) x1 x5; [zhyp|].
      refine (_ : IZF _ _ (zIff (RecV (vs vz) φ7 vz) (RecV (vs vz) φ7 vz))). apply ziff_refl.
  - apply ziff_sym. zuses recv_iff (wV4R x0 x3 x4 x5 φ7); zhyp.
Qed.

(** Contexte [y; v; f; a; φ; ψ] : y = v → rec(a) = y. *)
Lemma dr_val2 : IZF [ι V; ι V; ι V; ι V; σP; σR] [zEq x0 x1; Att φ2 φ5; InF φ2 φ3 (vs vz)] (DR φ3 φ4 (vs (vs vz))).
Proof.
  refine (_ : IZF _ _ (zEx (And (zEq x0 x4) (zAll (zIff (zMem x0 x2) (RecV (vs vz) φ7 vz)))))).
  zap (zex_I _ _ x3).
  refine (_ : IZF _ _ (And (zEq x3 x3) (zAll (zIff (zMem x0 x1) (RecV φ4 φ6 vz))))). zap zand_I; [zap zeq_refl|].
  zap zall_I.
  (* [z; y; v; f; a; φ; ψ] *)
  apply (ziff_trans _ _ (zMem x0 x2)).
  - zsubst (zIff (zMem x1 x0) (zMem x1 x3)) x2 x1; [zap zeq_sym; zhyp|].
    refine (_ : IZF _ _ (zIff (zMem x0 x2) (zMem x0 x2))). apply ziff_refl.
  - zuses recv_iff (wV4R x0 x2 x3 x4 φ6); zhyp.
Qed.

(** Contexte [w; v; f; a; φ; ψ] : w = rec(a) ↔ w = v. *)
Lemma eqr_iff : IZF [ι V; ι V; ι V; ι V; σP; σR] [Att φ2 φ5; InF φ2 φ3 (vs vz)] (zIff (EqR vz φ4 φ5 φ3) (zEq x0 x1)).
Proof.
  apply ziff_I.
  - zap (zex_E _ (And (zEq x0 x1) (zEx (And (DR φ5 φ6 φ4) (zEq x1 x0))))); [zhyp|]. apply zand_L.
    zap (zex_E _ (And (DR φ5 φ6 φ4) (zEq x1 x0))); [zhyp|]. apply zand_L.
    (* [y; u; w; v; f; a; φ; ψ] *)
    refine (_ : IZF _ _ (zEq x2 x3)).
    zap (zeq_trans _ x2 x1 x3); [zap zeq_sym; zhyp|].
    zap (zeq_trans _ x1 x0 x3); [zhyp|].
    zuses dr_val1 (wDR x0 x3 x4 x5 φ6 φ7); zhyp.
  - refine (_ : IZF _ _ (zEx (And (zEq x0 x1) (zEx (And (DR φ5 φ6 φ4) (zEq x1 x0)))))).
    zap (zex_I _ _ x0). refine (_ : IZF _ _ (And (zEq x0 x0) (zEx (And (DR φ4 φ5 φ3) (zEq x1 x0))))).
    zap zand_I; [zap zeq_refl|].
    zap (zex_I _ _ x0). refine (_ : IZF _ _ (And (DR φ3 φ4 (vs (vs vz))) (zEq x0 x0))).
    zap zand_I; [|zap zeq_refl].
    zuses dr_val2 (wDR x0 x1 x2 x3 φ4 φ5); zhyp.
Qed.

(** Contexte [β; v; f; a; φ; ψ] : β ε rec(a) ↔ β ∈ v. *)
Lemma epsr_iff : IZF [ι V; ι V; ι V; ι V; σP; σR] [Att φ2 φ5; InF φ2 φ3 (vs vz)] (zIff (EpsR vz φ4 φ5 φ3) (zMem x0 x1)).
Proof.
  apply ziff_I.
  - zap (zex_E _ (And (zEq x0 x1) (zEx (And (DR φ5 φ6 φ4) (zMem x1 x0))))); [zhyp|]. apply zand_L.
    zap (zex_E _ (And (DR φ5 φ6 φ4) (zMem x1 x0))); [zhyp|]. apply zand_L.
    (* [y; u; β; v; f; a; φ; ψ] *)
    refine (_ : IZF _ _ (zMem x2 x3)).
    zsubst (zMem x3 x0) x0 x3; [zuses dr_val1 (wDR x0 x3 x4 x5 φ6 φ7); zhyp|].
    refine (_ : IZF _ _ (zMem x2 x0)).
    zsubst (zMem x0 x1) x1 x2; [zhyp|]. refine (_ : IZF _ _ (zMem x1 x0)). zhyp.
  - refine (_ : IZF _ _ (zEx (And (zEq x0 x1) (zEx (And (DR φ5 φ6 φ4) (zMem x1 x0)))))).
    zap (zex_I _ _ x0). refine (_ : IZF _ _ (And (zEq x0 x0) (zEx (And (DR φ4 φ5 φ3) (zMem x1 x0))))).
    zap zand_I; [zap zeq_refl|].
    zap (zex_I _ _ x1). zap zand_I; [|zhyp].
    zuses dr_val2 (wDR x1 x1 x2 x3 φ4 φ5); [zap zeq_refl|zhyp|zhyp].
Qed.

(** Contexte [β; u; f; α; φ; ψ] : (∃w. w = rec(α) ∧ ψ(w, β)) ↔ R_f(α, β). *)
Lemma chi_rf : IZF [ι V; ι V; ι V; ι V; σP; σR] [Att φ2 φ5; InF φ2 φ3 (vs vz)]
                 (zIff (zEx (And (EqR vz φ5 φ6 φ4) (zapp2 φ6 x0 x1))) (RF φ2 φ5 φ3 vz)).
Proof.
  apply ziff_I.
  - zdes.
    (* [w; β; u; f; α; φ; ψ] *)
    apply (deriv_cut ZC Pr RIZF (φ := zEq x0 x2)).
    { apply (ziff_E1 _ (EqR vz φ5 φ6 φ4)); [|zhyp]. zuses eqr_iff (wDR x0 x2 x3 x4 φ5 φ6); zhyp. }
    refine (_ : IZF _ _ (RF φ3 φ6 φ4 (vs vz))). zap (zex_I _ _ x2).
    refine (_ : IZF _ _ (And (InF φ3 φ4 φ2) (zapp2 φ6 x2 x1))). zap zand_I; [zhyp|].
    zsubst (zapp2 φ7 x0 x2) x0 x2; [zhyp|]. refine (_ : IZF _ _ (zapp2 φ6 x0 x1)). zhyp.
  - zdes.
    (* [u'; β; u; f; α; φ; ψ] *)
    refine (_ : IZF _ _ (zEx (And (EqR vz φ6 φ7 φ5) (zapp2 φ7 x0 x2)))). zap (zex_I _ _ x0).
    refine (_ : IZF _ _ (And (EqR vz φ5 φ6 φ4) (zapp2 φ6 x0 x1))). zap zand_I; [|zhyp].
    apply (ziff_E2 _ _ (zEq x0 x0)); [|zap zeq_refl].
    zuses eqr_iff (wDR x0 x0 x3 x4 φ5 φ6); zhyp.
Qed.
