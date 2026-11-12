(** * CC et DC dans IZF : les schémas

    Suite de [IZFChoice.v] : les énoncés de CC et de DC dans L_IZF et
    leurs preuves dans IZFε + CC (resp. + DC). *)

From Stdlib Require Import List.
Import ListNotations.
From SF.Syntax Require Import Spec Terms Renaming Vectors.
From SF.Calculus Require Import System Rules.
From SF.Logic Require Import Judgment Propositional.
From SF.Functional Require Import Arrow.
From SF.Quantifiers Require Import Quant Order.
From SF.Extensions Require Import RuleExt.
From SF.SetTheory Require Import IZFe IZFeBasic IZFeExt IZFeIZF IZFeCC IZFeDC IZFChoice.

Local Notation ι a := (Spec [] a).
Tactic Notation "qap" uconstr(t) := eapply t; try typeclasses eauto.
Ltac hyp := apply d_ax; simpl; auto 20.
Ltac hypc := apply d_ax; repeat (first [left; reflexivity | right]).

(** ** Le choix dénombrable de IZF *)

Local Notation x7 := (var0 (vs (vs (vs (vs (vs (vs (vs vz)))))))).
Local Notation x8 := (var0 (vs (vs (vs (vs (vs (vs (vs (vs vz))))))))).
Local Notation x9 := (var0 (vs (vs (vs (vs (vs (vs (vs (vs (vs vz)))))))))).
Local Notation x10 := (var0 (vs (vs (vs (vs (vs (vs (vs (vs (vs (vs vz))))))))))).
Local Notation x11 := (var0 (vs (vs (vs (vs (vs (vs (vs (vs (vs (vs (vs vz)))))))))))).
Local Notation x12 := (var0 (vs (vs (vs (vs (vs (vs (vs (vs (vs (vs (vs (vs vz))))))))))))).
Local Notation φ3 := (vs (vs (vs vz))).
Local Notation φ4 := (vs (vs (vs (vs vz)))).
Local Notation φ5 := (vs (vs (vs (vs (vs vz))))).
Local Notation φ6 := (vs (vs (vs (vs (vs (vs vz)))))).
Local Notation φ7 := (vs (vs (vs (vs (vs (vs (vs vz))))))).
Local Notation φ8 := (vs (vs (vs (vs (vs (vs (vs (vs vz)))))))).

(** L'extensionnalité en le second argument : ∀a b b′. b ≃ b′ → ψ(a, b) → ψ(a, b′). *)
Definition ExtR2 : form [σR] :=
  All (All (All (Imp (Eqv x1 x0) (Imp (app2 φ3 x2 x1) (app2 φ3 x2 x0))))).

Lemma extR2_E :
  IZFm [ι V; ι V; ι V; σR]
    [All (All (All (Imp (Eqv x1 x0) (Imp (app2 φ6 x2 x1) (app2 φ6 x2 x0)))));
     Eqv x1 x2; app2 φ3 x0 x1]
    (app2 φ3 x0 x2).
Proof.
  qap (imp_E C Pr RIZFm _ (app2 φ3 x0 x1)); [|hyp].
  qap (imp_E C Pr RIZFm _ (Eqv x1 x2)); [|hyp].
  qap (qall_E C RIZFm V hV _ (Imp (Eqv x2 x0) (Imp (app2 φ4 x1 x2) (app2 φ4 x1 x0))) x2).
  qap (qall_E C RIZFm V hV _ (All (Imp (Eqv x1 x0) (Imp (app2 φ5 x2 x1) (app2 φ5 x2 x0)))) x1).
  qap (qall_E C RIZFm V hV _ (All (All (Imp (Eqv x1 x0) (Imp (app2 φ6 x2 x1) (app2 φ6 x2 x0))))) x0).
  hyp.
Qed.

(** Le schéma de IZF, pour une relation φ(n, y) : dans le contexte [φ],
    ∀w. Nat(w) → ∀X. (∀n. n ∈ w → ∃y. y ∈ X ∧ φ(n, y)) →
      ∃f. (∀n. n ∈ w → ∃y. y ∈ X ∧ φ(n, y) ∧ ∃p. p ∈ f ∧ Op(p, n, y))
        ∧ (∀n y y′ p p′. p ∈ f → Op(p, n, y) → p′ ∈ f → Op(p′, n, y′) → y ≃ y′)
        ∧ (∀p. p ∈ f → ∃n. n ∈ w ∧ ∃y. y ∈ X ∧ Op(p, n, y)). *)

(** Dans le contexte [X; w; φ]. *)
Definition HypC : form [ι V; ι V; σR] :=
  All (Imp (Mem x0 x2) (Ex (And (Mem x0 x2) (app2 φ4 x1 x0)))).

(** Dans le contexte [f; X; w; φ]. *)
Definition TotC : form [ι V; ι V; ι V; σR] :=
  All (Imp (Mem x0 x3) (Ex (And (Mem x0 x3) (And (app2 φ5 x1 x0) (Ex (And (Mem x0 x3) (OpF x0 x2 x1))))))).
Definition FunC : form [ι V; ι V; ι V; σR] :=
  All (All (All (All (All (Imp (Mem x1 x5) (Imp (OpF x1 x4 x3) (Imp (Mem x0 x5) (Imp (OpF x0 x4 x2) (Eqv x3 x2))))))))).
Definition SubC : form [ι V; ι V; ι V; σR] :=
  All (Imp (Mem x0 x1) (Ex (And (Mem x0 x4) (Ex (And (Mem x0 x4) (OpF x2 x1 x0)))))).

Definition IZF_cc : form [σR] :=
  All (Imp (NatF x0) (All (Imp HypC (Ex (And TotC (And FunC SubC)))))).

(** Un élément de f est ≃ à un ⟨n₀, y₀⟩ ε f avec n₀ ε ω, y₀ ε X   (contexte [p; f; X]). *)
Lemma rep_l : IZFm [ι V; ι V; ι V]
  [All (Imp (Eps x0 x2) (Ex (And (Eps x0 Omega) (Ex (And (Eps x0 x5) (EqV x2 (OPair x1 x0)))))));
   Mem x0 x1]
  (Ex (Ex (And (Eps x1 Omega) (And (Eps x0 x4) (And (Eps (OPair x1 x0) x3) (OpF x2 x1 x0)))))).
Proof.
  qap (qex_E C RIZFm V hV _ (And (Eqv x1 x0) (Eps x0 x2))).
  { qap iff_E1; [exact (axm A_mem _ (vV2 x0 x1))|hyp]. }
  (* [p0; p; f; X] *)
  qap (qex_E C RIZFm V hV _ (And (Eps x0 Omega) (Ex (And (Eps x0 x5) (EqV x2 (OPair x1 x0)))))).
  { qap (imp_E C Pr RIZFm _ (Eps x0 x2)).
    - qap (qall_E C RIZFm V hV _ (Imp (Eps x0 x3) (Ex (And (Eps x0 Omega) (Ex (And (Eps x0 x6) (EqV x2 (OPair x1 x0))))))) x0). hyp.
    - qap (and_E2 C Pr RIZFm _ (Eqv x1 x0)). hyp. }
  (* [n0; p0; p; f; X] *)
  qap (qex_E C RIZFm V hV _ (And (Eps x0 x5) (EqV x2 (OPair x1 x0)))).
  { qap (and_E2 C Pr RIZFm _ (Eps x0 Omega)). hyp. }
  (* [y0; n0; p0; p; f; X] *)
  qap (qex_I C RIZFm V hV _ _ x1). qap (qex_I C RIZFm V hV _ _ x0).
  qap (and_I C Pr RIZFm); [|qap (and_I C Pr RIZFm); [|qap (and_I C Pr RIZFm)]].
  - qap (and_E1 C Pr RIZFm _ _ (Ex (And (Eps x0 x6) (EqV x3 (OPair x2 x0))))). hyp.
  - qap (and_E1 C Pr RIZFm _ _ (EqV x2 (OPair x1 x0))). hyp.
  - refine (qeq_subst C RIZFm V hV _ (Eps x0 x5) x2 (OPair x1 x0) _ _).
    + qap (and_E2 C Pr RIZFm _ (Eps x0 x5)). hyp.
    + qap (and_E2 C Pr RIZFm _ (Eqv x3 x2)). hyp.
  - uses op_congr (vV6 (OPair x1 x0) x1 x0 x3 x1 x0).
    + refine (qeq_subst C RIZFm V hV _ (Eqv x0 x4) x2 (OPair x1 x0) _ _).
      * qap (and_E2 C Pr RIZFm _ (Eps x0 x5)). hyp.
      * uses eqv_sym (vV2 x3 x2). qap (and_E1 C Pr RIZFm _ _ (Eps x2 x4)). hyp.
    + uses eqv_refl1 (vV1 x1).
    + uses eqv_refl1 (vV1 x0).
    + uses op_base (vV2 x1 x0).
Qed.

(** La fonctionnalité de f, pour un même n₀   (contexte [n; y; y′; f]). *)
Lemma fun_use : IZFm [ι V; ι V; ι V; ι V]
  [All (All (All (Imp (Eps (OPair x2 x1) x6) (Imp (Eps (OPair x2 x0) x6) (EqV x1 x0)))));
   Eps (OPair x0 x1) x3; Eps (OPair x0 x2) x3]
  (EqV x1 x2).
Proof.
  qap (imp_E C Pr RIZFm _ (Eps (OPair x0 x2) x3)); [|hyp].
  qap (imp_E C Pr RIZFm _ (Eps (OPair x0 x1) x3)); [|hyp].
  qap (qall_E C RIZFm V hV _ (Imp (Eps (OPair x1 x2) x4) (Imp (Eps (OPair x1 x0) x4) (EqV x2 x0))) x2).
  qap (qall_E C RIZFm V hV _ (All (Imp (Eps (OPair x2 x1) x5) (Imp (Eps (OPair x2 x0) x5) (EqV x1 x0)))) x1).
  qap (qall_E C RIZFm V hV _ (All (All (Imp (Eps (OPair x2 x1) x6) (Imp (Eps (OPair x2 x0) x6) (EqV x1 x0))))) x0).
  hyp.
Qed.

(** Les composantes du schéma ε instancié en (X, φ), dans le contexte [f; X; w; φ]
    (et [X; w; φ] pour l'hypothèse). *)
Definition EPSe : form [ι V; ι V; σR] :=
  All (Imp (Eps x0 Omega) (Ex (And (Eps x0 x2) (app2 φ4 x1 x0)))).
Definition TOTe : form [ι V; ι V; ι V; σR] :=
  All (Imp (Eps x0 Omega) (Ex (And (Eps x0 x3) (And (Eps (OPair x1 x0) x2) (app2 φ5 x1 x0))))).
Definition FUNe : form [ι V; ι V; ι V; σR] :=
  All (All (All (Imp (Eps (OPair x2 x1) x3) (Imp (Eps (OPair x2 x0) x3) (EqV x1 x0))))).
Definition SUBe : form [ι V; ι V; ι V; σR] :=
  All (Imp (Eps x0 x1) (Ex (And (Eps x0 Omega) (Ex (And (Eps x0 x4) (EqV x2 (OPair x1 x0))))))).

(** L'hypothèse de IZF donne celle du schéma ε   (contexte [X; w; φ]). *)
Lemma epshyp_l : IZFm [ι V; ι V; σR]
  [All (All (All (Imp (Eqv x1 x0) (Imp (app2 φ5 x2 x1) (app2 φ5 x2 x0))))); NatF x1; HypC] EPSe.
Proof.
  unfold EPSe. qap (qall_I C RIZFm V hV). qap (imp_I C Pr RIZFm).
  (* [n; X; w; φ] *)
  qap (qex_E C RIZFm V hV _ (And (Mem x0 x2) (app2 φ4 x1 x0))).
  { qap (imp_E C Pr RIZFm _ (Mem x0 x2)).
    - qap (qall_E C RIZFm V hV _ (Imp (Mem x0 x3) (Ex (And (Mem x0 x3) (app2 φ5 x1 x0)))) x0). hypc.
    - uses omega_sub_nat (vV2 x0 x2); [hypc|hyp]. }
  (* [y; n; X; w; φ] *)
  qap (qex_E C RIZFm V hV _ (And (Eqv x1 x0) (Eps x0 x3))).
  { qap iff_E1; [exact (axm A_mem _ (vV2 x0 x2))|]. qap (and_E1 C Pr RIZFm _ _ (app2 φ4 x1 x0)). hyp. }
  (* [y'; y; n; X; w; φ] *)
  qap (qex_I C RIZFm V hV _ _ x0). qap (and_I C Pr RIZFm).
  - qap (and_E2 C Pr RIZFm _ (Eqv x1 x0)). hyp.
  - uses extR2_E (vVVVR x2 x1 x0 (eta σR (Γ := [ι V; ι V; ι V; ι V; ι V; σR]) φ5)); [hypc| |].
    + qap (and_E1 C Pr RIZFm _ _ (Eps x0 x3)). hyp.
    + qap (and_E2 C Pr RIZFm _ (Mem x1 x3)). hyp.
Qed.

(** La totalité   (contexte [f; X; w; φ]). *)
Lemma cc_tot_l : IZFm [ι V; ι V; ι V; σR]
  [All (All (All (Imp (Eqv x2 x1) (Imp (app2 φ6 x2 x0) (app2 φ6 x1 x0))))); NatF x2; TOTe] TotC.
Proof.
  unfold TotC. qap (qall_I C RIZFm V hV). qap (imp_I C Pr RIZFm).
  (* [n; f; X; w; φ] *)
  qap (qex_E C RIZFm V hV _ (And (Eqv x1 x0) (Eps x0 Omega))).
  { qap iff_E1; [exact (axm A_mem _ (vV2 x0 Omega))|]. uses nat_sub_omega (vV2 x0 x3); [hypc|hyp]. }
  (* [n'; n; f; X; w; φ] *)
  qap (qex_E C RIZFm V hV _ (And (Eps x0 x4) (And (Eps (OPair x1 x0) x3) (app2 φ6 x1 x0)))).
  { qap (imp_E C Pr RIZFm _ (Eps x0 Omega)).
    - qap (qall_E C RIZFm V hV _ (Imp (Eps x0 Omega) (Ex (And (Eps x0 x5) (And (Eps (OPair x1 x0) x4) (app2 φ7 x1 x0))))) x0).
      hypc.
    - qap (and_E2 C Pr RIZFm _ (Eqv x1 x0)). hyp. }
  (* [y; n'; n; f; X; w; φ] *)
  qap (qex_I C RIZFm V hV _ _ x0). qap (and_I C Pr RIZFm); [|qap (and_I C Pr RIZFm)].
  - uses eps_mem (vV2 x0 x4). qap (and_E1 C Pr RIZFm _ _ (And (Eps (OPair x1 x0) x3) (app2 φ6 x1 x0))). hyp.
  - uses extR_E (vVVVR x1 x2 x0 (eta σR (Γ := [ι V; ι V; ι V; ι V; ι V; ι V; σR]) φ6)); [hypc| |].
    + uses eqv_sym (vV2 x2 x1). qap (and_E1 C Pr RIZFm _ _ (Eps x1 Omega)). hyp.
    + qap (and_E2 C Pr RIZFm _ (Eps (OPair x1 x0) x3)). qap (and_E2 C Pr RIZFm _ (Eps x0 x4)). hyp.
  - refine (qex_I C RIZFm V hV _ _ (OPair x1 x0) _). qap (and_I C Pr RIZFm).
    + uses eps_mem (vV2 (OPair x1 x0) x3).
      qap (and_E1 C Pr RIZFm _ _ (app2 φ6 x1 x0)). qap (and_E2 C Pr RIZFm _ (Eps x0 x4)). hyp.
    + uses op_congr (vV6 (OPair x1 x0) x1 x0 (OPair x1 x0) x2 x0).
      * uses eqv_refl1 (vV1 (OPair x1 x0)).
      * uses eqv_sym (vV2 x2 x1). qap (and_E1 C Pr RIZFm _ _ (Eps x1 Omega)). hyp.
      * uses eqv_refl1 (vV1 x0).
      * uses op_base (vV2 x1 x0).
Qed.

(** Le domaine   (contexte [f; X; w; φ]). *)
Lemma cc_sub_l : IZFm [ι V; ι V; ι V; σR] [NatF x2; SUBe] SubC.
Proof.
  unfold SubC. qap (qall_I C RIZFm V hV). qap (imp_I C Pr RIZFm).
  (* [p; f; X; w; φ] *)
  qap (qex_E C RIZFm V hV _ (Ex (And (Eps x1 Omega) (And (Eps x0 x4) (And (Eps (OPair x1 x0) x3) (OpF x2 x1 x0)))))).
  { uses rep_l (vV3 x0 x1 x2); [hypc|hyp]. }
  qap (qex_E C RIZFm V hV _ (And (Eps x1 Omega) (And (Eps x0 x4) (And (Eps (OPair x1 x0) x3) (OpF x2 x1 x0))))); [hyp|].
  (* [y0; n0; p; f; X; w; φ] *)
  qap (qex_I C RIZFm V hV _ _ x1). qap (and_I C Pr RIZFm).
  - uses omega_sub_nat (vV2 x1 x5); [hypc|].
    qap (and_E1 C Pr RIZFm _ _ (And (Eps x0 x4) (And (Eps (OPair x1 x0) x3) (OpF x2 x1 x0)))). hyp.
  - qap (qex_I C RIZFm V hV _ _ x0). qap (and_I C Pr RIZFm).
    + uses eps_mem (vV2 x0 x4). qap (and_E1 C Pr RIZFm _ _ (And (Eps (OPair x1 x0) x3) (OpF x2 x1 x0))).
      qap (and_E2 C Pr RIZFm _ (Eps x1 Omega)). hyp.
    + qap (and_E2 C Pr RIZFm _ (Eps (OPair x1 x0) x3)). qap (and_E2 C Pr RIZFm _ (Eps x0 x4)).
      qap (and_E2 C Pr RIZFm _ (Eps x1 Omega)). hyp.
Qed.

(** La fonctionnalité   (contexte [f; X; w; φ]) : deux représentants n₀, n₁ ε ω
    du même n sont égaux au sens de Leibniz ([nat_leib]), puis on applique
    la fonctionnalité du schéma ε. *)
Lemma cc_fun_l : IZFm [ι V; ι V; ι V; σR] [FUNe; SUBe] FunC.
Proof.
  unfold FunC.
  do 5 qap (qall_I C RIZFm V hV). do 4 qap (imp_I C Pr RIZFm).
  (* [p'; p; y'; y; n; f; X; w; φ] *)
  qap (qex_E C RIZFm V hV _ (Ex (And (Eps x1 Omega) (And (Eps x0 x8) (And (Eps (OPair x1 x0) x7) (OpF x3 x1 x0)))))).
  { uses rep_l (vV3 x1 x5 x6); [hypc|hyp]. }
  qap (qex_E C RIZFm V hV _ (And (Eps x1 Omega) (And (Eps x0 x8) (And (Eps (OPair x1 x0) x7) (OpF x3 x1 x0))))); [hyp|].
  (* [y0; n0; p'; p; y'; y; n; f; X; w; φ] *)
  qap (qex_E C RIZFm V hV _ (Ex (And (Eps x1 Omega) (And (Eps x0 x10) (And (Eps (OPair x1 x0) x9) (OpF x4 x1 x0)))))).
  { uses rep_l (vV3 x2 x7 x8); [hypc|hyp]. }
  qap (qex_E C RIZFm V hV _ (And (Eps x1 Omega) (And (Eps x0 x10) (And (Eps (OPair x1 x0) x9) (OpF x4 x1 x0))))); [hyp|].
  (* [y1; n1; y0; n0; p'; p; y'; y; n; f; X; w; φ] *)
  set (Ha := And (Eps x3 Omega) (And (Eps x2 x10) (And (Eps (OPair x3 x2) x9) (OpF x5 x3 x2)))
             : form [ι V; ι V; ι V; ι V; ι V; ι V; ι V; ι V; ι V; ι V; ι V; ι V; σR]).
  assert (OA : forall Ξ, In Ha Ξ -> IZFm _ Ξ (OpF x5 x3 x2)).
  { intros Ξ H. qap (and_E2 C Pr RIZFm _ (Eps (OPair x3 x2) x9)). qap (and_E2 C Pr RIZFm _ (Eps x2 x10)).
    qap (and_E2 C Pr RIZFm _ (Eps x3 Omega)). apply d_ax, H. }
  assert (OB : forall Ξ, In (And (Eps x1 Omega) (And (Eps x0 x10) (And (Eps (OPair x1 x0) x9) (OpF x4 x1 x0)))
                     : form [ι V; ι V; ι V; ι V; ι V; ι V; ι V; ι V; ι V; ι V; ι V; ι V; σR]) Ξ ->
                 IZFm _ Ξ (OpF x4 x1 x0)).
  { intros Ξ H. qap (and_E2 C Pr RIZFm _ (Eps (OPair x1 x0) x9)). qap (and_E2 C Pr RIZFm _ (Eps x0 x10)).
    qap (and_E2 C Pr RIZFm _ (Eps x1 Omega)). apply d_ax, H. }
  (* y ≃ y₀ ≃ y₁ ≃ y′ *)
  uses eqv_trans (vV3 x7 x2 x6).
  - uses op_inj2 (vV5 x5 x8 x7 x3 x2); [hypc|apply OA; repeat (first [left; reflexivity | right])].
  - uses eqv_trans (vV3 x2 x0 x6).
    + uses eqV_eqv (vV2 x2 x0).
      uses fun_use (vV4 x3 x2 x0 x9); [hypc| |].
      * qap (and_E1 C Pr RIZFm _ _ (OpF x5 x3 x2)). qap (and_E2 C Pr RIZFm _ (Eps x2 x10)).
        qap (and_E2 C Pr RIZFm _ (Eps x3 Omega)). hypc.
      * refine (qeq_subst C RIZFm V hV _ (Eps (OPair x0 x1) x10) x1 x3 _ _).
        -- uses nat_leib (vV2 x1 x3).
           ++ qap (and_E1 C Pr RIZFm _ _ (And (Eps x0 x10) (And (Eps (OPair x1 x0) x9) (OpF x4 x1 x0)))). hypc.
           ++ qap (and_E1 C Pr RIZFm _ _ (And (Eps x2 x10) (And (Eps (OPair x3 x2) x9) (OpF x5 x3 x2)))). hypc.
           ++ uses eqv_trans (vV3 x1 x8 x3).
              ** uses eqv_sym (vV2 x8 x1). uses op_inj1 (vV5 x4 x8 x6 x1 x0); [hypc|apply OB; repeat (first [left; reflexivity | right])].
              ** uses op_inj1 (vV5 x5 x8 x7 x3 x2); [hypc|apply OA; repeat (first [left; reflexivity | right])].
        -- qap (and_E1 C Pr RIZFm _ _ (OpF x4 x1 x0)). qap (and_E2 C Pr RIZFm _ (Eps x0 x10)).
           qap (and_E2 C Pr RIZFm _ (Eps x1 Omega)). hypc.
    + uses eqv_sym (vV2 x6 x0). uses op_inj2 (vV5 x4 x8 x6 x1 x0); [hypc|apply OB; repeat (first [left; reflexivity | right])].
Qed.
