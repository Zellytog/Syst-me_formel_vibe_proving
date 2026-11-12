(** * DC dans IZF

    IZFε + DC (schéma ε, [IZFeDC.v]) prouve le choix dépendant de IZF
    énoncé dans L_IZF ([IZF_dc]), pour toute formule de L_IZF
    ([izf_dc_lizf]). Le pas « ⟨n, y⟩ ∈ f, ⟨m, y′⟩ ∈ f, Succ(m, n) ⇒ φ(y, y′) »
    se ramène au pas ε en identifiant les représentants : si n ≃ n₀ et
    m ≃ n₁ avec n₀, n₁ ε ω, alors n₁ ≃ S(n₀), d'où n₁ = S(n₀) au sens de
    Leibniz ([nat_leib]). *)

From Stdlib Require Import List.
Import ListNotations.
From SF.Syntax Require Import Spec Terms Renaming Vectors.
From SF.Calculus Require Import System Rules.
From SF.Logic Require Import Judgment Propositional.
From SF.Functional Require Import Arrow.
From SF.Quantifiers Require Import Quant Order.
From SF.Extensions Require Import RuleExt.
From SF.SetTheory Require Import IZFe IZFeBasic IZFeExt IZFeIZF IZFeCC IZFeDC IZFChoice IZFChoice2 IZFChoice3.

Local Notation ι a := (Spec [] a).
Tactic Notation "qap" uconstr(t) := eapply t; try typeclasses eauto.
Ltac hyp := apply d_ax; simpl; auto 20.
Ltac hypc := apply d_ax; repeat (first [left; reflexivity | right]).
Ltac inc := repeat (first [left; reflexivity | right]).

Local Notation x7 := (var0 (vs (vs (vs (vs (vs (vs (vs vz)))))))).
Local Notation x8 := (var0 (vs (vs (vs (vs (vs (vs (vs (vs vz))))))))).
Local Notation x9 := (var0 (vs (vs (vs (vs (vs (vs (vs (vs (vs vz)))))))))).
Local Notation x10 := (var0 (vs (vs (vs (vs (vs (vs (vs (vs (vs (vs vz))))))))))).
Local Notation x11 := (var0 (vs (vs (vs (vs (vs (vs (vs (vs (vs (vs (vs vz)))))))))))).
Local Notation x12 := (var0 (vs (vs (vs (vs (vs (vs (vs (vs (vs (vs (vs (vs vz))))))))))))).
Local Notation x13 := (var0 (vs (vs (vs (vs (vs (vs (vs (vs (vs (vs (vs (vs (vs vz)))))))))))))).
Local Notation φ4 := (vs (vs (vs (vs vz)))).
Local Notation φ5 := (vs (vs (vs (vs (vs vz))))).
Local Notation φ6 := (vs (vs (vs (vs (vs (vs vz)))))).
Local Notation φ7 := (vs (vs (vs (vs (vs (vs (vs vz))))))).
Local Notation φ8 := (vs (vs (vs (vs (vs (vs (vs (vs vz)))))))).
Local Notation φ9 := (vs (vs (vs (vs (vs (vs (vs (vs (vs vz))))))))).
Local Notation φ10 := (vs (vs (vs (vs (vs (vs (vs (vs (vs (vs vz)))))))))).
Local Notation φ15 := (vs (vs (vs (vs (vs (vs (vs (vs (vs (vs (vs (vs (vs (vs (vs vz))))))))))))))).

(** ** L'énoncé *)

(** Dans le contexte [X; w; φ] : ∀x. x ∈ X → ∃y. y ∈ X ∧ φ(x, y). *)
Definition HypD : form [ι V; ι V; σR] :=
  All (Imp (Mem x0 x1) (Ex (And (Mem x0 x2) (app2 φ4 x1 x0)))).

(** Dans le contexte [f; x₀; X; w; φ]. *)
Definition TotD : form [ι V; ι V; ι V; ι V; σR] :=
  All (Imp (Mem x0 x4) (Ex (And (Mem x0 x4) (Ex (And (Mem x0 x3) (OpF x0 x2 x1)))))).
Definition FunD : form [ι V; ι V; ι V; ι V; σR] :=
  All (All (All (All (All (Imp (Mem x1 x5) (Imp (OpF x1 x4 x3) (Imp (Mem x0 x5) (Imp (OpF x0 x4 x2) (Eqv x3 x2))))))))).
Definition SubD : form [ι V; ι V; ι V; ι V; σR] :=
  All (Imp (Mem x0 x1) (Ex (And (Mem x0 x5) (Ex (And (Mem x0 x5) (OpF x2 x1 x0)))))).
(** ⟨∅, x₀⟩ ∈ f : tout ensemble vide e donne un p ∈ f avec Op(p, e, x₀). *)
Definition StartD : form [ι V; ι V; ι V; ι V; σR] :=
  All (Imp (All (Neg (Mem x0 x1))) (Ex (And (Mem x0 x2) (OpF x0 x1 x3)))).
(** ∀n m y y′ p p′. Succ(m, n) → p ∈ f → Op(p, n, y) → p′ ∈ f → Op(p′, m, y′) → φ(y, y′). *)
Definition StepD : form [ι V; ι V; ι V; ι V; σR] :=
  All (All (All (All (All (All (Imp (All (Iff (Mem x0 x5) (Or (Mem x0 x6) (Eqv x0 x6))))
    (Imp (Mem x1 x6) (Imp (OpF x1 x5 x3) (Imp (Mem x0 x6) (Imp (OpF x0 x4 x2) (app2 φ10 x3 x2))))))))))).

(** ∀w. Nat(w) → ∀X. (∀x ∈ X ∃y ∈ X. φ(x, y)) → ∀x₀. x₀ ∈ X → ∃f. … *)
Definition IZF_dc : form [σR] :=
  All (Imp (NatF x0) (All (Imp HypD (All (Imp (Mem x0 x1)
    (Ex (And TotD (And FunD (And SubD (And StartD StepD)))))))))).

Local Notation φ11 := (vs (vs (vs (vs (vs (vs (vs (vs (vs (vs (vs vz))))))))))).
Local Notation C5 := [ι V; ι V; ι V; ι V; σR].
Local Notation C6 := [ι V; ι V; ι V; ι V; ι V; σR].

(** ** Lemmes auxiliaires *)

Lemma suc_omega : IZFm [ι V] [Eps x0 Omega] (Eps (Suc x0) Omega).
Proof.
  qap iff_E2; [exact (axm A_omega _ (vV1 (Suc x0)))|].
  qap (or_I2 C Pr RIZFm). qap (qex_I C RIZFm V hV _ _ x0). qap (and_I C Pr RIZFm); [hyp|].
  qap (qeq_refl C RIZFm V hV).
Qed.

Definition SuccT : form [ι V; ι V] := All (Iff (Mem x0 x1) (Or (Mem x0 x2) (Eqv x0 x2))).

Lemma lizf_SuccT : lizf _ SuccT.
Proof. repeat constructor. Qed.

(** Succ(m, n) → n ≃ n′ → Succ(m, n′)   (contexte [m; n; n′]). *)
Lemma succ_congr : IZFm [ι V; ι V; ι V]
  [Eqv x1 x2; All (Iff (Mem x0 x1) (Or (Mem x0 x2) (Eqv x0 x2)))]
  (All (Iff (Mem x0 x1) (Or (Mem x0 x3) (Eqv x0 x3)))).
Proof.
  refine (ext_lizf SuccT lizf_SuccT _ _ (vV2 x0 x1) (vV2 x0 x2) _ _); [|hypc].
  unfold vV2. apply erel_cons; [apply eqv_refl_gen|]. apply erel_cons; [hyp|apply erel_refl].
Qed.

Definition vV4R {Γ} (a b c d : tm Γ V) (ψ : tm (ι V :: ι V :: Γ) Pr) : vec isym [ι V; ι V; ι V; ι V; σR] Γ :=
  @acons _ isym Γ (ι V) _ a (vVVVR b c d ψ).

(** Le pas du schéma ε   (contexte [n; y; y′; f; φ]). *)
Lemma step_use : IZFm [ι V; ι V; ι V; ι V; σR]
  [All (All (All (Imp (Eps (OPair x2 x1) x6) (Imp (Eps (OPair (Suc x2) x0) x6) (app2 φ7 x1 x0)))));
   Eps (OPair x0 x1) x3; Eps (OPair (Suc x0) x2) x3]
  (app2 φ4 x1 x2).
Proof.
  qap (imp_E C Pr RIZFm _ (Eps (OPair (Suc x0) x2) x3)); [|hyp].
  qap (imp_E C Pr RIZFm _ (Eps (OPair x0 x1) x3)); [|hyp].
  qap (qall_E C RIZFm V hV _ (Imp (Eps (OPair x1 x2) x4) (Imp (Eps (OPair (Suc x1) x0) x4) (app2 φ5 x2 x0))) x2).
  qap (qall_E C RIZFm V hV _ (All (Imp (Eps (OPair x2 x1) x5) (Imp (Eps (OPair (Suc x2) x0) x5) (app2 φ6 x1 x0)))) x1).
  qap (qall_E C RIZFm V hV _ (All (All (Imp (Eps (OPair x2 x1) x6) (Imp (Eps (OPair (Suc x2) x0) x6) (app2 φ7 x1 x0))))) x0).
  hyp.
Qed.

(** ** Les composantes (contexte [f; e₀; x₀; X; w; φ], e₀ ε X le représentant de x₀) *)

(** L'hypothèse de IZF donne celle du schéma ε   (contexte [e₀; x₀; X; w; φ]). *)
Lemma dchyp_l : IZFm C5
  [All (All (All (Imp (Eqv x1 x0) (Imp (app2 φ7 x2 x1) (app2 φ7 x2 x0)))));
   All (Imp (Mem x0 x3) (Ex (And (Mem x0 x4) (app2 φ6 x1 x0))))]
  (All (Imp (Eps x0 x3) (Ex (And (Eps x0 x4) (app2 φ6 x1 x0))))).
Proof.
  qap (qall_I C RIZFm V hV). qap (imp_I C Pr RIZFm).
  (* [x; e0; x0; X; w; φ] *)
  qap (qex_E C RIZFm V hV _ (And (Mem x0 x4) (app2 φ6 x1 x0))).
  { qap (imp_E C Pr RIZFm _ (Mem x0 x3)).
    - qap (qall_E C RIZFm V hV _ (Imp (Mem x0 x4) (Ex (And (Mem x0 x5) (app2 φ7 x1 x0)))) x0). hyp.
    - uses eps_mem (vV2 x0 x3). hyp. }
  (* [y; x; e0; x0; X; w; φ] *)
  qap (qex_E C RIZFm V hV _ (And (Eqv x1 x0) (Eps x0 x5))).
  { qap iff_E1; [exact (axm A_mem _ (vV2 x0 x4))|]. qap (and_E1 C Pr RIZFm _ _ (app2 φ6 x1 x0)). hyp. }
  (* [y'; y; x; e0; x0; X; w; φ] *)
  qap (qex_I C RIZFm V hV _ _ x0). qap (and_I C Pr RIZFm).
  - qap (and_E2 C Pr RIZFm _ (Eqv x1 x0)). hyp.
  - uses extR2_E (vVVVR x2 x1 x0 (eta σR (Γ := [ι V; ι V; ι V; ι V; ι V; ι V; ι V; σR]) φ7)); [hypc| |].
    + qap (and_E1 C Pr RIZFm _ _ (Eps x0 x5)). hyp.
    + qap (and_E2 C Pr RIZFm _ (Mem x1 x5)). hyp.
Qed.

Lemma dc_tot_l : IZFm C6
  [NatF x4; All (Imp (Eps x0 Omega) (Ex (And (Eps x0 x5) (Eps (OPair x1 x0) x2))))]
  (All (Imp (Mem x0 x5) (Ex (And (Mem x0 x5) (Ex (And (Mem x0 x3) (OpF x0 x2 x1))))))).
Proof.
  qap (qall_I C RIZFm V hV). qap (imp_I C Pr RIZFm).
  (* [n; f; e0; x0; X; w; φ] *)
  qap (qex_E C RIZFm V hV _ (And (Eqv x1 x0) (Eps x0 Omega))).
  { qap iff_E1; [exact (axm A_mem _ (vV2 x0 Omega))|]. uses nat_sub_omega (vV2 x0 x5); [hypc|hyp]. }
  (* [n'; n; f; ...] *)
  qap (qex_E C RIZFm V hV _ (And (Eps x0 x6) (Eps (OPair x1 x0) x3))).
  { qap (imp_E C Pr RIZFm _ (Eps x0 Omega)).
    - qap (qall_E C RIZFm V hV _ (Imp (Eps x0 Omega) (Ex (And (Eps x0 x7) (Eps (OPair x1 x0) x4)))) x0). hypc.
    - qap (and_E2 C Pr RIZFm _ (Eqv x1 x0)). hyp. }
  (* [y; n'; n; f; ...] *)
  qap (qex_I C RIZFm V hV _ _ x0). qap (and_I C Pr RIZFm).
  - uses eps_mem (vV2 x0 x6). qap (and_E1 C Pr RIZFm _ _ (Eps (OPair x1 x0) x3)). hyp.
  - refine (qex_I C RIZFm V hV _ _ (OPair x1 x0) _). qap (and_I C Pr RIZFm).
    + uses eps_mem (vV2 (OPair x1 x0) x3). qap (and_E2 C Pr RIZFm _ (Eps x0 x6)). hyp.
    + uses op_congr (vV6 (OPair x1 x0) x1 x0 (OPair x1 x0) x2 x0).
      * uses eqv_refl1 (vV1 (OPair x1 x0)).
      * uses eqv_sym (vV2 x2 x1). qap (and_E1 C Pr RIZFm _ _ (Eps x1 Omega)). hyp.
      * uses eqv_refl1 (vV1 x0).
      * uses op_base (vV2 x1 x0).
Qed.

Lemma dc_start_l : IZFm C6 [Eps (OPair Empty x1) x0; Eqv x2 x1]
  (All (Imp (All (Neg (Mem x0 x1))) (Ex (And (Mem x0 x2) (OpF x0 x1 x4))))).
Proof.
  qap (qall_I C RIZFm V hV). qap (imp_I C Pr RIZFm).
  (* [e; f; e0; x0; X; w; φ] *)
  refine (qex_I C RIZFm V hV _ _ (OPair Empty x2) _). qap (and_I C Pr RIZFm).
  - uses eps_mem (vV2 (OPair Empty x2) x1). hyp.
  - uses op_congr (vV6 (OPair Empty x2) Empty x2 (OPair Empty x2) x0 x3).
    + uses eqv_refl1 (vV1 (OPair Empty x2)).
    + uses eqv_sym (vV2 x0 Empty). uses empty_eqv (vV1 x0). hyp.
    + uses eqv_sym (vV2 x3 x2). hyp.
    + uses op_base (vV2 Empty x2).
Qed.

Local Notation C16 := [ι V; ι V; ι V; ι V; ι V; ι V; ι V; ι V; ι V; ι V; ι V; ι V; ι V; ι V; ι V; σR].

(** Le pas : deux représentants consécutifs n₀ et n₁ = S(n₀) (Leibniz). *)
Lemma dc_step_l : IZFm C6
  [All (All (All (Imp (Eqv x2 x1) (Imp (app2 φ8 x2 x0) (app2 φ8 x1 x0)))));
   All (All (All (Imp (Eqv x1 x0) (Imp (app2 φ8 x2 x1) (app2 φ8 x2 x0)))));
   All (All (All (Imp (Eps (OPair x2 x1) x3) (Imp (Eps (OPair (Suc x2) x0) x3) (app2 φ8 x1 x0)))));
   All (Imp (Eps x0 x1) (Ex (And (Eps x0 Omega) (Ex (And (Eps x0 x6) (EqV x2 (OPair x1 x0)))))))]
  (All (All (All (All (All (All (Imp (All (Iff (Mem x0 x5) (Or (Mem x0 x6) (Eqv x0 x6))))
    (Imp (Mem x1 x6) (Imp (OpF x1 x5 x3) (Imp (Mem x0 x6) (Imp (OpF x0 x4 x2) (app2 φ11 x3 x2)))))))))))).
Proof.
  do 6 qap (qall_I C RIZFm V hV). do 5 qap (imp_I C Pr RIZFm).
  (* [p'; p; y'; y; m; n; f; e0; x0; X; w; φ] *)
  qap (qex_E C RIZFm V hV _ (Ex (And (Eps x1 Omega) (And (Eps x0 x11) (And (Eps (OPair x1 x0) x8) (OpF x3 x1 x0)))))).
  { uses rep_l (vV3 x1 x6 x9); [hypc|hyp]. }
  qap (qex_E C RIZFm V hV _ (And (Eps x1 Omega) (And (Eps x0 x11) (And (Eps (OPair x1 x0) x8) (OpF x3 x1 x0))))); [hyp|].
  qap (qex_E C RIZFm V hV _ (Ex (And (Eps x1 Omega) (And (Eps x0 x13) (And (Eps (OPair x1 x0) x10) (OpF x4 x1 x0)))))).
  { uses rep_l (vV3 x2 x8 x11); [hypc|hyp]. }
  qap (qex_E C RIZFm V hV _ (And (Eps x1 Omega) (And (Eps x0 x13) (And (Eps (OPair x1 x0) x10) (OpF x4 x1 x0))))); [hyp|].
  (* [y1; n1; y0; n0; p'; p; y'; y; m; n; f; e0; x0; X; w; φ] *)
  assert (OA : forall Ξ, In (And (Eps x3 Omega) (And (Eps x2 x13) (And (Eps (OPair x3 x2) x10) (OpF x5 x3 x2))) : form C16) Ξ ->
                 IZFm _ Ξ (OpF x5 x3 x2)).
  { intros Ξ H. qap (and_E2 C Pr RIZFm _ (Eps (OPair x3 x2) x10)). qap (and_E2 C Pr RIZFm _ (Eps x2 x13)).
    qap (and_E2 C Pr RIZFm _ (Eps x3 Omega)). apply d_ax, H. }
  assert (OB : forall Ξ, In (And (Eps x1 Omega) (And (Eps x0 x13) (And (Eps (OPair x1 x0) x10) (OpF x4 x1 x0))) : form C16) Ξ ->
                 IZFm _ Ξ (OpF x4 x1 x0)).
  { intros Ξ H. qap (and_E2 C Pr RIZFm _ (Eps (OPair x1 x0) x10)). qap (and_E2 C Pr RIZFm _ (Eps x0 x13)).
    qap (and_E2 C Pr RIZFm _ (Eps x1 Omega)). apply d_ax, H. }
  uses extR2_E (vVVVR x7 x0 x6 (eta σR (Γ := C16) φ15)); [hypc| |].
  - uses eqv_sym (vV2 x6 x0). uses op_inj2 (vV5 x4 x8 x6 x1 x0); [hypc|apply OB; inc].
  - uses extR_E (vVVVR x2 x7 x0 (eta σR (Γ := C16) φ15)); [hypc| |].
    + uses eqv_sym (vV2 x7 x2). uses op_inj2 (vV5 x5 x9 x7 x3 x2); [hypc|apply OA; inc].
    + uses step_use (vV4R x3 x2 x0 x10 (eta σR (Γ := C16) φ15)); [hypc| |].
      * qap (and_E1 C Pr RIZFm _ _ (OpF x5 x3 x2)). qap (and_E2 C Pr RIZFm _ (Eps x2 x13)).
        qap (and_E2 C Pr RIZFm _ (Eps x3 Omega)). hypc.
      * refine (qeq_subst C RIZFm V hV _ (Eps (OPair x0 x1) x11) x1 (Suc x3) _ _).
        -- uses nat_leib (vV2 x1 (Suc x3)).
           ++ qap (and_E1 C Pr RIZFm _ _ (And (Eps x0 x13) (And (Eps (OPair x1 x0) x10) (OpF x4 x1 x0)))). hypc.
           ++ uses suc_omega (vV1 x3).
              qap (and_E1 C Pr RIZFm _ _ (And (Eps x2 x13) (And (Eps (OPair x3 x2) x10) (OpF x5 x3 x2)))). hypc.
           ++ uses eqv_trans (vV3 x1 x8 (Suc x3)).
              ** uses eqv_sym (vV2 x8 x1). uses op_inj1 (vV5 x4 x8 x6 x1 x0); [hypc|apply OB; inc].
              ** uses succ_suc (vV2 x8 x3). uses succ_congr (vV3 x8 x9 x3); [|hypc].
                 uses op_inj1 (vV5 x5 x9 x7 x3 x2); [hypc|apply OA; inc].
        -- qap (and_E1 C Pr RIZFm _ _ (OpF x4 x1 x0)). qap (and_E2 C Pr RIZFm _ (Eps x0 x13)).
           qap (and_E2 C Pr RIZFm _ (Eps x1 Omega)). hypc.
Qed.
