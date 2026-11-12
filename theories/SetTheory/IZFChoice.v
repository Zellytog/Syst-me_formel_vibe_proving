(** * CC et DC dans IZF, déduits de leurs formes ε

    Les schémas de choix de [IZFeCC.v] et [IZFeDC.v] parlent de ε, de
    l'égalité de Leibniz et des termes ω et ⟨·,·⟩. On en déduit, dans
    IZFε + CC (resp. + DC), le choix dénombrable (resp. dépendant) **de
    IZF**, énoncé dans L_IZF : ω et les couples y sont définis par des
    formules (« w est le plus petit ensemble inductif », « p est le couple
    de Kuratowski de a et b »), l'égalité est ≃ et l'appartenance ∈.

    Le point délicat est la fonctionnalité : un entier n de IZF a plusieurs
    représentants n′ ε ω, et le schéma ε ne donne l'unicité que pour un
    même représentant (au sens de Leibniz). On prouve donc que **sur ω, ≃
    entraîne l'égalité de Leibniz** ([nat_leib], par ε-induction, avec
    l'absence de 2-cycle pour ∈). *)

From Stdlib Require Import List.
Import ListNotations.
From SF.Syntax Require Import Spec Terms Renaming Vectors.
From SF.Calculus Require Import System Rules.
From SF.Logic Require Import Judgment Propositional.
From SF.Functional Require Import Arrow.
From SF.Quantifiers Require Import Quant Order.
From SF.Extensions Require Import RuleExt.
From SF.SetTheory Require Import IZFe IZFeBasic IZFeExt IZFeIZF IZFeCC IZFeDC.

Local Notation ι a := (Spec [] a).
Tactic Notation "qap" uconstr(t) := eapply t; try typeclasses eauto.
Ltac hyp := apply d_ax; simpl; auto 20.

(** ** Paires et extensionnalité *)

(** z ∈ {a, b} ↔ z ≃ a ∨ z ≃ b   (contexte [z; a; b]). *)
Lemma pair_mem : IZFm [ι V; ι V; ι V] [] (Iff (Mem x0 (Pair x1 x2)) (Or (Eqv x0 x1) (Eqv x0 x2))).
Proof.
  qap (and_I C Pr RIZFm); qap (imp_I C Pr RIZFm).
  - qap (qex_E C RIZFm V hV _ (And (Eqv x1 x0) (Eps x0 (Pair x2 x3)))).
    { qap iff_E1; [exact (axm A_mem _ (vV2 x0 (Pair x1 x2)))|hyp]. }
    qap (or_E C Pr RIZFm _ (EqV x0 x2) (EqV x0 x3)).
    + qap iff_E1; [exact (axm A_pair _ (vV3 x0 x2 x3))|].
      qap (and_E2 C Pr RIZFm _ (Eqv x1 x0)). hyp.
    + qap (or_I1 C Pr RIZFm). uses eqv_trans (vV3 x1 x0 x2).
      * qap (and_E1 C Pr RIZFm _ _ (Eps x0 (Pair x2 x3))). hyp.
      * uses eqV_eqv (vV2 x0 x2). hyp.
    + qap (or_I2 C Pr RIZFm). uses eqv_trans (vV3 x1 x0 x3).
      * qap (and_E1 C Pr RIZFm _ _ (Eps x0 (Pair x2 x3))). hyp.
      * uses eqV_eqv (vV2 x0 x3). hyp.
  - qap (or_E C Pr RIZFm _ (Eqv x0 x1) (Eqv x0 x2)); [hyp| |].
    + uses mem_I (vV3 x0 x1 (Pair x1 x2)); [hyp|].
      qap iff_E2; [exact (axm A_pair _ (vV3 x1 x1 x2))|].
      qap (or_I1 C Pr RIZFm). qap (qeq_refl C RIZFm V hV).
    + uses mem_I (vV3 x0 x2 (Pair x1 x2)); [hyp|].
      qap iff_E2; [exact (axm A_pair _ (vV3 x2 x1 x2))|].
      qap (or_I2 C Pr RIZFm). qap (qeq_refl C RIZFm V hV).
Qed.

(** Extensionnalité : (∀u. u ∈ x ↔ u ∈ y) → x ≃ y   (contexte [x; y]). *)
Lemma ext_mem : IZFm [ι V; ι V] [All (Iff (Mem x0 x1) (Mem x0 x2))] (Eqv x0 x1).
Proof.
  qap iff_E2; [exact (axm A_eqv _ (vV2 x0 x1))|]. qap (and_I C Pr RIZFm).
  - uses sub_of_mem (vV2 x0 x1).
    qap (qall_I C RIZFm V hV). qap (imp_I C Pr RIZFm).
    qap (iff_E1 _ (Mem x0 x1)); [|hyp]. qap (qall_E C RIZFm V hV _ (Iff (Mem x0 x2) (Mem x0 x3)) x0). hyp.
  - uses sub_of_mem (vV2 x1 x0).
    qap (qall_I C RIZFm V hV). qap (imp_I C Pr RIZFm).
    qap (iff_E2 _ _ (Mem x0 x2)); [|hyp]. qap (qall_E C RIZFm V hV _ (Iff (Mem x0 x2) (Mem x0 x3)) x0). hyp.
Qed.

Ltac hypc := apply d_ax; repeat (first [left; reflexivity | right]).

(** ** Singletons et paires définis par des formules *)

(** Sg(z, a) := ∀u. u ∈ z ↔ u ≃ a   (contexte [z; a]). *)
(** Pr(z, a, b) := ∀u. u ∈ z ↔ u ≃ a ∨ u ≃ b   (contexte [z; a; b]). *)

(** z ∈ {a, a} → z ≃ a   (contexte [z; a]). *)
Lemma sing_mem : IZFm [ι V; ι V] [Mem x0 (Sing x1)] (Eqv x0 x1).
Proof.
  qap (or_E C Pr RIZFm _ (Eqv x0 x1) (Eqv x0 x1)); [|hyp|hyp].
  qap (iff_E1 _ (Mem x0 (Sing x1))); [uses pair_mem (vV3 x0 x1 x1)|hyp].
Qed.

(** z ≃ a → z ∈ {a, a}   (contexte [z; a]). *)
Lemma sing_mem_I : IZFm [ι V; ι V] [Eqv x0 x1] (Mem x0 (Sing x1)).
Proof.
  qap (iff_E2 _ _ (Or (Eqv x0 x1) (Eqv x0 x1))); [uses pair_mem (vV3 x0 x1 x1)|].
  qap (or_I1 C Pr RIZFm). hyp.
Qed.

Lemma pair_mem_l : IZFm [ι V; ι V] [] (Mem x0 (Pair x0 x1)).
Proof.
  qap (iff_E2 _ _ (Or (Eqv x0 x0) (Eqv x0 x1))); [uses pair_mem (vV3 x0 x0 x1)|].
  qap (or_I1 C Pr RIZFm). uses eqv_refl1 (vV1 x0).
Qed.

Lemma pair_mem_r : IZFm [ι V; ι V] [] (Mem x1 (Pair x0 x1)).
Proof.
  qap (iff_E2 _ _ (Or (Eqv x1 x0) (Eqv x1 x1))); [uses pair_mem (vV3 x1 x0 x1)|].
  qap (or_I2 C Pr RIZFm). uses eqv_refl1 (vV1 x1).
Qed.

(** Sg(z, a) ↔ z ≃ {a, a}, Pr(z, a, b) ↔ z ≃ {a, b}. *)
Lemma sg_of_eqv : IZFm [ι V; ι V] [Eqv x0 (Sing x1)] (All (Iff (Mem x0 x1) (Eqv x0 x2))).
Proof.
  qap (qall_I C RIZFm V hV). qap (and_I C Pr RIZFm); qap (imp_I C Pr RIZFm).
  - uses sing_mem (vV2 x0 x2). uses mem_congr_r (vV3 x0 x1 (Sing x2)); hyp.
  - uses mem_congr_r (vV3 x0 (Sing x2) x1).
    + uses eqv_sym (vV2 x1 (Sing x2)). hyp.
    + uses sing_mem_I (vV2 x0 x2). hyp.
Qed.

Lemma eqv_of_sg : IZFm [ι V; ι V] [All (Iff (Mem x0 x1) (Eqv x0 x2))] (Eqv x0 (Sing x1)).
Proof.
  uses ext_mem (vV2 x0 (Sing x1)).
  qap (qall_I C RIZFm V hV). qap (and_I C Pr RIZFm); qap (imp_I C Pr RIZFm).
  - uses sing_mem_I (vV2 x0 x2).
    qap (iff_E1 _ (Mem x0 x1)); [|hyp]. qap (qall_E C RIZFm V hV _ (Iff (Mem x0 x2) (Eqv x0 x3)) x0). hyp.
  - qap (iff_E2 _ (Mem x0 x1)); [qap (qall_E C RIZFm V hV _ (Iff (Mem x0 x2) (Eqv x0 x3)) x0); hyp|].
    uses sing_mem (vV2 x0 x2). hyp.
Qed.

Lemma pr_of_eqv : IZFm [ι V; ι V; ι V] [Eqv x0 (Pair x1 x2)] (All (Iff (Mem x0 x1) (Or (Eqv x0 x2) (Eqv x0 x3)))).
Proof.
  qap (qall_I C RIZFm V hV). qap (and_I C Pr RIZFm); qap (imp_I C Pr RIZFm).
  - qap (iff_E1 _ (Mem x0 (Pair x2 x3))); [uses pair_mem (vV3 x0 x2 x3)|].
    uses mem_congr_r (vV3 x0 x1 (Pair x2 x3)); hyp.
  - uses mem_congr_r (vV3 x0 (Pair x2 x3) x1).
    + uses eqv_sym (vV2 x1 (Pair x2 x3)). hyp.
    + qap (iff_E2 _ _ (Or (Eqv x0 x2) (Eqv x0 x3))); [uses pair_mem (vV3 x0 x2 x3)|hyp].
Qed.

Lemma eqv_of_pr : IZFm [ι V; ι V; ι V] [All (Iff (Mem x0 x1) (Or (Eqv x0 x2) (Eqv x0 x3)))] (Eqv x0 (Pair x1 x2)).
Proof.
  uses ext_mem (vV2 x0 (Pair x1 x2)).
  qap (qall_I C RIZFm V hV). qap (and_I C Pr RIZFm); qap (imp_I C Pr RIZFm).
  - qap (iff_E2 _ _ (Or (Eqv x0 x2) (Eqv x0 x3))); [uses pair_mem (vV3 x0 x2 x3)|].
    qap (iff_E1 _ (Mem x0 x1)); [|hyp].
    qap (qall_E C RIZFm V hV _ (Iff (Mem x0 x2) (Or (Eqv x0 x3) (Eqv x0 x4))) x0). hyp.
  - qap (iff_E2 _ (Mem x0 x1)); [qap (qall_E C RIZFm V hV _ (Iff (Mem x0 x2) (Or (Eqv x0 x3) (Eqv x0 x4))) x0); hyp|].
    qap (iff_E1 _ (Mem x0 (Pair x2 x3))); [uses pair_mem (vV3 x0 x2 x3)|hyp].
Qed.

(** ** Le couple de Kuratowski défini par une formule

    Op(p, a, b) := ∀z. z ∈ p ↔ Sg(z, a) ∨ Pr(z, a, b)   (contexte [p; a; b]). *)

Definition OpT : form [ι V; ι V; ι V] :=
  All (Iff (Mem x0 x1) (Or (All (Iff (Mem x0 x1) (Eqv x0 x3)))
                           (All (Iff (Mem x0 x1) (Or (Eqv x0 x3) (Eqv x0 x4)))))).

Definition OpF {Γ} (p a b : tm Γ V) : form Γ := vsubst OpT (vV3 p a b).

Lemma lizf_OpT : lizf _ OpT.
Proof. repeat constructor. Qed.

Definition vV5 {Γ} (a b c d e : tm Γ V) : vec isym [ι V; ι V; ι V; ι V; ι V] Γ :=
  @acons _ isym Γ (ι V) _ a (vV4 b c d e).
Definition vV6 {Γ} (a b c d e f : tm Γ V) : vec isym [ι V; ι V; ι V; ι V; ι V; ι V] Γ :=
  @acons _ isym Γ (ι V) _ a (vV5 b c d e f).

(** Congruence pour ≃ (lemme 1.5.8)   (contexte [p; a; b; p′; a′; b′]). *)
Lemma op_congr : IZFm [ι V; ι V; ι V; ι V; ι V; ι V]
  [Eqv x0 x3; Eqv x1 x4; Eqv x2 x5; OpF x0 x1 x2] (OpF x3 x4 x5).
Proof.
  apply (ext_lizf OpT lizf_OpT _ _ (vV3 x0 x1 x2) (vV3 x3 x4 x5)); [|hypc].
  unfold vV3. repeat (apply erel_cons; [hyp|]). apply erel_refl.
Qed.

(** Élimination et introduction   (contexte [z; p; a; b]). *)
Lemma op_E : IZFm [ι V; ι V; ι V; ι V] [OpF x1 x2 x3; Mem x0 x1]
  (Or (All (Iff (Mem x0 x1) (Eqv x0 x3))) (All (Iff (Mem x0 x1) (Or (Eqv x0 x3) (Eqv x0 x4))))).
Proof.
  qap (iff_E1 _ (Mem x0 x1)); [|hyp].
  qap (qall_E C RIZFm V hV _ (Iff (Mem x0 x2) (Or (All (Iff (Mem x0 x1) (Eqv x0 x4)))
                                                  (All (Iff (Mem x0 x1) (Or (Eqv x0 x4) (Eqv x0 x5)))))) x0).
  hypc.
Qed.

Lemma op_I : IZFm [ι V; ι V; ι V; ι V]
  [OpF x1 x2 x3; Or (All (Iff (Mem x0 x1) (Eqv x0 x3))) (All (Iff (Mem x0 x1) (Or (Eqv x0 x3) (Eqv x0 x4))))]
  (Mem x0 x1).
Proof.
  qap (iff_E2 _ _ (Or (All (Iff (Mem x0 x1) (Eqv x0 x3))) (All (Iff (Mem x0 x1) (Or (Eqv x0 x3) (Eqv x0 x4)))))); [|hyp].
  qap (qall_E C RIZFm V hV _ (Iff (Mem x0 x2) (Or (All (Iff (Mem x0 x1) (Eqv x0 x4)))
                                                  (All (Iff (Mem x0 x1) (Or (Eqv x0 x4) (Eqv x0 x5)))))) x0).
  hypc.
Qed.

(** Le couple ⟨a, b⟩ := {{a, a}, {a, b}} est un couple   (contexte [a; b]). *)
Lemma op_base : IZFm [ι V; ι V] [] (OpF (OPair x0 x1) x0 x1).
Proof.
  change (IZFm [ι V; ι V] [] (All (Iff (Mem x0 (OPair x1 x2))
            (Or (All (Iff (Mem x0 x1) (Eqv x0 x2))) (All (Iff (Mem x0 x1) (Or (Eqv x0 x2) (Eqv x0 x3)))))))).
  qap (qall_I C RIZFm V hV). qap (and_I C Pr RIZFm); qap (imp_I C Pr RIZFm).
  - qap (or_E C Pr RIZFm _ (Eqv x0 (Sing x1)) (Eqv x0 (Pair x1 x2))).
    + qap (iff_E1 _ (Mem x0 (Pair (Sing x1) (Pair x1 x2)))); [uses pair_mem (vV3 x0 (Sing x1) (Pair x1 x2))|hyp].
    + qap (or_I1 C Pr RIZFm). uses sg_of_eqv (vV2 x0 x1). hyp.
    + qap (or_I2 C Pr RIZFm). uses pr_of_eqv (vV3 x0 x1 x2). hyp.
  - qap (iff_E2 _ _ (Or (Eqv x0 (Sing x1)) (Eqv x0 (Pair x1 x2)))); [uses pair_mem (vV3 x0 (Sing x1) (Pair x1 x2))|].
    qap (or_E C Pr RIZFm _ (All (Iff (Mem x0 x1) (Eqv x0 x2))) (All (Iff (Mem x0 x1) (Or (Eqv x0 x2) (Eqv x0 x3))))); [hyp| |].
    + qap (or_I1 C Pr RIZFm). uses eqv_of_sg (vV2 x0 x1). hyp.
    + qap (or_I2 C Pr RIZFm). uses eqv_of_pr (vV3 x0 x1 x2). hyp.
Qed.

(** Un élément d'un Sg ou d'un Pr   (contextes [u; z; a; b] et [z; a; b]). *)
Lemma sgpr_mem : IZFm [ι V; ι V; ι V; ι V]
  [Or (All (Iff (Mem x0 x2) (Eqv x0 x3))) (All (Iff (Mem x0 x2) (Or (Eqv x0 x3) (Eqv x0 x4)))); Mem x0 x1]
  (Or (Eqv x0 x2) (Eqv x0 x3)).
Proof.
  qap (or_E C Pr RIZFm _ (All (Iff (Mem x0 x2) (Eqv x0 x3))) (All (Iff (Mem x0 x2) (Or (Eqv x0 x3) (Eqv x0 x4))))); [hyp| |].
  - qap (or_I1 C Pr RIZFm). qap (iff_E1 _ (Mem x0 x1)); [|hyp].
    qap (qall_E C RIZFm V hV _ (Iff (Mem x0 x2) (Eqv x0 x3)) x0). hyp.
  - qap (iff_E1 _ (Mem x0 x1)); [|hyp].
    qap (qall_E C RIZFm V hV _ (Iff (Mem x0 x2) (Or (Eqv x0 x3) (Eqv x0 x4))) x0). hyp.
Qed.

Lemma sgpr_self : IZFm [ι V; ι V; ι V]
  [Or (All (Iff (Mem x0 x1) (Eqv x0 x2))) (All (Iff (Mem x0 x1) (Or (Eqv x0 x2) (Eqv x0 x3))))]
  (Mem x1 x0).
Proof.
  qap (or_E C Pr RIZFm _ (All (Iff (Mem x0 x1) (Eqv x0 x2))) (All (Iff (Mem x0 x1) (Or (Eqv x0 x2) (Eqv x0 x3))))); [hyp| |].
  - qap (iff_E2 _ _ (Eqv x1 x1)); [qap (qall_E C RIZFm V hV _ (Iff (Mem x0 x1) (Eqv x0 x2)) x1); hyp|].
    uses eqv_refl1 (vV1 x1).
  - qap (iff_E2 _ _ (Or (Eqv x1 x1) (Eqv x1 x2))); [qap (qall_E C RIZFm V hV _ (Iff (Mem x0 x1) (Or (Eqv x0 x2) (Eqv x0 x3))) x1); hyp|].
    qap (or_I1 C Pr RIZFm). uses eqv_refl1 (vV1 x1).
Qed.

(** Injectivité du couple (intuitionniste)   (contexte [p; a; b; a′; b′]). *)
Lemma op_inj1 : IZFm [ι V; ι V; ι V; ι V; ι V] [OpF x0 x1 x2; OpF x0 x3 x4] (Eqv x1 x3).
Proof.
  uses eqv_sym (vV2 x3 x1). uses sing_mem (vV2 x3 x1).
  uses sgpr_self (vV3 (Sing x1) x3 x4).
  uses op_E (vV4 (Sing x1) x0 x3 x4); [hypc|].
  uses op_I (vV4 (Sing x1) x0 x1 x2); [hypc|].
  qap (or_I1 C Pr RIZFm). uses sg_of_eqv (vV2 (Sing x1) x1). uses eqv_refl1 (vV1 (Sing x1)).
Qed.

Lemma op_inj2 : IZFm [ι V; ι V; ι V; ι V; ι V] [OpF x0 x1 x2; OpF x0 x3 x4] (Eqv x2 x4).
Proof.
  qap (or_E C Pr RIZFm _ (Eqv x2 x3) (Eqv x2 x4)); [| |hyp].
  - uses sgpr_mem (vV4 x2 (Pair x1 x2) x3 x4).
    + uses op_E (vV4 (Pair x1 x2) x0 x3 x4); [hypc|].
      uses op_I (vV4 (Pair x1 x2) x0 x1 x2); [hypc|].
      qap (or_I2 C Pr RIZFm). uses pr_of_eqv (vV3 (Pair x1 x2) x1 x2). uses eqv_refl1 (vV1 (Pair x1 x2)).
    + uses pair_mem_r (vV2 x1 x2).
  - qap (or_E C Pr RIZFm _ (Eqv x4 x1) (Eqv x4 x2)).
    + uses sgpr_mem (vV4 x4 (Pair x3 x4) x1 x2).
      * uses op_E (vV4 (Pair x3 x4) x0 x1 x2); [hypc|].
        uses op_I (vV4 (Pair x3 x4) x0 x3 x4); [hypc|].
        qap (or_I2 C Pr RIZFm). uses pr_of_eqv (vV3 (Pair x3 x4) x3 x4). uses eqv_refl1 (vV1 (Pair x3 x4)).
      * uses pair_mem_r (vV2 x3 x4).
    + uses eqv_trans (vV3 x2 x3 x4); [hyp|].
      uses eqv_trans (vV3 x3 x1 x4).
      * uses eqv_sym (vV2 x1 x3). uses op_inj1 (vV5 x0 x1 x2 x3 x4); hypc.
      * uses eqv_sym (vV2 x4 x1). hyp.
    + uses eqv_sym (vV2 x4 x2). hyp.
Qed.

(** ** Le successeur *)

(** n ε S(n)   (contexte [n]). *)
Lemma eps_suc : IZFm [ι V] [] (Eps x0 (Suc x0)).
Proof.
  qap iff_E2; [exact (axm A_union _ (vV2 x0 (Pair x0 (Sing x0))))|].
  qap (qex_I C RIZFm V hV _ _ (Sing x0)). qap (and_I C Pr RIZFm).
  - qap iff_E2; [exact (axm A_pair _ (vV3 x0 x0 x0))|].
    qap (or_I1 C Pr RIZFm). qap (qeq_refl C RIZFm V hV).
  - qap iff_E2; [exact (axm A_pair _ (vV3 (Sing x0) x0 (Sing x0)))|].
    qap (or_I2 C Pr RIZFm). qap (qeq_refl C RIZFm V hV).
Qed.

(** z ∈ S(n) ↔ z ∈ n ∨ z ≃ n   (contexte [z; n]). *)
Lemma suc_mem : IZFm [ι V; ι V] [] (Iff (Mem x0 (Suc x1)) (Or (Mem x0 x1) (Eqv x0 x1))).
Proof.
  qap (and_I C Pr RIZFm); qap (imp_I C Pr RIZFm).
  - qap (qex_E C RIZFm V hV _ (And (Eqv x1 x0) (Eps x0 (Suc x2)))).
    { qap iff_E1; [exact (axm A_mem _ (vV2 x0 (Suc x1)))|hyp]. }
    (* [z'; z; n] *)
    qap (qex_E C RIZFm V hV _ (And (Eps x1 x0) (Eps x0 (Pair x3 (Sing x3))))).
    { qap iff_E1; [exact (axm A_union _ (vV2 x0 (Pair x2 (Sing x2))))|].
      qap (and_E2 C Pr RIZFm _ (Eqv x1 x0)). hyp. }
    (* [b; z'; z; n] *)
    qap (or_E C Pr RIZFm _ (EqV x0 x3) (EqV x0 (Sing x3))).
    { qap iff_E1; [exact (axm A_pair _ (vV3 x0 x3 (Sing x3)))|].
      qap (and_E2 C Pr RIZFm _ (Eps x1 x0)). hyp. }
    + qap (or_I1 C Pr RIZFm). uses mem_congr_l (vV3 x1 x2 x3).
      * uses eqv_sym (vV2 x2 x1). qap (and_E1 C Pr RIZFm _ _ (Eps x1 (Suc x3))). hyp.
      * uses eps_mem (vV2 x1 x3).
        qap (qeq_subst C RIZFm V hV _ (Eps x2 x0) x0 x3); [hyp|].
        qap (and_E1 C Pr RIZFm _ _ (Eps x0 (Pair x3 (Sing x3)))). hyp.
    + qap (or_I2 C Pr RIZFm). uses eqv_trans (vV3 x2 x1 x3).
      * qap (and_E1 C Pr RIZFm _ _ (Eps x1 (Suc x3))). hyp.
      * qap (or_E C Pr RIZFm _ (EqV x1 x3) (EqV x1 x3)).
        -- qap iff_E1; [exact (axm A_pair _ (vV3 x1 x3 x3))|].
           qap (qeq_subst C RIZFm V hV _ (Eps x2 x0) x0 (Sing x3)); [hyp|].
           qap (and_E1 C Pr RIZFm _ _ (Eps x0 (Pair x3 (Sing x3)))). hyp.
        -- uses eqV_eqv (vV2 x1 x3). hyp.
        -- uses eqV_eqv (vV2 x1 x3). hyp.
  - qap (or_E C Pr RIZFm _ (Mem x0 x1) (Eqv x0 x1)); [hyp| |].
    + qap (qex_E C RIZFm V hV _ (And (Eqv x1 x0) (Eps x0 x2))).
      { qap iff_E1; [exact (axm A_mem _ (vV2 x0 x1))|hyp]. }
      uses mem_I (vV3 x1 x0 (Suc x2)); [qap (and_E1 C Pr RIZFm _ _ (Eps x0 x2)); hyp|].
      qap iff_E2; [exact (axm A_union _ (vV2 x0 (Pair x2 (Sing x2))))|].
      qap (qex_I C RIZFm V hV _ _ x2). qap (and_I C Pr RIZFm).
      * qap (and_E2 C Pr RIZFm _ (Eqv x1 x0)). hyp.
      * qap iff_E2; [exact (axm A_pair _ (vV3 x2 x2 (Sing x2)))|].
        qap (or_I1 C Pr RIZFm). qap (qeq_refl C RIZFm V hV).
    + uses mem_I (vV3 x0 x1 (Suc x1)); [hyp|]. uses eps_suc (vV1 x1).
Qed.

(** ∅ n'a pas d'élément   (contexte [z]). *)
Lemma mem_empty : IZFm [ι V] [Mem x0 Empty] Bot.
Proof.
  qap (qex_E C RIZFm V hV _ (And (Eqv x1 x0) (Eps x0 Empty))).
  { qap iff_E1; [exact (axm A_mem _ (vV2 x0 Empty))|hyp]. }
  qap (imp_E C Pr RIZFm _ (Eps x0 Empty)); [exact (axm A_empty _ (vV1 x0))|].
  qap (and_E2 C Pr RIZFm _ (Eqv x1 x0)). hyp.
Qed.

(** Pas de 2-cycle pour ∈ (par ε-induction)   (contexte [a; b]). *)
Lemma nocycle : IZFm [ι V; ι V] [Mem x0 x1; Mem x1 x0] Bot.
Proof.
  qap (imp_E C Pr RIZFm _ (Mem x1 x0)); [|hyp].
  qap (imp_E C Pr RIZFm _ (Mem x0 x1)); [|hyp].
  qap (qall_E C RIZFm V hV _ (Imp (Mem x1 x0) (Imp (Mem x0 x1) Bot)) x1).
  qap (qall_E C RIZFm V hV _ (All (Imp (Mem x1 x0) (Imp (Mem x0 x1) Bot))) x0).
  qap (imp_E C Pr RIZFm); [exact (axm A_ind _ (vP1 (All (Imp (Mem x1 x0) (Imp (Mem x0 x1) Bot)))))|].
  qap (qall_I C RIZFm V hV). qap (imp_I C Pr RIZFm).
  (* [c; a; b] *)
  qap (qall_I C RIZFm V hV). qap (imp_I C Pr RIZFm). qap (imp_I C Pr RIZFm).
  (* [d; c; a; b] : c ∈ d, d ∈ c *)
  qap (qex_E C RIZFm V hV _ (And (Eqv x1 x0) (Eps x0 x2))).
  { qap iff_E1; [exact (axm A_mem _ (vV2 x0 x1))|hyp]. }
  (* [d'; d; c; a; b] *)
  qap (imp_E C Pr RIZFm _ (Mem x2 x0)).
  - qap (imp_E C Pr RIZFm _ (Mem x0 x2)).
    + qap (qall_E C RIZFm V hV _ (Imp (Mem x1 x0) (Imp (Mem x0 x1) Bot)) x2).
      qap (imp_E C Pr RIZFm _ (Eps x0 x2)).
      * qap (qall_E C RIZFm V hV _ (Imp (Eps x0 x3) (All (Imp (Mem x1 x0) (Imp (Mem x0 x1) Bot)))) x0). hyp.
      * qap (and_E2 C Pr RIZFm _ (Eqv x1 x0)). hyp.
    + uses eps_mem (vV2 x0 x2). qap (and_E2 C Pr RIZFm _ (Eqv x1 x0)). hyp.
  - uses mem_congr_r (vV3 x2 x1 x0); [qap (and_E1 C Pr RIZFm _ _ (Eps x0 x2)); hyp|hyp].
Qed.

(** S(y) ≃ S(y′) → y ≃ y′   (contexte [y; y′]). *)
Lemma suc_eqv_inj : IZFm [ι V; ι V] [Eqv (Suc x0) (Suc x1)] (Eqv x0 x1).
Proof.
  qap (or_E C Pr RIZFm _ (Mem x0 x1) (Eqv x0 x1)); [| |hyp].
  - qap (iff_E1 _ (Mem x0 (Suc x1))); [uses suc_mem (vV2 x0 x1)|].
    uses mem_congr_r (vV3 x0 (Suc x0) (Suc x1)); [hyp|].
    uses eps_mem (vV2 x0 (Suc x0)). uses eps_suc (vV1 x0).
  - qap (or_E C Pr RIZFm _ (Mem x1 x0) (Eqv x1 x0)).
    + qap (iff_E1 _ (Mem x1 (Suc x0))); [uses suc_mem (vV2 x1 x0)|].
      uses mem_congr_r (vV3 x1 (Suc x1) (Suc x0)); [uses eqv_sym (vV2 (Suc x0) (Suc x1)); hyp|].
      uses eps_mem (vV2 x1 (Suc x1)). uses eps_suc (vV1 x1).
    + qap (bot_E C Pr RIZFm). uses nocycle (vV2 x0 x1); hyp.
    + uses eqv_sym (vV2 x1 x0). hyp.
Qed.

(** ∅ ≃ S(y) est absurde   (contexte [c; y]). *)
Lemma empty_suc : IZFm [ι V; ι V] [EqV x0 Empty; Eqv x0 (Suc x1)] Bot.
Proof.
  uses mem_empty (vV1 x1).
  qap (qeq_subst C RIZFm V hV _ (Mem x2 x0) x0 Empty); [hyp|].
  uses mem_congr_r (vV3 x1 (Suc x1) x0); [uses eqv_sym (vV2 x0 (Suc x1)); hyp|].
  uses eps_mem (vV2 x1 (Suc x1)). uses eps_suc (vV1 x1).
Qed.

(** ** Sur ω, ≃ entraîne l'égalité de Leibniz

    Par ε-induction sur n, avec Φ(c) := c ε ω → ∀d. d ε ω → c ≃ d → c = d. *)

Definition NL {Γ} : form (ι V :: Γ) :=
  Imp (Eps x0 Omega) (All (Imp (Eps x0 Omega) (Imp (Eqv x1 x0) (EqV x1 x0)))).

Lemma nat_leib : IZFm [ι V; ι V] [Eps x0 Omega; Eps x1 Omega; Eqv x0 x1] (EqV x0 x1).
Proof.
  qap (imp_E C Pr RIZFm _ (Eqv x0 x1)); [|hyp]. qap (imp_E C Pr RIZFm _ (Eps x1 Omega)); [|hyp].
  qap (qall_E C RIZFm V hV _ (Imp (Eps x0 Omega) (Imp (Eqv x1 x0) (EqV x1 x0))) x1).
  qap (imp_E C Pr RIZFm _ (Eps x0 Omega)); [|hyp].
  qap (qall_E C RIZFm V hV _ NL x0).
  qap (imp_E C Pr RIZFm); [exact (axm A_ind _ (vP1 NL))|].
  qap (qall_I C RIZFm V hV). qap (imp_I C Pr RIZFm). unfold NL.
  qap (imp_I C Pr RIZFm). qap (qall_I C RIZFm V hV). qap (imp_I C Pr RIZFm). qap (imp_I C Pr RIZFm).
  (* [d; c; n; m] : c ε ω, d ε ω, c ≃ d *)
  qap (or_E C Pr RIZFm _ (EqV x1 Empty) (Ex (And (Eps x0 Omega) (EqV x2 (Suc x0))))).
  { qap iff_E1; [exact (axm A_omega _ (vV1 x1))|hyp]. }
  - (* c = ∅ *)
    qap (or_E C Pr RIZFm _ (EqV x0 Empty) (Ex (And (Eps x0 Omega) (EqV x1 (Suc x0))))).
    { qap iff_E1; [exact (axm A_omega _ (vV1 x0))|hyp]. }
    + qap (qeq_trans C RIZFm V hV _ x1 Empty x0); [hyp|]. qap (qeq_sym C RIZFm V hV). hyp.
    + qap (qex_E C RIZFm V hV _ (And (Eps x0 Omega) (EqV x1 (Suc x0)))); [hyp|].
      (* [y; d; c; n; m] *)
      qap (bot_E C Pr RIZFm). uses empty_suc (vV2 x2 x0); [hyp|].
      qap (qeq_subst C RIZFm V hV _ (Eqv x3 x0) x1 (Suc x0)); [|hyp].
      qap (and_E2 C Pr RIZFm _ (Eps x0 Omega)). hyp.
  - (* c = S y *)
    qap (qex_E C RIZFm V hV _ (And (Eps x0 Omega) (EqV x2 (Suc x0)))); [hyp|].
    (* [y; d; c; n; m] *)
    qap (or_E C Pr RIZFm _ (EqV x1 Empty) (Ex (And (Eps x0 Omega) (EqV x2 (Suc x0))))).
    { qap iff_E1; [exact (axm A_omega _ (vV1 x1))|hyp]. }
    + qap (bot_E C Pr RIZFm). uses empty_suc (vV2 x1 x0); [hyp|].
      qap (qeq_subst C RIZFm V hV _ (Eqv x2 x0) x2 (Suc x0)).
      * qap (and_E2 C Pr RIZFm _ (Eps x0 Omega)). hyp.
      * uses eqv_sym (vV2 x2 x1). hyp.
    + qap (qex_E C RIZFm V hV _ (And (Eps x0 Omega) (EqV x2 (Suc x0)))); [hyp|].
      (* [y'; y; d; c; n; m] : d = S y', c = S y *)
      qap (qeq_trans C RIZFm V hV _ x3 (Suc x1) x2); [qap (and_E2 C Pr RIZFm _ (Eps x1 Omega)); hyp|].
      qap (qeq_trans C RIZFm V hV _ (Suc x1) (Suc x0) x2);
        [|qap (qeq_sym C RIZFm V hV); qap (and_E2 C Pr RIZFm _ (Eps x0 Omega)); hyp].
      qap (qeq_subst C RIZFm V hV _ (EqV (Suc x2) (Suc x0)) x1 x0); [|qap (qeq_refl C RIZFm V hV)].
      (* y = y′, par l'hypothèse d'induction en y *)
      qap (imp_E C Pr RIZFm _ (Eqv x1 x0)).
      * qap (imp_E C Pr RIZFm _ (Eps x0 Omega)); [|qap (and_E1 C Pr RIZFm _ _ (EqV x2 (Suc x0))); hyp].
        qap (qall_E C RIZFm V hV _ (Imp (Eps x0 Omega) (Imp (Eqv x2 x0) (EqV x2 x0))) x0).
        qap (imp_E C Pr RIZFm _ (Eps x1 Omega)); [|qap (and_E1 C Pr RIZFm _ _ (EqV x3 (Suc x1))); hyp].
        qap (imp_E C Pr RIZFm _ (Eps x1 x3)).
        -- qap (qall_E C RIZFm V hV _ (Imp (Eps x0 x4) NL) x1). hyp.
        -- qap (qeq_subst C RIZFm V hV _ (Eps x2 x0) (Suc x1) x3).
           ++ qap (qeq_sym C RIZFm V hV). qap (and_E2 C Pr RIZFm _ (Eps x1 Omega)). hyp.
           ++ uses eps_suc (vV1 x1).
      * uses suc_eqv_inj (vV2 x1 x0).
        qap (qeq_subst C RIZFm V hV _ (Eqv (Suc x2) x0) x2 (Suc x0)); [qap (and_E2 C Pr RIZFm _ (Eps x0 Omega)); hyp|].
        qap (qeq_subst C RIZFm V hV _ (Eqv x0 x3) x3 (Suc x1)); [qap (and_E2 C Pr RIZFm _ (Eps x1 Omega)); hyp|].
        hyp.
Qed.

(** ** ω défini par une formule

    Ind(v) := (∃e. e ∈ v ∧ ∀z. ¬ z ∈ e) ∧ ∀n. n ∈ v → ∃m. m ∈ v ∧ Succ(m, n),
    Succ(m, n) := ∀z. z ∈ m ↔ z ∈ n ∨ z ≃ n (comme dans [IZF_inf]),
    Nat(w) := Ind(w) ∧ ∀v. Ind(v) → w ⊆ v. *)

Definition IndP {Γ} : form (ι V :: Γ) :=
  And (Ex (And (Mem x0 x1) (All (Neg (Mem x0 x1)))))
      (All (Imp (Mem x0 x1) (Ex (And (Mem x0 x2) (All (Iff (Mem x0 x1) (Or (Mem x0 x2) (Eqv x0 x2)))))))).
Definition NatP {Γ} : form (ι V :: Γ) := And IndP (All (Imp IndP (Sub x1 x0))).

Definition IndF {Γ} (v : tm Γ V) : form Γ := vsubst (IndP (Γ := [])) (vV1 v).
Definition NatF {Γ} (w : tm Γ V) : form Γ := vsubst (NatP (Γ := [])) (vV1 w).

Lemma lizf_NatP : lizf _ (NatP (Γ := [])).
Proof. unfold NatP, IndP. repeat constructor. Qed.

Lemma nat_ind : IZFm [ι V] [NatF x0] (IndF x0).
Proof. qap (and_E1 C Pr RIZFm _ _ (All (Imp IndP (Sub x1 x0)))). hypc. Qed.

Lemma nat_min : IZFm [ι V; ι V] [NatF x1; IndF x0] (Sub x1 x0).
Proof.
  qap (imp_E C Pr RIZFm _ (IndF x0)); [|hyp].
  qap (qall_E C RIZFm V hV _ (Imp IndP (Sub x2 x0)) x0).
  qap (and_E2 C Pr RIZFm _ (IndF x1)). hypc.
Qed.

Lemma ind_empty : IZFm [ι V] [IndF x0] (Ex (And (Mem x0 x1) (All (Neg (Mem x0 x1))))).
Proof.
  qap (and_E1 C Pr RIZFm _ _ (All (Imp (Mem x0 x1) (Ex (And (Mem x0 x2) (All (Iff (Mem x0 x1) (Or (Mem x0 x2) (Eqv x0 x2))))))))).
  hypc.
Qed.

Lemma ind_succ : IZFm [ι V; ι V] [IndF x1; Mem x0 x1]
  (Ex (And (Mem x0 x2) (All (Iff (Mem x0 x1) (Or (Mem x0 x2) (Eqv x0 x2)))))).
Proof.
  qap (imp_E C Pr RIZFm _ (Mem x0 x1)); [|hyp].
  qap (qall_E C RIZFm V hV _ (Imp (Mem x0 x2) (Ex (And (Mem x0 x3) (All (Iff (Mem x0 x1) (Or (Mem x0 x2) (Eqv x0 x2))))))) x0).
  qap (and_E2 C Pr RIZFm _ (Ex (And (Mem x0 x2) (All (Neg (Mem x0 x1)))))). hypc.
Qed.

(** Un ensemble sans élément est ≃ ∅   (contexte [e]). *)
Lemma empty_eqv : IZFm [ι V] [All (Neg (Mem x0 x1))] (Eqv x0 Empty).
Proof.
  uses ext_mem (vV2 x0 Empty).
  qap (qall_I C RIZFm V hV). qap (and_I C Pr RIZFm); qap (imp_I C Pr RIZFm); qap (bot_E C Pr RIZFm).
  - qap (imp_E C Pr RIZFm _ (Mem x0 x1)); [|hyp].
    qap (qall_E C RIZFm V hV _ (Neg (Mem x0 x2)) x0). hyp.
  - uses mem_empty (vV1 x0). hyp.
Qed.

(** Succ(m, n) → m ≃ S(n)   (contexte [m; n]). *)
Lemma succ_suc : IZFm [ι V; ι V] [All (Iff (Mem x0 x1) (Or (Mem x0 x2) (Eqv x0 x2)))] (Eqv x0 (Suc x1)).
Proof.
  uses ext_mem (vV2 x0 (Suc x1)).
  qap (qall_I C RIZFm V hV). qap (and_I C Pr RIZFm); qap (imp_I C Pr RIZFm).
  - qap (iff_E2 _ _ (Or (Mem x0 x2) (Eqv x0 x2))); [uses suc_mem (vV2 x0 x2)|].
    qap (iff_E1 _ (Mem x0 x1)); [|hyp].
    qap (qall_E C RIZFm V hV _ (Iff (Mem x0 x2) (Or (Mem x0 x3) (Eqv x0 x3))) x0). hyp.
  - qap (iff_E2 _ (Mem x0 x1)); [qap (qall_E C RIZFm V hV _ (Iff (Mem x0 x2) (Or (Mem x0 x3) (Eqv x0 x3))) x0); hyp|].
    qap (iff_E1 _ (Mem x0 (Suc x2))); [uses suc_mem (vV2 x0 x2)|hyp].
Qed.

(** ω est inductif. *)
Lemma ind_omega : IZFm [] [] (IndF Omega).
Proof.
  qap (and_I C Pr RIZFm).
  - qap (qex_I C RIZFm V hV _ _ Empty). qap (and_I C Pr RIZFm).
    + uses eps_mem (vV2 Empty Omega).
      qap iff_E2; [exact (axm A_omega _ (vV1 Empty))|].
      qap (or_I1 C Pr RIZFm). qap (qeq_refl C RIZFm V hV).
    + qap (qall_I C RIZFm V hV). qap (imp_I C Pr RIZFm). uses mem_empty (vV1 x0). hyp.
  - qap (qall_I C RIZFm V hV). qap (imp_I C Pr RIZFm).
    (* [n] *)
    qap (qex_E C RIZFm V hV _ (And (Eqv x1 x0) (Eps x0 Omega))).
    { qap iff_E1; [exact (axm A_mem _ (vV2 x0 Omega))|hyp]. }
    (* [n'; n] *)
    qap (qex_I C RIZFm V hV _ _ (Suc x0)). qap (and_I C Pr RIZFm).
    + uses eps_mem (vV2 (Suc x0) Omega).
      qap iff_E2; [exact (axm A_omega _ (vV1 (Suc x0)))|].
      qap (or_I2 C Pr RIZFm). qap (qex_I C RIZFm V hV _ _ x0). qap (and_I C Pr RIZFm).
      * qap (and_E2 C Pr RIZFm _ (Eqv x1 x0)). hyp.
      * qap (qeq_refl C RIZFm V hV).
    + qap (qall_I C RIZFm V hV).
      (* [z; n'; n] : z ∈ S n′ ↔ z ∈ n ∨ z ≃ n *)
      qap (and_I C Pr RIZFm); qap (imp_I C Pr RIZFm).
      * qap (or_E C Pr RIZFm _ (Mem x0 x1) (Eqv x0 x1)).
        -- qap (iff_E1 _ (Mem x0 (Suc x1))); [uses suc_mem (vV2 x0 x1)|hyp].
        -- qap (or_I1 C Pr RIZFm). uses mem_congr_r (vV3 x0 x1 x2); [|hyp].
           uses eqv_sym (vV2 x2 x1). qap (and_E1 C Pr RIZFm _ _ (Eps x1 Omega)). hyp.
        -- qap (or_I2 C Pr RIZFm). uses eqv_trans (vV3 x0 x1 x2); [hyp|].
           uses eqv_sym (vV2 x2 x1). qap (and_E1 C Pr RIZFm _ _ (Eps x1 Omega)). hyp.
      * qap (iff_E2 _ _ (Or (Mem x0 x1) (Eqv x0 x1))); [uses suc_mem (vV2 x0 x1)|].
        qap (or_E C Pr RIZFm _ (Mem x0 x2) (Eqv x0 x2)); [hyp| |].
        -- qap (or_I1 C Pr RIZFm). uses mem_congr_r (vV3 x0 x2 x1); [|hyp].
           qap (and_E1 C Pr RIZFm _ _ (Eps x1 Omega)). hyp.
        -- qap (or_I2 C Pr RIZFm). uses eqv_trans (vV3 x0 x2 x1); [hyp|].
           qap (and_E1 C Pr RIZFm _ _ (Eps x1 Omega)). hyp.
Qed.

(** Nat(w) → w ⊆ ω, et n ∈ w → n ∈ ω   (contexte [n; w]). *)
Lemma nat_sub_omega : IZFm [ι V; ι V] [NatF x1; Mem x0 x1] (Mem x0 Omega).
Proof.
  uses mem_of_sub (vV3 x0 x1 Omega); [|hyp].
  uses nat_min (vV2 Omega x1); [hypc|]. exact (use0 ind_omega _).
Qed.

(** Nat(w) → ω ⊆ w : n ε ω → n ∈ w, par ε-induction   (contexte [n; w]). *)
Lemma omega_sub_nat : IZFm [ι V; ι V] [NatF x1; Eps x0 Omega] (Mem x0 x1).
Proof.
  qap (imp_E C Pr RIZFm _ (Eps x0 Omega)); [|hyp].
  qap (qall_E C RIZFm V hV _ (Imp (Eps x0 Omega) (Mem x0 x2)) x0).
  qap (imp_E C Pr RIZFm); [exact (axm A_ind _ (vP1 (Imp (Eps x0 Omega) (Mem x0 x2))))|].
  qap (qall_I C RIZFm V hV). qap (imp_I C Pr RIZFm). qap (imp_I C Pr RIZFm).
  (* [c; n; w] : IH, c ε ω *)
  qap (or_E C Pr RIZFm _ (EqV x0 Empty) (Ex (And (Eps x0 Omega) (EqV x1 (Suc x0))))).
  { qap iff_E1; [exact (axm A_omega _ (vV1 x0))|hyp]. }
  - (* c = ∅ : l'élément vide de w *)
    qap (qex_E C RIZFm V hV _ (And (Mem x0 x3) (All (Neg (Mem x0 x1))))).
    { uses ind_empty (vV1 x2). uses nat_ind (vV1 x2). hypc. }
    (* [e; c; n; w] *)
    qap (qeq_subst C RIZFm V hV _ (Mem x0 x4) Empty x1); [qap (qeq_sym C RIZFm V hV); hyp|].
    uses mem_congr_l (vV3 x0 Empty x3).
    + uses empty_eqv (vV1 x0). qap (and_E2 C Pr RIZFm _ (Mem x0 x3)). hyp.
    + qap (and_E1 C Pr RIZFm _ _ (All (Neg (Mem x0 x1)))). hyp.
  - qap (qex_E C RIZFm V hV _ (And (Eps x0 Omega) (EqV x1 (Suc x0)))); [hyp|].
    (* [y; c; n; w] : y ∈ w par l'hypothèse d'induction *)
    qap (qex_E C RIZFm V hV _ (And (Mem x0 x4) (All (Iff (Mem x0 x1) (Or (Mem x0 x2) (Eqv x0 x2)))))).
    { uses ind_succ (vV2 x0 x3).
      - uses nat_ind (vV1 x3). hypc.
      - qap (imp_E C Pr RIZFm _ (Eps x0 Omega)); [|qap (and_E1 C Pr RIZFm _ _ (EqV x1 (Suc x0))); hyp].
        qap (imp_E C Pr RIZFm _ (Eps x0 x1)).
        + qap (qall_E C RIZFm V hV _ (Imp (Eps x0 x2) (Imp (Eps x0 Omega) (Mem x0 x4))) x0). hyp.
        + qap (qeq_subst C RIZFm V hV _ (Eps x1 x0) (Suc x0) x1).
          * qap (qeq_sym C RIZFm V hV). qap (and_E2 C Pr RIZFm _ (Eps x0 Omega)). hyp.
          * uses eps_suc (vV1 x0). }
    (* [m; y; c; n; w] : m ∈ w, Succ(m, y) *)
    qap (qeq_subst C RIZFm V hV _ (Mem x0 x5) (Suc x1) x2);
      [qap (qeq_sym C RIZFm V hV); qap (and_E2 C Pr RIZFm _ (Eps x1 Omega)); hyp|].
    uses mem_congr_l (vV3 x0 (Suc x1) x4).
    + uses succ_suc (vV2 x0 x1). qap (and_E2 C Pr RIZFm _ (Mem x0 x4)). hyp.
    + qap (and_E1 C Pr RIZFm _ _ (All (Iff (Mem x0 x1) (Or (Mem x0 x2) (Eqv x0 x2))))). hyp.
Qed.

