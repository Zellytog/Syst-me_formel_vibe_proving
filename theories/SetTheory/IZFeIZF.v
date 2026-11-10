(** * IZF⁻ε étend IZF (théorème 1.5.9)

    IZF est lu dans le langage ∈, ⊆, ≃ de L_IZF, son égalité étant ≃.
    Chaque axiome de IZF est une formule close, prouvée dans IZF⁻ε :
    extensionnalité, paire, réunion, parties (a ⊆ x → a ∈ p), vide,
    infini (avec un successeur défini par z ∈ m ↔ z ∈ n ∨ z ≃ n). Les
    schémas (séparation, collection, ∈-induction) sont prouvés pour une
    métavariable de formule sous l'hypothèse qu'elle est extensionnelle
    ([ExtP], [ExtR]), puis instanciés par toute formule de L_IZF, qui
    vérifie cette hypothèse par le lemme 1.5.8 ([ext_inst], [extR_inst]).
    Les preuves suivent celles des notes : un a ∈ x se ramène à un a′ ≃ a
    avec a′ ε x, auquel on applique l'axiome en ε. *)

From Stdlib Require Import List.
Import ListNotations.
From Equations Require Import Equations.
From SF.Syntax Require Import Spec Terms Renaming Vectors.
From SF.Calculus Require Import System Rules.
From SF.Logic Require Import Judgment Propositional.
From SF.Functional Require Import Arrow.
From SF.Quantifiers Require Import Quant Order.
From SF.SetTheory Require Import IZFe IZFeBasic IZFeExt.

Local Notation ι a := (Spec [] a).
Tactic Notation "qap" uconstr(t) := eapply t; try typeclasses eauto.
Ltac hyp := apply d_ax; simpl; auto 20.

(** ** Les formules de L_IZF sont stables par renommage *)

Lemma lizf_ren {Γ} (φ : form Γ) : lizf Γ φ -> forall Δ (ρ : ren Γ Δ), lizf Δ (ren_tm φ ρ).
Proof.
  induction 1; intros Δ ρ.
  - unfold Mem; rewrite ren_rel2. apply l_mem.
  - unfold Sub; rewrite ren_rel2. apply l_sub.
  - unfold Eqv; rewrite ren_rel2. apply l_eqv.
  - apply l_top.
  - apply l_bot.
  - change (lizf Δ (Imp (ren_tms (σ := ι Pr) φ ρ) (ren_tms (σ := ι Pr) ψ ρ))).
    rewrite !(ren_tms_nil (Sym := isym)). apply l_imp; auto.
  - change (lizf Δ (And (ren_tms (σ := ι Pr) φ ρ) (ren_tms (σ := ι Pr) ψ ρ))).
    rewrite !(ren_tms_nil (Sym := isym)). apply l_and; auto.
  - change (lizf Δ (Or (ren_tms (σ := ι Pr) φ ρ) (ren_tms (σ := ι Pr) ψ ρ))).
    rewrite !(ren_tms_nil (Sym := isym)). apply l_or; auto.
  - apply l_all; auto.
  - apply l_ex; auto.
Qed.

(** ** L'extensionnalité d'une métavariable de formule *)

(** Dans le contexte [φ] : ∀a b. a ≃ b → φ(a) → φ(b). *)
Definition ExtP : form [σP] :=
  All (All (Imp (Eqv x1 x0) (Imp (app1 (s := V) (vs (vs vz)) x1) (app1 (s := V) (vs (vs vz)) x0)))).

Lemma ext_inst {Γ} (Ξ : list (form Γ)) (φ : form (ι V :: Γ)) :
  lizf _ φ -> IZFm Γ Ξ (vsubst ExtP (vP1 φ)).
Proof.
  intros Hl. unfold ExtP, Quant.All.
  rewrite vsubst_Qnt, (vsubst_tms_vup (σ := σP)), vsubst_Qnt, (vsubst_tms_vup (σ := σP)).
  cbn [dom app]. unfold Imp; rewrite !vsubst_Bin, !vsubst_app1. rsimpl.
  set (w := vup [ι V] (vup [ι V] (vP1 φ))).
  assert (Hl' : lizf _ (ahd (atl (atl w)))).
  { subst w. unfold vup, vren. cbn [vcat ahd atl aget vmap app]. unfold ren_tms.
    cbn [dom app]. apply lizf_ren, lizf_ren, Hl. }
  qap (qall_I C RIZFm V hV). qap (qall_I C RIZFm V hV).
  qap (imp_I C Pr RIZFm). qap (imp_I C Pr RIZFm).
  apply (ext_lizf1 _ Hl' _ (ahd (atl w)) (ahd w)); hyp.
Qed.

(** ** Lemmes auxiliaires (contextes concrets) *)

(** a ≃ a′ et a′ ε x donnent a ∈ x   (contexte [a; a′; x]). *)
Lemma mem_I : IZFm [ι V; ι V; ι V] [Eqv x0 x1; Eps x1 x2] (Mem x0 x2).
Proof.
  qap iff_E2; [exact (axm A_mem _ (vV2 x0 x2))|].
  qap (qex_I C RIZFm V hV _ _ x1). qap (and_I C Pr RIZFm); hyp.
Qed.

(** L'égalité de Leibniz entraîne ≃   (contexte [a; b]). *)
Lemma eqV_eqv : IZFm [ι V; ι V] [EqV x0 x1] (Eqv x0 x1).
Proof.
  qap (qeq_subst C RIZFm V hV _ (Eqv x1 x0) x0 x1); [hyp|].
  uses eqv_refl1 (vV1 x0).
Qed.

(** Congruence de ∈ à gauche   (contexte [a; b; x]). *)
Lemma mem_congr_l : IZFm [ι V; ι V; ι V] [Eqv x0 x1; Mem x0 x2] (Mem x1 x2).
Proof. uses mem_congr0 (vV4 x0 x2 x1 x2); [hyp|uses eqv_refl1 (vV1 x2)|hyp]. Qed.

(** Congruence de ∈ à droite   (contexte [a; x; y]). *)
Lemma mem_congr_r : IZFm [ι V; ι V; ι V] [Eqv x1 x2; Mem x0 x1] (Mem x0 x2).
Proof. uses mem_congr0 (vV4 x0 x1 x0 x2); [uses eqv_refl1 (vV1 x0)|hyp|hyp]. Qed.

(** ** Les axiomes de IZF, l'égalité étant ≃

    Chaque axiome est une formule close de L_IZF (∈, ⊆, ≃), et les
    schémas sont énoncés pour une métavariable de formule. *)

(** Extensionnalité : ∀x y. (∀z. z ∈ x ↔ z ∈ y) → x ≃ y. *)
Definition IZF_ext : form [] := All (All (Imp (All (Iff (Mem x0 x2) (Mem x0 x1))) (Eqv x1 x0))).

Lemma izf_ext : IZFm [] [] IZF_ext.
Proof.
  qap (qall_I C RIZFm V hV). qap (qall_I C RIZFm V hV). qap (imp_I C Pr RIZFm).
  qap iff_E2; [exact (axm A_eqv _ (vV2 x1 x0))|]. qap (and_I C Pr RIZFm).
  - uses sub_of_mem (vV2 x1 x0).
    qap (qall_I C RIZFm V hV). qap (imp_I C Pr RIZFm).
    qap (iff_E1 _ (Mem x0 x2)); [|hyp]. qap (qall_E C RIZFm V hV _ (Iff (Mem x0 x3) (Mem x0 x2)) x0). hyp.
  - uses sub_of_mem (vV2 x0 x1).
    qap (qall_I C RIZFm V hV). qap (imp_I C Pr RIZFm).
    qap (iff_E2 _ _ (Mem x0 x1)); [|hyp]. qap (qall_E C RIZFm V hV _ (Iff (Mem x0 x3) (Mem x0 x2)) x0). hyp.
Qed.


(** Paire : ∀x y. ∃p. ∀z. z ∈ p ↔ z ≃ x ∨ z ≃ y. *)
Definition IZF_pair : form [] :=
  All (All (Ex (All (Iff (Mem x0 x1) (Or (Eqv x0 x3) (Eqv x0 x2)))))).

Lemma izf_pair : IZFm [] [] IZF_pair.
Proof.
  qap (qall_I C RIZFm V hV). qap (qall_I C RIZFm V hV).
  qap (qex_I C RIZFm V hV _ _ (Pair x1 x0)).
  qap (qall_I C RIZFm V hV).
  (* [z; y; x] *)
  qap (and_I C Pr RIZFm); qap (imp_I C Pr RIZFm).
  - qap (qex_E C RIZFm V hV _ (And (Eqv x1 x0) (Eps x0 (Pair x3 x2)))).
    { qap iff_E1; [exact (axm A_mem _ (vV2 x0 (Pair x2 x1)))|hyp]. }
    (* [z'; z; y; x] *)
    qap (or_E C Pr RIZFm _ (EqV x0 x3) (EqV x0 x2)).
    + qap iff_E1; [exact (axm A_pair _ (vV3 x0 x3 x2))|].
      qap (and_E2 C Pr RIZFm _ (Eqv x1 x0)). hyp.
    + qap (or_I1 C Pr RIZFm). uses eqv_trans (vV3 x1 x0 x3).
      * qap (and_E1 C Pr RIZFm _ _ (Eps x0 (Pair x3 x2))). hyp.
      * uses eqV_eqv (vV2 x0 x3). hyp.
    + qap (or_I2 C Pr RIZFm). uses eqv_trans (vV3 x1 x0 x2).
      * qap (and_E1 C Pr RIZFm _ _ (Eps x0 (Pair x3 x2))). hyp.
      * uses eqV_eqv (vV2 x0 x2). hyp.
  - qap (or_E C Pr RIZFm _ (Eqv x0 x2) (Eqv x0 x1)); [hyp| |].
    + uses mem_I (vV3 x0 x2 (Pair x2 x1)); [hyp|].
      qap iff_E2; [exact (axm A_pair _ (vV3 x2 x2 x1))|].
      qap (or_I1 C Pr RIZFm). qap (qeq_refl C RIZFm V hV).
    + uses mem_I (vV3 x0 x1 (Pair x2 x1)); [hyp|].
      qap iff_E2; [exact (axm A_pair _ (vV3 x1 x2 x1))|].
      qap (or_I2 C Pr RIZFm). qap (qeq_refl C RIZFm V hV).
Qed.

(** Ensemble vide : ∃e. ∀z. ¬ z ∈ e. *)
Definition IZF_empty : form [] := Ex (All (Neg (Mem x0 x1))).

Lemma izf_empty : IZFm [] [] IZF_empty.
Proof.
  qap (qex_I C RIZFm V hV _ _ Empty). qap (qall_I C RIZFm V hV). qap (imp_I C Pr RIZFm).
  qap (qex_E C RIZFm V hV _ (And (Eqv x1 x0) (Eps x0 Empty))).
  { qap iff_E1; [exact (axm A_mem _ (vV2 x0 Empty))|hyp]. }
  qap (imp_E C Pr RIZFm _ (Eps x0 Empty)); [exact (axm A_empty _ (vV1 x0))|].
  qap (and_E2 C Pr RIZFm _ (Eqv x1 x0)). hyp.
Qed.

(** Réunion : ∀x. ∃u. ∀z. z ∈ u ↔ ∃b. z ∈ b ∧ b ∈ x. *)
Definition IZF_union : form [] :=
  All (Ex (All (Iff (Mem x0 x1) (Ex (And (Mem x1 x0) (Mem x0 x3)))))).

Lemma izf_union : IZFm [] [] IZF_union.
Proof.
  qap (qall_I C RIZFm V hV). qap (qex_I C RIZFm V hV _ _ (Union x0)). qap (qall_I C RIZFm V hV).
  (* [z; x] *)
  qap (and_I C Pr RIZFm); qap (imp_I C Pr RIZFm).
  - qap (qex_E C RIZFm V hV _ (And (Eqv x1 x0) (Eps x0 (Union x2)))).
    { qap iff_E1; [exact (axm A_mem _ (vV2 x0 (Union x1)))|hyp]. }
    (* [z'; z; x] *)
    qap (qex_E C RIZFm V hV _ (And (Eps x1 x0) (Eps x0 x3))).
    { qap iff_E1; [exact (axm A_union _ (vV2 x0 x2))|].
      qap (and_E2 C Pr RIZFm _ (Eqv x1 x0)). hyp. }
    (* [b; z'; z; x] *)
    qap (qex_I C RIZFm V hV _ _ x0). qap (and_I C Pr RIZFm).
    + uses mem_I (vV3 x2 x1 x0).
      * qap (and_E1 C Pr RIZFm _ _ (Eps x1 (Union x3))). hyp.
      * qap (and_E1 C Pr RIZFm _ _ (Eps x0 x3)). hyp.
    + uses eps_mem (vV2 x0 x3). qap (and_E2 C Pr RIZFm _ (Eps x1 x0)). hyp.
  - qap (qex_E C RIZFm V hV _ (And (Mem x1 x0) (Mem x0 x2))); [hyp|].
    (* [b; z; x] *)
    qap (qex_E C RIZFm V hV _ (And (Eqv x1 x0) (Eps x0 x3))).
    { qap iff_E1; [exact (axm A_mem _ (vV2 x0 x2))|].
      qap (and_E2 C Pr RIZFm _ (Mem x1 x0)). hyp. }
    (* [b'; b; z; x] *)
    qap (qex_E C RIZFm V hV _ (And (Eqv x3 x0) (Eps x0 x1))).
    { qap iff_E1; [exact (axm A_mem _ (vV2 x2 x0))|].
      uses mem_congr_r (vV3 x2 x1 x0).
      - qap (and_E1 C Pr RIZFm _ _ (Eps x0 x3)). hyp.
      - qap (and_E1 C Pr RIZFm _ _ (Mem x1 x3)). hyp. }
    (* [z''; b'; b; z; x] *)
    uses mem_I (vV3 x3 x0 (Union x4)).
    + qap (and_E1 C Pr RIZFm _ _ (Eps x0 x1)). hyp.
    + qap iff_E2; [exact (axm A_union _ (vV2 x0 x4))|].
      qap (qex_I C RIZFm V hV _ _ x1). qap (and_I C Pr RIZFm).
      * qap (and_E2 C Pr RIZFm _ (Eqv x3 x0)). hyp.
      * qap (and_E2 C Pr RIZFm _ (Eqv x2 x1)). hyp.
Qed.

Definition vVVP {Γ} (z a : tm Γ V) (φ : form (ι V :: Γ)) : vec isym [ι V; ι V; σP] Γ :=
  @acons _ isym Γ (ι V) _ z (@acons _ isym Γ (ι V) _ a (@acons _ isym Γ σP _ φ anil)).

(** Parties : ∀x. ∃p. ∀a. a ⊆ x → a ∈ p.

    Pour a ⊆ x, on sépare b ≜ {α ε x | α ∈ a}, puis la partie faible
    donne b′ ε P(x) avec z ε b′ ↔ z ε x ∧ z ε b ; alors a ≃ b′. *)
Definition IZF_power : form [] := All (Ex (All (Imp (Sub x0 x2) (Mem x0 x1)))).

Lemma izf_power : IZFm [] [] IZF_power.
Proof.
  qap (qall_I C RIZFm V hV). qap (qex_I C RIZFm V hV _ _ (Power x0)). qap (qall_I C RIZFm V hV).
  qap (imp_I C Pr RIZFm).
  (* [a; x] *)
  qap (qex_E C RIZFm V hV _
         (And (Eps x0 (Power x2)) (All (Iff (Eps x0 x1) (And (Eps x0 x3) (Eps x0 (Sep x3 (Mem x0 x3)))))))).
  { exact (axm A_power _ (vV2 x1 (Sep x1 (Mem x0 x1)))). }
  (* [b'; a; x] *)
  uses mem_I (vV3 x1 x0 (Power x2)).
  2:{ qap (and_E1 C Pr RIZFm _ _ (All (Iff (Eps x0 x1) (And (Eps x0 x3) (Eps x0 (Sep x3 (Mem x0 x3))))))). hyp. }
  qap iff_E2; [exact (axm A_eqv _ (vV2 x1 x0))|]. qap (and_I C Pr RIZFm).
  - qap iff_E2; [exact (axm A_sub _ (vV2 x1 x0))|].
    qap (qall_I C RIZFm V hV). qap (imp_I C Pr RIZFm).
    (* [z; b'; a; x] : z ε a *)
    qap (qex_E C RIZFm V hV _ (And (Eqv x1 x0) (Eps x0 x4))).
    { qap iff_E1; [exact (axm A_mem _ (vV2 x0 x3))|].
      uses mem_of_sub (vV3 x0 x2 x3); [hyp|]. uses eps_mem (vV2 x0 x2). hyp. }
    (* [z'; z; b'; a; x] *)
    uses mem_I (vV3 x1 x0 x2); [qap (and_E1 C Pr RIZFm _ _ (Eps x0 x4)); hyp|].
    qap (iff_E2 _ (Eps x0 x2) (And (Eps x0 x4) (Eps x0 (Sep x4 (Mem x0 x4))))).
    + qap (qall_E C RIZFm V hV _ (Iff (Eps x0 x3) (And (Eps x0 x5) (Eps x0 (Sep x5 (Mem x0 x5))))) x0).
      qap (and_E2 C Pr RIZFm _ (Eps x2 (Power x4))). hyp.
    + qap (and_I C Pr RIZFm); [qap (and_E2 C Pr RIZFm _ (Eqv x1 x0)); hyp|].
      qap iff_E2; [exact (axm A_sep _ (vVVP x0 x4 (Mem x0 x4)))|].
      qap (and_I C Pr RIZFm); [qap (and_E2 C Pr RIZFm _ (Eqv x1 x0)); hyp|].
      uses mem_congr_l (vV3 x1 x0 x3); [qap (and_E1 C Pr RIZFm _ _ (Eps x0 x4)); hyp|].
      uses eps_mem (vV2 x1 x3). hyp.
  - qap iff_E2; [exact (axm A_sub _ (vV2 x0 x1))|].
    qap (qall_I C RIZFm V hV). qap (imp_I C Pr RIZFm).
    (* [z; b'; a; x] : z ε b' *)
    qap (and_E2 C Pr RIZFm _ (Eps x0 x3)).
    qap iff_E1; [exact (axm A_sep _ (vVVP x0 x3 (Mem x0 x3)))|].
    qap (and_E2 C Pr RIZFm _ (Eps x0 x3)).
    qap (iff_E1 _ (Eps x0 x1)); [|hyp].
    qap (qall_E C RIZFm V hV _ (Iff (Eps x0 x2) (And (Eps x0 x4) (Eps x0 (Sep x4 (Mem x0 x4))))) x0).
    qap (and_E2 C Pr RIZFm _ (Eps x1 (Power x3))). hyp.
Qed.

(** Infini : ∃w. (∃e. e ∈ w ∧ ∀z. ¬ z ∈ e) ∧ ∀n. n ∈ w → ∃m. m ∈ w ∧ ∀z. z ∈ m ↔ z ∈ n ∨ z ≃ n.

    Le témoin est ω ; pour n ≃ n′ ε ω, le successeur S n′ = ⋃{n′, {n′, n′}}
    convient. *)
Definition IZF_inf : form [] :=
  Ex (And (Ex (And (Mem x0 x1) (All (Neg (Mem x0 x1)))))
          (All (Imp (Mem x0 x1) (Ex (And (Mem x0 x2) (All (Iff (Mem x0 x1) (Or (Mem x0 x2) (Eqv x0 x2))))))))).

Lemma izf_inf : IZFm [] [] IZF_inf.
Proof.
  qap (qex_I C RIZFm V hV _ _ Omega). qap (and_I C Pr RIZFm).
  - qap (qex_I C RIZFm V hV _ _ Empty). qap (and_I C Pr RIZFm).
    + uses eps_mem (vV2 Empty Omega).
      qap iff_E2; [exact (axm A_omega _ (vV1 Empty))|].
      qap (or_I1 C Pr RIZFm). qap (qeq_refl C RIZFm V hV).
    + qap (qall_I C RIZFm V hV). qap (imp_I C Pr RIZFm).
      qap (qex_E C RIZFm V hV _ (And (Eqv x1 x0) (Eps x0 Empty))).
      { qap iff_E1; [exact (axm A_mem _ (vV2 x0 Empty))|hyp]. }
      qap (imp_E C Pr RIZFm _ (Eps x0 Empty)); [exact (axm A_empty _ (vV1 x0))|].
      qap (and_E2 C Pr RIZFm _ (Eqv x1 x0)). hyp.
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
      (* [z; n'; n] *)
      qap (and_I C Pr RIZFm); qap (imp_I C Pr RIZFm).
      * qap (qex_E C RIZFm V hV _ (And (Eqv x1 x0) (Eps x0 (Suc x2)))).
        { qap iff_E1; [exact (axm A_mem _ (vV2 x0 (Suc x1)))|hyp]. }
        (* [z'; z; n'; n] *)
        qap (qex_E C RIZFm V hV _ (And (Eps x1 x0) (Eps x0 (Pair x3 (Sing x3))))).
        { qap iff_E1; [exact (axm A_union _ (vV2 x0 (Pair x2 (Sing x2))))|].
          qap (and_E2 C Pr RIZFm _ (Eqv x1 x0)). hyp. }
        (* [b; z'; z; n'; n] *)
        qap (or_E C Pr RIZFm _ (EqV x0 x3) (EqV x0 (Sing x3))).
        { qap iff_E1; [exact (axm A_pair _ (vV3 x0 x3 (Sing x3)))|].
          qap (and_E2 C Pr RIZFm _ (Eps x1 x0)). hyp. }
        -- (* b = n' *)
           qap (or_I1 C Pr RIZFm). uses mem_congr_r (vV3 x2 x3 x4).
           ++ uses eqv_sym (vV2 x4 x3). qap (and_E1 C Pr RIZFm _ _ (Eps x3 Omega)). hyp.
           ++ uses mem_I (vV3 x2 x1 x3).
              ** qap (and_E1 C Pr RIZFm _ _ (Eps x1 (Suc x3))). hyp.
              ** qap (qeq_subst C RIZFm V hV _ (Eps x2 x0) x0 x3); [hyp|].
                 qap (and_E1 C Pr RIZFm _ _ (Eps x0 (Pair x3 (Sing x3)))). hyp.
        -- (* b = {n', n'} *)
           qap (or_I2 C Pr RIZFm). uses eqv_trans (vV3 x2 x3 x4).
           2:{ uses eqv_sym (vV2 x4 x3). qap (and_E1 C Pr RIZFm _ _ (Eps x3 Omega)). hyp. }
           uses eqv_trans (vV3 x2 x1 x3); [qap (and_E1 C Pr RIZFm _ _ (Eps x1 (Suc x3))); hyp|].
           qap (or_E C Pr RIZFm _ (EqV x1 x3) (EqV x1 x3)).
           ++ qap iff_E1; [exact (axm A_pair _ (vV3 x1 x3 x3))|].
              qap (qeq_subst C RIZFm V hV _ (Eps x2 x0) x0 (Sing x3)); [hyp|].
              qap (and_E1 C Pr RIZFm _ _ (Eps x0 (Pair x3 (Sing x3)))). hyp.
           ++ uses eqV_eqv (vV2 x1 x3). hyp.
           ++ uses eqV_eqv (vV2 x1 x3). hyp.
      * qap (or_E C Pr RIZFm _ (Mem x0 x2) (Eqv x0 x2)); [hyp| |].
        -- qap (qex_E C RIZFm V hV _ (And (Eqv x1 x0) (Eps x0 x2))).
           { qap iff_E1; [exact (axm A_mem _ (vV2 x0 x1))|].
             uses mem_congr_r (vV3 x0 x2 x1); [|hyp].
             qap (and_E1 C Pr RIZFm _ _ (Eps x1 Omega)). hyp. }
           uses mem_I (vV3 x1 x0 (Suc x2)); [qap (and_E1 C Pr RIZFm _ _ (Eps x0 x2)); hyp|].
           qap iff_E2; [exact (axm A_union _ (vV2 x0 (Pair x2 (Sing x2))))|].
           qap (qex_I C RIZFm V hV _ _ x2). qap (and_I C Pr RIZFm).
           ++ qap (and_E2 C Pr RIZFm _ (Eqv x1 x0)). hyp.
           ++ qap iff_E2; [exact (axm A_pair _ (vV3 x2 x2 (Sing x2)))|].
              qap (or_I1 C Pr RIZFm). qap (qeq_refl C RIZFm V hV).
        -- uses mem_I (vV3 x0 x1 (Suc x1)).
           ++ uses eqv_trans (vV3 x0 x2 x1); [hyp|].
              qap (and_E1 C Pr RIZFm _ _ (Eps x1 Omega)). hyp.
           ++ qap iff_E2; [exact (axm A_union _ (vV2 x1 (Pair x1 (Sing x1))))|].
              qap (qex_I C RIZFm V hV _ _ (Sing x1)). qap (and_I C Pr RIZFm).
              ** qap iff_E2; [exact (axm A_pair _ (vV3 x1 x1 x1))|].
                 qap (or_I1 C Pr RIZFm). qap (qeq_refl C RIZFm V hV).
              ** qap iff_E2; [exact (axm A_pair _ (vV3 (Sing x1) x1 (Sing x1)))|].
                 qap (or_I2 C Pr RIZFm). qap (qeq_refl C RIZFm V hV).
Qed.

(** ** Les schémas, pour une métavariable extensionnelle *)

Local Notation φ2 := (vs (vs vz)).
Local Notation φ3 := (vs (vs (vs vz))).
Local Notation φ4 := (vs (vs (vs (vs vz)))).
Local Notation φ5 := (vs (vs (vs (vs (vs vz))))).
Local Notation φ6 := (vs (vs (vs (vs (vs (vs vz)))))).
Local Notation φ7 := (vs (vs (vs (vs (vs (vs (vs vz))))))).
Local Notation φ8 := (vs (vs (vs (vs (vs (vs (vs (vs vz)))))))).
Local Notation φ9 := (vs (vs (vs (vs (vs (vs (vs (vs (vs vz))))))))).
Local Notation φ10 := (vs (vs (vs (vs (vs (vs (vs (vs (vs (vs vz)))))))))).
Local Notation φ11 := (vs (vs (vs (vs (vs (vs (vs (vs (vs (vs (vs vz))))))))))).
Local Notation φ12 := (vs (vs (vs (vs (vs (vs (vs (vs (vs (vs (vs (vs vz)))))))))))).


(** Utilisation de [ExtP], affaibli dans le contexte [a; b; φ]. *)
Lemma extP_E :
  IZFm [ι V; ι V; σP]
    [All (All (Imp (Eqv x1 x0) (Imp (app1 (s := V) φ4 x1) (app1 (s := V) φ4 x0))));
     Eqv x0 x1; app1 (s := V) φ2 x0]
    (app1 (s := V) φ2 x1).
Proof.
  qap (imp_E C Pr RIZFm _ (app1 (s := V) φ2 x0)); [|hyp].
  qap (imp_E C Pr RIZFm _ (Eqv x0 x1)); [|hyp].
  qap (qall_E C RIZFm V hV _ (Imp (Eqv x1 x0) (Imp (app1 (s := V) φ3 x1) (app1 (s := V) φ3 x0))) x1).
  qap (qall_E C RIZFm V hV _ (All (Imp (Eqv x1 x0) (Imp (app1 (s := V) φ4 x1) (app1 (s := V) φ4 x0)))) x0).
  hyp.
Qed.

(** Séparation : ∀a. ∃s. ∀b. b ∈ s ↔ b ∈ a ∧ φ(b). *)
Definition IZF_sep : form [σP] :=
  All (Ex (All (Iff (Mem x0 x1) (And (Mem x0 x2) (app1 (s := V) φ3 x0))))).

Lemma izf_sep : IZFm [σP] [ExtP] IZF_sep.
Proof.
  qap (qall_I C RIZFm V hV). qap (qex_I C RIZFm V hV _ _ (Sep x0 (app1 (s := V) φ2 x0))).
  qap (qall_I C RIZFm V hV).
  (* [b; a; φ] *)
  qap (and_I C Pr RIZFm); qap (imp_I C Pr RIZFm).
  - qap (qex_E C RIZFm V hV _ (And (Eqv x1 x0) (Eps x0 (Sep x2 (app1 (s := V) φ4 x0))))).
    { qap iff_E1; [exact (axm A_mem _ (vV2 x0 (Sep x1 (app1 (s := V) φ3 x0))))|hyp]. }
    (* [b'; b; a; φ] *)
    qap (and_I C Pr RIZFm).
    + uses mem_congr_l (vV3 x0 x1 x2).
      * uses eqv_sym (vV2 x1 x0). qap (and_E1 C Pr RIZFm _ _ (Eps x0 (Sep x2 (app1 (s := V) φ4 x0)))). hyp.
      * uses eps_mem (vV2 x0 x2). qap (and_E1 C Pr RIZFm _ _ (app1 (s := V) φ3 x0)).
        qap iff_E1; [exact (axm A_sep _ (vVVP x0 x2 (app1 (s := V) φ4 x0)))|].
        qap (and_E2 C Pr RIZFm _ (Eqv x1 x0)). hyp.
    + uses extP_E (vVVP x0 x1 (app1 (s := V) φ4 x0)); [hyp| |].
      * uses eqv_sym (vV2 x1 x0). qap (and_E1 C Pr RIZFm _ _ (Eps x0 (Sep x2 (app1 (s := V) φ4 x0)))). hyp.
      * qap (and_E2 C Pr RIZFm _ (Eps x0 x2)).
        qap iff_E1; [exact (axm A_sep _ (vVVP x0 x2 (app1 (s := V) φ4 x0)))|].
        qap (and_E2 C Pr RIZFm _ (Eqv x1 x0)). hyp.
  - qap (qex_E C RIZFm V hV _ (And (Eqv x1 x0) (Eps x0 x2))).
    { qap iff_E1; [exact (axm A_mem _ (vV2 x0 x1))|].
      qap (and_E1 C Pr RIZFm _ _ (app1 (s := V) φ2 x0)). hyp. }
    (* [b'; b; a; φ] *)
    uses mem_I (vV3 x1 x0 (Sep x2 (app1 (s := V) φ4 x0))); [qap (and_E1 C Pr RIZFm _ _ (Eps x0 x2)); hyp|].
    qap iff_E2; [exact (axm A_sep _ (vVVP x0 x2 (app1 (s := V) φ4 x0)))|].
    qap (and_I C Pr RIZFm); [qap (and_E2 C Pr RIZFm _ (Eqv x1 x0)); hyp|].
    uses extP_E (vVVP x1 x0 (app1 (s := V) φ4 x0)); [hyp| |].
    + qap (and_E1 C Pr RIZFm _ _ (Eps x0 x2)). hyp.
    + qap (and_E2 C Pr RIZFm _ (Mem x1 x2)). hyp.
Qed.

(** ∈-induction : (∀a. (∀b. b ∈ a → φ(b)) → φ(a)) → ∀a. φ(a). *)
Definition IZF_ind : form [σP] :=
  Imp (All (Imp (All (Imp (Mem x0 x1) (app1 (s := V) φ2 x0))) (app1 (s := V) (vs vz) x0)))
      (All (app1 (s := V) (vs vz) x0)).

Lemma izf_ind : IZFm [σP] [ExtP] IZF_ind.
Proof.
  qap (imp_I C Pr RIZFm).
  qap (imp_E C Pr RIZFm); [exact (axm A_ind _ (vP1 (app1 (s := V) (vs vz) x0)))|].
  qap (qall_I C RIZFm V hV). qap (imp_I C Pr RIZFm).
  (* [a; φ] *)
  qap (imp_E C Pr RIZFm _ (All (Imp (Mem x0 x1) (app1 (s := V) φ2 x0)))).
  - qap (qall_E C RIZFm V hV _
           (Imp (All (Imp (Mem x0 x1) (app1 (s := V) φ3 x0))) (app1 (s := V) φ2 x0)) x0). hyp.
  - qap (qall_I C RIZFm V hV). qap (imp_I C Pr RIZFm).
    (* [b; a; φ] *)
    qap (qex_E C RIZFm V hV _ (And (Eqv x1 x0) (Eps x0 x2))).
    { qap iff_E1; [exact (axm A_mem _ (vV2 x0 x1))|hyp]. }
    (* [b'; b; a; φ] *)
    uses extP_E (vVVP x0 x1 (app1 (s := V) φ4 x0)); [hyp| |].
    + uses eqv_sym (vV2 x1 x0). qap (and_E1 C Pr RIZFm _ _ (Eps x0 x2)). hyp.
    + qap (imp_E C Pr RIZFm _ (Eps x0 x2)).
      * qap (qall_E C RIZFm V hV _ (Imp (Eps x0 x3) (app1 (s := V) φ4 x0)) x0). hyp.
      * qap (and_E2 C Pr RIZFm _ (Eqv x1 x0)). hyp.
Qed.

(** Pour une relation ψ(α, β) : l'extensionnalité en α suffit. Dans le
    contexte [ψ] : ∀a a′ b. a ≃ a′ → ψ(a, b) → ψ(a′, b). *)
Definition ExtR : form [σR] :=
  All (All (All (Imp (Eqv x2 x1) (Imp (app2 φ3 x2 x0) (app2 φ3 x1 x0))))).

(** Utilisation de [ExtR], affaibli dans le contexte [a; a′; b; ψ]. *)
Lemma extR_E :
  IZFm [ι V; ι V; ι V; σR]
    [All (All (All (Imp (Eqv x2 x1) (Imp (app2 φ6 x2 x0) (app2 φ6 x1 x0)))));
     Eqv x0 x1; app2 φ3 x0 x2]
    (app2 φ3 x1 x2).
Proof.
  qap (imp_E C Pr RIZFm _ (app2 φ3 x0 x2)); [|hyp].
  qap (imp_E C Pr RIZFm _ (Eqv x0 x1)); [|hyp].
  qap (qall_E C RIZFm V hV _ (Imp (Eqv x1 x2) (Imp (app2 φ4 x1 x0) (app2 φ4 x2 x0))) x2).
  qap (qall_E C RIZFm V hV _ (All (Imp (Eqv x2 x1) (Imp (app2 φ5 x2 x0) (app2 φ5 x1 x0)))) x1).
  qap (qall_E C RIZFm V hV _ (All (All (Imp (Eqv x2 x1) (Imp (app2 φ6 x2 x0) (app2 φ6 x1 x0))))) x0).
  hyp.
Qed.

Definition vVR {Γ} (a : tm Γ V) (ψ : tm (ι V :: ι V :: Γ) Pr) : vec isym [ι V; σR] Γ :=
  @acons _ isym Γ (ι V) _ a (@acons _ isym Γ σR _ ψ anil).
Definition vVVVR {Γ} (a b c : tm Γ V) (ψ : tm (ι V :: ι V :: Γ) Pr) : vec isym [ι V; ι V; ι V; σR] Γ :=
  @acons _ isym Γ (ι V) _ a (@acons _ isym Γ (ι V) _ b (@acons _ isym Γ (ι V) _ c
    (@acons _ isym Γ σR _ ψ anil))).

(** Collection : ∀a. (∀α. α ∈ a → ∃β. ψ(α, β)) → ∃c. ∀α. α ∈ a → ∃β. β ∈ c ∧ ψ(α, β). *)
Definition IZF_coll : form [σR] :=
  All (Imp (All (Imp (Mem x0 x1) (Ex (app2 φ3 x1 x0))))
           (Ex (All (Imp (Mem x0 x2) (Ex (And (Mem x0 x2) (app2 φ4 x1 x0))))))).

Lemma izf_coll : IZFm [σR] [ExtR] IZF_coll.
Proof.
  qap (qall_I C RIZFm V hV). qap (imp_I C Pr RIZFm).
  (* [a; ψ] *)
  qap (qex_E C RIZFm V hV _ (All (Imp (Eps x0 x2) (Ex (And (Eps x0 x2) (app2 φ4 x1 x0)))))).
  { qap (imp_E C Pr RIZFm); [exact (axm A_coll _ (vVR x0 (eta σR (Γ := [ι V; σR]) (vs vz))))|].
    qap (qall_I C RIZFm V hV). qap (imp_I C Pr RIZFm).
    qap (imp_E C Pr RIZFm _ (Mem x0 x1)).
    - qap (qall_E C RIZFm V hV _ (Imp (Mem x0 x2) (Ex (app2 φ4 x1 x0))) x0). hyp.
    - uses eps_mem (vV2 x0 x1). hyp. }
  (* [c; a; ψ] *)
  qap (qex_I C RIZFm V hV _ _ x0). qap (qall_I C RIZFm V hV). qap (imp_I C Pr RIZFm).
  (* [α; c; a; ψ] *)
  qap (qex_E C RIZFm V hV _ (And (Eqv x1 x0) (Eps x0 x3))).
  { qap iff_E1; [exact (axm A_mem _ (vV2 x0 x2))|hyp]. }
  (* [α'; α; c; a; ψ] *)
  qap (qex_E C RIZFm V hV _ (And (Eps x0 x3) (app2 φ5 x1 x0))).
  { qap (imp_E C Pr RIZFm _ (Eps x0 x3)).
    - qap (qall_E C RIZFm V hV _ (Imp (Eps x0 x4) (Ex (And (Eps x0 x4) (app2 φ6 x1 x0)))) x0). hyp.
    - qap (and_E2 C Pr RIZFm _ (Eqv x1 x0)). hyp. }
  (* [β; α'; α; c; a; ψ] *)
  qap (qex_I C RIZFm V hV _ _ x0). qap (and_I C Pr RIZFm).
  - uses eps_mem (vV2 x0 x3). qap (and_E1 C Pr RIZFm _ _ (app2 φ5 x1 x0)). hyp.
  - uses extR_E (vVVVR x1 x2 x0 (eta σR (Γ := [ι V; ι V; ι V; ι V; ι V; σR]) φ5)); [hyp| |].
    + uses eqv_sym (vV2 x2 x1). qap (and_E1 C Pr RIZFm _ _ (Eps x1 x4)). hyp.
    + qap (and_E2 C Pr RIZFm _ (Eps x0 x3)). hyp.
Qed.

(** ** Les relations de L_IZF sont extensionnelles *)

Lemma erel_cons {Δ Γ} Ξ (a b : tm Γ V) (w w' : vec isym Δ Γ) :
  IZFm Γ Ξ (Eqv a b) -> erel Ξ w w' ->
  erel Ξ (@acons _ isym Γ (ι V) _ a w) (@acons _ isym Γ (ι V) _ b w').
Proof.
  intros H Hw x.
  set (P := fun σ (y : var (ι V :: Δ) σ) =>
    match σ as σ0 return var (ι V :: Δ) σ0 -> Type with
    | Spec [] V => fun y => IZFm Γ Ξ (Eqv (aget y (@acons _ isym Γ (ι V) _ a w))
                                          (aget y (@acons _ isym Γ (ι V) _ b w')))
    | _ => fun _ => unit
    end y).
  refine (var_inv P _ _ (ι V) x); unfold P.
  - exact H.
  - intros [[|? ?] [|]] y; try exact tt. apply Hw.
Qed.

Lemma erel_refl {Δ Γ} Ξ (w : vec isym Δ Γ) : erel Ξ w w.
Proof. intros x. apply eqv_refl_gen. Qed.

Lemma vsubst_app2 {Θ Γ} (x : var Θ σR) (t u : tm Θ V) (v : vec isym Θ Γ) :
  vsubst (app2 x t u) v =
  vsubst (aget x v) (@acons _ isym Γ (ι V) _ (vsubst t v) (@acons _ isym Γ (ι V) _ (vsubst u v) (vid Γ))).
Proof.
  change (happ σR (aget x v)
            (@acons _ isym Γ (ι V) _ (vsubst_tms (σ := ι V) t v)
              (@acons _ isym Γ (ι V) _ (vsubst_tms (σ := ι V) u v) anil))
          = vsubst (aget x v) (@acons _ isym Γ (ι V) _ (vsubst t v)
              (@acons _ isym Γ (ι V) _ (vsubst u v) (vid Γ)))).
  rewrite !vsubst_tms_nil, happ_vsubst; reflexivity.
Qed.

Definition vR1 {Γ} (ψ : form (ι V :: ι V :: Γ)) : vec isym [σR] Γ := @acons _ isym Γ σR _ ψ anil.

Lemma extR_inst {Γ} (Ξ : list (form Γ)) (ψ : form (ι V :: ι V :: Γ)) :
  lizf _ ψ -> IZFm Γ Ξ (vsubst ExtR (vR1 ψ)).
Proof.
  intros Hl. unfold ExtR, Quant.All.
  rewrite vsubst_Qnt, (vsubst_tms_vup (σ := σP)), vsubst_Qnt, (vsubst_tms_vup (σ := σP)),
    vsubst_Qnt, (vsubst_tms_vup (σ := σP)).
  cbn [dom app]. unfold Imp; rewrite !vsubst_Bin, !vsubst_app2. rsimpl.
  set (w := vup [ι V] (vup [ι V] (vup [ι V] (vR1 ψ)))).
  assert (Hl' : lizf _ (ahd (atl (atl (atl w))))).
  { subst w. unfold vup, vren. cbn [vcat ahd atl aget vmap app]. unfold ren_tms.
    cbn [dom app]. apply lizf_ren, lizf_ren, lizf_ren, Hl. }
  qap (qall_I C RIZFm V hV). qap (qall_I C RIZFm V hV). qap (qall_I C RIZFm V hV).
  qap (imp_I C Pr RIZFm). qap (imp_I C Pr RIZFm).
  refine (ext_lizf _ Hl' _ _
    (@acons _ isym _ (ι V) _ (ahd (atl (atl w))) (@acons _ isym _ (ι V) _ (ahd w) (vid _)))
    (@acons _ isym _ (ι V) _ (ahd (atl w)) (@acons _ isym _ (ι V) _ (ahd w) (vid _))) _ _).
  - apply erel_cons; [hyp|]. apply erel_cons; [apply eqv_refl_gen|apply erel_refl].
  - hyp.
Qed.

(** ** Réflexivité de l'égalité de IZF *)

Definition IZF_refl : form [] := All (Eqv x0 x0).

Lemma izf_refl : IZFm [] [] IZF_refl.
Proof. qap (qall_I C RIZFm V hV). exact eqv_refl1. Qed.

(** ** Théorème 1.5.9 : IZF⁻ε est une extension de IZF

    On lit IZF dans le langage ∈, ⊆, ≃, l'égalité de IZF étant ≃. Les
    axiomes d'égalité sont la réflexivité ([izf_refl]) et le transport
    pour les formules de L_IZF ([ext_lizf1]) ; les autres axiomes sont
    prouvés ci-dessus, et les schémas sont instanciés par n'importe quelle
    formule de L_IZF, avec paramètres (les variables de Γ). La logique
    étant la même (logique intuitionniste du premier ordre sur V), tout
    théorème de IZF est donc un théorème de IZF⁻ε. *)

Theorem izf_sep_lizf {Γ} (φ : form (ι V :: Γ)) :
  lizf _ φ -> IZFm Γ [] (vsubst IZF_sep (vP1 φ)).
Proof. intros Hl. uses izf_sep (vP1 φ). apply ext_inst, Hl. Qed.

Theorem izf_ind_lizf {Γ} (φ : form (ι V :: Γ)) :
  lizf _ φ -> IZFm Γ [] (vsubst IZF_ind (vP1 φ)).
Proof. intros Hl. uses izf_ind (vP1 φ). apply ext_inst, Hl. Qed.

Theorem izf_coll_lizf {Γ} (ψ : form (ι V :: ι V :: Γ)) :
  lizf _ ψ -> IZFm Γ [] (vsubst IZF_coll (vR1 ψ)).
Proof. intros Hl. uses izf_coll (vR1 ψ). apply extR_inst, Hl. Qed.

Theorem izfm_extends_izf :
  (* égalité *)
  IZFm [] [] IZF_refl /\
  (forall Γ (φ : form (ι V :: Γ)), lizf _ φ -> forall Ξ (a b : tm Γ V),
     IZFm Γ Ξ (Eqv a b) -> IZFm Γ Ξ (vsubst φ (inst1 a)) -> IZFm Γ Ξ (vsubst φ (inst1 b))) /\
  (* axiomes *)
  IZFm [] [] IZF_ext /\ IZFm [] [] IZF_pair /\ IZFm [] [] IZF_union /\
  IZFm [] [] IZF_power /\ IZFm [] [] IZF_empty /\ IZFm [] [] IZF_inf /\
  (* schémas *)
  (forall Γ (φ : form (ι V :: Γ)), lizf _ φ -> IZFm Γ [] (vsubst IZF_sep (vP1 φ))) /\
  (forall Γ (ψ : form (ι V :: ι V :: Γ)), lizf _ ψ -> IZFm Γ [] (vsubst IZF_coll (vR1 ψ))) /\
  (forall Γ (φ : form (ι V :: Γ)), lizf _ φ -> IZFm Γ [] (vsubst IZF_ind (vP1 φ))).
Proof.
  repeat split.
  - exact izf_refl.
  - intros Γ φ Hl. exact (ext_lizf1 φ Hl).
  - exact izf_ext.
  - exact izf_pair.
  - exact izf_union.
  - exact izf_power.
  - exact izf_empty.
  - exact izf_inf.
  - intros Γ φ; exact (izf_sep_lizf φ).
  - intros Γ ψ; exact (izf_coll_lizf ψ).
  - intros Γ φ; exact (izf_ind_lizf φ).
Qed.
