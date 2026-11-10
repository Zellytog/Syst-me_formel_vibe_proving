(** * IZFε : premiers développements

    Les lemmes 1.5.1 à 1.5.6 des notes : ⊆ est un préordre dont
    l'équivalence associée est ≃, et ⊆ se caractérise par ∈. Tout est
    prouvé dans IZF⁻ε. *)

From Stdlib Require Import List.
Import ListNotations.
From SF.Syntax Require Import Spec Terms Vectors.
From SF.Calculus Require Import System Rules.
From SF.Logic Require Import Judgment Propositional.
From SF.Functional Require Import Arrow.
From SF.Quantifiers Require Import Quant Order.
From SF.SetTheory Require Import IZFe.

Local Notation ι a := (Spec [] a).

Tactic Notation "qap" uconstr(t) := eapply t; try typeclasses eauto.
Ltac hyp := apply d_ax; simpl; auto 20.

(** ** Instances des axiomes *)

Lemma axm (i : izfm_idx) {Γ} (Ξ : list (form Γ)) (v : vec isym (d_ctx (izfm_rules i)) Γ) :
  IZFm Γ Ξ (vsubst (d_concl (izfm_rules i)) v).
Proof. apply (rule_inc C Pr RIZFm izfm_rules i Ξ v _ eq_refl). destruct i; intros p []. Qed.

Definition vV1 {Γ} (x : tm Γ V) : vec isym [ι V] Γ := @acons _ isym Γ (ι V) _ x anil.
Definition vV2 {Γ} (x y : tm Γ V) : vec isym [ι V; ι V] Γ :=
  @acons _ isym Γ (ι V) _ x (@acons _ isym Γ (ι V) _ y anil).
Definition vP1 {Γ} (φ : form (ι V :: Γ)) : vec isym [σP] Γ := @acons _ isym Γ σP _ φ anil.

(** ** Règles dérivées *)

Section Rules.
Context {Γ : ctx isort} (Ξ : list (form Γ)).

Lemma iff_E1 A B : IZFm Γ Ξ (Iff A B) -> IZFm Γ Ξ A -> IZFm Γ Ξ B.
Proof. intros H1 H2. qap (imp_E C Pr RIZFm _ A B); [qap (and_E1 C Pr RIZFm _ _ (Imp B A)); exact H1|exact H2]. Qed.

Lemma iff_E2 A B : IZFm Γ Ξ (Iff A B) -> IZFm Γ Ξ B -> IZFm Γ Ξ A.
Proof. intros H1 H2. qap (imp_E C Pr RIZFm _ B A); [qap (and_E2 C Pr RIZFm _ (Imp A B)); exact H1|exact H2]. Qed.

End Rules.

(** ** Lemme 1.5.1 : x ⊆ x *)

Lemma sub_refl : IZFm [] [] (All (Sub x0 x0)).
Proof.
  qap (imp_E C Pr RIZFm); [exact (axm A_ind [] (vP1 (Sub x0 x0)))|].
  qap (qall_I C RIZFm V hV). qap (imp_I C Pr RIZFm).
  qap iff_E2; [exact (axm A_sub _ (vV2 x0 x0))|].
  qap (qall_I C RIZFm V hV). qap (imp_I C Pr RIZFm).
  qap iff_E2; [exact (axm A_mem _ (vV2 x0 x1))|].
  qap (qex_I C RIZFm V hV _ _ x0).
  qap (and_I C Pr RIZFm); [|hyp].
  qap iff_E2; [exact (axm A_eqv _ (vV2 x0 x0))|].
  qap (and_I C Pr RIZFm);
    (qap (imp_E C Pr RIZFm _ (Eps x0 x1));
     [qap (qall_E C RIZFm V hV _ (Imp (Eps x0 x2) (Sub x0 x0)) x0); hyp|hyp]).
Qed.

(** ** Application d'un lemme ouvert

    Un lemme est énoncé dans un contexte de variables Γ₀ avec des
    hypothèses Ξ₀ ; on l'applique dans Γ par un vecteur w (des termes
    concrets, pour que [vsubst] calcule), en dérivant les hypothèses
    instanciées. *)

Lemma use {Γ0 Ξ0 φ} (H : IZFm Γ0 Ξ0 φ) {Γ} (w : vec isym Γ0 Γ) (Ξ : list (form Γ)) :
  (forall χ, In χ Ξ0 -> IZFm Γ Ξ (vsubst χ w)) -> IZFm Γ Ξ (vsubst φ w).
Proof.
  intros Hh. apply (deriv_cut_gen _ _ _ (deriv_subst _ _ _ H Γ w)).
  intros χ Hχ. unfold vsubst_list in Hχ. apply in_map_iff in Hχ as (χ0 & <- & Hχ0). apply Hh, Hχ0.
Qed.

Lemma use0 {φ} (H : IZFm [] [] φ) {Γ} (Ξ : list (form Γ)) : IZFm Γ Ξ (vsubst φ anil).
Proof. apply (use H anil Ξ). intros χ []. Qed.

Tactic Notation "uses" constr(H) uconstr(w) := refine (use H w _ _); [intros ? Hin; repeat (destruct Hin as [<-|Hin]); try contradiction].

(** x ⊆ x et x ≃ x, dans le contexte [x]. *)
Lemma sub_refl1 : IZFm [ι V] [] (Sub x0 x0).
Proof. qap (qall_E C RIZFm V hV _ (Sub x0 x0) x0). exact (use0 sub_refl []). Qed.

Lemma eqv_refl1 : IZFm [ι V] [] (Eqv x0 x0).
Proof.
  qap iff_E2; [exact (axm A_eqv _ (vV2 x0 x0))|].
  qap (and_I C Pr RIZFm); exact sub_refl1.
Qed.

(** ** Lemme 1.5.2 : a ε x → a ∈ x   (contexte [a; x]) *)

Lemma eps_mem : IZFm [ι V; ι V] [Eps x0 x1] (Mem x0 x1).
Proof.
  qap iff_E2; [exact (axm A_mem _ (vV2 x0 x1))|].
  qap (qex_I C RIZFm V hV _ _ x0).
  qap (and_I C Pr RIZFm); [|hyp].
  uses eqv_refl1 (vV1 x0).
Qed.

(** ** Lemme 1.5.3 : (∀a. a ∈ x → a ∈ y) → x ⊆ y   (contexte [x; y]) *)

Lemma sub_of_mem : IZFm [ι V; ι V] [All (Imp (Mem x0 x1) (Mem x0 x2))] (Sub x0 x1).
Proof.
  qap iff_E2; [exact (axm A_sub _ (vV2 x0 x1))|].
  qap (qall_I C RIZFm V hV). qap (imp_I C Pr RIZFm).
  qap (imp_E C Pr RIZFm _ (Mem x0 x1)).
  - qap (qall_E C RIZFm V hV _ (Imp (Mem x0 x2) (Mem x0 x3)) x0). hyp.
  - uses eps_mem (vV2 x0 x1). hyp.
Qed.

Notation x5 := (var0 (vs (vs (vs (vs (vs vz)))))).
Notation x6 := (var0 (vs (vs (vs (vs (vs (vs vz))))))).

(** ** Lemme 1.5.4 : x ⊆ y → (∀a. a ∈ y → a ∈ z) → x ⊆ z   (contexte [x; y; z])

    Immédiat à partir des définitions : un a ε x est dans y, donc dans z. *)

Lemma sub_mem_trans : IZFm [ι V; ι V; ι V] [Sub x0 x1; All (Imp (Mem x0 x2) (Mem x0 x3))] (Sub x0 x2).
Proof.
  qap iff_E2; [exact (axm A_sub _ (vV2 x0 x2))|].
  qap (qall_I C RIZFm V hV). qap (imp_I C Pr RIZFm).
  qap (imp_E C Pr RIZFm _ (Mem x0 x2)).
  - qap (qall_E C RIZFm V hV _ (Imp (Mem x0 x3) (Mem x0 x4)) x0). hyp.
  - qap (imp_E C Pr RIZFm _ (Eps x0 x1)); [|hyp].
    qap (qall_E C RIZFm V hV _ (Imp (Eps x0 x2) (Mem x0 x3)) x0).
    qap iff_E1; [exact (axm A_sub _ (vV2 x1 x2))|hyp].
Qed.

(** ** Lemme 1.5.5 : x ⊆ y → y ⊆ z → x ⊆ z, par ε-induction sur y

    Pour a ε x : a ≃ a′ ε y, puis a′ ≃ a″ ε z ; l'hypothèse de récurrence
    en a′ (deux fois) donne a ⊆ a″ et a″ ⊆ a, d'où a ∈ z. *)

Definition Tform : form [ι V] := All (All (Imp (Sub x1 x2) (Imp (Sub x2 x0) (Sub x1 x0)))).

Lemma sub_trans_all : IZFm [] [] (All Tform).
Proof.
  qap (imp_E C Pr RIZFm); [exact (axm A_ind [] (vP1 Tform))|].
  qap (qall_I C RIZFm V hV). qap (imp_I C Pr RIZFm).
  unfold Tform. qap (qall_I C RIZFm V hV). qap (qall_I C RIZFm V hV).
  qap (imp_I C Pr RIZFm). qap (imp_I C Pr RIZFm).
  (* contexte [z; x; y] ; but x ⊆ z *)
  qap iff_E2; [exact (axm A_sub _ (vV2 x1 x0))|].
  qap (qall_I C RIZFm V hV). qap (imp_I C Pr RIZFm).
  (* contexte [a; z; x; y] ; a ε x ; but a ∈ z *)
  (* a ∈ y *)
  qap (qex_E C RIZFm V hV _ (And (Eqv x1 x0) (Eps x0 x4))).
  { qap iff_E1; [exact (axm A_mem _ (vV2 x0 x3))|].
    qap (imp_E C Pr RIZFm _ (Eps x0 x2)); [|hyp].
    qap (qall_E C RIZFm V hV _ (Imp (Eps x0 x3) (Mem x0 x4)) x0).
    qap iff_E1; [exact (axm A_sub _ (vV2 x2 x3))|hyp]. }
  (* contexte [a'; a; z; x; y] ; a ≃ a' ∧ a' ε y ; a' ∈ z *)
  qap (qex_E C RIZFm V hV _ (And (Eqv x1 x0) (Eps x0 x3))).
  { qap iff_E1; [exact (axm A_mem _ (vV2 x0 x2))|].
    qap (imp_E C Pr RIZFm _ (Eps x0 x4)).
    - qap (qall_E C RIZFm V hV _ (Imp (Eps x0 x5) (Mem x0 x3)) x0).
      qap iff_E1; [exact (axm A_sub _ (vV2 x4 x2))|hyp].
    - qap (and_E2 C Pr RIZFm _ (Eqv x1 x0)). hyp. }
  (* contexte [a''; a'; a; z; x; y] ; a' ≃ a'' ∧ a'' ε z ; but a ∈ z *)
  qap iff_E2; [exact (axm A_mem _ (vV2 x2 x3))|].
  qap (qex_I C RIZFm V hV _ _ x0).
  qap (and_I C Pr RIZFm); [|qap (and_E2 C Pr RIZFm _ (Eqv x1 x0)); hyp].
  (* a ≃ a'' : deux fois l'hypothèse de récurrence en a' *)
  qap iff_E2; [exact (axm A_eqv _ (vV2 x2 x0))|]. qap (and_I C Pr RIZFm).
  - qap (imp_E C Pr RIZFm _ (Sub x1 x0)); [qap (imp_E C Pr RIZFm _ (Sub x2 x1))|].
    + qap (qall_E C RIZFm V hV _ (Imp (Sub x3 x2) (Imp (Sub x2 x0) (Sub x3 x0))) x0).
      qap (qall_E C RIZFm V hV _ (All (Imp (Sub x1 x3) (Imp (Sub x3 x0) (Sub x1 x0)))) x2).
      qap (imp_E C Pr RIZFm _ (Eps x1 x5)).
      * qap (qall_E C RIZFm V hV _ (Imp (Eps x0 x6) (All (All (Imp (Sub x1 x2) (Imp (Sub x2 x0) (Sub x1 x0)))))) x1). hyp.
      * qap (and_E2 C Pr RIZFm _ (Eqv x2 x1)). hyp.
    + qap (and_E1 C Pr RIZFm _ _ (Sub x1 x2)). qap iff_E1; [exact (axm A_eqv _ (vV2 x2 x1))|].
      qap (and_E1 C Pr RIZFm _ _ (Eps x1 x5)). hyp.
    + qap (and_E1 C Pr RIZFm _ _ (Sub x0 x1)). qap iff_E1; [exact (axm A_eqv _ (vV2 x1 x0))|].
      qap (and_E1 C Pr RIZFm _ _ (Eps x0 x3)). hyp.
  - qap (imp_E C Pr RIZFm _ (Sub x1 x2)); [qap (imp_E C Pr RIZFm _ (Sub x0 x1))|].
    + qap (qall_E C RIZFm V hV _ (Imp (Sub x1 x2) (Imp (Sub x2 x0) (Sub x1 x0))) x2).
      qap (qall_E C RIZFm V hV _ (All (Imp (Sub x1 x3) (Imp (Sub x3 x0) (Sub x1 x0)))) x0).
      qap (imp_E C Pr RIZFm _ (Eps x1 x5)).
      * qap (qall_E C RIZFm V hV _ (Imp (Eps x0 x6) (All (All (Imp (Sub x1 x2) (Imp (Sub x2 x0) (Sub x1 x0)))))) x1). hyp.
      * qap (and_E2 C Pr RIZFm _ (Eqv x2 x1)). hyp.
    + qap (and_E2 C Pr RIZFm _ (Sub x1 x0)). qap iff_E1; [exact (axm A_eqv _ (vV2 x1 x0))|].
      qap (and_E1 C Pr RIZFm _ _ (Eps x0 x3)). hyp.
    + qap (and_E2 C Pr RIZFm _ (Sub x2 x1)). qap iff_E1; [exact (axm A_eqv _ (vV2 x2 x1))|].
      qap (and_E1 C Pr RIZFm _ _ (Eps x1 x5)). hyp.
Qed.

Definition vV3 {Γ} (x y z : tm Γ V) : vec isym [ι V; ι V; ι V] Γ :=
  @acons _ isym Γ (ι V) _ x (@acons _ isym Γ (ι V) _ y (@acons _ isym Γ (ι V) _ z anil)).

(** Lemme 1.5.5, dans le contexte [x; y; z]. *)
Lemma sub_trans : IZFm [ι V; ι V; ι V] [Sub x0 x1; Sub x1 x2] (Sub x0 x2).
Proof.
  qap (imp_E C Pr RIZFm _ (Sub x1 x2)); [qap (imp_E C Pr RIZFm _ (Sub x0 x1))|]; [|hyp|hyp].
  qap (qall_E C RIZFm V hV _ (Imp (Sub x1 x2) (Imp (Sub x2 x0) (Sub x1 x0))) x2).
  qap (qall_E C RIZFm V hV _ (All (Imp (Sub x1 x3) (Imp (Sub x3 x0) (Sub x1 x0)))) x0).
  qap (qall_E C RIZFm V hV _ (All (All (Imp (Sub x1 x2) (Imp (Sub x2 x0) (Sub x1 x0))))) x1).
  exact (use0 sub_trans_all _).
Qed.

(** ≃ est une équivalence. *)
Lemma eqv_sym : IZFm [ι V; ι V] [Eqv x0 x1] (Eqv x1 x0).
Proof.
  qap iff_E2; [exact (axm A_eqv _ (vV2 x1 x0))|]. qap (and_I C Pr RIZFm).
  - qap (and_E2 C Pr RIZFm _ (Sub x0 x1)). qap iff_E1; [exact (axm A_eqv _ (vV2 x0 x1))|hyp].
  - qap (and_E1 C Pr RIZFm _ _ (Sub x1 x0)). qap iff_E1; [exact (axm A_eqv _ (vV2 x0 x1))|hyp].
Qed.

Lemma eqv_trans : IZFm [ι V; ι V; ι V] [Eqv x0 x1; Eqv x1 x2] (Eqv x0 x2).
Proof.
  qap iff_E2; [exact (axm A_eqv _ (vV2 x0 x2))|]. qap (and_I C Pr RIZFm).
  - uses sub_trans (vV3 x0 x1 x2).
    + qap (and_E1 C Pr RIZFm _ _ (Sub x1 x0)). qap iff_E1; [exact (axm A_eqv _ (vV2 x0 x1))|hyp].
    + qap (and_E1 C Pr RIZFm _ _ (Sub x2 x1)). qap iff_E1; [exact (axm A_eqv _ (vV2 x1 x2))|hyp].
  - uses sub_trans (vV3 x2 x1 x0).
    + qap (and_E2 C Pr RIZFm _ (Sub x1 x2)). qap iff_E1; [exact (axm A_eqv _ (vV2 x1 x2))|hyp].
    + qap (and_E2 C Pr RIZFm _ (Sub x0 x1)). qap iff_E1; [exact (axm A_eqv _ (vV2 x0 x1))|hyp].
Qed.

(** ** Lemme 1.5.6 : x ⊆ y ↔ ∀a. a ∈ x → a ∈ y *)

(** Le sens direct, dans le contexte [a; x; y]. *)
Lemma mem_of_sub : IZFm [ι V; ι V; ι V] [Sub x1 x2; Mem x0 x1] (Mem x0 x2).
Proof.
  qap (qex_E C RIZFm V hV _ (And (Eqv x1 x0) (Eps x0 x2))).
  { qap iff_E1; [exact (axm A_mem _ (vV2 x0 x1))|hyp]. }
  (* [a'; a; x; y] : a ≃ a' ∧ a' ε x *)
  qap (qex_E C RIZFm V hV _ (And (Eqv x1 x0) (Eps x0 x4))).
  { qap iff_E1; [exact (axm A_mem _ (vV2 x0 x3))|].
    qap (imp_E C Pr RIZFm _ (Eps x0 x2)).
    - qap (qall_E C RIZFm V hV _ (Imp (Eps x0 x3) (Mem x0 x4)) x0).
      qap iff_E1; [exact (axm A_sub _ (vV2 x2 x3))|hyp].
    - qap (and_E2 C Pr RIZFm _ (Eqv x1 x0)). hyp. }
  (* [a''; a'; a; x; y] : a' ≃ a'' ∧ a'' ε y *)
  qap iff_E2; [exact (axm A_mem _ (vV2 x2 x4))|].
  qap (qex_I C RIZFm V hV _ _ x0).
  qap (and_I C Pr RIZFm); [|qap (and_E2 C Pr RIZFm _ (Eqv x1 x0)); hyp].
  uses eqv_trans (vV3 x2 x1 x0).
  - qap (and_E1 C Pr RIZFm _ _ (Eps x1 x3)). hyp.
  - qap (and_E1 C Pr RIZFm _ _ (Eps x0 x4)). hyp.
Qed.

Lemma sub_iff_mem : IZFm [ι V; ι V] [] (Iff (Sub x0 x1) (All (Imp (Mem x0 x1) (Mem x0 x2)))).
Proof.
  qap (and_I C Pr RIZFm); qap (imp_I C Pr RIZFm).
  - qap (qall_I C RIZFm V hV). qap (imp_I C Pr RIZFm). uses mem_of_sub (vV3 x0 x1 x2); hyp.
  - uses sub_of_mem (vV2 x0 x1); hyp.
Qed.

(** Corollaire 1.5.7 : ⊆ est un préordre ([sub_refl1], [sub_trans]) dont
    l'équivalence associée est ≃ ([A_eqv], [eqv_sym], [eqv_trans]). *)
