(** * Logiques d'ordre (n,p)

    Une logique d'ordre (n,p) ne possède ∀, ∃ et = que pour les sortes
    *quantifiables*, c'est-à-dire de grade strictement sous (n,p). On l'impose
    au niveau des symboles eux-mêmes : [q_all s h] demande une preuve [h] que
    s est quantifiable. Les familles de règles sont indexées par les sortes
    quantifiables, et elles contiennent, pour chacune, les règles génériques
    de [Quant.v] : les règles dérivées s'appliquent donc telles quelles. *)

From Stdlib Require Import List.
Import ListNotations.
From SF.Syntax Require Import Spec Terms Vectors.
From SF.Calculus Require Import System.
From SF.Logic Require Import Judgment Propositional.
From SF.Functional Require Import Arrow Graded.
From SF.Quantifiers Require Import Quant.

Local Notation ι a := (Spec [] a).

Section Order.

Context {Srt : Type} (Sym : spec Srt -> Type) `{Functional Srt Sym} {G : Graded Sym}.
Context (P : Srt) (n p : bound).

Class Quantifiers := {
  q_all : forall s, quantifiable n p s -> Sym (Spec [Spec [ι s] P] P);
  q_ex  : forall s, quantifiable n p s -> Sym (Spec [Spec [ι s] P] P);
  q_eq  : forall s, quantifiable n p s -> Sym (Spec [ι s; ι s] P)
}.

Context `{Quantifiers}.

(** Les sortes quantifiables, avec leur preuve. *)
Definition qsort : Type := { s : Srt & quantifiable n p s }.

Definition qall_inst (k : qsort) : HasForall Sym P (projT1 k) := {| c_all := q_all _ (projT2 k) |}.
Definition qex_inst (k : qsort) : HasExists Sym P (projT1 k) := {| c_ex := q_ex _ (projT2 k) |}.
Definition qeq_inst (k : qsort) : HasEq Sym P (projT1 k) := {| c_eq := q_eq _ (projT2 k) |}.

Definition qall_rules (k : qsort * all_idx) : drule Sym P :=
  @all_rules _ Sym P (projT1 (fst k)) (qall_inst (fst k)) (snd k).
Definition qex_rules (k : qsort * ex_idx) : drule Sym P :=
  @ex_rules _ Sym P (projT1 (fst k)) (qex_inst (fst k)) (snd k).
Definition qeq_rules (k : qsort * eq_idx) : drule Sym P :=
  @eq_rules _ Sym P (projT1 (fst k)) (qeq_inst (fst k)) (snd k).

(** Toutes les règles de quantification et d'égalité de l'ordre (n,p). *)
Definition quant_rules := rsum qall_rules (rsum qex_rules qeq_rules).

(** Chaque famille contient les règles génériques de chaque sorte quantifiable. *)
#[export] Instance qall_includes s (h : quantifiable n p s) :
  Includes qall_rules (@all_rules _ Sym P s (qall_inst (existT _ s h))) :=
  {| inc := fun j => (existT _ s h, j); inc_eq := fun j => eq_refl |}.

#[export] Instance qex_includes s (h : quantifiable n p s) :
  Includes qex_rules (@ex_rules _ Sym P s (qex_inst (existT _ s h))) :=
  {| inc := fun j => (existT _ s h, j); inc_eq := fun j => eq_refl |}.

#[export] Instance qeq_includes s (h : quantifiable n p s) :
  Includes qeq_rules (@eq_rules _ Sym P s (qeq_inst (existT _ s h))) :=
  {| inc := fun j => (existT _ s h, j); inc_eq := fun j => eq_refl |}.

(** La logique intuitionniste d'ordre (n,p), et sa version classique. *)
Definition iorder_rules `{HasImp Srt Sym P} `{HasAnd Srt Sym P} `{HasOr Srt Sym P}
  `{HasTop Srt Sym P} `{HasBot Srt Sym P} := rsum ipc_rules quant_rules.
Definition corder_rules `{HasImp Srt Sym P} `{HasAnd Srt Sym P} `{HasOr Srt Sym P}
  `{HasTop Srt Sym P} `{HasBot Srt Sym P} := rsum cpc_rules quant_rules.

End Order.

Arguments Quantifiers {Srt} Sym {_ G} P n p.
Arguments q_all {Srt Sym _ G P n p _} s h.
Arguments q_ex {Srt Sym _ G P n p _} s h.
Arguments q_eq {Srt Sym _ G P n p _} s h.
Arguments qall_inst {Srt Sym _ G P n p _} k.
Arguments qex_inst {Srt Sym _ G P n p _} k.
Arguments qeq_inst {Srt Sym _ G P n p _} k.
Arguments quant_rules {Srt Sym _ G P n p _}.
Arguments iorder_rules {Srt Sym _ G P n p _ _ _ _ _ _}.
Arguments corder_rules {Srt Sym _ G P n p _ _ _ _ _ _}.

#[export] Typeclasses Transparent quant_rules iorder_rules corder_rules.
#[export] Hint Unfold quant_rules iorder_rules corder_rules : typeclass_instances.

(** ** Formules et règles dérivées dans une logique d'ordre (n,p) *)

Section OrderDerived.

Context {Srt : Type} {Sym : spec Srt -> Type} `{Functional Srt Sym} {G : Graded Sym}.
Context {P : Srt} {n p : bound} {QI : Quantifiers Sym P n p}.
Context (C : system Sym) {I : Type} (R : I -> drule Sym P).

Local Notation form := (form Sym P).
Local Notation "Ξ ⊢ φ" := (deriv C P R _ Ξ φ) (at level 70).

Definition QAll s (h : quantifiable n p s) {Γ} (φ : form (ι s :: Γ)) : form Γ :=
  @All _ Sym P s (qall_inst (existT _ s h)) Γ φ.
Definition QEx s (h : quantifiable n p s) {Γ} (φ : form (ι s :: Γ)) : form Γ :=
  @Ex _ Sym P s (qex_inst (existT _ s h)) Γ φ.
Definition QEq s (h : quantifiable n p s) {Γ} (t u : Terms.tm Sym Γ s) : form Γ :=
  @Eq _ Sym P s (qeq_inst (existT _ s h)) Γ t u.

Section Rules.
Context {Hall : Includes R (qall_rules Sym P n p)} {Hex : Includes R (qex_rules Sym P n p)}
  {Heq : Includes R (qeq_rules Sym P n p)}.

(** Composer les inclusions [R ⊇ qall_rules ⊇ all_rules s]. *)
Definition inc_comp {J K} (R1 : J -> drule Sym P) (R2 : K -> drule Sym P)
  (H1 : Includes R R1) (H2 : Includes R1 R2) : Includes R R2 :=
  {| inc := fun k => inc (inc k);
     inc_eq := fun k => eq_trans (inc_eq (inc k)) (inc_eq k) |}.

Lemma qall_I s h {Γ} (Ξ : list (form Γ)) φ :
  deriv C P R (ι s :: Γ) (wk_list [ι s] Ξ) φ -> Ξ ⊢ QAll s h φ.
Proof. exact (@all_I _ _ C P _ R s _ (inc_comp _ _ Hall (qall_includes Sym P n p s h)) Γ Ξ φ). Qed.

Lemma qall_E s h {Γ} (Ξ : list (form Γ)) φ (t : Terms.tm Sym Γ s) :
  Ξ ⊢ QAll s h φ -> Ξ ⊢ vsubst φ (inst1 t).
Proof. exact (@all_E _ _ C P _ R s _ (inc_comp _ _ Hall (qall_includes Sym P n p s h)) Γ Ξ φ t). Qed.

Lemma qex_I s h {Γ} (Ξ : list (form Γ)) φ (t : Terms.tm Sym Γ s) :
  Ξ ⊢ vsubst φ (inst1 t) -> Ξ ⊢ QEx s h φ.
Proof. exact (@ex_I _ _ C P _ R s _ (inc_comp _ _ Hex (qex_includes Sym P n p s h)) Γ Ξ φ t). Qed.

Lemma qex_E s h {Γ} (Ξ : list (form Γ)) φ χ :
  Ξ ⊢ QEx s h φ ->
  deriv C P R (ι s :: Γ) (φ :: wk_list [ι s] Ξ) (ren_tm χ (wk [ι s])) -> Ξ ⊢ χ.
Proof. exact (@ex_E _ _ C P _ R s _ (inc_comp _ _ Hex (qex_includes Sym P n p s h)) Γ Ξ φ χ). Qed.

Lemma qeq_refl s h {Γ} (Ξ : list (form Γ)) (t : Terms.tm Sym Γ s) : Ξ ⊢ QEq s h t t.
Proof. exact (@eq_refl_d _ _ C P _ R s _ (inc_comp _ _ Heq (qeq_includes Sym P n p s h)) Γ Ξ t). Qed.

Lemma qeq_subst s h {Γ} (Ξ : list (form Γ)) φ (t u : Terms.tm Sym Γ s) :
  Ξ ⊢ QEq s h t u -> Ξ ⊢ vsubst φ (inst1 t) -> Ξ ⊢ vsubst φ (inst1 u).
Proof. exact (@eq_subst _ _ C P _ R s _ (inc_comp _ _ Heq (qeq_includes Sym P n p s h)) Γ Ξ φ t u). Qed.

Lemma qeq_sym s h {Γ} (Ξ : list (form Γ)) (t u : Terms.tm Sym Γ s) :
  Ξ ⊢ QEq s h t u -> Ξ ⊢ QEq s h u t.
Proof. exact (@eq_sym_d _ _ C P _ R s _ (inc_comp _ _ Heq (qeq_includes Sym P n p s h)) Γ Ξ t u). Qed.

Lemma qeq_trans s h {Γ} (Ξ : list (form Γ)) (t u w : Terms.tm Sym Γ s) :
  Ξ ⊢ QEq s h t u -> Ξ ⊢ QEq s h u w -> Ξ ⊢ QEq s h t w.
Proof. exact (@eq_trans_d _ _ C P _ R s _ (inc_comp _ _ Heq (qeq_includes Sym P n p s h)) Γ Ξ t u w). Qed.

End Rules.

End OrderDerived.
