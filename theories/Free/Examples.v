(** * Exemples : systèmes libres engendrés par une signature

    Une sorte de base ι, une constante c : ι et une relation binaire R. Dans
    le système libre d'ordre (ω,ω) : l'égalité est réflexive, on quantifie
    sur les prédicats ι → O, et la β-conversion est disponible. À l'ordre
    (1,1), la sorte ι → O existe (au bord) mais n'est pas quantifiable. *)

From Stdlib Require Import List.
Import ListNotations.
From SF.Syntax Require Import Spec Terms Vectors.
From SF.Calculus Require Import System Rules.
From SF.Logic Require Import Judgment Propositional.
From SF.Functional Require Import Arrow Graded.
From SF.Quantifiers Require Import Quant Order.
From SF.Free Require Import Free.

Local Notation ι a := (Spec [] a).

(** ** La signature *)

Definition sι : osrt unit := osort unit (tbase tt).
Definition sO : osrt unit := oO unit.
Definition sP : osrt unit := osort unit (tarr (tbase tt) tO).

Inductive kc : spec (osrt unit) -> Type :=
| k_c : kc (ι sι)
| k_R : kc (Spec [ι sι; ι sι] sO).

Notation Sym := (fsym (S := unit) (n := omega) (p := omega) eq_refl kc).
Notation HOL Γ Ξ φ :=
  (deriv (free_calc unit omega omega eq_refl kc) sO
         (free_rules unit omega omega eq_refl kc) Γ Ξ φ).

Notation hq s := (o_quantifiable unit s kc).
Notation All' s := (QAll (n := omega) (p := omega) s (hq s)).
Notation Eq' s := (QEq (n := omega) (p := omega) s (hq s)).

Definition cst {Γ} : Terms.tm Sym Γ sι := @tsym _ Sym Γ _ (f_const _ _ _ _ _ _ k_c) anil.
Definition Rl {Γ} (t u : Terms.tm Sym Γ sι) : form Sym sO Γ :=
  @tsym _ Sym Γ _ (f_const _ _ _ _ _ _ k_R)
    (@acons _ Sym Γ (ι sι) _ t (@acons _ Sym Γ (ι sι) _ u anil)).

(** La flèche ι → O. *)
Definition wP : @Arr _ Sym _ sι sO sP := farr_i unit omega omega sι sO eq_refl.

Notation x0 := (var0 vz).
Notation x1 := (var0 (vs vz)).

Tactic Notation "qap" uconstr(t) := eapply t; try typeclasses eauto.
Ltac hyp := apply d_ax; simpl; auto.

Notation C := (free_calc unit omega omega eq_refl kc).

(** ** Premier ordre : ⊢ ∀x. x = x *)

Example eq_refl_all : HOL [] [] (All' sι (Eq' sι x0 x0)).
Proof.
  qap (qall_I C _ sι (hq sι)).
  qap (qeq_refl C _ sι (hq sι)).
Qed.

(** ** Ordre supérieur : ⊢ ∀P : ι → O. ∀x. P(x) ⇒ P(x) *)

Example pred_refl :
  HOL [] [] (All' sP (All' sι (Imp (App wP x1 x0) (App wP x1 x0)))).
Proof.
  qap (qall_I C _ sP (hq sP)).
  qap (qall_I C _ sι (hq sι)).
  qap imp_I. hyp.
Qed.

(** ** Calcul : (λx. R x x) c ⊢ R c c, par β *)

#[local] Instance beta_incl : CIncludes (beta_rules (Sym := Sym)) (beta_rules (Sym := Sym)) :=
  {| cinc := fun k => k; cinc_eq := fun _ => eq_refl |}.

Example beta_step : HOL [] [App wP (Lam wP (Rl x0 x0)) cst] (Rl cst cst).
Proof.
  eapply d_conv.
  - exact (beta_conv (beta_rules (Sym := Sym)) wP (Rl x0 x0) cst).
  - hyp.
Qed.

(** ** Ordre (1,1) : ι → O est une sorte, mais pas quantifiable *)

Definition hO11 : inb unit 1 1 tO = true := eq_refl.

Lemma sP_in_11 : inb unit 1 1 (tarr (tbase tt) tO) = true.
Proof. reflexivity. Qed.

Lemma sP_not_quantifiable_11 :
  qb unit 1 1 (tarr (tbase tt) tO) = false.
Proof. reflexivity. Qed.

Lemma ι_quantifiable_11 : qb unit 1 1 (tbase tt) = true.
Proof. reflexivity. Qed.

(** À l'ordre (1,1), (ι → O) → O n'est même pas une sorte. *)
Lemma sPP_not_in_11 : inb unit 1 1 (tarr (tarr (tbase tt) tO) tO) = false.
Proof. reflexivity. Qed.
