(** * IZFε avec le choix dépendant (forme bornée)

    Le schéma, à paramètres X (un ensemble) et φ (une relation) :

      (∀x. x ε X ⇒ ∃y. y ε X ∧ φ(x, y))
        ⇒ ∀x₀. x₀ ε X ⇒
          ∃f. (∀n. n ε ω ⇒ ∃y. y ε X ∧ ⟨n, y⟩ ε f)
            ∧ (∀n y y'. ⟨n, y⟩ ε f ⇒ ⟨n, y'⟩ ε f ⇒ y = y')
            ∧ (∀z. z ε f ⇒ ∃n. n ε ω ∧ ∃y. y ε X ∧ z = ⟨n, y⟩)
            ∧ ⟨∅, x₀⟩ ε f
            ∧ (∀n y y'. ⟨n, y⟩ ε f ⇒ ⟨S(n), y'⟩ ε f ⇒ φ(y, y')).

    f est le graphe d'une suite de X issue de x₀ dont deux termes
    consécutifs sont reliés par φ ; S(n) = ⋃{n, {n, n}} et l'égalité est
    celle de Leibniz. *)

From Stdlib Require Import List.
Import ListNotations.
From SF.Syntax Require Import Spec Terms.
From SF.Calculus Require Import System Rules.
From SF.Logic Require Import Judgment Propositional.
From SF.Functional Require Import Arrow.
From SF.Quantifiers Require Import Quant Order.
From SF.SetTheory Require Import IZFe.

Local Notation ι a := (Spec [] a).
Local Notation x5 := (var0 (vs (vs (vs (vs (vs vz)))))).

(** Dans le contexte [X; φ] (X est la variable 0). *)
Definition dc_hyp : form [ι V; σR] :=
  All (Imp (Eps x0 x1) (Ex (And (Eps x0 x2) (app2 (vs (vs (vs vz))) x1 x0)))).

(** Dans le contexte [f; x₀; X; φ]. *)
Definition dc_tot : form [ι V; ι V; ι V; σR] :=
  All (Imp (Eps x0 Omega) (Ex (And (Eps x0 x4) (Eps (OPair x1 x0) x2)))).

Definition dc_fun : form [ι V; ι V; ι V; σR] :=
  All (All (All (Imp (Eps (OPair x2 x1) x3) (Imp (Eps (OPair x2 x0) x3) (EqV x1 x0))))).

Definition dc_sub : form [ι V; ι V; ι V; σR] :=
  All (Imp (Eps x0 x1) (Ex (And (Eps x0 Omega) (Ex (And (Eps x0 x5) (EqV x2 (OPair x1 x0))))))).

Definition dc_start : form [ι V; ι V; ι V; σR] := Eps (OPair Empty x1) x0.

Definition dc_step : form [ι V; ι V; ι V; σR] :=
  All (All (All (Imp (Eps (OPair x2 x1) x3) (Imp (Eps (OPair (Suc x2) x0) x3)
    (app2 (vs (vs (vs (vs (vs (vs vz)))))) x1 x0))))).

Definition A_dc : drule isym Pr :=
  ax [ι V; σR] (Imp dc_hyp (All (Imp (Eps x0 x1)
    (Ex (And dc_tot (And dc_fun (And dc_sub (And dc_start dc_step)))))))).

Definition RIZFeD := rsum RIZFe (fun _ : unit => A_dc).

#[export] Typeclasses Transparent RIZFeD.
#[export] Hint Unfold RIZFeD : typeclass_instances.

Notation IZFeD Γ Ξ φ := (deriv C Pr RIZFeD Γ Ξ φ).
