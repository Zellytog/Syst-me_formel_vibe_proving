(** * IZFε avec le choix dénombrable (forme bornée)

    Le schéma, à paramètres X (un ensemble) et φ (une relation) :

      (∀n. n ε ω ⇒ ∃y. y ε X ∧ φ(n, y))
        ⇒ ∃f. (∀n. n ε ω ⇒ ∃y. y ε X ∧ ⟨n, y⟩ ε f ∧ φ(n, y))
            ∧ (∀n y y'. ⟨n, y⟩ ε f ⇒ ⟨n, y'⟩ ε f ⇒ y = y')
            ∧ (∀z. z ε f ⇒ ∃n. n ε ω ∧ ∃y. y ε X ∧ z = ⟨n, y⟩).

    f est le graphe d'une fonction de ω dans X qui choisit, pour chaque n,
    un témoin de φ(n, ·) ; l'égalité est celle de Leibniz. *)

From Stdlib Require Import List.
Import ListNotations.
From SF.Syntax Require Import Spec Terms.
From SF.Calculus Require Import System Rules.
From SF.Logic Require Import Judgment Propositional.
From SF.Quantifiers Require Import Quant Order.
From SF.SetTheory Require Import IZFe.

Local Notation ι a := (Spec [] a).

(** Dans le contexte [X; φ] (X est la variable 0). *)
Definition cc_hyp : form [ι V; σR] :=
  All (Imp (Eps x0 Omega) (Ex (And (Eps x0 x2) (app2 (vs (vs (vs vz))) x1 x0)))).

(** Dans le contexte [f; X; φ]. *)
Definition cc_tot : form [ι V; ι V; σR] :=
  All (Imp (Eps x0 Omega)
           (Ex (And (Eps x0 x3) (And (Eps (OPair x1 x0) x2) (app2 (vs (vs (vs (vs vz)))) x1 x0))))).

Definition cc_fun : form [ι V; ι V; σR] :=
  All (All (All (Imp (Eps (OPair x2 x1) x3) (Imp (Eps (OPair x2 x0) x3) (EqV x1 x0))))).

Definition cc_sub : form [ι V; ι V; σR] :=
  All (Imp (Eps x0 x1) (Ex (And (Eps x0 Omega) (Ex (And (Eps x0 x4) (EqV x2 (OPair x1 x0))))))).

Definition A_cc : drule isym Pr :=
  ax [ι V; σR] (Imp cc_hyp (Ex (And cc_tot (And cc_fun cc_sub)))).

Definition RIZFeC := rsum RIZFe (fun _ : unit => A_cc).

#[export] Typeclasses Transparent RIZFeC.
#[export] Hint Unfold RIZFeC : typeclass_instances.

Notation IZFeC Γ Ξ φ := (deriv C Pr RIZFeC Γ Ξ φ).
