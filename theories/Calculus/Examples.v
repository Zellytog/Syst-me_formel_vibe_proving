(** * Exemple : le λ-calcul modulo β

    La signature et la règle β viennent de [SF.Syntax.Examples]. La règle

      t : [L] -> L, u : L  ⊢  app(lambda(x. t(x)), u)  ~  t(u)

    engendre un système de calcul ; la catégorie syntaxique modulo ce système
    est cartésienne fermée. Le λ-calcul non typé n'est pas décidable : on
    n'en a pas besoin ici. *)

From Category Require Import Lib Theory.Category Structure.Terminal
  Structure.Cartesian Structure.Cartesian.Closed.
From Stdlib Require Import List.
Import ListNotations.
From SF.Syntax Require Import Spec Terms Vectors Examples.
From SF.Calculus Require Import System Rules SynConv.

(** Une seule règle. *)
Definition beta_rule : rule lsym :=
  {| r_ctx := Ξβ; r_sort := L; r_lhs := beta_lhs; r_rhs := beta_rhs |}.

Definition beta : system lsym := generated (fun _ : unit => beta_rule).

(** (λx. x x) y  ~  y y : une instance de la règle par le vecteur [inst_beta]. *)
Example beta_step :
  conv beta (Γ := [ι]) (App (Lam (App (v vz) (v vz))) (v vz)) (App (v vz) (v vz)).
Proof.
  change (conv beta (vsubst beta_lhs inst_beta) (vsubst beta_rhs inst_beta)).
  exact (generated_instance (fun _ : unit => beta_rule) tt inst_beta).
Qed.

(** La conversion passe sous les lieurs, par congruence :
    λz. (λx. x x) z  ~  λz. z z. *)
Example beta_under_lambda :
  conv beta (Γ := []) (Lam (App (Lam (App (v vz) (v vz))) (v vz))) (Lam (App (v vz) (v vz))).
Proof.
  unfold Lam. apply (conv_tsym beta (σ := Spec [Spec [ι] L] L) lam). cbn. split; [|exact Logic.I].
  change (conv beta (vsubst beta_lhs inst_beta) (vsubst beta_rhs inst_beta)).
  exact (generated_instance (fun _ : unit => beta_rule) tt inst_beta).
Qed.

(** La catégorie syntaxique du λ-calcul modulo β est cartésienne fermée. *)
Definition Lambda_beta : Category := SynConv beta.
Definition Lambda_beta_terminal : @Terminal Lambda_beta := SynConv_Terminal beta.
Definition Lambda_beta_cartesian : @Cartesian Lambda_beta := SynConv_Cartesian beta.
Definition Lambda_beta_closed : @Closed Lambda_beta Lambda_beta_cartesian := SynConv_Closed beta.
