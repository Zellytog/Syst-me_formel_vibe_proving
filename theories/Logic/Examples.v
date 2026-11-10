(** * Exemples : logique propositionnelle intuitionniste et classique

    Une signature avec une seule sorte de propositions et les cinq
    connecteurs. Le système de calcul sous-jacent est engendré par aucune
    règle : la conversion est alors l'égalité syntaxique (à clôture près).
    Les variables propositionnelles sont des variables de contexte de
    spécification [] -> P. *)

From Stdlib Require Import List.
Import ListNotations.
From SF.Syntax Require Import Spec Terms Vectors.
From SF.Calculus Require Import System Rules.
From SF.Logic Require Import Judgment Propositional.

Inductive psort := Pr.

Local Notation ι := (Spec [] Pr).

Inductive psym : spec psort -> Type :=
| s_imp : psym (Spec [ι; ι] Pr)
| s_and : psym (Spec [ι; ι] Pr)
| s_or  : psym (Spec [ι; ι] Pr)
| s_top : psym ι
| s_bot : psym ι.

#[export] Instance psym_imp : HasImp psym Pr := {| c_imp := s_imp |}.
#[export] Instance psym_and : HasAnd psym Pr := {| c_and := s_and |}.
#[export] Instance psym_or  : HasOr psym Pr  := {| c_or := s_or |}.
#[export] Instance psym_top : HasTop psym Pr := {| c_top := s_top |}.
#[export] Instance psym_bot : HasBot psym Pr := {| c_bot := s_bot |}.

(** Le système de calcul trivial : aucune règle. *)
Definition triv : system psym := generated (fun e : Empty_set => match e with end).

Notation IPC Ξ φ := (deriv triv Pr ipc_rules _ Ξ φ).
Notation CPC Ξ φ := (deriv triv Pr cpc_rules _ Ξ φ).

(** [apply] ne résout pas toujours l'instance [Includes] ; on la cherche ensuite. *)
Tactic Notation "nd" uconstr(t) := eapply t; try typeclasses eauto.

(** Trois variables propositionnelles A, B, C. *)
Definition Γ3 : ctx psort := [ι; ι; ι].
Definition A : form psym Pr Γ3 := mv vz.
Definition B : form psym Pr Γ3 := mv (vs vz).
Definition C : form psym Pr Γ3 := mv (vs (vs vz)).

Example id_A : IPC [] (Imp A A).
Proof. nd imp_I; apply hyp; simpl; auto. Qed.

Example and_comm : IPC [And A B] (And B A).
Proof.
  nd and_I.
  - nd (and_E2 _ _ _ _ A); apply hyp; simpl; auto.
  - nd (and_E1 _ _ _ _ _ B); apply hyp; simpl; auto.
Qed.

Example imp_trans : IPC [] (Imp (Imp A B) (Imp (Imp B C) (Imp A C))).
Proof.
  nd imp_I; nd imp_I; nd imp_I.
  nd (imp_E _ _ _ _ B); [apply hyp; simpl; auto|].
  nd (imp_E _ _ _ _ A); [apply hyp; simpl; auto|].
  apply hyp; simpl; auto.
Qed.

Example or_comm : IPC [Or A B] (Or B A).
Proof.
  nd (or_E _ _ _ _ A B); [apply hyp; simpl; auto| |].
  - nd or_I2; apply hyp; simpl; auto.
  - nd or_I1; apply hyp; simpl; auto.
Qed.

Example ex_falso : IPC [Bot] A.
Proof. nd bot_E; apply hyp; simpl; auto. Qed.

(** En logique classique : ¬¬A ⊢ A. *)
Example dne : CPC [Neg (Neg A)] A.
Proof.
  nd (or_E _ _ _ _ A (Neg A)); [nd excluded_middle| |].
  - apply hyp; simpl; auto.
  - nd bot_E. nd (imp_E _ _ _ _ (Neg A)).
    + apply hyp; simpl; auto.
    + apply hyp; simpl; auto.
Qed.

(** Méta-théorèmes génériques en action.

    Réindexation : de [⊢ A → A] dans Γ3, on obtient [⊢ φ → φ] pour toute
    formule φ, en substituant le vecteur [φ, B, C]. *)
Example id_any (φ : form psym Pr Γ3) : IPC [] (Imp φ φ).
Proof.
  pose proof (deriv_subst _ _ _ id_A Γ3
                (@acons _ psym _ ι _ φ (@acons _ psym _ ι _ B (@acons _ psym _ ι _ C anil))))
    as H.
  unfold Imp in H; rewrite vsubst_Bin in H. unfold A in H; rewrite vsubst_mvar in H.
  exact H.
Qed.

(** Coupure : de [⊢ A → A] et [A → A ⊢ B → B], on tire [⊢ B → B]. *)
Example cut_example : IPC [] (Imp B B).
Proof.
  apply (deriv_cut _ _ _ id_A).
  nd imp_I; apply hyp; simpl; auto.
Qed.
