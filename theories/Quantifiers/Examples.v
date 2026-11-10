(** * Exemple : une logique du premier ordre, vue comme logique d'ordre (1,1)

    Deux sortes : les individus D, de grade (0,0), et les propositions Pr,
    de grade (0,1). À l'ordre (1,1), seul D est quantifiable : Pr ne l'est
    pas, et la signature n'a de quantificateur que sur D. Une relation
    binaire R sur D. Pas de flèches entre sortes. *)

From Stdlib Require Import List Arith Lia.
Import ListNotations.
From SF.Syntax Require Import Spec Terms Vectors.
From SF.Calculus Require Import System Rules.
From SF.Logic Require Import Judgment Propositional.
From SF.Functional Require Import Arrow Graded.
From SF.Quantifiers Require Import Quant Order.

Inductive fsort := D | Pr.

Local Notation ι a := (Spec [] a).

Inductive fsym : spec fsort -> Type :=
| f_imp : fsym (Spec [ι Pr; ι Pr] Pr)
| f_and : fsym (Spec [ι Pr; ι Pr] Pr)
| f_or  : fsym (Spec [ι Pr; ι Pr] Pr)
| f_top : fsym (ι Pr)
| f_bot : fsym (ι Pr)
| f_rel : fsym (Spec [ι D; ι D] Pr)
| f_all : fsym (Spec [Spec [ι D] Pr] Pr)
| f_ex  : fsym (Spec [Spec [ι D] Pr] Pr)
| f_eq  : fsym (Spec [ι D; ι D] Pr).

#[export] Instance f_hasimp : HasImp fsym Pr := {| c_imp := f_imp |}.
#[export] Instance f_hasand : HasAnd fsym Pr := {| c_and := f_and |}.
#[export] Instance f_hasor  : HasOr fsym Pr  := {| c_or := f_or |}.
#[export] Instance f_hastop : HasTop fsym Pr := {| c_top := f_top |}.
#[export] Instance f_hasbot : HasBot fsym Pr := {| c_bot := f_bot |}.

(** Aucune flèche entre sortes. *)
#[export] Instance f_functional : Functional fsym := {|
  Arr := fun _ _ _ => Empty_set;
  s_lam := fun a b c w => match w with end;
  s_app := fun a b c w => match w with end
|}.

Definition f_grade (s : fsort) : grade := match s with D => (0, 0) | Pr => (0, 1) end.

Lemma f_gr_arr a b c (w : @Arr _ fsym f_functional a b c) : f_grade c = garr (f_grade a) (f_grade b).
Proof. destruct w. Qed.

#[export] Instance f_graded : Graded fsym := {| gr := f_grade; gr_arr := f_gr_arr |}.

Lemma D_quantifiable : quantifiable (Sym := fsym) 1 1 D.
Proof. split; cbn; lia. Qed.

Lemma Pr_not_quantifiable : ~ quantifiable (Sym := fsym) 1 1 Pr.
Proof. intros [_ H]; cbn in H; lia. Qed.

(** Les symboles de quantification n'existent que pour D. *)
Definition f_q (s : fsort) : quantifiable (Sym := fsym) 1 1 s -> fsym (Spec [Spec [ι s] Pr] Pr) :=
  match s with
  | D => fun _ => f_all
  | Pr => fun h => False_rect _ (Pr_not_quantifiable h)
  end.
Definition f_qe (s : fsort) : quantifiable (Sym := fsym) 1 1 s -> fsym (Spec [Spec [ι s] Pr] Pr) :=
  match s with
  | D => fun _ => f_ex
  | Pr => fun h => False_rect _ (Pr_not_quantifiable h)
  end.
Definition f_qq (s : fsort) : quantifiable (Sym := fsym) 1 1 s -> fsym (Spec [ι s; ι s] Pr) :=
  match s with
  | D => fun _ => f_eq
  | Pr => fun h => False_rect _ (Pr_not_quantifiable h)
  end.

#[export] Instance f_quantifiers : Quantifiers fsym Pr 1 1 :=
  {| q_all := f_q; q_ex := f_qe; q_eq := f_qq |}.

(** La logique : intuitionniste d'ordre (1,1), au-dessus du calcul trivial. *)
Definition triv : system fsym := generated (fun e : Empty_set => match e with end).

Notation FOL Γ Ξ φ := (deriv triv Pr (iorder_rules (n := 1) (p := 1)) Γ Ξ φ).

Notation hD := D_quantifiable.
Definition Rl {Γ} (t u : Terms.tm fsym Γ D) : form fsym Pr Γ :=
  @tsym _ fsym Γ _ f_rel (@acons _ fsym Γ (ι D) _ t (@acons _ fsym Γ (ι D) _ u anil)).
Notation x0 := (var0 vz).
Notation x1 := (var0 (vs vz)).
Notation x2 := (var0 (vs (vs vz))).
Notation All' := (QAll (n := 1) (p := 1) D hD).
Notation Ex' := (QEx (n := 1) (p := 1) D hD).

(** [eapply], puis recherche des instances d'inclusion ; [hyp] pour les hypothèses. *)
Tactic Notation "qap" uconstr(t) := eapply t; try typeclasses eauto.
Ltac hyp := apply d_ax; simpl; auto.

(** ∀x. R x x ⊢ R c c, dans le contexte [c]. *)
Example inst_refl : FOL [ι D] [All' (Rl x0 x0)] (Rl x0 x0).
Proof.
  qap (qall_E triv _ D hD _ (Rl x0 x0) x0). hyp.
Qed.

(** Échange des quantificateurs universels : ∀x∀y R x y ⊢ ∀y∀x R x y. *)
Example all_swap : FOL [] [All' (All' (Rl x1 x0))] (All' (All' (Rl x0 x1))).
Proof.
  qap (qall_I triv _ D hD). qap (qall_I triv _ D hD).
  qap (qall_E triv _ D hD _ (Rl x1 x0) x1).
  qap (qall_E triv _ D hD _ (All' (Rl x1 x0)) x0).
  hyp.
Qed.

(** ∃x∀y R x y ⊢ ∀y∃x R x y. *)
Example ex_all_all_ex : FOL [] [Ex' (All' (Rl x1 x0))] (All' (Ex' (Rl x0 x1))).
Proof.
  qap (qall_I triv _ D hD).
  qap (qex_E triv _ D hD _ (All' (Rl x1 x0))).
  - hyp.
  - qap (qex_I triv _ D hD _ (Rl x0 x2) x0).
    qap (qall_E triv _ D hD _ (Rl x1 x0) x1).
    hyp.
Qed.

(** L'égalité est symétrique et transitive (dans le contexte [a; b; c]). *)
Example eq_chain :
  FOL [ι D; ι D; ι D]
      [QEq (n := 1) (p := 1) D hD x0 x1; QEq (n := 1) (p := 1) D hD x2 x1]
      (QEq (n := 1) (p := 1) D hD x0 x2).
Proof.
  qap (qeq_trans triv _ D hD _ _ x1).
  - hyp.
  - qap (qeq_sym triv _ D hD). hyp.
Qed.
