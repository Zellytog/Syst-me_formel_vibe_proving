(** * Exemple : le modèle standard de l'arithmétique d'ordre (1,1)

    Pour la signature de [Arithmetic/Examples.v], on interprète N par les
    entiers (setoïde discret [disc nat]), Pr par les propositions
    ([PropS]), 0 et S par 0 et S, rec_N par [nat_rect], et les symboles
    logiques de façon standard. Les deux règles de rec sont valides, ce qui
    suffit à valider tout le système engendré ([pset_generated]). On obtient
    un modèle de la logique intuitionniste d'ordre (1,1) au-dessus de ce
    calcul, et donc, par correction, que 1 = 0 n'y est pas prouvable
    ([one_eq_zero_unprovable]) et que la logique est cohérente
    ([consistent]). *)

From Category Require Import Lib Theory.Category.
From Stdlib Require Import List.
Import ListNotations.
From SF.Syntax Require Import Spec Terms Vectors.
From SF.Calculus Require Import System Rules.
From SF.Logic Require Import Judgment Propositional.
From SF.Functional Require Import Arrow Graded.
From SF.Quantifiers Require Import Quant Order.
From SF.Arithmetic Require Import Arith Examples.
From SF.Models Require Import PSet Semantics Logic Order SetModels Tarski.

Local Notation ι a := (Spec [] a).

(** ** Les données *)

Definition aSo (s : asort) : pset := match s with N => disc nat | Pr => PropS end.

Local Notation Nv := (pexp punit (disc nat)).
Local Notation Pv := (pexp punit PropS).

Definition cst (k : nat) : Nv := Build_pmor punit (disc nat) (fun _ => k) (fun _ _ _ => eq_refl).

Local Ltac pprop :=
  intros [[u a] b] [[u' a'] b'] [[_ Ha] Hb]; cbn in *; specialize (Ha tt); specialize (Hb tt); tauto.

Definition i_imp : pmor (pprod (pprod punit Pv) Pv) PropS.
Proof.
  refine (Build_pmor (pprod (pprod punit Pv) Pv) PropS (fun q : pcar ((pprod (pprod punit Pv) Pv)) => (snd q tt : Prop) -> (snd (fst q) tt : Prop)) _). pprop. Defined.
Definition i_and : pmor (pprod (pprod punit Pv) Pv) PropS.
Proof.
  refine (Build_pmor (pprod (pprod punit Pv) Pv) PropS (fun q : pcar ((pprod (pprod punit Pv) Pv)) => (snd q tt : Prop) /\ (snd (fst q) tt : Prop)) _). pprop. Defined.
Definition i_or : pmor (pprod (pprod punit Pv) Pv) PropS.
Proof.
  refine (Build_pmor (pprod (pprod punit Pv) Pv) PropS (fun q : pcar ((pprod (pprod punit Pv) Pv)) => (snd q tt : Prop) \/ (snd (fst q) tt : Prop)) _). pprop. Defined.
Definition i_top : pmor punit PropS := Build_pmor punit PropS (fun _ => True) (fun _ _ _ => iff_refl _).
Definition i_bot : pmor punit PropS := Build_pmor punit PropS (fun _ => False) (fun _ _ _ => iff_refl _).

Definition i_zero : pmor punit (disc nat) := Build_pmor punit (disc nat) (fun _ => O) (fun _ _ _ => eq_refl).

Definition i_succ : pmor (pprod punit Nv) (disc nat).
Proof.
  refine (Build_pmor (pprod punit Nv) (disc nat) (fun q : pcar ((pprod punit Nv)) => S (snd q tt)) _).
  intros [u a] [u' a'] [_ H]. cbn in *. rewrite (H tt). reflexivity.
Defined.

Local Notation Sv := (pexp (pprod (pprod punit Nv) Nv) (disc nat)).

(** rec(z, st, m) : st reçoit (k, acc), k en première position. *)
Definition rec_val (z : nat) (st : Sv) (m : nat) : nat :=
  nat_rect (fun _ => nat) z (fun k acc => st ((tt, cst acc), cst k)) m.

Definition i_rec : pmor (pprod (pprod (pprod punit Nv) Sv) Nv) (disc nat).
Proof.
  refine (Build_pmor (pprod (pprod (pprod punit Nv) Sv) Nv) (disc nat) (fun q : pcar ((pprod (pprod (pprod punit Nv) Sv) Nv)) => rec_val (snd q tt) (snd (fst q)) (snd (fst (fst q)) tt)) _).
  intros [[[u m] st] z] [[[u' m'] st'] z'] [[[_ Hm] Hst] Hz]. cbn in *.
  rewrite (Hm tt), (Hz tt). unfold rec_val. induction (m' tt) as [|k IH]; cbn; [reflexivity|].
  rewrite IH. apply Hst.
Defined.

Definition i_all : pmor (pprod punit (pexp (pprod punit Nv) PropS)) PropS.
Proof.
  refine (Build_pmor (pprod punit (pexp (pprod punit Nv) PropS)) PropS (fun q : pcar ((pprod punit (pexp (pprod punit Nv) PropS))) => forall a : Nv, (snd q (tt, a) : Prop)) _).
  intros [u f] [u' f'] [_ H]. cbn in *. split; intros K a; apply (H (tt, a)), K.
Defined.

Definition i_ex : pmor (pprod punit (pexp (pprod punit Nv) PropS)) PropS.
Proof.
  refine (Build_pmor (pprod punit (pexp (pprod punit Nv) PropS)) PropS (fun q : pcar ((pprod punit (pexp (pprod punit Nv) PropS))) => @ex Nv (fun a => (snd q (tt, a) : Prop))) _).
  intros [u f] [u' f'] [_ H]. cbn in *. split; intros [a K]; exists a; apply (H (tt, a)), K.
Defined.

Definition i_eq : pmor (pprod (pprod punit Nv) Nv) PropS.
Proof.
  refine (Build_pmor (pprod (pprod punit Nv) Nv) PropS (fun q : pcar ((pprod (pprod punit Nv) Nv)) => snd q tt = snd (fst q) tt) _).
  intros [[u a] b] [[u' a'] b'] [[_ Ha] Hb]. cbn in *. rewrite (Ha tt), (Hb tt). reflexivity.
Defined.

Definition aIy (σ : spec asort) (c : asym σ) : ictx PSet aSo (dom σ) ~> aSo (cod σ) :=
  match c in asym σ0 return ictx PSet aSo (dom σ0) ~> aSo (cod σ0) with
  | a_imp => i_imp
  | a_and => i_and
  | a_or => i_or
  | a_top => i_top
  | a_bot => i_bot
  | s_0 => i_zero
  | s_S => i_succ
  | s_recN => i_rec
  | s_all => i_all
  | s_ex => i_ex
  | s_eq => i_eq
  end.

(** ** Validation des règles de rec *)

Lemma nat_rect_ext (z z' : nat) (f g : nat -> nat -> nat) m :
  z = z' -> (forall k a, f k a = g k a) -> nat_rect (fun _ => nat) z f m = nat_rect (fun _ => nat) z' g m.
Proof. intros -> H. induction m as [|m IH]; cbn; [reflexivity|]. rewrite IH. apply H. Qed.

Lemma a_rules_valid i γ :
  sval aSo aIy (r_lhs (rec_rules (r := 1) i)) γ ≡ sval aSo aIy (r_rhs (rec_rules (r := 1) i)) γ.
Proof.
  destruct i as [[[|] h] [|]]; [| |exfalso; exact (Pr_not_rec h)|exfalso; exact (Pr_not_rec h)].
  - cbn. apply (pfun_proper (snd (fst γ))). repeat split; try (intros []); cbn; try reflexivity.
    apply nat_rect_ext; [reflexivity|]. intros k a.
    apply (pfun_proper (snd (fst γ))). repeat split; intros []; reflexivity.
  - cbn. reflexivity.
Qed.

Definition aHc := pset_generated (rec_rules (r := 1)) aSo aIy a_rules_valid.

(** La vérité : l'identité de [PropS]. *)
Definition aT0 : ppred PropS := @mkp PropS (fun A => A) (fun A B E H => proj1 E H).

Local Notation AL := (order_logic C Pr (n := 1) (p := 1)).

Lemma a_imp_std q : aT0 (aIy _ c_imp q) <-> (aT0 (snd q tt) -> aT0 (snd (fst q) tt)).
Proof. reflexivity. Qed.
Lemma a_and_std q : aT0 (aIy _ c_and q) <-> (aT0 (snd q tt) /\ aT0 (snd (fst q) tt)).
Proof. reflexivity. Qed.
Lemma a_or_std q : aT0 (aIy _ c_or q) <-> (aT0 (snd q tt) \/ aT0 (snd (fst q) tt)).
Proof. reflexivity. Qed.
Lemma a_top_std q : aT0 (aIy _ c_top q) <-> True.
Proof. reflexivity. Qed.
Lemma a_bot_std q : aT0 (aIy _ c_bot q) <-> False.
Proof. reflexivity. Qed.

Lemma a_all_std (k : qsort asym 1 1) q :
  aT0 (aIy _ (Order.q_all (projT1 k) (projT2 k)) q) <-> forall a, aT0 (snd q (tt, a)).
Proof. destruct k as [[|] h]; [reflexivity|exfalso; exact (Pr_not_q h)]. Qed.
Lemma a_ex_std (k : qsort asym 1 1) q :
  aT0 (aIy _ (Order.q_ex (projT1 k) (projT2 k)) q) <-> @ex _ (fun a => aT0 (snd q (tt, a))).
Proof. destruct k as [[|] h]; [reflexivity|exfalso; exact (Pr_not_q h)]. Qed.
Lemma a_eq_std (k : qsort asym 1 1) q :
  aT0 (aIy _ (Order.q_eq (projT1 k) (projT2 k)) q) <-> snd q tt ≡ snd (fst q) tt.
Proof. destruct k as [[|] h]; [reflexivity|exfalso; exact (Pr_not_q h)]. Qed.

(** Le modèle standard, modèle de la logique intuitionniste d'ordre (1,1) sur ce calcul. *)
Definition standard_model :=
  tarski_lmodel C Pr aSo aIy aHc aT0 a_imp_std a_and_std a_or_std a_top_std a_bot_std
    a_all_std a_ex_std a_eq_std.

Lemma a_sound Γ Ξ φ :
  provable AL Γ Ξ φ -> forall γ, (forall χ, In χ Ξ -> sval aSo aIy χ γ) -> sval aSo aIy φ γ.
Proof.
  exact (tarski_sound C Pr aSo aIy aHc aT0 a_imp_std a_and_std a_or_std a_top_std a_bot_std
           a_all_std a_ex_std a_eq_std Γ Ξ φ).
Qed.

(** 1 = 0 n'est pas prouvable. *)
Theorem one_eq_zero_unprovable : ~ provable AL [] [] (EqN (Succ Zero) Zero).
Proof. intros H. pose proof (a_sound _ _ _ H tt (fun _ (E : In _ []) => match E with end)) as K. discriminate K. Qed.

(** Cohérence. *)
Theorem consistent : ~ provable AL [] [] Bot.
Proof. intros H. exact (a_sound _ _ _ H tt (fun _ (E : In _ []) => match E with end)). Qed.
