(** * Exemple : le modèle standard de l'arithmétique, vu dans le cadre Prop

    On reprend les données de [SetExamples.v] (N ↦ nat, Pr ↦ Prop, rec_N ↦
    nat_rect). On les fait passer par la construction générique
    [FrameTarski.v], avec le cadre d'évidence [prop_frame]. Il suffit de
    vérifier que les symboles logiques y sont standard, à ≡ (ici ↔) près.
    Les codages imprédicatifs de ∨, ⊥, ∃ et de l'égalité de Leibniz sont
    équivalents aux connecteurs de Rocq. La correction en réalisabilité
    redonne la cohérence. *)

From Category Require Import Lib Theory.Category.
From Stdlib Require Import List.
Import ListNotations.
From SF.Syntax Require Import Spec Terms Vectors.
From SF.Calculus Require Import System Rules.
From SF.Logic Require Import Judgment Propositional.
From SF.Functional Require Import Arrow Graded.
From SF.Quantifiers Require Import Quant Order.
From SF.Arithmetic Require Import Arith Examples.
From SF.Models Require Import PSet Frame Semantics Logic Order SetModels Tarski FrameModel FrameTarski
  SetExamples.

Local Notation ι a := (Spec [] a).

Definition aT : pmor PropS prop_frame := pmor_id PropS.

Local Ltac qsort_cases k := destruct k as [[|] h]; [|exfalso; exact (Pr_not_q h)].

Lemma f_imp_std q : aT (aIy _ c_imp q) ≡ fimp (F := prop_frame) (aT (snd q tt)) (aT (snd (fst q) tt)).
Proof. cbn. tauto. Qed.
Lemma f_and_std q : aT (aIy _ c_and q) ≡ fand (F := prop_frame) (aT (snd q tt)) (aT (snd (fst q) tt)).
Proof. cbn. tauto. Qed.
Lemma f_or_std q : aT (aIy _ c_or q) ≡ for_ (F := prop_frame) (aT (snd q tt)) (aT (snd (fst q) tt)).
Proof.
  cbn -[fall]. split.
  - intros H. apply prop_fall. intros χ [H1 H2]. cbn in H1, H2. destruct H; auto.
  - intros H. apply (proj1 (prop_fall _) H). cbn. split; auto.
Qed.
Lemma f_top_std q : aT (aIy _ c_top q) ≡ ftop (F := prop_frame).
Proof. cbn. tauto. Qed.
Lemma f_bot_std0 q : aT (aIy _ c_bot q) ≡ fbot (F := prop_frame).
Proof. cbn -[fall]. split; [intros []|intros H; exact (proj1 (prop_fall _) H False)]. Qed.
Definition f_bot_std := fequiv_of_eq _ _ f_bot_std0.

(** Un argument de [Nv] = ⟦N⟧^1 ne dépend que de sa valeur en tt. *)
Lemma nv_const (a : pexp punit (disc nat)) : @peq (pprod punit (pexp punit (disc nat))) (tt, a) (up1 aSo N (a tt)).
Proof. split; [exact Logic.I|]. intros []. reflexivity. Qed.

Lemma f_all_std (k : qsort asym 1 1) q :
  aT (aIy _ (Order.q_all (projT1 k) (projT2 k)) q)
  ≡ fall (F := prop_frame) (fun a : aSo (projT1 k) => aT (snd q (up1 aSo _ a))).
Proof.
  qsort_cases k. cbn -[fall]. split.
  - intros H. apply prop_fall. intros a. apply H.
  - intros H a. apply (proj2 (pfun_proper (snd q) (nv_const a))), (proj1 (prop_fall _) H).
Qed.

Lemma f_ex_std (k : qsort asym 1 1) q :
  aT (aIy _ (Order.q_ex (projT1 k) (projT2 k)) q)
  ≡ fex (F := prop_frame) (fun a : aSo (projT1 k) => aT (snd q (up1 aSo _ a))).
Proof.
  qsort_cases k. cbn -[fall]. split.
  - intros [a Ha]. apply prop_fall. intros χ H. apply (proj1 (prop_fall _) H (a tt)).
    apply (proj1 (pfun_proper (snd q) (nv_const a))), Ha.
  - intros H. apply (proj1 (prop_fall _) H). apply prop_fall. intros a Ha. exists (pconst aSo (s := N) a). exact Ha.
Qed.

Lemma f_eq_std0 (k : qsort asym 1 1) q :
  aT (aIy _ (Order.q_eq (projT1 k) (projT2 k)) q) ≡ leib (F := prop_frame) (snd q tt) (snd (fst q) tt).
Proof.
  qsort_cases k. cbn -[fall]. split.
  - intros E. apply prop_fall. intros ψ H. rewrite <- E. exact H.
  - intros H.
    set (ψ := Build_pmor (disc nat) PropS (fun z => snd q tt = z)
                (fun z z' (E : z = z') => conj (fun e => eq_trans e E) (fun e => eq_trans e (eq_sym E)))).
    exact (proj1 (prop_fall _) H ψ eq_refl).
Qed.

Definition f_eq_std (k : qsort asym 1 1) := fequiv_of_eq _ _ (f_eq_std0 k).

Local Notation AL := (order_logic C Pr (n := 1) (p := 1)).

Definition prop_arith_model :=
  frame_lmodel prop_frame C Pr aSo aIy aHc aT f_imp_std f_and_std f_or_std f_top_std f_bot_std
    f_all_std f_ex_std f_eq_std.

(** La cohérence, par la correction générique dans un cadre d'évidence. *)
Theorem consistent' : ~ provable AL [] [] Bot.
Proof.
  intros Hd.
  destruct (frame_sound_closed prop_frame C Pr aSo aIy aHc aT f_imp_std f_and_std f_or_std f_top_std
              f_bot_std f_all_std f_ex_std f_eq_std _ Hd) as [e He].
  exact (He Logic.I).
Qed.
