(** * Quantificateurs bornés et recherche bornée (méta) *)

From Stdlib Require Import List Arith Lia Bool.

Fixpoint ball (N : nat) (P : nat -> bool) : bool :=
  match N with 0 => true | S k => ball k P && P k end.

Fixpoint bex (N : nat) (P : nat -> bool) : bool :=
  match N with 0 => false | S k => bex k P || P k end.

Lemma ball_spec N P : ball N P = true <-> forall k, k < N -> P k = true.
Proof.
  induction N as [|N IH]; cbn; [split; [intros _ k Hk; lia|reflexivity]|].
  rewrite Bool.andb_true_iff, IH. split.
  - intros [H1 H2] k Hk. destruct (Nat.eq_dec k N) as [->|]; [exact H2|apply H1; lia].
  - intros H. split; [intros k Hk; apply H; lia|apply H; lia].
Qed.

Lemma bex_spec N P : bex N P = true <-> exists k, k < N /\ P k = true.
Proof.
  induction N as [|N IH]; cbn; [split; [discriminate|intros (k & Hk & _); lia]|].
  rewrite Bool.orb_true_iff, IH. split.
  - intros [(k & Hk & H)|H]; [exists k; split; [lia|exact H]|exists N; split; [lia|exact H]].
  - intros (k & Hk & H). destruct (Nat.eq_dec k N) as [->|]; [right; exact H|left; exists k; split; [lia|exact H]].
Qed.

Fixpoint blast (N : nat) (P : nat -> bool) : nat :=
  match N with 0 => 0 | S k => if P k then k else blast k P end.

Lemma blast_spec N P : (exists k, k < N /\ P k = true) -> blast N P < N /\ P (blast N P) = true.
Proof.
  induction N as [|N IH]; intros (k & Hk & H); [lia|]. cbn.
  destruct (P N) eqn:EN; [split; [lia|exact EN]|].
  destruct (Nat.eq_dec k N) as [->|Hne]; [congruence|].
  destruct IH as [H1 H2]; [exists k; split; [lia|exact H]|]. split; [lia|exact H2].
Qed.
