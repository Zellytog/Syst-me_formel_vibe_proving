(** * Le lemme méta : une fonctionnelle continue a une borne uniforme calculable

    Pour G : (N → B) → N, on note
    - path k j : le mot des j premiers bits de k, prolongé par des 0 ;
    - trunc α j : α↾j prolongé par des 0 ;
    - C'_G(n) : pour tout mot k < 2ⁿ de longueur n, il existe j ≤ n tel que
      G(path k j) ≤ j (c'est la version décidable de « n est une borne
      uniforme de la barre C_G(ℓ) :⇔ ∃ j ≤ |ℓ|, G((ℓ↾j)0^∞) ≤ j »).

    [fan_meta] : sous WKL et Markov, si G est continue en tout chemin, il
    existe n tel que C'_G(n). C'est l'argument de l'article (théorème 28) :
    sinon les mots qui évitent C_G forment un arbre infini, dont WKL donne un
    chemin α, et la continuité de G en α fournit un préfixe de α dans C_G.

    [t0_meta] : si C'_G(n), alors pour tout α il existe j ≤ n avec
    G(trunc α j) ≤ j ; c'est ce que cherche le réalisateur de la borne. *)

From Stdlib Require Import List Arith Lia Bool.
Import ListNotations.
From SF.Fan Require Import Statement Bounded.

Definition path (k j : nat) : nat -> bool := fun i => (i <? j) && Nat.testbit k i.
Definition trunc (α : nat -> bool) (j : nat) : nat -> bool := fun i => (i <? j) && α i.

Definition Pk (G : (nat -> bool) -> nat) (k j : nat) : bool := G (path k j) <=? j.
Definition Cp (G : (nat -> bool) -> nat) (n : nat) : bool := ball (2 ^ n) (fun k => bex (S n) (Pk G k)).

(** ** Outils *)

Lemma cont_ext G : (forall α, cont_at G α) -> forall β β', (forall i, β i = β' i) -> G β = G β'.
Proof. intros HC β β' H. destruct (HC β') as [m Hm]. apply Hm. intros i _. apply H. Qed.

Lemma bex_ext N P Q : (forall j, j < N -> P j = Q j) -> bex N P = bex N Q.
Proof.
  induction N as [|N IH]; intros H; [reflexivity|]. cbn. rewrite IH, H; [reflexivity|lia|].
  intros j Hj; apply H; lia.
Qed.

Lemma ball_false N P : ball N P = false -> exists k, k < N /\ P k = false.
Proof.
  induction N as [|N IH]; cbn; [discriminate|]. intros H.
  apply andb_false_iff in H as [H|H].
  - destruct (IH H) as (k & Hk & Hk'). exists k; split; [lia|exact Hk'].
  - exists N; split; [lia|exact H].
Qed.

Lemma nth_pre α n i : i < n -> nth i (pre α n) false = α i.
Proof.
  intros Hi. unfold pre.
  rewrite (nth_indep _ false (α 0)) by (rewrite length_map, length_seq; exact Hi).
  rewrite map_nth, seq_nth by exact Hi. reflexivity.
Qed.

Lemma length_pre α n : length (pre α n) = n.
Proof. unfold pre. rewrite length_map, length_seq. reflexivity. Qed.

(** Tout mot de longueur n est formé des n premiers bits d'un k < 2ⁿ. *)
Lemma bits α n : exists k, k < 2 ^ n /\ forall i, i < n -> Nat.testbit k i = α i.
Proof.
  revert α. induction n as [|n IH]; intros α.
  - exists 0. split; [cbn; lia|intros i Hi; lia].
  - destruct (IH (fun i => α (S i))) as (k & Hk & Hb).
    exists (Nat.b2n (α 0) + 2 * k). split.
    + rewrite Nat.pow_succ_r'. destruct (α 0); cbn [Nat.b2n]; lia.
    + intros [|i] Hi.
      * apply Nat.add_b2n_double_bit0.
      * cbn [Nat.testbit]. rewrite Nat.div2_div, Nat.add_b2n_double_div2. apply Hb. lia.
Qed.

Lemma pre_trunc α j m : m <= j -> pre (trunc α j) m = pre α m.
Proof.
  intros Hm. unfold pre. apply map_ext_in. intros i Hi. apply in_seq in Hi.
  unfold trunc. replace (i <? j) with true by (symmetry; apply Nat.ltb_lt; lia). reflexivity.
Qed.

Lemma prefix_pre α m n : m <= n -> prefix (pre α m) (pre α n).
Proof.
  intros H. exists (map α (seq m (n - m))). unfold pre.
  rewrite <- map_app, <- seq_app. f_equal. f_equal. lia.
Qed.

(** ** La borne uniforme existe *)

(** Le mot ℓ, tronqué à j et prolongé par des 0. *)
Definition wpath (l : list bool) (j : nat) : nat -> bool := fun i => (i <? j) && nth i l false.
Definition Cl (G : (nat -> bool) -> nat) (l : list bool) : bool :=
  bex (S (length l)) (fun j => G (wpath l j) <=? j).

Theorem fan_meta G : WKL_meta -> MP_meta -> (forall α, cont_at G α) -> exists n, Cp G n = true.
Proof.
  intros WKL MP HC. apply MP. intros Hno.
  set (T := fun l => negb (Cl G l)).
  assert (Hpc : forall l l', prefix l l' -> T l' = true -> T l = true).
  { intros l l' [s ->] H. unfold T in *. apply negb_true_iff in H. apply negb_true_iff.
    destruct (Cl G l) eqn:El; [|reflexivity]. rewrite <- H. symmetry.
    unfold Cl in *. apply bex_spec in El as (j & Hj & Hjt). apply bex_spec.
    exists j. split; [rewrite length_app; lia|]. rewrite <- Hjt. f_equal. apply (cont_ext G HC).
    intros i. unfold wpath. destruct (Nat.ltb_spec i j); [|reflexivity]. cbn.
    apply app_nth1. lia. }
  assert (Hinf : forall n, exists l, length l = n /\ T l = true).
  { intros n. destruct (ball_false _ _ (Hno n)) as (k & Hk & Hkf).
    exists (pre (Nat.testbit k) n). split; [apply length_pre|].
    unfold T. apply negb_true_iff. unfold Cl. rewrite length_pre. rewrite <- Hkf.
    apply bex_ext. intros j Hj. unfold Pk. f_equal. apply (cont_ext G HC).
    intros i. unfold wpath, path. destruct (Nat.ltb_spec i j); [|reflexivity]. cbn.
    apply nth_pre. lia. }
  destruct (WKL T Hpc Hinf) as [α Hα].
  destruct (HC α) as [m Hm]. set (M := Nat.max m (G α)).
  specialize (Hα M). unfold T in Hα. apply negb_true_iff in Hα.
  assert (Hc : Cl G (pre α M) = true).
  { unfold Cl. rewrite length_pre. apply bex_spec. exists M. split; [lia|].
    apply Nat.leb_le. rewrite Hm; [lia|]. intros i Hi. unfold wpath.
    replace (i <? M) with true by (symmetry; apply Nat.ltb_lt; lia). cbn. apply nth_pre. lia. }
  congruence.
Qed.

(** ** Ce que cherche le réalisateur *)

Theorem t0_meta G n : (forall α, cont_at G α) -> Cp G n = true ->
  forall α, exists j, j < S n /\ (G (trunc α j) <=? j) = true.
Proof.
  intros HC Hn α. destruct (bits α n) as (k & Hk & Hb).
  unfold Cp in Hn. rewrite ball_spec in Hn. specialize (Hn k Hk). apply bex_spec in Hn as (j & Hj & Hjt).
  exists j. split; [exact Hj|]. unfold Pk in Hjt. rewrite <- Hjt. f_equal. apply (cont_ext G HC).
  intros i. unfold trunc, path. destruct (Nat.ltb_spec i j); [|reflexivity]. cbn. symmetry. apply Hb. lia.
Qed.
