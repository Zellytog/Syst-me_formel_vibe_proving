(** * Récursion primitive avec oracles dans un EFdata

    Une fonction (méta) f : X → N est *réalisée* sous le contexte Γ si une
    même évidence envoie Γ(x) sur ⌜f(x)⌝ pour tout x ([RZ]). Les paramètres
    x portent les entrées, les oracles (fonctions, chemins, fonctionnelles)
    sont des hypothèses du contexte. On obtient, à partir de c0, cS, crec :
    les constantes, S, la récursion primitive ([rz_rec]), l'appel d'oracles
    ([rz_call], [rz_call2]), l'abstraction en code de fonction ou de chemin
    ([ent_cfun], [ent_cpath]), puis l'arithmétique nécessaire à la preuve
    de FT, chacune avec sa correction. *)

From Stdlib Require Import Arith Lia.
From SF.Models Require Import PSet Frame.
From SF.Fan Require Import Ent Statement.

Section PR.

Context (E : efdata).

Local Notation Φ := (pcar (fprop E)).
Local Notation "⌜ n ⌝" := (code (e := E) n).

Definition RZ {X : Type} (Γ : X -> Φ) (f : X -> nat) : Prop := ENT Γ (fun x => ⌜f x⌝).

Section Basic.
Context {X : Type} (Γ : X -> Φ).

Lemma rz_ext (f g : X -> nat) : (forall x, f x = g x) -> RZ Γ f -> RZ Γ g.
Proof. intros H. apply ent_eq_r. intros x. rewrite H. apply peq_refl. Qed.

Lemma rz_zero : RZ Γ (fun _ => 0).
Proof.
  eapply ent_trans; [apply ent_top|]. destruct (c0 E) as [e He]. exists e. intros _. exact He.
Qed.

Lemma rz_succ f : RZ Γ f -> RZ Γ (fun x => S (f x)).
Proof. intros H. eapply ent_trans; [exact H|]. destruct (cS E) as [e He]. exists e. intros x. apply He. Qed.

Lemma rz_const n : RZ Γ (fun _ => n).
Proof. induction n as [|n IH]; [apply rz_zero|apply rz_succ, IH]. Qed.

End Basic.

(** Le contexte d'un pas de récursion : Γ(x), ⌜k⌝, ⌜acc⌝. *)
Definition sctx {X} (Γ : X -> Φ) (p : X * nat * nat) : Φ :=
  fand (fand (Γ (fst (fst p))) ⌜snd (fst p)⌝) ⌜snd p⌝.

Definition prec {X} (z : X -> nat) (s : X -> nat -> nat -> nat) (x : X) (k : nat) : nat :=
  nat_rect (fun _ => nat) (z x) (fun k acc => s x k acc) k.

Lemma rz_rec {X} (Γ : X -> Φ) (m z : X -> nat) (s : X -> nat -> nat -> nat) :
  RZ Γ m -> RZ Γ z ->
  RZ (sctx Γ) (fun p => s (fst (fst p)) (snd (fst p)) (snd p)) ->
  RZ Γ (fun x => prec z s x (m x)).
Proof.
  intros Hm Hz Hs.
  set (fam := fun x k => fimp (Γ x) ⌜prec z s x k⌝).
  set (STEP := fun x => fall (fun n => fimp ⌜n⌝ (fimp (fam x n) (fam x (S n))))).
  assert (Hr : ENT Γ (fun x => fimp (fam x 0) (fimp (STEP x) (fall (fun n => fimp ⌜n⌝ (fam x n)))))).
  { destruct (crec E) as [e He]. exists (e_comp e_top e). intros x. eapply f_comp; [apply f_top|]. exact (He (fam x)). }
  assert (H0 : ENT Γ (fun x => fam x 0)).
  { unfold fam. apply ent_lam. eapply ent_trans; [apply ent_snd|exact Hz]. }
  assert (HS : ENT Γ STEP).
  { unfold STEP. apply (ent_gen (I := nat)). apply ent_lam. apply ent_lam. unfold fam at 2. apply ent_lam.
    set (c := fun p : X * nat =>
                fand (fand (fand (Γ (fst p)) ⌜snd p⌝) (fam (fst p) (snd p))) (Γ (fst p))).
    change (ENT c (fun p => ⌜s (fst p) (snd p) (prec z s (fst p) (snd p))⌝)).
    assert (Hc : ENT c (fun p => sctx Γ (fst p, snd p, prec z s (fst p) (snd p)))).
    { unfold sctx; cbn [fst snd]. apply ent_pair; [apply ent_pair|].
      - apply ent_snd.
      - eapply ent_trans; [apply ent_fst|]. eapply ent_trans; [apply ent_fst|]. apply ent_snd.
      - eapply ent_app; [|apply ent_snd].
        eapply ent_trans; [apply ent_fst|]. apply ent_snd. }
    eapply ent_trans; [exact Hc|].
    exact (ent_reindex (fun p : X * nat => (fst p, snd p, prec z s (fst p) (snd p))) _ _ Hs). }
  pose proof (ent_app _ _ _ (ent_app _ _ _ Hr H0) HS) as K.
  pose proof (ent_inst _ _ m K) as K'. cbn beta in K'.
  pose proof (ent_app _ _ _ K' Hm) as K''. unfold fam in K''.
  exact (ent_app _ _ _ K'' (ent_refl Γ)).
Qed.

(** ** Oracles *)

Section Oracles.
Context {X : Type} (Γ : X -> Φ).

Lemma rz_call (g : X -> nat -> nat) (a : X -> nat) :
  ENT Γ (fun x => cfun E (g x)) -> RZ Γ a -> RZ Γ (fun x => g x (a x)).
Proof.
  intros Hg Ha. unfold cfun in Hg.
  exact (ent_app _ _ _ (ent_inst _ _ a Hg) Ha).
Qed.

Lemma rz_call2 (G : X -> (nat -> bool) -> nat) (β : X -> nat -> bool) :
  ENT Γ (fun x => cfun2 E (G x)) -> ENT Γ (fun x => cpath E (β x)) -> RZ Γ (fun x => G x (β x)).
Proof.
  intros HG Hb. unfold cfun2 in HG.
  exact (ent_app _ _ _ (ent_inst _ _ β HG) Hb).
Qed.

Lemma ent_cfun (g : X -> nat -> nat) :
  RZ (fun p : X * nat => fand (Γ (fst p)) ⌜snd p⌝) (fun p => g (fst p) (snd p)) ->
  ENT Γ (fun x => cfun E (g x)).
Proof. intros H. unfold cfun. apply (ent_gen (I := nat)). apply ent_lam. exact H. Qed.

Lemma ent_cpath (β : X -> nat -> bool) :
  RZ (fun p : X * nat => fand (Γ (fst p)) ⌜snd p⌝) (fun p => Nat.b2n (β (fst p) (snd p))) ->
  ENT Γ (fun x => cpath E (β x)).
Proof. intros H. apply ent_cfun. exact H. Qed.

End Oracles.

(** Réaliser une fonction des paramètres dans le contexte d'un pas. *)
Lemma rz_up {X} (Γ : X -> Φ) (f : X -> nat) : RZ Γ f -> RZ (sctx Γ) (fun p => f (fst (fst p))).
Proof.
  intros H. eapply ent_trans; [|exact (ent_reindex (fun p : X * nat * nat => fst (fst p)) _ _ H)].
  eapply ent_trans; [apply ent_fst|apply ent_fst].
Qed.

Lemma rz_k {X} (Γ : X -> Φ) : RZ (sctx Γ) (fun p => snd (fst p)).
Proof. eapply ent_trans; [apply ent_fst|apply ent_snd]. Qed.

Lemma rz_acc {X} (Γ : X -> Φ) : RZ (sctx Γ) (fun p => snd p).
Proof. apply ent_snd. Qed.

(** Un réalisateur sous Γ ∧ ⌜k⌝, vu dans le contexte d'un pas. *)
Lemma rz_up_k {X} (Γ : X -> Φ) (P : X -> nat -> nat) :
  RZ (fun p : X * nat => fand (Γ (fst p)) ⌜snd p⌝) (fun p => P (fst p) (snd p)) ->
  RZ (sctx Γ) (fun p => P (fst (fst p)) (snd (fst p))).
Proof.
  intros H. eapply ent_trans; [|exact (ent_reindex (fun p : X * nat * nat => fst p) _ _ H)].
  apply ent_fst.
Qed.

(** ** Arithmétique *)

Lemma rz_add {X} (Γ : X -> Φ) a b : RZ Γ a -> RZ Γ b -> RZ Γ (fun x => a x + b x).
Proof.
  intros Ha Hb.
  eapply rz_ext; [|exact (rz_rec Γ b a (fun _ _ acc => S acc) Hb Ha (rz_succ _ _ (rz_acc Γ)))].
  intros x. unfold prec. induction (b x) as [|k IH]; cbn; lia.
Qed.

Lemma rz_pred {X} (Γ : X -> Φ) a : RZ Γ a -> RZ Γ (fun x => pred (a x)).
Proof.
  intros Ha.
  eapply rz_ext; [|exact (rz_rec Γ a (fun _ => 0) (fun _ k _ => k) Ha (rz_zero _) (rz_k Γ))].
  intros x. unfold prec. destruct (a x); reflexivity.
Qed.

Lemma rz_sub {X} (Γ : X -> Φ) a b : RZ Γ a -> RZ Γ b -> RZ Γ (fun x => a x - b x).
Proof.
  intros Ha Hb.
  eapply rz_ext; [|exact (rz_rec Γ b a (fun _ _ acc => pred acc) Hb Ha (rz_pred _ _ (rz_acc Γ)))].
  intros x. unfold prec. induction (b x) as [|k IH]; cbn; [lia|]. rewrite IH. lia.
Qed.

Lemma rz_mul {X} (Γ : X -> Φ) a b : RZ Γ a -> RZ Γ b -> RZ Γ (fun x => a x * b x).
Proof.
  intros Ha Hb.
  eapply rz_ext; [|exact (rz_rec Γ b (fun _ => 0) (fun x _ acc => acc + a x) Hb (rz_zero _)
                            (rz_add _ _ _ (rz_acc Γ) (rz_up Γ a Ha)))].
  intros x. unfold prec. induction (b x) as [|k IH]; cbn; [lia|]. rewrite IH. lia.
Qed.

Lemma rz_isz {X} (Γ : X -> Φ) a : RZ Γ a -> RZ Γ (fun x => Nat.b2n (a x =? 0)).
Proof.
  intros Ha.
  eapply rz_ext; [|exact (rz_rec Γ a (fun _ => 1) (fun _ _ _ => 0) Ha (rz_const _ _) (rz_zero _))].
  intros x. unfold prec. destruct (a x); reflexivity.
Qed.

Lemma rz_leb {X} (Γ : X -> Φ) a b : RZ Γ a -> RZ Γ b -> RZ Γ (fun x => Nat.b2n (a x <=? b x)).
Proof.
  intros Ha Hb. eapply rz_ext; [|exact (rz_isz _ _ (rz_sub _ _ _ Ha Hb))].
  intros x. f_equal. destruct (Nat.leb_spec (a x) (b x)), (Nat.eqb_spec (a x - b x) 0); try reflexivity; lia.
Qed.

Lemma rz_ltb {X} (Γ : X -> Φ) a b : RZ Γ a -> RZ Γ b -> RZ Γ (fun x => Nat.b2n (a x <? b x)).
Proof. intros Ha Hb. exact (rz_leb _ _ _ (rz_succ _ _ Ha) Hb). Qed.

Lemma rz_odd {X} (Γ : X -> Φ) a : RZ Γ a -> RZ Γ (fun x => Nat.b2n (Nat.odd (a x))).
Proof.
  intros Ha.
  eapply rz_ext; [|exact (rz_rec Γ a (fun _ => 0) (fun _ _ acc => 1 - acc) Ha (rz_zero _)
                            (rz_sub _ _ _ (rz_const _ 1) (rz_acc Γ)))].
  intros x. unfold prec. induction (a x) as [|k IH]; [reflexivity|]. cbn [nat_rect]. rewrite IH.
  rewrite Nat.odd_succ, <- Nat.negb_odd. destruct (Nat.odd k); reflexivity.
Qed.

Lemma div2_succ n : Nat.div2 (S n) = Nat.div2 n + Nat.b2n (Nat.odd n).
Proof.
  pose proof (Nat.div2_odd n) as E1. pose proof (Nat.div2_odd (S n)) as E2.
  rewrite Nat.odd_succ, <- Nat.negb_odd in E2. destruct (Nat.odd n); cbn [negb Nat.b2n] in *; lia.
Qed.

Lemma rz_div2 {X} (Γ : X -> Φ) a : RZ Γ a -> RZ Γ (fun x => Nat.div2 (a x)).
Proof.
  intros Ha.
  eapply rz_ext; [|exact (rz_rec Γ a (fun _ => 0) (fun _ k acc => acc + Nat.b2n (Nat.odd k)) Ha (rz_zero _)
                            (rz_add _ _ _ (rz_acc Γ) (rz_odd _ _ (rz_k Γ))))].
  intros x. unfold prec. induction (a x) as [|k IH]; [reflexivity|]. cbn [nat_rect]. rewrite IH.
  symmetry; apply div2_succ.
Qed.

Lemma testbit_iter k i : Nat.testbit k i = Nat.odd (nat_rect (fun _ => nat) k (fun _ acc => Nat.div2 acc) i).
Proof.
  revert k. induction i as [|i IH]; intros k; [reflexivity|].
  cbn [Nat.testbit nat_rect]. rewrite IH. f_equal. clear IH.
  induction i as [|i IH]; [reflexivity|]. cbn [nat_rect]. rewrite IH. reflexivity.
Qed.

Lemma rz_testbit {X} (Γ : X -> Φ) a b : RZ Γ a -> RZ Γ b -> RZ Γ (fun x => Nat.b2n (Nat.testbit (a x) (b x))).
Proof.
  intros Ha Hb.
  pose proof (rz_rec Γ b a (fun _ _ acc => Nat.div2 acc) Hb Ha (rz_div2 _ _ (rz_acc Γ))) as K.
  eapply rz_ext; [|exact (rz_odd _ _ K)]. intros x. unfold prec. rewrite testbit_iter. reflexivity.
Qed.

Lemma rz_pow2 {X} (Γ : X -> Φ) a : RZ Γ a -> RZ Γ (fun x => 2 ^ a x).
Proof.
  intros Ha.
  eapply rz_ext; [|exact (rz_rec Γ a (fun _ => 1) (fun _ _ acc => acc + acc) Ha (rz_const _ 1)
                            (rz_add _ _ _ (rz_acc Γ) (rz_acc Γ)))].
  intros x. unfold prec. induction (a x) as [|k IH]; [reflexivity|]. cbn [nat_rect]. rewrite IH.
  rewrite Nat.pow_succ_r'. lia.
Qed.

Lemma rz_band {X} (Γ : X -> Φ) a b : RZ Γ (fun x => Nat.b2n (a x)) -> RZ Γ (fun x => Nat.b2n (b x)) ->
  RZ Γ (fun x => Nat.b2n (a x && b x)).
Proof.
  intros Ha Hb. eapply rz_ext; [|exact (rz_mul _ _ _ Ha Hb)].
  intros x. cbv beta. destruct (a x), (b x); reflexivity.
Qed.

(** ** Quantificateurs bornés et recherche bornée *)

(** Un prédicat booléen des paramètres et d'un entier k, réalisé sous Γ ∧ ⌜k⌝. *)
Definition RZP {X} (Γ : X -> Φ) (P : X -> nat -> bool) : Prop :=
  RZ (fun p : X * nat => fand (Γ (fst p)) ⌜snd p⌝) (fun p => Nat.b2n (P (fst p) (snd p))).

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

Section Bounded.
Context {X : Type} (Γ : X -> Φ).

Lemma rz_ball (N : X -> nat) P : RZ Γ N -> RZP Γ P -> RZ Γ (fun x => Nat.b2n (ball (N x) (P x))).
Proof.
  intros HN HP.
  eapply rz_ext; [|exact (rz_rec Γ N (fun _ => 1) (fun x k acc => acc * Nat.b2n (P x k)) HN (rz_const _ 1)
                            (rz_mul _ _ _ (rz_acc Γ) (rz_up_k Γ (fun x k => Nat.b2n (P x k)) HP)))].
  intros x. unfold prec. induction (N x) as [|k IH]; [reflexivity|]. cbn [nat_rect ball]. rewrite IH.
  destruct (ball k (P x)), (P x k); reflexivity.
Qed.

Lemma rz_bex (N : X -> nat) P : RZ Γ N -> RZP Γ P -> RZ Γ (fun x => Nat.b2n (bex (N x) (P x))).
Proof.
  intros HN HP.
  (* acc ∨ b = acc + b - acc·b *)
  eapply rz_ext; [|exact (rz_rec Γ N (fun _ => 0) (fun x k acc => acc + Nat.b2n (P x k) - acc * Nat.b2n (P x k))
                            HN (rz_zero _)
                            (rz_sub _ _ _ (rz_add _ _ _ (rz_acc Γ) (rz_up_k Γ (fun x k => Nat.b2n (P x k)) HP))
                                    (rz_mul _ _ _ (rz_acc Γ) (rz_up_k Γ (fun x k => Nat.b2n (P x k)) HP))))].
  intros x. unfold prec. induction (N x) as [|k IH]; [reflexivity|]. cbn [nat_rect bex]. rewrite IH.
  destruct (bex k (P x)), (P x k); reflexivity.
Qed.

(** La dernière position k < N où P vaut vrai (0 s'il n'y en a pas). *)
Fixpoint blast (N : nat) (P : nat -> bool) : nat :=
  match N with 0 => 0 | S k => if P k then k else blast k P end.

Lemma blast_spec N P : (exists k, k < N /\ P k = true) -> blast N P < N /\ P (blast N P) = true.
Proof.
  induction N as [|N IH]; intros (k & Hk & H); [lia|]. cbn.
  destruct (P N) eqn:EN; [split; [lia|exact EN]|].
  destruct (Nat.eq_dec k N) as [->|Hne]; [congruence|].
  destruct IH as [H1 H2]; [exists k; split; [lia|exact H]|]. split; [lia|exact H2].
Qed.

Lemma rz_blast (N : X -> nat) P : RZ Γ N -> RZP Γ P -> RZ Γ (fun x => blast (N x) (P x)).
Proof.
  intros HN HP.
  (* if b then k else acc = b·k + (1 - b)·acc *)
  eapply rz_ext; [|exact (rz_rec Γ N (fun _ => 0)
                            (fun x k acc => Nat.b2n (P x k) * k + (1 - Nat.b2n (P x k)) * acc)
                            HN (rz_zero _)
                            (rz_add _ _ _ (rz_mul _ _ _ (rz_up_k Γ (fun x k => Nat.b2n (P x k)) HP) (rz_k Γ))
                                    (rz_mul _ _ _ (rz_sub _ _ _ (rz_const _ 1) (rz_up_k Γ (fun x k => Nat.b2n (P x k)) HP)) (rz_acc Γ))))].
  intros x. unfold prec. induction (N x) as [|k IH]; [reflexivity|]. cbn [nat_rect blast]. rewrite IH.
  destruct (P x k); cbn; lia.
Qed.

End Bounded.

End PR.
