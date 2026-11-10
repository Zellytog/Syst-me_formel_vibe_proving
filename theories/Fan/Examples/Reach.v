(** * Accessibilité bornée et extraction du numéral calculé

    Les réduits en un pas d'un terme s'énumèrent ([reducts]) : il y a un
    nombre fini de radicaux, et l'interprétation des oracles est donnée.
    L'ensemble des termes accessibles en au plus s pas est donc une liste
    ([reach]), et « un numéral est accessible en au plus s pas » est
    décidable. Par description constructive (sans axiome), un terme dont on
    sait qu'il se réduit vers *un* numéral donne ce numéral ([eval_num]). *)

From Stdlib Require Import List Arith Lia Bool ConstructiveEpsilon.
Import ListNotations.
From SF.Fan.Examples Require Import Lam Confluence.

Section Reach.

Context {C : Type} (O : C -> option (nat -> bool)).

Local Notation tm := (tm C).

Definition rootapp (a b : tm) : list tm :=
  match a with
  | Lam x => [beta x b]
  | Orc c => match isnum b, O c with Some n, Some f => [num (Nat.b2n (f n))] | _, _ => [] end
  | _ => []
  end.

Fixpoint reducts (t : tm) : list tm :=
  match t with
  | Var _ | Zero | Orc _ => []
  | Lam b => map Lam (reducts b)
  | App a b => rootapp a b ++ map (fun a' => App a' b) (reducts a) ++ map (fun b' => App a b') (reducts b)
  | Pair a b => map (fun a' => Pair a' b) (reducts a) ++ map (fun b' => Pair a b') (reducts b)
  | P1 a => match a with Pair x _ => [x] | _ => [] end ++ map P1 (reducts a)
  | P2 a => match a with Pair _ y => [y] | _ => [] end ++ map P2 (reducts a)
  | Succ a => map Succ (reducts a)
  | Rec a b c =>
      match c with Zero => [a] | Succ v => [App (App b v) (Rec a b v)] | _ => [] end
      ++ map (fun a' => Rec a' b c) (reducts a) ++ map (fun b' => Rec a b' c) (reducts b)
      ++ map (fun c' => Rec a b c') (reducts c)
  end.

Lemma reducts_complete (t u : tm) : step O t u -> In u (reducts t).
Proof.
  induction 1; cbn; try (rewrite isnum_num, H; cbn); rewrite ?in_app_iff, ?in_map_iff;
    try solve [left; reflexivity]; try solve [left; left; reflexivity]; firstorder eauto.
Qed.

Lemma reducts_sound (t u : tm) : In u (reducts t) -> step O t u.
Proof.
  revert u; induction t as [n|b IH|a IHa b IHb|a IHa b IHb|a IH|a IH| |a IH|a IHa b IHb c IHc|c];
    intros u H; cbn in H; rewrite ?in_app_iff, ?in_map_iff in H.
  - contradiction.
  - destruct H as (x & <- & Hx). constructor. apply IH, Hx.
  - destruct H as [H|[(x & <- & Hx)|(x & <- & Hx)]].
    + destruct a; cbn in H; try contradiction.
      * destruct H as [<-|[]]. constructor.
      * destruct (isnum b) eqn:Eb; [destruct (O c) eqn:Ec|]; cbn in H; try contradiction.
        destruct H as [<-|[]]. apply isnum_spec in Eb; subst. constructor. assumption.
    + apply s_appl, IHa, Hx.
    + apply s_appr, IHb, Hx.
  - destruct H as [(x & <- & Hx)|(x & <- & Hx)]; [apply s_pairl, IHa, Hx|apply s_pairr, IHb, Hx].
  - destruct H as [H|(x & <- & Hx)]; [|apply s_p1c, IH, Hx].
    destruct a; cbn in H; try contradiction. destruct H as [<-|[]]. constructor.
  - destruct H as [H|(x & <- & Hx)]; [|apply s_p2c, IH, Hx].
    destruct a; cbn in H; try contradiction. destruct H as [<-|[]]. constructor.
  - contradiction.
  - destruct H as (x & <- & Hx). apply s_succ, IH, Hx.
  - destruct H as [H|[(x & <- & Hx)|[(x & <- & Hx)|(x & <- & Hx)]]].
    + destruct c; cbn in H; try contradiction; destruct H as [<-|[]]; constructor.
    + apply s_rec1, IHa, Hx.
    + apply s_rec2, IHb, Hx.
    + apply s_rec3, IHc, Hx.
  - contradiction.
Qed.

Fixpoint reach (s : nat) (t : tm) : list tm :=
  match s with 0 => [t] | S s => t :: flat_map (reach s) (reducts t) end.

Lemma reach_sound s (t u : tm) : In u (reach s t) -> red O t u.
Proof.
  revert t; induction s; intros t H; cbn in H.
  - destruct H as [<-|[]]. apply r_refl.
  - destruct H as [<-|H]; [apply r_refl|]. apply in_flat_map in H as (x & Hx & Hu).
    eapply r_step; [apply reducts_sound, Hx|]. apply IHs, Hu.
Qed.

Lemma reach_mono s (t u : tm) : In u (reach s t) -> In u (reach (S s) t).
Proof.
  revert t; induction s; intros t H; cbn in *.
  - destruct H as [<-|[]]. left; reflexivity.
  - destruct H as [<-|H]; [left; reflexivity|right]. apply in_flat_map in H as (x & Hx & Hu).
    apply in_flat_map. exists x. split; [exact Hx|]. apply IHs, Hu.
Qed.

Lemma reach_complete (t u : tm) : red O t u -> exists s, In u (reach s t).
Proof.
  induction 1 as [t|t u v H _ (s & Hs)]; [exists 0; left; reflexivity|].
  exists (S s). right. apply in_flat_map. exists u. split; [apply reducts_complete, H|exact Hs].
Qed.

Fixpoint find_num (l : list tm) : option nat :=
  match l with [] => None | t :: l => match isnum t with Some n => Some n | None => find_num l end end.

Lemma find_num_spec l n : find_num l = Some n -> In (num n) l.
Proof.
  induction l as [|t l IH]; cbn; [discriminate|].
  destruct (isnum t) eqn:E; [intros [=<-]; left; symmetry; symmetry; exact (isnum_spec _ _ E)|intros H; right; apply IH, H].
Qed.

Lemma find_num_complete l n : In (num n) l -> exists m, find_num l = Some m.
Proof.
  induction l as [|t l IH]; cbn; [intros []|]. intros [->|H].
  - rewrite isnum_num. eexists; reflexivity.
  - destruct (isnum t); [eexists; reflexivity|apply IH, H].
Qed.

(** Le numéral vers lequel t se réduit, calculé. *)
Definition eval_num (t : tm) (H : exists n, red O t (num n)) : nat.
Proof.
  refine (match find_num (reach (proj1_sig (constructive_indefinite_ground_description_nat
                      (fun s => find_num (reach s t) <> None) _ _)) t) as o
                return find_num (reach _ t) = o -> nat with
          | Some n => fun _ => n
          | None => fun _ => 0
          end eq_refl).
  - intros s. destruct (find_num (reach s t)); [left; discriminate|right; tauto].
  - destruct H as (n & Hn). destruct (reach_complete _ _ Hn) as (s & Hs).
    destruct (find_num_complete _ _ Hs) as (m & Hm). exists s. rewrite Hm. discriminate.
Defined.

Lemma eval_num_spec t H : red O t (num (eval_num t H)).
Proof.
  unfold eval_num.
  destruct (constructive_indefinite_ground_description_nat _ _ _) as (s & Hs). cbn.
  generalize (eq_refl (find_num (reach s t))).
  generalize (find_num (reach s t)) at 2 3 as o. intros o E.
  destruct o as [n|]; [|exfalso; apply Hs, E].
  apply (reach_sound s). apply find_num_spec, E.
Qed.

End Reach.
