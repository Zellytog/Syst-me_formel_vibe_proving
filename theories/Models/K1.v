(** * K1 : la PCA de Kleene sur ℕ

    Les réalisateurs sont des entiers, codes de programmes d'un petit
    langage universel ; a·b ↓ c signifie : le programme de code a, sur
    l'entrée b, s'arrête avec la sortie c.

    Le langage (une seule variable d'entrée x) :
    - [x], les constantes n, les couples ⟨e₁, e₂⟩ et leurs projections
      (couplage de Cantor de la Stdlib) ;
    - le successeur et un test à zéro paresseux ;
    - l'**appel universel** e₁ · e₂ : exécuter le programme de code e₁ sur
      la valeur de e₂.

    Tout entier est un code (un étiquetage invalide ne termine pas), et
    l'évaluation est une fonction Rocq à carburant ([eval]) : l'application
    est donc semi-décidable, calculée par un interprète écrit une fois pour
    toutes. On ne prouve pas l'équivalence avec les fonctions
    μ-récursives ; l'appel universel rend la combinatoire immédiate : K et
    S sont des programmes qui fabriquent des codes, et s2 a b est le
    programme « (a x) (b x) ».

    L'application est déterministe ([ap_det]) : K1 est une PCA au sens
    strict. *)

From Stdlib Require Import Arith Lia Cantor.
From SF.Models Require Import PCA.

(** ** Codes *)

Definition pair (a b : nat) : nat := Cantor.to_nat (a, b).
Definition unpair (n : nat) : nat * nat := Cantor.of_nat n.

Lemma unpair_pair a b : unpair (pair a b) = (a, b).
Proof. apply Cantor.cancel_of_to. Qed.

Definition cVar : nat := pair 0 0.
Definition cConst (m : nat) : nat := pair 1 m.
Definition cPair (a b : nat) : nat := pair 2 (pair a b).
Definition cFst (a : nat) : nat := pair 3 a.
Definition cSnd (a : nat) : nat := pair 4 a.
Definition cApp (a b : nat) : nat := pair 5 (pair a b).
Definition cSucc (a : nat) : nat := pair 6 a.
Definition cIfz (c a b : nat) : nat := pair 7 (pair c (pair a b)).

(** ** L'interprète, à carburant *)

Fixpoint eval (n c x : nat) {struct n} : option nat :=
  match n with
  | 0 => None
  | S n =>
    let (t, r) := unpair c in
    match t with
    | 0 => Some x
    | 1 => Some r
    | 2 => let (a, b) := unpair r in
           match eval n a x with
           | Some v1 => match eval n b x with Some v2 => Some (pair v1 v2) | None => None end
           | None => None
           end
    | 3 => match eval n r x with Some v => Some (fst (unpair v)) | None => None end
    | 4 => match eval n r x with Some v => Some (snd (unpair v)) | None => None end
    | 5 => let (a, b) := unpair r in
           match eval n a x with
           | Some f => match eval n b x with Some v => eval n f v | None => None end
           | None => None
           end
    | 6 => match eval n r x with Some v => Some (S v) | None => None end
    | 7 => let (c0, rest) := unpair r in
           let (a, b) := unpair rest in
           match eval n c0 x with
           | Some 0 => eval n a x
           | Some (S _) => eval n b x
           | None => None
           end
    | _ => None
    end
  end.

Lemma eval_var n x : eval (S n) cVar x = Some x.
Proof. cbn [eval]. unfold cVar. rewrite unpair_pair. reflexivity. Qed.

Lemma eval_const n m x : eval (S n) (cConst m) x = Some m.
Proof. cbn [eval]. unfold cConst. rewrite unpair_pair. reflexivity. Qed.

Lemma eval_pair n a b x :
  eval (S n) (cPair a b) x =
  match eval n a x with
  | Some v1 => match eval n b x with Some v2 => Some (pair v1 v2) | None => None end
  | None => None
  end.
Proof. cbn [eval]. unfold cPair. rewrite !unpair_pair. reflexivity. Qed.

Lemma eval_app n a b x :
  eval (S n) (cApp a b) x =
  match eval n a x with
  | Some f => match eval n b x with Some v => eval n f v | None => None end
  | None => None
  end.
Proof. cbn [eval]. unfold cApp. rewrite !unpair_pair. reflexivity. Qed.

(** Plus de carburant ne change pas un résultat obtenu. *)
Lemma eval_mono n m c x v : n <= m -> eval n c x = Some v -> eval m c x = Some v.
Proof.
  revert m c x v. induction n as [|n IH]; intros m c x v Hle H; [discriminate|].
  destruct m as [|m]; [lia|]. assert (Hnm : n <= m) by lia.
  cbn [eval] in H |- *. destruct (unpair c) as [t r].
  destruct t as [|[|[|[|[|[|[|[|t]]]]]]]]; try exact H.
  - destruct (unpair r) as [a b].
    destruct (eval n a x) as [v1|] eqn:E1; [|discriminate].
    destruct (eval n b x) as [v2|] eqn:E2; [|discriminate].
    rewrite (IH m a x v1 Hnm E1), (IH m b x v2 Hnm E2). exact H.
  - destruct (eval n r x) as [w|] eqn:E; [|discriminate]. rewrite (IH m r x w Hnm E). exact H.
  - destruct (eval n r x) as [w|] eqn:E; [|discriminate]. rewrite (IH m r x w Hnm E). exact H.
  - destruct (unpair r) as [a b].
    destruct (eval n a x) as [f|] eqn:E1; [|discriminate].
    destruct (eval n b x) as [w|] eqn:E2; [|discriminate].
    rewrite (IH m a x f Hnm E1), (IH m b x w Hnm E2). exact (IH m f w v Hnm H).
  - destruct (eval n r x) as [w|] eqn:E; [|discriminate]. rewrite (IH m r x w Hnm E). exact H.
  - destruct (unpair r) as [c0 rest]. destruct (unpair rest) as [a b].
    destruct (eval n c0 x) as [[|k]|] eqn:E; [| |discriminate];
      rewrite (IH m c0 x _ Hnm E); exact (IH m _ x v Hnm H).
Qed.

(** ** L'application *)

Definition kap (a b c : nat) : Prop := exists n, eval n a b = Some c.

Lemma ap_det a b c c' : kap a b c -> kap a b c' -> c = c'.
Proof.
  intros [n H] [n' H'].
  pose proof (eval_mono n (n + n') a b c ltac:(lia) H) as E.
  pose proof (eval_mono n' (n + n') a b c' ltac:(lia) H') as E'.
  congruence.
Qed.

(** ** Gabarits : des programmes qui fabriquent des codes *)

Inductive tpl : Type :=
| TVar
| TConst (n : nat)
| TPair (t1 t2 : tpl).

Fixpoint tcode (t : tpl) : nat :=
  match t with
  | TVar => cVar
  | TConst n => cConst n
  | TPair t1 t2 => cPair (tcode t1) (tcode t2)
  end.

Fixpoint tval (x : nat) (t : tpl) : nat :=
  match t with
  | TVar => x
  | TConst n => n
  | TPair t1 t2 => pair (tval x t1) (tval x t2)
  end.

Fixpoint tdepth (t : tpl) : nat :=
  match t with
  | TVar | TConst _ => 1
  | TPair t1 t2 => S (Nat.max (tdepth t1) (tdepth t2))
  end.

Lemma tcode_eval t n x : tdepth t <= n -> eval n (tcode t) x = Some (tval x t).
Proof.
  revert n. induction t as [| m | t1 IH1 t2 IH2]; intros n Hn; destruct n as [|n]; cbn in Hn; try lia.
  - apply eval_var.
  - apply eval_const.
  - cbn [tcode tval]. rewrite eval_pair, (IH1 n ltac:(lia)), (IH2 n ltac:(lia)). reflexivity.
Qed.

Lemma tcode_ap t x : kap (tcode t) x (tval x t).
Proof. exists (tdepth t). apply tcode_eval. lia. Qed.

(** ** K et S *)

Definition k1v (a : nat) : nat := cConst a.
Definition s2v (a b : nat) : nat := cApp (cApp (cConst a) cVar) (cApp (cConst b) cVar).

(** s1 a : sur b, rend le code s2 a b. *)
Definition Ts1 (a : nat) : tpl :=
  TPair (TConst 5) (TPair (TConst (cApp (cConst a) cVar))
                          (TPair (TConst 5) (TPair (TPair (TConst 1) TVar) (TConst cVar)))).
Definition s1v (a : nat) : nat := tcode (Ts1 a).

(** K : sur a, rend le code de la constante a. *)
Definition TK : tpl := TPair (TConst 1) TVar.

(** S : sur a, rend le code s1 a. *)
Definition REST : nat := cPair (cConst 5) (cPair (cPair (cConst 1) cVar) (cConst cVar)).
Definition TS : tpl :=
  TPair (TConst 2) (TPair (TConst (cConst 5))
    (TPair (TConst 2) (TPair (TPair (TConst 1) (TPair (TConst 5) (TPair (TPair (TConst 1) TVar) (TConst cVar))))
                             (TConst REST)))).

Lemma kap_K a : kap (tcode TK) a (k1v a).
Proof. exact (tcode_ap TK a). Qed.

Lemma kap_K1 a b : kap (k1v a) b a.
Proof. exists 1. apply eval_const. Qed.

Lemma kap_S a : kap (tcode TS) a (s1v a).
Proof. exact (tcode_ap TS a). Qed.

Lemma kap_S1 a b : kap (s1v a) b (s2v a b).
Proof. exact (tcode_ap (Ts1 a) b). Qed.

Lemma kap_S2 a b c u w v : kap a c u -> kap b c w -> kap u w v -> kap (s2v a b) c v.
Proof.
  intros [n1 H1] [n2 H2] [n3 H3]. set (N := n1 + n2 + n3).
  exists (S (S (S N))). unfold s2v. rewrite eval_app, !eval_app, !eval_const, !eval_var.
  rewrite (eval_mono n1 (S N) a c u ltac:(lia) H1), (eval_mono n2 (S N) b c w ltac:(lia) H2).
  exact (eval_mono n3 (S (S N)) u w v ltac:(lia) H3).
Qed.

Definition K1 : pca := {|
  pc := nat;
  ap := kap;
  cK := tcode TK; cS := tcode TS;
  k1 := k1v; s1 := s1v; s2 := s2v;
  ap_K := kap_K; ap_K1 := kap_K1;
  ap_S := kap_S; ap_S1 := kap_S1; ap_S2 := kap_S2
|}.

(** Les autres primitives, pour programmer sur les entiers. *)

Lemma eval_succ n a x :
  eval (S n) (cSucc a) x = match eval n a x with Some v => Some (S v) | None => None end.
Proof. cbn [eval]. unfold cSucc. rewrite unpair_pair. reflexivity. Qed.

Lemma eval_ifz n c a b x :
  eval (S n) (cIfz c a b) x =
  match eval n c x with Some 0 => eval n a x | Some (S _) => eval n b x | None => None end.
Proof. cbn [eval]. unfold cIfz. rewrite !unpair_pair. reflexivity. Qed.

Lemma eval_fst n a x :
  eval (S n) (cFst a) x = match eval n a x with Some v => Some (fst (unpair v)) | None => None end.
Proof. cbn [eval]. unfold cFst. rewrite unpair_pair. reflexivity. Qed.

Lemma eval_snd n a x :
  eval (S n) (cSnd a) x = match eval n a x with Some v => Some (snd (unpair v)) | None => None end.
Proof. cbn [eval]. unfold cSnd. rewrite unpair_pair. reflexivity. Qed.
