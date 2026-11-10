(** * V(E) : les constructions

    ∅, {a, b}, ⋃a, {α ε a | φ}, P(x) (faible) et ω. Chacune est donnée par
    sa forme, qui ne dépend que des formes des arguments, et par ses
    étiquettes ; d'où la compatibilité avec l'égalité. Les étiquettes de la
    paire et de ω sont des **booléens de Church** (correction A.7), qui
    permettent de choisir uniformément la branche d'une disjonction. *)

From SF.Models Require Import PSet Frame FrameModel.
From SF.VE Require Import Trees Base.

Section Cons.

Context (F : frame).
(** Φ est essentiellement petit : P(x) est indexé par les fonctions vers Φ₀. *)
Context (Φ0 : Type) (enc : pcar F -> Φ0) (dec : Φ0 -> pcar F).

Local Notation V := (V F).
Local Notation lab := (lab F).
Local Notation idx := (idx F).
Local Notation lbl := (lbl F).
Local Notation sub := (sub F).
Local Notation labS := (labS F).

Definition mkS (T : Type) (sh : T -> shape) (lb : forall t, (pcar F * lab (sh t))%type) : V :=
  existT _ (node T sh) lb.

(** Changer les étiquettes d'un ensemble : ψₜ devient g(t) ∧ ψₜ. *)
Definition rel (s : shape) : lab s -> (idxS s -> pcar F) -> lab s :=
  match s as s0 return lab s0 -> (idxS s0 -> pcar F) -> lab s0 with
  | node T k => fun l g t => (fand (g t) (fst (l t)), snd (l t))
  end.

Lemma rel_proper s l l' g g' : leq F s l l' -> (forall t, g t ≡ g' t) -> leq F s (rel s l g) (rel s l' g').
Proof.
  destruct s as [T k]; intros H Hg t. destruct (H t) as [H1 H2]. split; [apply fand_proper; auto|exact H2].
Qed.

Lemma lbl_rel s l g t : lbl (existT _ s (rel s l g)) t = fand (g t) (lbl (existT _ s l) t).
Proof. destruct s; reflexivity. Qed.

Lemma sub_rel s l g t : teq F (sub (existT _ s (rel s l g)) t) (sub (existT _ s l) t).
Proof. destruct s as [T k]. exists eq_refl. apply leq_refl. Qed.

(** *** Les booléens de Church *)

Definition tagT : pcar F := fall (fun φ : pcar F => fall (fun ψ : pcar F => fimp φ (fimp ψ φ))).
Definition tagF : pcar F := fall (fun φ : pcar F => fall (fun ψ : pcar F => fimp φ (fimp ψ ψ))).

(** *** ∅, la paire, la réunion *)

Definition vempty : V := mkS Empty_set (fun e => match e with end) (fun e => match e with end).

Definition vpair (a b : V) : V :=
  mkS bool (fun c => if c then projT1 a else projT1 b)
      (fun c => match c as c0 return (pcar F * lab (if c0 then projT1 a else projT1 b))%type with
                | true => (tagT, projT2 a)
                | false => (tagF, projT2 b)
                end).

Lemma vpair_proper a a' b b' : teq F a a' -> teq F b b' -> teq F (vpair a b) (vpair a' b').
Proof.
  destruct a as [s l], a' as [s' l'], b as [r m], b' as [r' m']. intros [E H] [E' H']; cbn in *. destruct E, E'.
  exists eq_refl. intros [|]; (split; [apply peq_refl|]); assumption.
Qed.

Definition vunion (a : V) : V :=
  mkS { t : idxS (projT1 a) & idxS (subS (projT1 a) t) }
      (fun p => subS (subS (projT1 a) (projT1 p)) (projT2 p))
      (fun p => (fand (fst (labS (projT1 a) (projT2 a) (projT1 p)))
                      (fst (labS _ (snd (labS (projT1 a) (projT2 a) (projT1 p))) (projT2 p))),
                 snd (labS _ (snd (labS (projT1 a) (projT2 a) (projT1 p))) (projT2 p)))).

Lemma vunion_proper a a' : teq F a a' -> teq F (vunion a) (vunion a').
Proof.
  destruct a as [s l], a' as [s' l']. intros [E H]; cbn in *. destruct E.
  exists eq_refl. intros [t u]; cbn.
  destruct (leq_lab F s l l' H t) as [H1 H2]. destruct (leq_lab F _ _ _ H2 u) as [H3 H4].
  split; [apply fand_proper; assumption|exact H4].
Qed.

(** *** Séparation : {α ε a | φ}, les étiquettes devenant φ(α) ∧ ψ. *)

Definition vsep (a : V) (φ : pmor (Vset F) F) : V :=
  existT _ (projT1 a) (rel (projT1 a) (projT2 a) (fun t => φ (sub a t))).

Lemma vsep_proper a a' (φ φ' : pmor (Vset F) F) :
  teq F a a' -> (forall z, φ z ≡ φ' z) -> teq F (vsep a φ) (vsep a' φ').
Proof.
  destruct a as [s l], a' as [s' l']. intros [E H] Hφ; cbn in *. destruct E.
  exists eq_refl. cbn. apply rel_proper; [exact H|]. intros t.
  eapply peq_trans; [apply Hφ|]. apply pfun_proper. exact (proj2 (teq_br F s l l' t H)).
Qed.

(** *** Parties (faible) : P(x) ≜ {(⊤, b_g) | g : x → Φ₀}, b_g ≜ {(g(t) ∧ ψₜ, xₜ)}. *)

Definition bsub (x : V) (g : idx x -> Φ0) : V := existT _ (projT1 x) (rel (projT1 x) (projT2 x) (fun t => dec (g t))).

Definition vpower (x : V) : V :=
  mkS (idx x -> Φ0) (fun _ => projT1 x) (fun g => (ftop, rel (projT1 x) (projT2 x) (fun t => dec (g t)))).

Lemma vpower_proper x x' : teq F x x' -> teq F (vpower x) (vpower x').
Proof.
  destruct x as [s l], x' as [s' l']. intros [E H]; cbn in *. destruct E.
  exists eq_refl. intros g. split; [apply peq_refl|]. apply rel_proper; [exact H|]. intros; apply peq_refl.
Qed.

Lemma sub_power x g : teq F (sub (vpower x) g) (bsub x g).
Proof. apply teq_refl. Qed.

(** *** ω : sₙ ≜ Sⁿ(∅), S(b) ≜ ⋃{b, {b, b}}, étiquettes p₀ ≜ tag₀ ∧ ⊤, pₙ₊₁ ≜ tag_S ∧ pₙ. *)

Definition vsuc (b : V) : V := vunion (vpair b (vpair b b)).

Lemma vsuc_proper b b' : teq F b b' -> teq F (vsuc b) (vsuc b').
Proof. intros H. apply vunion_proper, vpair_proper; [exact H|apply vpair_proper; exact H]. Qed.

Fixpoint snat (n : nat) : V := match n with O => vempty | S m => vsuc (snat m) end.
Fixpoint pnat (n : nat) : pcar F := match n with O => fand tagT ftop | S m => fand tagF (pnat m) end.

Definition vomega : V := mkS nat (fun n => projT1 (snat n)) (fun n => (pnat n, projT2 (snat n))).

End Cons.
