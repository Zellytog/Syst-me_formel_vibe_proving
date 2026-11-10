(** * V(E) : les ensembles comme arbres d'Aczel étiquetés

    Un ensemble est un couple (forme, étiquettes) : la forme est un arbre
    d'Aczel nu (une famille de sous-formes indexée par un type), les
    étiquettes une proposition de Φ par branche, récursivement. Deux
    ensembles sont égaux s'ils ont la **même forme** (égalité de Leibniz)
    et des étiquettes ≡ ; c'est ce qui rend compatibles avec l'égalité
    les interprétations de ε (un ⋁ indexé par les branches) et des
    constructions (réunion, parties, séparation), sans extensionnalité. *)

From SF.Models Require Import PSet Frame FrameModel.

Inductive shape : Type := node (T : Type) (k : T -> shape).

Section Trees.

Context (F : frame).

Fixpoint lab (s : shape) : Type :=
  match s with node T k => forall t : T, (pcar F * lab (k t))%type end.

Definition V : Type := { s : shape & lab s }.

Fixpoint leq (s : shape) : lab s -> lab s -> Prop :=
  match s as s0 return lab s0 -> lab s0 -> Prop with
  | node T k => fun l l' => forall t, fst (l t) ≡ fst (l' t) /\ leq (k t) (snd (l t)) (snd (l' t))
  end.

Lemma leq_refl s : forall l, leq s l l.
Proof. induction s as [T k IH]; intros l t. split; [apply peq_refl|apply IH]. Qed.

Lemma leq_sym s : forall l l', leq s l l' -> leq s l' l.
Proof.
  induction s as [T k IH]; intros l l' H t. destruct (H t) as [H1 H2].
  split; [apply peq_sym, H1|apply IH, H2].
Qed.

Lemma leq_trans s : forall l l' l'', leq s l l' -> leq s l' l'' -> leq s l l''.
Proof.
  induction s as [T k IH]; intros l l' l'' H H' t. destruct (H t) as [H1 H2], (H' t) as [H1' H2'].
  split; [eapply peq_trans; eassumption|eapply IH; eassumption].
Qed.

Definition teq (v w : V) : Prop :=
  exists E : projT1 v = projT1 w, leq (projT1 w) (eq_rect _ lab (projT2 v) _ E) (projT2 w).

Lemma teq_refl v : teq v v.
Proof. exists eq_refl. apply leq_refl. Qed.

Lemma teq_sym v w : teq v w -> teq w v.
Proof.
  destruct v as [s l], w as [s' l']; intros [E H]; cbn in *. destruct E. exists eq_refl. apply leq_sym, H.
Qed.

Lemma teq_trans u v w : teq u v -> teq v w -> teq u w.
Proof.
  destruct u as [s l], v as [s' l'], w as [s'' l'']; intros [E H] [E' H']; cbn in *.
  destruct E, E'. exists eq_refl. eapply leq_trans; eassumption.
Qed.

Definition Vset : pset := {| pcar := V; peq := teq; peq_refl := teq_refl; peq_sym := teq_sym; peq_trans := teq_trans |}.

(** Les branches, au niveau des formes et des étiquettes. La forme d'une
    sous-branche ne dépend que de la forme : c'est ce qui permet aux
    constructions de respecter l'égalité sans extensionnalité. *)
Definition idxS (s : shape) : Type := match s with node T _ => T end.
Definition subS (s : shape) : idxS s -> shape := match s as s0 return idxS s0 -> shape with node T k => k end.
Definition labS (s : shape) : lab s -> forall t : idxS s, (pcar F * lab (subS s t))%type :=
  match s as s0 return lab s0 -> forall t : idxS s0, (pcar F * lab (subS s0 t))%type with
  | node T k => fun l => l
  end.

Lemma leq_lab s l l' : leq s l l' ->
  forall t, fst (labS s l t) ≡ fst (labS s l' t) /\ leq (subS s t) (snd (labS s l t)) (snd (labS s l' t)).
Proof. destruct s as [T k]. exact (fun H => H). Qed.

Definition idx (v : V) : Type := idxS (projT1 v).
Definition lbl (v : V) (t : idx v) : pcar F := fst (labS (projT1 v) (projT2 v) t).
Definition sub (v : V) (t : idx v) : V := existT _ (subS (projT1 v) t) (snd (labS (projT1 v) (projT2 v) t)).

(** Deux ensembles de même forme, d'étiquettes ≡, ont des branches égales. *)
Lemma teq_br s l l' t : leq s l l' ->
  lbl (existT _ s l) t ≡ lbl (existT _ s l') t /\ teq (sub (existT _ s l) t) (sub (existT _ s l') t).
Proof.
  intros H. destruct (leq_lab s l l' H t) as [H1 H2]. split; [exact H1|]. exists eq_refl. exact H2.
Qed.

(** Construire un ensemble à partir de ses branches. *)
Definition mk (T : Type) (f : T -> (pcar F * V)%type) : V :=
  existT _ (node T (fun t => projT1 (snd (f t)))) (fun t => (fst (f t), projT2 (snd (f t)))).

Lemma lbl_mk T f t : lbl (mk T f) t = fst (f t).
Proof. reflexivity. Qed.

Lemma sub_mk T f t : teq (sub (mk T f) t) (snd (f t)).
Proof. unfold sub; cbn. destruct (snd (f t)) as [s l]. apply teq_refl. Qed.

End Trees.
