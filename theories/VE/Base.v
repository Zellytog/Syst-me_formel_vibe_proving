(** * V(E) : appartenance, inclusion, égalité extensionnelle

    ⟦x ε y⟧ ≜ ⋁_{t ∈ y} (ψₜ ∧ x = yₜ), où = est l'égalité de Leibniz du
    cadre (corrections A.1 et A.2). Les formes bornées de ⊆, ∈ et ≃
    (correction A.3) sont définies par récurrence sur le premier argument :
    [subP x y] donne à la fois x ⊆ y et y ⊆ x, la seconde composante
    coïncidant, à ≡ près, avec la première de [subP y x] ([subP_swap]). *)

From SF.Models Require Import PSet Frame FrameModel.
From SF.VE Require Import Trees.

Section Base.

Context (F : frame).

Local Notation V := (V F).
Local Notation Vset := (Vset F).
Local Notation idx := (idx F).
Local Notation lbl := (lbl F).
Local Notation sub := (sub F).

(** x = y, de Leibniz. *)
Definition veq (x y : V) : pcar F := leib (F := F) (A := Vset) x y.

Lemma veq_proper x x' y y' : teq F x x' -> teq F y y' -> veq x y ≡ veq x' y'.
Proof. intros; apply leib_proper; assumption. Qed.

(** ⟦x ε y⟧ ≜ ⋁_{t ∈ y} (ψₜ ∧ x = yₜ). *)
Definition eps (x y : V) : pcar F := fex (fun t : idx y => fand (lbl y t) (veq x (sub y t))).

Lemma eps_proper x x' y y' : teq F x x' -> teq F y y' -> eps x y ≡ eps x' y'.
Proof.
  intros Ex Ey. destruct y as [s l], y' as [s' l'], Ey as [E H]; cbn in E, H. destruct E.
  apply fex_proper. intros t. destruct (teq_br F s l l' t H) as [H1 H2].
  apply fand_proper; [exact H1|]. apply veq_proper; [exact Ex|exact H2].
Qed.

(** (x ⊆ y, y ⊆ x), par récurrence sur x. *)
Fixpoint subP (s : shape) : lab F s -> V -> (pcar F * pcar F)%type :=
  match s as s0 return lab F s0 -> V -> (pcar F * pcar F)%type with
  | node T k => fun l y =>
      let E t z := subP (k t) (snd (l t)) z in
      (fall (fun t : T => fimp (fst (l t))
               (fex (fun u : idx y => fand (lbl y u) (fand (fst (E t (sub y u))) (snd (E t (sub y u))))))),
       fall (fun u : idx y => fimp (lbl y u)
               (fex (fun t : T => fand (fst (l t)) (fand (snd (E t (sub y u))) (fst (E t (sub y u))))))))
  end.

Definition subV (x y : V) := subP (projT1 x) (projT2 x) y.

Definition pequiv (p q : (pcar F * pcar F)%type) : Prop := fst p ≡ fst q /\ snd p ≡ snd q.

Lemma subP_proper_r s : forall l y y', teq F y y' -> pequiv (subP s l y) (subP s l y').
Proof.
  induction s as [T k IH]; intros l y y' Ey.
  destruct y as [s' l'], y' as [s'' l''], Ey as [E H]; cbn in E, H. destruct E.
  split; cbn [subP fst snd].
  - apply fall_proper; intros t. apply fimp_proper; [apply peq_refl|]. apply fex_proper; intros u.
    destruct (teq_br F s' l' l'' u H) as [J1 J2].
    apply fand_proper; [exact J1|].
    destruct (IH t (snd (l t)) _ _ J2) as [I1 I2]. apply fand_proper; assumption.
  - apply fall_proper; intros u. destruct (teq_br F s' l' l'' u H) as [J1 J2].
    apply fimp_proper; [exact J1|]. apply fex_proper; intros t.
    apply fand_proper; [apply peq_refl|].
    destruct (IH t (snd (l t)) _ _ J2) as [I1 I2]. apply fand_proper; assumption.
Qed.

Lemma subP_proper_l s : forall l l' y, leq F s l l' -> pequiv (subP s l y) (subP s l' y).
Proof.
  induction s as [T k IH]; intros l l' y H.
  split; cbn [subP fst snd].
  - apply fall_proper; intros t. apply fimp_proper; [exact (proj1 (H t))|]. apply fex_proper; intros u.
    apply fand_proper; [apply peq_refl|].
    destruct (IH t (snd (l t)) (snd (l' t)) (sub y u) (proj2 (H t))) as [I1 I2]. apply fand_proper; assumption.
  - apply fall_proper; intros u. apply fimp_proper; [apply peq_refl|]. apply fex_proper; intros t.
    apply fand_proper; [exact (proj1 (H t))|].
    destruct (IH t (snd (l t)) (snd (l' t)) (sub y u) (proj2 (H t))) as [I1 I2]. apply fand_proper; assumption.
Qed.

Lemma subV_proper x x' y y' : teq F x x' -> teq F y y' -> pequiv (subV x y) (subV x' y').
Proof.
  intros Ex Ey. destruct x as [s l], x' as [s' l'], Ex as [E H]; cbn in E, H. destruct E.
  destruct (subP_proper_r s l y y' Ey) as [A1 A2]. destruct (subP_proper_l s l l' y' H) as [B1 B2].
  split; eapply peq_trans; eassumption.
Qed.

(** Symétrie : la seconde composante de subP x y est la première de subP y x. *)
Lemma subP_swap s : forall l y,
  snd (subP s l y) ≡ fst (subV y (existT _ s l)) /\ fst (subP s l y) ≡ snd (subV y (existT _ s l)).
Proof.
  induction s as [T k IH]; intros l [[U k'] l']. cbn [subP subV projT1 projT2 fst snd].
  unfold sub, lbl; cbn [projT1 projT2 idxS subS labS].
  split.
  - apply fall_proper; intros u. apply fimp_proper; [apply peq_refl|]. apply fex_proper; intros t.
    apply fand_proper; [apply peq_refl|].
    destruct (IH t (snd (l t)) (existT _ (k' u) (snd (l' u)))) as [I1 I2].
    apply fand_proper.
    + eapply peq_trans; [exact I1|]. apply peq_refl.
    + eapply peq_trans; [exact I2|]. apply peq_refl.
  - apply fall_proper; intros t. apply fimp_proper; [apply peq_refl|]. apply fex_proper; intros u.
    apply fand_proper; [apply peq_refl|].
    destruct (IH t (snd (l t)) (existT _ (k' u) (snd (l' u)))) as [I1 I2].
    apply fand_proper; [exact I2|exact I1].
Qed.

(** ⟦x ⊆ y⟧, ⟦x ≃ y⟧, ⟦x ∈ y⟧. *)
Definition vsub (x y : V) : pcar F := fst (subV x y).
Definition veqv (x y : V) : pcar F := fand (vsub x y) (vsub y x).
Definition vmem (x y : V) : pcar F := fex (fun u : idx y => fand (lbl y u) (veqv x (sub y u))).

Lemma vsub_proper x x' y y' : teq F x x' -> teq F y y' -> vsub x y ≡ vsub x' y'.
Proof. intros Ex Ey. exact (proj1 (subV_proper x x' y y' Ex Ey)). Qed.

Lemma veqv_proper x x' y y' : teq F x x' -> teq F y y' -> veqv x y ≡ veqv x' y'.
Proof. intros Ex Ey. apply fand_proper; apply vsub_proper; assumption. Qed.

Lemma vmem_proper x x' y y' : teq F x x' -> teq F y y' -> vmem x y ≡ vmem x' y'.
Proof.
  intros Ex Ey. destruct y as [s l], y' as [s' l'], Ey as [E H]; cbn in E, H. destruct E.
  apply fex_proper. intros t. destruct (teq_br F s l l' t H) as [H1 H2].
  apply fand_proper; [exact H1|]. apply veqv_proper; [exact Ex|exact H2].
Qed.

(** Le dépliage de x ⊆ y : ⋀_{t ∈ x} (ψₜ ⊃ xₜ ∈ y). *)
Lemma vsub_unfold x y :
  vsub x y ≡ fall (fun t : idx x => fimp (lbl x t) (vmem (sub x t) y)).
Proof.
  destruct x as [[T k] l]. unfold vsub, subV. cbn [subP projT1 projT2 fst].
  apply fall_proper; intros t. apply fimp_proper; [apply peq_refl|]. apply fex_proper; intros u.
  apply fand_proper; [apply peq_refl|]. unfold veqv, vsub, subV. cbn [projT1 projT2].
  apply fand_proper; [apply peq_refl|].
  exact (proj1 (subP_swap (k t) (snd (l t)) (sub y u))).
Qed.

End Base.
