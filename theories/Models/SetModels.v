(** * Set-modèles

    Un **set-modèle** est un modèle dans la catégorie [PSet] des setoïdes
    propositionnels, avec l'hyperdoctrine des prédicats ([phd]) : un prédicat
    sur X est une propriété X → Prop qui respecte l'égalité de X, l'ordre est
    l'implication point par point et la réindexation est la précomposition.

    Pour tout modèle du calcul M dans [PSet] et *toute* sorte s (pas
    seulement les quantifiables), cette hyperdoctrine porte :
    - une structure de quantification ([set_qstruct]) :
      (∀_Γ p)(γ) := ∀ a, p⟨γ, a⟩ et (∃_Γ p)(γ) := ∃ a, p⟨γ, a⟩ ;
    - une structure d'égalité ([set_eqstruct]) : E_Γ⟨γ, a, b⟩ := a ≡ b.

    Un set-modèle d'une logique d'ordre (n,p) est donc donné par un modèle
    du calcul, un prédicat de vérité T sur ⟦P⟧ et la compatibilité des
    symboles logiques avec ces structures ([set_order_structure]). *)

From Category Require Import Lib Theory.Category Theory.Isomorphism Theory.Functor
  Structure.Terminal Structure.Cartesian Structure.Cartesian.Closed
  Functor.Structure.Cartesian Functor.Structure.Cartesian.Closed.
From Stdlib Require Import List.
Import ListNotations.
From SF.Syntax Require Import Spec Terms Renaming Traversal Eta Composition Vectors Syn.
From SF.Calculus Require Import System SynConv.
From SF.Logic Require Import Judgment Propositional.
From SF.Functional Require Import Arrow Graded.
From SF.Quantifiers Require Import Quant Order.
From SF.Models Require Import PSet Calculus Hyperdoctrine Logic Quantifiers Equality Order.

Local Notation ι a := (Spec [] a).

(** ** L'hyperdoctrine des prédicats *)

Record ppred (X : pset) := {
  pp :> X -> Prop;
  pp_proper : forall x y, x ≡ y -> pp x -> pp y
}.

Arguments pp {X} _ _.
Arguments pp_proper {X} _ {x y} _ _.

Lemma pp_iff {X} (p : ppred X) {x y : X} : x ≡ y -> p x <-> p y.
Proof. intros E; split; apply pp_proper; [exact E|exact (peq_sym E)]. Qed.

Definition mkp {X : pset} (f : X -> Prop) (Hf : forall x y, x ≡ y -> f x -> f y) : ppred X :=
  {| pp := f; pp_proper := Hf |}.

Definition p_top {X} : ppred X := mkp (fun _ => True) (fun _ _ _ H => H).
Definition p_bot {X} : ppred X := mkp (fun _ => False) (fun _ _ _ H => H).
Definition p_and {X} (p q : ppred X) : ppred X :=
  mkp (fun x => p x /\ q x) (fun x y E H => conj (pp_proper p E (proj1 H)) (pp_proper q E (proj2 H))).
Definition p_or {X} (p q : ppred X) : ppred X :=
  mkp (fun x => p x \/ q x)
      (fun x y E H => match H with
                      | or_introl h => or_introl (pp_proper p E h)
                      | or_intror h => or_intror (pp_proper q E h)
                      end).
Definition p_imp {X} (p q : ppred X) : ppred X :=
  mkp (fun x => p x -> q x) (fun x y E H h => pp_proper q E (H (pp_proper p (peq_sym E) h))).
Definition p_reidx {X Y : PSet} (f : X ~> Y) (p : ppred Y) : ppred X :=
  mkp (fun x => p (f x)) (fun x y E H => pp_proper p (pfun_proper f E) H).

Definition phd : hyperdoctrine PSet.
Proof.
  refine (@Build_hyperdoctrine PSet ppred (fun X p q => forall x, p x -> q x) _ _
            (@p_top) (@p_bot) (@p_and) (@p_or) (@p_imp) _ _ _ _ _ _ _ _ _
            (@p_reidx) _ _ _ _ _ _ _ _ _); cbn; try firstorder.
  match goal with E : pmor_eq ?f ?g, x : _, h : pp ?p (pfun ?f ?x) |- _ => exact (pp_proper p (E x) h) end.
Defined.

(** ** Un modèle du calcul dans PSet et ses isomorphismes de produit *)

Section SetStructures.

Context {Srt : Type} {Sym : spec Srt -> Type} (L : logic Sym).

Local Notation CS := (l_calc Sym L).
Local Notation P := (l_prop Sym L).
Local Notation Syn := (SynConv CS).

Context (M : cmodel CS PSet).

Local Notation F := (cm_fun M).

Definition piso (Γ Δ : Syn) : F (Γ × Δ) ≅ F Γ × F Δ :=
  @fobj_prod_iso _ _ F _ _ (cm_cartesian _ _ M) Γ Δ.

Definition pout (Γ Δ : Syn) : F (Γ × Δ) ~> F Γ × F Δ := to (piso Γ Δ).
Definition pin (Γ Δ : Syn) : F Γ × F Δ ~> F (Γ × Δ) := from (piso Γ Δ).

Lemma pout_pin Γ Δ p : pout Γ Δ (pin Γ Δ p) ≡ p.
Proof. exact (pset_equiv_at (iso_to_from (piso Γ Δ)) p). Qed.

Lemma pin_pout Γ Δ w : pin Γ Δ (pout Γ Δ w) ≡ w.
Proof. exact (pset_equiv_at (iso_from_to (piso Γ Δ)) w). Qed.

Lemma fmap_exl_at Γ Δ w : fmap[F] (@exl Syn _ Γ Δ) w ≡ fst (pout Γ Δ w).
Proof. exact (pset_equiv_at (@fmap_exl _ _ F _ _ (cm_cartesian _ _ M) Γ Δ) w). Qed.

Lemma fmap_exr_at Γ Δ w : fmap[F] (@exr Syn _ Γ Δ) w ≡ snd (pout Γ Δ w).
Proof. exact (pset_equiv_at (@fmap_exr _ _ F _ _ (cm_cartesian _ _ M) Γ Δ) w). Qed.

Lemma fmap_fork_at {X Γ Δ : Syn} (f : X ~> Γ) (g : X ~> Δ) x :
  fmap[F] (f △ g) x ≡ pin Γ Δ (fmap[F] f x, fmap[F] g x).
Proof. exact (pset_equiv_at (@fmap_fork _ _ F _ _ (cm_cartesian _ _ M) X Γ Δ f g) x). Qed.

Lemma fmap_comp_at {X Y Z : Syn} (f : Y ~> Z) (g : X ~> Y) x :
  fmap[F] (f ∘ g) x ≡ fmap[F] f (fmap[F] g x).
Proof. exact (pset_equiv_at (@fmap_comp _ _ F X Y Z f g) x). Qed.

Lemma fmap_id_at (X : Syn) x : fmap[F] (@id Syn X) x ≡ x.
Proof. exact (pset_equiv_at (@fmap_id _ _ F X) x). Qed.

Lemma pin_proper Γ Δ (a a' : F Γ) (b b' : F Δ) : a ≡ a' -> b ≡ b' -> pin Γ Δ (a, b) ≡ pin Γ Δ (a', b').
Proof. intros E1 E2. apply pfun_proper. split; assumption. Qed.

(** ⟦first v⟧⟨δ, a⟩ ≡ ⟨⟦v⟧ δ, a⟩. *)
Lemma fmap_first_at {Δ Γ Z : Syn} (v : Δ ~> Γ) (δ : F Δ) (a : F Z) :
  fmap[F] (@first Syn _ Δ Γ Z v) (pin Δ Z (δ, a)) ≡ pin Γ Z (fmap[F] v δ, a).
Proof.
  unfold first. eapply peq_trans; [apply fmap_fork_at|]. apply pin_proper.
  - eapply peq_trans; [apply fmap_comp_at|]. apply pfun_proper.
    eapply peq_trans; [apply fmap_exl_at|]. exact (proj1 (pout_pin Δ Z (δ, a))).
  - eapply peq_trans; [apply fmap_exr_at|]. exact (proj2 (pout_pin Δ Z (δ, a))).
Qed.

(** *** Faits syntaxiques *)

Lemma wkv_exl s Γ : wkv (Sym := Sym) s Γ = @exl Syn _ Γ [ι s].
Proof. reflexivity. Qed.

Lemma vup_first s {Γ Δ} (v : vec Sym Γ Δ) : vup [ι s] v = @first Syn _ Δ Γ [ι s] v.
Proof.
  unfold vup, first. simpl. f_equal.
  rewrite <- (vcomp_vid_r v) at 1. rewrite vren_vcomp. f_equal.
  apply vec_ext; intros σ x. unfold vget, vren, sexl, vid. rewrite aget_vmap, !aget_etas.
  apply eta_ren.
Qed.

Lemma vdiag_fork s Γ :
  vdiag (Sym := Sym) s Γ = @fork Syn _ (ι s :: Γ) (ι s :: Γ) [ι s] (@id Syn _) (@exr Syn _ Γ [ι s]).
Proof. reflexivity. Qed.

(** ** Quantification le long de toute projection *)

Variable s : Srt.

Local Notation π Γ := (fmap[F] (wkv (Sym := Sym) s Γ)).

Definition sall Γ (p : ppred (F (ι s :: Γ))) : ppred (F Γ) :=
  mkp (fun γ => forall a, p (pin Γ [ι s] (γ, a)))
      (fun γ γ' E H a => pp_proper p (pin_proper _ _ _ _ _ _ E (peq_refl a)) (H a)).

Definition sex Γ (p : ppred (F (ι s :: Γ))) : ppred (F Γ) :=
  mkp (fun γ => @ex _ (fun a => p (pin Γ [ι s] (γ, a))))
      (fun γ γ' E H => match H with
                       | ex_intro _ a h => ex_intro _ a (pp_proper p (pin_proper _ _ _ _ _ _ E (peq_refl a)) h)
                       end).

Lemma pi_at Γ w : π Γ w ≡ fst (pout Γ [ι s] w).
Proof. exact (fmap_exl_at Γ [ι s] w). Qed.

Lemma pi_pin Γ γ a : π Γ (pin Γ [ι s] (γ, a)) ≡ γ.
Proof. eapply peq_trans; [apply pi_at|]. exact (proj1 (pout_pin _ _ (γ, a))). Qed.

(** Toute w se recompose à partir de ses composantes. *)
Lemma pin_split Γ Δ w : w ≡ pin Γ Δ (fst (pout Γ Δ w), snd (pout Γ Δ w)).
Proof.
  apply peq_sym. eapply peq_trans; [|apply (pin_pout Γ Δ w)].
  apply pfun_proper. split; apply peq_refl.
Qed.

Lemma vup_pin {Γ Δ} (v : vec Sym Γ Δ) δ a :
  fmap[F] (vup [ι s] v) (pin Δ [ι s] (δ, a)) ≡ pin Γ [ι s] (fmap[F] v δ, a).
Proof.
  eapply peq_trans; [|exact (fmap_first_at v δ a)].
  exact (pset_equiv_at (@fmap_respects _ _ F (ι s :: Δ) (ι s :: Γ) _ _ (arel_eq CS _ _ (vup_first s v))) _).
Qed.

Definition set_qstruct : qstruct L PSet M phd s.
Proof.
  refine (@Build_qstruct _ _ L PSet _ _ _ M phd s sall sex _ _ _ _); cbn.
  - intros Γ q p. split.
    + intros H γ Hq a. apply H. exact (pp_proper q (peq_sym (pi_pin Γ γ a)) Hq).
    + intros H w Hq. apply (pp_proper p (peq_sym (pin_split Γ [ι s] w))).
      apply H. exact (pp_proper q (pi_at Γ w) Hq).
  - intros Γ p q. split.
    + intros H w Hp. apply (pp_proper q (peq_sym (pi_at Γ w))). apply H.
      exists (snd (pout Γ [ι s] w)). exact (pp_proper p (pin_split Γ [ι s] w) Hp).
    + intros H γ [a Ha]. exact (pp_proper q (pi_pin Γ γ a) (H _ Ha)).
  - intros Γ Δ v p. split.
    + intros δ H a. exact (pp_proper p (peq_sym (vup_pin v δ a)) (H a)).
    + intros δ H a. exact (pp_proper p (vup_pin v δ a) (H a)).
  - intros Γ Δ v p. split.
    + intros δ [a Ha]. exists a. exact (pp_proper p (peq_sym (vup_pin v δ a)) Ha).
    + intros δ [a Ha]. exists a. exact (pp_proper p (vup_pin v δ a) Ha).
Defined.

(** ** Égalité : E⟨γ, a, b⟩ := a ≡ b *)

Definition seq_rel Γ (w : F (ι s :: ι s :: Γ)) : Prop :=
  snd (pout Γ [ι s] (fst (pout (ι s :: Γ) [ι s] w))) ≡ snd (pout (ι s :: Γ) [ι s] w).

Lemma seq_rel_proper Γ w w' : w ≡ w' -> seq_rel Γ w -> seq_rel Γ w'.
Proof.
  intros E H. unfold seq_rel in *.
  pose proof (pfun_proper (pout (ι s :: Γ) [ι s]) E) as [E1 E2].
  pose proof (pfun_proper (pout Γ [ι s]) E1) as [_ E3].
  eapply peq_trans; [exact (peq_sym E3)|]. eapply peq_trans; [exact H|exact E2].
Qed.

Definition seq Γ : ppred (F (ι s :: ι s :: Γ)) := mkp (seq_rel Γ) (seq_rel_proper Γ).

(** ⟦δ⟧ x ≡ ⟨x, x₀⟩. *)
Lemma vdiag_at Γ x :
  fmap[F] (vdiag (Sym := Sym) s Γ) x ≡ pin (ι s :: Γ) [ι s] (x, snd (pout Γ [ι s] x)).
Proof.
  eapply peq_trans; [exact (fmap_fork_at (@id Syn _) (@exr Syn _ Γ [ι s]) x)|].
  apply (pin_proper (ι s :: Γ) [ι s]); [apply fmap_id_at|apply (fmap_exr_at Γ [ι s])].
Qed.

Lemma seq_pin Γ x b : seq Γ (pin (ι s :: Γ) [ι s] (x, b)) <-> snd (pout Γ [ι s] x) ≡ b.
Proof.
  cbn. unfold seq_rel. destruct (pout_pin (ι s :: Γ) [ι s] (x, b)) as [E1 E2]. cbn in E1, E2.
  destruct (pfun_proper (pout Γ [ι s]) E1) as [_ E3].
  split; intros H.
  - eapply peq_trans; [exact (peq_sym E3)|]. eapply peq_trans; [exact H|exact E2].
  - eapply peq_trans; [exact E3|]. eapply peq_trans; [exact H|exact (peq_sym E2)].
Qed.

Definition set_eqstruct : eqstruct L PSet M phd s.
Proof.
  refine (@Build_eqstruct _ _ L PSet _ _ _ M phd s seq _ _); cbn.
  - intros Γ x _. apply (pp_proper (seq Γ) (peq_sym (vdiag_at Γ x))). apply seq_pin, peq_refl.
  - intros Γ q K w Hw.
    apply (pp_proper q (peq_sym (pin_split (ι s :: Γ) [ι s] w))).
    set (r := fst (pout (ι s :: Γ) [ι s] w)). set (b := snd (pout (ι s :: Γ) [ι s] w)).
    apply (pp_proper q (vdiag_at Γ r)) in K; [|exact Logic.I]. revert K. apply pp_proper.
    apply (pin_proper (ι s :: Γ) [ι s]); [apply peq_refl|exact Hw].
Defined.

End SetStructures.
