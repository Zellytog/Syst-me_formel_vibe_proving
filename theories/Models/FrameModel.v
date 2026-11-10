(** * Le tripos d'un cadre d'évidence, et ses structures logiques

    Pour un cadre d'évidence F (voir [Frame.v]), l'hyperdoctrine [fhd F]
    au-dessus de [PSet] :
    - un prédicat sur X est un morphisme X → Φ (une famille de propositions
      qui respecte l'égalité de X) ;
    - l'ordre est **uniforme** : φ ≤ ψ s'il existe *une* évidence e telle
      que φ(x) —e→ ψ(x) pour tout x ;
    - les connecteurs sont ceux de Φ, point par point, et la réindexation
      est la précomposition.

    Pour tout modèle du calcul M dans [PSet] et *toute* sorte s, cette
    hyperdoctrine porte :
    - une structure de quantification ([fqstruct]) :
      (∀_Γ p)(γ) := ⋀ₐ p⟨γ, a⟩ et (∃_Γ p)(γ) := ⋁ₐ p⟨γ, a⟩ ;
    - une structure d'égalité ([feqstruct]) : l'égalité de Leibniz
      E⟨γ, a, b⟩ := ⋀_ψ (ψ a ⇒ ψ b), où ψ parcourt les prédicats sur ⟦s⟧.

    Pour Φ = Prop ([prop_frame]), on retrouve le set-modèle usuel
    ([SetModels.v]). *)

From Category Require Import Lib Theory.Category Theory.Isomorphism Theory.Functor
  Structure.Terminal Structure.Cartesian Structure.Cartesian.Closed
  Functor.Structure.Cartesian Functor.Structure.Cartesian.Closed.
From Stdlib Require Import List.
Import ListNotations.
From SF.Syntax Require Import Spec Terms Vectors Syn.
From SF.Calculus Require Import System SynConv.
From SF.Logic Require Import Judgment.
From SF.Models Require Import PSet Frame Calculus Hyperdoctrine Logic Quantifiers Equality SetModels.

Local Notation ι a := (Spec [] a).

Set Default Proof Using "All".

(** ** L'hyperdoctrine *)

Section Tripos.

Context (F : frame).

Local Notation "φ —[ e ]→ ψ" := (fent (F := F) φ e ψ) (at level 70).

Definition fmor {X : pset} (f : X -> F) (Hf : forall x x', x ≡ x' -> f x ≡ f x') : pmor X F :=
  Build_pmor X F f Hf.

Definition fle {X : pset} (p q : pmor X F) : Prop := exists e, forall x, p x —[e]→ q x.

Definition ft_top {X : pset} : pmor X F := fmor (fun _ => ftop) (fun _ _ _ => peq_refl _).
Definition ft_bot {X : pset} : pmor X F := fmor (fun _ => fbot) (fun _ _ _ => peq_refl _).
Definition ft_and {X : pset} (p q : pmor X F) : pmor X F :=
  fmor (fun x => fand (p x) (q x)) (fun x x' E => fand_proper F _ _ _ _ (pfun_proper p E) (pfun_proper q E)).
Definition ft_or {X : pset} (p q : pmor X F) : pmor X F :=
  fmor (fun x => for_ (p x) (q x)) (fun x x' E => for_proper _ _ _ _ (pfun_proper p E) (pfun_proper q E)).
Definition ft_imp {X : pset} (p q : pmor X F) : pmor X F :=
  fmor (fun x => fimp (p x) (q x)) (fun x x' E => fimp_proper F _ _ _ _ (pfun_proper p E) (pfun_proper q E)).
Definition ft_reidx {X Y : PSet} (f : X ~> Y) (p : pmor Y F) : pmor X F := pmor_comp p f.

Lemma fle_eq {X : pset} (p q : pmor X F) : (forall x, p x ≡ q x) -> fle p q.
Proof. intros H. exists e_id. intros x. apply fent_of_eq, H. Qed.

Lemma fle_refl {X : pset} (p : pmor X F) : fle p p.
Proof. apply fle_eq. intros x. apply peq_refl. Qed.

Definition fhd : hyperdoctrine PSet.
Proof.
  refine (@Build_hyperdoctrine PSet (fun X => pmor X F) (@fle) _ _
            (@ft_top) (@ft_bot) (@ft_and) (@ft_or) (@ft_imp) _ _ _ _ _ _ _ _ _
            (@ft_reidx) _ _ _ _ _ _ _ _ _).
  - (* refl *) intros X p. apply fle_refl.
  - (* trans *) intros X p q r [e1 H1] [e2 H2]. exists (e_comp e1 e2). intros x. eapply f_comp; eauto.
  - (* top *) intros X p. exists e_top. intros x. apply f_top.
  - (* bot *) intros X p. exists e_inst. intros x. apply f_bot.
  - (* and_l *) intros X p q. exists e_fst. intros x. apply f_fst.
  - (* and_r *) intros X p q. exists e_snd. intros x. apply f_snd.
  - (* and_intro *) intros X p q r [e1 H1] [e2 H2]. exists (e_pair e1 e2). intros x. apply f_pair; auto.
  - (* or_l *) intros X p q. exists e_inl. intros x. apply f_inl.
  - (* or_r *) intros X p q. exists e_inr. intros x. apply f_inr.
  - (* or_elim *) intros X p q r [e1 H1] [e2 H2]. exists (e_case e1 e2). intros x. apply f_case; auto.
  - (* imp_adj *) intros X p q r. split.
    + intros [e H]. exists (e_lam e). intros x. apply f_lam, H.
    + intros [e H]. exists (e_unlam e). intros x. apply f_unlam, H.
  - (* reidx_proper *) intros X Y f g p E. apply fle_eq. intros x. apply (pfun_proper p (E x)).
  - (* reidx_mono *) intros X Y f p q [e H]. exists e. intros x. apply H.
  - (* reidx_id *) intros X p. split; apply fle_refl.
  - (* reidx_comp *) intros X Y Z f g p. split; apply fle_refl.
  - (* reidx_top *) intros X Y f. apply fle_refl.
  - (* reidx_bot *) intros X Y f. apply fle_refl.
  - (* reidx_and *) intros X Y f p q. apply fle_refl.
  - (* reidx_or *) intros X Y f p q. apply fle_refl.
  - (* reidx_imp *) intros X Y f p q. split; apply fle_refl.
Defined.

(** *** L'égalité de Leibniz dans Φ *)

Definition leib {A : pset} (a b : A) : F := fall (I := pmor A F) (fun ψ => fimp (ψ a) (ψ b)).

Lemma leib_proper {A : pset} (a a' b b' : A) : a ≡ a' -> b ≡ b' -> leib a b ≡ leib a' b'.
Proof.
  intros Ea Eb. apply fall_proper. intros ψ. apply fimp_proper; apply pfun_proper; assumption.
Qed.

Definition e_refl : fev F := e_gen (e_lam e_snd).

Lemma f_leib_refl {A : pset} (a : A) φ : φ —[e_refl]→ leib a a.
Proof. apply f_gen. intros ψ. apply f_lam, f_snd. Qed.

End Tripos.

Arguments fmor {F X} f Hf.
Arguments fle {F X} p q.
Arguments leib {F A} a b.

(** ** Quantification et égalité, pour toute sorte *)

Section FrameStructures.

Context (F : frame).
Context {Srt : Type} {Sym : spec Srt -> Type} (L : logic Sym).

Local Notation CS := (l_calc Sym L).
Local Notation Syn := (SynConv CS).
Local Notation "φ —[ e ]→ ψ" := (fent (F := F) φ e ψ) (at level 70).

Context (M : cmodel CS PSet).
Context (s : Srt).

Local Notation FM := (cm_fun M).
Local Notation pin := (pin L M).
Local Notation pout := (pout L M).
Local Notation π Γ := (fmap[FM] (wkv (Sym := Sym) s Γ)).

Definition fsall Γ (p : pmor (FM (ι s :: Γ)) F) : pmor (FM Γ) F :=
  fmor (fun γ => fall (fun a => p (pin Γ [ι s] (γ, a))))
       (fun γ γ' E => fall_proper F _ _ _ (fun a => pfun_proper p (pin_proper L M Γ [ι s] _ _ _ _ E (peq_refl a)))).

Definition fsex Γ (p : pmor (FM (ι s :: Γ)) F) : pmor (FM Γ) F :=
  fmor (fun γ => fex (fun a => p (pin Γ [ι s] (γ, a))))
       (fun γ γ' E => fex_proper _ _ _ (fun a => pfun_proper p (pin_proper L M Γ [ι s] _ _ _ _ E (peq_refl a)))).

Definition fqstruct : qstruct L PSet M (fhd F) s.
Proof.
  refine (@Build_qstruct _ _ L PSet _ _ _ M (fhd F) s fsall fsex _ _ _ _); cbn.
  - (* ∀ ⊣ *) intros Γ q p. split.
    + intros [e H]. exists (e_gen e). intros γ. apply f_gen. intros a.
      apply (fent_eq (q (π Γ (pin Γ [ι s] (γ, a))))); [apply pfun_proper, (pi_pin L M s)|apply H].
    + intros [e H]. exists (e_comp e e_inst). intros w. eapply f_comp; [apply H|].
      apply (fent_eq_r _ _ _ _ (pfun_proper p (peq_trans (pin_proper L M Γ [ι s] _ _ _ _
               (pi_at L M s Γ w) (peq_refl _)) (peq_sym (pin_split L M Γ [ι s] w))))).
      apply (f_inst F _ (fun a => p (pin Γ [ι s] (π Γ w, a))) (snd (pout Γ [ι s] w))).
  - (* ∃ ⊣ *) intros Γ p q. split.
    + intros [e H]. exists (e_comp e_exI e). intros w.
      apply (fent_eq (p (pin Γ [ι s] (fst (pout Γ [ι s] w), snd (pout Γ [ι s] w)))));
        [apply pfun_proper, peq_sym, (pin_split L M Γ [ι s] w)|].
      eapply f_comp; [apply (f_exI _ (fun a => p (pin Γ [ι s] (fst (pout Γ [ι s] w), a))))|].
      apply (fent_eq_r _ _ _ _ (pfun_proper q (peq_sym (pi_at L M s Γ w)))), H.
    + intros [e H]. exists (e_exE e). intros γ. apply f_exE. intros a.
      apply (fent_eq_r _ _ _ _ (pfun_proper q (pi_pin L M s Γ γ a))), H.
  - (* BC ∀ *) intros Γ Δ v p. split; apply fle_eq; intros δ; cbn; apply fall_proper; intros a;
      apply pfun_proper; [apply peq_sym|]; apply (vup_pin L M s v δ a).
  - (* BC ∃ *) intros Γ Δ v p. split; apply fle_eq; intros δ; cbn; apply fex_proper; intros a;
      apply pfun_proper; [apply peq_sym|]; apply (vup_pin L M s v δ a).
Defined.

(** *** L'égalité *)

(** Les deux dernières composantes de w ∈ ⟦Γ, x₁ : s, x₀ : s⟧. *)
Definition c1 Γ (w : FM (ι s :: ι s :: Γ)) := snd (pout Γ [ι s] (fst (pout (ι s :: Γ) [ι s] w))).
Definition c0 Γ (w : FM (ι s :: ι s :: Γ)) := snd (pout (ι s :: Γ) [ι s] w).

Lemma c_proper Γ w w' : w ≡ w' -> c1 Γ w ≡ c1 Γ w' /\ c0 Γ w ≡ c0 Γ w'.
Proof.
  intros E. pose proof (pfun_proper (pout (ι s :: Γ) [ι s]) E) as [E1 E2].
  pose proof (pfun_proper (pout Γ [ι s]) E1) as [_ E3]. split; assumption.
Qed.

Definition feq Γ : pmor (FM (ι s :: ι s :: Γ)) F :=
  fmor (fun w => leib (c1 Γ w) (c0 Γ w))
       (fun w w' E => leib_proper F _ _ _ _ (proj1 (c_proper Γ w w' E)) (proj2 (c_proper Γ w w' E))).

Lemma feq_pin Γ x b : feq Γ (pin (ι s :: Γ) [ι s] (x, b)) ≡ leib (snd (pout Γ [ι s] x)) b.
Proof.
  cbn. destruct (pout_pin L M (ι s :: Γ) [ι s] (x, b)) as [E1 E2]. cbn in E1, E2.
  destruct (pfun_proper (pout Γ [ι s]) E1) as [_ E3].
  apply leib_proper; assumption.
Qed.

Definition feqstruct : eqstruct L PSet M (fhd F) s.
Proof.
  refine (@Build_eqstruct _ _ L PSet _ _ _ M (fhd F) s feq _ _); cbn.
  - (* réflexivité *) intros Γ. exists (e_refl F). intros x. cbn.
    apply (fent_eq_r _ _ _ _ (peq_sym (pfun_proper (feq Γ) (vdiag_at L M s Γ x)))).
    apply (fent_eq_r _ _ _ _ (peq_sym (feq_pin Γ x _))). apply f_leib_refl.
  - (* minimalité *) intros Γ q [e K].
    exists (e_comp (e_pair e_inst (e_const e)) e_eval). intros w.
    set (r := fst (pout (ι s :: Γ) [ι s] w)). set (b := snd (pout (ι s :: Γ) [ι s] w)).
    set (c := snd (pout Γ [ι s] r)).
    set (ψ := fmor (X := FM [ι s]) (fun z => q (pin (ι s :: Γ) [ι s] (r, z)))
                (fun z z' E => pfun_proper q (pin_proper L M (ι s :: Γ) [ι s] _ _ _ _ (peq_refl r) E))).
    assert (Ew : feq Γ w ≡ leib c b).
    { eapply peq_trans; [apply pfun_proper, (pin_split L M (ι s :: Γ) [ι s] w)|apply feq_pin]. }
    apply (fent_proper F (leib c b) (feq Γ w) _ (ψ b) (q w) (peq_sym Ew)).
    { cbn. apply pfun_proper, peq_sym, (pin_split L M (ι s :: Γ) [ι s] w). }
    eapply f_comp; [apply f_pair|apply f_eval].
    + apply (f_inst F _ (fun ψ0 : pmor (FM [ι s]) F => fimp (ψ0 c) (ψ0 b)) ψ).
    + apply f_const. apply (fent_eq_r _ _ _ _ (pfun_proper q (vdiag_at L M s Γ r))), K.
Defined.

End FrameStructures.

(** L'égalité de Leibniz est préservée par tout morphisme, et reflétée par
    tout morphisme qui a une rétraction. *)
Lemma f_leib_map (F : frame) {A B : pset} (f : pmor A B) (a b : A) :
  fent (F := F) (leib a b) (e_gen e_inst) (leib (f a) (f b)).
Proof.
  apply f_gen. intros ψ.
  apply (f_inst F _ (fun ψ0 : pmor A F => fimp (ψ0 a) (ψ0 b)) (pmor_comp ψ f)).
Qed.

Lemma f_leib_back (F : frame) {A B : pset} (f : pmor A B) (g : pmor B A) (a b : A) :
  g (f a) ≡ a -> g (f b) ≡ b -> fent (F := F) (leib (f a) (f b)) (e_gen e_inst) (leib a b).
Proof.
  intros Ea Eb. apply f_gen. intros ψ.
  apply (fent_eq_r _ _ _ _ (fimp_proper F _ _ _ _ (pfun_proper ψ Ea) (pfun_proper ψ Eb))).
  apply (f_inst F _ (fun ψ0 : pmor B F => fimp (ψ0 (f a)) (ψ0 (f b))) (pmor_comp ψ g)).
Qed.
