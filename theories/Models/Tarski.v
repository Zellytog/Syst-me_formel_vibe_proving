(** * Set-modèles standard (« tarskiens »)

    On construit un set-modèle à partir de données concrètes, par
    Lawvere–Lambek–Scott dans [PSet] :
    - un setoïde ⟦b⟧ pour chaque sorte (souvent un type, vu comme setoïde
      discret) ;
    - pour chaque symbole f : σ, un morphisme ⟦dom σ⟧ → ⟦cod σ⟧ ;
    - un prédicat de vérité T₀ sur ⟦P⟧ (pour ⟦P⟧ = [PropS], l'identité).

    1. **Validation du calcul par les règles.** Dans [PSet], l'égalité des
       morphismes est une proposition ; si le système est engendré par des
       règles, il suffit donc que chaque règle soit valide
       ([pset_generated]). C'est le point qui échappe à [Sets].
    2. **Vérité.** ⟦φ⟧γ ⇔ T₀(⟦φ⟧₀ γ), où ⟦φ⟧₀ := [stm] φ est la valeur de
       la formule ([interp_at]).
    3. **Symboles logiques standard.** Si ⇒, ∧, ∨, ⊤, ⊥, ∀, ∃, = sont
       interprétés de façon standard *relativement à T₀* (hypothèses
       ponctuelles [Himp], …, [Heq]), ils sont compatibles avec la
       structure de Heyting et avec les structures de quantification et
       d'égalité de [SetModels.v] : on obtient un modèle de la logique
       intuitionniste d'ordre (n,p) ([tarski_order_structure],
       [tarski_lmodel]). *)

From Category Require Import Lib Theory.Category Theory.Isomorphism Theory.Functor
  Structure.Terminal Structure.Cartesian Structure.Cartesian.Closed
  Functor.Structure.Cartesian Functor.Structure.Cartesian.Closed.
From Stdlib Require Import List.
Import ListNotations.
From SF.Syntax Require Import Spec Terms Renaming Traversal Eta Composition Vectors Syn.
From SF.Calculus Require Import System Rules SynConv.
From SF.Logic Require Import Judgment Propositional.
From SF.Functional Require Import Arrow Graded.
From SF.Quantifiers Require Import Quant Order.
From SF.Models Require Import PSet Semantics LLS Calculus Hyperdoctrine Logic Quantifiers Equality
  Order SetModels.

Local Notation ι a := (Spec [] a).

Set Default Proof Using "All".

Local Notation "a ⋄ b" := (peq_trans a b) (at level 50, left associativity, only parsing).

(** ** Sémantique ponctuelle dans PSet *)

Section PSetSem.

Context {Srt : Type} {Sym : spec Srt -> Type}.
Context (So : Srt -> pset).
Context (Iy : forall σ, Sym σ -> ictx PSet So (dom σ) ~> So (cod σ)).

Local Notation tm := (Terms.tm Sym).
Local Notation ictx := (ictx PSet So).
Local Notation penv := (penv PSet So).
Local Notation ext := (ext PSet So).
Local Notation stm := (stm PSet So Iy).
Local Notation sargs := (sargs PSet So Iy).
Local Notation stms := (stms PSet So Iy).
Local Notation sp_from := (sp_from PSet So).

(** La valeur d'un terme en un point de ⟦Γ⟧. *)
Definition sval {Γ s} (t : tm Γ s) (γ : ictx Γ) : So s := stm t (penv Γ) γ.

Lemma stm_ext_penv_at D {Γ s} (t : tm (D ++ Γ) s) (w : ictx Γ × ictx D) :
  stm t (ext D (penv Γ)) w ≡ sval t (sp_from D Γ w).
Proof.
  eapply peq_trans.
  - exact (pset_equiv_at (stm_ext PSet So Iy t _ _ (ext_penv PSet So D Γ)) w).
  - exact (pset_equiv_at (symmetry (stm_nat PSet So Iy t (penv (D ++ Γ)) (sp_from D Γ))) w).
Qed.

(** Sous un lieur vide, rien ne change. *)
Lemma stm_ext0_at {Γ s} (t : tm Γ s) (γ : ictx Γ) (u : punit) : stm t (ext [] (penv Γ)) (γ, u) ≡ sval t γ.
Proof.
  refine (pset_equiv_at (stm_ext PSet So Iy t (ext [] (penv Γ)) (env_comp PSet So (penv Γ) exl) _) (γ, u)
          ⋄ pset_equiv_at (symmetry (stm_nat PSet So Iy t (penv Γ) exl)) (γ, u)).
  intros σ x. reflexivity.
Qed.

End PSetSem.


(** ** Systèmes engendrés : il suffit de valider les règles *)

Section Generated.

Context {Srt : Type} {Sym : spec Srt -> Type} {I : Type} (rules : I -> rule Sym).
Context (So : Srt -> pset).
Context (Iy : forall σ, Sym σ -> ictx PSet So (dom σ) ~> So (cod σ)).

Local Notation stm := (stm PSet So Iy).
Local Notation sargs := (sargs PSet So Iy).
Local Notation penv := (penv PSet So).

Context (Hr : forall i γ, sval So Iy (r_lhs (rules i)) γ ≡ sval So Iy (r_rhs (rules i)) γ).

Lemma pset_generated_mut :
  (forall Γ s (t u : Terms.tm Sym Γ s), gconv rules Γ s t u -> forall γ, sval So Iy t γ ≡ sval So Iy u γ) /\
  (forall Γ Θ (a a' : args Sym Γ Θ), gargs rules Γ Θ a a' ->
      forall γ, sargs a (penv Γ) γ ≡ sargs a' (penv Γ) γ).
Proof.
  apply gconv_gargs_ind.
  - intros i γ. apply Hr.
  - intros Γ s t γ. apply peq_refl.
  - intros Γ s t u _ IH γ. apply peq_sym, IH.
  - intros Γ s t u w _ IH1 _ IH2 γ. exact (IH1 γ ⋄ IH2 γ).
  - intros Γ Δ s t t' v v' _ IHt _ IHv δ. unfold sval.
    refine (pset_equiv_at (stm_vsubst PSet So Iy t v (penv Δ)) δ ⋄ _).
    refine (_ ⋄ pset_equiv_at (symmetry (stm_vsubst PSet So Iy t' v' (penv Δ))) δ).
    exact (IHt _ ⋄ pfun_proper (stm t' (penv Γ)) (IHv δ)).
  - intros Γ γ. exact Logic.I.
  - intros Γ σ Θ u u' a a' _ IHu _ IHa γ. split; [apply IHa|].
    destruct σ as [D b]. cbn [dom cod] in *. intros y.
    refine (stm_ext_penv_at So Iy D u (γ, y) ⋄ _ ⋄ peq_sym (stm_ext_penv_at So Iy D u' (γ, y))).
    apply IHu.
Qed.

Theorem pset_generated Γ s (t u : Terms.tm Sym Γ s) :
  conv (generated rules) t u -> stm t (penv Γ) ≈ stm u (penv Γ).
Proof. intros H. apply pset_equiv_intro. exact (proj1 pset_generated_mut _ _ _ _ H). Qed.

(** Le set-modèle engendré par des données qui valident les règles. *)
Definition pset_model : cmodel (generated rules) PSet := lls_model (generated rules) PSet So Iy pset_generated.

End Generated.

(** ** Modèles standard des logiques d'ordre (n,p) *)

Section Tarski.

Context {Srt : Type} {Sym : spec Srt -> Type} {FS : Functional Sym} {G : Graded Sym}.
Context (CS : system Sym) (P : Srt) {n p : bound} {QI : Quantifiers Sym P n p}.
Context {HI : HasImp Sym P} {HA : HasAnd Sym P} {HO : HasOr Sym P} {HT : HasTop Sym P} {HB : HasBot Sym P}.

Local Notation L := (order_logic CS P (n := n) (p := p)).
Local Notation qs := (qsort Sym n p).
Local Notation form := (form Sym P).

Context (So : Srt -> pset).
Context (Iy : forall σ, Sym σ -> ictx PSet So (dom σ) ~> So (cod σ)).
Context (Hc : forall Γ s (t u : Terms.tm Sym Γ s),
            conv CS t u -> stm PSet So Iy t (penv PSet So Γ) ≈ stm PSet So Iy u (penv PSet So Γ)).

Definition tmodel : cmodel (l_calc Sym L) PSet := lls_model CS PSet So Iy Hc.
Local Notation M := tmodel.
Local Notation sval := (sval So Iy).

(** Le prédicat de vérité sur ⟦P⟧. *)
Context (T0 : ppred (So P)).

Definition Ttruth : ppred (ictx PSet So [ι P]) :=
  @mkp (pprod punit (pexp punit (So P))) (fun w => T0 (snd w tt))
       (fun w w' E H => pp_proper T0 (proj2 E tt) H).

Local Notation "⟦ φ ⟧" := (interp (L := L) M phd Ttruth φ).

Lemma interp_at {Γ} (φ : form Γ) γ : ⟦φ⟧ γ <-> T0 (sval φ γ).
Proof. exact (pp_iff T0 (stm_ext0_at So Iy φ γ tt)). Qed.

(** Interprétation standard des symboles logiques, relativement à T₀. *)
Context (Himp : forall q, T0 (Iy _ c_imp q) <-> (T0 (snd q tt) -> T0 (snd (fst q) tt))).
Context (Hand : forall q, T0 (Iy _ c_and q) <-> (T0 (snd q tt) /\ T0 (snd (fst q) tt))).
Context (Hor : forall q, T0 (Iy _ c_or q) <-> (T0 (snd q tt) \/ T0 (snd (fst q) tt))).
Context (Htop : forall q, T0 (Iy _ c_top q) <-> True).
Context (Hbot : forall q, T0 (Iy _ c_bot q) <-> False).
Context (Hall : forall (k : qs) q,
            T0 (Iy _ (Order.q_all (projT1 k) (projT2 k)) q) <-> forall a, T0 (snd q (tt, a))).
Context (Hex : forall (k : qs) q,
            T0 (Iy _ (Order.q_ex (projT1 k) (projT2 k)) q) <-> @ex _ (fun a => T0 (snd q (tt, a)))).
Context (Heq : forall (k : qs) q,
            T0 (Iy _ (Order.q_eq (projT1 k) (projT2 k)) q) <-> snd q tt ≡ snd (fst q) tt).

Lemma bin_at (c : Sym (Spec [ι P; ι P] P)) (R : Prop -> Prop -> Prop)
  (Hc' : forall q, T0 (Iy _ c q) <-> R (T0 (snd q tt)) (T0 (snd (fst q) tt))) {Γ} (a b : form Γ) γ :
  ⟦Bin c a b⟧ γ <-> R (⟦a⟧ γ) (⟦b⟧ γ).
Proof.
  etransitivity; [apply interp_at|].
  exact (Hc' (sargs PSet So Iy (@acons _ Sym Γ (ι P) _ a (@acons _ Sym Γ (ι P) _ b anil)) (penv PSet So Γ) γ)).
Qed.

Lemma tarski_imp : bin_compat L PSet M phd Ttruth c_imp (fun X => pimp).
Proof.
  intros Γ a b; split; intros γ K;
    [exact (proj1 (bin_at _ (fun A B => A -> B) Himp a b γ) K)
    |exact (proj2 (bin_at _ (fun A B => A -> B) Himp a b γ) K)].
Qed.
Lemma tarski_and : bin_compat L PSet M phd Ttruth c_and (fun X => pand).
Proof.
  intros Γ a b; split; intros γ K;
    [exact (proj1 (bin_at _ and Hand a b γ) K)|exact (proj2 (bin_at _ and Hand a b γ) K)].
Qed.
Lemma tarski_or : bin_compat L PSet M phd Ttruth c_or (fun X => por).
Proof.
  intros Γ a b; split; intros γ K;
    [exact (proj1 (bin_at _ or Hor a b γ) K)|exact (proj2 (bin_at _ or Hor a b γ) K)].
Qed.

Lemma cst_at (c : Sym (ι P)) {Γ} γ : ⟦Cst (Γ := Γ) c⟧ γ <-> T0 (Iy _ c tt).
Proof. etransitivity; [apply interp_at|]. reflexivity. Qed.

Lemma tarski_top : cst_compat L PSet M phd Ttruth c_top (fun X => ptop).
Proof.
  intros Γ; split; intros γ K; [exact Logic.I|].
  apply (proj2 (cst_at _ γ)), (proj2 (Htop tt)). exact Logic.I.
Qed.

Lemma tarski_bot : cst_compat L PSet M phd Ttruth c_bot (fun X => pbot).
Proof. intros Γ; split; intros γ K; [|destruct K]. exact (proj1 (Hbot tt) (proj1 (cst_at _ γ) K)). Qed.

(** *** Quantificateurs et égalité *)

Section Sort.
Variable k : qs.
Local Notation s := (projT1 k).

Lemma pin_at {Γ} (φ : form (ι s :: Γ)) γ a :
  ⟦φ⟧ (pin L M Γ [ι s] (γ, a)) <-> T0 (stm PSet So Iy φ (ext PSet So [ι s] (penv PSet So Γ)) (γ, a)).
Proof.
  etransitivity; [apply interp_at|].
  exact (pp_iff T0 (peq_sym (stm_ext_penv_at So Iy [ι s] φ (γ, a)))).
Qed.

Lemma pair_tt {Γ} (γ : ictx PSet So Γ) (a : pprod punit (pexp punit (So s))) :
  @peq (pprod (ictx PSet So Γ) (pprod punit (pexp punit (So s)))) (γ, a) (γ, (tt, snd a)).
Proof. split; [apply peq_refl|split; [exact Logic.I|apply peq_refl]]. Qed.

Lemma all_at {Γ} (φ : form (ι s :: Γ)) γ :
  ⟦@All _ Sym P s (qall_inst k) Γ φ⟧ γ
  <-> forall a, T0 (stm PSet So Iy φ (ext PSet So [ι s] (penv PSet So Γ)) (γ, (tt, a))).
Proof.
  etransitivity; [apply interp_at|].
  exact (Hall k (sargs PSet So Iy (@acons _ Sym Γ (Spec [ι s] P) _ φ anil) (penv PSet So Γ) γ)).
Qed.

Lemma ex_at {Γ} (φ : form (ι s :: Γ)) γ :
  ⟦@Ex _ Sym P s (qex_inst k) Γ φ⟧ γ
  <-> @ex _ (fun a => T0 (stm PSet So Iy φ (ext PSet So [ι s] (penv PSet So Γ)) (γ, (tt, a)))).
Proof.
  etransitivity; [apply interp_at|].
  exact (Hex k (sargs PSet So Iy (@acons _ Sym Γ (Spec [ι s] P) _ φ anil) (penv PSet So Γ) γ)).
Qed.

Lemma tarski_all : @all_compat _ _ L PSet _ _ _ M phd Ttruth s (set_qstruct L M s) (qall_inst k).
Proof.
  intros Γ φ; split; intros γ K.
  - intros a. apply (proj2 (pin_at φ γ a)).
    apply (pp_proper T0 (pfun_proper _ (peq_sym (pair_tt γ a)))).
    exact (proj1 (all_at φ γ) K (snd a)).
  - apply (proj2 (all_at φ γ)). intros a. exact (proj1 (pin_at φ γ (tt, a)) (K (tt, a))).
Qed.

Lemma tarski_ex : @ex_compat _ _ L PSet _ _ _ M phd Ttruth s (set_qstruct L M s) (qex_inst k).
Proof.
  intros Γ φ; split; intros γ K.
  - destruct (proj1 (ex_at φ γ) K) as [a Ha]. exists (tt, a). exact (proj2 (pin_at φ γ (tt, a)) Ha).
  - destruct K as [a Ha]. apply (proj2 (ex_at φ γ)). exists (snd a).
    apply (pp_proper T0 (pfun_proper _ (pair_tt γ a))). exact (proj1 (pin_at φ γ a) Ha).
Qed.

Lemma eq_at {Γ} (t u : Terms.tm Sym Γ s) γ :
  ⟦@Eq _ Sym P s (qeq_inst k) Γ t u⟧ γ
  <-> stm PSet So Iy t (ext PSet So [] (penv PSet So Γ)) (γ, tt)
      ≡ stm PSet So Iy u (ext PSet So [] (penv PSet So Γ)) (γ, tt).
Proof.
  etransitivity; [apply interp_at|].
  exact (Heq k (sargs PSet So Iy (@acons _ Sym Γ (ι s) _ t (@acons _ Sym Γ (ι s) _ u anil))
                  (penv PSet So Γ) γ)).
Qed.

Lemma seq_at {Γ} (t u : Terms.tm Sym Γ s) γ :
  seq L M s Γ (fmap[cm_fun M] (vpair s t u) γ)
  <-> stm PSet So Iy t (ext PSet So [] (penv PSet So Γ)) (γ, tt)
      ≡ stm PSet So Iy u (ext PSet So [] (penv PSet So Γ)) (γ, tt).
Proof.
  split.
  - intros [_ H]. exact (H tt).
  - intros H. split; [exact Logic.I|]. intros []. exact H.
Qed.

Lemma tarski_eq : @eq_compat _ _ L PSet _ _ _ M phd Ttruth s (set_eqstruct L M s) (qeq_inst k).
Proof.
  intros Γ t u; split; intros γ K.
  - exact (proj2 (seq_at t u γ) (proj1 (eq_at t u γ) K)).
  - exact (proj2 (eq_at t u γ) (proj1 (seq_at t u γ) K)).
Qed.

End Sort.

(** *** Le modèle *)

Definition tarski_order_structure : order_structure L PSet M phd Ttruth := {|
  os_imp := tarski_imp; os_and := tarski_and; os_or := tarski_or;
  os_top := tarski_top; os_bot := tarski_bot;
  os_q := fun k => set_qstruct L M (projT1 k);
  os_all := tarski_all; os_ex := tarski_ex;
  os_e := fun k => set_eqstruct L M (projT1 k);
  os_eq := tarski_eq
|}.

Definition tarski_lmodel : lmodel L PSet := order_lmodel CS P PSet M phd Ttruth tarski_order_structure.

(** Correction : un jugement prouvable est vrai en tout point où ses
    hypothèses sont vraies. *)
Theorem tarski_sound Γ Ξ φ :
  provable L Γ Ξ φ -> forall γ, (forall χ, In χ Ξ -> T0 (sval χ γ)) -> T0 (sval φ γ).
Proof.
  intros Hd γ Hγ. apply (proj1 (interp_at φ γ)).
  apply (lmodel_sound tarski_lmodel Γ Ξ φ Hd γ).
  clear Hd. induction Ξ as [|χ Ξ IH]; [exact Logic.I|]. split.
  - apply (proj2 (interp_at χ γ)), Hγ. left; reflexivity.
  - apply IH. intros χ' H. apply Hγ. right; exact H.
Qed.

End Tarski.
