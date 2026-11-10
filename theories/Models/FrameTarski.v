(** * Modèles standard à valeurs dans un cadre d'évidence

    Données :
    - un cadre d'évidence F ;
    - un modèle du calcul dans [PSet], construit par Lawvere–Lambek–Scott
      à partir d'un setoïde par sorte et d'un morphisme par symbole ;
    - un prédicat de vérité T₀ : ⟦P⟧ → Φ (pour ⟦P⟧ = Φ, l'identité).

    Si les symboles logiques sont interprétés de façon standard
    relativement à T₀, à ≡ près dans Φ (hypothèses [Himp], …, [Heq] ; pour
    ⊥ et =, à équivalence uniforme près), alors
    ils sont compatibles avec le tripos [fhd F] et avec ses structures de
    quantification et d'égalité. Concrètement :
    - ⇒, ∧, ∨, ⊤, ⊥ deviennent ceux de Φ ;
    - ∀ₛ et ∃ₛ deviennent ⋀ et ⋁ indexés par ⟦s⟧ ;
    - =ₛ devient l'égalité de Leibniz de Φ sur ⟦s⟧.

    On obtient un modèle de la logique intuitionniste d'ordre (n,p)
    ([frame_lmodel]). La correction prend la forme d'un théorème de
    **réalisabilité** ([frame_sound]) : à toute preuve correspond *une*
    évidence, uniforme en l'environnement, de la conjonction des hypothèses
    vers la conclusion. Pour F = [prop_frame], c'est la correction
    tarskienne usuelle. *)

From Category Require Import Lib Theory.Category Theory.Isomorphism Theory.Functor
  Structure.Terminal Structure.Cartesian Structure.Cartesian.Closed
  Functor.Structure.Cartesian Functor.Structure.Cartesian.Closed.
From Stdlib Require Import List.
Import ListNotations.
From SF.Syntax Require Import Spec Terms Vectors Syn.
From SF.Calculus Require Import System SynConv.
From SF.Logic Require Import Judgment Propositional.
From SF.Functional Require Import Arrow Graded.
From SF.Quantifiers Require Import Quant Order.
From SF.Models Require Import PSet Frame Semantics LLS Calculus Hyperdoctrine Logic Quantifiers
  Equality Order SetModels Tarski FrameModel.

Local Notation ι a := (Spec [] a).

Set Default Proof Using "All".

(** Deux familles de propositions *uniformément équivalentes* : une même
    évidence dans chaque sens, pour tous les points. C'est tout ce que
    demande la compatibilité avec le tripos ; l'égalité ≡ dans Φ en est un
    cas particulier ([fequiv_of_eq]). *)
Definition fequiv {F : frame} {X : Type} (f g : X -> pcar F) : Prop :=
  exists e1 e2, forall x, fent (F := F) (f x) e1 (g x) /\ fent (F := F) (g x) e2 (f x).

Lemma fequiv_of_eq {F : frame} {X : Type} (f g : X -> pcar F) : (forall x, f x ≡ g x) -> fequiv f g.
Proof.
  intros H. exists e_id, e_id. intros x. split; apply fent_of_eq; [apply H|apply peq_sym, H].
Qed.

Section FrameTarski.

Context (F : frame).
Context {Srt : Type} {Sym : spec Srt -> Type} {FS : Functional Sym} {G : Graded Sym}.
Context (CS : system Sym) (P : Srt) {n p : bound} {QI : Quantifiers Sym P n p}.
Context {HI : HasImp Sym P} {HA : HasAnd Sym P} {HO : HasOr Sym P} {HT : HasTop Sym P} {HB : HasBot Sym P}.

Local Notation L := (order_logic CS P (n := n) (p := p)).
Local Notation qs := (qsort Sym n p).
Local Notation form := (form Sym P).
Local Notation "φ —[ e ]→ ψ" := (fent (F := F) φ e ψ) (at level 70).

Context (So : Srt -> pset).
Context (Iy : forall σ, Sym σ -> ictx PSet So (dom σ) ~> So (cod σ)).
Context (Hc : forall Γ s (t u : Terms.tm Sym Γ s),
            conv CS t u -> stm PSet So Iy t (penv PSet So Γ) ≈ stm PSet So Iy u (penv PSet So Γ)).

Definition fmodel : cmodel (l_calc Sym L) PSet := lls_model CS PSet So Iy Hc.
Local Notation M := fmodel.
Local Notation sval := (sval So Iy).
Local Notation H := (fhd F).

Context (T0 : pmor (So P) F).

Definition ftruth : pmor (ictx PSet So [ι P]) F :=
  fmor (X := pprod punit (pexp punit (So P))) (fun w => T0 (snd w tt))
       (fun w w' E => pfun_proper T0 (proj2 E tt)).

Local Notation "⟦ φ ⟧" := (interp (L := L) M H ftruth φ).

Lemma finterp_at {Γ} (φ : form Γ) γ : ⟦φ⟧ γ ≡ T0 (sval φ γ).
Proof. exact (pfun_proper T0 (stm_ext0_at So Iy φ γ tt)). Qed.

(** Un élément de ⟦s⟧ vu dans ⟦[ι s]⟧ = 1 × ⟦s⟧^1, et réciproquement. *)
Definition pconst {s} (x : So s) : pexp punit (So s) :=
  Build_pmor punit (So s) (fun _ => x) (fun _ _ _ => peq_refl x).

Definition up1 s : pmor (So s) (pprod punit (pexp punit (So s))) :=
  Build_pmor (So s) (pprod punit (pexp punit (So s))) (fun x => (tt, pconst x))
             (fun x x' E => conj Logic.I (fun _ => E)).

Definition down1 s : pmor (pprod punit (pexp punit (So s))) (So s) :=
  Build_pmor (pprod punit (pexp punit (So s))) (So s) (fun w => snd w tt)
             (fun w w' E => proj2 E tt).

Lemma up_down s (w : pprod punit (pexp punit (So s))) : up1 s (down1 s w) ≡ w.
Proof. split; [exact Logic.I|]. intros []. apply peq_refl. Qed.

(** Interprétation standard des symboles logiques, relativement à T₀ ;
    pour ⊥ et l'égalité, une équivalence uniforme ([fequiv]) suffit. *)
Context (Himp : forall q, T0 (Iy _ c_imp q) ≡ fimp (T0 (snd q tt)) (T0 (snd (fst q) tt))).
Context (Hand : forall q, T0 (Iy _ c_and q) ≡ fand (T0 (snd q tt)) (T0 (snd (fst q) tt))).
Context (Hor : forall q, T0 (Iy _ c_or q) ≡ for_ (T0 (snd q tt)) (T0 (snd (fst q) tt))).
Context (Htop : forall q, T0 (Iy _ c_top q) ≡ ftop).
Context (Hbot : fequiv (fun q => T0 (Iy _ c_bot q)) (fun _ => fbot)).
Context (Hall : forall (k : qs) q,
            T0 (Iy _ (Order.q_all (projT1 k) (projT2 k)) q)
            ≡ fall (fun a : So (projT1 k) => T0 (snd q (up1 _ a)))).
Context (Hex : forall (k : qs) q,
            T0 (Iy _ (Order.q_ex (projT1 k) (projT2 k)) q)
            ≡ fex (fun a : So (projT1 k) => T0 (snd q (up1 _ a)))).
Context (Heq : forall (k : qs),
            fequiv (fun q => T0 (Iy _ (Order.q_eq (projT1 k) (projT2 k)) q))
                   (fun q => leib (snd q tt) (snd (fst q) tt))).

Lemma fbin_compat (c : Sym (Spec [ι P; ι P] P)) (op : F -> F -> F)
  (opH : forall X, pmor X F -> pmor X F -> pmor X F)
  (Eop : forall X (a b : pmor X F) x, opH X a b x = op (a x) (b x))
  (Hc' : forall q, T0 (Iy _ c q) ≡ op (T0 (snd q tt)) (T0 (snd (fst q) tt))) :
  bin_compat L PSet M H ftruth c opH.
Proof.
  intros Γ a b. split; apply fle_eq; intros γ; rewrite Eop.
  - exact (peq_trans (finterp_at (Bin c a b) γ)
             (Hc' (sargs PSet So Iy (@acons _ Sym Γ (ι P) _ a (@acons _ Sym Γ (ι P) _ b anil))
                     (penv PSet So Γ) γ))).
  - exact (peq_sym (peq_trans (finterp_at (Bin c a b) γ)
             (Hc' (sargs PSet So Iy (@acons _ Sym Γ (ι P) _ a (@acons _ Sym Γ (ι P) _ b anil))
                     (penv PSet So Γ) γ)))).
Qed.

Lemma fcst_compat (c : Sym (ι P)) (k : F) (kH : forall X, pmor X F)
  (Ek : forall X x, kH X x = k) (Hc' : forall q, T0 (Iy _ c q) ≡ k) :
  cst_compat L PSet M H ftruth c kH.
Proof.
  intros Γ. split; apply fle_eq; intros γ; rewrite Ek.
  - exact (peq_trans (finterp_at (Cst c) γ) (Hc' tt)).
  - exact (peq_sym (peq_trans (finterp_at (Cst c) γ) (Hc' tt))).
Qed.

Lemma fimp_compat : bin_compat L PSet M H ftruth c_imp (fun X => pimp).
Proof. exact (fbin_compat _ fimp (fun X => ft_imp F) (fun _ _ _ _ => eq_refl) Himp). Qed.
Lemma fand_compat : bin_compat L PSet M H ftruth c_and (fun X => pand).
Proof. exact (fbin_compat _ fand (fun X => ft_and F) (fun _ _ _ _ => eq_refl) Hand). Qed.
Lemma for_compat : bin_compat L PSet M H ftruth c_or (fun X => por).
Proof. exact (fbin_compat _ for_ (fun X => ft_or F) (fun _ _ _ _ => eq_refl) Hor). Qed.
Lemma ftop_compat : cst_compat L PSet M H ftruth c_top (fun X => ptop).
Proof. exact (fcst_compat _ ftop (fun X => ft_top F) (fun _ _ => eq_refl) Htop). Qed.
Lemma fbot_compat : cst_compat L PSet M H ftruth c_bot (fun X => pbot).
Proof.
  destruct Hbot as (e1 & e2 & He). intros Γ. split.
  - exists e1. intros γ. apply (fent_eq _ _ _ _ (peq_sym (finterp_at (Cst (Γ := Γ) c_bot) γ))). exact (proj1 (He tt)).
  - exists e2. intros γ. apply (fent_eq_r _ _ _ _ (peq_sym (finterp_at (Cst (Γ := Γ) c_bot) γ))). exact (proj2 (He tt)).
Qed.

(** *** Quantificateurs et égalité *)

Section Sort.
Variable k : qs.
Local Notation s := (projT1 k).

Lemma fpin_at {Γ} (φ : form (ι s :: Γ)) γ a :
  ⟦φ⟧ (pin L M Γ [ι s] (γ, a)) ≡ T0 (stm PSet So Iy φ (ext PSet So [ι s] (penv PSet So Γ)) (γ, a)).
Proof.
  eapply peq_trans; [apply finterp_at|].
  exact (pfun_proper T0 (peq_sym (stm_ext_penv_at So Iy [ι s] φ (γ, a)))).
Qed.

Lemma fall_compat : @all_compat _ _ L PSet _ _ _ M H ftruth s (fqstruct F L M s) (qall_inst k).
Proof.
  intros Γ φ. set (q := sargs PSet So Iy (@acons _ Sym Γ (Spec [ι s] P) _ φ anil) (penv PSet So Γ)).
  split.
  - exists (e_gen e_inst). intros γ. cbn.
    apply (fent_eq _ _ _ _ (peq_sym (peq_trans (finterp_at (@All _ Sym P s (qall_inst k) Γ φ) γ) (Hall k (q γ))))).
    apply (f_fall_map _ _ (down1 s)). intros w.
    eapply peq_trans; [|apply peq_sym, fpin_at].
    apply (pfun_proper T0). apply (pfun_proper (stm PSet So Iy φ _)).
    split; [apply peq_refl|apply up_down].
  - exists (e_gen e_inst). intros γ. cbn.
    apply (fent_eq_r _ _ _ _ (peq_sym (peq_trans (finterp_at (@All _ Sym P s (qall_inst k) Γ φ) γ) (Hall k (q γ))))).
    apply (f_fall_map _ _ (up1 s)). intros x. apply fpin_at.
Qed.

Lemma fex_compat : @ex_compat _ _ L PSet _ _ _ M H ftruth s (fqstruct F L M s) (qex_inst k).
Proof.
  intros Γ φ. set (q := sargs PSet So Iy (@acons _ Sym Γ (Spec [ι s] P) _ φ anil) (penv PSet So Γ)).
  split.
  - exists (e_exE e_exI). intros γ. cbn.
    apply (fent_eq _ _ _ _ (peq_sym (peq_trans (finterp_at (@Ex _ Sym P s (qex_inst k) Γ φ) γ) (Hex k (q γ))))).
    apply (f_fex_map _ _ (up1 s)). intros x. apply peq_sym, fpin_at.
  - exists (e_exE e_exI). intros γ. cbn.
    apply (fent_eq_r _ _ _ _ (peq_sym (peq_trans (finterp_at (@Ex _ Sym P s (qex_inst k) Γ φ) γ) (Hex k (q γ))))).
    apply (f_fex_map _ _ (down1 s)). intros w.
    eapply peq_trans; [apply fpin_at|].
    apply (pfun_proper T0). apply (pfun_proper (stm PSet So Iy φ _)).
    split; [apply peq_refl|apply peq_sym, up_down].
Qed.

Lemma feq_compat : @eq_compat _ _ L PSet _ _ _ M H ftruth s (feqstruct F L M s) (qeq_inst k).
Proof.
  intros Γ t u.
  set (q := sargs PSet So Iy (@acons _ Sym Γ (ι s) _ t (@acons _ Sym Γ (ι s) _ u anil)) (penv PSet So Γ)).
  destruct (Heq k) as (e1 & e2 & He). split.
  - exists (e_comp e1 (e_gen e_inst)). intros γ. cbn.
    apply (fent_eq _ _ _ _ (peq_sym (finterp_at (@Eq _ Sym P s (qeq_inst k) Γ t u) γ))).
    eapply f_comp; [exact (proj1 (He (q γ)))|].
    apply (fent_eq_r _ _ _ _ (leib_proper F _ _ _ _ (up_down s _) (up_down s _))).
    apply (f_leib_map F (up1 s)).
  - exists (e_comp (e_gen e_inst) e2). intros γ. cbn.
    apply (fent_eq_r _ _ _ _ (peq_sym (finterp_at (@Eq _ Sym P s (qeq_inst k) Γ t u) γ))).
    eapply f_comp; [apply (f_leib_map F (down1 s))|exact (proj2 (He (q γ)))].
Qed.

End Sort.

(** *** Le modèle *)

Definition frame_order_structure : order_structure L PSet M H ftruth := {|
  os_imp := fimp_compat; os_and := fand_compat; os_or := for_compat;
  os_top := ftop_compat; os_bot := fbot_compat;
  os_q := fun k => fqstruct F L M (projT1 k);
  os_all := fall_compat; os_ex := fex_compat;
  os_e := fun k => feqstruct F L M (projT1 k);
  os_eq := feq_compat
|}.

Definition frame_lmodel : lmodel L PSet := order_lmodel CS P PSet M H ftruth frame_order_structure.

(** La conjonction des hypothèses. *)
Fixpoint fconj (l : list (pcar F)) : F :=
  match l with
  | [] => ftop
  | φ :: l' => fand φ (fconj l')
  end.

Lemma mconj_at {Γ} (Ξ : list (form Γ)) γ :
  mconj M H ftruth Ξ γ ≡ fconj (map (fun χ => T0 (sval χ γ)) Ξ).
Proof.
  induction Ξ as [|χ Ξ IH]; cbn; [apply peq_refl|].
  apply fand_proper; [apply finterp_at|exact IH].
Qed.

(** **Correction (réalisabilité)** : une preuve de Ξ ⊢ φ donne une évidence
    uniforme de ⋀Ξ vers φ, en tout point de ⟦Γ⟧. *)
Theorem frame_sound Γ Ξ φ :
  provable L Γ Ξ φ ->
  exists e, forall γ, fconj (map (fun χ => T0 (sval χ γ)) Ξ) —[e]→ T0 (sval φ γ).
Proof.
  intros Hd. destruct (lmodel_sound frame_lmodel Γ Ξ φ Hd) as [e He].
  exists e. intros γ. apply (fent_proper F _ _ _ _ _ (mconj_at Ξ γ) (finterp_at φ γ)), He.
Qed.

(** Un énoncé clos prouvable est *réalisé* : ⊤ —e→ ⟦φ⟧. *)
Corollary frame_sound_closed φ :
  provable L [] [] φ -> exists e, ftop —[e]→ T0 (sval φ tt).
Proof. intros Hd. destruct (frame_sound _ _ _ Hd) as [e He]. exists e. apply He. Qed.

(** Un axiome (règle sans prémisse) réalisé uniformément, en tout point
    du contexte de ses métavariables, est sain. *)
Lemma fax_sound (Θ : ctx Srt) (φ : form Θ) :
  (exists e, forall δ : ictx PSet So Θ, ftop —[e]→ T0 (sval φ δ)) ->
  mrule_sound M H ftruth {| d_ctx := Θ; d_prems := []; d_concl := φ |}.
Proof.
  intros [e He] Γ Ξ v _. cbn [d_concl d_ctx].
  destruct (proj2 (interp_vsubst L PSet M H ftruth φ v)) as [e1 H1].
  exists (e_comp (e_const e) e1). intros γ.
  eapply f_comp; [|apply H1]. cbn.
  apply f_const. eapply fent_eq_r; [apply peq_sym, finterp_at|apply He].
Qed.

End FrameTarski.
