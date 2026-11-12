(** * V(E) ⊨ IZFε (théorème 2.2.2)

    Le modèle d'arbres V(E) au-dessus d'un cadre d'évidence E réalise
    IZFε : à toute preuve de Ξ ⊢ φ correspond une évidence uniforme de ⋀Ξ
    vers ⟦φ⟧. Hypothèses nommées (aucun axiome) :
    - Φ est essentiellement petit : [enc], [dec], [dec_enc] (pour P) ;
    - un combinateur de point fixe [yfix] (pour la ε-induction) ;
    - la collection [coll], propre, de spécification [coll_spec]
      (pour la collection, le remplacement et rec).

    Les règles logiques sont saines par [FrameTarski] ; chaque axiome par
    [fax_sound] et son réalisateur ([Axioms.v]), à ≡ près entre la valeur
    sémantique calculée et sa forme propre ([psolve]). *)

From Category Require Import Lib Theory.Category.
From Stdlib Require Import List.
Import ListNotations.
From SF.Syntax Require Import Spec Terms.
From SF.Calculus Require Import System Rules.
From SF.Logic Require Import Judgment Propositional.
From SF.Functional Require Import Arrow Graded.
From SF.Quantifiers Require Import Quant Order.
From SF.Models Require Import PSet Frame Semantics Hyperdoctrine Logic Order FrameModel Tarski FrameTarski.
From SF.VE Require Import Trees Base ND Real1 Cons Real2 Ind Coll Model Axioms CC DC.
From SF.SetTheory Require Import IZFe IZFeCC IZFeDC.

Local Notation ι a := (Spec [] a).

Set Default Proof Using "All".

Section Sound.

Context (F : frame).
Context (Φ0 : Type) (enc : pcar F -> Φ0) (dec : Φ0 -> pcar F).
Context (dec_enc : forall φ, dec (enc φ) ≡ φ).
Context (yfix : eexp F -> fev F).
Context (yfix_spec : forall a φ ψ, fent (F := F) φ (eeval F (yfix a) a) ψ -> fent (F := F) φ (yfix a) ψ).
Context (coll : forall T, (T -> Trees.V F) -> (Trees.V F -> Trees.V F -> pcar F) -> Trees.V F).
Context (coll_proper : forall T (xs xs' : T -> Trees.V F) ψ ψ', Rproper F ψ ->
           (forall t, teq F (xs t) (xs' t)) -> (forall x y, ψ x y ≡ ψ' x y) ->
           teq F (coll T xs ψ) (coll T xs' ψ')).
Context (coll_spec : forall T (xs : T -> Trees.V F) ψ, Rproper F ψ ->
           forall t β, exists s, ψ (xs t) β ≡ ψ (xs t) (sub F (coll T xs ψ) s)).

Local Notation "φ —[ e ]→ ψ" := (fent (F := F) φ e ψ) (at level 70).

Definition So' := So F.
Definition Iy' := Iy F Φ0 enc dec coll coll_proper.

Definition Hc : forall Γ s (t u : Terms.tm isym Γ s),
    conv C t u -> stm PSet So' Iy' t (penv PSet So' Γ) ≈ stm PSet So' Iy' u (penv PSet So' Γ) :=
  pset_generated (fun e : Empty_set => match e with end) So' Iy' (fun i => match i with end).

Definition T0 : pmor (So' Pr) F := pmor_id (So' Pr).

(** *** Les symboles logiques sont standard *)

Local Notation qs := (qsort isym 1 1).

Lemma Himp q : T0 (Iy' _ c_imp q) ≡ fimp (T0 (snd q tt)) (T0 (snd (fst q) tt)).
Proof. apply peq_refl. Qed.
Lemma Hand q : T0 (Iy' _ c_and q) ≡ fand (T0 (snd q tt)) (T0 (snd (fst q) tt)).
Proof. apply peq_refl. Qed.
Lemma Hor q : T0 (Iy' _ c_or q) ≡ for_ (T0 (snd q tt)) (T0 (snd (fst q) tt)).
Proof. apply peq_refl. Qed.
Lemma Htop q : T0 (Iy' _ c_top q) ≡ ftop.
Proof. apply peq_refl. Qed.
Lemma Hbot : fequiv (fun q => T0 (Iy' _ c_bot q)) (fun _ => fbot).
Proof. apply fequiv_of_eq. intros q. apply peq_refl. Qed.

Local Ltac qsort_cases k := destruct k as [[|] h]; [|exfalso; exact (Pr_not_q h)].

Lemma Hall (k : qs) q :
  T0 (Iy' _ (Order.q_all (projT1 k) (projT2 k)) q) ≡ fall (fun a : So' (projT1 k) => T0 (snd q (up1 So' _ a))).
Proof. qsort_cases k. apply peq_refl. Qed.
Lemma Hex (k : qs) q :
  T0 (Iy' _ (Order.q_ex (projT1 k) (projT2 k)) q) ≡ fex (fun a : So' (projT1 k) => T0 (snd q (up1 So' _ a))).
Proof. qsort_cases k. apply peq_refl. Qed.
Lemma Heq (k : qs) :
  fequiv (fun q => T0 (Iy' _ (Order.q_eq (projT1 k) (projT2 k)) q))
         (fun q => leib (snd q tt) (snd (fst q) tt)).
Proof. qsort_cases k. apply fequiv_of_eq. intros q. apply peq_refl. Qed.

Definition OS := frame_order_structure F C Pr So' Iy' Hc T0 Himp Hand Hor Htop Hbot Hall Hex Heq.

Local Notation M := (fmodel C Pr So' Iy' Hc).
Local Notation ftruth := (ftruth F Pr So' T0).
Local Notation sval := (sval So' Iy').

(** *** Valeur calculée et forme propre *)

Lemma b1_unfold f x : b1 F f x ≡ (f : pmor _ _) (tt, pconst So' (s := V) x).
Proof. apply peq_refl. Qed.
Lemma b2_unfold f x y : b2 F f x y ≡ (f : pmor _ _) ((tt, pconst So' (s := V) y), pconst So' (s := V) x).
Proof. apply peq_refl. Qed.
Lemma pair_peq {A B : pset} (a a' : A) (b b' : B) : a ≡ a' -> b ≡ b' -> @peq (pprod A B) (a, b) (a', b').
Proof. intros H1 H2. exact (conj H1 H2). Qed.
Lemma pc_peq (x : Vset F) (g : pexp punit (Vset F)) : (forall u, x ≡ (g : pmor _ _) u) -> @peq (pexp punit (Vset F)) (pconst So' (s := V) x) g.
Proof. intros H u. exact (H u). Qed.
Lemma tt_peq (u v : punit) : u ≡ v.
Proof. exact Logic.I. Qed.

(** On décompose selon la forme propre (à gauche) ; la valeur calculée (à
    droite) n'est réduite que par unification, en tête : le noyau n'a
    ainsi jamais à comparer de gros termes réduits. *)
Ltac psolve :=
  lazymatch goal with
  | |- Axioms.iff _ _ _ ≡ _ => unfold Axioms.iff; psolve
  | |- @peq _ (vrec F _ _ _) _ =>
      apply (vrec_proper F coll coll_proper); [apply b2_proper|intros ? ?; psolve|psolve]
  | |- Axioms.ExU _ _ ≡ _ => unfold Axioms.ExU; psolve
  | |- fimp _ _ ≡ _ => apply (fimp_proper F); psolve
  | |- fand _ _ ≡ _ => apply (fand_proper F); psolve
  | |- for_ _ _ ≡ _ => apply for_proper; psolve
  | |- fall _ ≡ _ => apply (fall_proper F); intro; psolve
  | |- fex _ ≡ _ => apply fex_proper; intro; psolve
  | |- eps F _ _ ≡ _ => apply (eps_proper F); psolve
  | |- veq F _ _ ≡ _ => apply (veq_proper F); psolve
  | |- vmem F _ _ ≡ _ => apply (vmem_proper F); psolve
  | |- vsub F _ _ ≡ _ => apply (vsub_proper F); psolve
  | |- veqv F _ _ ≡ _ => apply (veqv_proper F); psolve
  | |- pfun (b1 F ?f) ?x ≡ _ => refine (peq_trans (b1_unfold f x) _); psolve
  | |- b2 F ?f ?x ?y ≡ _ => refine (peq_trans (b2_unfold f x y) _); psolve
  | |- @peq ?A (pfun ?f ?x) ?R =>
      let R' := eval hnf in R in change (@peq A (pfun f x) R'); apply pfun_proper; psolve
  | |- teq F (vsuc F _) _ => unfold vsuc; psolve
  | |- teq F (vunion F _) _ => apply (vunion_proper F); psolve
  | |- teq F (vpair F _ _) _ => apply (vpair_proper F); psolve
  | |- teq F (vpower F _ _ _) _ => apply (vpower_proper F Φ0 dec); psolve
  | |- teq F (vsep F _ _) _ => apply (vsep_proper F); [psolve|intro; psolve]
  | |- teq F (vrepl F _ _ _) _ =>
      apply (vrepl_proper F coll coll_proper); [apply b2_proper|psolve|intros ? ?; psolve]
  | |- teq F (vrec F _ _ _) _ =>
      apply (vrec_proper F coll coll_proper); [apply b2_proper|intros ? ?; psolve|psolve]
  | |- teq F _ _ => exact (teq_refl F _)
  | |- @peq ?A (?a, ?b) ?R =>
      let R' := eval hnf in R in change (@peq A (a, b) R'); apply pair_peq; psolve
  | |- @peq _ (pconst _ _) _ => apply pc_peq; intro; psolve
  | |- @peq _ tt _ => apply tt_peq
  | |- @peq (Vset F) _ _ => exact (teq_refl F _)
  | |- _ ≡ _ =>
      first [ exact (peq_refl _)
            | let u := fresh "u" in intro u;
              lazymatch goal with |- @peq ?B ?L ?R =>
                let L' := eval cbn in L in change (@peq B L' R) end; psolve
            ]
  end.

Lemma ax_real (Θ : ctx isort) (φ : form Θ) (S : ictx PSet So' Θ -> pcar F) :
  (exists e, forall δ, ftop —[e]→ S δ) -> (forall δ, S δ ≡ T0 (sval φ δ)) ->
  mrule_sound M (fhd F) ftruth {| d_ctx := Θ; d_prems := []; d_concl := φ |}.
Proof.
  intros [e He] HS. apply (fax_sound F C Pr So' Iy' Hc T0 Himp Hand Hor Htop Hbot Hall Hex Heq).
  exists e. intros δ. exact (fent_eq_r _ _ _ _ (HS δ) (He δ)).
Qed.

Local Ltac use R := destruct (R F Φ0 enc dec dec_enc yfix yfix_spec coll coll_proper coll_spec) as [e He]; exists e; intros δ.

(** La vérification du noyau (Qed) compare la valeur calculée et la forme
    propre ; on lui fait déplier la sémantique avant les constructions. *)
Strategy 1000 [eps veq vmem vsub veqv vsep vrepl vrec vrecS vrecB Wset vunion vpair vpower vempty vomega
               Trees.sub Trees.idx Trees.lbl Trees.lab fimp fand for_ fall fex fbot ftop].

Local Notation B1 f := (b1 F f).
Local Notation B2 f := (b2 F f).
Local Notation B2P f := (b2_proper F f).

Lemma s_mem : mrule_sound M (fhd F) ftruth (izfm_rules A_mem).
Proof.
  eapply ax_real.
  - use R_mem. exact (He (snd δ tt) (snd (fst δ) tt)).
  - intros δ. cbv beta. psolve.
Qed.

Lemma s_sub : mrule_sound M (fhd F) ftruth (izfm_rules A_sub).
Proof.
  eapply ax_real.
  - use R_sub. exact (He (snd δ tt) (snd (fst δ) tt)).
  - intros δ. cbv beta. psolve.
Qed.

Lemma s_eqv : mrule_sound M (fhd F) ftruth (izfm_rules A_eqv).
Proof.
  eapply ax_real.
  - use R_eqv. exact (He (snd δ tt) (snd (fst δ) tt)).
  - intros δ. cbv beta. psolve.
Qed.

Lemma s_pair : mrule_sound M (fhd F) ftruth (izfm_rules A_pair).
Proof.
  eapply ax_real.
  - use R_pair. exact (He (snd δ tt) (snd (fst δ) tt) (snd (fst (fst δ)) tt)).
  - intros δ. cbv beta. psolve.
Qed.

Lemma s_union : mrule_sound M (fhd F) ftruth (izfm_rules A_union).
Proof.
  eapply ax_real.
  - use R_union. exact (He (snd δ tt) (snd (fst δ) tt)).
  - intros δ. cbv beta. psolve.
Qed.

Lemma s_power : mrule_sound M (fhd F) ftruth (izfm_rules A_power).
Proof.
  eapply ax_real.
  - use R_power. exact (He (snd δ tt) (snd (fst δ) tt)).
  - intros δ. cbv beta. psolve.
Qed.

Lemma s_coll : mrule_sound M (fhd F) ftruth (izfm_rules A_coll).
Proof.
  eapply ax_real.
  - use R_coll. exact (He (snd δ tt) (B2 (snd (fst δ))) (B2P (snd (fst δ)))).
  - intros δ. cbv beta. psolve.
Qed.

Lemma s_sep : mrule_sound M (fhd F) ftruth (izfm_rules A_sep).
Proof.
  eapply ax_real.
  - use R_sep. exact (He (snd δ tt) (snd (fst δ) tt) (B1 (snd (fst (fst δ))))).
  - intros δ. cbv beta. psolve.
Qed.

Lemma s_empty : mrule_sound M (fhd F) ftruth (izfm_rules A_empty).
Proof.
  eapply ax_real.
  - use R_empty. exact (He (snd δ tt)).
  - intros δ. cbv beta. psolve.
Qed.

Lemma s_omega : mrule_sound M (fhd F) ftruth (izfm_rules A_omega).
Proof.
  eapply ax_real.
  - use R_omega. exact (He (snd δ tt)).
  - intros δ. cbv beta. psolve.
Qed.

Lemma s_ind : mrule_sound M (fhd F) ftruth (izfm_rules A_ind).
Proof.
  eapply ax_real.
  - use R_ind. exact (He (B1 (snd δ))).
  - intros δ. cbv beta. psolve.
Qed.

Lemma s_rec : mrule_sound M (fhd F) ftruth (izfe_extra A_rec).
Proof.
  eapply ax_real.
  - use R_rec. exact (He (fun x => B1 (snd δ) x) (B2 (snd (fst δ))) (B2P (snd (fst δ)))).
  - intros δ. cbv beta. psolve.
Qed.

Lemma s_repl : mrule_sound M (fhd F) ftruth (izfe_extra A_repl).
Proof.
  eapply ax_real.
  - use R_repl. exact (He (snd δ tt) (B2 (snd (fst δ))) (B2P (snd (fst δ)))).
  - intros δ. cbv beta. psolve.
Qed.

Lemma s_sep_power : mrule_sound M (fhd F) ftruth (izfe_extra A_sep_power).
Proof.
  eapply ax_real.
  - use R_sep_power. exact (He (snd δ tt) (B1 (snd (fst δ)))).
  - intros δ. cbv beta. psolve.
Qed.

Lemma s_power_sub : mrule_sound M (fhd F) ftruth (izfe_extra A_power_sub).
Proof.
  eapply ax_real.
  - use R_power_sub. exact (He (snd δ tt) (snd (fst δ) tt)).
  - intros δ. cbv beta. psolve.
Qed.

Lemma izfm_sound i : mrule_sound M (fhd F) ftruth (izfm_rules i).
Proof.
  destruct i; [exact s_mem|exact s_sub|exact s_eqv|exact s_pair|exact s_union|exact s_power
              |exact s_coll|exact s_sep|exact s_empty|exact s_omega|exact s_ind].
Qed.

Lemma izfe_sound i : mrule_sound M (fhd F) ftruth (izfe_extra i).
Proof. destruct i; [exact s_rec|exact s_repl|exact s_sep_power|exact s_power_sub]. Qed.

(** *** Le théorème *)

Definition IZFeL : logic isym := {| l_calc := C; l_prop := Pr; l_idx := _; l_rules := RIZFe |}.

Lemma rules_sound i : mrule_sound (L := IZFeL) M (fhd F) ftruth (l_rules isym IZFeL i).
Proof.
  destruct i as [[i|i]|i].
  - exact (iorder_sound (order_logic C Pr (n := 1) (p := 1)) PSet M (fhd F) ftruth OS i).
  - apply izfm_sound.
  - apply izfe_sound.
Qed.

(** **V(E) ⊨ IZFε** : toute preuve de Ξ ⊢ φ dans IZFε donne une évidence
    uniforme de ⋀⟦Ξ⟧ vers ⟦φ⟧, en tout point γ de ⟦Γ⟧. *)
Theorem ve_sound Γ Ξ φ :
  IZFe Γ Ξ φ ->
  exists e, forall γ, fconj F (map (fun χ => T0 (sval χ γ)) Ξ) —[e]→ T0 (sval φ γ).
Proof.
  intros Hd. destruct (soundness IZFeL PSet M (fhd F) ftruth rules_sound Γ Ξ φ Hd) as [e He].
  exists e. intros γ.
  apply (fent_proper F _ _ _ _ _
           (mconj_at F C Pr So' Iy' Hc T0 Himp Hand Hor Htop Hbot Hall Hex Heq Ξ γ)
           (finterp_at F C Pr So' Iy' Hc T0 φ γ)), He.
Qed.

(** Un énoncé clos prouvable dans IZFε est réalisé. *)
Corollary ve_sound_closed φ : IZFe [] [] φ -> exists e, ftop —[e]→ T0 (sval φ tt).
Proof. intros Hd. destruct (ve_sound _ _ _ Hd) as [e He]. exists e. apply He. Qed.

(** *** Le choix dénombrable *)

(** Si le cadre valide le choix dénombrable au niveau du tripos
    ([frame_cc], voir [CC.v]), V(E) réalise IZFε + CC (forme bornée). *)
Section CCs.
Context (m : fev F) (Hcc : frame_cc F m).

Lemma s_cc : mrule_sound M (fhd F) ftruth A_cc.
Proof.
  eapply ax_real.
  - destruct (R_cc F m Hcc) as [e He]. exists e. intros δ.
    exact (He (snd δ tt) (B2 (snd (fst δ))) (B2P (snd (fst δ)))).
  - intros δ. cbv beta. unfold ccS, ccHyp, ccTot, ccFun, ccSub, CC.vop. psolve.
Qed.

Definition IZFeCL : logic isym := {| l_calc := C; l_prop := Pr; l_idx := _; l_rules := RIZFeC |}.

Lemma rules_sound_cc i : mrule_sound (L := IZFeCL) M (fhd F) ftruth (l_rules isym IZFeCL i).
Proof. destruct i as [i|[]]; [apply (rules_sound i)|apply s_cc]. Qed.

(** **V(E) ⊨ IZFε + CC.** *)
Theorem ve_sound_cc Γ Ξ φ :
  IZFeC Γ Ξ φ ->
  exists e, forall γ, fconj F (map (fun χ => T0 (sval χ γ)) Ξ) —[e]→ T0 (sval φ γ).
Proof.
  intros Hd. destruct (soundness IZFeCL PSet M (fhd F) ftruth rules_sound_cc Γ Ξ φ Hd) as [e He].
  exists e. intros γ.
  apply (fent_proper F _ _ _ _ _
           (mconj_at F C Pr So' Iy' Hc T0 Himp Hand Hor Htop Hbot Hall Hex Heq Ξ γ)
           (finterp_at F C Pr So' Iy' Hc T0 φ γ)), He.
Qed.

End CCs.

(** *** Le choix dépendant *)

(** Si le cadre valide DC au niveau du tripos ([frame_dc], voir [DC.v]),
    V(E) réalise IZFε + DC (forme bornée). *)
Section DCs.
Context (m : fev F) (Hdc : frame_dc F m).

Lemma s_dc : mrule_sound M (fhd F) ftruth A_dc.
Proof.
  eapply ax_real.
  - destruct (R_dc F m Hdc) as [e He]. exists e. intros δ.
    exact (He (snd δ tt) (B2 (snd (fst δ))) (B2P (snd (fst δ)))).
  - intros δ. cbv beta. unfold dcS, dcHyp, dcTot, dcStart, dcStep, ccFun, ccSub, CC.vop. psolve.
Qed.

Definition IZFeDL : logic isym := {| l_calc := C; l_prop := Pr; l_idx := _; l_rules := RIZFeD |}.

Lemma rules_sound_dc i : mrule_sound (L := IZFeDL) M (fhd F) ftruth (l_rules isym IZFeDL i).
Proof. destruct i as [i|[]]; [apply (rules_sound i)|apply s_dc]. Qed.

(** **V(E) ⊨ IZFε + DC.** *)
Theorem ve_sound_dc Γ Ξ φ :
  IZFeD Γ Ξ φ ->
  exists e, forall γ, fconj F (map (fun χ => T0 (sval χ γ)) Ξ) —[e]→ T0 (sval φ γ).
Proof.
  intros Hd. destruct (soundness IZFeDL PSet M (fhd F) ftruth rules_sound_dc Γ Ξ φ Hd) as [e He].
  exists e. intros γ.
  apply (fent_proper F _ _ _ _ _
           (mconj_at F C Pr So' Iy' Hc T0 Himp Hand Hor Htop Hbot Hall Hex Heq Ξ γ)
           (finterp_at F C Pr So' Iy' Hc T0 φ γ)), He.
Qed.

End DCs.

End Sound.

(** ** Cohérence de IZFε (relativement à la collection)

    Dans le cadre [prop_frame] (Φ = Prop, E = unit), Φ est petit (Φ₀ :=
    Prop) et tout combinateur convient comme point fixe ; seule la
    collection reste une hypothèse. ⟦⊥⟧ = ∀P. P n'est pas réalisé. *)

Section PropModel.

Context (coll : forall T, (T -> Trees.V prop_frame) -> (Trees.V prop_frame -> Trees.V prop_frame -> Prop) -> Trees.V prop_frame).
Context (coll_proper : forall T (xs xs' : T -> Trees.V prop_frame) ψ ψ', Rproper prop_frame ψ ->
           (forall t, teq prop_frame (xs t) (xs' t)) -> (forall x y, ψ x y ≡ ψ' x y) ->
           teq prop_frame (coll T xs ψ) (coll T xs' ψ')).
Context (coll_spec : forall T (xs : T -> Trees.V prop_frame) ψ, Rproper prop_frame ψ ->
           forall t β, exists s, ψ (xs t) β ≡ ψ (xs t) (sub prop_frame (coll T xs ψ) s)).

Theorem izfe_consistent : ~ IZFe [] [] (Bot (Γ := [])).
Proof.
  intros Hd.
  destruct (ve_sound_closed prop_frame Prop (fun φ => φ) (fun φ => φ) (fun φ => peq_refl (p := PropS) φ)
              (fun _ => tt) (fun _ _ _ H => H) coll coll_proper coll_spec _ Hd) as [e He].
  exact (proj1 (prop_fall _) (He Logic.I) False).
Qed.

End PropModel.
