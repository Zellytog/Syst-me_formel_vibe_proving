(** * Quantificateurs dans les modèles

    Pour une sorte s, une **structure de quantification** sur s dans un
    modèle (M, H, T) est la donnée, pour chaque contexte Γ, de deux
    opérations ∀_Γ, ∃_Γ : H(M(ι s :: Γ)) → H(M Γ), adjointes à droite et
    à gauche à la réindexation le long de la projection
    π_Γ = M(wk) : M(Γ × [ι s]) → M Γ, et stables par réindexation
    (la condition de **Beck–Chevalley** ci-dessous).

    C'est ici que l'ordre (n,p) intervient : on ne demande une telle
    structure que pour les sortes *quantifiables*. Les sortes du bord sont
    interprétées, mais aucun adjoint n'est exigé le long de leurs
    projections.

    Si les symboles ∀_s et ∃_s sont **compatibles** avec ces opérations
    (⟦∀_s φ⟧ ≡ ∀_Γ ⟦φ⟧), les règles ∀I, ∀E, ∃I, ∃E sont saines
    ([all_sound], [ex_sound]). Pour ∃E, la réciprocité de Frobenius n'est
    pas une hypothèse : elle découle de l'adjonction et de ce que la
    réindexation préserve ⇒. Enfin, le modèle syntaxique porte une telle
    structure pour toute sorte dont la logique contient les règles
    ([syn_qstruct]). *)

From Category Require Import Lib Theory.Category Theory.Functor
  Structure.Terminal Structure.Cartesian Structure.Cartesian.Closed.
From Stdlib Require Import List.
Import ListNotations.
From SF.Syntax Require Import Spec Terms Renaming Traversal Eta Vectors Syn.
From SF.Calculus Require Import System SynConv.
From SF.Logic Require Import Judgment Propositional.
From SF.Functional Require Import Arrow.
From SF.Quantifiers Require Import Quant.
From SF.Models Require Import Calculus Hyperdoctrine Logic Completeness.

Local Notation ι a := (Spec [] a).


(** ** Faits syntaxiques *)

Section SynFacts.
Context {Srt : Type} {Sym : spec Srt -> Type}.

(** La projection Γ × [ι s] → Γ de la catégorie syntaxique. *)
Definition wkv (s : Srt) (Γ : ctx Srt) : vec Sym Γ (ι s :: Γ) := sexl Sym Γ [ι s].

Lemma vsubst_wkv {s Γ b} (t : Terms.tm Sym Γ b) : vsubst t (wkv s Γ) = ren_tm t (wk [ι s]).
Proof.
  rewrite ren_as_vsubst. f_equal. apply vec_ext; intros σ x. unfold vget, wkv, sexl.
  rewrite aget_etas, aget_vpre, aget_vid. reflexivity.
Qed.

Lemma wkv_inst1 {s Γ} (t : Terms.tm Sym Γ s) : vcomp (wkv s Γ) (inst1 t) = vid Γ.
Proof.
  apply vec_ext; intros σ x. unfold vget. rewrite aget_vcomp. unfold wkv, sexl.
  rewrite aget_etas, vsubst_eta. cbn [vr aget atl]. reflexivity.
Qed.

(** Affaiblir sous le lieur, puis remettre la variable 0 : identité. *)
Lemma vsubst_shift {Γ} a b (u : Terms.tm Sym (ι a :: Γ) b) :
  vsubst (ren_tms (σ := Spec [ι a] b) u (wk [ι a])) (inst1 (var0 vz)) = u.
Proof.
  unfold ren_tms; rewrite vsubst_ren. rewrite <- (vsubst_vid u) at 2. f_equal.
  apply vec_ext; intros σ x; unfold vget; rewrite aget_vpre.
  vcase x; autorewrite with vsimpl; [|reflexivity].
  revert σ z. refine (var_inv _ _ _); [reflexivity|intros σ' y; destruct (var_nil y)].
Qed.

End SynFacts.

(** ** Structures de quantification *)

Section QStruct.
Context {Srt : Type} {Sym : spec Srt -> Type} (L : logic Sym).
Context (C : Category) {CT : @Terminal C} {CC : @Cartesian C} {CL : @Closed C CC}.
Context (M : cmodel (l_calc Sym L) C) (H : hyperdoctrine C) (T : pred H (M [ι (l_prop Sym L)])).
Context (s : Srt).

Local Notation P := (l_prop Sym L).
Local Notation form := (form Sym P).
Local Notation "p ≤ q" := (ple (h := H) p q) (at level 70).
Local Notation "⟦ φ ⟧" := (interp M H T φ).
Local Notation π Γ := (fmap[cm_fun M] (wkv (Sym := Sym) s Γ)).
Local Notation σφ := (Spec [ι s] P).

Record qstruct := {
  q_all : forall Γ, pred H (M (ι s :: Γ)) -> pred H (M Γ);
  q_ex : forall Γ, pred H (M (ι s :: Γ)) -> pred H (M Γ);
  q_all_adj : forall Γ (q : pred H (M Γ)) p, reidx (π Γ) q ≤ p <-> q ≤ q_all Γ p;
  q_ex_adj : forall Γ p (q : pred H (M Γ)), q_ex Γ p ≤ q <-> p ≤ reidx (π Γ) q;
  q_all_bc : forall Γ Δ (v : vec Sym Γ Δ) p,
      reidx (fmap[cm_fun M] v) (q_all Γ p) ≤ q_all Δ (reidx (fmap[cm_fun M] (vup [ι s] v)) p) /\
      q_all Δ (reidx (fmap[cm_fun M] (vup [ι s] v)) p) ≤ reidx (fmap[cm_fun M] v) (q_all Γ p);
  q_ex_bc : forall Γ Δ (v : vec Sym Γ Δ) p,
      reidx (fmap[cm_fun M] v) (q_ex Γ p) ≤ q_ex Δ (reidx (fmap[cm_fun M] (vup [ι s] v)) p) /\
      q_ex Δ (reidx (fmap[cm_fun M] (vup [ι s] v)) p) ≤ reidx (fmap[cm_fun M] v) (q_ex Γ p)
}.

Context (Q : qstruct).

Definition all_compat {HA : HasForall Sym P s} :=
  forall Γ (φ : form (ι s :: Γ)), ⟦All s φ⟧ ≤ q_all Q Γ ⟦φ⟧ /\ q_all Q Γ ⟦φ⟧ ≤ ⟦All s φ⟧.
Definition ex_compat {HE : HasExists Sym P s} :=
  forall Γ (φ : form (ι s :: Γ)), ⟦Ex s φ⟧ ≤ q_ex Q Γ ⟦φ⟧ /\ q_ex Q Γ ⟦φ⟧ ≤ ⟦Ex s φ⟧.

(** ** Lemmes de réindexation *)

(** L'affaiblissement est la réindexation le long de la projection. *)
Lemma interp_wk {Γ} (χ : form Γ) :
  ⟦ren_tm χ (wk [ι s])⟧ ≤ reidx (π Γ) ⟦χ⟧ /\ reidx (π Γ) ⟦χ⟧ ≤ ⟦ren_tm χ (wk [ι s])⟧.
Proof. rewrite <- vsubst_wkv. apply interp_vsubst. Qed.

Lemma mconj_wk {Γ} (Ξ : list (form Γ)) : reidx (π Γ) (mconj M H T Ξ) ≤ mconj M H T (wk_list [ι s] Ξ).
Proof.
  induction Ξ as [|χ Ξ IH]; cbn [mconj wk_list map].
  - apply top_max.
  - apply and_intro.
    + eapply ple_trans; [apply reidx_mono, and_l|apply interp_wk].
    + eapply ple_trans; [apply reidx_mono, and_r|exact IH].
Qed.

(** Instancier puis affaiblir ne fait rien. *)
Lemma reidx_retract {Γ} (t : Terms.tm Sym Γ s) (q : pred H (M Γ)) :
  reidx (fmap[cm_fun M] (inst1 t)) (reidx (π Γ) q) ≤ q /\ q ≤ reidx (fmap[cm_fun M] (inst1 t)) (reidx (π Γ) q).
Proof.
  assert (E : π Γ ∘ fmap[cm_fun M] (inst1 t) ≈ id).
  { rewrite <- fmap_comp. rewrite <- fmap_id. apply fmap_respects. simpl. rewrite wkv_inst1. apply arel_refl. }
  destruct (reidx_comp _ H (π Γ) (fmap[cm_fun M] (inst1 t)) q) as [C1 C2].
  destruct (reidx_id _ H q) as [I1 I2]. split.
  - eapply ple_trans; [exact C2|]. eapply ple_trans; [apply reidx_proper, E|exact I1].
  - eapply ple_trans; [exact I2|]. eapply ple_trans; [apply reidx_proper; symmetry; exact E|exact C1].
Qed.

Lemma ple_of_eq {X} (p q : pred H X) : p = q -> p ≤ q.
Proof. intros ->; apply ple_refl. Qed.

Lemma interp_eq {Γ} (φ ψ : form Γ) : φ = ψ -> ⟦φ⟧ ≤ ⟦ψ⟧.
Proof. intros ->; apply ple_refl. Qed.

Lemma all_counit {Γ} (p : pred H (M (ι s :: Γ))) : reidx (π Γ) (q_all Q Γ p) ≤ p.
Proof. apply (q_all_adj Q), ple_refl. Qed.

Lemma ex_unit {Γ} (p : pred H (M (ι s :: Γ))) : p ≤ reidx (π Γ) (q_ex Q Γ p).
Proof. apply (q_ex_adj Q), ple_refl. Qed.

(** ** Correction des règles *)

Theorem all_sound {HA : HasForall Sym P s} (Hc : all_compat) i : mrule_sound M H T (all_rules s i).
Proof.
  intros Γ Ξ v Hp. unfold mvalid. destruct i; cbn [all_rules mkr d_prems d_concl d_ctx] in *.
  - (* ∀I *)
    pose proof (Hp _ (or_introl eq_refl)) as K. unfold mvalid, inst_hyps, inst_goal in K.
    cbn [p_ext p_hyps p_goal premx vsubst_list map app] in K.
    eapply ple_trans; [|apply interp_eq; symmetry; unfold All; exact (vsubst_Qnt_eta c_all vz v)].
    eapply ple_trans; [|apply (Hc Γ (aget vz v))]. apply (q_all_adj Q). eapply ple_trans; [apply mconj_wk|].
    eapply ple_trans; [exact K|]. apply interp_eq. exact (vsubst_eta_up [ι s] P vz v).
  - (* ∀E *)
    pose proof (Hp _ (or_introl eq_refl)) as K. apply prem_valid in K. cbn [vsubst_list map app] in K.
    unfold mvalid in K.
    eapply ple_trans; [|apply interp_eq; symmetry; exact (vsubst_app1 vz (vs vz) v)].
    eapply ple_trans; [exact K|].
    eapply ple_trans; [apply interp_eq; unfold All; exact (vsubst_Qnt_eta c_all vz v)|].
    eapply ple_trans; [apply (Hc Γ (aget vz v))|].
    eapply ple_trans; [apply (proj2 (reidx_retract (aget (vs vz) v) _))|].
    eapply ple_trans; [apply reidx_mono, all_counit|]. apply interp_vsubst.
Qed.

Theorem ex_sound {HE : HasExists Sym P s} (Hc : ex_compat) i : mrule_sound M H T (ex_rules s i).
Proof.
  intros Γ Ξ v Hp. unfold mvalid. destruct i; cbn [ex_rules mkr d_prems d_concl d_ctx] in *.
  - (* ∃I *)
    pose proof (Hp _ (or_introl eq_refl)) as K. apply prem_valid in K. cbn [vsubst_list map app] in K.
    unfold mvalid in K.
    eapply ple_trans; [|apply interp_eq; symmetry; unfold Ex; exact (vsubst_Qnt_eta c_ex vz v)].
    eapply ple_trans; [exact K|].
    eapply ple_trans; [apply interp_eq; exact (vsubst_app1 vz (vs vz) v)|].
    eapply ple_trans; [apply interp_vsubst|].
    eapply ple_trans; [apply reidx_mono, ex_unit|].
    eapply ple_trans; [apply (proj1 (reidx_retract (aget (vs vz) v) _))|]. apply (Hc Γ (aget vz v)).
  - (* ∃E *)
    pose proof (Hp _ (or_introl eq_refl)) as K1. apply prem_valid in K1. cbn [vsubst_list map app] in K1.
    unfold mvalid in K1.
    pose proof (Hp _ (or_intror (or_introl eq_refl))) as K2. unfold mvalid, inst_hyps, inst_goal in K2.
    cbn [p_ext p_hyps p_goal premx vsubst_list map app mconj] in K2.
    assert (E2 : vsubst (var0 (Θ := [ι s] ++ [σφ; ι P]) (vs (vs vz))) (vup [ι s] v)
                 = ren_tm (aget (vs vz) v) (wk [ι s])).
    { etransitivity; [exact (vsubst_var0 (vs (vs vz)) _)|].
      unfold vup, vren; cbn [vcat ahd atl aget vmap]. apply ren_tms_nil. }
    eapply ple_trans; [|apply interp_eq; symmetry; exact (vsubst_var0 (vs vz) v)].
    set (φ := aget vz v) in *. set (χ := aget (vs vz) v) in *. set (X := mconj M H T Ξ) in *.
    apply (ple_trans _ (pand (q_ex Q Γ ⟦φ⟧) X)).
    + apply and_intro; [|apply ple_refl].
      eapply ple_trans; [exact K1|].
      eapply ple_trans; [apply interp_eq; unfold Ex; exact (vsubst_Qnt_eta c_ex vz v)|].
      apply (Hc Γ φ).
    + apply imp_adj. apply (q_ex_adj Q).
      eapply ple_trans; [|apply reidx_imp]. apply imp_adj.
      eapply ple_trans; [apply (and_mono _ _ _ _ (ple_refl _) (mconj_wk Ξ))|].
      eapply ple_trans; [|eapply ple_trans; [exact K2|]].
      * apply and_mono; [|apply ple_refl]. apply interp_eq. symmetry.
        exact (vsubst_eta_up [ι s] P vz v).
      * eapply ple_trans; [apply interp_eq; exact E2|apply interp_wk].
Qed.

End QStruct.


(** ** Le modèle syntaxique porte les structures de quantification *)

Set Default Proof Using "All".

Section SynQuant.
Context {Srt : Type} {Sym : spec Srt -> Type} (L : logic Sym).

Local Notation P := (l_prop Sym L).
Local Notation CS := (l_calc Sym L).
Local Notation R := (l_rules Sym L).
Local Notation form := (form Sym P).
Local Notation "Ξ ⊢ φ" := (deriv CS P R _ Ξ φ) (at level 70).
Local Notation SM := (syn_model CS).

Context {HI : HasImp Sym P} {HA : HasAnd Sym P} {HO : HasOr Sym P} {HT : HasTop Sym P} {HB : HasBot Sym P}.
Context {HR : Includes R ipc_rules}.
Context (s : Srt) {HF : HasForall Sym P s} {HE : HasExists Sym P s}.
Context {HRA : Includes R (all_rules s)} {HRE : Includes R (ex_rules s)}.

Local Notation HD := (syn_hd L (HR := HR)).
Local Notation TT := (syn_truth L).

Lemma wk_single {Γ} (q : form Γ) : vsubst_list [q] (wkv s Γ) = wk_list [ι s] [q].
Proof. cbn. rewrite vsubst_wkv. reflexivity. Qed.

Lemma vsubst_All {Γ Δ} (φ : form (ι s :: Γ)) (v : vec Sym Γ Δ) :
  vsubst (All s φ) v = All s (vsubst φ (vup [ι s] v)).
Proof. unfold All. rewrite vsubst_Qnt, vsubst_tms_vup. reflexivity. Qed.

Lemma vsubst_Ex {Γ Δ} (φ : form (ι s :: Γ)) (v : vec Sym Γ Δ) :
  vsubst (Ex s φ) v = Ex s (vsubst φ (vup [ι s] v)).
Proof. unfold Ex. rewrite vsubst_Qnt, vsubst_tms_vup. reflexivity. Qed.

Local Ltac hyp := apply d_ax; simpl; auto.

Definition syn_qstruct : qstruct L (SynConv CS) SM HD s.
Proof.
  refine (@Build_qstruct _ _ L (SynConv CS) _ _ _ SM HD s
            (fun Γ (φ : form (ι s :: Γ)) => All s φ) (fun Γ (φ : form (ι s :: Γ)) => Ex s φ) _ _ _ _).
  - (* ∀ ⊣ *) intros Γ q φ. cbn. rewrite vsubst_wkv. split; intros K.
    + apply (all_I CS P R s [q] φ). exact K.
    + apply (deriv_wk CS P R [ι s]) in K. cbn [wk_list map] in K.
      change (ren_tm (All s φ) (wk [ι s])) with (All s (ren_tms (σ := Spec [ι s] P) φ (wk [ι s]))) in K.
      apply (all_E CS P R s _ _ (var0 vz)) in K.
      refine (eq_rect _ (fun ψ => deriv CS P R _ _ ψ) K _ _). apply vsubst_shift.
  - (* ∃ ⊣ *) intros Γ φ q. cbn. rewrite vsubst_wkv. split; intros K.
    + apply (deriv_wk CS P R [ι s]) in K. cbn [wk_list map] in K.
      change (ren_tm (Ex s φ) (wk [ι s])) with (Ex s (ren_tms (σ := Spec [ι s] P) φ (wk [ι s]))) in K.
      apply (deriv_cut CS P R (φ := Ex s (ren_tms (σ := Spec [ι s] P) φ (wk [ι s])))).
      * apply (ex_I CS P R s _ _ (var0 vz)).
        apply (eq_rect φ (fun ψ => deriv CS P R _ [φ] ψ)); [hyp|symmetry; apply vsubst_shift].
      * eapply deriv_weaken; [exact K|]. intros x [<-|[]]; left; reflexivity.
    + apply (ex_E CS P R s [Ex s φ] φ q); [hyp|].
      eapply deriv_weaken; [exact K|]. intros x [<-|[]]; left; reflexivity.
  - (* BC ∀ *) intros Γ Δ v φ.
    split; (eapply (eq_rect _ (fun ψ => deriv CS P R _ _ ψ)); [apply d_ax; left; reflexivity|]);
      [apply vsubst_All|symmetry; apply vsubst_All].
  - (* BC ∃ *) intros Γ Δ v φ.
    split; (eapply (eq_rect _ (fun ψ => deriv CS P R _ _ ψ)); [apply d_ax; left; reflexivity|]);
      [apply vsubst_Ex|symmetry; apply vsubst_Ex].
Defined.

Lemma syn_all_compat : all_compat L (SynConv CS) SM HD TT s syn_qstruct.
Proof. intros Γ φ. rewrite !syn_interp. split; apply d_ax; left; reflexivity. Qed.

Lemma syn_ex_compat : ex_compat L (SynConv CS) SM HD TT s syn_qstruct.
Proof. intros Γ φ. rewrite !syn_interp. split; apply d_ax; left; reflexivity. Qed.

End SynQuant.
