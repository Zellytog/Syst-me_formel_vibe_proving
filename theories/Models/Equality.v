(** * L'égalité dans les modèles, à la Lawvere

    Pour une sorte s, une **structure d'égalité** est la donnée, pour chaque
    contexte Γ, d'un prédicat E_Γ au-dessus de M(Γ × [ι s] × [ι s]) qui est
    le plus petit prédicat vrai le long de la diagonale
    δ_Γ : Γ × [ι s] → Γ × [ι s] × [ι s] (c'est ∃_δ ⊤, sans demander
    l'adjoint en entier). Le symbole = est **compatible** si
    ⟦t = u⟧ ≡ ⟨t, u⟩*(E_Γ).

    La réflexivité vient de ce que E est vrai le long de δ, le transport
    (égalité de Leibniz) de sa minimalité, appliquée à φ(x) ⇒ φ(y). *)

From Category Require Import Lib Theory.Category Theory.Functor
  Structure.Terminal Structure.Cartesian Structure.Cartesian.Closed.
From Stdlib Require Import List.
Import ListNotations.
From SF.Syntax Require Import Spec Terms Renaming Traversal Eta Vectors Syn.
From SF.Calculus Require Import System SynConv.
From SF.Logic Require Import Judgment Propositional.
From SF.Functional Require Import Arrow.
From SF.Quantifiers Require Import Quant.
From SF.Models Require Import Calculus Hyperdoctrine Logic Quantifiers.

Local Notation ι a := (Spec [] a).


(** ** Les vecteurs de la diagonale *)

Section Vecs.
Context {Srt : Type} {Sym : spec Srt -> Type} (s : Srt).

Local Notation tm := (Terms.tm Sym).

(** ⟨t, u⟩ : Γ → Γ × [ι s] × [ι s] ; la variable 1 reçoit t, la variable 0 reçoit u. *)
Definition vpair {Γ} (t u : tm Γ s) : vec Sym (ι s :: ι s :: Γ) Γ :=
  @acons _ Sym Γ (ι s) _ u (@acons _ Sym Γ (ι s) _ t (vid Γ)).

(** δ : Γ × [ι s] → Γ × [ι s] × [ι s]. *)
Definition vdiag Γ : vec Sym (ι s :: ι s :: Γ) (ι s :: Γ) :=
  @acons _ Sym _ (ι s) _ (var0 vz) (@acons _ Sym _ (ι s) _ (var0 vz) (wkv s Γ)).

(** φ(x₁) et φ(x₀), dans Γ × [ι s] × [ι s]. *)
Definition vsel {Γ} (k : var (ι s :: ι s :: Γ) (ι s)) : vec Sym (ι s :: Γ) (ι s :: ι s :: Γ) :=
  @acons _ Sym _ (ι s) _ (var0 k) (sexl Sym Γ [ι s; ι s]).

Local Ltac vec3 :=
  apply vec_ext; intros σ x; unfold vget; revert σ x;
  refine (var_inv _ _ _); [|intros σ y];
  rewrite ?aget_vcomp; cbn [aget ahd atl vdiag vpair vsel inst1];
  rewrite ?vsubst_tms_nil, ?vsubst_var0; cbn [aget ahd atl vdiag vpair vsel inst1]; try reflexivity.

Lemma vdiag_inst1 {Γ} (t : tm Γ s) : vcomp (vdiag Γ) (inst1 t) = vpair t t.
Proof.
  vec3. revert σ y. refine (var_inv _ _ _); [|intros σ y]; cbn [aget ahd atl].
  - rewrite vsubst_tms_nil, vsubst_var0. reflexivity.
  - unfold wkv, sexl. rewrite aget_etas, vsubst_eta. reflexivity.
Qed.

Lemma vsel_diag {Γ} : vcomp (vsel (vs vz)) (vdiag Γ) = vcomp (vsel vz) (vdiag Γ).
Proof. vec3. Qed.

Lemma vsel_pair1 {Γ} (t u : tm Γ s) : vcomp (vsel (vs vz)) (vpair t u) = inst1 t.
Proof. vec3. unfold sexl. rewrite aget_etas, vsubst_eta. reflexivity. Qed.

Lemma vsel_pair0 {Γ} (t u : tm Γ s) : vcomp (vsel vz) (vpair t u) = inst1 u.
Proof. vec3. unfold sexl. rewrite aget_etas, vsubst_eta. reflexivity. Qed.

End Vecs.

(** ** Structures d'égalité *)

Section EqStruct.
Context {Srt : Type} {Sym : spec Srt -> Type} (L : logic Sym).
Context (C : Category) {CT : @Terminal C} {CC : @Cartesian C} {CL : @Closed C CC}.
Context (M : cmodel (l_calc Sym L) C) (H : hyperdoctrine C) (T : pred H (M [ι (l_prop Sym L)])).
Context (s : Srt).

Local Notation P := (l_prop Sym L).
Local Notation form := (form Sym P).
Local Notation "p ≤ q" := (ple (h := H) p q) (at level 70).
Local Notation "⟦ φ ⟧" := (interp M H T φ).
Local Notation F v := (fmap[cm_fun M] v).

Record eqstruct := {
  e_pred : forall Γ, pred H (M (ι s :: ι s :: Γ));
  e_refl : forall Γ, ptop ≤ reidx (F (vdiag s Γ)) (e_pred Γ);
  e_least : forall Γ q, ptop ≤ reidx (F (vdiag s Γ)) q -> e_pred Γ ≤ q
}.

Context (E : eqstruct).

Definition eq_compat {HQ : HasEq Sym P s} :=
  forall Γ (t u : Terms.tm Sym Γ s),
    ⟦Eq s t u⟧ ≤ reidx (F (vpair s t u)) (e_pred E Γ) /\ reidx (F (vpair s t u)) (e_pred E Γ) ≤ ⟦Eq s t u⟧.

(** Réindexer le long d'un composé. *)
Lemma reidx_vcomp {Γ Δ Ξ} (a : vec Sym Γ Δ) (b : vec Sym Δ Ξ) (q : pred H (M Γ)) :
  reidx (F (vcomp a b)) q ≤ reidx (F b) (reidx (F a) q) /\ reidx (F b) (reidx (F a) q) ≤ reidx (F (vcomp a b)) q.
Proof.
  assert (Ec : F (vcomp a b) ≈ F a ∘ F b) by (exact (@fmap_comp _ _ (cm_fun M) Ξ Δ Γ a b)).
  destruct (reidx_comp _ H (F a) (F b) q) as [C1 C2]. split.
  - eapply ple_trans; [apply reidx_proper, Ec|exact C1].
  - eapply ple_trans; [exact C2|apply reidx_proper; symmetry; exact Ec].
Qed.

Lemma interp_vsubst_vcomp {Γ Δ Ξ} (φ : form Γ) (a : vec Sym Γ Δ) (b : vec Sym Δ Ξ) :
  ⟦vsubst (vsubst φ a) b⟧ ≤ ⟦vsubst φ (vcomp a b)⟧.
Proof. rewrite vsubst_vsubst. apply ple_refl. Qed.

Theorem eq_sound {HQ : HasEq Sym P s} (Hc : eq_compat) i : mrule_sound M H T (eq_rules s i).
Proof.
  intros Γ Ξ v Hp. unfold mvalid. destruct i; cbn [eq_rules mkr d_prems d_concl d_ctx] in *.
  - (* réflexivité *)
    set (t := aget vz v).
    eapply ple_trans; [|apply interp_eq; symmetry; etransitivity;
      [apply (vsubst_Eq (s := s))|rewrite vsubst_var0; reflexivity]].
    eapply ple_trans; [apply top_max|]. eapply ple_trans; [|apply (Hc Γ t t)].
    rewrite <- vdiag_inst1. eapply ple_trans; [|apply reidx_vcomp].
    eapply ple_trans; [apply (reidx_top _ H (F (inst1 t)))|]. apply reidx_mono, e_refl.
  - (* transport *)
    pose proof (Hp _ (or_introl eq_refl)) as K1. apply prem_valid in K1.
    pose proof (Hp _ (or_intror (or_introl eq_refl))) as K2. apply prem_valid in K2.
    cbn [vsubst_list map app] in K1, K2. unfold mvalid in K1, K2.
    set (φ := aget vz v) in *. set (t := aget (vs vz) v) in *. set (u := aget (vs (vs vz)) v) in *.
    assert (K1' : mconj M H T Ξ ≤ ⟦Eq s t u⟧).
    { eapply ple_trans; [exact K1|]. apply interp_eq.
      etransitivity; [apply (vsubst_Eq (s := s))|rewrite !vsubst_var0; reflexivity]. }
    assert (K2' : mconj M H T Ξ ≤ ⟦vsubst φ (inst1 t)⟧).
    { eapply ple_trans; [exact K2|]. apply interp_eq. exact (vsubst_app1 vz (vs vz) v). }
    clear K1 K2. rename K1' into K1. rename K2' into K2.
    eapply ple_trans; [|apply interp_eq; symmetry; exact (vsubst_app1 vz (vs (vs vz)) v)].
    set (φ1 := vsubst φ (vsel s (vs vz))). set (φ2 := vsubst φ (vsel s vz)).
    (* E ≤ φ(x₁) ⇒ φ(x₀) *)
    assert (HE : e_pred E Γ ≤ pimp ⟦φ1⟧ ⟦φ2⟧).
    { apply e_least. eapply ple_trans; [|apply reidx_imp]. apply imp_adj.
      eapply ple_trans; [apply and_r|].
      destruct (interp_vsubst L C M H T φ1 (vdiag s Γ)) as [A1 A2].
      destruct (interp_vsubst L C M H T φ2 (vdiag s Γ)) as [B1 B2].
      eapply ple_trans; [exact A2|]. eapply ple_trans; [|exact B1].
      apply interp_eq. unfold φ1, φ2. rewrite !vsubst_vsubst. f_equal; try apply vsel_diag. }
    apply (ple_trans _ (pand (pimp ⟦vsubst φ (inst1 t)⟧ ⟦vsubst φ (inst1 u)⟧) ⟦vsubst φ (inst1 t)⟧));
      [|apply imp_eval].
    apply and_intro; [|exact K2].
    eapply ple_trans; [exact K1|]. eapply ple_trans; [apply (Hc Γ t u)|].
    eapply ple_trans; [apply reidx_mono, HE|]. eapply ple_trans; [apply reidx_imp|].
    destruct (interp_vsubst L C M H T φ1 (vpair s t u)) as [A1 A2].
    destruct (interp_vsubst L C M H T φ2 (vpair s t u)) as [B1 B2].
    apply imp_adj.
    eapply ple_trans; [apply and_mono; [apply ple_refl|]|].
    { eapply ple_trans; [|exact A1]. apply interp_eq.
      unfold φ1. rewrite vsubst_vsubst. f_equal; try first [apply vsel_pair1|symmetry; apply vsel_pair1]. }
    eapply ple_trans; [apply imp_eval|]. eapply ple_trans; [exact B2|]. apply interp_eq.
    unfold φ2. rewrite vsubst_vsubst. f_equal; try first [apply vsel_pair0|symmetry; apply vsel_pair0].
Qed.

End EqStruct.
