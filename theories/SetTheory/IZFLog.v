(** * Outils de dérivation dans IZF

    Règles dérivées sur ↔, et **théorème de remplacement** : dans une
    formule dont les métavariables sont des prédicats sur V, remplacer
    chaque prédicat par un prédicat équivalent donne une formule
    équivalente. C'est la congruence de tous les gabarits de la
    traduction. *)

From Stdlib Require Import List.
Import ListNotations.
From SF.Syntax Require Import Spec Terms Renaming Eta Composition Vectors.
From SF.Calculus Require Import System Rules.
From SF.Logic Require Import Judgment Propositional.
From SF.Functional Require Import Arrow.
From SF.Quantifiers Require Import Quant Order.
From SF.SetTheory Require Import Sets IZFe IZF.

Local Notation ι a := (Spec [] a).

Tactic Notation "zap" uconstr(t) := eapply t; try typeclasses eauto.
Ltac zhyp := apply d_ax; cbn [In wk_list map app]; auto 20.

Notation zimp_I := (imp_I ZC Pr RIZF).
Notation zimp_E := (imp_E ZC Pr RIZF).
Notation zand_I := (and_I ZC Pr RIZF).
Notation zand_E1 := (and_E1 ZC Pr RIZF).
Notation zand_E2 := (and_E2 ZC Pr RIZF).
Notation zor_I1 := (or_I1 ZC Pr RIZF).
Notation zor_I2 := (or_I2 ZC Pr RIZF).
Notation zor_E := (or_E ZC Pr RIZF).
Notation zall_I := (qall_I ZC RIZF V hZ).
Notation zall_E := (qall_E ZC RIZF V hZ).
Notation zex_I := (qex_I ZC RIZF V hZ).
Notation zex_E := (qex_E ZC RIZF V hZ).
Notation zeq_refl := (qeq_refl ZC RIZF V hZ).
Notation zeq_subst := (qeq_subst ZC RIZF V hZ).
Notation zeq_sym := (qeq_sym ZC RIZF V hZ).
Notation zeq_trans := (qeq_trans ZC RIZF V hZ).

(** ** Règles dérivées sur ↔ *)

Section Iff.
Context {Γ : ctx isort}.
Implicit Types (Ξ : list (zform Γ)) (A B C D : zform Γ).

Lemma ziff_E1 Ξ A B : IZF Γ Ξ (zIff A B) -> IZF Γ Ξ A -> IZF Γ Ξ B.
Proof. intros H1 H2. zap (zimp_E _ A B); [zap (zand_E1 _ _ (Imp B A)); exact H1|exact H2]. Qed.

Lemma ziff_E2 Ξ A B : IZF Γ Ξ (zIff A B) -> IZF Γ Ξ B -> IZF Γ Ξ A.
Proof. intros H1 H2. zap (zimp_E _ B A); [zap (zand_E2 _ (Imp A B)); exact H1|exact H2]. Qed.

Lemma ziff_I Ξ A B : IZF Γ (A :: Ξ) B -> IZF Γ (B :: Ξ) A -> IZF Γ Ξ (zIff A B).
Proof. intros H1 H2. zap zand_I; zap zimp_I; assumption. Qed.

Lemma ziff_refl Ξ A : IZF Γ Ξ (zIff A A).
Proof. apply ziff_I; zhyp. Qed.

Lemma ziff_sym Ξ A B : IZF Γ Ξ (zIff A B) -> IZF Γ Ξ (zIff B A).
Proof.
  intros H. apply ziff_I.
  - apply (ziff_E2 _ A B); [exact (deriv_weaken _ _ _ H _ (incl_tl _ (incl_refl _)))|zhyp].
  - apply (ziff_E1 _ A B); [exact (deriv_weaken _ _ _ H _ (incl_tl _ (incl_refl _)))|zhyp].
Qed.

Lemma ziff_trans Ξ A B C : IZF Γ Ξ (zIff A B) -> IZF Γ Ξ (zIff B C) -> IZF Γ Ξ (zIff A C).
Proof.
  intros H1 H2. apply ziff_I.
  - apply (ziff_E1 _ B C); [exact (deriv_weaken _ _ _ H2 _ (incl_tl _ (incl_refl _)))|].
    apply (ziff_E1 _ A B); [exact (deriv_weaken _ _ _ H1 _ (incl_tl _ (incl_refl _)))|zhyp].
  - apply (ziff_E2 _ A B); [exact (deriv_weaken _ _ _ H1 _ (incl_tl _ (incl_refl _)))|].
    apply (ziff_E2 _ B C); [exact (deriv_weaken _ _ _ H2 _ (incl_tl _ (incl_refl _)))|zhyp].
Qed.

Lemma ziff_imp Ξ A B C D : IZF Γ Ξ (zIff A C) -> IZF Γ Ξ (zIff B D) -> IZF Γ Ξ (zIff (Imp A B) (Imp C D)).
Proof.
  intros H1 H2. apply ziff_I; zap zimp_I.
  - apply (ziff_E1 _ B D); [exact (deriv_weaken _ _ _ H2 _ (incl_tl _ (incl_tl _ (incl_refl _))))|].
    zap (zimp_E _ A); [zhyp|].
    apply (ziff_E2 _ A C); [exact (deriv_weaken _ _ _ H1 _ (incl_tl _ (incl_tl _ (incl_refl _))))|zhyp].
  - apply (ziff_E2 _ B D); [exact (deriv_weaken _ _ _ H2 _ (incl_tl _ (incl_tl _ (incl_refl _))))|].
    zap (zimp_E _ C); [zhyp|].
    apply (ziff_E1 _ A C); [exact (deriv_weaken _ _ _ H1 _ (incl_tl _ (incl_tl _ (incl_refl _))))|zhyp].
Qed.

Lemma ziff_and Ξ A B C D : IZF Γ Ξ (zIff A C) -> IZF Γ Ξ (zIff B D) -> IZF Γ Ξ (zIff (And A B) (And C D)).
Proof.
  intros H1 H2. apply ziff_I; zap zand_I.
  - apply (ziff_E1 _ A C); [exact (deriv_weaken _ _ _ H1 _ (incl_tl _ (incl_refl _)))|].
    zap (zand_E1 _ _ B); zhyp.
  - apply (ziff_E1 _ B D); [exact (deriv_weaken _ _ _ H2 _ (incl_tl _ (incl_refl _)))|].
    zap (zand_E2 _ A); zhyp.
  - apply (ziff_E2 _ A C); [exact (deriv_weaken _ _ _ H1 _ (incl_tl _ (incl_refl _)))|].
    zap (zand_E1 _ _ D); zhyp.
  - apply (ziff_E2 _ B D); [exact (deriv_weaken _ _ _ H2 _ (incl_tl _ (incl_refl _)))|].
    zap (zand_E2 _ C); zhyp.
Qed.

Lemma ziff_or Ξ A B C D : IZF Γ Ξ (zIff A C) -> IZF Γ Ξ (zIff B D) -> IZF Γ Ξ (zIff (Or A B) (Or C D)).
Proof.
  intros H1 H2. apply ziff_I.
  - zap (zor_E _ A B); [zhyp| |].
    + zap zor_I1. apply (ziff_E1 _ A C); [exact (deriv_weaken _ _ _ H1 _ (incl_tl _ (incl_tl _ (incl_refl _))))|zhyp].
    + zap zor_I2. apply (ziff_E1 _ B D); [exact (deriv_weaken _ _ _ H2 _ (incl_tl _ (incl_tl _ (incl_refl _))))|zhyp].
  - zap (zor_E _ C D); [zhyp| |].
    + zap zor_I1. apply (ziff_E2 _ A C); [exact (deriv_weaken _ _ _ H1 _ (incl_tl _ (incl_tl _ (incl_refl _))))|zhyp].
    + zap zor_I2. apply (ziff_E2 _ B D); [exact (deriv_weaken _ _ _ H2 _ (incl_tl _ (incl_tl _ (incl_refl _))))|zhyp].
Qed.

End Iff.

(** Instancier en la variable 0 le corps affaibli d'un quantificateur. *)
Lemma zinst_up {Γ} (φ : zform (ι V :: Γ)) :
  vsubst (ren_tm φ (upr [ι V] (wk [ι V]))) (inst1 x0) = φ.
Proof.
  rewrite vsubst_ren. rewrite <- (vsubst_vid φ) at 2. f_equal.
  apply vec_ext; intros σ x; unfold vget; rewrite aget_vpre.
  change (var ([ι V] ++ Γ) σ) in x. vcase x.
  - refine (var_inv (fun σ z => aget (upr [ι V] (wk [ι V]) σ (vl Γ z)) (inst1 x0) = aget (vl Γ z) (vid (ι V :: Γ))) _ _ σ z).
    + reflexivity.
    + intros ? y. inversion y.
  - unfold upr. rewrite vsplit_vr. reflexivity.
Qed.

(** ∀E en la variable 0, après affaiblissement. *)
Lemma zall_E0 {Γ} (Ξ : list (zform Γ)) (A : zform (ι V :: Γ)) :
  IZF Γ Ξ (zAll A) -> IZF (ι V :: Γ) (wk_list [ι V] Ξ) A.
Proof.
  intros H. pose proof (deriv_wk _ _ _ [ι V] H) as K.
  pose proof (zall_E _ (ren_tm A (upr [ι V] (wk [ι V]))) x0 K) as K2.
  exact (eq_rect _ (fun f => IZF _ _ f) K2 _ (zinst_up _)).
Qed.

(** ∃I en la variable 0. *)
Lemma zex_I0 {Γ} (Ξ : list (zform (ι V :: Γ))) (A : zform (ι V :: Γ)) :
  IZF (ι V :: Γ) Ξ A -> IZF (ι V :: Γ) Ξ (ren_tm (zEx A) (wk [ι V])).
Proof.
  intros H. zap (zex_I _ _ x0). exact (eq_rect _ (fun f => IZF _ _ f) H _ (eq_sym (zinst_up _))).
Qed.

(** Décomposer une conjonction en hypothèse. *)
Lemma zand_L {Γ} (Ξ : list (zform Γ)) A B C : IZF Γ (A :: B :: Ξ) C -> IZF Γ (And A B :: Ξ) C.
Proof.
  intros H. apply (deriv_cut_gen _ _ _ H). intros χ [<-|[<-|Hχ]].
  - zap (zand_E1 _ _ B). zhyp.
  - zap (zand_E2 _ A). zhyp.
  - zhyp.
Qed.

(** Sous un quantificateur. *)
Lemma ziff_all {Γ} (Ξ : list (zform Γ)) (A B : zform (ι V :: Γ)) :
  IZF (ι V :: Γ) (wk_list [ι V] Ξ) (zIff A B) -> IZF Γ Ξ (zIff (zAll A) (zAll B)).
Proof.
  intros H. apply ziff_I; zap zall_I.
  - apply (ziff_E1 _ A B); [exact (deriv_weaken _ _ _ H _ (incl_tl _ (incl_refl _)))|].
    apply (zall_E0 (zAll A :: Ξ)). zhyp.
  - apply (ziff_E2 _ A B); [exact (deriv_weaken _ _ _ H _ (incl_tl _ (incl_refl _)))|].
    apply (zall_E0 (zAll B :: Ξ)). zhyp.
Qed.

Lemma ziff_ex {Γ} (Ξ : list (zform Γ)) (A B : zform (ι V :: Γ)) :
  IZF (ι V :: Γ) (wk_list [ι V] Ξ) (zIff A B) -> IZF Γ Ξ (zIff (zEx A) (zEx B)).
Proof.
  intros H. apply ziff_I.
  - zap (zex_E _ A); [zhyp|]. apply zex_I0.
    apply (ziff_E1 _ A B); [exact (deriv_weaken _ _ _ H _ (incl_tl _ (incl_tl _ (incl_refl _))))|zhyp].
  - zap (zex_E _ B); [zhyp|]. apply zex_I0.
    apply (ziff_E2 _ A B); [exact (deriv_weaken _ _ _ H _ (incl_tl _ (incl_tl _ (incl_refl _))))|zhyp].
Qed.

(** ** Instanciation de deux variables *)

Definition inst2 {Sg : spec isort -> Type} {Γ} (t u : Terms.tm Sg Γ V) : vec Sg (ι V :: ι V :: Γ) Γ :=
  @acons _ Sg Γ (ι V) _ t (@acons _ Sg Γ (ι V) _ u (vid Γ)).

Lemma vsubst_app2_gen {Sg : spec isort -> Type} {Θ Γ} (x : var Θ σR) (t u : Terms.tm Sg Θ V) (v : vec Sg Θ Γ) :
  vsubst (@tvar _ Sg Θ σR x (@acons _ Sg Θ (ι V) _ t (@acons _ Sg Θ (ι V) _ u anil))) v =
  vsubst (aget x v) (inst2 (vsubst t v) (vsubst u v)).
Proof.
  change (happ σR (aget x v)
            (@acons _ Sg Γ (ι V) _ (vsubst_tms (σ := ι V) t v)
              (@acons _ Sg Γ (ι V) _ (vsubst_tms (σ := ι V) u v) anil))
          = vsubst (aget x v) (inst2 (vsubst t v) (vsubst u v))).
  rewrite !vsubst_tms_nil, happ_vsubst; reflexivity.
Qed.

Lemma vsubst_tms_wk_cat_g {Sg : spec isort -> Type} Λ {Γ Δ σ} (u : tms Sg Γ σ) (a : args Sg Δ Λ) (w : vec Sg Γ Δ) :
  vsubst_tms (ren_tms u (wk Λ)) (vcat Λ a w) = vsubst_tms u w.
Proof.
  unfold vsubst_tms; rewrite subst_tms_ren; apply subst_tms_ext; intros ρ y.
  unfold rs_comp, vget, wk. rewrite aget_vcat_r. reflexivity.
Qed.

Lemma vup_cat_g {Sg : spec isort -> Type} Λ {Δ Γ Γ'} (w : vec Sg Δ Γ) (a : args Sg Γ' Λ) (w' : vec Sg Γ Γ') :
  vcomp (vup Λ w) (vcat Λ a w') = vcat Λ a (vcomp w w').
Proof.
  apply vec_ext; intros σ x; unfold vget. rewrite aget_vcomp. vcase x.
  - unfold vup. rewrite !aget_vcat_l, aget_etas, vsubst_eta, aget_vcat_l. reflexivity.
  - unfold vup. rewrite !aget_vcat_r. unfold vren. rewrite aget_vmap, vsubst_tms_wk_cat_g, aget_vcomp.
    reflexivity.
Qed.

Lemma inst_nest_g {Sg : spec isort -> Type} {Θ Γ} (χ : Terms.tm Sg (ι V :: Θ) Pr) (W : vec Sg Θ Γ) (t : Terms.tm Sg Γ V) :
  vsubst (vsubst χ (vup [ι V] W)) (inst1 t) = vsubst χ (@acons _ Sg Γ (ι V) _ t W).
Proof.
  rewrite vsubst_vsubst. f_equal.
  change (vcomp (vup [ι V] W) (vcat [ι V] (@acons _ Sg Γ (ι V) _ t anil) (vid Γ))
          = vcat [ι V] (@acons _ Sg Γ (ι V) _ t anil) W).
  rewrite vup_cat_g, vcomp_vid_r. reflexivity.
Qed.

Lemma upr2 {Γ Δ} (ρ : ren Γ Δ) σ (x : var (ι V :: ι V :: Γ) σ) :
  upr [ι V] (upr [ι V] ρ) σ x = upr [ι V; ι V] ρ σ x.
Proof.
  refine (var_inv (fun σ x => upr [ι V] (upr [ι V] ρ) σ x = upr [ι V; ι V] ρ σ x) _ _ σ x); [reflexivity|].
  intros τ y.
  refine (var_inv (fun τ y => upr [ι V] (upr [ι V] ρ) τ (vs y) = upr [ι V; ι V] ρ τ (vs y)) _ _ τ y); [reflexivity|].
  intros τ' w.
  change (upr [ι V] (upr [ι V] ρ) τ' (vr [ι V] (vr [ι V] w)) = upr [ι V; ι V] ρ τ' (vr [ι V; ι V] w)).
  rewrite !upr_vr. reflexivity.
Qed.

Lemma ren_all2 {Γ Δ} (A A' : zform (ι V :: ι V :: Γ)) (ρ : ren Γ Δ) :
  ren_tm (zAll (zAll (zIff A A'))) ρ = zAll (zAll (zIff (ren_tms (σ := σR) A ρ) (ren_tms (σ := σR) A' ρ))).
Proof.
  unfold ren_tms. cbn [dom].
  rewrite !(ren_ext _ (upr [ι V; ι V] ρ) (upr [ι V] (upr [ι V] ρ))) by (intros; symmetry; apply upr2).
  reflexivity.
Qed.

(** ∀∀ instancié en deux termes. *)
Lemma zall2_E {Γ} (Ξ : list (zform Γ)) (A : zform (ι V :: ι V :: Γ)) (t u : ztm Γ V) :
  IZF Γ Ξ (zAll (zAll A)) -> IZF Γ Ξ (vsubst A (inst2 t u)).
Proof.
  intros H. pose proof (zall_E _ _ u H) as K. unfold Quant.All in K. rewrite vsubst_Qnt, (vsubst_tms_vup (σ := σP)) in K.
  pose proof (zall_E _ _ t K) as K2. exact (eq_rect _ (fun f => IZF Γ Ξ f) K2 _ (inst_nest_g A (inst1 u) t)).
Qed.

(** ** Théorème de remplacement *)

(** Contextes de gabarits : des ensembles et des prédicats sur V. *)
Definition tctx (Θ : ctx isort) : Prop := forall σ (x : var Θ σ), σ = ι V \/ σ = σP \/ σ = σR.

Lemma tctx_cons {Θ} σ : (σ = ι V \/ σ = σP \/ σ = σR) -> tctx Θ -> tctx (σ :: Θ).
Proof.
  intros Hσ H τ x.
  refine (var_inv (fun τ _ => τ = ι V \/ τ = σP \/ τ = σR) _ _ τ x); [exact Hσ|intros ? y; apply H, y].
Qed.

Lemma tctx_app D {Θ} : tctx D -> tctx Θ -> tctx (D ++ Θ).
Proof.
  intros HD HΘ σ x. destruct (vsplit_case D x) as [[z _]|[z _]]; [exact (HD σ z)|exact (HΘ σ z)].
Qed.

(** Deux instanciations reliées : mêmes ensembles, prédicats équivalents. *)
Definition vrel {Θ Γ} (Ξ : list (zform Γ)) (v v' : vec zsym Θ Γ) : Prop :=
  (forall x : var Θ (ι V), aget x v = aget x v') /\
  (forall x : var Θ σP, IZF Γ Ξ (zAll (zIff (aget x v) (aget x v')))) /\
  (forall x : var Θ σR, IZF Γ Ξ (zAll (zAll (zIff (aget x v) (aget x v'))))).

(** Relation entre les instances d'un argument de spécification σ. *)
Definition compR {Θ Γ} (Ξ : list (zform Γ)) σ (u : tms zsym Θ σ) (v v' : vec zsym Θ Γ) : Prop :=
  tctx (dom σ) ->
  match cod σ as b return tms zsym Θ (Spec (dom σ) b) -> Prop with
  | V => fun u => vsubst_tms (σ := Spec (dom σ) V) u v = vsubst_tms (σ := Spec (dom σ) V) u v'
  | Pr => fun u => IZF (dom σ ++ Γ) (wk_list (dom σ) Ξ)
                     (zIff (vsubst_tms (σ := Spec (dom σ) Pr) u v) (vsubst_tms (σ := Spec (dom σ) Pr) u v'))
  end u.

Fixpoint AR {Θ Γ} (Ξ : list (zform Γ)) (L : list (spec isort)) :
  args zsym Θ L -> vec zsym Θ Γ -> vec zsym Θ Γ -> Prop :=
  match L as L0 return args zsym Θ L0 -> vec zsym Θ Γ -> vec zsym Θ Γ -> Prop with
  | [] => fun _ _ _ => True
  | σ :: L' => fun a v v' => compR Ξ σ (ahd a) v v' /\ AR Ξ L' (atl a) v v'
  end.

Lemma tctx_nil : tctx [].
Proof. intros σ x. destruct (var_nil x). Qed.

Lemma vrel_up D {Θ Γ} (Ξ : list (zform Γ)) (v v' : vec zsym Θ Γ) :
  tctx D -> vrel Ξ v v' -> vrel (wk_list D Ξ) (vup D v) (vup D v').
Proof.
  intros HD [H1 [H2 H3]]. split; [|split].
  - intros x. vcase x.
    + unfold vup. rewrite !aget_vcat_l. reflexivity.
    + unfold vup, vren. rewrite !aget_vcat_r, !aget_vmap, H1. reflexivity.
  - intros x. vcase x.
    + unfold vup. rewrite !aget_vcat_l. zap zall_I. apply ziff_refl.
    + unfold vup, vren. rewrite !aget_vcat_r, !aget_vmap. exact (deriv_wk _ _ _ D (H2 z)).
  - intros x. vcase x.
    + unfold vup. rewrite !aget_vcat_l. zap zall_I. zap zall_I. apply ziff_refl.
    + unfold vup, vren. rewrite !aget_vcat_r, !aget_vmap, <- ren_all2. exact (deriv_wk _ _ _ D (H3 z)).
Qed.

Lemma args1_inv {Sg : spec isort -> Type} {Θ σ} (a : args Sg Θ [σ]) : { t | a = acons t anil }.
Proof. exists (ahd a). rewrite (args_eta a) at 1. rewrite (args_nil (atl a)). reflexivity. Defined.

Lemma args2_inv {Sg : spec isort -> Type} {Θ σ τ} (a : args Sg Θ [σ; τ]) : { t & { u | a = acons t (acons u anil) } }.
Proof.
  exists (ahd a), (ahd (atl a)). rewrite (args_eta a) at 1. rewrite (args_eta (atl a)), (args_nil (atl (atl a))).
  reflexivity.
Defined.

Theorem repl_mut :
  (forall Θ s (t : ztm Θ s), tctx Θ -> forall Γ (Ξ : list (zform Γ)) (v v' : vec zsym Θ Γ), vrel Ξ v v' ->
     match s as s0 return ztm Θ s0 -> Prop with
     | V => fun t => vsubst t v = vsubst t v'
     | Pr => fun t => IZF Γ Ξ (zIff (vsubst t v) (vsubst t v'))
     end t) /\
  (forall Θ L (a : args zsym Θ L), tctx Θ -> forall Γ (Ξ : list (zform Γ)) (v v' : vec zsym Θ Γ),
     vrel Ξ v v' -> AR Ξ L a v v').
Proof.
  apply tm_args_ind.
  - intros Θ σ x a IH HΘ Γ Ξ v v' Hv. pose proof (IH HΘ Γ Ξ v v' Hv) as K.
    destruct (HΘ σ x) as [E|[E|E]]; subst σ.
    + rewrite (args_nil a). change (vsubst (var0 (Sym := zsym) x) v = vsubst (var0 (Sym := zsym) x) v'). rewrite !vsubst_var0. apply Hv.
    + destruct (args1_inv a) as [t ->]. change (ztm Θ V) in t. cbn [AR ahd] in K. destruct K as [K _].
      specialize (K tctx_nil). cbn [cod dom] in K. rewrite !vsubst_tms_nil in K.
      assert (K' : vsubst t v = vsubst t v') by exact K. clear K. rename K' into K.
      change (IZF Γ Ξ (zIff (vsubst (app1 (s := V) x t) v) (vsubst (app1 (s := V) x t) v'))).
      rewrite !vsubst_app1_gen'.
      pose proof (zall_E _ _ (vsubst t v) (proj1 (proj2 Hv) x)) as K2.
      unfold zIff, And, Imp in K2 |- *. rewrite !vsubst_Bin in K2. rewrite K in K2 at 2 3. exact K2.
    + destruct (args2_inv a) as [t1 [t2 ->]]. change (ztm Θ V) in t1, t2. cbn [AR ahd atl] in K.
      destruct K as [K1 [K2 _]]. specialize (K1 tctx_nil); specialize (K2 tctx_nil). cbn [cod dom] in K1, K2.
      rewrite !vsubst_tms_nil in K1, K2.
      assert (E1 : vsubst t1 v = vsubst t1 v') by exact K1. assert (E2 : vsubst t2 v = vsubst t2 v') by exact K2.
      clear K1 K2. change (IZF Γ Ξ (zIff (vsubst (zapp2 x t1 t2) v) (vsubst (zapp2 x t1 t2) v'))).
      unfold zapp2. rewrite !vsubst_app2_gen, <- E1, <- E2.
      pose proof (zall2_E _ _ (vsubst t1 v) (vsubst t2 v) (proj2 (proj2 Hv) x)) as K3.
      unfold zIff, And, Imp in K3 |- *. rewrite !vsubst_Bin in K3. exact K3.
  - intros Θ σ c a IH HΘ Γ Ξ v v' Hv. pose proof (IH HΘ Γ Ξ v v' Hv) as K.
    destruct c;
      first [ destruct (args2_inv a) as [t1 [t2 ->]] | destruct (args1_inv a) as [t1 ->] | rewrite (args_nil a) in * ];
      cbn [AR compR dom cod ahd atl] in K; cbn [cod].
    + destruct K as [K1 [K2 _]]. specialize (K1 tctx_nil); specialize (K2 tctx_nil). cbn [cod dom app] in K1, K2.
      rewrite wk_list_nil in K1, K2. exact (ziff_imp _ _ _ _ _ K1 K2).
    + destruct K as [K1 [K2 _]]. specialize (K1 tctx_nil); specialize (K2 tctx_nil). cbn [cod dom app] in K1, K2.
      rewrite wk_list_nil in K1, K2. exact (ziff_and _ _ _ _ _ K1 K2).
    + destruct K as [K1 [K2 _]]. specialize (K1 tctx_nil); specialize (K2 tctx_nil). cbn [cod dom app] in K1, K2.
      rewrite wk_list_nil in K1, K2. exact (ziff_or _ _ _ _ _ K1 K2).
    + apply ziff_refl.
    + apply ziff_refl.
    + destruct K as [K1 _]. specialize (K1 (tctx_cons _ (or_introl eq_refl) tctx_nil)). cbn [cod dom app] in K1.
      exact (ziff_all _ _ _ K1).
    + destruct K as [K1 _]. specialize (K1 (tctx_cons _ (or_introl eq_refl) tctx_nil)). cbn [cod dom app] in K1.
      exact (ziff_ex _ _ _ K1).
    + destruct K as [K1 [K2 _]]. specialize (K1 tctx_nil); specialize (K2 tctx_nil). cbn [cod dom app] in K1, K2.
      change (IZF Γ Ξ (zIff (@tsym _ zsym Γ _ z_eq (@acons _ zsym Γ (ι V) _ (vsubst_tms (σ := ι V) t1 v)
                               (@acons _ zsym Γ (ι V) _ (vsubst_tms (σ := ι V) t2 v) anil)))
                            (@tsym _ zsym Γ _ z_eq (@acons _ zsym Γ (ι V) _ (vsubst_tms (σ := ι V) t1 v')
                               (@acons _ zsym Γ (ι V) _ (vsubst_tms (σ := ι V) t2 v') anil))))).
      rewrite K1, K2. apply ziff_refl.
    + destruct K as [K1 [K2 _]]. specialize (K1 tctx_nil); specialize (K2 tctx_nil). cbn [cod dom app] in K1, K2.
      change (IZF Γ Ξ (zIff (@tsym _ zsym Γ _ z_mem (@acons _ zsym Γ (ι V) _ (vsubst_tms (σ := ι V) t1 v)
                               (@acons _ zsym Γ (ι V) _ (vsubst_tms (σ := ι V) t2 v) anil)))
                            (@tsym _ zsym Γ _ z_mem (@acons _ zsym Γ (ι V) _ (vsubst_tms (σ := ι V) t1 v')
                               (@acons _ zsym Γ (ι V) _ (vsubst_tms (σ := ι V) t2 v') anil))))).
      rewrite K1, K2. apply ziff_refl.
  - intros; exact I.
  - intros Θ σ L u IHu a IHa HΘ Γ Ξ v v' Hv. split; [|exact (IHa HΘ Γ Ξ v v' Hv)].
    intros HD. cbn [ahd]. specialize (IHu (tctx_app _ HD HΘ) _ _ _ _ (vrel_up (dom σ) Ξ v v' HD Hv)).
    destruct σ as [D [|]]; cbn [cod dom] in *; rewrite !vsubst_tms_vup; exact IHu.
Qed.

(** La forme utilisée : deux gabarits instanciés par des prédicats équivalents. *)
Corollary repl {Θ Γ} (F : zform Θ) (Ξ : list (zform Γ)) (v v' : vec zsym Θ Γ) :
  tctx Θ -> vrel Ξ v v' -> IZF Γ Ξ (zIff (vsubst F v) (vsubst F v')).
Proof. intros HΘ Hv. exact (proj1 repl_mut Θ Pr F HΘ Γ Ξ v v' Hv). Qed.
