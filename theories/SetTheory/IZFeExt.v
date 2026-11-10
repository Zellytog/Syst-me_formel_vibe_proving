(** * IZFε : l'extensionnalité pour les formules de L_IZF (axiome 1.5.8)

    Les formules de L_IZF n'utilisent que ∈, ⊆, ≃ entre variables, les
    connecteurs et les quantificateurs sur V ; ni ε, ni =, ni les symboles
    d'ensembles. Pour une telle formule φ, si deux substitutions w et w′
    envoient chaque variable sur des ensembles ≃-équivalents, alors
    φ[w] entraîne φ[w′] ([ext_lizf]). Le cas a ≃ b → φ(a) → φ(b) en est
    un cas particulier ([ext_lizf1]).

    La preuve est par récurrence sur la formule, sous forme de règle (de
    Ξ ⊢ φ[w] à Ξ ⊢ φ[w′]) : le cas de ⇒ utilise la récurrence dans
    l'autre sens, d'où la symétrie de la relation entre w et w′. *)

From Stdlib Require Import List.
Import ListNotations.
From Equations Require Import Equations.
From SF.Syntax Require Import Spec Terms Renaming Vectors.
From SF.Calculus Require Import System Rules.
From SF.Logic Require Import Judgment Propositional.
From SF.Functional Require Import Arrow.
From SF.Quantifiers Require Import Quant Order.
From SF.SetTheory Require Import Sets IZFe IZFeBasic.

Local Notation ι a := (Spec [] a).

Derive Signature for var.

(** ** Calcul des substitutions *)

Lemma vsubst_rel2 c {Θ Γ} (t u : tm Θ V) (v : vec isym Θ Γ) :
  vsubst (rel2 c t u) v = rel2 c (vsubst t v) (vsubst u v).
Proof. apply vsubst_tsym2. Qed.

Lemma ren_rel2 c {Γ Δ} (t u : tm Γ V) (ρ : ren Γ Δ) :
  ren_tm (rel2 c t u) ρ = rel2 c (ren_tm t ρ) (ren_tm u ρ).
Proof.
  rewrite <- (ren_tms_nil (Sym := isym) V t ρ), <- (ren_tms_nil (Sym := isym) V u ρ). reflexivity.
Qed.

(** Instancier en la variable 0 le corps affaibli d'un quantificateur
    redonne le corps. *)
Lemma inst_up {Γ} (φ : form (ι V :: Γ)) :
  vsubst (ren_tm φ (upr [ι V] (wk [ι V]))) (inst1 x0) = φ.
Proof.
  rewrite vsubst_ren. rewrite <- (vsubst_vid φ) at 2. f_equal.
  apply vec_ext; intros σ x; unfold vget; rewrite aget_vpre.
  depelim x; reflexivity.
Qed.

Ltac rsimpl := unfold Mem, Sub, Eqv in *; rewrite ?vsubst_rel2, ?vsubst_var0 in *; cbn [aget ahd atl] in *.

(** ** Les congruences, dans un contexte quelconque *)

Definition vV4 {Γ} (a b c d : tm Γ V) : vec isym [ι V; ι V; ι V; ι V] Γ :=
  @acons _ isym Γ (ι V) _ a (vV3 b c d).

(** Les formes concrètes, dans le contexte [a; c; a'; c']. *)
Lemma mem_congr0 : IZFm [ι V; ι V; ι V; ι V] [Eqv x0 x2; Eqv x1 x3; Mem x0 x1] (Mem x2 x3).
Proof.
  uses mem_of_sub (vV3 x2 x1 x3).
  - qap (and_E1 C Pr RIZFm _ _ (Sub x3 x1)). qap iff_E1; [exact (axm A_eqv _ (vV2 x1 x3))|hyp].
  - qap (qex_E C RIZFm V hV _ (And (Eqv x1 x0) (Eps x0 x2))).
    { qap iff_E1; [exact (axm A_mem _ (vV2 x0 x1))|hyp]. }
    qap iff_E2; [exact (axm A_mem _ (vV2 x3 x2))|].
    qap (qex_I C RIZFm V hV _ _ x0).
    qap (and_I C Pr RIZFm); [|qap (and_E2 C Pr RIZFm _ (Eqv x1 x0)); hyp].
    uses eqv_trans (vV3 x3 x1 x0).
    + uses eqv_sym (vV2 x1 x3). hyp.
    + qap (and_E1 C Pr RIZFm _ _ (Eps x0 x2)). hyp.
Qed.

Lemma sub_congr0 : IZFm [ι V; ι V; ι V; ι V] [Eqv x0 x2; Eqv x1 x3; Sub x0 x1] (Sub x2 x3).
Proof.
  uses sub_trans (vV3 x2 x0 x3).
  - qap (and_E2 C Pr RIZFm _ (Sub x0 x2)). qap iff_E1; [exact (axm A_eqv _ (vV2 x0 x2))|hyp].
  - uses sub_trans (vV3 x0 x1 x3); [hyp|].
    qap (and_E1 C Pr RIZFm _ _ (Sub x3 x1)). qap iff_E1; [exact (axm A_eqv _ (vV2 x1 x3))|hyp].
Qed.

Lemma eqv_congr0 : IZFm [ι V; ι V; ι V; ι V] [Eqv x0 x2; Eqv x1 x3; Eqv x0 x1] (Eqv x2 x3).
Proof.
  uses eqv_trans (vV3 x2 x0 x3).
  - uses eqv_sym (vV2 x0 x2). hyp.
  - uses eqv_trans (vV3 x0 x1 x3); hyp.
Qed.

Section Congr.
Context {Γ : ctx isort} (Ξ : list (form Γ)).

Lemma congr_gen c (H0 : IZFm [ι V; ι V; ι V; ι V] [Eqv x0 x2; Eqv x1 x3; rel2 c x0 x1] (rel2 c x2 x3))
  (a b a' b' : tm Γ V) :
  IZFm Γ Ξ (Eqv a a') -> IZFm Γ Ξ (Eqv b b') -> IZFm Γ Ξ (rel2 c a b) -> IZFm Γ Ξ (rel2 c a' b').
Proof.
  intros H1 H2 H3. pose proof (use H0 (vV4 a b a' b') Ξ) as K. rsimpl.
  apply K.
  intros χ Hχ. repeat destruct Hχ as [<-|Hχ]; try contradiction; rsimpl; assumption.
Qed.

Lemma eqv_sym_gen (a b : tm Γ V) : IZFm Γ Ξ (Eqv a b) -> IZFm Γ Ξ (Eqv b a).
Proof.
  intros H. pose proof (use eqv_sym (vV2 a b) Ξ) as K. rsimpl. apply K.
  intros χ [<-|[]]. rsimpl. exact H.
Qed.

Lemma eqv_refl_gen (a : tm Γ V) : IZFm Γ Ξ (Eqv a a).
Proof. pose proof (use eqv_refl1 (vV1 a) Ξ) as K. rsimpl. apply K. intros χ []. Qed.

End Congr.

(** ** Les formules de L_IZF *)

Inductive lizf : forall Γ, form Γ -> Prop :=
| l_mem {Γ} (x y : var Γ (ι V)) : lizf Γ (Mem (var0 x) (var0 y))
| l_sub {Γ} (x y : var Γ (ι V)) : lizf Γ (Sub (var0 x) (var0 y))
| l_eqv {Γ} (x y : var Γ (ι V)) : lizf Γ (Eqv (var0 x) (var0 y))
| l_top {Γ} : lizf Γ Top
| l_bot {Γ} : lizf Γ Bot
| l_imp {Γ} φ ψ : lizf Γ φ -> lizf Γ ψ -> lizf Γ (Imp φ ψ)
| l_and {Γ} φ ψ : lizf Γ φ -> lizf Γ ψ -> lizf Γ (And φ ψ)
| l_or {Γ} φ ψ : lizf Γ φ -> lizf Γ ψ -> lizf Γ (Or φ ψ)
| l_all {Γ} φ : lizf (ι V :: Γ) φ -> lizf Γ (All φ)
| l_ex {Γ} φ : lizf (ι V :: Γ) φ -> lizf Γ (Ex φ).

(** Deux substitutions ≃-reliées sur les variables d'ensemble. *)
Definition erel {Δ Γ} (Ξ : list (form Γ)) (w w' : vec isym Δ Γ) : Prop :=
  forall x : var Δ (ι V), IZFm Γ Ξ (Eqv (aget x w) (aget x w')).

Lemma erel_sym {Δ Γ} Ξ (w w' : vec isym Δ Γ) : erel Ξ w w' -> erel Ξ w' w.
Proof. intros H x. apply eqv_sym_gen, H. Qed.

Lemma erel_weaken {Δ Γ} Ξ Ξ' (w w' : vec isym Δ Γ) : incl Ξ Ξ' -> erel Ξ w w' -> erel Ξ' w w'.
Proof. intros Hi H x. exact (deriv_weaken _ _ _ (H x) _ Hi). Qed.

Lemma erel_up {Δ Γ} Ξ (w w' : vec isym Δ Γ) :
  erel Ξ w w' -> erel (wk_list [ι V] Ξ) (vup [ι V] w) (vup [ι V] w').
Proof.
  intros H x. change (var ([ι V] ++ Δ) (ι V)) in x. vcase x.
  - unfold vup. rewrite !aget_vcat_l. apply eqv_refl_gen.
  - unfold vup, vren. rewrite !aget_vcat_r, !aget_vmap, !(ren_tms_nil (Sym := isym)).
    pose proof (deriv_wk _ _ _ [ι V] (H z)) as K. unfold Eqv in K. rewrite ren_rel2 in K. exact K.
Qed.

Theorem ext_lizf {Δ} (φ : form Δ) : lizf Δ φ ->
  forall Γ (Ξ : list (form Γ)) (w w' : vec isym Δ Γ), erel Ξ w w' ->
  IZFm Γ Ξ (vsubst φ w) -> IZFm Γ Ξ (vsubst φ w').
Proof.
  induction 1 as [Δ x y|Δ x y|Δ x y|Δ|Δ|Δ φ ψ _ IH1 _ IH2|Δ φ ψ _ IH1 _ IH2|Δ φ ψ _ IH1 _ IH2|Δ φ _ IH|Δ φ _ IH];
    intros Γ Ξ w w' Hw Hφ.
  - rsimpl. exact (congr_gen Ξ i_mem mem_congr0 _ _ _ _ (Hw x) (Hw y) Hφ).
  - rsimpl. exact (congr_gen Ξ i_sub sub_congr0 _ _ _ _ (Hw x) (Hw y) Hφ).
  - rsimpl. exact (congr_gen Ξ i_eqv eqv_congr0 _ _ _ _ (Hw x) (Hw y) Hφ).
  - exact Hφ.
  - exact Hφ.
  - unfold Imp in *. rewrite vsubst_Bin in *. fold (Imp (vsubst φ w') (vsubst ψ w')).
    fold (Imp (vsubst φ w) (vsubst ψ w)) in Hφ.
    qap (imp_I C Pr RIZFm).
    apply (IH2 _ _ w); [apply (erel_weaken Ξ); [intros ? ?; right; assumption|exact Hw]|].
    qap (imp_E C Pr RIZFm _ (vsubst φ w)).
    + exact (deriv_weaken _ _ _ Hφ _ (incl_tl _ (incl_refl _))).
    + apply (IH1 _ _ w'); [apply erel_sym, (erel_weaken Ξ); [intros ? ?; right; assumption|exact Hw]|hyp].
  - unfold And in *. rewrite vsubst_Bin in *.
    fold (And (vsubst φ w') (vsubst ψ w')). fold (And (vsubst φ w) (vsubst ψ w)) in Hφ.
    qap (and_I C Pr RIZFm).
    + apply (IH1 _ _ w w' Hw). qap (and_E1 C Pr RIZFm _ _ (vsubst ψ w)). exact Hφ.
    + apply (IH2 _ _ w w' Hw). qap (and_E2 C Pr RIZFm _ (vsubst φ w)). exact Hφ.
  - unfold Or in *. rewrite vsubst_Bin in *.
    fold (Or (vsubst φ w') (vsubst ψ w')). fold (Or (vsubst φ w) (vsubst ψ w)) in Hφ.
    qap (or_E C Pr RIZFm _ (vsubst φ w) (vsubst ψ w)); [exact Hφ| |].
    + qap (or_I1 C Pr RIZFm). apply (IH1 _ _ w); [|hyp].
      apply (erel_weaken Ξ); [intros ? ?; right; assumption|exact Hw].
    + qap (or_I2 C Pr RIZFm). apply (IH2 _ _ w); [|hyp].
      apply (erel_weaken Ξ); [intros ? ?; right; assumption|exact Hw].
  - unfold Quant.All, Quant.Ex in *. rewrite vsubst_Qnt, (vsubst_tms_vup (σ := σP)) in *. cbn [dom] in *.
    qap (qall_I C RIZFm V hV).
    apply (IH _ _ (vup [ι V] w)); [exact (erel_up Ξ w w' Hw)|].
    pose proof (deriv_wk _ _ _ [ι V] Hφ) as K.
    pose proof (qall_E C RIZFm V hV _ (ren_tm (vsubst φ (vup [ι V] w)) (upr [ι V] (wk [ι V]))) x0 K) as K2.
    exact (eq_rect _ (fun f => IZFm _ _ f) K2 _ (inst_up _)).
  - unfold Quant.All, Quant.Ex in *. rewrite vsubst_Qnt, (vsubst_tms_vup (σ := σP)) in *. cbn [dom] in *.
    qap (qex_E C RIZFm V hV _ (vsubst φ (vup [ι V] w))); [exact Hφ|].
    qap (qex_I C RIZFm V hV _ _ x0).
    refine (eq_rect _ (fun f => IZFm _ _ f) _ _ (eq_sym (inst_up _))).
    apply (IH _ _ (vup [ι V] w)); [|hyp].
    apply (erel_weaken (wk_list [ι V] Ξ)); [intros ? ?; right; assumption|exact (erel_up Ξ w w' Hw)].
Qed.

(** ** Cas particulier : a ≃ b → φ(a) → φ(b) *)

Lemma erel_inst1 {Γ} Ξ (a b : tm Γ V) :
  IZFm Γ Ξ (Eqv a b) -> erel Ξ (inst1 a) (inst1 b).
Proof.
  intros H x.
  set (P := fun σ (y : var (ι V :: Γ) σ) =>
    match σ as σ0 return var (ι V :: Γ) σ0 -> Type with
    | Spec [] V => fun y => IZFm Γ Ξ (Eqv (aget y (inst1 a)) (aget y (inst1 b)))
    | _ => fun _ => unit
    end y).
  refine (var_inv P _ _ (ι V) x); unfold P.
  - exact H.
  - intros [[|? ?] [|]] y; try exact tt. apply eqv_refl_gen.
Qed.

Corollary ext_lizf1 {Γ} (φ : form (ι V :: Γ)) : lizf (ι V :: Γ) φ ->
  forall Ξ (a b : tm Γ V), IZFm Γ Ξ (Eqv a b) ->
  IZFm Γ Ξ (vsubst φ (inst1 a)) -> IZFm Γ Ξ (vsubst φ (inst1 b)).
Proof. intros Hl Ξ a b H. apply (ext_lizf φ Hl), erel_inst1, H. Qed.
