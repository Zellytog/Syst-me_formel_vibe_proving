(** * La catégorie syntaxique modulo un système de calcul

    Mêmes objets et mêmes morphismes que [Syn], mais deux vecteurs sont
    égaux quand leurs composantes sont convertibles. Seule la relation de
    setoïde des homs change ; toutes les constructions (produits,
    exponentielles) sont celles de [SF.Syntax.Syn]. *)

From Category Require Import Lib Theory.Category Theory.Isomorphism
  Structure.Terminal Structure.Cartesian Structure.Cartesian.Closed Instance.Sets.
From Stdlib Require Import List.
Import ListNotations.
From SF.Syntax Require Import Spec Terms Renaming Traversal Eta Composition Vectors Syn.
From SF.Calculus Require Import System.

Section SynConv.

Context {Srt : Type} {Sym : spec Srt -> Type} (S : system Sym).
Implicit Types (Λ Θ Γ Δ Ξ D M : ctx Srt) (σ τ ρ : spec Srt).

Local Notation args := (Terms.args Sym).
Local Notation "a ≃ b" := (arel (conv S) a b) (at level 70).

Lemma arel_equiv Γ Δ : Equivalence (fun f g : args Γ Δ => f ≃ g).
Proof.
  constructor.
  - intros f; apply arel_refl.
  - intros f g H; apply arel_sym, H.
  - intros f g h H1 H2; eapply arel_trans; eassumption.
Qed.

Definition conv_homset Γ Δ : Setoid (args Γ Δ) :=
  {| equiv := fun f g => f ≃ g; setoid_equiv := arel_equiv Γ Δ |}.

#[export]
Program Instance SynConv : Category := {
  obj := ctx Srt;
  hom := fun Γ Δ => args Γ Δ;
  homset := conv_homset;
  id := fun Γ => vid Γ;
  compose := fun Γ Δ Ξ f g => vcomp f g
}.
Solve All Obligations with
  (simpl; intros;
   first [ repeat intro; simpl in *; apply arel_vcomp; assumption
         | rewrite ?vcomp_vid_l, ?vcomp_vid_r, ?vcomp_assoc; apply arel_refl ]).

#[export]
Program Instance SynConv_Terminal : @Terminal SynConv := {
  terminal_obj := [];
  one := fun Γ => anil
}.

#[export]
Program Instance SynConv_Cartesian : @Cartesian SynConv := {
  product_obj := fun Γ Δ => Δ ++ Γ;
  fork := fun Ξ Γ Δ f g => vcat Δ g f;
  exl := fun Γ Δ => sexl Sym Γ Δ;
  exr := fun Γ Δ => sexr Sym Γ Δ
}.
Next Obligation. repeat intro; simpl in *; apply arel_vcat; assumption. Qed.
Next Obligation.
  simpl. split.
  - intros Hh. split.
    + rewrite <- (vcomp_sexl Sym f g). apply arel_vcomp; [apply arel_refl|exact Hh].
    + rewrite <- (vcomp_sexr Sym f g). apply arel_vcomp; [apply arel_refl|exact Hh].
  - intros [Hl Hr]. rewrite (vcat_surj Sym h). apply arel_vcat; assumption.
Qed.

Lemma arel_vcurry M Ξ Γ (f f' : args (M ++ Ξ) Γ) :
  f ≃ f' -> vcurry Sym M Ξ Γ f ≃ vcurry Sym M Ξ Γ f'.
Proof.
  induction Γ as [|σ Γ IH]; cbn; [trivial|].
  intros [H1 H2]; split; [apply conv_ren, H1|apply IH, H2].
Qed.

Lemma arel_vuncurry M Ξ Γ (g g' : args Ξ (expo M Γ)) :
  g ≃ g' -> vuncurry Sym M Ξ Γ g ≃ vuncurry Sym M Ξ Γ g'.
Proof.
  induction Γ as [|σ Γ IH]; cbn; [trivial|].
  intros [H1 H2]; split; [apply conv_ren, H1|apply IH, H2].
Qed.

#[export]
Program Instance SynConv_Closed : @Closed SynConv SynConv_Cartesian := {
  exponent_obj := fun Δ Γ => expo Δ Γ;
  exp_iso := fun Ξ Δ Γ =>
    {| to   := {| morphism := vcurry Sym Δ Ξ Γ |}
     ; from := {| morphism := vuncurry Sym Δ Ξ Γ |} |}
}.
Next Obligation. repeat intro; simpl in *; apply arel_vcurry; assumption. Qed.
Next Obligation. repeat intro; simpl in *; apply arel_vuncurry; assumption. Qed.
Next Obligation. simpl; rewrite vcurry_vuncurry; apply arel_refl. Qed.
Next Obligation. simpl; rewrite vuncurry_vcurry; apply arel_refl. Qed.
Next Obligation.
  simpl. unfold first; simpl.
  change (vcat y (sexr Sym x y) (vcomp (vcurry Sym y x z f) (sexl Sym x y)))
    with (sfirst Sym y (vcurry Sym y x z f)).
  rewrite vuncurry_nat, vcomp_vid_l, vuncurry_vcurry. apply arel_refl.
Qed.

End SynConv.
