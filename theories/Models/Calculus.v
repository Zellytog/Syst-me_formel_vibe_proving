(** * Modèles des systèmes de calcul

    Un modèle d'un système de calcul (Sig, ~) dans une catégorie cartésienne
    fermée C est un **morphisme de CCC** depuis la catégorie syntaxique
    modulo conversion [SynConv] : un foncteur qui préserve l'objet terminal,
    les produits et les exponentielles *à isomorphisme canonique près*
    ([CartesianFunctor] et [ClosedFunctor] de la bibliothèque category-theory ;
    pour l'objet terminal, M [] est isomorphe à 1).

    Par construction, deux termes convertibles ont la même interprétation, et
    la substitution est interprétée par la composition. On retrouve les
    données « concrètes » d'un modèle :
    - un objet ⟦s⟧ := M [ι s] pour chaque sorte ;
    - un morphisme ⟦f⟧ : M (dom σ) ~> ⟦cod σ⟧ pour chaque symbole f : σ ;
    - l'interprétation ⟦t⟧ : M Γ ~> ⟦s⟧ de chaque terme t : tm Γ s.

    Le foncteur identité de [SynConv] est le **modèle syntaxique**. *)

From Category Require Import Lib Theory.Category Theory.Isomorphism Theory.Functor
  Structure.Terminal Structure.Cartesian Structure.Cartesian.Closed
  Functor.Structure.Cartesian Functor.Structure.Cartesian.Closed.
From Stdlib Require Import List.
Import ListNotations.
From SF.Syntax Require Import Spec Terms Vectors Syn.
From SF.Calculus Require Import System SynConv.
From SF.Logic Require Import Judgment.

Local Notation ι a := (Spec [] a).

(** ** Modèles *)

Section Models.
Context {Srt : Type} {Sym : spec Srt -> Type} (S : system Sym).
Context (C : Category) {CT : @Terminal C} {CC : @Cartesian C} {CL : @Closed C CC}.

Local Notation Syn := (SynConv S).

Record cmodel := {
  cm_fun :> Syn ⟶ C;
  cm_terminal : cm_fun [] ≅ 1;
  cm_cartesian : @CartesianFunctor Syn C cm_fun (SynConv_Cartesian S) CC;
  cm_closed : @ClosedFunctor Syn C cm_fun (SynConv_Cartesian S) CC cm_cartesian (SynConv_Closed S) CL
}.

(** Un terme est un morphisme de la catégorie syntaxique vers le contexte
    [ι s] : le vecteur à une composante. *)
Definition hat {Γ s} (t : Terms.tm Sym Γ s) : @hom Syn Γ [ι s] :=
  @acons _ Sym Γ (ι s) [] t anil.

Context (M : cmodel).

Definition sort_obj (s : Srt) : C := M [ι s].
Definition ctx_obj (Γ : ctx Srt) : C := M Γ.

(** Interprétation d'un terme. *)
Definition sem {Γ s} (t : Terms.tm Sym Γ s) : ctx_obj Γ ~> sort_obj s := fmap[M] (hat t).

(** Interprétation d'un symbole : celle de son terme générique f(x₁, …, xₙ). *)
Definition sym_mor {σ} (c : Sym σ) : ctx_obj (dom σ) ~> sort_obj (cod σ) :=
  sem (@tsym _ Sym (dom σ) σ c (vid (dom σ))).

(** *** Correction du calcul : deux termes convertibles ont la même interprétation *)
Theorem sem_conv {Γ s} (t u : Terms.tm Sym Γ s) : conv S t u -> sem t ≈ sem u.
Proof. intros H. unfold sem. apply fmap_respects. simpl. split; [exact H|exact Logic.I]. Qed.

(** *** La substitution est interprétée par la composition *)
Lemma hat_vsubst {Γ Δ s} (t : Terms.tm Sym Γ s) (v : vec Sym Γ Δ) :
  @equiv _ (@homset Syn Δ [ι s]) (hat (vsubst t v)) (@compose Syn Δ Γ [ι s] (hat t) v).
Proof.
  simpl. unfold vcomp, hat; cbn [vmap]. split; [|exact Logic.I].
  cbn [ahd]. rewrite vsubst_tms_nil. apply conv_refl.
Qed.

Theorem sem_vsubst {Γ Δ s} (t : Terms.tm Sym Γ s) (v : vec Sym Γ Δ) :
  sem (vsubst t v) ≈ sem t ∘ fmap[M] v.
Proof. unfold sem. etransitivity; [apply fmap_respects, hat_vsubst|apply fmap_comp]. Qed.

(** L'interprétation d'une application de symbole. *)
Theorem sem_tsym {σ Γ} (c : Sym σ) (a : args Sym Γ (dom σ)) :
  sem (tsym c a) ≈ sym_mor c ∘ fmap[M] a.
Proof.
  unfold sym_mor. rewrite <- sem_vsubst. apply sem_conv.
  assert (E : vsubst (@tsym _ Sym (dom σ) σ c (vid (dom σ))) a = tsym c a).
  { transitivity (@tsym _ Sym Γ σ c (vsubst_args (vid (dom σ)) a)); [reflexivity|]. f_equal.
    apply vec_ext; intros τ z. unfold vget, vsubst_args.
    rewrite aget_subst_args, aget_vid. apply vsubst_eta. }
  rewrite E. apply conv_refl.
Qed.

End Models.

Arguments cm_fun {Srt Sym S C CT CC CL} c.
Arguments hat {Srt Sym S Γ s} t.
Arguments sort_obj {Srt Sym S C CT CC CL} M s.
Arguments ctx_obj {Srt Sym S C CT CC CL} M Γ.
Arguments sem {Srt Sym S C CT CC CL} M {Γ s} t.
Arguments sym_mor {Srt Sym S C CT CC CL} M {σ} c.

(** ** Le modèle syntaxique *)

Section Syntactic.
Context {Srt : Type} {Sym : spec Srt -> Type} (S : system Sym).

Local Notation Syn := (SynConv S).

#[local] Program Instance id_cartesian : @CartesianFunctor Syn Syn Id (SynConv_Cartesian S) (SynConv_Cartesian S) := {
  fobj_prod_iso := fun x y => iso_id
}.
Next Obligation. simpl; rewrite ?vcomp_vid_l, ?vcomp_vid_r; first [apply arel_refl | cat]. Qed.
Next Obligation. simpl; rewrite ?vcomp_vid_l, ?vcomp_vid_r; first [apply arel_refl | cat]. Qed.
Next Obligation. simpl; rewrite ?vcomp_vid_l, ?vcomp_vid_r; first [apply arel_refl | cat]. Qed.

#[local] Program Instance id_closed :
  @ClosedFunctor Syn Syn Id (SynConv_Cartesian S) (SynConv_Cartesian S) id_cartesian
    (SynConv_Closed S) (SynConv_Closed S) := {
  fobj_exp_iso := fun x y => iso_id
}.
Next Obligation. simpl; rewrite ?vcomp_vid_l, ?vcomp_vid_r; first [apply arel_refl | cat]. Qed.
Next Obligation. simpl; rewrite ?vcomp_vid_l, ?vcomp_vid_r; first [apply arel_refl | cat]. Qed.

Definition syn_model : cmodel S Syn := {|
  cm_fun := Id;
  cm_terminal := iso_id;
  cm_cartesian := id_cartesian;
  cm_closed := id_closed
|}.

End Syntactic.
