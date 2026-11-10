(** * La catégorie syntaxique et sa structure cartésienne fermée

    On utilise la bibliothèque category-theory de John Wiegley (homs
    setoïdes, sans axiome).

    - Objets : les contextes.
    - Morphismes Γ ~> Δ : les vecteurs de termes de Γ pour les variables
      de Δ, c'est-à-dire [args Γ Δ] (= [vec Δ Γ]).
    - Identité : [vid] ; composition : [vcomp].
    - Égalité des morphismes : l'égalité de Leibniz des vecteurs. Plus tard,
      la catégorie « modulo conversion » s'obtiendra en changeant seulement
      cette relation de setoïde.

    Produit : [Γ × Δ := Δ ++ Γ], de sorte que les variables du second facteur
    sont les plus récentes. Exponentielle : [Γ^Δ] remplace chaque
    spécification [Spec D c] de Γ par [Spec (D ++ Δ) c]. Curryfication et
    décurryfication sont alors des renommages de réassociation
    [D ++ (Δ ++ Ξ) ≃ (D ++ Δ) ++ Ξ]. *)

From Category Require Import Lib Theory.Category Theory.Isomorphism
  Structure.Terminal Structure.Cartesian Structure.Cartesian.Closed Instance.Sets.
From Stdlib Require Import List.
Import ListNotations.
From SF.Syntax Require Import Spec Terms Renaming Traversal Eta Composition Vectors.

Section Syn.

Context {Srt : Type} (Sym : spec Srt -> Type).
Implicit Types (Λ Θ Γ Δ Ξ A B D M : ctx Srt) (σ τ ρ : spec Srt).

Local Notation tm := (Terms.tm Sym).
Local Notation args := (Terms.args Sym).
Local Notation tms := (Terms.tms Sym).
Local Notation vec := (Vectors.vec Sym).

(** ** La catégorie *)

#[export]
Program Instance Syn : Category := {
  obj := ctx Srt;
  hom := fun Γ Δ => args Γ Δ;
  homset := fun Γ Δ => eq_Setoid (args Γ Δ);
  id := fun Γ => vid Γ;
  compose := fun Γ Δ Ξ f g => vcomp f g
}.
Next Obligation. simpl; rewrite vcomp_vid_l; reflexivity. Qed.
Next Obligation. simpl; rewrite vcomp_vid_r; reflexivity. Qed.
Next Obligation. simpl; rewrite vcomp_assoc; reflexivity. Qed.
Next Obligation. simpl; rewrite vcomp_assoc; reflexivity. Qed.

(** ** Objet terminal : le contexte vide *)

#[export]
Program Instance Syn_Terminal : @Terminal Syn := {
  terminal_obj := [];
  one := fun Γ => anil
}.
Next Obligation. simpl in *. rewrite (args_nil f), (args_nil g); reflexivity. Qed.

(** ** Produits : concaténation *)

Definition sexl Γ Δ : args (Δ ++ Γ) Γ := etas Γ (fun ρ v => vr Δ v).
Definition sexr Γ Δ : args (Δ ++ Γ) Δ := etas Δ (fun ρ v => vl Γ v).

(** Composer avec un vecteur d'η-expansés de variables, c'est réindexer. *)
Lemma aget_vcomp_etas {Γ Δ Ξ σ} (f : forall ρ, var Γ ρ -> var Δ ρ) (h : args Ξ Δ) (z : var Γ σ) :
  aget z (vcomp (etas Γ f) h) = aget (f σ z) h.
Proof. rewrite aget_vcomp, aget_etas; apply vsubst_eta. Qed.

Lemma vcomp_sexl {Γ Δ Ξ} (f : args Ξ Γ) (g : args Ξ Δ) : vcomp (sexl Γ Δ) (vcat Δ g f) = f.
Proof. apply vec_ext; intros σ z; unfold vget, sexl; rewrite aget_vcomp_etas, aget_vcat_r; reflexivity. Qed.

Lemma vcomp_sexr {Γ Δ Ξ} (f : args Ξ Γ) (g : args Ξ Δ) : vcomp (sexr Γ Δ) (vcat Δ g f) = g.
Proof. apply vec_ext; intros σ z; unfold vget, sexr; rewrite aget_vcomp_etas, aget_vcat_l; reflexivity. Qed.

Lemma vcat_surj {Γ Δ Ξ} (h : args Ξ (Δ ++ Γ)) :
  h = vcat Δ (vcomp (sexr Γ Δ) h) (vcomp (sexl Γ Δ) h).
Proof.
  apply vec_ext; intros σ x; unfold vget. vcase x;
    rewrite ?aget_vcat_l, ?aget_vcat_r; unfold sexl, sexr; rewrite aget_vcomp_etas; reflexivity.
Qed.

#[export]
Program Instance Syn_Cartesian : @Cartesian Syn := {
  product_obj := fun Γ Δ => Δ ++ Γ;
  fork := fun Ξ Γ Δ f g => vcat Δ g f;
  exl := fun Γ Δ => sexl Γ Δ;
  exr := fun Γ Δ => sexr Γ Δ
}.
Next Obligation.
  simpl. split.
  - intros ->. split; [apply vcomp_sexl|apply vcomp_sexr].
  - intros [Hl Hr]. rewrite (vcat_surj h), Hl, Hr; reflexivity.
Qed.

(** ** Réassociation des contextes *)

Definition assoc_l D M Ξ : ren (D ++ (M ++ Ξ)) ((D ++ M) ++ Ξ) :=
  fun σ v => match vsplit D v with
             | inl z => vl Ξ (vl M z)
             | inr w => match vsplit M w with
                        | inl m => vl Ξ (vr D m)
                        | inr a => vr (D ++ M) a
                        end
             end.

Definition assoc_r D M Ξ : ren ((D ++ M) ++ Ξ) (D ++ (M ++ Ξ)) :=
  fun σ v => match vsplit (D ++ M) v with
             | inl w => match vsplit D w with
                        | inl z => vl (M ++ Ξ) z
                        | inr m => vr D (vl Ξ m)
                        end
             | inr a => vr D (vr M a)
             end.

Lemma assoc_l_D D M Ξ σ (z : var D σ) : assoc_l D M Ξ σ (vl (M ++ Ξ) z) = vl Ξ (vl M z).
Proof. unfold assoc_l; rewrite vsplit_vl; reflexivity. Qed.
Lemma assoc_l_M D M Ξ σ (m : var M σ) : assoc_l D M Ξ σ (vr D (vl Ξ m)) = vl Ξ (vr D m).
Proof. unfold assoc_l; rewrite vsplit_vr, vsplit_vl; reflexivity. Qed.
Lemma assoc_l_X D M Ξ σ (a : var Ξ σ) : assoc_l D M Ξ σ (vr D (vr M a)) = vr (D ++ M) a.
Proof. unfold assoc_l; rewrite !vsplit_vr; reflexivity. Qed.
Lemma assoc_r_D D M Ξ σ (z : var D σ) : assoc_r D M Ξ σ (vl Ξ (vl M z)) = vl (M ++ Ξ) z.
Proof. unfold assoc_r; rewrite !vsplit_vl; reflexivity. Qed.
Lemma assoc_r_M D M Ξ σ (m : var M σ) : assoc_r D M Ξ σ (vl Ξ (vr D m)) = vr D (vl Ξ m).
Proof. unfold assoc_r; rewrite vsplit_vl, vsplit_vr; reflexivity. Qed.
Lemma assoc_r_X D M Ξ σ (a : var Ξ σ) : assoc_r D M Ξ σ (vr (D ++ M) a) = vr D (vr M a).
Proof. unfold assoc_r; rewrite vsplit_vr; reflexivity. Qed.

Lemma assoc_rl D M Ξ σ (v : var (D ++ (M ++ Ξ)) σ) : assoc_r D M Ξ σ (assoc_l D M Ξ σ v) = v.
Proof.
  vcase v; [rewrite assoc_l_D, assoc_r_D; reflexivity|].
  vcase z; [rewrite assoc_l_M, assoc_r_M; reflexivity|].
  rewrite assoc_l_X, assoc_r_X; reflexivity.
Qed.

Lemma assoc_lr D M Ξ σ (v : var ((D ++ M) ++ Ξ) σ) : assoc_l D M Ξ σ (assoc_r D M Ξ σ v) = v.
Proof.
  vcase v; [|rewrite assoc_r_X, assoc_l_X; reflexivity].
  vcase z; [rewrite assoc_r_D, assoc_l_D|rewrite assoc_r_M, assoc_l_M]; reflexivity.
Qed.

(** ** Exponentielles *)

Fixpoint expo M (Γ : ctx Srt) : ctx Srt :=
  match Γ with
  | [] => []
  | σ :: Γ' => Spec (Spec.dom σ ++ M) (Spec.cod σ) :: expo M Γ'
  end.

Fixpoint vcurry M Ξ Γ : args (M ++ Ξ) Γ -> args Ξ (expo M Γ) :=
  match Γ return args (M ++ Ξ) Γ -> args Ξ (expo M Γ) with
  | [] => fun _ => anil
  | σ :: Γ' => fun f =>
      @acons _ Sym Ξ (Spec (Spec.dom σ ++ M) (Spec.cod σ)) (expo M Γ')
        (ren_tm (ahd f) (assoc_l (Spec.dom σ) M Ξ)) (vcurry M Ξ Γ' (atl f))
  end.

Fixpoint vuncurry M Ξ Γ : args Ξ (expo M Γ) -> args (M ++ Ξ) Γ :=
  match Γ return args Ξ (expo M Γ) -> args (M ++ Ξ) Γ with
  | [] => fun _ => anil
  | σ :: Γ' => fun g =>
      @acons _ Sym (M ++ Ξ) σ Γ'
        (ren_tm (s := Spec.cod σ) (Γ := (Spec.dom σ ++ M) ++ Ξ) (ahd g) (assoc_r (Spec.dom σ) M Ξ))
        (vuncurry M Ξ Γ' (atl g))
  end.

Lemma vuncurry_vcurry M Ξ Γ (f : args (M ++ Ξ) Γ) : vuncurry M Ξ Γ (vcurry M Ξ Γ f) = f.
Proof.
  induction Γ as [|σ Γ IH]; cbn.
  - symmetry; apply args_nil.
  - refine (eq_trans _ (eq_sym (args_eta f))). f_equal; [|apply IH].
    rewrite ren_ren, (ren_ext (ahd f) _ rid); [apply ren_id|intros; apply assoc_rl].
Qed.

Lemma vcurry_vuncurry M Ξ Γ (g : args Ξ (expo M Γ)) : vcurry M Ξ Γ (vuncurry M Ξ Γ g) = g.
Proof.
  induction Γ as [|σ Γ IH]; cbn.
  - symmetry; apply args_nil.
  - refine (eq_trans _ (eq_sym (args_eta g))). f_equal; [|apply IH].
    rewrite ren_ren, (ren_ext (ahd g) _ rid); [apply ren_id|intros; apply assoc_lr].
Qed.

(** *** Substituer par des η-expansés de variables, c'est renommer *)

Lemma vsubst_tms_etas {Γ Δ σ} (u : tms Γ σ) (f : ren Γ Δ) :
  vsubst_tms u (etas Γ f) = ren_tms u f.
Proof.
  unfold vsubst_tms, ren_tms. rewrite ren_as_subst, subst_tms_up.
  apply subst_ext; intros ρ v; unfold vget, up_sub, rs_comp, ids.
  vcase v; autorewrite with vsimpl; rewrite ?aget_etas; [reflexivity|].
  unfold sr_comp; rewrite aget_etas, eta_ren; reflexivity.
Qed.

(** *** Naturalité de la décurryfication *)

(** [first h] dans la catégorie syntaxique. *)
Definition sfirst M {A B} (h : args B A) : args (M ++ B) (M ++ A) :=
  vcat M (sexr B M) (vcomp h (sexl B M)).

Lemma head_nat D M {A B} c (u : tm ((D ++ M) ++ A) c) (h : args B A) :
  vsubst_tms (σ := Spec D c) (ren_tm u (assoc_r D M A)) (sfirst M h) =
  ren_tm (vsubst_tms (σ := Spec (D ++ M) c) u h) (assoc_r D M B).
Proof.
  rewrite !vsubst_tms_vup; cbn [Spec.dom]. rewrite vsubst_ren, ren_vsubst.
  unfold vsubst; apply subst_ext; intros ρ v; unfold vget.
  rewrite aget_vpre; unfold vren; rewrite aget_vmap. unfold vup, vren.
  vcase v.
  - vcase z.
    + rewrite assoc_r_D, aget_vcat_l, aget_vcat_l, !aget_etas, eta_ren, assoc_r_D; reflexivity.
    + rewrite assoc_r_M, aget_vcat_r, aget_vmap. unfold sfirst, sexr.
      rewrite !aget_vcat_l, !aget_etas, !eta_ren, assoc_r_M; reflexivity.
  - rewrite assoc_r_X, !aget_vcat_r, !aget_vmap. unfold sfirst, sexl.
    rewrite aget_vcat_r, aget_vcomp, vsubst_tms_etas, !ren_tms_ren.
    apply ren_tms_ext; intros τ y; unfold rcomp, wk.
    rewrite assoc_r_X; reflexivity.
Qed.

Lemma vuncurry_nat M {A B} Γ (g : args A (expo M Γ)) (h : args B A) :
  vcomp (vuncurry M A Γ g) (sfirst M h) = vuncurry M B Γ (vcomp g h).
Proof.
  induction Γ as [|σ Γ IH]; cbn; [reflexivity|].
  f_equal; [|apply IH].
  destruct σ as [D c]; cbn [Spec.dom Spec.cod] in *. apply head_nat.
Qed.

(** ** La structure fermée *)

#[export]
Program Instance Syn_Closed : @Closed Syn Syn_Cartesian := {
  exponent_obj := fun Δ Γ => expo Δ Γ;
  exp_iso := fun Ξ Δ Γ =>
    {| to   := {| morphism := vcurry Δ Ξ Γ |}
     ; from := {| morphism := vuncurry Δ Ξ Γ |} |}
}.
Next Obligation. simpl; apply vcurry_vuncurry. Qed.
Next Obligation. simpl; apply vuncurry_vcurry. Qed.
Next Obligation.
  simpl. unfold first; simpl.
  change (vcat y (sexr x y) (vcomp (vcurry y x z f) (sexl x y))) with (sfirst y (vcurry y x z f)).
  rewrite vuncurry_nat, vcomp_vid_l. apply vuncurry_vcurry.
Qed.

End Syn.
