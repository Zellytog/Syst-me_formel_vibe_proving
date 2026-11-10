(** * La catégorie des setoïdes propositionnels

    Les set-modèles vivent dans la catégorie [PSet] : un objet est un type
    muni d'une relation d'équivalence *à valeurs dans [Prop]*, un morphisme
    une fonction qui la respecte, et deux morphismes sont égaux quand ils le
    sont point par point. [PSet] est cartésienne fermée **sans axiome** :
    l'exponentielle est le setoïde des fonctions respectueuses avec l'égalité
    point par point, si bien qu'on n'a pas besoin de l'extensionnalité
    fonctionnelle (la catégorie [Coq] des types de category-theory, elle, la
    postule).

    Pourquoi pas la catégorie [Sets] de la bibliothèque ? Ses égalités sont à
    valeurs dans [Type]. Ici, l'égalité de deux morphismes,
    ∀ x, f x ≈ g x, est une proposition, *définitionnellement*, quels que
    soient les objets. On peut donc l'établir par récurrence sur une preuve
    de conversion (qui vit dans [Prop]) : c'est ce qui permet de valider un
    système de calcul engendré en ne vérifiant que ses règles
    ([SetModels.pset_generated]).

    Un type quelconque est un objet discret ([disc], l'égalité de Leibniz) ;
    les propositions forment l'objet [PropS] (l'équivalence logique). *)

From Category Require Import Lib Theory.Category Theory.Isomorphism Instance.Sets
  Structure.Terminal Structure.Cartesian Structure.Cartesian.Closed.

Record pset := {
  pcar :> Type;
  peq : pcar -> pcar -> Prop;
  peq_refl : forall x, peq x x;
  peq_sym : forall x y, peq x y -> peq y x;
  peq_trans : forall x y z, peq x y -> peq y z -> peq x z
}.

Arguments peq {p} x y.
Arguments peq_refl {p} x.
Arguments peq_sym {p x y} _.
Arguments peq_trans {p x y z} _ _.

Notation "x ≡ y" := (peq x y) (at level 70, no associativity).

Record pmor (X Y : pset) := {
  pfun :> X -> Y;
  pfun_proper : forall x x', x ≡ x' -> pfun x ≡ pfun x'
}.

Arguments pfun {X Y} _ _.
Arguments pfun_proper {X Y} _ {x x'} _.

(** Égalité point par point : une proposition. *)
Definition pmor_eq {X Y} (f g : pmor X Y) : Prop := forall x, f x ≡ g x.

Program Definition pmor_setoid (X Y : pset) : Setoid (pmor X Y) := {|
  equiv := fun f g => pmor_eq f g
|}.
Next Obligation.
  constructor.
  - intros f x. apply peq_refl.
  - intros f g H x. apply peq_sym, H.
  - intros f g h H1 H2 x. eapply peq_trans; [apply H1|apply H2].
Qed.

Definition pmor_id (X : pset) : pmor X X := {| pfun := fun x => x; pfun_proper := fun _ _ H => H |}.

Definition pmor_comp {X Y Z} (f : pmor Y Z) (g : pmor X Y) : pmor X Z :=
  {| pfun := fun x => f (g x); pfun_proper := fun _ _ H => pfun_proper f (pfun_proper g H) |}.

Program Instance PSet : Category := {
  obj := pset;
  hom := pmor;
  homset := pmor_setoid;
  id := pmor_id;
  compose := fun X Y Z f g => pmor_comp f g
}.
Next Obligation.
  intros f f' Hf g g' Hg a. simpl in *. eapply peq_trans; [apply pfun_proper, Hg|apply Hf].
Qed.
Next Obligation. intros a; apply peq_refl. Qed.
Next Obligation. intros a; apply peq_refl. Qed.
Next Obligation. intros a; apply peq_refl. Qed.
Next Obligation. intros a; apply peq_refl. Qed.

(** ** Objets usuels *)

Program Definition disc (A : Type) : pset := {| pcar := A; peq := @eq A |}.

Program Definition PropS : pset := {| pcar := Prop; peq := iff |}.
Next Obligation. tauto. Qed.
Next Obligation. tauto. Qed.

(** Une fonction quelconque entre objets discrets est un morphisme. *)
Definition dmap {A B : Type} (f : A -> B) : pmor (disc A) (disc B) :=
  Build_pmor (disc A) (disc B) f (fun x x' (H : x = x') => f_equal f H).

(** ** Structure cartésienne fermée *)

Program Definition punit : pset := {| pcar := unit; peq := fun _ _ => True |}.

Program Instance PSet_Terminal : @Terminal PSet := {
  terminal_obj := punit;
  one := fun X => {| pfun := fun _ => tt |}
}.
Next Obligation. intros a; exact Logic.I. Qed.

Program Definition pprod (X Y : pset) : pset := {|
  pcar := X * Y;
  peq := fun p q => fst p ≡ fst q /\ snd p ≡ snd q
|}.
Next Obligation. split; apply peq_refl. Qed.
Next Obligation. split; apply peq_sym; assumption. Qed.
Next Obligation. split; eapply peq_trans; eassumption. Qed.

Program Instance PSet_Cartesian : @Cartesian PSet := {
  product_obj := pprod;
  fork := fun X Y Z f g => {| pfun := fun x => (f x, g x) |};
  exl := fun X Y => {| pfun := fst |};
  exr := fun X Y => {| pfun := snd |}
}.
Next Obligation. split; apply pfun_proper; assumption. Qed.
Next Obligation.
  split.
  - intros E; split; intros a; apply (E a).
  - intros [H1 H2] a; split; [apply H1|apply H2].
Qed.

Program Definition pexp (Y Z : pset) : pset := {|
  pcar := pmor Y Z;
  peq := fun f g => forall y, f y ≡ g y
|}.
Next Obligation. apply peq_refl. Qed.
Next Obligation. apply peq_sym, H. Qed.
Next Obligation. eapply peq_trans; [apply H|apply H0]. Qed.

Program Definition pcurry {X Y Z} (f : pmor (pprod X Y) Z) : pmor X (pexp Y Z) := {|
  pfun := fun x => {| pfun := fun y => f (x, y) |}
|}.
Next Obligation. apply pfun_proper. split; [apply peq_refl|assumption]. Qed.
Next Obligation. apply pfun_proper. split; [assumption|apply peq_refl]. Qed.

Program Definition puncurry {X Y Z} (g : pmor X (pexp Y Z)) : pmor (pprod X Y) Z := {|
  pfun := fun p => g (fst p) (snd p)
|}.
Next Obligation.
  eapply peq_trans; [apply (pfun_proper g H)|apply pfun_proper, H0].
Qed.

Program Instance PSet_Closed : @Closed PSet PSet_Cartesian := {
  exponent_obj := pexp;
  exp_iso := fun X Y Z =>
    {| to   := {| morphism := @pcurry X Y Z |};
       from := {| morphism := @puncurry X Y Z |} |}
}.
Next Obligation. intros u u' E [a b]. apply E. Qed.
Next Obligation. intros a b. apply peq_refl. Qed.
Next Obligation. intros [a b]. apply peq_refl. Qed.
Next Obligation. intros [a b]. apply peq_refl. Qed.

(** Dans [PSet], l'égalité de deux morphismes se lit point par point. *)
Definition pset_equiv_at {X Y : PSet} {f g : X ~> Y} : f ≈ g -> forall x, f x ≡ g x := fun H => H.
Definition pset_equiv_intro {X Y : PSet} {f g : X ~> Y} : (forall x, f x ≡ g x) -> f ≈ g := fun H => H.
