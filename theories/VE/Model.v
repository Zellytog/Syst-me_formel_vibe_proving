(** * Le modèle V(E) de IZFε : l'interprétation des symboles

    Les sortes : V ↦ [Vset] (les arbres à la Aczel, à égalité de forme et
    ≡ des étiquettes), Pr ↦ Φ. Les symboles logiques sont standard ; les
    relations et constructions ensemblistes sont celles de [Base.v],
    [Cons.v] et [Coll.v]. Les lieurs (Sep, Repl, Rec) reçoivent des
    morphismes de setoïdes, déjà propres. *)

From Category Require Import Lib Theory.Category.
From Stdlib Require Import List.
Import ListNotations.
From SF.Syntax Require Import Spec Terms.
From SF.Calculus Require Import System Rules.
From SF.Logic Require Import Judgment Propositional.
From SF.Functional Require Import Arrow Graded.
From SF.Quantifiers Require Import Quant Order.
From SF.Models Require Import PSet Frame Semantics FrameModel Tarski FrameTarski.
From SF.VE Require Import Trees Base Cons Coll.
From SF.SetTheory Require Import IZFe.

Local Notation ι a := (Spec [] a).

Set Default Proof Using "All".

Section Model.

Context (F : frame).

Local Notation VV := (Trees.V F).

Definition So (s : isort) : pset := match s with V => Vset F | Pr => fprop F end.

Local Notation E s := (pexp punit (So s)).
Local Notation pc x := (pconst So (s := V) x).

(** Les arguments d'un lieur unaire ou binaire, vus comme fonctions. *)
Definition b1 (f : pexp (pprod punit (E V)) (So Pr)) : pmor (Vset F) F :=
  Build_pmor (Vset F) F (fun x => (f : pmor _ _) (up1 So V x))
    (fun x x' Ex => pfun_proper f (pfun_proper (up1 So V) Ex)).

Definition b2 (f : pexp (pprod (pprod punit (E V)) (E V)) (So Pr)) : VV -> VV -> pcar F :=
  fun x y => (f : pmor _ _) ((tt, pc y), pc x).

Lemma b2_proper f : Rproper F (b2 f).
Proof.
  intros x x' y y' Ex Ey. unfold b2. apply pfun_proper.
  split; [split; [exact Logic.I|intros u; exact Ey]|intros u; exact Ex].
Qed.

Lemma b1_ext f f' : f ≡ f' -> forall x, b1 f x ≡ b1 f' x.
Proof. intros H x. apply H. Qed.

Lemma b2_ext f f' : f ≡ f' -> forall x y, b2 f x y ≡ b2 f' x y.
Proof. intros H x y. apply H. Qed.

(** *** Les symboles *)

Local Notation Q2 s := (pprod (pprod punit (E s)) (E s)).

Definition y_bin (op : pcar F -> pcar F -> pcar F) (Hop : forall φ φ' ψ ψ', φ ≡ φ' -> ψ ≡ ψ' -> op φ ψ ≡ op φ' ψ') :
  pmor (Q2 Pr) (So Pr).
Proof.
  refine (Build_pmor (Q2 Pr) (So Pr) (fun q : pcar (Q2 Pr) => op (snd q tt) (snd (fst q) tt)) _).
  intros [[u a] b] [[u' a'] b'] [[_ Ha] Hb]. cbn in *. apply Hop; [apply Hb|apply Ha].
Defined.

Definition y_rel (op : VV -> VV -> pcar F) (Hop : forall x x' y y', teq F x x' -> teq F y y' -> op x y ≡ op x' y') :
  pmor (Q2 V) (So Pr).
Proof.
  refine (Build_pmor (Q2 V) (So Pr) (fun q : pcar (Q2 V) => op (snd q tt) (snd (fst q) tt)) _).
  intros [[u a] b] [[u' a'] b'] [[_ Ha] Hb]. cbn in *. apply Hop; [apply Hb|apply Ha].
Defined.

Definition y_cst (k : pcar F) : pmor punit (So Pr) := Build_pmor punit (So Pr) (fun _ => k) (fun _ _ _ => peq_refl _).
Definition y_vcst (k : VV) : pmor punit (So V) := Build_pmor punit (So V) (fun _ => k) (fun _ _ _ => teq_refl F k).

Local Notation Qp := (pprod punit (pexp (pprod punit (E V)) (So Pr))).

Definition y_all : pmor Qp (So Pr).
Proof.
  refine (Build_pmor Qp (So Pr) (fun q : pcar Qp => fall (fun a : VV => (snd q : pmor _ _) (up1 So V a))) _).
  intros [u f] [u' f'] [_ H]. cbn in *. apply fall_proper. intros a. apply H.
Defined.

Definition y_ex : pmor Qp (So Pr).
Proof.
  refine (Build_pmor Qp (So Pr) (fun q : pcar Qp => fex (fun a : VV => (snd q : pmor _ _) (up1 So V a))) _).
  intros [u f] [u' f'] [_ H]. cbn in *. apply fex_proper. intros a. apply H.
Defined.

Definition y_un (op : VV -> VV) (Hop : forall x x', teq F x x' -> teq F (op x) (op x')) :
  pmor (pprod punit (E V)) (So V).
Proof.
  refine (Build_pmor (pprod punit (E V)) (So V) (fun q : pcar (pprod punit (E V)) => op (snd q tt)) _).
  intros [u a] [u' a'] [_ Ha]. cbn in *. apply Hop, Ha.
Defined.

Definition y_pair : pmor (Q2 V) (So V).
Proof.
  refine (Build_pmor (Q2 V) (So V) (fun q : pcar (Q2 V) => vpair F (snd q tt) (snd (fst q) tt)) _).
  intros [[u a] b] [[u' a'] b'] [[_ Ha] Hb]. cbn in *. apply vpair_proper; [apply Hb|apply Ha].
Defined.

Local Notation Qsep := (pprod (pprod punit (pexp (pprod punit (E V)) (So Pr))) (E V)).

Definition y_sep : pmor Qsep (So V).
Proof.
  refine (Build_pmor Qsep (So V) (fun q : pcar Qsep => vsep F (snd q tt) (b1 (snd (fst q)))) _).
  intros [[u f] a] [[u' f'] a'] [[_ Hf] Ha]. cbn in *. apply vsep_proper; [apply Ha|].
  intros x. apply Hf.
Defined.

Context (Φ0 : Type) (enc : pcar F -> Φ0) (dec : Φ0 -> pcar F).
Context (coll : forall T, (T -> Trees.V F) -> (Trees.V F -> Trees.V F -> pcar F) -> Trees.V F).
Context (coll_proper : forall T (xs xs' : T -> Trees.V F) ψ ψ', Rproper F ψ ->
           (forall t, teq F (xs t) (xs' t)) -> (forall x y, ψ x y ≡ ψ' x y) ->
           teq F (coll T xs ψ) (coll T xs' ψ')).

Local Notation ER := (pexp (pprod (pprod punit (E V)) (E V)) (So Pr)).
Local Notation Qrepl := (pprod (pprod punit ER) (E V)).

Definition y_repl : pmor Qrepl (So V).
Proof.
  refine (Build_pmor Qrepl (So V) (fun q : pcar Qrepl => vrepl F coll (snd q tt) (b2 (snd (fst q)))) _).
  intros [[u f] a] [[u' f'] a'] [[_ Hf] Ha]. cbn in *.
  apply vrepl_proper; [exact coll_proper|apply b2_proper|apply Ha|intros x y; apply Hf].
Defined.

Local Notation Qrec := (pprod (pprod (pprod punit (E V)) ER) (pexp (pprod punit (E V)) (So Pr))).

Definition y_rec : pmor Qrec (So V).
Proof.
  refine (Build_pmor Qrec (So V) (fun q : pcar Qrec => vrec F coll (b2 (snd (fst q))) (snd (fst (fst q)) tt)) _).
  intros [[[u a] f] g] [[[u' a'] f'] g'] [[[_ Ha] Hf] _]. cbn in *.
  apply vrec_proper; [exact coll_proper|apply b2_proper|intros x y; apply Hf|apply Ha].
Defined.

Definition Iy (σ : spec isort) (c : isym σ) : ictx PSet So (dom σ) ~> So (cod σ) :=
  match c in isym σ0 return ictx PSet So (dom σ0) ~> So (cod σ0) with
  | i_imp => y_bin fimp (fimp_proper F)
  | i_and => y_bin fand (fand_proper F)
  | i_or => y_bin for_ for_proper
  | i_top => y_cst ftop
  | i_bot => y_cst fbot
  | i_all => y_all
  | i_ex => y_ex
  | i_eq => y_rel (veq F) (veq_proper F)
  | i_eps => y_rel (eps F) (eps_proper F)
  | i_mem => y_rel (vmem F) (vmem_proper F)
  | i_sub => y_rel (vsub F) (vsub_proper F)
  | i_eqv => y_rel (veqv F) (veqv_proper F)
  | i_empty => y_vcst (vempty F)
  | i_omega => y_vcst (vomega F)
  | i_pair => y_pair
  | i_union => y_un (vunion F) (vunion_proper F)
  | i_power => y_un (vpower F Φ0 dec) (vpower_proper F Φ0 dec)
  | i_sep => y_sep
  | i_repl => y_repl
  | i_rec => y_rec
  end.

End Model.
