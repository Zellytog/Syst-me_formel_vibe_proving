(** * Le système libre d'ordre (n,p) engendré par une signature

    Donnée : un type [S] de sortes de base et une famille [K] de constantes
    (la signature non logique). On construit :
    - les sortes : les types simples sur S et la sorte des propositions O
      ([fty S]), restreints à ceux dont le grade est sous la borne (n,p) ;
    - les symboles : λ et app pour toutes les flèches présentes, les
      connecteurs, ∀, ∃ et = pour toutes les sortes *quantifiables*
      (strictement sous (n,p)), et les constantes de [K] ;
    - les instances des classes du formalisme ([Functional], [Graded],
      [Bounded n p], [PropGrade], les connecteurs, [Quantifiers n p]) ;
    - la logique libre [Free] : le calcul β et les règles de la logique
      intuitionniste d'ordre (n,p), sans aucun axiome ([FreeC] : la version
      classique) ; et [Theory CR DR], qui y ajoute des règles de calcul et de
      déduction.

    Les sortes de base sont de grade (0,0), O de grade (0,1). Le cas (ω,ω)
    ([Free_omega]) contient toutes les sortes, toutes quantifiables.

    Les preuves d'appartenance à la borne sont des égalités booléennes, ce
    qui donne l'unicité de leurs preuves sans axiome. *)

From Stdlib Require Import List Arith Lia Bool.
Import ListNotations.
From SF.Syntax Require Import Spec Terms Vectors.
From SF.Calculus Require Import System Rules.
From SF.Logic Require Import Judgment Propositional.
From SF.Functional Require Import Arrow Graded.
From SF.Quantifiers Require Import Quant Order.
From SF.Extensions Require Import RuleExt.

Local Notation ι a := (Spec [] a).

(** ** Types simples et grades *)

Inductive fty (S : Type) : Type :=
| tbase (s : S)
| tO
| tarr (a b : fty S).

Arguments tbase {S} s.
Arguments tO {S}.
Arguments tarr {S} a b.

Fixpoint tgr {S} (t : fty S) : grade :=
  match t with
  | tbase _ => (0, 0)
  | tO => (0, 1)
  | tarr a b => garr (tgr a) (tgr b)
  end.

(** Versions booléennes de ≤ b et < b. *)
Definition bleb (m : nat) (b : bound) : bool :=
  match b with fin k => Nat.leb m k | omega => true end.
Definition bltb (m : nat) (b : bound) : bool :=
  match b with fin k => Nat.ltb m k | omega => true end.

Lemma bleb_spec m b : bleb m b = true <-> ble m b.
Proof. destruct b; cbn; [apply Nat.leb_le|tauto]. Qed.

Lemma bltb_spec m b : bltb m b = true <-> blt m b.
Proof. destruct b; cbn; [apply Nat.ltb_lt|tauto]. Qed.

(** ** La signature *)

Section FreeSig.

Context (S : Type) (n p : bound).

(** Les sortes du système : les types dont le grade est sous (n,p). *)
Definition inb (t : fty S) : bool := bleb (fst (tgr t)) n && bleb (snd (tgr t)) p.
Definition srt : Type := { t : fty S | inb t = true }.

(** Les sortes quantifiables : grade strictement sous (n,p). *)
Definition qb (t : fty S) : bool := bltb (fst (tgr t)) n && bltb (snd (tgr t)) p.

(** La flèche a → b est présente quand son grade reste sous la borne. *)
Inductive farr : srt -> srt -> srt -> Type :=
| farr_i (a b : srt) (h : inb (tarr (proj1_sig a) (proj1_sig b)) = true) :
    farr a b (exist _ _ h).

(** La sorte des propositions est présente (p ≥ 1). *)
Context (hO : inb tO = true).
Definition sO : srt := exist _ tO hO.

(** Les constantes de la signature. *)
Context (K : spec srt -> Type).

Inductive fsym : spec srt -> Type :=
| f_lam (a b c : srt) (w : farr a b c) : fsym (Spec [Spec [ι a] b] c)
| f_app (a b c : srt) (w : farr a b c) : fsym (Spec [ι c; ι a] b)
| f_imp : fsym (Spec [ι sO; ι sO] sO)
| f_and : fsym (Spec [ι sO; ι sO] sO)
| f_or : fsym (Spec [ι sO; ι sO] sO)
| f_top : fsym (ι sO)
| f_bot : fsym (ι sO)
| f_all (s : srt) (q : qb (proj1_sig s) = true) : fsym (Spec [Spec [ι s] sO] sO)
| f_ex (s : srt) (q : qb (proj1_sig s) = true) : fsym (Spec [Spec [ι s] sO] sO)
| f_eq (s : srt) (q : qb (proj1_sig s) = true) : fsym (Spec [ι s; ι s] sO)
| f_const (σ : spec srt) (k : K σ) : fsym σ.

(** ** Instances *)

#[export] Instance free_functional : Functional fsym := {|
  Arr := farr;
  s_lam := fun a b c w => f_lam a b c w;
  s_app := fun a b c w => f_app a b c w
|}.

Definition sgr (s : srt) : grade := tgr (proj1_sig s).

Lemma sgr_arr a b c (w : farr a b c) : sgr c = garr (sgr a) (sgr b).
Proof. destruct w. reflexivity. Qed.

#[export] Instance free_graded : Graded fsym := {| gr := sgr; gr_arr := sgr_arr |}.

Lemma inb_gleb t : inb t = true <-> gleb (tgr t) n p.
Proof.
  unfold inb, gleb. rewrite andb_true_iff, !bleb_spec. tauto.
Qed.

Lemma qb_quantifiable (s : srt) : qb (proj1_sig s) = true <-> quantifiable (Sym := fsym) n p s.
Proof.
  unfold qb, quantifiable, gbelow. cbn. unfold sgr. rewrite andb_true_iff, !bltb_spec. tauto.
Qed.

#[export] Instance free_bounded : Bounded fsym n p.
Proof.
  split.
  - intros s. cbn. unfold sgr. apply inb_gleb. exact (proj2_sig s).
  - intros a b H.
    assert (h : inb (tarr (proj1_sig a) (proj1_sig b)) = true) by (apply inb_gleb; exact H).
    exact (existT _ (exist _ _ h) (farr_i a b h)).
Defined.

#[export] Instance free_propgrade : PropGrade fsym sO.
Proof. split. reflexivity. Defined.

#[export] Instance free_hasimp : HasImp fsym sO := {| c_imp := f_imp |}.
#[export] Instance free_hasand : HasAnd fsym sO := {| c_and := f_and |}.
#[export] Instance free_hasor : HasOr fsym sO := {| c_or := f_or |}.
#[export] Instance free_hastop : HasTop fsym sO := {| c_top := f_top |}.
#[export] Instance free_hasbot : HasBot fsym sO := {| c_bot := f_bot |}.

#[export] Instance free_quantifiers : Quantifiers fsym sO n p := {|
  q_all := fun s h => f_all s (proj2 (qb_quantifiable s) h);
  q_ex := fun s h => f_ex s (proj2 (qb_quantifiable s) h);
  q_eq := fun s h => f_eq s (proj2 (qb_quantifiable s) h)
|}.

(** ** Les logiques *)

Definition free_calc : system fsym := generated (beta_rules (Sym := fsym)).

Definition free_rules := iorder_rules (Sym := fsym) (P := sO) (n := n) (p := p).
Definition free_crules := corder_rules (Sym := fsym) (P := sO) (n := n) (p := p).

(** Le système libre : β et la logique intuitionniste d'ordre (n,p). *)
Definition Free : logic fsym :=
  {| l_calc := free_calc; l_prop := sO; l_idx := _; l_rules := free_rules |}.

(** Sa version classique. *)
Definition FreeC : logic fsym :=
  {| l_calc := free_calc; l_prop := sO; l_idx := _; l_rules := free_crules |}.

(** Une théorie sur le système libre : des règles de calcul [CR] en plus de
    β, des règles de déduction [DR] en plus de la logique. *)
Definition Theory {I J} (CR : I -> rule fsym) (DR : J -> drule fsym sO) : logic fsym :=
  {| l_calc := generated (crsum (beta_rules (Sym := fsym)) CR); l_prop := sO;
     l_idx := _; l_rules := rsum free_rules DR |}.

(** Une théorie ne fait qu'ajouter des règles : tout ce que prouve le
    système libre, elle le prouve. *)
Lemma free_in_theory {I J} (CR : I -> rule fsym) (DR : J -> drule fsym sO) Γ Ξ φ :
  provable Free Γ Ξ φ -> provable (Theory CR DR) Γ Ξ φ.
Proof.
  unfold provable; cbn. apply deriv_mono.
  - apply sys_le_generated_incl.
    exact {| cinc := inl; cinc_eq := fun _ => eq_refl |}.
  - exact {| inc := inl; inc_eq := fun _ => eq_refl |}.
Qed.

End FreeSig.

Arguments srt S n p : clear implicits.
Arguments sO {S n p} hO.
Arguments fsym {S n p} hO K _.

(** ** Le cas (ω,ω) : toutes les sortes, toutes quantifiables *)

Section Omega.

Context (S : Type).

Definition osrt : Type := srt S omega omega.

(** Tout type simple est une sorte du système d'ordre (ω,ω). *)
Definition osort (t : fty S) : osrt := exist _ t eq_refl.

Definition oO : osrt := osort tO.

Lemma o_quantifiable (s : osrt) (K : spec osrt -> Type) :
  quantifiable (Sym := fsym (S := S) (n := omega) (p := omega) eq_refl K) omega omega s.
Proof. split; exact I. Qed.

Context (K : spec osrt -> Type).

Definition Free_omega : logic (fsym (S := S) (n := omega) (p := omega) eq_refl K) :=
  Free S omega omega eq_refl K.

Definition FreeC_omega : logic (fsym (S := S) (n := omega) (p := omega) eq_refl K) :=
  FreeC S omega omega eq_refl K.

End Omega.
