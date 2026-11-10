(** * HA^{ω,ω}_ω et le système arithmétique libre (ω,ω,ω)

    La signature des types finis : sortes N, O (les propositions) et
    a → b ; symboles λ, app, 0, S, rec_s (pour toute sorte de hauteur
    propositionnelle nulle), les connecteurs, ∀_s, ∃_s, =_s pour toute
    sorte.

    Deux logiques sur cette signature, toutes deux d'ordre (ω,ω) avec des
    récurseurs de toute hauteur (r = ω) :
    - **HA^{ω,ω}_ω** ([HA]) : calcul β + rec, règles de la logique
      intuitionniste d'ordre (ω,ω), récurrence et S t ≠ 0 ;
    - le **système libre** ([Free]) : calcul β + rec + (S t = 0 ~ ⊥), et
      seulement les règles de la logique intuitionniste d'ordre (ω,ω), sans
      aucun axiome arithmétique.

    La **relativisation** ([D]) est définie par récurrence sur les types.
    La clause D_N(x) code la récurrence de façon imprédicative :
    D_N(x) := ∀X : N → O. X(0) ⇒ (∀n. X(n) ⇒ X(S n)) ⇒ X(x). Ensuite,
    D_O := ⊤ et D_{a → b}(f) := ∀x : a. D_a(x) ⇒ D_b(f x).
    L'interprétation [Rel] de HA dans le système libre est l'identité sur
    les sortes et sur les symboles, sauf les quantificateurs, qui sont
    relativisés : ∀x. φ ↦ ∀x. D(x) ⇒ φ, et ∃x. φ ↦ ∃x. D(x) ∧ φ.

    **Types inductifs.** Tout est paramétré par une famille de types
    inductifs à arités finies (fichier [Arithmetic/Inductive.v]) : un type
    d'indices [Ind] et une description [dsc i] de chaque Wᵢ. Les sortes
    sont alors N, O, a → b et les Wᵢ ; les symboles comprennent les
    constructeurs et les récurseurs rec_{i,s}. HA_ω^{ω,ω} au sens strict est
    le cas Ind = ∅. Trois logiques :
    - [HA] : les équations de rec_{i,s} sont des *conversions*, et l'on a la
      récurrence sur chaque Wᵢ ;
    - [HAE] : la version « équationnelle » : les mêmes équations sont des
      *règles de déduction* (égalités de Leibniz) ;
    - [Free] : les conversions de HA et S t = 0 ~ ⊥, sans règle
      arithmétique ni récurrence.
    La relativisation de Wᵢ est imprédicative, comme celle de N :
    D_W(x) := ∀X : W → O. Cl₁(X) ⇒ … ⇒ Clₙ(X) ⇒ X(x), où Cl_c(X) dit que X
    est clos par le constructeur c : ∀x⃗. D_N(p) ⇒ … ⇒ X(y) ⇒ … ⇒ X(c(x⃗))
    (une hypothèse D_N(p) par paramètre p, X(y) par argument récursif y). *)

From Stdlib Require Import List Lia.
Import ListNotations.
From SF.Syntax Require Import Spec Terms Vectors.
From SF.Calculus Require Import System Rules.
From SF.Logic Require Import Judgment Propositional.
From SF.Functional Require Import Arrow Graded.
From SF.Quantifiers Require Import Quant Order.
From SF.Arithmetic Require Import Arith Inductive.
From SF.Extensions Require Import Conservativity Same.

Local Notation ι a := (Spec [] a).

(** ** Types finis *)

Inductive ty {Ind : Type} := tN | tO | tarr (a b : ty) | tW (i : Ind).
Arguments ty : clear implicits.

Fixpoint tgr {Ind} (t : ty Ind) : grade :=
  match t with
  | tN => (0, 0)
  | tO => (0, 1)
  | tarr a b => garr (tgr a) (tgr b)
  | tW _ => (0, 0)
  end.

Inductive tarrw {Ind} : ty Ind -> ty Ind -> ty Ind -> Type := tarrw_i a b : tarrw a b (tarr a b).

Inductive hsym {Ind : Type} (dsc : Ind -> list (list bool)) : spec (ty Ind) -> Type :=
| h_lam (a b : ty Ind) : hsym dsc (Spec [Spec [ι a] b] (tarr a b))
| h_app (a b : ty Ind) : hsym dsc (Spec [ι (tarr a b); ι a] b)
| h_zero : hsym dsc (ι tN)
| h_succ : hsym dsc (Spec [ι tN] tN)
| h_rec (s : ty Ind) : snd (tgr s) = 0 -> hsym dsc (Spec [ι s; Spec [ι tN; ι s] s; ι tN] s)
| h_imp : hsym dsc (Spec [ι tO; ι tO] tO)
| h_and : hsym dsc (Spec [ι tO; ι tO] tO)
| h_or : hsym dsc (Spec [ι tO; ι tO] tO)
| h_top : hsym dsc (ι tO)
| h_bot : hsym dsc (ι tO)
| h_all (s : ty Ind) : hsym dsc (Spec [Spec [ι s] tO] tO)
| h_ex (s : ty Ind) : hsym dsc (Spec [Spec [ι s] tO] tO)
| h_eq (s : ty Ind) : hsym dsc (Spec [ι s; ι s] tO)
| h_con (i : Ind) (bs : list bool) : mem (dsc i) bs -> hsym dsc (con_spec tN tW i bs)
| h_wrec (i : Ind) (s : ty Ind) : snd (tgr s) = 0 -> hsym dsc (wrec_spec tN tW dsc i s).

Arguments h_lam {Ind dsc} a b.
Arguments h_app {Ind dsc} a b.
Arguments h_zero {Ind dsc}.
Arguments h_succ {Ind dsc}.
Arguments h_rec {Ind dsc} s _.
Arguments h_imp {Ind dsc}.
Arguments h_and {Ind dsc}.
Arguments h_or {Ind dsc}.
Arguments h_top {Ind dsc}.
Arguments h_bot {Ind dsc}.
Arguments h_all {Ind dsc} s.
Arguments h_ex {Ind dsc} s.
Arguments h_eq {Ind dsc} s.
Arguments h_con {Ind dsc} i bs _.
Arguments h_wrec {Ind dsc} i s _.

#[export] Instance h_functional {Ind dsc} : Functional (@hsym Ind dsc) := {|
  Arr := tarrw;
  s_lam := fun a b c w => match w in tarrw a0 b0 c0 return hsym dsc (Spec [Spec [ι a0] b0] c0) with
                          | tarrw_i a0 b0 => h_lam a0 b0 end;
  s_app := fun a b c w => match w in tarrw a0 b0 c0 return hsym dsc (Spec [ι c0; ι a0] b0) with
                          | tarrw_i a0 b0 => h_app a0 b0 end
|}.

#[export] Instance h_graded {Ind dsc} : Graded (@hsym Ind dsc) := {|
  gr := tgr;
  gr_arr := fun a b c w => match w in tarrw a0 b0 c0 return tgr c0 = garr (tgr a0) (tgr b0) with
                           | tarrw_i a0 b0 => eq_refl end
|}.

#[export] Instance h_hasimp {Ind dsc} : HasImp (@hsym Ind dsc) tO := {| c_imp := h_imp |}.
#[export] Instance h_hasand {Ind dsc} : HasAnd (@hsym Ind dsc) tO := {| c_and := h_and |}.
#[export] Instance h_hasor {Ind dsc} : HasOr (@hsym Ind dsc) tO := {| c_or := h_or |}.
#[export] Instance h_hastop {Ind dsc} : HasTop (@hsym Ind dsc) tO := {| c_top := h_top |}.
#[export] Instance h_hasbot {Ind dsc} : HasBot (@hsym Ind dsc) tO := {| c_bot := h_bot |}.
#[export] Instance h_hasall {Ind dsc} s : HasForall (@hsym Ind dsc) tO s := {| c_all := h_all s |}.
#[export] Instance h_hasex {Ind dsc} s : HasExists (@hsym Ind dsc) tO s := {| c_ex := h_ex s |}.
#[export] Instance h_haseq {Ind dsc} s : HasEq (@hsym Ind dsc) tO s := {| c_eq := h_eq s |}.

(** Toutes les sortes sont quantifiables à l'ordre (ω,ω). *)
#[export] Instance h_quant {Ind dsc} : Quantifiers (@hsym Ind dsc) tO omega omega := {|
  q_all := fun s _ => h_all s;
  q_ex := fun s _ => h_ex s;
  q_eq := fun s _ => h_eq s
|}.

(** Des récurseurs à toute sorte de hauteur propositionnelle nulle. *)
#[export] Instance h_arith {Ind dsc} : Arithmetic (@hsym Ind dsc) tN omega := {|
  a_zero := h_zero;
  a_succ := h_succ;
  a_rec := fun s h => h_rec s (match h with conj _ p => p end)
|}.

#[export] Instance h_ind {Ind dsc} : Inductives (@hsym Ind dsc) tN omega tW dsc := {|
  a_con := fun i bs c => h_con i bs c;
  a_wrec := fun i s h => h_wrec i s (match h with conj _ p => p end)
|}.

Section Sig.
Context {Ind : Type} {dsc : Ind -> list (list bool)}.

Local Notation ty := (ty Ind).
Local Notation hsym := (hsym dsc).
Local Notation tm := (Terms.tm hsym).
Local Notation form := (form hsym tO).

Definition w_ab (a b : ty) : tarrw a b (tarr a b) := tarrw_i a b.

(** ** Les logiques *)

(** S t = 0 ~ ⊥. *)
Definition neq_rule : rule hsym := {|
  r_ctx := [ι tN];
  r_sort := tO;
  r_lhs := Eq tN (Succ (var0 vz)) Zero;
  r_rhs := Bot
|}.

Definition neq_rules (u : unit) : rule hsym := neq_rule.

Definition hae_calc_rules := crsum (rec_rules (N := tN) (r := omega)) (beta_rules (Sym := hsym)).
Definition ha_calc_rules := crsum hae_calc_rules (wrec_rules (N := tN) (r := omega) (W := tW) (dsc := dsc)).
Definition free_calc_rules := crsum ha_calc_rules neq_rules.

Definition ha_rules :=
  rsum (iorder_rules (Sym := hsym) (P := tO) (n := omega) (p := omega))
       (rsum (ind_rules (N := tN) (r := omega) tO)
          (rsum (peano_rules (N := tN) (r := omega) tO) (wind_rules (IN := h_ind) tO))).

Definition hae_rules := rsum ha_rules (weq_rules (IN := h_ind) tO).

Definition free_rules := iorder_rules (Sym := hsym) (P := tO) (n := omega) (p := omega).

Definition HA : logic hsym :=
  {| l_calc := generated ha_calc_rules; l_prop := tO; l_idx := _; l_rules := ha_rules |}.

Definition HAE : logic hsym :=
  {| l_calc := generated hae_calc_rules; l_prop := tO; l_idx := _; l_rules := hae_rules |}.

Definition Free : logic hsym :=
  {| l_calc := generated free_calc_rules; l_prop := tO; l_idx := _; l_rules := free_rules |}.

(** ** La relativisation *)

(** D_s(t). *)
Definition Dat {Γ} s (Ds : form [ι s]) (t : tm Γ s) : form Γ :=
  vsubst Ds (@acons _ hsym Γ (ι s) [] t anil).

(** N(x) := ∀X. X(0) ⇒ (∀n. X(n) ⇒ X(S n)) ⇒ X(x), dans le contexte [x : N]. *)
Definition NatF : form [ι tN] :=
  All (tarr tN tO)
    (Imp (App (w_ab tN tO) (var0 vz) Zero)
       (Imp (All tN (Imp (App (w_ab tN tO) (var0 (vs vz)) (var0 vz))
                         (App (w_ab tN tO) (var0 (vs vz)) (Succ (var0 vz)))))
            (App (w_ab tN tO) (var0 vz) (var0 (vs vz))))).

(** *** Relativisation des types inductifs *)

Local Notation XW i := (tarr (tW i) tO).
Local Notation wW i := (w_ab (tW i) tO).

(** ∀x⃗. φ, pour les arguments x⃗ d'un constructeur. *)
Fixpoint AllA i (bs : list bool) {Γ} : form (cargs tN tW i bs ++ Γ) -> form Γ :=
  match bs as bs0 return form (cargs tN tW i bs0 ++ Γ) -> form Γ with
  | [] => fun φ => φ
  | b :: bs' => fun φ => AllA i bs' (All (asrt tN tW i b) φ)
  end.

Definition Imps {Γ} (hs : list (form Γ)) (φ : form Γ) : form Γ := fold_right Imp φ hs.

(** Les hypothèses de la clôture : D_N(p) pour un paramètre, X(y) pour un
    argument récursif. *)
Fixpoint chyps i {Γ} (X : tm Γ (XW i)) (bs : list bool) : args hsym Γ (cargs tN tW i bs) -> list (form Γ) :=
  match bs as bs0 return args hsym Γ (cargs tN tW i bs0) -> list (form Γ) with
  | [] => fun _ => []
  | b :: bs' =>
      match b as b0 return args hsym Γ (cargs tN tW i (b0 :: bs')) -> list (form Γ) with
      | true => fun a => Dat tN NatF (ahd a) :: chyps i X bs' (atl a)
      | false => fun a => App (wW i) X (ahd a) :: chyps i X bs' (atl a)
      end
  end.

(** Cl_c(X) : X est clos par le constructeur c. *)
Definition Clos i bs (c : mem (dsc i) bs) {Γ} (X : tm Γ (XW i)) : form Γ :=
  AllA i bs (Imps (chyps i (ren_tm X (wk (cargs tN tW i bs))) bs (lvars _ Γ))
                  (App (wW i) (ren_tm X (wk (cargs tN tW i bs))) (Con i bs c (lvars _ Γ)))).

Definition Closs i {Γ} (X : tm Γ (XW i)) : list (form Γ) :=
  map (fun p => Clos i (projT1 p) (projT2 p) X) (mems (dsc i)).

(** D_W(t) := ∀X. Cl₁(X) ⇒ … ⇒ Clₙ(X) ⇒ X(t). *)
Definition DW i {Γ} (t : tm Γ (tW i)) : form Γ :=
  All (XW i) (Imps (Closs i (var0 vz)) (App (wW i) (var0 vz) (ren_tm t (wk [ι (XW i)])))).

Fixpoint D (s : ty) : form [ι s] :=
  match s with
  | tN => NatF
  | tO => Top
  | tarr a b =>
      All a (Imp (Dat a (D a) (var0 vz))
                 (Dat b (D b) (App (w_ab a b) (var0 (vs vz)) (var0 vz))))
  | tW i => DW i (var0 vz)
  end.

(** La relativisation d'une spécification : D pour une sorte, ⊤ sinon
    (on ne traduit que des jugements dont les variables sont de sorte). *)
Definition Dspec (σ : spec ty) : form [σ] :=
  match σ as σ0 return form [σ0] with
  | Spec [] s => D s
  | Spec (_ :: _) _ => Top
  end.

(** Les quantificateurs relativisés, dans le contexte [φ : s → O]. *)
Definition relAll s : tm [Spec [ι s] tO] tO :=
  All s (Imp (Dat s (D s) (var0 vz)) (app1 (vs vz) (var0 vz))).

Definition relEx s : tm [Spec [ι s] tO] tO :=
  Ex s (And (Dat s (D s) (var0 vz)) (app1 (vs vz) (var0 vz))).

(** Les symboles gardés : tous, sauf les quantificateurs. *)
Definition keep (σ : spec ty) (c : hsym σ) : bool :=
  match c with h_all _ | h_ex _ => false | _ => true end.

Definition rel_sym (σ : spec ty) (c : hsym σ) : tm (dom σ) (cod σ) :=
  match c in Signature.hsym _ σ0 return hsym σ0 -> tm (dom σ0) (cod σ0) with
  | h_all s => fun _ => relAll s
  | h_ex s => fun _ => relEx s
  | _ => fun c0 => tsym c0 (vid _)
  end c.

Lemma rel_keep σ (c : hsym σ) : keep σ c = true -> rel_sym σ c = tsym c (vid (dom σ)).
Proof. destruct c; cbn; intros H; try discriminate H; reflexivity. Qed.

Definition rel_interp : sinterp hsym hsym := {| s_sym := rel_sym |}.

Definition Rel : slinterp HA Free := @Build_slinterp _ _ _ HA Free rel_interp eq_refl Dspec.

End Sig.

(** Les contextes de sortes : toutes les variables sont de spécification ι s. *)
Definition sctx {Ind} (Γ : ctx (ty Ind)) : Prop := Forall (fun σ => dom σ = []) Γ.
