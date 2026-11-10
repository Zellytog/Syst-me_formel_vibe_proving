(** * Exemple : une arithmétique d'ordre (1,1) à récursion de hauteur 1

    Sortes N (grade (0,0)) et Pr (grade (0,1)). On quantifie sur N
    seulement ; le seul récurseur est rec_N (r = 1) : ce sont les fonctions
    récursives primitives. Le système de calcul est engendré par les règles
    de rec ; la logique est intuitionniste, avec ∀, ∃, = sur N, la
    récurrence et S t ≠ 0. *)

From Stdlib Require Import List Arith Lia.
Import ListNotations.
From SF.Syntax Require Import Spec Terms Vectors.
From SF.Calculus Require Import System Rules.
From SF.Logic Require Import Judgment Propositional.
From SF.Functional Require Import Arrow Graded.
From SF.Quantifiers Require Import Quant Order.
From SF.Arithmetic Require Import Arith.

Inductive asort := N | Pr.

Local Notation ι a := (Spec [] a).

Inductive asym : spec asort -> Type :=
| a_imp : asym (Spec [ι Pr; ι Pr] Pr)
| a_and : asym (Spec [ι Pr; ι Pr] Pr)
| a_or  : asym (Spec [ι Pr; ι Pr] Pr)
| a_top : asym (ι Pr)
| a_bot : asym (ι Pr)
| s_0 : asym (ι N)
| s_S : asym (Spec [ι N] N)
| s_recN : asym (Spec [ι N; Spec [ι N; ι N] N; ι N] N)
| s_all : asym (Spec [Spec [ι N] Pr] Pr)
| s_ex  : asym (Spec [Spec [ι N] Pr] Pr)
| s_eq  : asym (Spec [ι N; ι N] Pr).

#[export] Instance a_hasimp : HasImp asym Pr := {| c_imp := a_imp |}.
#[export] Instance a_hasand : HasAnd asym Pr := {| c_and := a_and |}.
#[export] Instance a_hasor  : HasOr asym Pr  := {| c_or := a_or |}.
#[export] Instance a_hastop : HasTop asym Pr := {| c_top := a_top |}.
#[export] Instance a_hasbot : HasBot asym Pr := {| c_bot := a_bot |}.

#[export] Instance a_functional : Functional asym := {|
  Arr := fun _ _ _ => Empty_set;
  s_lam := fun a b c w => match w with end;
  s_app := fun a b c w => match w with end
|}.

Definition a_grade (s : asort) : grade := match s with N => (0, 0) | Pr => (0, 1) end.

Lemma a_gr_arr a b c (w : @Arr _ asym a_functional a b c) : a_grade c = garr (a_grade a) (a_grade b).
Proof. destruct w. Qed.

#[export] Instance a_graded : Graded asym := {| gr := a_grade; gr_arr := a_gr_arr |}.

Lemma hN : quantifiable (Sym := asym) 1 1 N.
Proof. split; cbn; lia. Qed.
Lemma Pr_not_q : ~ quantifiable (Sym := asym) 1 1 Pr.
Proof. intros [_ H]; cbn in H; lia. Qed.
Lemma hRN : rec_ok (Sym := asym) 1 N.
Proof. split; cbn; lia. Qed.
Lemma Pr_not_rec : ~ rec_ok (Sym := asym) 1 Pr.
Proof. intros [_ H]; cbn in H; discriminate. Qed.

#[export] Instance a_arith : Arithmetic asym N 1 := {|
  a_zero := s_0;
  a_succ := s_S;
  a_rec := fun s => match s with N => fun _ => s_recN | Pr => fun h => False_rect _ (Pr_not_rec h) end
|}.

Definition qa (s : asort) : quantifiable (Sym := asym) 1 1 s -> asym (Spec [Spec [ι s] Pr] Pr) :=
  match s with N => fun _ => s_all | Pr => fun h => False_rect _ (Pr_not_q h) end.
Definition qe (s : asort) : quantifiable (Sym := asym) 1 1 s -> asym (Spec [Spec [ι s] Pr] Pr) :=
  match s with N => fun _ => s_ex | Pr => fun h => False_rect _ (Pr_not_q h) end.
Definition qq (s : asort) : quantifiable (Sym := asym) 1 1 s -> asym (Spec [ι s; ι s] Pr) :=
  match s with N => fun _ => s_eq | Pr => fun h => False_rect _ (Pr_not_q h) end.

#[export] Instance a_quant : Quantifiers asym Pr 1 1 := {| q_all := qa; q_ex := qe; q_eq := qq |}.

(** Le calcul et la logique. *)
Definition C : system asym := arith_system asym N 1.

Definition RR := rsum (iorder_rules (Sym := asym) (P := Pr) (n := 1) (p := 1))
                      (rsum (ind_rules (Sym := asym) (N := N) (r := 1) Pr)
                            (peano_rules (N := N) (r := 1) Pr (HQ := qeq_inst (existT _ N hN)))).

#[export] Typeclasses Transparent RR.
#[export] Hint Unfold RR : typeclass_instances.

Notation PA Γ Ξ φ := (deriv C Pr RR Γ Ξ φ).

Notation x0 := (var0 vz).
Notation x1 := (var0 (vs vz)).
Notation EqN := (QEq (n := 1) (p := 1) N hN).

(** Prédécesseur et addition, par récursion primitive. *)
Definition pred {Γ} (t : Terms.tm asym Γ N) := Rec (r := 1) N hRN Zero x0 t.
Definition plus {Γ} (m t : Terms.tm asym Γ N) := Rec (r := 1) N hRN m (Succ x1) t.

Tactic Notation "qap" uconstr(t) := eapply t; try typeclasses eauto.
Ltac hyp := apply d_ax; simpl; auto.

(** ** Calculs *)

Example pred_succ : conv C (Γ := [ι N]) (pred (Succ x0)) x0.
Proof. exact (rec_succ_conv _ N hRN Zero x0 x0). Qed.

Example plus_zero : conv C (Γ := [ι N]) (plus x0 Zero) x0.
Proof. exact (rec_zero_conv _ N hRN x0 (Succ x1)). Qed.

Example plus_succ : conv C (Γ := [ι N; ι N]) (plus x0 (Succ x1)) (Succ (plus x0 x1)).
Proof. exact (rec_succ_conv _ N hRN x0 (Succ x1) x1). Qed.

(** Congruence de l'égalité vis-à-vis de la conversion. *)
Lemma conv_EqN {Γ} (a a' b b' : Terms.tm asym Γ N) :
  conv C a a' -> conv C b b' -> conv C (EqN a b) (EqN a' b').
Proof.
  intros Ha Hb. unfold QEq, Eq. eapply (conv_tsym C (σ := Spec [ι N; ι N] Pr)). cbn. repeat split; assumption.
Qed.

(** ** Dérivations *)

(** L'injectivité de S, par transport et calcul du prédécesseur. *)
Example succ_inj : PA [ι N; ι N] [EqN (Succ x0) (Succ x1)] (EqN x0 x1).
Proof.
  eapply d_conv.
  - apply conv_EqN; [exact (rec_succ_conv _ N hRN Zero x0 x0)|exact (rec_succ_conv _ N hRN Zero x0 x1)].
  - qap (qeq_subst C RR N hN _ (EqN (pred (Succ x1)) (pred x0)) (Succ x0) (Succ x1)).
    + hyp.
    + qap (qeq_refl C RR N hN).
Qed.

(** 1 ≠ 0. *)
Example one_neq_zero : PA [] [] (Neg (EqN (Succ Zero) Zero)).
Proof.
  qap (imp_I C Pr RR). qap (succ_neq_zero C RR (HQ := qeq_inst (existT _ N hN)) _ Zero).
  apply d_ax; left; reflexivity. Unshelve. all: typeclasses eauto.
Qed.
(** 0 + t = t, par récurrence sur t. *)
Example zero_plus : PA [ι N] [] (EqN (plus Zero x0) x0).
Proof.
  refine (induction C RR [] (EqN (plus Zero x0) x0) x0 _ _).
  - (* base : 0 + 0 = 0, par calcul *)
    change (PA [ι N] [] (EqN (plus Zero Zero) Zero)).
    eapply d_conv.
    + apply conv_EqN; [apply conv_sym; exact (rec_zero_conv _ N hRN Zero (Succ x1))|apply conv_refl].
    + qap (qeq_refl C RR N hN).
  - (* hérédité : 0 + S x ~ S (0 + x), puis transport par l'hypothèse *)
    change (PA [ι N; ι N] [EqN (plus Zero x0) x0] (EqN (plus Zero (Succ x0)) (Succ x0))).
    eapply d_conv.
    + apply conv_EqN; [apply conv_sym; exact (rec_succ_conv _ N hRN Zero (Succ x1) x0)|apply conv_refl].
    + qap (qeq_subst C RR N hN _ (EqN (Succ (plus Zero x1)) (Succ x0)) (plus Zero x0) x0).
      * hyp.
      * qap (qeq_refl C RR N hN).
Qed.
