(** * Extensions par des règles, sur une même signature

    La signature et la sorte des propositions sont fixées. On étend le
    système de calcul (C ⊆ C') ou la famille de règles de déduction
    (R ⊆ R'). L'identité sur les jugements est alors une extension saine
    ([deriv_mono]). Elle est conservative dès que les nouvelles règles sont
    **admissibles** dans l'ancien système et que les nouvelles conversions y
    sont déjà valides ([admissible_conservative]). *)

From Stdlib Require Import List.
Import ListNotations.
From SF.Syntax Require Import Spec Terms Vectors.
From SF.Calculus Require Import System Rules.
From SF.Logic Require Import Judgment Propositional.
From SF.Extensions Require Import Conservativity.

Section RuleExt.
Context {Srt : Type} {Sym : spec Srt -> Type} (P : Srt).

(** Inclusion de systèmes de calcul. *)
Definition sys_le (C C' : system Sym) :=
  forall Γ s (t u : Terms.tm Sym Γ s), conv C t u -> conv C' t u.

Lemma sys_le_refl C : sys_le C C.
Proof. intros ? ? ? ? H; exact H. Qed.

(** Un système engendré est inclus dans tout système qui valide ses règles. *)
Lemma sys_le_generated {I} (R : I -> rule Sym) (C' : system Sym) :
  (forall i, conv C' (r_lhs (R i)) (r_rhs (R i))) -> sys_le (generated R) C'.
Proof. intros H Γ s t u; apply generated_least, H. Qed.

(** Ajouter des règles de calcul agrandit le système engendré. *)
Lemma sys_le_generated_incl {I J} (R : I -> rule Sym) (R' : J -> rule Sym) {HI : CIncludes R' R} :
  sys_le (generated R) (generated R').
Proof.
  apply sys_le_generated; intros i.
  pose proof (generated_included R' R i (vid _)) as Hr. rewrite !vsubst_vid in Hr. exact Hr.
Qed.

(** *** Monotonie de la dérivabilité *)
Theorem deriv_mono (C C' : system Sym) {I J} (R : I -> drule Sym P) (R' : J -> drule Sym P) :
  sys_le C C' -> Includes R' R ->
  forall Γ Ξ φ, deriv C P R Γ Ξ φ -> deriv C' P R' Γ Ξ φ.
Proof.
  intros HC HR. induction 1 as [Γ Ξ φ Hin|Γ Ξ φ ψ Hc H IH|Γ Ξ i v Hp IH].
  - apply d_ax, Hin.
  - eapply d_conv; [apply HC, Hc|exact IH].
  - eapply d_rule_eq; [apply (inc_eq i)|exact IH].
Qed.

Definition mklogic (C : system Sym) {I} (R : I -> drule Sym P) : logic Sym :=
  {| l_calc := C; l_prop := P; l_idx := I; l_rules := R |}.

(** L'extension identité de (C, R) vers (C', R'). *)
Lemma rule_ext_sound (C C' : system Sym) {I J} (R : I -> drule Sym P) (R' : J -> drule Sym P) :
  sys_le C C' -> Includes R' R ->
  sound (L1 := mklogic C R) (L2 := mklogic C' R') (fun j => j).
Proof. intros HC HR j Hj; exact (deriv_mono C C' R R' HC HR _ _ _ Hj). Qed.

Definition rule_extension (C C' : system Sym) {I J} (R : I -> drule Sym P) (R' : J -> drule Sym P)
  (HC : sys_le C C') (HR : Includes R' R) : extension (mklogic C R) (mklogic C' R') :=
  @Build_extension _ _ _ _ (mklogic C R) (mklogic C' R') (fun j => j) (rule_ext_sound C C' R R' HC HR).

(** *** Règles admissibles

    Une règle est admissible dans (C, R) si chacune de ses instances l'est :
    dès que les prémisses instanciées sont dérivables, la conclusion
    instanciée l'est aussi. *)
Definition admissible (C : system Sym) {I} (R : I -> drule Sym P) (r : drule Sym P) :=
  forall Γ Ξ (v : vec Sym (d_ctx r) Γ),
    (forall p, In p (d_prems r) -> deriv C P R _ (inst_hyps p v Ξ) (inst_goal p v)) ->
    deriv C P R Γ Ξ (vsubst (d_concl r) v).

(** Les règles de R sont admissibles dans (C, R). *)
Lemma admissible_rule (C : system Sym) {I} (R : I -> drule Sym P) i : admissible C R (R i).
Proof. intros Γ Ξ v Hp; apply d_rule, Hp. Qed.

(** Si (C', R') ne dérive que des conversions et des règles admissibles dans
    (C, R), toute dérivation de (C', R') se recolle dans (C, R). *)
Theorem deriv_admissible (C C' : system Sym) {I J} (R : I -> drule Sym P) (R' : J -> drule Sym P) :
  sys_le C' C -> (forall j, admissible C R (R' j)) ->
  forall Γ Ξ φ, deriv C' P R' Γ Ξ φ -> deriv C P R Γ Ξ φ.
Proof.
  intros HC HR. induction 1 as [Γ Ξ φ Hin|Γ Ξ φ ψ Hc H IH|Γ Ξ i v Hp IH].
  - apply d_ax, Hin.
  - eapply d_conv; [apply HC, Hc|exact IH].
  - apply HR, IH.
Qed.

Theorem admissible_conservative (C C' : system Sym) {I J} (R : I -> drule Sym P) (R' : J -> drule Sym P)
  (HC : sys_le C C') (HR : Includes R' R) :
  sys_le C' C -> (forall j, admissible C R (R' j)) ->
  conservative (rule_extension C C' R R' HC HR).
Proof. intros HC' HA j _ Hv; exact (deriv_admissible C C' R R' HC' HA _ _ _ Hv). Qed.

End RuleExt.

Arguments mklogic {Srt Sym} P C {I} R.
Arguments rule_extension {Srt Sym} P C C' {I J} R R' HC HR.
Arguments admissible {Srt Sym} P C {I} R r.
