(** * Logique propositionnelle

    Une signature *contient* un connecteur quand on dispose d'un symbole de
    la bonne arité : c'est une classe ([HasImp], [HasAnd], ...), ce qui
    permet de combiner les fragments sans fixer l'inductif des symboles.

    Chaque connecteur vient avec sa famille de règles d'introduction et
    d'élimination, écrites comme des schémas dans un contexte de
    métavariables. Les familles se combinent par somme ([rsum]) ; la classe
    [Includes] dit qu'une famille de règles en contient une autre, et les
    règles dérivées de déduction naturelle ([imp_I], [and_E1], ...) valent
    pour toute famille qui contient celles du connecteur. *)

From Stdlib Require Import List.
Import ListNotations.
From SF.Syntax Require Import Spec Terms Vectors.
From SF.Calculus Require Import System.
From SF.Logic Require Import Judgment.

Section Connectives.

Context {Srt : Type} (Sym : spec Srt -> Type) (P : Srt).

Local Notation ι := (Spec [] P).
Local Notation form := (form Sym P).

(** ** Connecteurs *)

Class HasImp := { c_imp : Sym (Spec [ι; ι] P) }.
Class HasAnd := { c_and : Sym (Spec [ι; ι] P) }.
Class HasOr  := { c_or  : Sym (Spec [ι; ι] P) }.
Class HasTop := { c_top : Sym ι }.
Class HasBot := { c_bot : Sym ι }.

Definition Bin (c : Sym (Spec [ι; ι] P)) {Γ} (φ ψ : form Γ) : form Γ :=
  @tsym _ Sym Γ (Spec [ι; ι] P) c
    (@acons _ Sym Γ ι _ φ (@acons _ Sym Γ ι _ ψ anil)).

Definition Cst (c : Sym ι) {Γ} : form Γ := @tsym _ Sym Γ ι c anil.

Definition Imp `{HasImp} {Γ} (φ ψ : form Γ) : form Γ := Bin c_imp φ ψ.
Definition And `{HasAnd} {Γ} (φ ψ : form Γ) : form Γ := Bin c_and φ ψ.
Definition Or  `{HasOr}  {Γ} (φ ψ : form Γ) : form Γ := Bin c_or φ ψ.
Definition Top `{HasTop} {Γ} : form Γ := Cst c_top.
Definition Bot `{HasBot} {Γ} : form Γ := Cst c_bot.
Definition Neg `{HasImp} `{HasBot} {Γ} (φ : form Γ) : form Γ := Imp φ Bot.

(** ** Métavariables propositionnelles *)

Definition mv {Θ} (x : var Θ ι) : form Θ := @tvar _ Sym Θ ι x anil.

Definition Θ1 : ctx Srt := [ι].
Definition Θ2 : ctx Srt := [ι; ι].
Definition Θ3 : ctx Srt := [ι; ι; ι].

Local Notation MA := (mv vz).
Local Notation MB := (mv (vs vz)).
Local Notation MC := (mv (vs (vs vz))).

(** ** Familles de règles *)

Inductive imp_idx := ImpI | ImpE.
Inductive and_idx := AndI | AndE1 | AndE2.
Inductive or_idx  := OrI1 | OrI2 | OrE.
Inductive top_idx := TopI.
Inductive bot_idx := BotE.

Definition imp_rules `{HasImp} (i : imp_idx) : drule Sym P :=
  match i with
  | ImpI => {| d_ctx := Θ2; d_prems := [prem (Θ := Θ2) [MA] MB]; d_concl := Imp MA MB |}
  | ImpE => {| d_ctx := Θ2; d_prems := [prem (Θ := Θ2) [] (Imp MA MB); prem [] MA];
               d_concl := MB |}
  end.

Definition and_rules `{HasAnd} (i : and_idx) : drule Sym P :=
  match i with
  | AndI  => {| d_ctx := Θ2; d_prems := [prem (Θ := Θ2) [] MA; prem [] MB]; d_concl := And MA MB |}
  | AndE1 => {| d_ctx := Θ2; d_prems := [prem (Θ := Θ2) [] (And MA MB)]; d_concl := MA |}
  | AndE2 => {| d_ctx := Θ2; d_prems := [prem (Θ := Θ2) [] (And MA MB)]; d_concl := MB |}
  end.

Definition or_rules `{HasOr} (i : or_idx) : drule Sym P :=
  match i with
  | OrI1 => {| d_ctx := Θ2; d_prems := [prem (Θ := Θ2) [] MA]; d_concl := Or MA MB |}
  | OrI2 => {| d_ctx := Θ2; d_prems := [prem (Θ := Θ2) [] MB]; d_concl := Or MA MB |}
  | OrE  => {| d_ctx := Θ3;
               d_prems := [prem (Θ := Θ3) [] (Or MA MB); prem [MA] MC; prem [MB] MC];
               d_concl := MC |}
  end.

Definition top_rules `{HasTop} (i : top_idx) : drule Sym P :=
  match i with
  | TopI => {| d_ctx := []; d_prems := []; d_concl := Top |}
  end.

Definition bot_rules `{HasBot} (i : bot_idx) : drule Sym P :=
  match i with
  | BotE => {| d_ctx := Θ1; d_prems := [prem (Θ := Θ1) [] Bot]; d_concl := MA |}
  end.

(** Tiers exclu, pour la logique classique. *)
Inductive em_idx := EM.
Definition em_rules `{HasImp} `{HasBot} `{HasOr} (i : em_idx) : drule Sym P :=
  match i with
  | EM => {| d_ctx := Θ1; d_prems := []; d_concl := Or MA (Neg MA) |}
  end.

(** ** Combinaison de familles *)

Definition rsum {I J} (R1 : I -> drule Sym P) (R2 : J -> drule Sym P) : I + J -> drule Sym P :=
  fun k => match k with inl i => R1 i | inr j => R2 j end.

Class Includes {I J} (R : I -> drule Sym P) (R' : J -> drule Sym P) := {
  inc : J -> I;
  inc_eq : forall j, R (inc j) = R' j
}.

#[export] Instance Includes_refl {I} (R : I -> drule Sym P) : Includes R R :=
  {| inc := fun j => j; inc_eq := fun j => eq_refl |}.

#[export] Instance Includes_l {I J K} (R1 : I -> drule Sym P) (R2 : K -> drule Sym P)
  (R' : J -> drule Sym P) `{Includes I J R1 R'} : Includes (rsum R1 R2) R' :=
  {| inc := fun j => inl (inc j); inc_eq := fun j => inc_eq j |}.

#[export] Instance Includes_r {I J K} (R1 : I -> drule Sym P) (R2 : K -> drule Sym P)
  (R' : J -> drule Sym P) `{Includes K J R2 R'} : Includes (rsum R1 R2) R' :=
  {| inc := fun j => inr (inc j); inc_eq := fun j => inc_eq j |}.

(** La logique propositionnelle intuitionniste complète, et sa version classique. *)
Definition ipc_rules `{HasImp} `{HasAnd} `{HasOr} `{HasTop} `{HasBot} :=
  rsum imp_rules (rsum and_rules (rsum or_rules (rsum top_rules bot_rules))).

Definition cpc_rules `{HasImp} `{HasAnd} `{HasOr} `{HasTop} `{HasBot} :=
  rsum ipc_rules em_rules.

End Connectives.

Arguments c_imp {Srt Sym P HasImp}.
Arguments c_and {Srt Sym P HasAnd}.
Arguments c_or {Srt Sym P HasOr}.
Arguments c_top {Srt Sym P HasTop}.
Arguments c_bot {Srt Sym P HasBot}.
Arguments Imp {Srt Sym P _ Γ} φ ψ.
Arguments And {Srt Sym P _ Γ} φ ψ.
Arguments Or {Srt Sym P _ Γ} φ ψ.
Arguments Top {Srt Sym P _ Γ}.
Arguments Bot {Srt Sym P _ Γ}.
Arguments Neg {Srt Sym P _ _ Γ} φ.
Arguments Bin {Srt Sym P} c {Γ} φ ψ.
Arguments Cst {Srt Sym P} c {Γ}.
Arguments mv {Srt Sym P Θ} x.
Arguments imp_rules {Srt Sym P _} i.
Arguments and_rules {Srt Sym P _} i.
Arguments or_rules {Srt Sym P _} i.
Arguments top_rules {Srt Sym P _} i.
Arguments bot_rules {Srt Sym P _} i.
Arguments em_rules {Srt Sym P _ _ _} i.
Arguments rsum {Srt Sym P I J} R1 R2 k.
Arguments ipc_rules {Srt Sym P _ _ _ _ _}.
Arguments cpc_rules {Srt Sym P _ _ _ _ _}.
Arguments Includes {Srt Sym P I J} R R'.

#[export] Typeclasses Transparent ipc_rules cpc_rules.
#[export] Hint Unfold ipc_rules cpc_rules : typeclass_instances.
Arguments inc {Srt Sym P I J R R' _} j.
Arguments inc_eq {Srt Sym P I J R R' _} j.

(** ** Règles dérivées de déduction naturelle

    Elles valent dans toute logique dont la famille de règles contient celle
    du connecteur. *)

(** Substitution dans les formules propositionnelles. *)
Section SubstForm.
Context {Srt : Type} {Sym : spec Srt -> Type} {P : Srt}.

Lemma vsubst_Bin (c : Sym (Spec [Spec [] P; Spec [] P] P)) {Θ Γ} (φ ψ : form Sym P Θ)
  (v : Vectors.vec Sym Θ Γ) : vsubst (Bin c φ ψ) v = Bin c (vsubst φ v) (vsubst ψ v).
Proof.
  unfold Bin.
  transitivity (@tsym _ Sym Γ _ c (@acons _ Sym Γ (Spec [] P) _ (vsubst_tms (σ := Spec [] P) φ v)
                  (@acons _ Sym Γ (Spec [] P) _ (vsubst_tms (σ := Spec [] P) ψ v) anil)));
    [reflexivity|].
  rewrite !vsubst_tms_nil; reflexivity.
Qed.

Lemma vsubst_Cst (c : Sym (Spec [] P)) {Θ Γ} (v : Vectors.vec Sym Θ Γ) :
  vsubst (Cst (Γ := Θ) c) v = Cst c.
Proof. reflexivity. Qed.

Lemma vsubst_mvar {Θ Γ} (x : var Θ (Spec [] P)) (v : Vectors.vec Sym Θ Γ) :
  vsubst (mv (Sym := Sym) x) v = aget x v.
Proof. apply vsubst_mv. Qed.

End SubstForm.

Ltac prop_simpl :=
  unfold inst_hyps, inst_goal, vsubst_list; cbn [p_ext p_hyps p_goal prem map app];
  rewrite ?vup_nil, ?wk_list_nil;
  unfold Neg in *; unfold Imp, And, Or, Top, Bot in *;
  rewrite ?vsubst_Bin, ?vsubst_Cst, ?vsubst_mvar; cbn [aget ahd atl app].

Section Derived.

Context {Srt : Type} {Sym : spec Srt -> Type} (C : system Sym) (P : Srt).
Context {I : Type} (R : I -> drule Sym P).

Local Notation form := (form Sym P).
Local Notation "Ξ ⊢ φ" := (deriv C P R _ Ξ φ) (at level 70).
Local Notation ι := (Spec [] P).

Lemma rule_inc {J} (R' : J -> drule Sym P) `{Includes _ Sym P I J R R'} (j : J)
  {Γ} (Ξ : list (form Γ)) (v : Vectors.vec Sym (d_ctx (R' j)) Γ) (φ : form Γ) :
  vsubst (d_concl (R' j)) v = φ ->
  (forall p, In p (d_prems (R' j)) -> deriv C P R _ (inst_hyps p v Ξ) (inst_goal p v)) ->
  Ξ ⊢ φ.
Proof. intros <- Hp; eapply d_rule_eq; [apply inc_eq|exact Hp]. Qed.

(** Le vecteur de deux formules. *)
Definition v2 {Γ} (φ ψ : form Γ) : Vectors.vec Sym [ι; ι] Γ :=
  @acons _ Sym Γ ι _ φ (@acons _ Sym Γ ι _ ψ anil).
Definition v1 {Γ} (φ : form Γ) : Vectors.vec Sym [ι] Γ := @acons _ Sym Γ ι _ φ anil.
Definition v3 {Γ} (φ ψ χ : form Γ) : Vectors.vec Sym [ι; ι; ι] Γ :=
  @acons _ Sym Γ ι _ φ (@acons _ Sym Γ ι _ ψ (@acons _ Sym Γ ι _ χ anil)).

Section Imp.
Context `{HasImp Srt Sym P} `{Includes _ Sym P I imp_idx R imp_rules}.

Lemma imp_I {Γ} (Ξ : list (form Γ)) φ ψ : (φ :: Ξ) ⊢ ψ -> Ξ ⊢ Imp φ ψ.
Proof.
  intros Hψ. apply (rule_inc imp_rules ImpI Ξ (v2 φ ψ)); unfold v2; cbn [imp_rules d_concl d_prems].
  - prop_simpl; reflexivity.
  - intros p [<-|[]]; prop_simpl; exact Hψ.
Qed.

Lemma imp_E {Γ} (Ξ : list (form Γ)) φ ψ : Ξ ⊢ Imp φ ψ -> Ξ ⊢ φ -> Ξ ⊢ ψ.
Proof.
  intros H1 H2. apply (rule_inc imp_rules ImpE Ξ (v2 φ ψ)); unfold v2; cbn [imp_rules d_concl d_prems].
  - prop_simpl; reflexivity.
  - intros p [<-|[<-|[]]]; prop_simpl; assumption.
Qed.
End Imp.

Section And.
Context `{HasAnd Srt Sym P} `{Includes _ Sym P I and_idx R and_rules}.

Lemma and_I {Γ} (Ξ : list (form Γ)) φ ψ : Ξ ⊢ φ -> Ξ ⊢ ψ -> Ξ ⊢ And φ ψ.
Proof.
  intros H1 H2. apply (rule_inc and_rules AndI Ξ (v2 φ ψ)); unfold v2; cbn [and_rules d_concl d_prems].
  - prop_simpl; reflexivity.
  - intros p [<-|[<-|[]]]; prop_simpl; assumption.
Qed.

Lemma and_E1 {Γ} (Ξ : list (form Γ)) φ ψ : Ξ ⊢ And φ ψ -> Ξ ⊢ φ.
Proof.
  intros H1. apply (rule_inc and_rules AndE1 Ξ (v2 φ ψ)); unfold v2; cbn [and_rules d_concl d_prems].
  - prop_simpl; reflexivity.
  - intros p [<-|[]]; prop_simpl; assumption.
Qed.

Lemma and_E2 {Γ} (Ξ : list (form Γ)) φ ψ : Ξ ⊢ And φ ψ -> Ξ ⊢ ψ.
Proof.
  intros H1. apply (rule_inc and_rules AndE2 Ξ (v2 φ ψ)); unfold v2; cbn [and_rules d_concl d_prems].
  - prop_simpl; reflexivity.
  - intros p [<-|[]]; prop_simpl; assumption.
Qed.
End And.

Section Or.
Context `{HasOr Srt Sym P} `{Includes _ Sym P I or_idx R or_rules}.

Lemma or_I1 {Γ} (Ξ : list (form Γ)) φ ψ : Ξ ⊢ φ -> Ξ ⊢ Or φ ψ.
Proof.
  intros H1. apply (rule_inc or_rules OrI1 Ξ (v2 φ ψ)); unfold v2; cbn [or_rules d_concl d_prems].
  - prop_simpl; reflexivity.
  - intros p [<-|[]]; prop_simpl; assumption.
Qed.

Lemma or_I2 {Γ} (Ξ : list (form Γ)) φ ψ : Ξ ⊢ ψ -> Ξ ⊢ Or φ ψ.
Proof.
  intros H1. apply (rule_inc or_rules OrI2 Ξ (v2 φ ψ)); unfold v2; cbn [or_rules d_concl d_prems].
  - prop_simpl; reflexivity.
  - intros p [<-|[]]; prop_simpl; assumption.
Qed.

Lemma or_E {Γ} (Ξ : list (form Γ)) φ ψ χ :
  Ξ ⊢ Or φ ψ -> (φ :: Ξ) ⊢ χ -> (ψ :: Ξ) ⊢ χ -> Ξ ⊢ χ.
Proof.
  intros H1 H2 H3. apply (rule_inc or_rules OrE Ξ (v3 φ ψ χ)); unfold v3; cbn [or_rules d_concl d_prems].
  - prop_simpl; reflexivity.
  - intros p [<-|[<-|[<-|[]]]]; prop_simpl; assumption.
Qed.
End Or.

Section Top.
Context `{HasTop Srt Sym P} `{Includes _ Sym P I top_idx R top_rules}.

Lemma top_I {Γ} (Ξ : list (form Γ)) : Ξ ⊢ Top.
Proof.
  apply (rule_inc top_rules TopI Ξ anil); cbn [top_rules d_concl d_prems].
  - prop_simpl; reflexivity.
  - intros p [].
Qed.
End Top.

Section Bot.
Context `{HasBot Srt Sym P} `{Includes _ Sym P I bot_idx R bot_rules}.

Lemma bot_E {Γ} (Ξ : list (form Γ)) φ : Ξ ⊢ Bot -> Ξ ⊢ φ.
Proof.
  intros H1. apply (rule_inc bot_rules BotE Ξ (v1 φ)); unfold v1; cbn [bot_rules d_concl d_prems].
  - prop_simpl; reflexivity.
  - intros p [<-|[]]; prop_simpl; assumption.
Qed.
End Bot.

Section EM.
Context `{HasImp Srt Sym P} `{HasBot Srt Sym P} `{HasOr Srt Sym P}.
Context `{Includes _ Sym P I em_idx R em_rules}.

Lemma excluded_middle {Γ} (Ξ : list (form Γ)) φ : Ξ ⊢ Or φ (Neg φ).
Proof.
  apply (rule_inc em_rules EM Ξ (v1 φ)); unfold v1; cbn [em_rules d_concl d_prems].
  - prop_simpl; reflexivity.
  - intros p [].
Qed.
End EM.

(** L'hypothèse est dérivable. *)
Lemma hyp {Γ} (Ξ : list (form Γ)) φ : In φ Ξ -> Ξ ⊢ φ.
Proof. apply d_ax. Qed.

End Derived.
