(** * Exemple : une théorie des ensembles d'ordre (1,1) en déduction modulo

    Sortes V (ensembles, grade (0,0)) et Pr (grade (0,1)) ; on quantifie
    sur V seulement. La compréhension et le remplacement prennent une
    formule ou une fonction en argument : ce sont des lieurs de la
    signature, pas des quantifications. Les axiomes d'appartenance sont des
    règles du calcul ; la logique ajoute l'extensionnalité et la
    description à la logique intuitionniste d'ordre (1,1). *)

From Stdlib Require Import List Arith Lia.
Import ListNotations.
From SF.Syntax Require Import Spec Terms Vectors.
From SF.Calculus Require Import System Rules.
From SF.Logic Require Import Judgment Propositional.
From SF.Functional Require Import Arrow Graded.
From SF.Quantifiers Require Import Quant Order.
From SF.SetTheory Require Import Sets.

Inductive zsort := V | Pr.

Local Notation ι a := (Spec [] a).
Local Notation σP := (Spec [ι V] Pr).
Local Notation σF := (Spec [ι V] V).

Inductive zsym : spec zsort -> Type :=
| z_imp : zsym (Spec [ι Pr; ι Pr] Pr)
| z_and : zsym (Spec [ι Pr; ι Pr] Pr)
| z_or  : zsym (Spec [ι Pr; ι Pr] Pr)
| z_top : zsym (ι Pr)
| z_bot : zsym (ι Pr)
| z_all : zsym (Spec [σP] Pr)
| z_ex  : zsym (Spec [σP] Pr)
| z_eq  : zsym (Spec [ι V; ι V] Pr)
| z_mem : zsym (Spec [ι V; ι V] Pr)
| z_empty : zsym (ι V)
| z_omega : zsym (ι V)
| z_pair : zsym (Spec [ι V; ι V] V)
| z_union : zsym (Spec [ι V] V)
| z_power : zsym (Spec [ι V] V)
| z_compr : zsym (Spec [ι V; σP] V)
| z_repl : zsym (Spec [ι V; σF] V)
| z_iota : zsym (Spec [σP] V).

#[export] Instance z_hasimp : HasImp zsym Pr := {| c_imp := z_imp |}.
#[export] Instance z_hasand : HasAnd zsym Pr := {| c_and := z_and |}.
#[export] Instance z_hasor  : HasOr zsym Pr  := {| c_or := z_or |}.
#[export] Instance z_hastop : HasTop zsym Pr := {| c_top := z_top |}.
#[export] Instance z_hasbot : HasBot zsym Pr := {| c_bot := z_bot |}.

#[export] Instance z_sets : SetSig zsym Pr V := {|
  s_mem := z_mem; s_empty := z_empty; s_omega := z_omega; s_pair := z_pair;
  s_union := z_union; s_power := z_power; s_compr := z_compr; s_repl := z_repl; s_iota := z_iota
|}.

#[export] Instance z_functional : Functional zsym := {|
  Arr := fun _ _ _ => Empty_set;
  s_lam := fun a b c w => match w with end;
  s_app := fun a b c w => match w with end
|}.

Definition z_grade (s : zsort) : grade := match s with V => (0, 0) | Pr => (0, 1) end.

Lemma z_gr_arr a b c (w : @Arr _ zsym z_functional a b c) : z_grade c = garr (z_grade a) (z_grade b).
Proof. destruct w. Qed.

#[export] Instance z_graded : Graded zsym := {| gr := z_grade; gr_arr := z_gr_arr |}.

Lemma hV : quantifiable (Sym := zsym) 1 1 V.
Proof. split; cbn; lia. Qed.
Lemma Pr_not_q : ~ quantifiable (Sym := zsym) 1 1 Pr.
Proof. intros [_ H]; cbn in H; lia. Qed.

Definition qa (s : zsort) : quantifiable (Sym := zsym) 1 1 s -> zsym (Spec [Spec [ι s] Pr] Pr) :=
  match s with V => fun _ => z_all | Pr => fun h => False_rect _ (Pr_not_q h) end.
Definition qe (s : zsort) : quantifiable (Sym := zsym) 1 1 s -> zsym (Spec [Spec [ι s] Pr] Pr) :=
  match s with V => fun _ => z_ex | Pr => fun h => False_rect _ (Pr_not_q h) end.
Definition qq (s : zsort) : quantifiable (Sym := zsym) 1 1 s -> zsym (Spec [ι s; ι s] Pr) :=
  match s with V => fun _ => z_eq | Pr => fun h => False_rect _ (Pr_not_q h) end.

#[export] Instance z_quant : Quantifiers zsym Pr 1 1 := {| q_all := qa; q_ex := qe; q_eq := qq |}.

(** Les quantificateurs et l'égalité sur V, vus comme instances de
    [HasForall] etc. : ce sont ceux de la logique d'ordre (1,1). *)
#[export] Instance z_forallV : HasForall zsym Pr V := qall_inst (existT _ V hV).
#[export] Instance z_existsV : HasExists zsym Pr V := qex_inst (existT _ V hV).
#[export] Instance z_eqV : HasEq zsym Pr V := qeq_inst (existT _ V hV).

(** Le calcul : les règles d'appartenance. La logique : intuitionniste
    d'ordre (1,1), plus l'extensionnalité et la description. *)
Definition C : system zsym := generated mem_rules.

Definition RR := rsum (iorder_rules (Sym := zsym) (P := Pr) (n := 1) (p := 1)) set_rules.

#[export] Typeclasses Transparent RR.
#[export] Hint Unfold RR : typeclass_instances.

Notation ZF Γ Ξ φ := (deriv C Pr RR Γ Ξ φ).

Notation x0 := (var0 vz).
Notation x1 := (var0 (vs vz)).
Notation x2 := (var0 (vs (vs vz))).
Notation EqV := (QEq (n := 1) (p := 1) V hV).

Tactic Notation "qap" uconstr(t) := eapply t; try typeclasses eauto.
Ltac hyp := apply d_ax; simpl; auto.

(** ** Calculs *)

Example mem_compr_ex : conv C (Γ := [ι V; ι V])
  (Mem x0 (Compr x1 (Neg (Mem x0 x0)))) (And (Mem x0 x1) (Neg (Mem x0 x0))).
Proof. exact (mem_compr mem_rules x0 x1 (Neg (Mem x0 x0))). Qed.

(** ** Dérivations *)

(** Rien n'appartient à ∅. *)
Example empty_no : ZF [ι V] [] (Neg (Mem x0 Empty)).
Proof.
  qap (imp_I C Pr RR).
  eapply d_conv; [exact (mem_empty mem_rules x0)|hyp].
Qed.

(** a ∈ {a, b}. *)
Example pair_left : ZF [ι V; ι V] [] (Mem x0 (Pair x0 x1)).
Proof.
  eapply d_conv; [apply conv_sym; exact (mem_pair mem_rules x0 x0 x1)|].
  qap (or_I1 C Pr RR). qap (qeq_refl C RR V hV).
Qed.

(** {z ∈ a | φ} ⊆ a, pour une métavariable φ du contexte. *)
Notation φv := (eta σP (Γ := [ι V; ι V; σP]) (vs (vs vz))).

Example compr_sub : ZF [ι V; ι V; σP] [Mem x0 (Compr x1 φv)] (Mem x0 x1).
Proof.
  qap (and_E1 C Pr RR _ _ (vsubst φv (inst1 x0))).
  eapply d_conv; [exact (mem_compr mem_rules x0 x1 φv)|hyp].
Qed.

(** a ∈ 𝒫(a). *)
Example self_power : ZF [ι V] [] (Mem x0 (Power x0)).
Proof.
  eapply d_conv; [apply conv_sym; exact (mem_power mem_rules x0 x0)|].
  qap (qall_I C RR V hV). qap (imp_I C Pr RR). hyp.
Qed.

(** Russell, en version restreinte : r := {z ∈ a | z ∉ z} n'est pas dans a.
    La preuve est intuitionniste. *)
Notation russ := (Compr x0 (Neg (Mem x0 x0))).

Example russell : ZF [ι V] [] (Neg (Mem russ x0)).
Proof.
  qap (imp_I C Pr RR).
  (* r ∈ r ⊢ r ∉ r, donc r ∉ r *)
  assert (Hn : ZF [ι V] [Mem russ x0] (Neg (Mem russ russ))).
  { qap (imp_I C Pr RR).
    qap (imp_E C Pr RR _ (Mem russ russ) Bot).
    - qap (and_E2 C Pr RR _ (Mem russ x0)).
      eapply d_conv; [exact (mem_compr mem_rules russ x0 (Neg (Mem x0 x0)))|hyp].
    - hyp. }
  (* mais alors r ∈ r *)
  qap (imp_E C Pr RR _ (Mem russ russ) Bot); [exact Hn|].
  eapply d_conv; [apply conv_sym; exact (mem_compr mem_rules russ x0 (Neg (Mem x0 x0)))|].
  qap (and_I C Pr RR); [hyp|exact Hn].
Qed.

(** Par extensionnalité : {z ∈ a | ⊤} = a. *)
Example compr_top : ZF [ι V] [] (EqV (Compr x0 Top) x0).
Proof.
  qap (extensionality C RR).
  - change (ZF [ι V; ι V] [Mem x0 (Compr x1 Top)] (Mem x0 x1)).
    qap (and_E1 C Pr RR _ _ Top).
    eapply d_conv; [exact (mem_compr mem_rules x0 x1 Top)|hyp].
  - change (ZF [ι V; ι V] [Mem x0 x1] (Mem x0 (Compr x1 Top))).
    eapply d_conv; [apply conv_sym; exact (mem_compr mem_rules x0 x1 Top)|].
    qap (and_I C Pr RR); [hyp|qap (top_I C Pr RR)].
Qed.

(** Par description : ι z. (z = a) vérifie z = a. *)
Example iota_eq : ZF [ι V] [] (EqV (Iota (EqV x0 x1)) x0).
Proof.
  refine (description C RR [] (EqV x0 x1) x0 _ _).
  - qap (qeq_refl C RR V hV).
  - hyp.
Qed.
