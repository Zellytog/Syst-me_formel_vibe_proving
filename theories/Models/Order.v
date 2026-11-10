(** * Modèles des logiques d'ordre (n,p)

    Une structure de modèle d'ordre (n,p) demande, en plus des connecteurs
    compatibles, une structure de quantification ([qstruct]) et une
    structure d'égalité ([eqstruct]) **pour chaque sorte quantifiable**, et
    seulement pour celles-là : les sortes du bord sont interprétées par le
    modèle du calcul, mais rien n'est demandé le long de leurs projections.

    Toutes les règles de la logique intuitionniste d'ordre (n,p)
    ([iorder_rules]) sont alors saines ([iorder_sound]) ; avec des fibres
    booléennes, celles de la logique classique ([corder_sound]). *)

From Category Require Import Lib Theory.Category Theory.Functor
  Structure.Terminal Structure.Cartesian Structure.Cartesian.Closed.
From Stdlib Require Import List.
Import ListNotations.
From SF.Syntax Require Import Spec Terms Vectors Syn.
From SF.Calculus Require Import System SynConv.
From SF.Logic Require Import Judgment Propositional.
From SF.Functional Require Import Arrow Graded.
From SF.Quantifiers Require Import Quant Order.
From SF.Models Require Import Calculus Hyperdoctrine Logic Quantifiers Equality.

Local Notation ι a := (Spec [] a).

Set Default Proof Using "All".

Section OrderModels.
Context {Srt : Type} {Sym : spec Srt -> Type} {FS : Functional Sym} {G : Graded Sym}.
Context (L : logic Sym).

Local Notation P := (l_prop Sym L).

Context {n p : bound} {QI : Quantifiers Sym P n p}.
Context {HI : HasImp Sym P} {HA : HasAnd Sym P} {HO : HasOr Sym P} {HT : HasTop Sym P} {HB : HasBot Sym P}.
Context (C : Category) {CT : @Terminal C} {CC : @Cartesian C} {CL : @Closed C CC}.
Context (M : cmodel (l_calc Sym L) C) (H : hyperdoctrine C) (T : pred H (M [ι P])).

Local Notation qs := (qsort Sym n p).

(** La structure demandée par l'ordre (n,p). *)
Record order_structure := {
  os_imp : bin_compat L C M H T c_imp (fun X => pimp);
  os_and : bin_compat L C M H T c_and (fun X => pand);
  os_or : bin_compat L C M H T c_or (fun X => por);
  os_top : cst_compat L C M H T c_top (fun X => ptop);
  os_bot : cst_compat L C M H T c_bot (fun X => pbot);
  os_q : forall k : qs, qstruct L C M H (projT1 k);
  os_all : forall k : qs, @all_compat _ _ L C _ _ _ M H T (projT1 k) (os_q k) (qall_inst k);
  os_ex : forall k : qs, @ex_compat _ _ L C _ _ _ M H T (projT1 k) (os_q k) (qex_inst k);
  os_e : forall k : qs, eqstruct L C M H (projT1 k);
  os_eq : forall k : qs, @eq_compat _ _ L C _ _ _ M H T (projT1 k) (os_e k) (qeq_inst k)
}.

Context (OS : order_structure).

Theorem quant_sound j : mrule_sound M H T (quant_rules (Sym := Sym) (P := P) (n := n) (p := p) j).
Proof.
  destruct j as [[k i]|[[k i]|[k i]]]; cbn [quant_rules rsum qall_rules qex_rules qeq_rules fst snd].
  - exact (@all_sound _ _ L C _ _ _ M H T (projT1 k) (os_q OS k) (qall_inst k) (os_all OS k) i).
  - exact (@ex_sound _ _ L C _ _ _ M H T (projT1 k) (os_q OS k) (qex_inst k) (os_ex OS k) i).
  - exact (@eq_sound _ _ L C _ _ _ M H T (projT1 k) (os_e OS k) (qeq_inst k) (os_eq OS k) i).
Qed.

(** Toutes les règles de la logique intuitionniste d'ordre (n,p) sont saines. *)
Theorem iorder_sound i : mrule_sound M H T (iorder_rules (Sym := Sym) (P := P) (n := n) (p := p) i).
Proof.
  destruct i as [i|j]; cbn [iorder_rules rsum].
  - exact (ipc_sound L C M H T (os_imp OS) (os_and OS) (os_or OS) (os_top OS) (os_bot OS) i).
  - apply quant_sound.
Qed.

(** Et celles de la logique classique, si les fibres sont booléennes. *)
Theorem corder_sound (Hb : boolean C H) i :
  mrule_sound M H T (corder_rules (Sym := Sym) (P := P) (n := n) (p := p) i).
Proof.
  destruct i as [[i|i]|j]; cbn [corder_rules cpc_rules rsum].
  - exact (ipc_sound L C M H T (os_imp OS) (os_and OS) (os_or OS) (os_top OS) (os_bot OS) i).
  - exact (em_sound L C M H T (os_imp OS) (os_or OS) (os_bot OS) Hb i).
  - apply quant_sound.
Qed.

End OrderModels.

(** La logique intuitionniste d'ordre (n,p) au-dessus d'un calcul. *)
Definition order_logic {Srt : Type} {Sym : spec Srt -> Type} {FS : Functional Sym} {G : Graded Sym}
  (CS : system Sym) (P : Srt) {n p : bound} {QI : Quantifiers Sym P n p}
  {HI : HasImp Sym P} {HA : HasAnd Sym P} {HO : HasOr Sym P} {HT : HasTop Sym P} {HB : HasBot Sym P} :
  logic Sym :=
  {| l_calc := CS; l_prop := P; l_idx := _; l_rules := iorder_rules (Sym := Sym) (P := P) (n := n) (p := p) |}.

(** Toute structure d'ordre (n,p) sur un modèle du calcul en fait un
    modèle de la logique intuitionniste d'ordre (n,p). *)
Definition order_lmodel {Srt : Type} {Sym : spec Srt -> Type} {FS : Functional Sym} {G : Graded Sym}
  (CS : system Sym) (P : Srt) {n p : bound} {QI : Quantifiers Sym P n p}
  {HI : HasImp Sym P} {HA : HasAnd Sym P} {HO : HasOr Sym P} {HT : HasTop Sym P} {HB : HasBot Sym P}
  (C : Category) {CT : @Terminal C} {CC : @Cartesian C} {CL : @Closed C CC}
  (M : cmodel (l_calc Sym (order_logic CS P (n := n) (p := p))) C) (H : hyperdoctrine C)
  (T : pred H (M [ι (l_prop Sym (order_logic CS P (n := n) (p := p)))]))
  (OS : order_structure (order_logic CS P (n := n) (p := p)) C M H T) :
  lmodel (order_logic CS P (n := n) (p := p)) C :=
  {| lm_calc := M; lm_hd := H; lm_truth := T;
     lm_rules := ltac:(intros i; eapply iorder_sound; exact OS) |}.
