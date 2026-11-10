(** * Exemples de systèmes fonctionnels

    1. Le λ-calcul simplement typé : les sortes sont les types simples, la
       relation [Arr a b c] dit « c est le type a → b ». Les flèches sont
       totales et libres.
    2. Un système *tronqué* : les sortes sont N et les N^k → N. Il n'existe
       pas de sorte (N → N) → N : seules les flèches de source N ont un
       témoin. C'est un système d'ordre (1,0), exactement les « fonctions
       d'entiers » sur lesquelles quantifie une (2,1)-arithmétique. *)

From Stdlib Require Import List Arith Lia.
Import ListNotations.
From SF.Syntax Require Import Spec Terms Vectors.
From SF.Calculus Require Import System Rules.
From SF.Functional Require Import Arrow Graded.

(** ** 1. Le λ-calcul simplement typé *)

Inductive ty := base | arr (a b : ty).

Local Notation ι a := (Spec [] a).

Inductive is_arr (a b : ty) : ty -> Type := mk_arr : is_arr a b (arr a b).

Inductive stlc : spec ty -> Type :=
| slam a b : stlc (Spec [Spec [ι a] b] (arr a b))
| sapp a b : stlc (Spec [ι (arr a b); ι a] b).

#[export] Instance stlc_functional : Functional stlc := {|
  Arr := is_arr;
  s_lam := fun a b c w => match w in is_arr _ _ c0 return stlc (Spec [Spec [ι a] b] c0) with
                          | mk_arr _ _ => slam a b end;
  s_app := fun a b c w => match w in is_arr _ _ c0 return stlc (Spec [ι c0; ι a] b) with
                          | mk_arr _ _ => sapp a b end
|}.

(** Les flèches sont fonctionnelles. *)
Lemma stlc_arr_functional : arr_functional stlc.
Proof. intros a b c c' [] []; reflexivity. Qed.

(** La graduation : hauteur fonctionnelle, aucune proposition. *)
Fixpoint ty_height (t : ty) : nat :=
  match t with base => 0 | arr a b => Nat.max (S (ty_height a)) (ty_height b) end.

Lemma stlc_gr_arr a b c (w : is_arr a b c) :
  (ty_height c, 0) = garr (ty_height a, 0) (ty_height b, 0).
Proof. destruct w; reflexivity. Qed.

#[export] Instance stlc_graded : Graded stlc := {|
  gr := fun t => (ty_height t, 0);
  gr_arr := stlc_gr_arr
|}.

Definition w_bb : Arr (Sym := stlc) base base (arr base base) := mk_arr base base.

(** β : (λx. x) y  ~  y, dans le contexte [y : base]. *)
Example beta_id :
  conv (beta_system stlc) (Γ := [ι base])
    (App w_bb (Lam w_bb (var0 vz)) (var0 vz)) (var0 vz).
Proof. exact (beta_conv beta_rules w_bb (var0 vz) (var0 vz)). Qed.

(** η : λx. f x  ~  f, dans le contexte [f : base → base], modulo βη. *)
Example eta_f :
  conv (beta_eta_system stlc) (Γ := [ι (arr base base)])
    (Lam w_bb (App w_bb (Terms.ren_tm (var0 vz) (wk [ι base])) (var0 vz))) (var0 vz).
Proof. exact (eta_conv (crsum beta_rules eta_rules) w_bb (var0 vz)). Qed.

(** ** 2. Un système tronqué : N et les N^k → N *)

(** La sorte [k] représente N^k → N ; la sorte 0 est N. *)
Definition nsort := nat.

Inductive n_arr : nsort -> nsort -> nsort -> Type := mk_narr k : n_arr 0 k (S k).

Inductive nsym : spec nsort -> Type :=
| nlam k : nsym (Spec [Spec [ι 0] k] (S k))
| napp k : nsym (Spec [ι (S k); ι 0] k).

#[export] Instance n_functional : Functional nsym := {|
  Arr := n_arr;
  s_lam := fun a b c w => match w in n_arr a0 b0 c0 return nsym (Spec [Spec [ι a0] b0] c0) with
                          | mk_narr k => nlam k end;
  s_app := fun a b c w => match w in n_arr a0 b0 c0 return nsym (Spec [ι c0; ι a0] b0) with
                          | mk_narr k => napp k end
|}.

Definition n_grade (k : nsort) : grade := (match k with 0 => 0 | S _ => 1 end, 0).

Lemma n_gr_arr a b c (w : n_arr a b c) : n_grade c = garr (n_grade a) (n_grade b).
Proof. destruct w as [[|k]]; reflexivity. Qed.

#[export] Instance n_graded : Graded nsym := {| gr := n_grade; gr_arr := n_gr_arr |}.

(** Toutes les sortes sont de grade ≤ (1,0), et toute flèche de grade ≤ (1,0)
    existe : c'est un système d'ordre (1,0). *)
#[export] Instance n_bounded : Bounded nsym 1 0.
Proof.
  constructor.
  - intros [|k]; compute; split; auto.
  - intros a b Hab. destruct a as [|a].
    + exists (S b). constructor.
    + exfalso. compute in Hab. destruct Hab as [Hab _].
      destruct b; [inversion Hab as [|? H']; inversion H'|inversion Hab as [|? H']; inversion H'].
Defined.

(** Il n'y a pas de flèche de source N → N : la sorte (N → N) → N n'existe pas. *)
Lemma no_higher_arrow b c : n_arr 1 b c -> False.
Proof. intros w. inversion w. Qed.
