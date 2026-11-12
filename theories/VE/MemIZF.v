(** * CC et DC de IZF dans V(Mem)

    Le choix dénombrable et le choix dépendant **de IZF** (énoncés dans
    L_IZF, ω et les couples étant définis par des formules) sont réalisés
    dans V(Mem), pour toute formule de L_IZF : on compose la réalisation de
    IZFε + CC (resp. + DC) ([MemSCA.v]) avec leur preuve dans IZFε + CC
    (resp. + DC) ([IZFChoice3.v], [IZFChoice5.v]). *)

From Stdlib Require Import List.
Import ListNotations.
From SF.Syntax Require Import Spec Terms Vectors.
From SF.Logic Require Import Judgment.
From SF.Models Require Import PSet Frame Tarski.
From SF.VE Require Import Trees Coll Sound MemSCA.
From SF.SetTheory Require Import IZFe IZFeExt IZFeIZF IZFChoice2 IZFChoice3 IZFChoice4 IZFChoice5.

Local Notation ι a := (Spec [] a).

Section VMemIZF.

Context (CC_N : forall (I : Type) (Q : nat -> I -> Prop),
          exists f : nat -> option I, forall n, (exists i, Q n i) -> exists i, f n = Some i /\ Q n i).
Context (coll : forall T, (T -> Trees.V MF) -> (Trees.V MF -> Trees.V MF -> pcar MF) -> Trees.V MF).
Context (coll_proper : forall T (xs xs' : T -> Trees.V MF) ψ ψ', Rproper MF ψ ->
           (forall t, teq MF (xs t) (xs' t)) -> (forall x y, ψ x y ≡ ψ' x y) ->
           teq MF (coll T xs ψ) (coll T xs' ψ')).
Context (coll_spec : forall T (xs : T -> Trees.V MF) ψ, Rproper MF ψ ->
           forall t β, exists s, ψ (xs t) β ≡ ψ (xs t) (sub MF (coll T xs ψ) s)).

Local Notation Iy0 := (Iy' MF (state -> code -> Prop) mp mdec coll coll_proper).

(** Le choix dénombrable de IZF, pour toute formule φ(n, y) de L_IZF. *)
Theorem ve_mem_izf_cc (ψ : form [ι IZFe.V; ι IZFe.V]) :
  lizf _ ψ -> exists e, fent (F := MF) ftop e (T0 MF (sval (So' MF) Iy0 (vsubst IZF_cc (vR1 ψ)) tt)).
Proof. intros Hl. exact (ve_mem_cc CC_N coll coll_proper coll_spec _ (izf_cc_lizf ψ Hl)). Qed.

Context (DC_N : forall (T : Type) (Rl : nat -> T -> T -> Prop) (t0 : T),
          (forall n x, exists y, Rl n x y) -> exists f : nat -> T, f 0 = t0 /\ forall n, Rl n (f n) (f (S n))).

(** Le choix dépendant de IZF, pour toute formule φ(x, y) de L_IZF. *)
Theorem ve_mem_izf_dc (ψ : form [ι IZFe.V; ι IZFe.V]) :
  lizf _ ψ -> exists e, fent (F := MF) ftop e (T0 MF (sval (So' MF) Iy0 (vsubst IZF_dc (vR1 ψ)) tt)).
Proof. intros Hl. exact (ve_mem_dc CC_N DC_N coll coll_proper coll_spec _ (izf_dc_lizf ψ Hl)). Qed.

End VMemIZF.
