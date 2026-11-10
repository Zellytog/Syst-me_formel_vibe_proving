(** * Le théorème de l'éventail dans les cadres d'évidence : énoncé

    Formalisation de la section 5 de « Oracles just for Fan » (Leclercq,
    Miquey, LICS 2026) : des conditions calculatoires sur un cadre
    d'évidence (EF) qui suffisent à réaliser le théorème de l'éventail.

    La version formalisée ne fait intervenir *que des entailments
    uniformes* : ni points, ni mondes. Les faits de la méta-théorie dont la
    preuve a besoin (« f s'annule », « F est continue ») sont portés par des
    propositions sans contenu calculatoire, [P] := ⋁_{p : P} ⊤ ([fprop_of]),
    et produits *à l'intérieur* de l'entailment. Trois hypothèses :

    - **Recherche non bornée, forme de Markov interne** ([search]) :
      ⌜f⌝ ∧ [∃n, f n = 0] ≤ ∃n. ⌜n⌝ ∧ [f n = 0], uniformément en f ;
    - **Existentiel fort au type (N → B) → N** ([choice]) : un réalisateur
      de ∀α. ∃n. φ(α, n) calcule une fonctionnelle F :
      ⋀_α (⌜α⌝ ⊃ ∃n. ⌜n⌝ ∧ φ(α, n)) ≤ ⋁_F ⌜F⌝ ∧ ⋀_α (⌜α⌝ ⊃ φ(α, F α)) ;
    - **Continuité partout** ([continuity]) : ⌜F⌝ ≤ [F continue en tout
      chemin α] — *tout* chemin, et non seulement ceux qui ont un code :
      c'est ce qu'apportent les oracles.

    La méta-théorie fournit WKL (pour les arbres décidables) et le principe
    de Markov, sous forme d'hypothèses. *)

From Stdlib Require Import List Arith.
Import ListNotations.
From SF.Models Require Import PSet Frame.
From SF.Fan Require Import Ent.

(** ** Cadres d'évidence avec entiers (EFdata, définition 33) *)

Record efdata := {
  ef :> frame;
  code : nat -> pcar (fprop ef);
  c0 : exists e, fent ftop e (code 0);
  cS : exists e, forall n, fent (code n) e (code (S n));
  crec : exists e, forall f : nat -> pcar (fprop ef),
      fent ftop e
        (fimp (f 0) (fimp (fall (fun n => fimp (code n) (fimp (f n) (f (S n)))))
                          (fall (fun n => fimp (code n) (f n)))))
}.

Arguments code {e} n.

Section Data.

Context (E : efdata).

Local Notation Φ := (pcar (fprop E)).

(** Codes des fonctions N → N, des chemins N → B, des fonctionnelles
    (N → B) → N (remarque 34). *)
Definition cfun (f : nat -> nat) : Φ := fall (fun n => fimp (code n) (code (f n))).
Definition cpath (α : nat -> bool) : Φ := cfun (fun n => Nat.b2n (α n)).
Definition cfun2 (G : (nat -> bool) -> nat) : Φ := fall (fun α => fimp (cpath α) (code (G α))).

(** α↾n, et l'ordre préfixe. *)
Definition pre (α : nat -> bool) (n : nat) : list bool := map α (seq 0 n).
Definition prefix (l l' : list bool) : Prop := exists s, l' = l ++ s.

(** ** Le théorème de l'éventail *)

(** La monotonie le long des chemins codés, avec des longueurs codées :
    B(α↾n) ⊃ B(α↾(n+k)). C'est la forme que prend la monotonie dans
    HA_ω^{ω,ω} relativisé ([FT.v]). *)
Definition Mono (B : list bool -> Φ) : Φ :=
  fall (fun α => fimp (cpath α) (fall (fun n => fimp (code n) (fall (fun k => fimp (code k)
    (fimp (B (pre α n)) (B (pre α (n + k))))))))).

Definition Bar (B : list bool -> Φ) : Φ :=
  fall (fun α => fimp (cpath α) (fex (fun n => fand (code n) (B (pre α n))))).

Definition Unif (B : list bool -> Φ) : Φ :=
  fex (fun n => fand (code n) (fall (fun α => fimp (cpath α) (B (pre α n))))).

Definition FT : Φ := fall (fun B : list bool -> Φ => fimp (fand (Mono B) (Bar B)) (Unif B)).

(** ** Les conditions calculatoires *)

Definition search : Prop :=
  exists e, forall f : nat -> nat,
    fent (fand (cfun f) (fprop_of (exists n, f n = 0))) e
         (fex (fun n => fand (code n) (fprop_of (f n = 0)))).

Definition choice : Prop :=
  exists e, forall φ : (nat -> bool) -> nat -> Φ,
    fent (fall (fun α => fimp (cpath α) (fex (fun n => fand (code n) (φ α n))))) e
         (fex (fun G : (nat -> bool) -> nat =>
                 fand (cfun2 G) (fall (fun α => fimp (cpath α) (φ α (G α)))))).

(** Continuité de G en α. *)
Definition cont_at (G : (nat -> bool) -> nat) (α : nat -> bool) : Prop :=
  exists m, forall β, (forall i, i < m -> β i = α i) -> G β = G α.

Definition continuity : Prop :=
  exists e, forall G, fent (cfun2 G) e (fprop_of (forall α, cont_at G α)).

End Data.

(** ** La méta-théorie *)

(** WKL pour les arbres décidables : un arbre infini a un chemin infini. *)
Definition WKL_meta : Prop :=
  forall T : list bool -> bool,
    (forall l l', prefix l l' -> T l' = true -> T l = true) ->
    (forall n, exists l, length l = n /\ T l = true) ->
    exists α, forall n, T (pre α n) = true.

(** Le principe de Markov. *)
Definition MP_meta : Prop :=
  forall p : nat -> bool, ~ (forall n, p n = false) -> exists n, p n = true.

(** ** Le théorème 41 *)

Definition robust_fan : Prop :=
  forall E : efdata, search E -> choice E -> continuity E ->
    exists e, fent ftop e (FT E).
