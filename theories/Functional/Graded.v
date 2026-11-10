(** * Graduation (n,p) des sortes

    La graduation est une *donnée* [gr : Srt -> nat * nat] (hauteur
    fonctionnelle, hauteur propositionnelle), soumise à une contrainte de
    cohérence avec [Arr] :

      Arr a b c  ->  gr c = garr (gr a) (gr b)

    avec garr (m,q) (m',q') = (max (1+m) m', max (q + χ(q)) q'), où
    χ(q) = 0 si q = 0, 1 sinon. Un système d'ordre (n,p) a toutes ses sortes
    sous (n,p) et contient toutes les flèches dont le grade calculé reste sous
    (n,p). On ne quantifiera que sur les sortes strictement sous la borne. *)

From Stdlib Require Import List Arith Lia.
Import ListNotations.
From SF.Syntax Require Import Spec Terms.
From SF.Functional Require Import Arrow.

Definition grade : Type := (nat * nat)%type.

(** ** Bornes : un entier ou ω

    Les ordres (n,p) et la hauteur r des récurseurs sont des bornes, finies
    ou infinies. Un entier est une borne finie (coercion [fin]) ; [omega] ne
    borne rien. *)
Inductive bound : Type := fin (n : nat) | omega.
Coercion fin : nat >-> bound.
Bind Scope nat_scope with bound.

(** m < b et m ≤ b. *)
Definition blt (m : nat) (b : bound) : Prop := match b with fin n => m < n | omega => True end.
Definition ble (m : nat) (b : bound) : Prop := match b with fin n => m <= n | omega => True end.

Lemma blt_ble m b : blt m b -> ble m b.
Proof. destruct b; cbn; lia. Qed.

Lemma blt_mono m m' b : m <= m' -> blt m' b -> blt m b.
Proof. destruct b; cbn; lia. Qed.

Lemma ble_mono m m' b : m <= m' -> ble m' b -> ble m b.
Proof. destruct b; cbn; lia. Qed.

(** m < b ⇔ m + 1 ≤ b. *)
Lemma blt_S m b : blt m b <-> ble (S m) b.
Proof. destruct b; cbn; lia. Qed.

Definition chi (q : nat) : nat := if Nat.eqb q 0 then 0 else 1.

Definition garr (g g' : grade) : grade :=
  (Nat.max (S (fst g)) (fst g'), Nat.max (snd g + chi (snd g)) (snd g')).

(** Ordre large composante par composante, et « strictement sous la borne ». *)
Definition gle (g g' : grade) : Prop := fst g <= fst g' /\ snd g <= snd g'.
Definition gleb (g : grade) (n p : bound) : Prop := ble (fst g) n /\ ble (snd g) p.
Definition gbelow (g : grade) (n p : bound) : Prop := blt (fst g) n /\ blt (snd g) p.

Section Graded.

Context {Srt : Type} (Sym : spec Srt -> Type) `{Functional Srt Sym}.

Class Graded := {
  gr : Srt -> grade;
  gr_arr : forall a b c, Arr a b c -> gr c = garr (gr a) (gr b)
}.

Context {G : Graded}.

(** Un système d'ordre (n,p) : sortes sous (n,p), flèches « au bord » présentes. *)
Class Bounded (n p : bound) := {
  bnd_sorts : forall s, gleb (gr s) n p;
  bnd_closed : forall a b, gleb (garr (gr a) (gr b)) n p -> { c & Arr a b c }
}.

(** Les sortes sur lesquelles une logique d'ordre (n,p) quantifie. *)
Definition quantifiable (n p : bound) (s : Srt) : Prop := gbelow (gr s) n p.

(** La sorte des propositions est de grade (0,1). *)
Class PropGrade (P : Srt) := { gr_P : gr P = (0, 1) }.

(** Les prédicats sur une sorte quantifiable existent (au bord) : c'est ce qui
    permet d'écrire des schémas sur les prédicats de cette sorte. *)
Theorem predicate_sort n p `{Bounded n p} (P : Srt) `{PropGrade P} (a : Srt) :
  quantifiable n p a -> { c & Arr a P c }.
Proof.
  intros [Hn Hp]. apply bnd_closed. rewrite (gr_P (P := P)). unfold garr, gleb, chi; cbn [fst snd].
  split.
  - eapply ble_mono; [|apply (proj1 (blt_S _ _) Hn)]. lia.
  - destruct (Nat.eqb (snd (gr a)) 0); destruct p as [p|]; cbn in *; lia.
Qed.

(** Le grade d'une flèche majore celui de son argument (strictement en
    hauteur fonctionnelle) et celui de son résultat. *)
Lemma garr_fst g g' : fst g < fst (garr g g') /\ fst g' <= fst (garr g g').
Proof. unfold garr; cbn [fst]; lia. Qed.

Lemma garr_snd g g' : snd g <= snd (garr g g') /\ snd g' <= snd (garr g g').
Proof. unfold garr, chi; cbn [snd]; destruct (Nat.eqb (snd g) 0); lia. Qed.

Lemma garr_prop g g' : 0 < snd g -> snd g < snd (garr g g').
Proof.
  unfold garr, chi; cbn [snd]; intros Hq.
  destruct (Nat.eqb_spec (snd g) 0); [lia|lia].
Qed.

End Graded.

Arguments Graded {Srt} Sym {_}.
Arguments gr {Srt Sym _ _} s.
Arguments Bounded {Srt} Sym {_ G} n p.
Arguments quantifiable {Srt Sym _ G} n p s.
Arguments PropGrade {Srt} Sym {_ G} P.
