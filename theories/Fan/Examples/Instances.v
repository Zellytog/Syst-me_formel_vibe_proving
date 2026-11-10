(** * Deux modèles qui réalisent le théorème de l'éventail

    - **ESAT** (section 3 de l'article) : les mondes sont les listes finies
      σ = [f₀; …; fₖ₋₁] de fonctions N → B, ordonnées par préfixe ; l'oracle
      ξᵢ est interprété par σ[i] quand i < |σ|, et bloqué sinon. Un oracle
      frais pour α s'obtient en prolongeant σ par α.
    - **La variante « oracles partout »**, qui tient le rôle de K2 : un seul
      monde, et un oracle (i, f) pour chaque fonction f et chaque étiquette
      i ; tout chemin a un code, et les étiquettes fournissent des oracles
      frais.

    Dans les deux cas, sous WKL et Markov (méta), l'EF induit réalise FT
    ([esat_fan], [oracles_fan]), donc aussi l'énoncé FT de HA_ω^{ω,ω} +
    listes dans le modèle de HA sur cette EF ([esat_ft], [oracles_ft]) : HA
    + listes ne réfute pas FT ([ha_not_refutes_FT_esat]). *)

From Stdlib Require Import List Arith Lia.
Import ListNotations.
From SF.Models Require Import Frame.
From SF.Models Require Import Tarski.
From SF.Extensions Require Import Same.
From SF.Calculus Require Import System.
From SF.Logic Require Import Judgment Propositional.
From SF.HA Require Import Signature Model.
From SF.Fan Require Import Statement Terms FT.
From SF.Fan.Examples Require Import Lam Kripke.

(** ** ESAT *)

Definition prefix_le (σ τ : list (nat -> bool)) : Prop := exists l, τ = σ ++ l.

Lemma prefix_refl σ : prefix_le σ σ.
Proof. exists []. rewrite app_nil_r. reflexivity. Qed.

Lemma prefix_trans a b c : prefix_le a b -> prefix_le b c -> prefix_le a c.
Proof. intros [l1 ->] [l2 ->]. exists (l1 ++ l2). rewrite app_assoc. reflexivity. Qed.

Definition esat_O (σ : list (nat -> bool)) (i : nat) : option (nat -> bool) := nth_error σ i.

Lemma esat_mono σ τ i f : prefix_le σ τ -> esat_O σ i = Some f -> esat_O τ i = Some f.
Proof.
  intros [l ->] H. unfold esat_O in *. rewrite nth_error_app1; [exact H|].
  apply nth_error_Some. congruence.
Qed.

Definition esat_fresh (σ : list (nat -> bool)) (N : nat) (α : nat -> bool) : list (nat -> bool) * nat :=
  (σ ++ repeat (fun _ => false) (N - length σ) ++ [α], length σ + (N - length σ)).

Lemma esat_fresh_le σ N α : prefix_le σ (fst (esat_fresh σ N α)).
Proof. eexists. reflexivity. Qed.

Lemma esat_fresh_tag σ N α : N <= snd (esat_fresh σ N α).
Proof. cbn. lia. Qed.

Lemma esat_fresh_O σ N α : esat_O (fst (esat_fresh σ N α)) (snd (esat_fresh σ N α)) = Some α.
Proof.
  unfold esat_O, esat_fresh; cbn [fst snd].
  rewrite nth_error_app2 by lia. replace (length σ + (N - length σ) - length σ) with (N - length σ) by lia.
  rewrite nth_error_app2 by (rewrite repeat_length; lia). rewrite repeat_length, Nat.sub_diag. reflexivity.
Qed.

Definition ESAT : efdata := kE (list (nat -> bool)) prefix_le prefix_refl prefix_trans esat_O esat_mono.

Theorem esat_consistent : ~ exists e, fent (F := ESAT) ftop e fbot.
Proof. exact (k_consistent (C := nat) (list (nat -> bool)) prefix_le prefix_refl prefix_trans esat_O esat_mono []). Qed.

Theorem esat_fan : WKL_meta -> MP_meta -> exists e, fent ftop e (Statement.FT ESAT).
Proof.
  exact (kripke_fan (C := nat) (fun i => i) (list (nat -> bool)) prefix_le prefix_refl prefix_trans esat_O esat_mono
           esat_fresh esat_fresh_le esat_fresh_tag esat_fresh_O).
Qed.

Lemma esat_hyps : search ESAT /\ choice ESAT /\ continuity ESAT.
Proof.
  exact (kripke_hyps (C := nat) (fun i => i) (list (nat -> bool)) prefix_le prefix_refl prefix_trans esat_O esat_mono
           esat_fresh esat_fresh_le esat_fresh_tag esat_fresh_O).
Qed.

(** FT, énoncé dans HA_ω^{ω,ω} + listes, est réalisé dans le modèle de HA sur ESAT. *)
Theorem esat_ft : WKL_meta -> MP_meta ->
  exists e, fent (F := ESAT) ftop e (sval (So ESAT) (Iy ESAT (dsc := dL)) (ltr (Rel (dsc := dL)) FT.FT) tt).
Proof.
  intros WKL MP. destruct esat_hyps as (HS & HCh & HCo). exact (ft_realized ESAT WKL MP HS HCh HCo).
Qed.

Corollary ha_not_refutes_FT_esat : WKL_meta -> MP_meta -> ~ provable (HA (dsc := dL)) [] [] (Imp FT.FT Bot).
Proof.
  intros WKL MP. destruct esat_hyps as (HS & HCh & HCo).
  exact (ha_not_refutes_FT ESAT WKL MP HS HCh HCo esat_consistent).
Qed.

(** ** Oracles partout *)

Definition all_O (_ : unit) (c : nat * (nat -> bool)) : option (nat -> bool) := Some (snd c).

Definition all_fresh (_ : unit) (N : nat) (α : nat -> bool) : unit * (nat * (nat -> bool)) := (tt, (N, α)).

Definition ORACLES : efdata :=
  kE unit (fun _ _ => True) (fun _ => Logic.I) (fun _ _ _ _ _ => Logic.I) all_O
     (fun _ _ _ _ _ H => H).

Theorem oracles_consistent : ~ exists e, fent (F := ORACLES) ftop e fbot.
Proof.
  exact (k_consistent (C := nat * (nat -> bool)) unit (fun _ _ => True) (fun _ => Logic.I)
           (fun _ _ _ _ _ => Logic.I) all_O (fun _ _ _ _ _ H => H) tt).
Qed.

Theorem oracles_fan : WKL_meta -> MP_meta -> exists e, fent ftop e (Statement.FT ORACLES).
Proof.
  exact (kripke_fan (C := nat * (nat -> bool)) fst unit (fun _ _ => True) (fun _ => Logic.I)
           (fun _ _ _ _ _ => Logic.I) all_O (fun _ _ _ _ _ H => H)
           all_fresh (fun _ _ _ => Logic.I) (fun _ _ _ => le_n _) (fun _ _ _ => eq_refl)).
Qed.

Lemma oracles_hyps : search ORACLES /\ choice ORACLES /\ continuity ORACLES.
Proof.
  exact (kripke_hyps (C := nat * (nat -> bool)) fst unit (fun _ _ => True) (fun _ => Logic.I)
           (fun _ _ _ _ _ => Logic.I) all_O (fun _ _ _ _ _ H => H)
           all_fresh (fun _ _ _ => Logic.I) (fun _ _ _ => le_n _) (fun _ _ _ => eq_refl)).
Qed.

Theorem oracles_ft : WKL_meta -> MP_meta ->
  exists e, fent (F := ORACLES) ftop e (sval (So ORACLES) (Iy ORACLES (dsc := dL)) (ltr (Rel (dsc := dL)) FT.FT) tt).
Proof.
  intros WKL MP. destruct oracles_hyps as (HS & HCh & HCo). exact (ft_realized ORACLES WKL MP HS HCh HCo).
Qed.
