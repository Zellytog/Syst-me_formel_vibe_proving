(** * Réalisabilité de HA_ω^{ω,ω} dans toute PCA

    Une PCA donne un cadre d'évidence ([Models/PCA.v]) ; on instancie la
    construction de [Model.v] avec ce cadre. Tout théorème clos de HA a un
    réalisateur : un élément de A dans l'interprétation de sa traduction
    relativisée ([ha_realizable]). Le réalisateur est obtenu en appliquant
    l'évidence (un combinateur construit à partir de la preuve) à K. *)

From Stdlib Require Import List.
Import ListNotations.
From SF.Syntax Require Import Spec Terms.
From SF.Logic Require Import Judgment Propositional.
From SF.Extensions Require Import Same.
From SF.Models Require Import PSet Frame Tarski FrameModel PCA K1.
From SF.HA Require Import Signature Translation Model.

Section Realizability.

Context (A : pca) {Ind : Type} (dsc : Ind -> list (list bool)).
Local Notation hsym := (hsym dsc).
Local Notation HA := (HA (dsc := dsc)).
Local Notation Rel := (Rel (dsc := dsc)).

Local Notation RF := (pca_frame A).

(** r réalise l'énoncé clos φ de HA : r ∈ ⟦φ^D⟧. *)
Definition realizes (φ : Judgment.form hsym tO []) (r : A) : Prop :=
  sval (So RF) (Iy RF) (ltr Rel φ) tt r.

Theorem ha_realizable φ : provable HA [] [] φ -> exists r, realizes φ r.
Proof.
  intros H. destruct (ha_sound_closed RF (dsc := dsc) φ H) as [e He].
  destruct (He cK Logic.I) as (r & _ & Hr). exists r. exact Hr.
Qed.

(** ⊥ n'est pas réalisé : HA ne prouve pas ⊥ (pour toute PCA). *)
Lemma bot_unrealized r : ~ realizes Bot r.
Proof.
  intros Hr. destruct (Hr (fall_idx (F := RF) _ (bsel RF (fun _ => False) (fun _ => True)))) as (b & _ & Hb).
  destruct (Hb cK Logic.I) as (c & _ & Hc). exact Hc.
Qed.

Corollary ha_consistent_pca : ~ provable HA [] [] Bot.
Proof. intros H. destruct (ha_realizable _ H) as [r Hr]. exact (bot_unrealized r Hr). Qed.

End Realizability.

(** ** Une instance : la PCA triviale

    Un seul élément, toutes les applications définies. Elle sert à vérifier
    que la construction s'instancie de bout en bout ; les PCA intéressantes
    (Kleene K1, modèles de graphes, termes de λ-calcul) s'y substituent
    sans rien changer d'autre. *)

Definition unit_pca : pca := {|
  pc := unit;
  ap := fun _ _ _ => True;
  cK := tt; cS := tt;
  k1 := fun _ => tt; s1 := fun _ => tt; s2 := fun _ _ => tt;
  ap_K := fun _ => Logic.I; ap_K1 := fun _ _ => Logic.I;
  ap_S := fun _ => Logic.I; ap_S1 := fun _ _ => Logic.I;
  ap_S2 := fun _ _ _ _ _ _ _ _ _ => Logic.I
|}.

Definition unit_realizable {Ind} (dsc : Ind -> list (list bool)) := ha_realizable unit_pca dsc.

(** ** Réalisabilité de Kleene

    Avec K1 ([Models/K1.v]), les réalisateurs sont des entiers, codes de
    programmes : tout théorème clos de HA_ω^{ω,ω} (avec types inductifs)
    est réalisé par un code. *)

Corollary kleene_realizable {Ind} (dsc : Ind -> list (list bool)) φ :
  provable (HA (dsc := dsc)) [] [] φ -> exists n : nat, realizes K1 dsc φ n.
Proof. exact (ha_realizable K1 dsc φ). Qed.

