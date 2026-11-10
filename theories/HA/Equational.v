(** * La version équationnelle de HA est contenue dans HA

    Dans [HAE], les équations des récurseurs des types inductifs sont des
    règles de déduction ⊢ rec(c(x⃗), st⃗) = st_c(x⃗, rec(y⃗, st⃗)) ; dans [HA], ce
    sont des conversions. Chaque équation se prouve dans HA par réflexivité,
    modulo la conversion : tout théorème de HAE est un théorème de HA
    ([hae_to_ha]). Le modèle de HA dans un cadre d'évidence quelconque
    ([Model.v]) est donc aussi un modèle de HAE. *)

From Stdlib Require Import List.
Import ListNotations.
From SF.Syntax Require Import Spec Terms Vectors.
From SF.Calculus Require Import System Rules.
From SF.Logic Require Import Judgment Propositional.
From SF.Functional Require Import Arrow Graded.
From SF.Quantifiers Require Import Quant Order.
From SF.Arithmetic Require Import Arith Inductive.
From SF.Extensions Require Import Conservativity RuleExt.
From SF.HA Require Import Signature.

Local Notation ι a := (Spec [] a).

Section Equational.
Context {Ind : Type} {dsc : Ind -> list (list bool)}.
Local Notation hsym := (Signature.hsym dsc).
Local Notation HC := (generated (ha_calc_rules (dsc := dsc))).

#[local] Typeclasses Transparent ha_calc_rules hae_calc_rules ha_rules hae_rules.

Lemma hae_calc_le : sys_le (generated (hae_calc_rules (dsc := dsc))) HC.
Proof. apply sys_le_generated_incl. typeclasses eauto. Qed.

Lemma weq_admissible k :
  admissible tO HC (ha_rules (dsc := dsc)) (weq_rules (IN := h_ind) (HQ := h_haseq) tO k).
Proof.
  destruct k as [i [s [h [bs c]]]]. intros Γ Ξ v _. cbn [weq_rules weq_rule d_concl d_ctx] in *.
  rewrite vsubst_Eq.
  eapply d_conv; [|exact (qeq_refl HC ha_rules s (conj Logic.I Logic.I) Ξ (vsubst (wrec_lhs i s h bs c) v))].
  pose proof (generated_instance (ha_calc_rules (dsc := dsc)) (inr (existT _ i (existT _ s (existT _ h (existT _ bs c))))) v) as H.
  exact (conv_tsym HC (σ := Spec [ι s; ι s] tO) (h_eq s)
           (@acons _ hsym Γ (ι s) _ (vsubst (wrec_lhs i s h bs c) v) (@acons _ hsym Γ (ι s) _ (vsubst (wrec_lhs i s h bs c) v) anil))
           (@acons _ hsym Γ (ι s) _ (vsubst (wrec_lhs i s h bs c) v) (@acons _ hsym Γ (ι s) _ (vsubst (wrec_rhs i s h bs c) v) anil))
           (conj (conv_refl _ _) (conj H Logic.I))).
Qed.

Theorem hae_to_ha Γ Ξ φ : provable (HAE (dsc := dsc)) Γ Ξ φ -> provable (HA (dsc := dsc)) Γ Ξ φ.
Proof.
  apply (deriv_admissible tO _ _ ha_rules hae_rules hae_calc_le).
  intros [j|k]; [exact (admissible_rule tO HC ha_rules j)|apply weq_admissible].
Qed.

End Equational.
