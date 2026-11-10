(** * Correction par admissibilité, sur une classe de contextes

    [rule_tr_sound] (dans [Criterion.v]) demande que la traduction d'une
    règle soit *une règle* de L2. Pour les relativisations, la traduction
    d'une règle n'est en général qu'*admissible* dans L2. C'est le cas de
    ∀I, qui conclut ∀x (D(x) ⇒ φ), ou de la récurrence. Et elle ne l'est
    souvent que pour certains contextes : par exemple ceux dont toutes les
    variables sont de sorte, pour lesquels les hypothèses de relativisation
    D(x) ont un sens.

    [tr_rule_adm Q r] : pour tout contexte Γ de la classe Q, toute instance
    de la règle traduite, dont les prémisses sont dérivables (sous les
    hypothèses de relativisation de Γ), a sa conclusion dérivable.

    [interp_sound_on] : si les conversions sont préservées, si la classe Q
    est stable par les extensions de contexte des prémisses, et si les
    traductions de toutes les règles sont admissibles sur Q, alors tout
    jugement prouvable dans L1, de contexte dans Q, a une traduction
    prouvable dans L2. *)

From Stdlib Require Import List.
Import ListNotations.
From SF.Syntax Require Import Spec Terms Renaming Traversal Eta Composition Vectors.
From SF.Calculus Require Import System Rules.
From SF.Logic Require Import Judgment.
From SF.Extensions Require Import Conservativity Interpretation Commute Soundness Criterion.

Section Admissible.
Context {S1 S2 : Type} {Sym1 : spec S1 -> Type} {Sym2 : spec S2 -> Type}.
Context (L1 : logic Sym1) (L2 : logic Sym2) (F : linterp L1 L2).

Local Notation P1 := (l_prop Sym1 L1).
Local Notation P2 := (l_prop Sym2 L2).
Local Notation G := (li_sig F).
Local Notation fs := (i_srt G).
Local Notation cm := (cmap fs).
Local Notation form2 := (form Sym2 P2).
Local Notation "Γ ; Ξ ⊢₂ φ" := (provable L2 Γ Ξ φ) (at level 70).

(** La règle traduite de r est admissible dans L2, pour les contextes de Q. *)
Definition tr_rule_adm (Q : ctx S1 -> Prop) (r : drule Sym1 P1) : Prop :=
  forall Γ, Q Γ -> forall (Ξ : list (form2 (cm Γ))) (w : vec Sym2 (cm (d_ctx r)) (cm Γ)),
    (forall p, In p (d_prems (tr_rule F r)) ->
       (p_ext p ++ cm Γ) ; inst_hyps p w (rel_hyps F Γ ++ Ξ) ⊢₂ inst_goal p w) ->
    cm Γ ; rel_hyps F Γ ++ Ξ ⊢₂ vsubst (d_concl (tr_rule F r)) w.

(** Une règle de L2 est admissible pour elle-même : le cas où la traduction
    est une règle. *)
Lemma tr_rule_adm_rule Q r : (exists j, l_rules Sym2 L2 j = tr_rule F r) -> tr_rule_adm Q r.
Proof. intros [j Hj] Γ _ Ξ w Hp. eapply d_rule_eq; [exact Hj|exact Hp]. Qed.

Theorem interp_sound_on (Q : ctx S1 -> Prop) :
  (forall Γ s (t u : Terms.tm Sym1 Γ s), conv (l_calc Sym1 L1) t u -> conv (l_calc Sym2 L2) (tr G t) (tr G u)) ->
  (forall i p Γ, In p (d_prems (l_rules Sym1 L1 i)) -> Q Γ -> Q (p_ext p ++ Γ)) ->
  (forall i, tr_rule_adm Q (l_rules Sym1 L1 i)) ->
  forall Γ Ξ φ, Q Γ -> provable L1 Γ Ξ φ -> valid L2 (jtr F (mkJ Γ Ξ φ)).
Proof.
  intros HC HQ HR Γ Ξ φ HΓ H. unfold valid, provable in *; cbn [j_ctx j_hyps j_goal] in *.
  revert HΓ. induction H as [Γ Ξ φ Hin|Γ Ξ φ ψ Hc H IH|Γ Ξ i v Hp IH]; intros HΓ.
  - apply d_ax. apply in_or_app; right. exact (in_map (ltr F) _ _ Hin).
  - eapply d_conv; [|exact (IH HΓ)]. unfold ltr, pcast. apply conv_cast, HC, Hc.
  - unfold jtr, strans; cbn [j_ctx j_hyps j_goal].
    rewrite ltr_vsubst.
    change (vsubst (ltr F (d_concl (l_rules Sym1 L1 i))) (trv G v))
      with (vsubst (d_concl (tr_rule F (l_rules Sym1 L1 i))) (trv G v)).
    apply (HR i Γ HΓ (map (ltr F) Ξ) (trv G v)).
    intros p' Hp'. cbn [tr_rule d_prems] in Hp'. apply in_map_iff in Hp' as (p & <- & Hin).
    specialize (IH p Hin (HQ i p Γ Hin HΓ)).
    unfold valid, provable, jtr, strans, inst_hyps, inst_goal in IH |- *.
    cbn [j_ctx j_hyps j_goal tr_prem premx p_ext p_hyps p_goal] in IH |- *.
    apply (deriv_ren L2 _ (capp fs (p_ext p))) in IH.
    rewrite (ltr_vup_capp L1 L2 F) in IH.
    eapply deriv_weaken; [exact IH|].
    apply (hyps_incl L1 L2 F).
Qed.

End Admissible.

Arguments tr_rule_adm {S1 S2 Sym1 Sym2 L1 L2} F Q r.
