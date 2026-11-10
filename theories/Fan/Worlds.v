(** * Le théorème 41 avec des mondes

    La forme de l'article : un préordre (W, ≤, 1) de mondes et un foncteur
    F : W → EFdata à morphismes stricts (définition 35), avec E := F(1).
    Les conditions sont énoncées « en contexte », c'est-à-dire comme des
    entailments et non sur des réalisateurs :
    - recherche non bornée dans E (définition 39) ;
    - choix dans E : un réalisateur de ∀α. ∃n. φ(α, n) calcule une
      fonctionnelle (l'article l'utilise implicitement : « g(b) est un code
      d'une fonction (N → N) → N ») ;
    - sur un ensemble dense de mondes, continuité en contexte :
      ⌜G⌝ ∧ ⌜α⌝ ≤ [G continue en α] ;
    - chemins : tout α est codé dans un monde futur de chaque monde ;
    - localité : un fait méta que l'image de φ entraîne, dans un monde
      futur, pour chaque α, est entraîné par φ dans E.

    On en déduit les hypothèses de [Statement.v] pour E
    ([search_of_unbounded], [continuity_of_worlds]), d'où FT dans le modèle
    de HA_ω^{ω,ω} + listes sur E ([fan_worlds]). *)

From Stdlib Require Import List Arith.
Import ListNotations.
From SF.Models Require Import PSet Frame Tarski.
From SF.Extensions Require Import Same.
From SF.HA Require Import Signature Model.
From SF.Fan Require Import Ent Statement Terms FT.

Set Universe Polymorphism.

(** ** Morphismes stricts d'EFdata *)

Record smor (E1 E2 : efdata) := {
  mphi :> pcar (fprop E1) -> pcar (fprop E2);
  mev : fev E1 -> fev E2;
  m_ent : forall φ e ψ, fent φ e ψ -> fent (mphi φ) (mev e) (mphi ψ);
  m_top : mphi ftop ≡ ftop;
  m_and : forall φ ψ, mphi (fand φ ψ) ≡ fand (mphi φ) (mphi ψ);
  m_imp : forall φ ψ, mphi (fimp φ ψ) ≡ fimp (mphi φ) (mphi ψ);
  m_all : forall I (f : I -> pcar (fprop E1)), mphi (fall f) ≡ fall (fun i => mphi (f i));
  m_code : forall n, mphi (code n) ≡ code n
}.

Arguments mev {E1 E2} s e.
Arguments m_ent {E1 E2} s φ e ψ.
Arguments m_top {E1 E2} s.
Arguments m_imp {E1 E2} s φ ψ.
Arguments m_all {E1 E2} s I f.
Arguments m_code {E1 E2} s n.

Section Smor.
Context {E1 E2 : efdata} (m : smor E1 E2).

Lemma smor_cfun f : m (cfun E1 f) ≡ cfun E2 f.
Proof.
  unfold cfun. eapply peq_trans; [apply m_all|]. apply fall_proper. intros n.
  eapply peq_trans; [apply m_imp|]. apply fimp_proper; apply m_code.
Qed.

Lemma smor_cpath α : m (cpath E1 α) ≡ cpath E2 α.
Proof. apply smor_cfun. Qed.

Lemma smor_cfun2 G : m (cfun2 E1 G) ≡ cfun2 E2 G.
Proof.
  unfold cfun2. eapply peq_trans; [apply m_all|]. apply fall_proper. intros α.
  eapply peq_trans; [apply m_imp|]. apply fimp_proper; [apply smor_cpath|apply m_code].
Qed.

End Smor.

(** ** Les conditions *)

(** Définition 39 : recherche non bornée, pour les f qui ont un zéro. *)
Definition unbounded_search (E : efdata) : Prop :=
  exists e, forall f : nat -> nat, (exists n, f n = 0) ->
    fent (cfun E f) e (fex (fun n => fand (code n) (fprop_of (F := E) (f n = 0)))).

(** Continuité en contexte. *)
Definition cont_ctx (E : efdata) : Prop :=
  exists e, forall G α, fent (fand (cfun2 E G) (cpath E α)) e (fprop_of (F := E) (cont_at G α)).

Lemma search_of_unbounded E : unbounded_search E -> search E.
Proof.
  intros [e He].
  assert (K : ENT (fun f : nat -> nat => fand (cfun E f) (fprop_of (exists n, f n = 0)))
                  (fun f => fex (fun n => fand (code n) (fprop_of (F := E) (f n = 0))))).
  { apply (ent_meta_elim (fun f => exists n, f n = 0) (fun f => cfun E f)). exists e.
    intros [f Hf]. exact (He f Hf). }
  destruct K as [e' He']. exists e'. exact He'.
Qed.

Section Worlds.

Context (W : Type) (le : W -> W -> Prop) (one : W) (le_one : forall w, le one w).
Context (F : W -> efdata) (fm : forall w w', le w w' -> smor (F w) (F w')).

Local Notation E := (F one).

Definition dense (W' : W -> Prop) : Prop := forall w, exists w', le w w' /\ W' w'.

Definition paths : Prop :=
  forall α w, exists w' (h : le w w'), exists e, fent (F := F w') ftop e (cpath (F w') α).

Definition locality : Prop :=
  exists e, forall (φ : pcar (fprop E)) (P : (nat -> bool) -> Prop),
    (forall α, exists w e', fent (fm one w (le_one w) φ) e' (fprop_of (F := F w) (P α))) ->
    fent φ e (fprop_of (F := E) (forall α, P α)).

Theorem continuity_of_worlds (W' : W -> Prop) :
  dense W' -> (forall w, W' w -> cont_ctx (F w)) -> paths -> locality -> continuity E.
Proof.
  intros Hd Hc Hp [e Hl]. exists e. intros G. apply Hl. intros α.
  destruct (Hp α one) as (w1 & h1 & e1 & H1).
  destruct (Hd w1) as (w2 & h2 & Hw2). destruct (Hc w2 Hw2) as [ec Hec].
  pose proof (m_ent (fm w1 w2 h2) _ _ _ H1) as K.
  apply (fent_proper _ _ _ _ _ _ (m_top _) (smor_cpath _ α)) in K.
  exists w2, (e_comp (e_pair e_id (e_comp e_top (mev (fm w1 w2 h2) e1))) ec).
  apply (fent_proper _ _ _ _ _ _ (peq_sym (smor_cfun2 (fm one w2 (le_one w2)) G)) (peq_refl _)).
  eapply f_comp; [|exact (Hec G α)]. apply f_pair; [apply f_id|]. eapply f_comp; [apply f_top|exact K].
Qed.

(** ** Le théorème 41 *)

Theorem fan_worlds (W' : W -> Prop) :
  WKL_meta -> MP_meta -> unbounded_search E -> choice E ->
  dense W' -> (forall w, W' w -> cont_ctx (F w)) -> paths -> locality ->
  exists e, fent (F := E) ftop e (sval (So E) (Iy E (dsc := dL)) (ltr (Rel (dsc := dL)) FT.FT) tt).
Proof.
  intros WKL MP HS HCh Hd Hc Hp Hl.
  exact (ft_realized E WKL MP (search_of_unbounded E HS) HCh (continuity_of_worlds W' Hd Hc Hp Hl)).
Qed.

End Worlds.
