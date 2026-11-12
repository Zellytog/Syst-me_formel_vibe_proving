(** * Le choix dépendant dans V(E)

    Si le cadre E valide le choix dépendant **au niveau du tripos**
    ([frame_dc] : d'un départ ⋁ᵢ A(i) ∧ P₀(i) et d'une relation totale
    ⋀ᵢ A(i) ⇒ ⋁ⱼ A(j) ∧ R(i, j), une suite S(t, i) totale, déterminée,
    dans A, issue de P₀ et qui suit R), alors V(E) réalise le schéma
    borné de IZFε ([IZFeDC.v]). La suite est f ≜ {⟨sₜ, X(s)⟩ | ⌜t⌝ ∧ S(t, s)}
    (la même construction [fS] que pour le choix dénombrable) ; le pas
    utilise S(sₜ) = sₜ₊₁ et l'injectivité de t ↦ sₜ ([snat_inj]). *)

From SF.Models Require Import PSet Frame FrameModel.
From SF.VE Require Import Trees Base ND Cons Coll CC.

Set Default Proof Using "All".

Section DC.
Context (F : frame).
Local Notation "φ —[ e ]→ ψ" := (fent (F := F) φ e ψ) (at level 70).
Local Notation V := (Trees.V F).
Local Notation teq := (teq F).
Local Notation idx := (idx F).
Local Notation lbl := (lbl F).
Local Notation sub := (sub F).
Local Notation eps := (eps F).
Local Notation veq := (veq F).
Local Notation vop := (vop F).
Local Notation pnat := (pnat F).
Local Notation snat := (snat F).
Local Notation vomega := (vomega F).
Local Notation vempty := (vempty F).
Local Notation vsuc := (vsuc F).
Local Notation fmeta := (fmeta F).
Local Notation fS := (fS F).

(** ** Le choix dépendant du tripos *)

Definition DHyp {I : Type} (A P0 : I -> pcar F) (R : I -> I -> pcar F) : pcar F :=
  fand (fex (fun i : I => fand (A i) (P0 i)))
       (fall (fun i : I => fimp (A i) (fex (fun j : I => fand (A j) (R i j))))).

Definition DPack {I : Type} (A P0 : I -> pcar F) (R : I -> I -> pcar F) (S : nat -> I -> pcar F) : pcar F :=
  fand (fall (fun t : nat => fimp (pnat t) (fex (fun i : I => S t i))))
  (fand (fall (fun t : nat => fall (fun i : I => fimp (S t i) (A i))))
  (fand (fall (fun t : nat => fall (fun i : I => fall (fun i' : I =>
           fimp (fand (S t i) (S t i')) (fmeta (i = i'))))))
  (fand (fall (fun i : I => fimp (S 0 i) (P0 i)))
        (fall (fun t : nat => fall (fun i : I => fall (fun j : I =>
           fimp (fand (S t i) (S (Datatypes.S t) j)) (R i j)))))))).

Definition frame_dc (m : fev F) : Prop :=
  forall (I : Type) (A P0 : I -> pcar F) (R : I -> I -> pcar F),
    DHyp A P0 R —[m]→ fex (fun S : nat -> I -> pcar F => DPack A P0 R S).

(** ** Le schéma, sous forme sémantique « propre » *)

Definition dcHyp (X : V) (ψ : V -> V -> pcar F) : pcar F :=
  fall (fun x : V => fimp (eps x X) (fex (fun y : V => fand (eps y X) (ψ x y)))).
Definition dcTot (X f : V) : pcar F :=
  fall (fun n : V => fimp (eps n vomega) (fex (fun y : V => fand (eps y X) (eps (vop n y) f)))).
Definition dcStart (x0 f : V) : pcar F := eps (vop vempty x0) f.
Definition dcStep (ψ : V -> V -> pcar F) (f : V) : pcar F :=
  fall (fun n : V => fall (fun y : V => fall (fun y' : V =>
     fimp (eps (vop n y) f) (fimp (eps (vop (vsuc n) y') f) (ψ y y'))))).
Definition dcS (X : V) (ψ : V -> V -> pcar F) : pcar F :=
  fimp (dcHyp X ψ) (fall (fun x0 : V => fimp (eps x0 X)
    (fex (fun f : V => fand (dcTot X f) (fand (ccFun F f) (fand (ccSub F X f)
                         (fand (dcStart x0 f) (dcStep ψ f)))))))).

(** Les données du choix dépendant pour X, φ et x₀. *)
Definition AX (X : V) (s : idx X) : pcar F := lbl X s.
Definition P0X (X x0 : V) (s : idx X) : pcar F := veq x0 (sub X s).
Definition RXX (X : V) (ψ : V -> V -> pcar F) (s s' : idx X) : pcar F := ψ (sub X s) (sub X s').

Definition Popr (c a : V) : pmor (Vset F) F :=
  fmor (X := Vset F) (fun z : V => veq c (vop a z))
       (fun z z' E => veq_proper F _ _ _ _ (teq_refl F c) (vop_proper F _ _ _ _ (teq_refl F a) E)).

(** ⌜0⌝ est réalisé, uniformément. *)
Lemma n_pnat0 : exists e, forall φ, φ —[e]→ pnat 0.
Proof.
  eexists. intros φ. cbn. apply n_pair; [|apply f_top].
  apply n_gen. intros a. apply n_gen. intros b. apply n_lam, n_lam. apply n_wk, n_hyp0.
Qed.

(** *** Étape 1 : les hypothèses du schéma donnent celles du tripos *)

Lemma step_hyp : exists e, forall X ψ (Hψ : Rproper F ψ) x0,
  fand (dcHyp X ψ) (eps x0 X) —[e]→ DHyp (AX X) (P0X X x0) (RXX X ψ).
Proof.
  eexists. intros X ψ Hψ x0. apply n_pair; [apply f_snd|].
  apply n_gen. intros s. apply n_lam.
  eapply n_exE.
  { apply (n_app _ (eps (sub X s) X)).
    - apply (n_inst (fun x : V => fimp (eps x X) (fex (fun y : V => fand (eps y X) (ψ x y)))) (sub X s)).
      eapply n_fst. apply n_wk, f_id.
    - apply (n_sub F), n_hyp0. }
  intros y. cbv beta. eapply n_exE; [eapply n_fst; apply n_hyp0|]. intros s'. cbv beta.
  apply (n_exI (fun j => fand (AX X j) (RXX X ψ s j)) s'). unfold AX, RXX. apply n_pair.
  - eapply n_fst; apply n_hyp0.
  - apply (n_leib (CC.Pr F ψ Hψ (sub X s)) y (sub X s')).
    + eapply n_snd; apply n_hyp0.
    + cbn. eapply n_snd. apply n_wk, n_hyp0.
Qed.

(** *** Étape 2 : la suite f ≜ fS X S *)


Lemma step_dtot : exists e, forall X ψ x0 (S : nat -> idx X -> pcar F),
  DPack (AX X) (P0X X x0) (RXX X ψ) S —[e]→ dcTot X (fS X S).
Proof.
  eexists. intros X ψ x0 S. apply n_gen. intros n. apply n_lam.
  eapply n_exE; [apply n_hyp0|]. intros t. cbv beta.
  eapply n_exE.
  { apply (n_app _ (pnat t)).
    - apply (n_inst (fun t => fimp (pnat t) (fex (fun i => S t i))) t). eapply n_fst. apply n_wk, n_wk, f_id.
    - eapply n_fst; apply n_hyp0. }
  intros s. cbv beta.
  apply (n_cut _ (lbl X s)).
  { apply (n_app _ (S t s)); [|apply n_hyp0].
    apply (n_inst (fun i => fimp (S t i) (AX X i)) s).
    apply (n_inst (fun t => fall (fun i => fimp (S t i) (AX X i))) t).
    eapply n_fst; eapply n_snd. apply n_wk, n_wk, n_wk, f_id. }
  apply (n_exI (fun y => fand (eps y X) (eps (vop n y) (fS X S))) (sub X s)). cbv beta.
  apply n_pair.
  - apply (n_sub F), n_hyp0.
  - apply (n_exI (fun p => fand (lbl (fS X S) p) (veq (vop n (sub X s)) (sub (fS X S) p))) (t, s)). cbv beta.
    apply n_pair.
    + apply n_pair; [eapply n_fst; apply n_wk, n_wk, n_hyp0|apply n_wk, n_hyp0].
    + apply (CC.n_veq_conv F _ (vop (snat t) (sub X s))); [apply teq_sym, sub_fS|].
      apply (n_leib (Pop F (vop n (sub X s)) (sub X s)) n (snat t)).
      * apply (CC.n_veq_conv F _ (sub vomega t)); [apply sub_omega|]. eapply n_snd. apply n_wk, n_wk, n_hyp0.
      * cbn. apply n_refl.
Qed.

Lemma step_dfun : exists e, forall X ψ x0 (S : nat -> idx X -> pcar F),
  DPack (AX X) (P0X X x0) (RXX X ψ) S —[e]→ ccFun F (fS X S).
Proof.
  eexists. intros X ψ x0 S. apply n_gen. intros n. apply n_gen. intros y. apply n_gen. intros y'.
  apply n_lam, n_lam.
  eapply n_exE; [apply n_wk, n_hyp0|]. intros [t s]. cbv beta.
  eapply n_exE; [apply n_wk, n_hyp0|]. intros [t' s']. cbv beta.
  eapply n_exE; [apply (n_leib_meta F); eapply n_snd; apply n_wk, n_hyp0|]. intros H1.
  eapply n_exE; [apply (n_leib_meta F); eapply n_snd; apply n_wk, n_hyp0|]. intros H2.
  pose proof (teq_trans F _ _ _ H1 (sub_fS F X S t s)) as K1. apply vop_inj in K1 as [Kn Ky].
  pose proof (teq_trans F _ _ _ H2 (sub_fS F X S t' s')) as K2. apply vop_inj in K2 as [Kn' Ky'].
  assert (Et : t = t') by (apply (snat_inj F); exact (teq_trans F _ _ _ (teq_sym F _ _ Kn) Kn')). subst t'.
  eapply n_exE.
  { apply (n_app _ (fand (S t s) (S t s'))).
    - apply (n_inst (fun i' => fimp (fand (S t s) (S t i')) (fmeta (s = i'))) s').
      apply (n_inst (fun i => fall (fun i' => fimp (fand (S t i) (S t i')) (fmeta (i = i')))) s).
      apply (n_inst (fun t => fall (fun i => fall (fun i' => fimp (fand (S t i) (S t i')) (fmeta (i = i'))))) t).
      eapply n_fst; eapply n_snd; eapply n_snd. apply n_wk, n_wk, n_wk, n_wk, n_wk, n_wk, f_id.
    - apply n_pair.
      + eapply n_snd; eapply n_fst. apply n_wk, n_wk, n_wk, n_hyp0.
      + eapply n_snd; eapply n_fst. apply n_wk, n_wk, n_hyp0. }
  intros Es. subst s'. apply (CC.n_veq_teq F). exact (teq_trans F _ _ _ Ky (teq_sym F _ _ Ky')).
Qed.

Lemma step_dsub : exists e, forall X ψ x0 (S : nat -> idx X -> pcar F),
  DPack (AX X) (P0X X x0) (RXX X ψ) S —[e]→ ccSub F X (fS X S).
Proof.
  eexists. intros X ψ x0 S. apply n_gen. intros z. apply n_lam.
  eapply n_exE; [apply n_hyp0|]. intros [t s]. cbv beta.
  apply (n_cut _ (lbl X s)).
  { apply (n_app _ (S t s)).
    - apply (n_inst (fun i => fimp (S t i) (AX X i)) s).
      apply (n_inst (fun t => fall (fun i => fimp (S t i) (AX X i))) t).
      eapply n_fst; eapply n_snd. apply n_wk, n_wk, f_id.
    - eapply n_snd; eapply n_fst. apply n_hyp0. }
  apply (n_exI (fun n => fand (eps n vomega) (fex (fun y => fand (eps y X) (veq z (vop n y))))) (snat t)).
  cbv beta. apply n_pair.
  - apply (n_omega F). eapply n_fst; eapply n_fst. apply n_wk, n_hyp0.
  - apply (n_exI (fun y => fand (eps y X) (veq z (vop (snat t) y))) (sub X s)). cbv beta. apply n_pair.
    + apply (n_sub F), n_hyp0.
    + apply (CC.n_veq_conv F _ (sub (fS X S) (t, s))); [apply sub_fS|]. eapply n_snd. apply n_wk, n_hyp0.
Qed.

Lemma step_dstart : exists e, forall X ψ x0 (S : nat -> idx X -> pcar F),
  DPack (AX X) (P0X X x0) (RXX X ψ) S —[e]→ dcStart x0 (fS X S).
Proof.
  destruct n_pnat0 as [e0 H0].
  eexists. intros X ψ x0 S.
  eapply n_exE.
  { apply (n_app _ (pnat 0)).
    - apply (n_inst (fun t => fimp (pnat t) (fex (fun i => S t i))) 0). eapply n_fst. apply f_id.
    - apply H0. }
  intros s. cbv beta.
  apply (n_cut _ (veq x0 (sub X s))).
  { apply (n_app _ (S 0 s)); [|apply n_hyp0].
    apply (n_inst (fun i => fimp (S 0 i) (P0X X x0 i)) s).
    eapply n_fst; eapply n_snd; eapply n_snd; eapply n_snd. apply n_wk, f_id. }
  apply (n_exI (fun p => fand (lbl (fS X S) p) (veq (vop vempty x0) (sub (fS X S) p))) (0, s)). cbv beta.
  apply n_pair.
  - apply n_pair; [apply H0|apply n_wk, n_hyp0].
  - apply (CC.n_veq_conv F _ (vop (snat 0) (sub X s))); [apply teq_sym, sub_fS|].
    apply (n_leib (Popr (vop vempty x0) vempty) x0 (sub X s)).
    + apply n_hyp0.
    + cbn. apply n_refl.
Qed.

Lemma step_dstep : exists e, forall X ψ (Hψ : Rproper F ψ) x0 (S : nat -> idx X -> pcar F),
  DPack (AX X) (P0X X x0) (RXX X ψ) S —[e]→ dcStep ψ (fS X S).
Proof.
  eexists. intros X ψ Hψ x0 S. apply n_gen. intros n. apply n_gen. intros y. apply n_gen. intros y'.
  apply n_lam, n_lam.
  eapply n_exE; [apply n_wk, n_hyp0|]. intros [t s]. cbv beta.
  eapply n_exE; [apply n_wk, n_hyp0|]. intros [t' s']. cbv beta.
  eapply n_exE; [apply (n_leib_meta F); eapply n_snd; apply n_wk, n_hyp0|]. intros H1.
  eapply n_exE; [apply (n_leib_meta F); eapply n_snd; apply n_wk, n_hyp0|]. intros H2.
  pose proof (teq_trans F _ _ _ H1 (sub_fS F X S t s)) as K1. apply vop_inj in K1 as [Kn Ky].
  pose proof (teq_trans F _ _ _ H2 (sub_fS F X S t' s')) as K2. apply vop_inj in K2 as [Kn' Ky'].
  assert (Et : t' = Datatypes.S t).
  { apply (snat_inj F). refine (teq_trans F _ _ _ (teq_sym F _ _ Kn') _). cbn.
    exact (vsuc_proper F _ _ Kn). }
  subst t'.
  apply (n_eq _ (ψ (sub X s) (sub X s'))); [exact (Hψ _ _ _ _ (teq_sym F _ _ Ky) (teq_sym F _ _ Ky'))|].
  apply (n_app _ (fand (S t s) (S (Datatypes.S t) s'))).
  - apply (n_inst (fun j => fimp (fand (S t s) (S (Datatypes.S t) j)) (RXX X ψ s j)) s').
    apply (n_inst (fun i => fall (fun j => fimp (fand (S t i) (S (Datatypes.S t) j)) (RXX X ψ i j))) s).
    apply (n_inst (fun t => fall (fun i => fall (fun j => fimp (fand (S t i) (S (Datatypes.S t) j)) (RXX X ψ i j)))) t).
    eapply n_snd; eapply n_snd; eapply n_snd; eapply n_snd.
    apply n_wk, n_wk, n_wk, n_wk, n_wk, n_wk, f_id.
  - apply n_pair.
    + eapply n_snd; eapply n_fst. apply n_wk, n_wk, n_wk, n_hyp0.
    + eapply n_snd; eapply n_fst. apply n_wk, n_wk, n_hyp0.
Qed.

(** *** Le schéma est réalisé *)

Theorem R_dc m : frame_dc m -> exists e, forall X (ψ : V -> V -> pcar F), Rproper F ψ -> ftop —[e]→ dcS X ψ.
Proof.
  intros Hm. destruct step_hyp as [e0 H0], step_dtot as [e1 H1], step_dfun as [e2 H2],
    step_dsub as [e3 H3], step_dstart as [e4 H4], step_dstep as [e5 H5].
  eexists. intros X ψ Hψ. apply n_lam. apply n_gen. intros x0. apply n_lam.
  eapply f_comp; [apply f_pair; [eapply n_snd; apply n_wk, f_id|apply n_hyp0]|].
  eapply f_comp; [apply (H0 X ψ Hψ x0)|].
  eapply f_comp; [apply (Hm (idx X) (AX X) (P0X X x0) (RXX X ψ))|]. apply f_exE. intros S.
  apply (n_exI (fun f => fand (dcTot X f) (fand (ccFun F f) (fand (ccSub F X f)
                           (fand (dcStart x0 f) (dcStep ψ f))))) (fS X S)). cbv beta.
  apply n_pair; [apply H1|]. apply n_pair; [apply H2|]. apply n_pair; [apply H3|].
  apply n_pair; [apply H4|apply H5, Hψ].
Qed.

End DC.
