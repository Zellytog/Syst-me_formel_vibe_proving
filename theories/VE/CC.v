(** * Le choix dénombrable dans V(E)

    Si le cadre E valide le choix dénombrable **au niveau du tripos** (une
    relation totale sur les entiers, vus comme les étiquettes ⌜t⌝ de ω, a
    une sous-relation totale et déterminée), alors V(E) réalise le schéma
    borné de IZFε :

      (∀n. n ε ω ⇒ ∃y. y ε X ∧ φ(n, y))
        ⇒ ∃f. (∀n. n ε ω ⇒ ∃y. y ε X ∧ ⟨n, y⟩ ε f ∧ φ(n, y))
            ∧ (∀n y y'. ⟨n, y⟩ ε f ⇒ ⟨n, y'⟩ ε f ⇒ y = y')
            ∧ (∀z. z ε f ⇒ ∃n. n ε ω ∧ ∃y. y ε X ∧ z = ⟨n, y⟩).

    La fonction est f ≜ {⟨sₜ, X(s)⟩ | ⌜t⌝ ∧ S(t, s)}, S étant la sous-relation
    déterminée de R(t, s) ≜ X_s ∧ φ(sₜ, X(s)). La fonctionnalité passe par
    deux faits méta sur les arbres : un couple de Kuratowski détermine ses
    composantes, et sₜ détermine t (par l'appartenance au niveau des
    arbres, sans injectivité des formes, qui demanderait un axiome). *)

From Stdlib Require Import PeanoNat Lia.
From SF.Models Require Import PSet Frame FrameModel.
From SF.VE Require Import Trees Base ND Cons Coll.

Set Default Proof Using "All".

(** ** Faits méta sur les arbres *)

Section Meta.
Context (F : frame).
Local Notation V := (Trees.V F).
Local Notation teq := (teq F).
Local Notation idx := (idx F).
Local Notation sub := (sub F).
Local Notation vpair := (vpair F).

(** L'appartenance au niveau des arbres. *)
Definition tmem (a z : V) : Prop := exists u : idx z, teq (sub z u) a.

Lemma tmem_teq a a' z z' : teq a a' -> teq z z' -> tmem a z -> tmem a' z'.
Proof.
  destruct z as [s l], z' as [s' l']. intros Ha [E H] [u Hu]. cbn in *. destruct E.
  exists u. destruct (teq_br F s l l' u H) as [_ H2].
  exact (teq_trans F _ _ _ (teq_trans F _ _ _ (teq_sym F _ _ H2) Hu) Ha).
Qed.

Lemma tmem_pair x a b : tmem x (vpair a b) <-> teq x a \/ teq x b.
Proof.
  split.
  - intros [[|] Hu]; [left|right]; apply teq_sym; destruct a, b; exact Hu.
  - intros [H|H]; [exists true|exists false]; apply teq_sym; destruct a, b; exact H.
Qed.

Lemma tmem_self_l a b : tmem a (vpair a b).
Proof. apply tmem_pair. left; apply teq_refl. Qed.

Lemma tmem_self_r a b : tmem b (vpair a b).
Proof. apply tmem_pair. right; apply teq_refl. Qed.

Lemma tmem_sing x a : tmem x (vpair a a) -> teq x a.
Proof. intros H. apply tmem_pair in H as [H|H]; exact H. Qed.

Definition vop (a b : V) : V := vpair (vpair a a) (vpair a b).

Lemma vop_proper a a' b b' : teq a a' -> teq b b' -> teq (vop a b) (vop a' b').
Proof.
  intros Ha Hb. unfold vop. apply vpair_proper; apply vpair_proper; assumption.
Qed.

Ltac tsym := apply teq_sym.
Ltac ttr y := apply (teq_trans F _ y).

(** Un couple de Kuratowski détermine ses composantes. *)
Lemma vop_inj a b c d : teq (vop a b) (vop c d) -> teq a c /\ teq b d.
Proof.
  intros H. unfold vop in H.
  assert (HP : teq (vpair a a) (vpair c c) \/ teq (vpair a a) (vpair c d)).
  { apply tmem_pair, (tmem_teq _ _ _ _ (teq_refl F _) H), tmem_self_l. }
  assert (Hac : teq a c).
  { destruct HP as [HP|HP]; tsym; apply tmem_sing;
      apply (tmem_teq c c _ _ (teq_refl F _) (teq_sym F _ _ HP)); [apply tmem_self_l|apply tmem_self_l]. }
  split; [exact Hac|].
  assert (HQ' : teq (vpair c d) (vpair a a) \/ teq (vpair c d) (vpair a b)).
  { apply tmem_pair, (tmem_teq _ _ _ _ (teq_refl F _) (teq_sym F _ _ H)), tmem_self_r. }
  destruct HQ' as [HQ'|HQ'].
  - assert (Hda : teq d a) by (apply tmem_sing, (tmem_teq d d _ _ (teq_refl F _) HQ'), tmem_self_r).
    assert (HQ : teq (vpair a b) (vpair c c) \/ teq (vpair a b) (vpair c d)).
    { apply tmem_pair, (tmem_teq _ _ _ _ (teq_refl F _) H), tmem_self_r. }
    destruct HQ as [HQ|HQ].
    + assert (Hbc : teq b c) by (apply tmem_sing, (tmem_teq b b _ _ (teq_refl F _) HQ), tmem_self_r).
      ttr c; [exact Hbc|]. ttr a; [tsym; exact Hac|tsym; exact Hda].
    + assert (Hba : teq b a).
      { apply tmem_sing. apply (tmem_teq b b _ _ (teq_refl F _) (teq_trans F _ _ _ HQ HQ')). apply tmem_self_r. }
      ttr a; [exact Hba|tsym; exact Hda].
  - assert (Hd : teq d a \/ teq d b) by (apply tmem_pair, (tmem_teq d d _ _ (teq_refl F _) HQ'), tmem_self_r).
    destruct Hd as [Hda|Hdb]; [|tsym; exact Hdb].
    assert (Hb : teq b c \/ teq b d).
    { apply tmem_pair, (tmem_teq b b _ _ (teq_refl F _) (teq_sym F _ _ HQ')), tmem_self_r. }
    destruct Hb as [Hbc|Hbd]; [|exact Hbd].
    ttr c; [exact Hbc|]. ttr a; [tsym; exact Hac|tsym; exact Hda].
Qed.

(** sₜ détermine t : un sous-arbre direct d'une forme n'est pas la forme
    elle-même, et sₖ est un sous-arbre direct de sₙ pour k < n. *)
Definition child (a s : shape) : Prop := exists u : idxS s, subS s u = a.

Lemma child_irrefl s : ~ child s s.
Proof.
  induction s as [T k IH]. intros [u Hu]. cbn in Hu. apply (IH u). rewrite Hu. exists u. exact Hu.
Qed.

Local Notation sh n := (projT1 (snat F n)).

Lemma child_suc n : child (sh n) (sh (S n)).
Proof. exists (existT _ false true). reflexivity. Qed.

Lemma child_suc_mono a n : child a (sh n) -> child a (sh (S n)).
Proof. intros [u Hu]. exists (existT _ true u). exact Hu. Qed.

Lemma child_lt k n : k < n -> child (sh k) (sh n).
Proof.
  induction n as [|n IH]; intros Hk; [inversion Hk|].
  destruct (Nat.eq_dec k n) as [->|Hne]; [apply child_suc|].
  apply child_suc_mono, IH. lia.
Qed.

Lemma snat_inj n m : teq (snat F n) (snat F m) -> n = m.
Proof.
  intros [E _]. destruct (Nat.lt_total n m) as [Hl|[He|Hl]]; [|exact He|].
  - exfalso. pose proof (child_lt n m Hl) as Hc. rewrite <- E in Hc. exact (child_irrefl _ Hc).
  - exfalso. pose proof (child_lt m n Hl) as Hc. rewrite E in Hc. exact (child_irrefl _ Hc).
Qed.

Lemma sub_omega t : teq (sub (vomega F) t) (snat F t).
Proof. unfold vomega, sub. cbn. destruct (snat F t). apply teq_refl. Qed.

End Meta.


(** ** Le choix dénombrable du tripos et sa conséquence dans V(E) *)

Section CC.
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

(** Un fait méta, comme proposition : [P] ≜ ⋁_{p : P} ⊤. *)
Definition fmeta (P : Prop) : pcar F := fex (fun _ : P => ftop).

Lemma fmeta_iff (P Q : Prop) : (P <-> Q) -> fmeta P ≡ fmeta Q.
Proof.
  intros [H1 H2]. unfold fmeta, fex. apply (fall_proper F). intros χ.
  apply (fimp_proper F); [|apply peq_refl]. apply (fallP_proper F). intros ψ.
  split; intros [p Hp]; [exists (H1 p)|exists (H2 p)]; exact Hp.
Qed.

Lemma n_meta (P : Prop) φ : P -> φ —[e_comp e_top e_exI]→ fmeta P.
Proof. intros p. apply (n_exI (fun _ : P => ftop) p). apply f_top. Qed.

(** Le choix dénombrable au niveau du tripos : une relation R totale sur
    les entiers (donnés par les étiquettes ⌜t⌝ de ω) a une sous-relation S
    totale et déterminée, uniformément en I et en R. *)
Definition SPack {I : Type} (R S : nat -> I -> pcar F) : pcar F :=
  fand (fall (fun t : nat => fimp (pnat t) (fex (fun i : I => S t i))))
       (fand (fall (fun t : nat => fall (fun i : I => fimp (S t i) (R t i))))
             (fall (fun t : nat => fall (fun i : I => fall (fun i' : I =>
                fimp (fand (S t i) (S t i')) (fmeta (i = i'))))))).

Definition frame_cc (m : fev F) : Prop :=
  forall (I : Type) (R : nat -> I -> pcar F),
    fall (fun t : nat => fimp (pnat t) (fex (fun i : I => R t i))) —[m]→
    fex (fun S : nat -> I -> pcar F => SPack R S).

(** Le schéma, sous forme sémantique « propre ». *)
Definition ccHyp (X : V) (ψ : V -> V -> pcar F) : pcar F :=
  fall (fun n : V => fimp (eps n vomega) (fex (fun y : V => fand (eps y X) (ψ n y)))).
Definition ccTot (X : V) (ψ : V -> V -> pcar F) (f : V) : pcar F :=
  fall (fun n : V => fimp (eps n vomega)
          (fex (fun y : V => fand (eps y X) (fand (eps (vop n y) f) (ψ n y))))).
Definition ccFun (f : V) : pcar F :=
  fall (fun n : V => fall (fun y : V => fall (fun y' : V =>
     fimp (eps (vop n y) f) (fimp (eps (vop n y') f) (veq y y'))))).
Definition ccSub (X f : V) : pcar F :=
  fall (fun z : V => fimp (eps z f)
     (fex (fun n : V => fand (eps n vomega) (fex (fun y : V => fand (eps y X) (veq z (vop n y))))))).
Definition ccS (X : V) (ψ : V -> V -> pcar F) : pcar F :=
  fimp (ccHyp X ψ) (fex (fun f : V => fand (ccTot X ψ f) (fand (ccFun f) (ccSub X f)))).

(** *** Prédicats propres utilisés pour les transports de Leibniz *)

Definition Pmeta (a : V) : pmor (Vset F) F :=
  fmor (X := Vset F) (fun z : V => fmeta (teq a z))
       (fun z z' E => fmeta_iff _ _ (conj (fun H => teq_trans F _ _ _ H E)
                                         (fun H => teq_trans F _ _ _ H (teq_sym F _ _ E)))).

Definition Pl (ψ : V -> V -> pcar F) (Hψ : Rproper F ψ) (y : V) : pmor (Vset F) F :=
  fmor (X := Vset F) (fun z : V => ψ z y) (fun z z' E => Hψ z z' y y E (teq_refl F y)).

Definition Pr (ψ : V -> V -> pcar F) (Hψ : Rproper F ψ) (x : V) : pmor (Vset F) F :=
  fmor (X := Vset F) (fun z : V => ψ x z) (fun z z' E => Hψ x x z z' (teq_refl F x) E).

Definition Pop (a y : V) : pmor (Vset F) F :=
  fmor (X := Vset F) (fun z : V => veq a (vop z y))
       (fun z z' E => veq_proper F _ _ _ _ (teq_refl F a) (vop_proper F _ _ _ _ E (teq_refl F y))).

Lemma n_veq_teq a b φ : teq a b -> φ —[e_refl F]→ veq a b.
Proof.
  intros H. apply (n_eq _ (veq a a)); [apply (veq_proper F); [apply teq_refl|exact H]|apply n_refl].
Qed.

Lemma n_veq_conv a b b' φ e : teq b b' -> φ —[e]→ veq a b -> φ —[e]→ veq a b'.
Proof. intros H. apply n_eq. apply (veq_proper F); [apply teq_refl|exact H]. Qed.

(** Une égalité de Leibniz donne le fait méta correspondant. *)
Lemma n_leib_meta a b φ e : φ —[e]→ veq a b -> φ —[e_app (e_comp e e_inst) (e_comp e_top e_exI)]→ fmeta (teq a b).
Proof. intros H. exact (n_leib (Pmeta a) a b φ e _ H (n_meta _ φ (teq_refl F a))). Qed.

(** sₜ ε ω, à partir de ⌜t⌝. *)
Lemma n_omega t φ e : φ —[e]→ pnat t -> φ —[e_comp (e_pair e (e_refl F)) e_exI]→ eps (snat t) vomega.
Proof.
  intros H. apply (n_exI (fun u : nat => fand (lbl vomega u) (veq (snat t) (sub vomega u))) t).
  cbv beta. apply n_pair; [exact H|]. apply n_veq_teq. apply teq_sym, sub_omega.
Qed.

(** X(s) ε X, à partir de l'étiquette X_s. *)
Lemma n_sub (X : V) s φ e : φ —[e]→ lbl X s -> φ —[e_comp (e_pair e (e_refl F)) e_exI]→ eps (sub X s) X.
Proof.
  intros H. apply (n_exI (fun u : idx X => fand (lbl X u) (veq (sub X s) (sub X u))) s).
  cbv beta. apply n_pair; [exact H|apply n_refl].
Qed.

(** *** Étape 1 : la totalité de φ donne celle de R(t, s) ≜ X_s ∧ φ(sₜ, X(s)) *)

Definition RX (X : V) (ψ : V -> V -> pcar F) (t : nat) (s : idx X) : pcar F :=
  fand (lbl X s) (ψ (snat t) (sub X s)).

Lemma step_tot : exists e, forall X ψ (Hψ : Rproper F ψ),
  ccHyp X ψ —[e]→ fall (fun t : nat => fimp (pnat t) (fex (fun s : idx X => RX X ψ t s))).
Proof.
  eexists. intros X ψ Hψ. apply n_gen. intros t. apply n_lam.
  eapply n_exE.
  { apply (n_app _ (eps (snat t) vomega)).
    - apply (n_inst (fun n : V => fimp (eps n vomega) (fex (fun y : V => fand (eps y X) (ψ n y)))) (snat t)).
      apply n_wk, f_id.
    - apply n_omega, n_hyp0. }
  intros y. cbv beta. eapply n_exE; [eapply n_fst; apply n_hyp0|]. intros s. cbv beta.
  apply (n_exI (fun s' : idx X => RX X ψ t s') s). unfold RX. apply n_pair.
  - eapply n_fst; apply n_hyp0.
  - apply (n_leib (Pr ψ Hψ (snat t)) y (sub X s)).
    + eapply n_snd; apply n_hyp0.
    + cbn. eapply n_snd. apply n_wk, n_hyp0.
Qed.

(** *** Étape 2 : la fonction f ≜ {⟨sₜ, X(s)⟩ | ⌜t⌝ ∧ S(t, s)} *)

Definition fS (X : V) (S : nat -> idx X -> pcar F) : V :=
  mk F (nat * idx X) (fun p => (fand (pnat (fst p)) (S (fst p) (snd p)), vop (snat (fst p)) (sub X (snd p)))).

Lemma sub_fS X S t s : teq (sub (fS X S) (t, s)) (vop (snat t) (sub X s)).
Proof. apply sub_mk. Qed.

Lemma step_ftot : exists e, forall X ψ (Hψ : Rproper F ψ) (S : nat -> idx X -> pcar F),
  SPack (RX X ψ) S —[e]→ ccTot X ψ (fS X S).
Proof.
  eexists. intros X ψ Hψ S. apply n_gen. intros n. apply n_lam.
  eapply n_exE; [apply n_hyp0|]. intros t. cbv beta.
  eapply n_exE.
  { apply (n_app _ (pnat t)).
    - apply (n_inst (fun t => fimp (pnat t) (fex (fun i => S t i))) t). eapply n_fst. apply n_wk, n_wk, f_id.
    - eapply n_fst; apply n_hyp0. }
  intros s. cbv beta.
  apply (n_cut _ (RX X ψ t s)).
  { apply (n_app _ (S t s)); [|apply n_hyp0].
    apply (n_inst (fun i => fimp (S t i) (RX X ψ t i)) s).
    apply (n_inst (fun t => fall (fun i => fimp (S t i) (RX X ψ t i))) t).
    eapply n_fst; eapply n_snd. apply n_wk, n_wk, n_wk, f_id. }
  apply (n_exI (fun y => fand (eps y X) (fand (eps (vop n y) (fS X S)) (ψ n y))) (sub X s)). cbv beta.
  apply n_pair; [|apply n_pair].
  - apply n_sub. eapply n_fst; apply n_hyp0.
  - apply (n_exI (fun p => fand (lbl (fS X S) p) (veq (vop n (sub X s)) (sub (fS X S) p))) (t, s)). cbv beta.
    apply n_pair.
    + apply n_pair; [eapply n_fst; apply n_wk, n_wk, n_hyp0|apply n_wk, n_hyp0].
    + apply (n_veq_conv _ (vop (snat t) (sub X s))); [apply teq_sym, sub_fS|].
      apply (n_leib (Pop (vop n (sub X s)) (sub X s)) n (snat t)).
      * apply (n_veq_conv _ (sub vomega t)); [apply sub_omega|]. eapply n_snd. apply n_wk, n_wk, n_hyp0.
      * cbn. apply n_refl.
  - apply (n_leib (Pl ψ Hψ (sub X s)) (snat t) n).
    + apply n_sym. apply (n_veq_conv _ (sub vomega t)); [apply sub_omega|]. eapply n_snd. apply n_wk, n_wk, n_hyp0.
    + cbn. eapply n_snd; apply n_hyp0.
Qed.

Lemma step_ffun : exists e, forall X ψ (Hψ : Rproper F ψ) (S : nat -> idx X -> pcar F),
  SPack (RX X ψ) S —[e]→ ccFun (fS X S).
Proof.
  eexists. intros X ψ Hψ S. apply n_gen. intros n. apply n_gen. intros y. apply n_gen. intros y'.
  apply n_lam, n_lam.
  eapply n_exE; [apply n_wk, n_hyp0|]. intros [t s]. cbv beta.
  eapply n_exE; [apply n_wk, n_hyp0|]. intros [t' s']. cbv beta.
  eapply n_exE; [apply n_leib_meta; eapply n_snd; apply n_wk, n_hyp0|]. intros H1.
  eapply n_exE; [apply n_leib_meta; eapply n_snd; apply n_wk, n_hyp0|]. intros H2.
  pose proof (teq_trans F _ _ _ H1 (sub_fS X S t s)) as K1. apply vop_inj in K1 as [Kn Ky].
  pose proof (teq_trans F _ _ _ H2 (sub_fS X S t' s')) as K2. apply vop_inj in K2 as [Kn' Ky'].
  assert (Et : t = t') by (apply (snat_inj F); exact (teq_trans F _ _ _ (teq_sym F _ _ Kn) Kn')). subst t'.
  eapply n_exE.
  { apply (n_app _ (fand (S t s) (S t s'))).
    - apply (n_inst (fun i' => fimp (fand (S t s) (S t i')) (fmeta (s = i'))) s').
      apply (n_inst (fun i => fall (fun i' => fimp (fand (S t i) (S t i')) (fmeta (i = i')))) s).
      apply (n_inst (fun t => fall (fun i => fall (fun i' => fimp (fand (S t i) (S t i')) (fmeta (i = i'))))) t).
      eapply n_snd; eapply n_snd. apply n_wk, n_wk, n_wk, n_wk, n_wk, n_wk, f_id.
    - apply n_pair.
      + eapply n_snd; eapply n_fst. apply n_wk, n_wk, n_wk, n_hyp0.
      + eapply n_snd; eapply n_fst. apply n_wk, n_wk, n_hyp0. }
  intros Es. subst s'. apply n_veq_teq. exact (teq_trans F _ _ _ Ky (teq_sym F _ _ Ky')).
Qed.

Lemma step_fsub : exists e, forall X ψ (Hψ : Rproper F ψ) (S : nat -> idx X -> pcar F),
  SPack (RX X ψ) S —[e]→ ccSub X (fS X S).
Proof.
  eexists. intros X ψ Hψ S. apply n_gen. intros z. apply n_lam.
  eapply n_exE; [apply n_hyp0|]. intros [t s]. cbv beta.
  apply (n_cut _ (RX X ψ t s)).
  { apply (n_app _ (S t s)).
    - apply (n_inst (fun i => fimp (S t i) (RX X ψ t i)) s).
      apply (n_inst (fun t => fall (fun i => fimp (S t i) (RX X ψ t i))) t).
      eapply n_fst; eapply n_snd. apply n_wk, n_wk, f_id.
    - eapply n_snd; eapply n_fst. apply n_hyp0. }
  apply (n_exI (fun n => fand (eps n vomega) (fex (fun y => fand (eps y X) (veq z (vop n y))))) (snat t)).
  cbv beta. apply n_pair.
  - apply n_omega. eapply n_fst; eapply n_fst. apply n_wk, n_hyp0.
  - apply (n_exI (fun y => fand (eps y X) (veq z (vop (snat t) y))) (sub X s)). cbv beta. apply n_pair.
    + apply n_sub. eapply n_fst; apply n_hyp0.
    + apply (n_veq_conv _ (sub (fS X S) (t, s))); [apply sub_fS|]. eapply n_snd. apply n_wk, n_hyp0.
Qed.

(** *** Le schéma est réalisé *)

Theorem R_cc m : frame_cc m -> exists e, forall X (ψ : V -> V -> pcar F), Rproper F ψ -> ftop —[e]→ ccS X ψ.
Proof.
  intros Hm. destruct step_tot as [e1 H1], step_ftot as [e2 H2], step_ffun as [e3 H3], step_fsub as [e4 H4].
  eexists. intros X ψ Hψ. apply n_lam. eapply f_comp; [apply f_snd|]. eapply f_comp; [apply (H1 X ψ Hψ)|].
  eapply f_comp; [apply (Hm (idx X) (RX X ψ))|]. apply f_exE. intros S.
  apply (n_exI (fun f => fand (ccTot X ψ f) (fand (ccFun f) (ccSub X f))) (fS X S)). cbv beta.
  apply n_pair; [apply H2, Hψ|apply n_pair; [apply H3, Hψ|apply H4, Hψ]].
Qed.

End CC.
