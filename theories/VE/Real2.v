(** * V(E) : réalisation des axiomes des constructions

    Paire, réunion, séparation, vide, parties (faible et IZFε), ω. Chaque
    sens est réalisé par une évidence uniforme ; pour la paire et ω, ce
    sont les étiquettes (booléens de Church) qui choisissent la branche. *)

From SF.Models Require Import PSet Frame FrameModel.
From SF.VE Require Import Trees Base ND Cons.

Section Real2.

Context (F : frame).
Context (Φ0 : Type) (enc : pcar F -> Φ0) (dec : Φ0 -> pcar F).
Context (dec_enc : forall φ, dec (enc φ) ≡ φ).

Local Notation "φ —[ e ]→ ψ" := (fent (F := F) φ e ψ) (at level 70).
Local Notation V := (V F).
Local Notation Vset := (Vset F).
Local Notation idx := (idx F).
Local Notation lbl := (lbl F).
Local Notation sub := (sub F).
Local Notation eps := (eps F).
Local Notation veq := (veq F).
Local Notation tagT := (tagT F).
Local Notation tagF := (tagF F).

Definition Peps (z : V) : pmor Vset F :=
  Build_pmor Vset F (fun b => eps z b) (fun b b' E => eps_proper F z z b b' (teq_refl F z) E).
Definition PepsL (b : V) : pmor Vset F :=
  Build_pmor Vset F (fun z => eps z b) (fun z z' E => eps_proper F z z' b b E (teq_refl F b)).

(** Réaliser les booléens de Church. *)
Lemma n_tagT φ : φ —[e_gen (e_gen (e_lam (e_lam (e_comp e_fst e_snd))))]→ tagT.
Proof.
  apply n_gen; intros A. apply n_gen; intros B. apply n_lam, n_lam. apply n_wk, n_hyp0.
Qed.

Lemma n_tagF φ : φ —[e_gen (e_gen (e_lam (e_lam e_snd)))]→ tagF.
Proof. apply n_gen; intros A. apply n_gen; intros B. apply n_lam, n_lam, n_hyp0. Qed.

(** Sous un contexte qui commence par un booléen, choisir. *)
Lemma n_selT φ A B e : φ —[e]→ tagT -> φ —[e_comp (e_comp e e_inst) e_inst]→ fimp A (fimp B A).
Proof.
  intros H. eapply (n_inst (fun ψ => fimp A (fimp ψ A)) B).
  eapply (n_inst (fun φ0 => fall (fun ψ => fimp φ0 (fimp ψ φ0))) A). exact H.
Qed.

Lemma n_selF φ A B e : φ —[e]→ tagF -> φ —[e_comp (e_comp e e_inst) e_inst]→ fimp A (fimp B B).
Proof.
  intros H. eapply (n_inst (fun ψ => fimp A (fimp ψ ψ)) B).
  eapply (n_inst (fun φ0 => fall (fun ψ => fimp φ0 (fimp ψ ψ))) A). exact H.
Qed.

(** *** ∅ *)

Lemma empty_real : exists e, forall z, eps z (vempty F) —[e]→ fbot.
Proof. exists (e_exE e_id). intros z. apply f_exE. intros []. Qed.

(** *** La paire *)

Lemma pair_to : exists e, forall z x y, eps z (vpair F x y) —[e]→ for_ (veq z x) (veq z y).
Proof.
  eexists. intros z [s l] [r m]. apply f_exE. intros c.
  set (R := for_ (veq z (existT _ s l)) (veq z (existT _ r m))).
  set (A := fimp (veq z (existT _ s l)) R). set (B := fimp (veq z (existT _ r m)) R).
  destruct c.
  - eapply (n_app _ (veq z (existT _ s l)) R); [|apply n_hyp0].
    eapply (n_app _ B A); [eapply (n_app _ A (fimp B A)); [apply n_selT, f_fst|]|].
    + apply n_lam. eapply f_comp; [apply n_hyp0|apply f_inl].
    + apply n_lam. eapply f_comp; [apply n_hyp0|apply f_inr].
  - eapply (n_app _ (veq z (existT _ r m)) R); [|apply n_hyp0].
    eapply (n_app _ B B); [eapply (n_app _ A (fimp B B)); [apply n_selF, f_fst|]|].
    + apply n_lam. eapply f_comp; [apply n_hyp0|apply f_inl].
    + apply n_lam. eapply f_comp; [apply n_hyp0|apply f_inr].
Qed.

Lemma pair_from : exists e, forall z x y, for_ (veq z x) (veq z y) —[e]→ eps z (vpair F x y).
Proof.
  eexists. intros z [s l] [r m]. apply f_case.
  - eapply (n_exI _ true). apply n_pair; [apply n_tagT|apply f_id].
  - eapply (n_exI _ false). apply n_pair; [apply n_tagF|apply f_id].
Qed.

(** *** La réunion *)

Lemma union_to : exists e, forall z x, eps z (vunion F x) —[e]→ fex (fun b : V => fand (eps z b) (eps b x)).
Proof.
  eexists. intros z [s l]. apply f_exE. intros [t u].
  eapply (n_exI (fun b : V => fand (eps z b) (eps b (existT _ s l))) (sub (existT _ s l) t)).
  apply n_pair.
  - eapply (n_exI _ u). apply n_pair; [eapply n_snd, f_fst|apply f_snd].
  - eapply (n_exI _ t). apply n_pair; [eapply n_fst, f_fst|apply n_refl].
Qed.

Lemma union_from : exists e, forall z x, fex (fun b : V => fand (eps z b) (eps b x)) —[e]→ eps z (vunion F x).
Proof.
  eexists. intros z [s l]. apply f_exE. intros b.
  eapply n_exE; [apply f_snd|]. intros t.
  eapply n_exE.
  { eapply (n_leib (Peps z) b (sub (existT _ s l) t)); [eapply n_snd, n_hyp0|]. eapply n_fst, n_wk, f_id. }
  intros u.
  eapply (n_exI _ (existT _ t u)). apply n_pair.
  - apply n_pair; [eapply n_fst, n_snd, n_wk, f_id|eapply n_fst, n_hyp0].
  - eapply n_snd, n_hyp0.
Qed.


(** *** Séparation : α ε {α ε a | φ} ↔ α ε a ∧ φ(α) *)

Lemma sep_to : exists e, forall z a (φ : pmor Vset F), eps z (vsep F a φ) —[e]→ fand (eps z a) (φ z).
Proof.
  eexists. intros z [[T k] l] φ. apply f_exE. intros t.
  apply n_pair.
  - eapply (n_exI _ t). apply n_pair; [eapply n_snd, f_fst|apply f_snd].
  - eapply (n_leib φ (sub (existT _ (node T k) l) t) z); [eapply n_sym, f_snd|]. eapply n_fst, f_fst.
Qed.

Lemma sep_from : exists e, forall z a (φ : pmor Vset F), fand (eps z a) (φ z) —[e]→ eps z (vsep F a φ).
Proof.
  eexists. intros z [[T k] l] φ.
  eapply n_exE; [apply f_fst|]. intros t.
  eapply (n_exI _ t). apply n_pair; [apply n_pair|eapply n_snd, n_hyp0].
  - eapply (n_leib φ z (sub (existT _ (node T k) l) t)); [eapply n_snd, n_hyp0|]. eapply n_snd, n_wk, f_id.
  - eapply n_fst, n_hyp0.
Qed.

(** *** Parties *)

Lemma eps_bsub_to : exists e, forall z x g, eps z (bsub F Φ0 dec x g) —[e]→ eps z x.
Proof.
  eexists. intros z [[T k] l] g. apply f_exE. intros t.
  eapply (n_exI _ t). apply n_pair; [eapply n_snd, f_fst|apply f_snd].
Qed.

(** La partie b_g avec g(t) = enc(xₜ ε a) : z ε b_g ↔ z ε x ∧ z ε a. *)
Definition gpow (x a : V) : idx x -> Φ0 := fun t => enc (eps (sub x t) a).

Lemma bsub_to : exists e, forall z x a, eps z (bsub F Φ0 dec x (gpow x a)) —[e]→ fand (eps z x) (eps z a).
Proof.
  eexists. intros z [[T k] l] a. apply f_exE. intros t.
  apply n_pair.
  - eapply (n_exI _ t). apply n_pair; [eapply n_snd, f_fst|apply f_snd].
  - eapply (n_leib (PepsL a) (sub (existT _ (node T k) l) t) z); [eapply n_sym, f_snd|].
    eapply n_eq; [apply dec_enc|]. eapply n_fst, f_fst.
Qed.

Lemma bsub_from : exists e, forall z x a, fand (eps z x) (eps z a) —[e]→ eps z (bsub F Φ0 dec x (gpow x a)).
Proof.
  eexists. intros z [[T k] l] a.
  eapply n_exE; [apply f_fst|]. intros t.
  eapply (n_exI _ t). apply n_pair; [apply n_pair|eapply n_snd, n_hyp0].
  - eapply n_eq; [apply peq_sym, dec_enc|].
    eapply (n_leib (PepsL a) z (sub (existT _ (node T k) l) t)); [eapply n_snd, n_hyp0|]. eapply n_snd, n_wk, f_id.
  - eapply n_fst, n_hyp0.
Qed.

Lemma bsub_in_power : exists e, forall x g, ftop —[e]→ eps (bsub F Φ0 dec x g) (vpower F Φ0 dec x).
Proof.
  eexists. intros x g. eapply (n_exI _ g). apply n_pair; [apply f_top|apply n_refl].
Qed.

(** {α ε a | φ} ε P(a). *)
Lemma sep_power_real : exists e, forall a (φ : pmor Vset F), ftop —[e]→ eps (vsep F a φ) (vpower F Φ0 dec a).
Proof.
  eexists. intros [s l] φ. eapply (n_exI _ (fun t => enc (φ (sub (existT _ s l) t)))).
  apply n_pair; [apply f_top|].
  eapply n_eq; [apply veq_proper; [|apply teq_refl]|apply n_refl].
  exists eq_refl. cbn. apply rel_proper; [apply leq_refl|]. intros t. exact (dec_enc _).
Qed.

(** a ε P(x) → α ε a → α ε x. *)
Lemma power_sub_real : exists e, forall a x z, fand (eps a (vpower F Φ0 dec x)) (eps z a) —[e]→ eps z x.
Proof.
  destruct eps_bsub_to as [e0 H0].
  eexists. intros a x z.
  eapply n_exE; [apply f_fst|]. intros g.
  eapply f_comp; [|apply (H0 z x g)].
  eapply (n_leib (Peps z) a (bsub F Φ0 dec x g)); [eapply n_snd, n_hyp0|]. eapply n_snd, n_wk, f_id.
Qed.

(** *** ω : a ε ω ↔ a = ∅ ∨ ∃b. b ε ω ∧ a = S(b) *)

Local Notation vomega := (vomega F).
Local Notation snat := (snat F).

Lemma sub_omega n : teq F (sub vomega n) (snat n).
Proof. unfold sub; cbn. destruct (snat n) as [s l]. apply teq_refl. Qed.

Definition Psuc (a : V) : pmor Vset F :=
  Build_pmor Vset F (fun z => veq a (vsuc F z))
             (fun z z' E => veq_proper F a a _ _ (teq_refl F a) (vsuc_proper F z z' E)).

Definition Rom (a : V) : pcar F :=
  for_ (veq a (vempty F)) (fex (fun b : V => fand (eps b vomega) (veq a (vsuc F b)))).

Lemma om_G0 : exists e, forall a φ, φ —[e]→ fimp (fand (pnat F 0) (veq a (sub vomega 0))) (Rom a).
Proof.
  eexists. intros a φ. apply n_lam. eapply f_comp; [|apply f_inl].
  eapply n_eq; [apply veq_proper; [apply teq_refl|apply (sub_omega 0)]|]. eapply n_snd, n_hyp0.
Qed.

Lemma om_GS : exists e, forall a φ m, φ —[e]→ fimp (fand (pnat F (S m)) (veq a (sub vomega (S m)))) (Rom a).
Proof.
  eexists. intros a φ m. apply n_lam. eapply f_comp; [|apply f_inr].
  eapply (n_exI (fun b : V => fand (eps b vomega) (veq a (vsuc F b))) (snat m)). apply n_pair.
  - eapply (n_exI _ m). apply n_pair; [eapply n_snd, n_fst, n_hyp0|].
    eapply n_eq; [apply veq_proper; [apply teq_refl|apply teq_sym, sub_omega]|apply n_refl].
  - eapply n_eq; [apply veq_proper; [apply teq_refl|apply (sub_omega (S m))]|]. eapply n_snd, n_hyp0.
Qed.

Lemma omega_to : exists e, forall a, eps a vomega —[e]→ Rom a.
Proof.
  destruct om_G0 as [g0 G0], om_GS as [gs GS].
  eexists. intros a. apply f_exE. intros n.
  set (A := fimp (fand (pnat F 0) (veq a (sub vomega 0))) (Rom a)).
  set (B := fun m => fimp (fand (pnat F (S m)) (veq a (sub vomega (S m)))) (Rom a)).
  destruct n as [|m].
  - eapply (n_app _ (fand (pnat F 0) (veq a (sub vomega 0))) (Rom a)); [|apply f_id].
    eapply (n_app _ (B 0) A); [eapply (n_app _ A (fimp (B 0) A)); [|apply G0]|apply GS].
    apply n_selT. eapply n_fst. eapply n_fst. apply f_id.
  - eapply (n_app _ (fand (pnat F (S m)) (veq a (sub vomega (S m)))) (Rom a)); [|apply f_id].
    eapply (n_app _ (B m) (B m)); [eapply (n_app _ A (fimp (B m) (B m))); [|apply G0]|apply GS].
    apply n_selF. eapply n_fst. eapply n_fst. apply f_id.
Qed.

Lemma omega_from : exists e, forall a, Rom a —[e]→ eps a vomega.
Proof.
  eexists. intros a. apply f_case.
  - eapply (n_exI _ 0). apply n_pair; [apply n_pair; [apply n_tagT|apply f_top]|].
    eapply n_eq; [apply veq_proper; [apply teq_refl|apply teq_sym, (sub_omega 0)]|apply f_id].
  - apply f_exE. intros b.
    eapply n_exE; [apply f_fst|]. intros n.
    eapply (n_exI _ (S n)). apply n_pair; [apply n_pair; [apply n_tagF|eapply n_fst, n_hyp0]|].
    eapply n_eq; [apply veq_proper; [apply teq_refl|apply teq_sym, (sub_omega (S n))]|].
    eapply (n_leib (Psuc a) b (snat n)).
    + eapply n_eq; [apply veq_proper; [apply teq_refl|apply (sub_omega n)]|]. eapply n_snd, n_hyp0.
    + eapply n_snd, n_wk, f_id.
Qed.

End Real2.
