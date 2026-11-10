(** * V(E) : réalisation des axiomes de ∈, ⊆, ≃

    Avec les formes bornées de [Base.v], les axiomes de définition de ∈, ⊆
    et ≃ (déf. 1.3.2) valent à équivalence uniforme près : chaque sens est
    réalisé par une évidence indépendante des ensembles. *)

From SF.Models Require Import PSet Frame FrameModel.
From SF.VE Require Import Trees Base ND.

Section Real1.

Context (F : frame).

Local Notation "φ —[ e ]→ ψ" := (fent (F := F) φ e ψ) (at level 70).
Local Notation V := (V F).
Local Notation Vset := (Vset F).
Local Notation idx := (idx F).
Local Notation lbl := (lbl F).
Local Notation sub := (sub F).
Local Notation eps := (eps F).
Local Notation veq := (veq F).
Local Notation vmem := (vmem F).
Local Notation vsub := (vsub F).
Local Notation veqv := (veqv F).

Definition Pmem (y : V) : pmor Vset F :=
  Build_pmor Vset F (fun z => vmem z y) (fun z z' E => vmem_proper F z z' y y E (teq_refl F y)).
Definition Peqv (x : V) : pmor Vset F :=
  Build_pmor Vset F (fun z => veqv x z) (fun z z' E => veqv_proper F x x z z' (teq_refl F x) E).

(** x ∈ y → ∃a. x ≃ a ∧ a ε y. *)
Lemma mem_to : exists e, forall x y, vmem x y —[e]→ fex (fun a : V => fand (veqv x a) (eps a y)).
Proof.
  eexists. intros x y. apply f_exE. intros u.
  eapply (n_exI (fun a : V => fand (veqv x a) (eps a y)) (sub y u)).
  apply n_pair; [apply n_hyp0|].
  eapply (n_exI (fun t => fand (lbl y t) (veq (sub y u) (sub y t))) u).
  apply n_pair; [apply f_fst|apply n_refl].
Qed.

(** ∃a. x ≃ a ∧ a ε y → x ∈ y. *)
Lemma mem_from : exists e, forall x y, fex (fun a : V => fand (veqv x a) (eps a y)) —[e]→ vmem x y.
Proof.
  eexists. intros x y. apply f_exE. intros a.
  eapply n_exE; [apply n_hyp0|]. intros u.
  eapply (n_exI (fun t => fand (lbl y t) (veqv x (sub y t))) u).
  apply n_pair; [eapply n_fst; apply n_hyp0|].
  eapply (n_leib (Peqv x) a (sub y u)); [eapply n_snd; apply n_hyp0|].
  eapply n_fst. apply n_wk, f_id.
Qed.

(** x ⊆ y → ∀a. a ε x → a ∈ y. *)
Lemma sub_to : exists e, forall x y, vsub x y —[e]→ fall (fun a : V => fimp (eps a x) (vmem a y)).
Proof.
  eexists. intros x y. eapply f_comp; [apply fent_of_eq, vsub_unfold|].
  apply n_gen. intros a. apply n_lam.
  eapply n_exE; [apply n_hyp0|]. intros t.
  eapply (n_leib (Pmem y) (sub x t) a); [eapply n_sym; eapply n_snd; apply n_hyp0|].
  eapply n_app; [|eapply n_fst; apply n_hyp0].
  eapply (n_inst (fun t : idx x => fimp (lbl x t) (vmem (sub x t) y)) t).
  apply n_wk, n_wk, f_id.
Qed.

(** (∀a. a ε x → a ∈ y) → x ⊆ y. *)
Lemma sub_from : exists e, forall x y, fall (fun a : V => fimp (eps a x) (vmem a y)) —[e]→ vsub x y.
Proof.
  eexists. intros x y. eapply f_comp; [|apply fent_of_eq, peq_sym, vsub_unfold].
  apply n_gen. intros t. apply n_lam.
  eapply n_app; [eapply (n_inst (fun a : V => fimp (eps a x) (vmem a y)) (sub x t)); apply n_wk, f_id|].
  eapply (n_exI (fun u => fand (lbl x u) (veq (sub x t) (sub x u))) t).
  apply n_pair; [apply n_hyp0|apply n_refl].
Qed.

End Real1.
