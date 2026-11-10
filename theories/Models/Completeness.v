(** * Le modèle syntaxique et la complétude

    Pour un système logique L qui contient IPC, on construit le **modèle
    générique** :
    - le calcul est interprété par le foncteur identité de [SynConv] ;
    - la fibre au-dessus de Γ est l'ensemble des formules de Γ, préordonnées
      par la prouvabilité (φ ≤ ψ ssi φ ⊢ ψ), les opérations de Heyting étant
      les connecteurs et la réindexation la substitution ;
    - le prédicat générique est la variable de [ι P].

    L'interprétation d'une formule y est la formule elle-même. Toute règle
    de L y est saine, c'est donc un modèle de L, et un jugement valide dans
    tous les modèles l'est dans celui-ci, donc il est prouvable : c'est la
    **complétude** ([completeness]). *)

From Category Require Import Lib Theory.Category Theory.Functor
  Structure.Terminal Structure.Cartesian Structure.Cartesian.Closed.
From Stdlib Require Import List.
Import ListNotations.
From SF.Syntax Require Import Spec Terms Vectors Syn.
From SF.Calculus Require Import System SynConv.
From SF.Logic Require Import Judgment Propositional.
From SF.Models Require Import Calculus Hyperdoctrine Logic.

Local Notation ι a := (Spec [] a).

Set Default Proof Using "All".

Section Syntactic.
Context {Srt : Type} {Sym : spec Srt -> Type} (L : logic Sym).

Local Notation P := (l_prop Sym L).
Local Notation CS := (l_calc Sym L).
Local Notation R := (l_rules Sym L).
Local Notation form := (form Sym P).
Local Notation "Ξ ⊢ φ" := (deriv CS P R _ Ξ φ) (at level 70).
Local Notation Syn := (SynConv CS).

Context {HI : HasImp Sym P} {HA : HasAnd Sym P} {HO : HasOr Sym P} {HT : HasTop Sym P} {HB : HasBot Sym P}.
Context {HR : Includes R ipc_rules}.

(** Toute famille incluse dans IPC est incluse dans les règles de L. *)
Definition inc_via_ipc {J} (R' : J -> drule Sym P) (H : Includes (ipc_rules (Sym := Sym) (P := P)) R') :
  Includes R R' :=
  {| inc := fun k => @inc _ _ _ _ _ R ipc_rules HR (@inc _ _ _ _ _ ipc_rules R' H k);
     inc_eq := fun k => eq_trans (@inc_eq _ _ _ _ _ R ipc_rules HR _) (@inc_eq _ _ _ _ _ ipc_rules R' H k) |}.
#[local] Existing Instance inc_via_ipc.

Local Tactic Notation "nd" uconstr(t) := eapply t; try typeclasses eauto.
Local Ltac hyp := apply d_ax; simpl; auto.

(** ** La hyperdoctrine syntaxique *)

Lemma syn_trans {Γ} (p q r : form Γ) : [p] ⊢ q -> [q] ⊢ r -> [p] ⊢ r.
Proof.
  intros H1 H2. apply (deriv_cut _ _ _ H1). eapply deriv_weaken; [exact H2|]. intros x [<-|[]]; left; reflexivity.
Qed.

Lemma syn_weak1 {Γ} (p q r : form Γ) : [q] ⊢ r -> [p; q] ⊢ r.
Proof. intros H. eapply deriv_weaken; [exact H|]. intros x [<-|[]]; right; left; reflexivity. Qed.

Definition syn_hd : hyperdoctrine Syn.
Proof.
  refine (@Build_hyperdoctrine Syn
    (fun Γ : obj[Syn] => form Γ)
    (fun (Γ : obj[Syn]) (p q : form Γ) => [p] ⊢ q) _ _
    (fun Γ : obj[Syn] => Top) (fun Γ : obj[Syn] => Bot)
    (fun Γ : obj[Syn] => And) (fun Γ : obj[Syn] => Or) (fun Γ : obj[Syn] => Imp)
    _ _ _ _ _ _ _ _ _
    (fun (X Y : obj[Syn]) (f : X ~{Syn}~> Y) (p : form Y) => vsubst p f)
    _ _ _ _ _ _ _ _ _).
  all: cbn beta.
  - (* refl *) intros Γ p; hyp.
  - (* trans *) intros Γ p q r; apply syn_trans.
  - (* top *) intros Γ p; nd top_I.
  - (* bot *) intros Γ p; nd bot_E; hyp.
  - (* and_l *) intros Γ p q; nd and_E1; hyp.
  - (* and_r *) intros Γ p q; nd and_E2; hyp.
  - (* and_intro *) intros Γ p q r H1 H2; nd and_I; assumption.
  - (* or_l *) intros Γ p q; nd or_I1; hyp.
  - (* or_r *) intros Γ p q; nd or_I2; hyp.
  - (* or_elim *) intros Γ p q r H1 H2.
    refine (or_E CS P R [Or p q] p q r _ _ _); [hyp| |].
    + eapply deriv_weaken; [exact H1|]. intros x [<-|[]]; left; reflexivity.
    + eapply deriv_weaken; [exact H2|]. intros x [<-|[]]; left; reflexivity.
  - (* imp_adj *) intros Γ p q r; split; intros H.
    + nd imp_I. apply (deriv_cut _ _ _ (φ := And r p)); [nd and_I; hyp|].
      eapply deriv_weaken; [exact H|]. intros x [<-|[]]; left; reflexivity.
    + nd imp_E; [|nd and_E2; hyp]. apply (deriv_cut _ _ _ (φ := r)); [nd and_E1; hyp|].
      eapply deriv_weaken; [exact H|]. intros x [<-|[]]; left; reflexivity.
  - (* reidx_proper *) intros X Y f g p Hfg. simpl in Hfg.
    eapply d_conv; [apply conv_subst; [apply conv_refl|exact Hfg]|hyp].
  - (* reidx_mono *) intros X Y f p q H. exact (deriv_subst _ _ _ H X f).
  - (* reidx_id *) intros X p. simpl. rewrite vsubst_vid. split; hyp.
  - (* reidx_comp *) intros X Y Z f g p. simpl. rewrite vsubst_vsubst. split; hyp.
  - (* reidx_top *) intros X Y f. unfold Top. rewrite vsubst_Cst. hyp.
  - (* reidx_bot *) intros X Y f. unfold Bot. rewrite vsubst_Cst. hyp.
  - (* reidx_and *) intros X Y f p q. unfold And. rewrite vsubst_Bin. hyp.
  - (* reidx_or *) intros X Y f p q. unfold Or. rewrite vsubst_Bin. hyp.
  - (* reidx_imp *) intros X Y f p q. unfold Imp. rewrite vsubst_Bin. split; hyp.
Defined.

Definition syn_truth : pred syn_hd (cm_fun (syn_model CS) [ι P]) := mv (Θ := [ι P]) vz.

Local Notation SM := (syn_model CS).

(** Dans le modèle syntaxique, une formule s'interprète par elle-même. *)
Lemma syn_interp {Γ} (φ : form Γ) : interp SM syn_hd syn_truth φ = φ.
Proof.
  unfold interp, syn_truth. change (vsubst (mv (Θ := [ι P]) vz) (hat (S := CS) φ) = φ).
  rewrite vsubst_mvar. reflexivity.
Qed.

Lemma syn_mconj_derivable {Γ} (Ξ : list (form Γ)) : Ξ ⊢ mconj SM syn_hd syn_truth Ξ.
Proof.
  induction Ξ as [|ψ Ξ IH]; cbn [mconj].
  - nd top_I.
  - rewrite syn_interp. nd and_I; [hyp|]. eapply deriv_weaken; [exact IH|]. intros x Hx; right; exact Hx.
Qed.

Lemma syn_mconj_proj {Γ} (Ξ : list (form Γ)) χ : In χ Ξ -> [mconj SM syn_hd syn_truth Ξ] ⊢ χ.
Proof.
  induction Ξ as [|ψ Ξ IH]; [intros []|]. intros [<-|Hin]; cbn [mconj].
  - rewrite syn_interp. nd and_E1; hyp.
  - eapply syn_trans; [nd and_E2; hyp|]. apply IH, Hin.
Qed.

(** Validité syntaxique et prouvabilité coïncident. *)
Lemma syn_valid_iff Γ Ξ φ : mvalid SM syn_hd syn_truth Γ Ξ φ <-> Ξ ⊢ φ.
Proof.
  unfold mvalid. rewrite syn_interp. split; intros H.
  - apply (deriv_cut _ _ _ (syn_mconj_derivable Ξ)). eapply deriv_weaken; [exact H|].
    intros x [<-|[]]; left; reflexivity.
  - apply (deriv_cut_gen _ _ _ H). intros χ Hχ. apply syn_mconj_proj, Hχ.
Qed.

(** Toute règle de L est saine dans le modèle syntaxique. *)
Lemma syn_rules_sound i : mrule_sound SM syn_hd syn_truth (R i).
Proof.
  intros Γ Ξ v Hp. apply syn_valid_iff. apply d_rule. intros p Hin. apply syn_valid_iff, Hp, Hin.
Qed.

Definition syn_lmodel : lmodel L Syn := {|
  lm_calc := SM;
  lm_hd := syn_hd;
  lm_truth := syn_truth;
  lm_rules := syn_rules_sound
|}.

(** ** Complétude *)

Theorem completeness Γ Ξ φ :
  (forall (C : Category) (CT : @Terminal C) (CC : @Cartesian C) (CL : @Closed C CC) (N : lmodel L C),
      mvalid (lm_calc L C N) (lm_hd L C N) (lm_truth L C N) Γ Ξ φ) ->
  provable L Γ Ξ φ.
Proof. intros H. apply syn_valid_iff, (H Syn _ _ _ syn_lmodel). Qed.

(** Correction et complétude ensemble. *)
Corollary sound_complete Γ Ξ φ :
  provable L Γ Ξ φ <->
  (forall (C : Category) (CT : @Terminal C) (CC : @Cartesian C) (CL : @Closed C CC) (N : lmodel L C),
      mvalid (lm_calc L C N) (lm_hd L C N) (lm_truth L C N) Γ Ξ φ).
Proof.
  split; [intros Hd C CT CC CL N; apply lmodel_sound, Hd|apply completeness].
Qed.

End Syntactic.
