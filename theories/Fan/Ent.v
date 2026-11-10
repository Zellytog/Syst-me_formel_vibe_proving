(** * Entailments uniformes dans un cadre d'évidence

    [ENT Γ Δ] : une même évidence réalise Γ(x) ≤ Δ(x) pour tous les
    paramètres x. C'est la forme de toutes les constructions de la preuve
    de FT : chaque réalisateur est uniforme en les objets méta (prédicat B,
    fonctionnelle F, entier n, chemin α…), seule sa *correction* en dépend.

    Les règles forment une petite logique interne : identité, coupure, ⊤,
    ∧, ⇒ (λ et application), ⋀ (généralisation, instanciation), ∃
    (introduction, élimination avec contexte), réindexation, et la vérité
    méta [P] := ⋁_{p : P} ⊤ ([fprop_of]), qui transporte un fait de la
    méta-théorie sans contenu calculatoire. *)

From SF.Models Require Import PSet Frame.

Section Ent.

Context {F : frame}.

Local Notation Φ := (pcar (fprop F)).
Local Notation "φ —[ e ]→ ψ" := (fent (F := F) φ e ψ) (at level 70).

Definition ENT {X : Type} (Γ Δ : X -> Φ) : Prop := exists e, forall x, Γ x —[e]→ Δ x.

(** La vérité méta. *)
Definition fprop_of (P : Prop) : Φ := fex (fun _ : P => ftop).

Section Rules.
Context {X : Type}.
Implicit Types Γ Δ A B C : X -> Φ.

Lemma ent_refl Γ : ENT Γ Γ.
Proof. exists e_id. intros x. apply f_id. Qed.

Lemma ent_trans Γ Δ C : ENT Γ Δ -> ENT Δ C -> ENT Γ C.
Proof. intros [e1 H1] [e2 H2]. exists (e_comp e1 e2). intros x. eapply f_comp; [apply H1|apply H2]. Qed.

Lemma ent_eq_r Γ Δ Δ' : (forall x, Δ x ≡ Δ' x) -> ENT Γ Δ -> ENT Γ Δ'.
Proof. intros E [e H]. exists e. intros x. apply (fent_eq_r _ _ _ _ (E x)), H. Qed.

Lemma ent_eq_l Γ Γ' Δ : (forall x, Γ x ≡ Γ' x) -> ENT Γ Δ -> ENT Γ' Δ.
Proof. intros E [e H]. exists e. intros x. apply (fent_eq _ _ _ _ (E x)), H. Qed.

Lemma ent_top Γ : ENT Γ (fun _ => ftop).
Proof. exists e_top. intros x. apply f_top. Qed.

Lemma ent_pair Γ A B : ENT Γ A -> ENT Γ B -> ENT Γ (fun x => fand (A x) (B x)).
Proof. intros [e1 H1] [e2 H2]. exists (e_pair e1 e2). intros x. apply f_pair; auto. Qed.

Lemma ent_fst A B : ENT (fun x => fand (A x) (B x)) A.
Proof. exists e_fst. intros x. apply f_fst. Qed.

Lemma ent_snd A B : ENT (fun x => fand (A x) (B x)) B.
Proof. exists e_snd. intros x. apply f_snd. Qed.

Lemma ent_fst' Γ A B : ENT Γ (fun x => fand (A x) (B x)) -> ENT Γ A.
Proof. intros H. eapply ent_trans; [exact H|apply ent_fst]. Qed.

Lemma ent_snd' Γ A B : ENT Γ (fun x => fand (A x) (B x)) -> ENT Γ B.
Proof. intros H. eapply ent_trans; [exact H|apply ent_snd]. Qed.

Lemma ent_lam Γ A B : ENT (fun x => fand (Γ x) (A x)) B -> ENT Γ (fun x => fimp (A x) (B x)).
Proof. intros [e H]. exists (e_lam e). intros x. apply f_lam, H. Qed.

Lemma ent_app Γ A B : ENT Γ (fun x => fimp (A x) (B x)) -> ENT Γ A -> ENT Γ B.
Proof.
  intros [e1 H1] [e2 H2]. exists (e_comp (e_pair e1 e2) e_eval). intros x.
  eapply f_comp; [apply f_pair; [apply H1|apply H2]|apply f_eval].
Qed.

(** Composer à gauche par une fonction de contexte. *)
Lemma ent_cut Γ A B : ENT Γ A -> ENT A B -> ENT Γ B.
Proof. apply ent_trans. Qed.

(** Réindexation le long d'une fonction des paramètres. *)
Lemma ent_reindex {Y} (h : Y -> X) Γ Δ : ENT Γ Δ -> ENT (fun y => Γ (h y)) (fun y => Δ (h y)).
Proof. intros [e H]. exists e. intros y. apply H. Qed.

(** ⋀ : généralisation (le paramètre i s'ajoute aux paramètres). *)
Lemma ent_gen {I : Type} Γ (f : X -> I -> Φ) :
  ENT (fun p : X * I => Γ (fst p)) (fun p => f (fst p) (snd p)) -> ENT Γ (fun x => fall (f x)).
Proof.
  intros [e H]. exists (e_gen e). intros x. apply f_gen. intros i. exact (H (x, i)).
Qed.

Lemma ent_inst {I : Type} Γ (f : X -> I -> Φ) (i : X -> I) :
  ENT Γ (fun x => fall (f x)) -> ENT Γ (fun x => f x (i x)).
Proof.
  intros [e H]. exists (e_comp e e_inst). intros x. eapply f_comp; [apply H|].
  apply (f_inst F _ (f x) (i x)).
Qed.

(** ∃ : introduction. *)
Lemma ent_exI {I : Type} Γ (f : X -> I -> Φ) (i : X -> I) :
  ENT Γ (fun x => f x (i x)) -> ENT Γ (fun x => fex (f x)).
Proof.
  intros [e H]. exists (e_comp e e_exI). intros x. eapply f_comp; [apply H|].
  apply (f_exI _ (f x) (i x)).
Qed.

End Rules.

(** ∃ : élimination, avec contexte (Frobenius). *)
Lemma ent_exE {X I : Type} (Γ : X -> Φ) (f : X -> I -> Φ) (ψ : X -> Φ) :
  ENT (fun p : X * I => fand (Γ (fst p)) (f (fst p) (snd p))) (fun p => ψ (fst p)) ->
  ENT (fun x => fand (Γ x) (fex (f x))) ψ.
Proof.
  intros H.
  (* ∃ᵢ f ≤ Γ ⊃ ψ, puis on décurryfie. *)
  assert (K : ENT (fun x => fex (f x)) (fun x => fimp (Γ x) (ψ x))).
  { destruct H as [e He]. exists (e_exE (e_lam (e_comp (e_pair e_snd e_fst) e))). intros x.
    apply f_exE. intros i. apply f_lam. eapply f_comp; [apply f_pair; [apply f_snd|apply f_fst]|].
    exact (He (x, i)). }
  eapply ent_app.
  - eapply ent_trans; [apply ent_snd|exact K].
  - apply ent_fst.
Qed.

(** Élimination d'une vérité méta : on peut alors supposer P. *)
Lemma ent_meta_elim {X : Type} (P : X -> Prop) (Γ ψ : X -> Φ) :
  ENT (fun p : { x | P x } => Γ (proj1_sig p)) (fun p => ψ (proj1_sig p)) ->
  ENT (fun x => fand (Γ x) (fprop_of (P x))) ψ.
Proof.
  intros [e H].
  assert (K : ENT (fun x => fprop_of (P x)) (fun x => fimp (Γ x) (ψ x))).
  { exists (e_exE (e_lam (e_comp e_snd e))). intros x.
    apply f_exE. intros p. apply f_lam. eapply f_comp; [apply f_snd|]. exact (H (exist _ x p)). }
  eapply ent_app.
  - eapply ent_trans; [apply ent_snd|exact K].
  - apply ent_fst.
Qed.

Lemma ent_meta_intro {X : Type} (P : X -> Prop) (Γ : X -> Φ) :
  (forall x, P x) -> ENT Γ (fun x => fprop_of (P x)).
Proof.
  intros HP. exists (e_comp e_top e_exI). intros x. eapply f_comp; [apply f_top|].
  apply (f_exI _ (fun _ : P x => ftop) (HP x)).
Qed.

Lemma ent_meta_map {X : Type} (P Q : X -> Prop) :
  (forall x, P x -> Q x) -> ENT (fun x => fprop_of (P x)) (fun x => fprop_of (Q x)).
Proof.
  intros HPQ. exists (e_exE e_exI). intros x. apply f_exE. intros p.
  apply (f_exI _ (fun _ : Q x => ftop) (HPQ x p)).
Qed.

End Ent.
