(** * Déduction naturelle dans un cadre d'évidence

    Les règles s'énoncent sous un contexte φ (une proposition, en pratique
    une conjonction d'hypothèses) : φ —[e]→ ψ se lit « sous φ, e prouve ψ ».
    Les évidences se composent comme des preuves, ce qui permet de
    construire un réalisateur uniforme en laissant Rocq l'inférer
    ([eexists] avant d'introduire les paramètres). *)

From SF.Models Require Import PSet Frame FrameModel.

Section ND.

Context {F : frame}.

Local Notation "φ —[ e ]→ ψ" := (fent (F := F) φ e ψ) (at level 70).

Definition e_app (e1 e2 : fev F) : fev F := e_comp (e_pair e1 e2) e_eval.

Lemma n_app φ A B e1 e2 : φ —[e1]→ fimp A B -> φ —[e2]→ A -> φ —[e_app e1 e2]→ B.
Proof. intros H1 H2. eapply f_comp; [apply f_pair; eassumption|apply f_eval]. Qed.

Lemma n_lam φ A B e : fand φ A —[e]→ B -> φ —[e_lam e]→ fimp A B.
Proof. apply f_lam. Qed.

Lemma n_fst φ A B e : φ —[e]→ fand A B -> φ —[e_comp e e_fst]→ A.
Proof. intros H. eapply f_comp; [exact H|apply f_fst]. Qed.

Lemma n_snd φ A B e : φ —[e]→ fand A B -> φ —[e_comp e e_snd]→ B.
Proof. intros H. eapply f_comp; [exact H|apply f_snd]. Qed.

Lemma n_pair φ A B e1 e2 : φ —[e1]→ A -> φ —[e2]→ B -> φ —[e_pair e1 e2]→ fand A B.
Proof. apply f_pair. Qed.

Lemma n_inst {I} (f : I -> F) i φ e : φ —[e]→ fall f -> φ —[e_comp e e_inst]→ f i.
Proof. intros H. eapply f_comp; [exact H|apply f_inst]. Qed.

Lemma n_gen {I} (f : I -> F) φ e : (forall i, φ —[e]→ f i) -> φ —[e_gen e]→ fall f.
Proof. apply f_gen. Qed.

Lemma n_exI {I} (f : I -> F) i φ e : φ —[e]→ f i -> φ —[e_comp e e_exI]→ fex f.
Proof. intros H. eapply f_comp; [exact H|apply f_exI]. Qed.

Definition e_exE_ctx (e0 e : fev F) : fev F :=
  e_app (e_comp e0 (e_exE (e_lam (e_comp (e_pair e_snd e_fst) e)))) e_id.

(** ∃E sous contexte : la prémisse reçoit φ ∧ f i. *)
Lemma n_exE {I} (f : I -> F) φ χ e0 e :
  φ —[e0]→ fex f -> (forall i, fand φ (f i) —[e]→ χ) -> φ —[e_exE_ctx e0 e]→ χ.
Proof.
  intros H0 H. unfold e_exE_ctx. apply (n_app φ φ χ); [|apply f_id].
  eapply f_comp; [exact H0|]. apply f_exE. intros i. apply f_lam.
  eapply f_comp; [apply f_pair; [apply f_snd|apply f_fst]|apply H].
Qed.

Lemma n_eq φ ψ ψ' e : ψ ≡ ψ' -> φ —[e]→ ψ -> φ —[e]→ ψ'.
Proof. intros E H. exact (fent_eq_r _ _ _ _ E H). Qed.

Lemma n_cut φ A B e1 e2 : φ —[e1]→ A -> fand φ A —[e2]→ B -> φ —[e_comp (e_pair e_id e1) e2]→ B.
Proof. intros H1 H2. eapply f_comp; [apply f_pair; [apply f_id|exact H1]|exact H2]. Qed.

(** Accès aux hypothèses d'un contexte φ₀ ∧ A₁ ∧ … emboîté à gauche. *)
Lemma n_hyp0 φ A : fand φ A —[e_snd]→ A.
Proof. apply f_snd. Qed.
Lemma n_wk φ A B e : φ —[e]→ B -> fand φ A —[e_comp e_fst e]→ B.
Proof. intros H. eapply f_comp; [apply f_fst|exact H]. Qed.

(** *** L'égalité de Leibniz *)

Lemma n_leib {A : pset} (P : pmor A F) (a b : A) φ e1 e2 :
  φ —[e1]→ leib (F := F) a b -> φ —[e2]→ P a -> φ —[e_app (e_comp e1 e_inst) e2]→ P b.
Proof.
  intros H1 H2. apply (n_app φ (P a) (P b)); [|exact H2]. unfold leib in H1.
  exact (n_inst (fun ψ : pmor A F => fimp (ψ a) (ψ b)) P φ e1 H1).
Qed.

Lemma n_refl {A : pset} (a : A) φ : φ —[e_refl F]→ leib (F := F) a a.
Proof. apply f_leib_refl. Qed.

Definition leibL {A : pset} (b : A) : pmor A F :=
  Build_pmor A F (fun z => leib (F := F) z b) (fun z z' E => leib_proper F z z' b b E (peq_refl b)).

Definition e_sym (e : fev F) : fev F := e_app (e_comp e e_inst) (e_refl F).

Lemma n_sym {A : pset} (a b : A) φ e : φ —[e]→ leib (F := F) a b -> φ —[e_sym e]→ leib (F := F) b a.
Proof. intros H. exact (n_leib (leibL a) a b φ e _ H (n_refl a φ)). Qed.

Definition leibR {A : pset} (a : A) : pmor A F :=
  Build_pmor A F (fun z => leib (F := F) a z) (fun z z' E => leib_proper F a a z z' (peq_refl a) E).

Definition e_trans (e1 e2 : fev F) : fev F := e_app (e_comp e2 e_inst) e1.

Lemma n_trans {A : pset} (a b c : A) φ e1 e2 :
  φ —[e1]→ leib (F := F) a b -> φ —[e2]→ leib (F := F) b c -> φ —[e_trans e1 e2]→ leib (F := F) a c.
Proof. intros H1 H2. exact (n_leib (leibR a) b c φ e2 e1 H2 H1). Qed.

End ND.
