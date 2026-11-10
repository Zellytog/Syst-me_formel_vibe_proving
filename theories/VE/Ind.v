(** * V(E) : l'ε-induction

    Le réalisateur de la régularité est un point fixe (correction A.4) :
    on suppose un **combinateur de point fixe** pour l'opérade engendrée
    par les évidences du cadre (déf. 2.1.2), c'est-à-dire pour les
    fonctions E → E données par une expression [eexp] à une variable. *)

From SF.Models Require Import PSet Frame FrameModel.
From SF.VE Require Import Trees Base ND.

Section Ind.

Context (F : frame).

Local Notation "φ —[ e ]→ ψ" := (fent (F := F) φ e ψ) (at level 70).

(** ** L'opérade des évidences *)

Inductive eexp : Type :=
| ex_var | ex_cst (e : fev F) | ex_id | ex_comp (a b : eexp) | ex_top | ex_fst | ex_snd
| ex_pair (a b : eexp) | ex_lam (a : eexp) | ex_eval | ex_gen (a : eexp) | ex_inst.

Fixpoint eeval (t : fev F) (a : eexp) : fev F :=
  match a with
  | ex_var => t
  | ex_cst e => e
  | ex_id => e_id
  | ex_comp a b => e_comp (eeval t a) (eeval t b)
  | ex_top => e_top
  | ex_fst => e_fst
  | ex_snd => e_snd
  | ex_pair a b => e_pair (eeval t a) (eeval t b)
  | ex_lam a => e_lam (eeval t a)
  | ex_eval => e_eval
  | ex_gen a => e_gen (eeval t a)
  | ex_inst => e_inst
  end.

(** Le combinateur de point fixe (déf. 2.1.2). *)
Context (yfix : eexp -> fev F).
Context (yfix_spec : forall a φ ψ, φ —[eeval (yfix a) a]→ ψ -> φ —[yfix a]→ ψ).

(** ** Le pas de la récurrence *)

Definition Hind (φ : pmor (Vset F) F) : pcar F :=
  fall (fun a : V F => fimp (fall (fun b : V F => fimp (eps F b a) (φ b))) (φ a)).

Definition step (t : fev F) : fev F :=
  e_app (e_comp e_id e_inst)
    (e_gen (e_lam (e_exE_ctx e_snd
       (e_app (e_comp (e_sym (e_comp e_snd e_snd)) e_inst) (e_comp (e_comp (e_comp e_fst e_id) e_fst) t))))).

Lemma ind_step t (φ : pmor (Vset F) F) a :
  (forall u, Hind φ —[t]→ φ (sub F a u)) -> Hind φ —[step t]→ φ a.
Proof.
  intros IH. unfold step.
  eapply n_app; [eapply (n_inst (fun a : V F => fimp (fall (fun b : V F => fimp (eps F b a) (φ b))) (φ a)) a); apply f_id|].
  apply n_gen. intros b. apply n_lam.
  eapply n_exE; [apply n_hyp0|]. intros u.
  eapply (n_leib φ (sub F a u) b); [eapply n_sym, n_snd, n_hyp0|].
  eapply f_comp; [|apply IH]. eapply n_fst, n_wk, f_id.
Qed.

(** Le pas, comme expression de l'opérade. *)
Definition x_app (a b : eexp) : eexp := ex_comp (ex_pair a b) ex_eval.
Definition x_exE (a : eexp) : eexp := ex_comp (ex_pair ex_inst (ex_comp ex_top (ex_gen (ex_lam (ex_comp ex_snd a))))) ex_eval.
Definition x_exE_ctx (a0 a : eexp) : eexp := x_app (ex_comp a0 (x_exE (ex_lam (ex_comp (ex_pair ex_snd ex_fst) a)))) ex_id.
Definition x_refl : eexp := ex_gen (ex_lam ex_snd).
Definition x_sym (a : eexp) : eexp := x_app (ex_comp a ex_inst) x_refl.

Definition x_step : eexp :=
  x_app (ex_comp ex_id ex_inst)
    (ex_gen (ex_lam (x_exE_ctx ex_snd
       (x_app (ex_comp (x_sym (ex_comp ex_snd ex_snd)) ex_inst) (ex_comp (ex_comp (ex_comp ex_fst ex_id) ex_fst) ex_var))))).

Lemma eeval_step t : eeval t x_step = step t.
Proof. reflexivity. Qed.

(** ** La régularité *)

Definition yind : fev F := yfix x_step.

Lemma yind_spec (φ : pmor (Vset F) F) : forall a : V F, Hind φ —[yind]→ φ a.
Proof.
  intros [s l]. revert l. induction s as [T k IH]; intros l.
  apply yfix_spec. rewrite eeval_step. apply ind_step. intros u. apply IH.
Qed.

(** (∀a. (∀b. b ε a → φ(b)) → φ(a)) → ∀a. φ(a), réalisé uniformément en φ. *)
Lemma ind_real : exists e, forall φ : pmor (Vset F) F, ftop —[e]→ fimp (Hind φ) (fall (fun a : V F => φ a)).
Proof.
  eexists. intros φ. apply n_lam. apply n_gen. intros a. eapply f_comp; [apply f_snd|apply yind_spec].
Qed.

End Ind.
