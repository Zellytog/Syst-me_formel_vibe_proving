(** * Exemple : l'implication intuitionniste comme théorie brute

    On reprend la signature propositionnelle de [Logic/Examples.v]. La
    théorie brute contient deux règles, ⇒I et ⇒E. Une preuve brute de
    ⊢ A ⇒ (B ⇒ A) est acceptée par le vérificateur (calculé par
    [vm_compute]), et [chk_sound] en fait une dérivation au sens de
    [deriv]. *)

From Stdlib Require Import List.
Import ListNotations.
From SF.Syntax Require Import Spec Terms.
From SF.Calculus Require Import System.
From SF.Logic Require Import Judgment Propositional Examples.
From SF.Checker Require Import Raw Check.

Local Notation ι := (Spec [] Pr).

Definition psort_eq_dec (a b : psort) : {a = b} + {a <> b}.
Proof. decide equality. Defined.

(** ** Signature brute *)

Inductive rp := RImp | RAnd | ROr | RTop | RBot.

Definition rp_eq_dec (a b : rp) : {a = b} + {a <> b}.
Proof. decide equality. Defined.

Definition rp_spec (r : rp) : spec psort :=
  match r with
  | RImp | RAnd | ROr => Spec [ι; ι] Pr
  | RTop | RBot => ι
  end.

Definition rp_sym (r : rp) : psym (rp_spec r) :=
  match r with
  | RImp => s_imp | RAnd => s_and | ROr => s_or | RTop => s_top | RBot => s_bot
  end.

Definition rp_enc {σ} (c : psym σ) : rp :=
  match c with
  | s_imp => RImp | s_and => RAnd | s_or => ROr | s_top => RTop | s_bot => RBot
  end.

Lemma rp_enc_spec σ (c : psym σ) : rp_spec (rp_enc c) = σ.
Proof. destruct c; reflexivity. Defined.

Lemma rp_enc_sym σ (c : psym σ) : eq_rect _ psym (rp_sym (rp_enc c)) _ (rp_enc_spec σ c) = c.
Proof. destruct c; reflexivity. Qed.

(** ** La théorie brute de l'implication *)

Notation rv n := (rvar n rnil).
Definition rimp (a b : rtm rp) : rtm rp := rsym RImp (rcons a (rcons b rnil)).

(** ⇒I : métavariables [φ; ψ] (indices 0 et 1) ; de φ ⊢ ψ, conclure φ ⇒ ψ. *)
Definition r_impI : rrule psort rp :=
  {| rr_ctx := [ι; ι];
     rr_prems := [ {| rp_ext := []; rp_hyps := [rv 0]; rp_goal := rv 1 |} ];
     rr_concl := rimp (rv 0) (rv 1) |}.

(** ⇒E : de φ ⇒ ψ et φ, conclure ψ. *)
Definition r_impE : rrule psort rp :=
  {| rr_ctx := [ι; ι];
     rr_prems := [ {| rp_ext := []; rp_hyps := []; rp_goal := rimp (rv 0) (rv 1) |};
                   {| rp_ext := []; rp_hyps := []; rp_goal := rv 0 |} ];
     rr_concl := rv 1 |}.

Definition imp_theory : list (rrule psort rp) := [r_impI; r_impE].

(** Pas de conversion dans cette théorie : aucun certificat n'est accepté. *)
Definition no_cert (Γ : ctx psort) (_ : unit) (_ _ : form psym Pr Γ) : bool := false.

Lemma no_cert_sound Γ c (φ ψ : form psym Pr Γ) : no_cert Γ c φ ψ = true -> conv triv φ ψ.
Proof. discriminate. Qed.

Notation pchk := (chk psym psort_eq_dec rp rp_spec rp_sym rp_eq_dec (@rp_enc)
                      Pr unit no_cert imp_theory).
Notation IMP := (Rfam psym psort_eq_dec rp rp_spec rp_sym Pr imp_theory).

(** ** Une preuve : ⊢ A ⇒ (B ⇒ A), dans le contexte [A; B; C] *)

Definition rA : rtm rp := rv 0.
Definition rB : rtm rp := rv 1.

Definition K_proof : rproof rp unit :=
  prule 0 (rcons rA (rcons (rimp rB rA) rnil))          (* ⇒I : A ⊢ B ⇒ A *)
    (pcons (prule 0 (rcons rB (rcons rA rnil))           (* ⇒I : B, A ⊢ A *)
              (pcons (pax 1) pnil))
           pnil).

Example K_checked : pchk Γ3 [] (Imp A (Imp B A)) K_proof = true.
Proof. vm_compute. reflexivity. Qed.

Theorem K_deriv : deriv triv Pr IMP Γ3 [] (Imp A (Imp B A)).
Proof.
  eapply (chk_sound psym psort_eq_dec rp rp_spec rp_sym rp_eq_dec (@rp_enc)
            rp_enc_spec rp_enc_sym triv Pr unit no_cert no_cert_sound imp_theory).
  exact K_checked.
Qed.

(** Une preuve fausse est rejetée : on ne peut pas conclure B à partir de A. *)
Example bad_rejected :
  pchk Γ3 [] (Imp A (Imp B B)) K_proof = false.
Proof. vm_compute. reflexivity. Qed.

(** * Exemple du premier ordre : ∀I et ∀E

    Une sorte d'individus D, une sorte de formules ; ∀ est un lieur
    [[D] → P] → P, Q un prédicat unaire. Les règles ∀I (variable propre,
    prémisse qui étend le contexte) et ∀E ont une métavariable d'ordre
    supérieur φ : [D] → P : l'instanciation des prémisses passe par la
    substitution héréditaire. *)

From SF.Calculus Require Import Rules.

Inductive fsort := D | F.

Definition fsort_eq_dec (a b : fsort) : {a = b} + {a <> b}.
Proof. decide equality. Defined.

Local Notation ιD := (Spec [] D).
Local Notation ιF := (Spec [] F).

Inductive fsym : spec fsort -> Type :=
| f_all : fsym (Spec [Spec [ιD] F] F)
| f_imp : fsym (Spec [ιF; ιF] F)
| f_Q : fsym (Spec [ιD] F).

Inductive rf := RAll | RImpF | RQ.

Definition rf_eq_dec (a b : rf) : {a = b} + {a <> b}.
Proof. decide equality. Defined.

Definition rf_spec (r : rf) : spec fsort :=
  match r with
  | RAll => Spec [Spec [ιD] F] F
  | RImpF => Spec [ιF; ιF] F
  | RQ => Spec [ιD] F
  end.

Definition rf_sym (r : rf) : fsym (rf_spec r) :=
  match r with RAll => f_all | RImpF => f_imp | RQ => f_Q end.

Definition rf_enc {σ} (c : fsym σ) : rf :=
  match c with f_all => RAll | f_imp => RImpF | f_Q => RQ end.

Lemma rf_enc_spec σ (c : fsym σ) : rf_spec (rf_enc c) = σ.
Proof. destruct c; reflexivity. Defined.

Lemma rf_enc_sym σ (c : fsym σ) : eq_rect _ fsym (rf_sym (rf_enc c)) _ (rf_enc_spec σ c) = c.
Proof. destruct c; reflexivity. Qed.

Definition ftriv : system fsym := generated (fun e : Empty_set => match e with end).

Definition fall (body : rtm rf) : rtm rf := rsym RAll (rcons body rnil).
Definition fimp (a b : rtm rf) : rtm rf := rsym RImpF (rcons a (rcons b rnil)).
Definition fQ (t : rtm rf) : rtm rf := rsym RQ (rcons t rnil).
Notation fv n := (rvar n rnil).
(** Application d'une métavariable n à un argument. *)
Definition fapp (n : nat) (t : rtm rf) : rtm rf := rvar n (rcons t rnil).

(** ∀I : métavariable φ : [D] → F (indice 0). Prémisse : dans le contexte
    étendu par x : D (indice 0, φ devient l'indice 1), dériver φ(x). *)
Definition r_allI : rrule fsort rf :=
  {| rr_ctx := [Spec [ιD] F];
     rr_prems := [ {| rp_ext := [ιD]; rp_hyps := []; rp_goal := fapp 1 (fv 0) |} ];
     rr_concl := fall (fapp 1 (fv 0)) |}.

(** ∀E : métavariables φ : [D] → F (0) et t : D (1). *)
Definition r_allE : rrule fsort rf :=
  {| rr_ctx := [Spec [ιD] F; ιD];
     rr_prems := [ {| rp_ext := []; rp_hyps := []; rp_goal := fall (fapp 1 (fv 0)) |} ];
     rr_concl := fapp 0 (fv 1) |}.

Definition r_impIF : rrule fsort rf :=
  {| rr_ctx := [ιF; ιF];
     rr_prems := [ {| rp_ext := []; rp_hyps := [fv 0]; rp_goal := fv 1 |} ];
     rr_concl := fimp (fv 0) (fv 1) |}.

Definition fo_theory : list (rrule fsort rf) := [r_allI; r_allE; r_impIF].

Definition no_certF (Γ : ctx fsort) (_ : unit) (_ _ : form fsym F Γ) : bool := false.
Lemma no_certF_sound Γ c (φ ψ : form fsym F Γ) : no_certF Γ c φ ψ = true -> conv ftriv φ ψ.
Proof. discriminate. Qed.

Notation fjudg := (check_judgment fsym fsort_eq_dec rf rf_spec rf_sym rf_eq_dec (@rf_enc)
                     F unit no_certF fo_theory).

(** ⊢ ∀x. Q(x) ⇒ Q(x), dans le contexte vide. Le vecteur de ∀I est le
    corps λx. Q(x) ⇒ Q(x), écrit sous le lieur (x est l'indice 0). *)
Definition refl_proof : rproof rf unit :=
  prule 0 (rcons (fimp (fQ (fv 0)) (fQ (fv 0))) rnil)
    (pcons (prule 2 (rcons (fQ (fv 0)) (rcons (fQ (fv 0)) rnil))
              (pcons (pax 0) pnil))
           pnil).

Example refl_checked : fjudg [] [] (fall (fimp (fQ (fv 0)) (fQ (fv 0)))) refl_proof = true.
Proof. vm_compute. reflexivity. Qed.

(** ∀x. Q(x) ⊢ Q(c), dans le contexte [c : D] : ∀E instancié par
    λx. Q(x) et c. *)
Definition inst_proof : rproof rf unit :=
  prule 1 (rcons (fQ (fv 0)) (rcons (fv 0) rnil)) (pcons (pax 0) pnil).

Example inst_checked : fjudg [ιD] [fall (fQ (fv 0))] (fQ (fv 0)) inst_proof = true.
Proof. vm_compute. reflexivity. Qed.

Theorem inst_deriv : exists Ξ φ,
  elab_forms fsym fsort_eq_dec rf rf_spec rf_sym F [ιD] [fall (fQ (fv 0))] = Some Ξ /\
  elab_form fsym fsort_eq_dec rf rf_spec rf_sym F [ιD] (fQ (fv 0)) = Some φ /\
  deriv ftriv F (Rfam fsym fsort_eq_dec rf rf_spec rf_sym F fo_theory) [ιD] Ξ φ.
Proof.
  eapply (check_judgment_sound fsym fsort_eq_dec rf rf_spec rf_sym rf_eq_dec (@rf_enc)
            rf_enc_spec rf_enc_sym ftriv F unit no_certF no_certF_sound fo_theory).
  exact inst_checked.
Qed.

(** La variable propre est contrôlée : on ne peut pas généraliser une
    hypothèse sur c. Ici, Q(c) ⊢ ∀x. Q(x) est rejeté. *)
Example eigen_rejected :
  fjudg [ιD] [fQ (fv 0)] (fall (fQ (fv 0))) (prule 0 (rcons (fQ (fv 0)) rnil) (pcons (pax 0) pnil)) = false.
Proof. vm_compute. reflexivity. Qed.
