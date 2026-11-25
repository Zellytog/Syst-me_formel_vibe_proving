(** * Exemples : la syntaxe brute du λ-calcul

    On instancie [Raw.v] avec la signature du λ-calcul de
    [Syntax/Examples.v] : des symboles bruts [RLam], [RAp], leur codage, et
    l'on vérifie par calcul que des termes bruts s'élaborent (ou non). *)

From Stdlib Require Import List.
Import ListNotations.
From SF.Syntax Require Import Spec Terms Examples.
From SF.Checker Require Import Raw.

Definition lsort_eq_dec (a b : lsort) : {a = b} + {a <> b}.
Proof. decide equality. Defined.

Inductive rl := RLam | RAp.

Definition rl_spec (r : rl) : spec lsort :=
  match r with
  | RLam => Spec [Spec [ι] L] L
  | RAp => Spec [ι; ι] L
  end.

Definition rl_sym (r : rl) : lsym (rl_spec r) :=
  match r with
  | RLam => lam
  | RAp => ap
  end.

Definition rl_enc {σ} (c : lsym σ) : rl :=
  match c with
  | lam => RLam
  | ap => RAp
  end.

Lemma rl_enc_spec σ (c : lsym σ) : rl_spec (rl_enc c) = σ.
Proof. destruct c; reflexivity. Defined.

Lemma rl_enc_sym σ (c : lsym σ) : eq_rect _ lsym (rl_sym (rl_enc c)) _ (rl_enc_spec σ c) = c.
Proof. destruct c; reflexivity. Qed.

Lemma rl_enc_rsym r : rl_enc (rl_sym r) = r.
Proof. destruct r; reflexivity. Qed.

Notation lelab := (elab lsym lsort_eq_dec rl rl_spec rl_sym).
Notation lcheck := (check lsym lsort_eq_dec rl rl_spec rl_sym).
Notation lerase := (erase lsym rl (@rl_enc)).

(** λx. x, en brut : le corps est sous un lieur, la variable 0 est x. *)
Definition r_id : rtm rl := rsym RLam (rcons (rvar 0 rnil) rnil).

Example r_id_ok : lcheck [] r_id L = true.
Proof. vm_compute. reflexivity. Qed.

Example r_id_elab : lelab [] r_id = Some (existT _ L (Lam (v vz))).
Proof. reflexivity. Qed.

(** Une variable libre n'est pas bien formée dans le contexte vide. *)
Example r_free_ko : lcheck [] (rvar 0 rnil) L = false.
Proof. vm_compute. reflexivity. Qed.

(** Mauvaise arité : app appliqué à un seul argument. *)
Example r_arity_ko : lcheck [ι] (rsym RAp (rcons (rvar 0 rnil) rnil)) L = false.
Proof. vm_compute. reflexivity. Qed.

(** Le membre gauche de β, effacé puis réélaboré. *)
Example beta_roundtrip : lelab Ξβ (lerase beta_lhs) = Some (existT _ L beta_lhs).
Proof. apply (elab_erase _ _ _ _ _ _ _ rl_enc_sym). Qed.

Example beta_raw : lerase beta_lhs =
  rsym RAp (rcons (rsym RLam (rcons (rvar 1 (rcons (rvar 0 rnil) rnil)) rnil))
                  (rcons (rvar 1 rnil) rnil)).
Proof. reflexivity. Qed.
