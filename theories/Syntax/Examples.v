(** * Exemples : le λ-calcul comme signature, règle β et substitution héréditaire *)

From Stdlib Require Import List.
Import ListNotations.
From SF.Syntax Require Import Spec Terms Renaming Traversal Eta Composition Vectors.

(** ** Signature du λ-calcul : une sorte L, deux symboles

      lambda ∈ Symb([[L] -> L] -> L)      app ∈ Symb([L, L] -> L)  *)

Inductive lsort := L.

(** Spécification d'une variable ordinaire de sorte L : [] -> L. *)
Notation ι := (Spec [] L).

Inductive lsym : spec lsort -> Type :=
| lam : lsym (Spec [Spec [ι] L] L)
| ap  : lsym (Spec [ι; ι] L).

Definition Λsig : signature := {| srt := lsort; sym := lsym |}.

Notation term := (tm lsym).

Definition v {Γ} (x : var Γ ι) : term Γ L := tvar x anil.
Definition Lam {Γ} (b : term (ι :: Γ) L) : term Γ L := tsym lam (acons (σ := Spec [ι] L) b anil).
Definition App {Γ} (t u : term Γ L) : term Γ L :=
  tsym ap (acons (σ := ι) t (acons (σ := ι) u anil)).

(** ** La règle β, écrite dans un contexte de métavariables

    Ξ = [t : [L] -> L ; u : L]
    app(lambda(x. t(x)), u)  ~  t(u)

    Le membre droit [t(u)] est une simple variable appliquée : c'est la
    substitution héréditaire qui calcule le contractum à l'instanciation. *)

Definition Ξβ : ctx lsort := [Spec [ι] L; ι].

Definition beta_lhs : term Ξβ L :=
  App (Lam (tvar (σ := Spec [ι] L) (vs vz) (acons (σ := ι) (v vz) anil))) (v (vs vz)).

Definition beta_rhs : term Ξβ L :=
  tvar (σ := Spec [ι] L) vz (acons (σ := ι) (v (vs vz)) anil).

(** Instanciation par le vecteur [t := (x. x x) ; u := y], dans Γ = [y : L].
    Un vecteur est littéralement une liste d'arguments. *)
Definition inst_beta : vec lsym Ξβ [ι] :=
  acons (σ := Spec [ι] L) (App (v vz) (v vz)) (acons (σ := ι) (v vz) anil).

Example beta_instance_rhs : vsubst beta_rhs inst_beta = App (v vz) (v vz).
Proof. reflexivity. Qed.

Example beta_instance_lhs :
  vsubst beta_lhs inst_beta = App (Lam (App (v vz) (v vz))) (v vz).
Proof. reflexivity. Qed.

(** ** Une substitution réellement héréditaire

    F est une variable de spécification [[L] -> L] -> L. On remplace F par
    le corps (f. f(c)) : chaque occurrence F(x. b) devient f(c)[f := x. b],
    ce qui crée un nouveau rédex, contracté immédiatement en b[x := c]. *)

Definition ΓF : ctx lsort := [Spec [Spec [ι] L] L; ι].   (* F, c *)

Definition F_applied : term ΓF L :=   (* F(x. x x) *)
  tvar (σ := Spec [Spec [ι] L] L) vz (acons (σ := Spec [ι] L) (App (v vz) (v vz)) anil).

Definition inst_F : vec lsym ΓF [ι] :=
  acons (σ := Spec [Spec [ι] L] L)
        (tvar (σ := Spec [ι] L) vz (acons (σ := ι) (v (vs vz)) anil))   (* F := f. f(c) *)
        (acons (σ := ι) (v vz) anil).                                  (* c := c *)

Example hereditary : vsubst F_applied inst_F = App (v vz) (v vz).   (* c c *)
Proof. reflexivity. Qed.

(** ** Les lois générales, sur cet exemple *)

Example vid_example : vsubst beta_lhs (vid Ξβ) = beta_lhs.
Proof. asimpl. Qed.

Example assoc_example (θ : vec lsym [ι] [ι]) :
  vsubst (vsubst beta_rhs inst_beta) θ = vsubst beta_rhs (vcomp inst_beta θ).
Proof. asimpl. Qed.

(** Égalité de vecteurs : une vraie égalité, sans axiome. *)
Example vcomp_example (θ : vec lsym [ι] [ι]) (χ : vec lsym [ι] [ι]) :
  vcomp (vcomp inst_beta (vid [ι])) (vcomp θ χ) = vcomp (vcomp inst_beta θ) χ.
Proof. asimpl. Qed.
