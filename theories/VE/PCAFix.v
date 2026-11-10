(** * Le point fixe dans le cadre d'une PCA, et V(A) ⊨ IZFε

    Dans [pca_frame A], toute expression de l'opérade ([eexp], déf. 2.1.2)
    a un point fixe ([pfix]) : c'est le combinateur de Turing « paresseux »
    Z = δδ avec δ := λw.λx. H (w w) x, où H calcule, *à l'intérieur de A*,
    l'évidence eeval t a à partir de t ([qexp], [qexp_ev]).

    Pour calculer eeval t a en interne, on remarque que chaque évidence
    construite (r_comp, r_pair, r_lam, r_gen) est la valeur [lval ρ E]
    d'une expression fixe E, où les évidences arguments sont des variables
    de l'environnement ρ ; et [lval] lui-même se calcule en interne avec K
    et S ([lq], [lq_ev]).

    Conséquence : pour toute PCA, l'hypothèse [yfix] de V(E) est levée ;
    Φ = parties de A est essentiellement petit (Φ₀ := A → Prop). Il ne
    reste que la collection ([ve_sound_pca]). Instance : K1. *)

From Stdlib Require Import List.
Import ListNotations.
From SF.Models Require Import PSet Frame FrameModel Tarski PCA K1.
From SF.VE Require Import Trees Base Ind Coll Sound.
From SF.SetTheory Require Import IZFe.

Section PFix.

Context (A : pca).

Local Notation cexp := (cexp A).
Local Notation ev := (ev A).
Local Notation lval := (lval A).
Local Notation RF := (pca_frame A).

(** ** lval, calculé en interne *)

Fixpoint lq (E : cexp) (env : nat -> cexp) : cexp :=
  match E with
  | cv 0 => cc (s2 cK cK)
  | cv (S n) => capp (cc cK) (env n)
  | cc a => cc (k1 a)
  | capp e1 e2 => capp (capp (cc cS) (lq e1 env)) (lq e2 env)
  end.

Lemma lq_ev σ E env (ρ : nat -> A) :
  (forall n, ev σ (env n) (ρ n)) -> ev σ (lq E env) (lval ρ E).
Proof.
  intros Henv. induction E as [[|n]|a|e1 IH1 e2 IH2]; cbn.
  - apply ev_c.
  - eapply ev_app; [apply ev_c|apply Henv|apply ap_K].
  - apply ev_c.
  - eapply ev_app; [eapply ev_app; [apply ev_c|exact IH1|apply ap_S]|exact IH2|apply ap_S1].
Qed.

Definition env1 (c : cexp) : nat -> cexp := fun n => match n with 0 => c | _ => cc cK end.
Definition env2 (c1 c2 : cexp) : nat -> cexp :=
  fun n => match n with 0 => c1 | 1 => c2 | _ => cc cK end.

Lemma env1_ev σ c v : ev σ c v -> forall n, ev σ (env1 c n) (scons A v (ρ0 A) n).
Proof. intros H [|n]; [exact H|apply ev_c]. Qed.

Lemma env2_ev σ c1 c2 v1 v2 : ev σ c1 v1 -> ev σ c2 v2 ->
  forall n, ev σ (env2 c1 c2 n) (scons A v1 (scons A v2 (ρ0 A)) n).
Proof. intros H1 H2 [|[|n]]; [exact H1|exact H2|apply ev_c]. Qed.

(** Les évidences construites, comme valeurs d'expressions fixes. *)
Definition Ecomp : cexp := capp (cv 2) (capp (cv 1) (cv 0)).
Definition Epair : cexp := capp (capp (cc (PCA.cPair A)) (capp (cv 1) (cv 0))) (capp (cv 2) (cv 0)).
Definition Elam : cexp := lam A (capp (cv 2) (capp (capp (cc (PCA.cPair A)) (cv 1)) (cv 0))).
Definition Egen : cexp := lam A (capp (cv 2) (cv 1)).

(** ** eeval, calculé en interne (la variable 0 est t) *)

Fixpoint qexp (a : eexp RF) : cexp :=
  match a with
  | ex_var _ => cv 0
  | ex_cst _ e => cc e
  | ex_id _ => cc (cI A)
  | ex_comp _ a b => lq Ecomp (env2 (qexp a) (qexp b))
  | ex_top _ => cc cK
  | ex_fst _ => cc (PCA.cFst A)
  | ex_snd _ => cc (PCA.cSnd A)
  | ex_pair _ a b => lq Epair (env2 (qexp a) (qexp b))
  | ex_lam _ a => lq Elam (env1 (qexp a))
  | ex_eval _ => cc (r_eval A)
  | ex_gen _ a => lq Egen (env1 (qexp a))
  | ex_inst _ => cc (PCA.cFst A)
  end.

Lemma qexp_ev t a : ev (scons A t (ρ0 A)) (qexp a) (eeval RF t a).
Proof.
  induction a; cbn [qexp eeval].
  - apply ev_v.
  - apply ev_c.
  - apply ev_c.
  - exact (lq_ev _ Ecomp _ _ (env2_ev _ _ _ _ _ IHa1 IHa2)).
  - apply ev_c.
  - apply ev_c.
  - apply ev_c.
  - exact (lq_ev _ Epair _ _ (env2_ev _ _ _ _ _ IHa1 IHa2)).
  - exact (lq_ev _ Elam _ _ (env1_ev _ _ _ IHa)).
  - apply ev_c.
  - exact (lq_ev _ Egen _ _ (env1_ev _ _ _ IHa)).
  - apply ev_c.
Qed.

(** ** Le point fixe *)

Definition Hq (a : eexp RF) : A := clo A (qexp a).

Lemma Hq_ap a t : ap (Hq a) t (eeval RF t a).
Proof. apply clo_ap, qexp_ev. Qed.

(** δ := λw.λx. H (w w) x, et Z := δδ. *)
Definition zbody (a : eexp RF) : cexp := capp (capp (cc (Hq a)) (capp (cv 1) (cv 1))) (cv 0).
Definition delta (a : eexp RF) : A := clo A (lam A (zbody a)).
Definition pfix (a : eexp RF) : A := lval (scons A (delta a) (ρ0 A)) (zbody a).

Lemma delta_self a : ap (delta a) (delta a) (pfix a).
Proof. apply clo2_ap1. Qed.

Lemma pfix_unfold a x y : ap (eeval RF (pfix a) a) x y -> ap (pfix a) x y.
Proof.
  intros H. apply clo2_ap2.
  eapply ev_app; [|apply ev_v|exact H].
  eapply ev_app; [apply ev_c| |apply Hq_ap].
  eapply ev_app; [apply ev_v|apply ev_v|apply delta_self].
Qed.

Lemma pfix_spec a φ ψ :
  fent (F := RF) φ (eeval RF (pfix a) a) ψ -> fent (F := RF) φ (pfix a) ψ.
Proof.
  intros H x Hx. destruct (H x Hx) as (y & Hy & Hψ). exists y. split; [apply pfix_unfold, Hy|exact Hψ].
Qed.

End PFix.

(** ** V(A) ⊨ IZFε pour toute PCA, sous la seule collection *)

Section VPCA.

Context (A : pca).
Local Notation RF := (pca_frame A).

Context (coll : forall T, (T -> Trees.V RF) -> (Trees.V RF -> Trees.V RF -> pcar RF) -> Trees.V RF).
Context (coll_proper : forall T (xs xs' : T -> Trees.V RF) ψ ψ', Rproper RF ψ ->
           (forall t, teq RF (xs t) (xs' t)) -> (forall x y, ψ x y ≡ ψ' x y) ->
           teq RF (coll T xs ψ) (coll T xs' ψ')).
Context (coll_spec : forall T (xs : T -> Trees.V RF) ψ, Rproper RF ψ ->
           forall t β, exists s, ψ (xs t) β ≡ ψ (xs t) (sub RF (coll T xs ψ) s)).

Local Notation Iy0 := (Iy' RF (A -> Prop) (fun p => p) (fun p => p) coll coll_proper).

(** Un énoncé clos prouvable dans IZFε est réalisé dans V(A). *)
Theorem ve_sound_pca φ : IZFe [] [] φ -> exists e, fent (F := RF) ftop e (T0 RF (sval (So' RF) Iy0 φ tt)).
Proof.
  exact (ve_sound_closed RF (A -> Prop) (fun p => p) (fun p => p) (fun p => peq_refl p)
           (pfix A) (pfix_spec A) coll coll_proper coll_spec φ).
Qed.

End VPCA.

(** Instance : la réalisabilité de Kleene pour IZFε (V(K1)), sous la
    collection. *)
Definition ve_sound_K1 := ve_sound_pca K1.
