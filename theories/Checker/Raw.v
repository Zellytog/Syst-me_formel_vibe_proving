(** * Syntaxe brute et élaboration vers les termes intrinsèques

    Première brique du vérificateur certifié. Le front-end (OCaml) et le
    vérificateur manipulent des termes *bruts* : sans types dépendants,
    avec des indices de de Bruijn entiers et des symboles pris dans un type
    quelconque [RSym]. L'élaboration [elab] vérifie qu'un terme brut est
    bien formé dans un contexte et rend le terme intrinsèque correspondant
    ([tm Sym Γ s]) ; l'effacement [erase] va dans l'autre sens.

    Résultats :
    - [elab_erase] (complétude) : élaborer l'effacement d'un terme
      intrinsèque redonne ce terme ;
    - [erase_elab] (adéquation) : si un terme brut s'élabore en [u], alors
      il est l'effacement de [u].

    Les deux ensemble disent que les termes bruts bien formés et les termes
    intrinsèques sont en bijection. Aucun axiome : l'unicité des preuves
    d'égalité entre sortes vient de leur décidabilité ([Eqdep_dec]). *)

From Stdlib Require Import List Eqdep_dec.
Import ListNotations.
From SF.Syntax Require Import Spec Terms.

(** ** Termes bruts

    Ils ont la même forme que les termes intrinsèques : une tête (variable
    ou symbole) appliquée à une liste d'arguments. Comme pour [tm]/[args],
    la liste est un type mutuel, ce qui donne des récursions structurelles
    simples. *)

Section RawSyntax.

Context (RSym : Type).

Inductive rtm : Type :=
| rvar (n : nat) (a : rargs)
| rsym (f : RSym) (a : rargs)
with rargs : Type :=
| rnil
| rcons (t : rtm) (a : rargs).

End RawSyntax.

Arguments rvar {RSym} n a.
Arguments rsym {RSym} f a.
Arguments rnil {RSym}.
Arguments rcons {RSym} t a.

Scheme rtm_ind' := Induction for rtm Sort Prop
  with rargs_ind' := Induction for rargs Sort Prop.
Combined Scheme rtm_rargs_ind from rtm_ind', rargs_ind'.

(** ** Élaboration *)

Section Elab.

Context {Srt : Type} (Sym : spec Srt -> Type).
Context (srt_eq_dec : forall a b : Srt, {a = b} + {a <> b}).

(** Une signature brute : chaque symbole brut a une spécification et
    désigne un symbole de la signature intrinsèque. *)
Context (RSym : Type) (rspec : RSym -> spec Srt) (rsym_of : forall r, Sym (rspec r)).

Local Notation ctx := (ctx Srt).
Local Notation spec := (spec Srt).
Local Notation rtm := (rtm RSym).
Local Notation rargs := (rargs RSym).

(** Recherche d'une variable : l'indice [n] dans [Γ], avec sa spécification. *)
Fixpoint lookup (Γ : ctx) (n : nat) : option {σ & var Γ σ} :=
  match Γ return option {σ & var Γ σ} with
  | [] => None
  | τ :: Γ' =>
      match n with
      | 0 => Some (existT _ τ vz)
      | S n' =>
          match lookup Γ' n' with
          | Some (existT _ σ x) => Some (existT _ σ (vs x))
          | None => None
          end
      end
  end.

(** [elab Γ t] : le terme intrinsèque désigné par [t] dans [Γ], avec sa
    sorte, s'il est bien formé. La sorte est déterminée par la tête :
    c'est le codomaine de la spécification de la variable ou du symbole. *)
Fixpoint elab (Γ : ctx) (t : rtm) {struct t} : option {s & tm Sym Γ s} :=
  match t with
  | rvar n a =>
      match lookup Γ n with
      | Some (existT _ σ x) =>
          match elab_args Γ (dom σ) a with
          | Some a' => Some (existT _ (cod σ) (tvar x a'))
          | None => None
          end
      | None => None
      end
  | rsym f a =>
      match elab_args Γ (dom (rspec f)) a with
      | Some a' => Some (existT _ (cod (rspec f)) (tsym (rsym_of f) a'))
      | None => None
      end
  end
with elab_args (Γ : ctx) (Θ : list spec) (a : rargs) {struct a} : option (args Sym Γ Θ) :=
  match Θ return option (args Sym Γ Θ) with
  | [] => match a with rnil => Some anil | rcons _ _ => None end
  | σ :: Θ' =>
      match a with
      | rnil => None
      | rcons t a' =>
          match elab (dom σ ++ Γ) t, elab_args Γ Θ' a' with
          | Some (existT _ s u), Some r =>
              match srt_eq_dec s (cod σ) with
              | left e => Some (acons (eq_rect _ (tm Sym (dom σ ++ Γ)) u _ e) r)
              | right _ => None
              end
          | _, _ => None
          end
      end
  end.

(** Version booléenne, pour la réflexion : le terme est-il bien formé, de
    sorte [s] ? *)
Definition check (Γ : ctx) (t : rtm) (s : Srt) : bool :=
  match elab Γ t with
  | Some (existT _ s' _) => if srt_eq_dec s' s then true else false
  | None => false
  end.

(** Un terme brut accepté par [check] désigne un terme intrinsèque. *)
Definition realize (Γ : ctx) (t : rtm) (s : Srt) (H : check Γ t s = true) : tm Sym Γ s.
Proof.
  unfold check in H.
  destruct (elab Γ t) as [[s' u]|]; [|discriminate].
  destruct (srt_eq_dec s' s) as [e|]; [|discriminate].
  exact (eq_rect _ (tm Sym Γ) u _ e).
Defined.

End Elab.

(** ** Effacement et aller-retour *)

Section Erase.

Context {Srt : Type} (Sym : spec Srt -> Type).
Context (srt_eq_dec : forall a b : Srt, {a = b} + {a <> b}).
Context (RSym : Type) (rspec : RSym -> spec Srt) (rsym_of : forall r, Sym (rspec r)).

(** Codage des symboles intrinsèques par des symboles bruts, compatible
    avec [rspec] et [rsym_of]. *)
Context (renc : forall σ, Sym σ -> RSym).
Context (renc_spec : forall σ (c : Sym σ), rspec (renc σ c) = σ).
Context (renc_sym : forall σ (c : Sym σ),
            eq_rect _ Sym (rsym_of (renc σ c)) _ (renc_spec σ c) = c).
Context (renc_rsym : forall r, renc _ (rsym_of r) = r).

Local Notation ctx := (ctx Srt).
Local Notation elab := (elab Sym srt_eq_dec RSym rspec rsym_of).
Local Notation elab_args := (elab_args Sym srt_eq_dec RSym rspec rsym_of).
Local Notation lookup := (@lookup Srt).

Fixpoint var_idx {Γ : ctx} {σ} (x : var Γ σ) : nat :=
  match x with
  | vz => 0
  | vs y => S (var_idx y)
  end.

Fixpoint erase {Γ s} (t : tm Sym Γ s) : rtm RSym :=
  match t with
  | tvar x a => rvar (var_idx x) (erase_args a)
  | tsym c a => rsym (renc _ c) (erase_args a)
  end
with erase_args {Γ Θ} (a : args Sym Γ Θ) : rargs RSym :=
  match a with
  | anil => rnil
  | acons t a' => rcons (erase t) (erase_args a')
  end.

Lemma lookup_var_idx {Γ σ} (x : var Γ σ) : lookup Γ (var_idx x) = Some (existT _ σ x).
Proof.
  induction x as [Γ σ|Γ σ τ y IH]; simpl; [reflexivity|].
  rewrite IH. reflexivity.
Qed.

Lemma eq_dec_refl (s : Srt) : exists e, srt_eq_dec s s = left e /\ e = eq_refl.
Proof.
  destruct (srt_eq_dec s s) as [e|n]; [|contradiction].
  exists e. split; [reflexivity|]. apply UIP_dec. exact srt_eq_dec.
Qed.

(** Le cas d'un symbole : on se ramène à un symbole brut [r] et à une
    égalité [rspec r = σ], qu'on élimine. *)
Lemma elab_tsym {Γ σ} (c : Sym σ) (a : args Sym Γ (dom σ)) :
  elab_args Γ (dom σ) (erase_args a) = Some a ->
  elab Γ (rsym (renc σ c) (erase_args a)) = Some (existT _ (cod σ) (tsym c a)).
Proof.
  intro Ha. simpl.
  pose proof (renc_sym σ c) as Hc.
  generalize dependent (renc_spec σ c).
  generalize (renc σ c) as r. intros r e. destruct e. simpl. intros Hc.
  rewrite Ha. subst c. reflexivity.
Qed.

Lemma elab_erase_mut :
  (forall Γ s (t : tm Sym Γ s), elab Γ (erase t) = Some (existT _ s t)) /\
  (forall Γ Θ (a : args Sym Γ Θ), elab_args Γ Θ (erase_args a) = Some a).
Proof.
  apply tm_args_ind; intros.
  - simpl. rewrite lookup_var_idx. rewrite H. reflexivity.
  - apply elab_tsym. exact H.
  - reflexivity.
  - simpl. rewrite H, H0.
    destruct (eq_dec_refl (cod σ)) as [e [-> ->]]. reflexivity.
Qed.

(** Complétude : un terme intrinsèque est reconnu par l'élaboration. *)
Theorem elab_erase {Γ s} (t : tm Sym Γ s) : elab Γ (erase t) = Some (existT _ s t).
Proof. apply elab_erase_mut. Qed.

Corollary check_erase {Γ s} (t : tm Sym Γ s) : check Sym srt_eq_dec RSym rspec rsym_of Γ (erase t) s = true.
Proof.
  unfold check. rewrite elab_erase.
  destruct (eq_dec_refl s) as [e [-> _]]. reflexivity.
Qed.

Lemma lookup_some {Γ n} (p : {σ & var Γ σ}) :
  lookup Γ n = Some p -> var_idx (projT2 p) = n.
Proof.
  revert n p. induction Γ as [|τ Γ IH]; intros n p H; simpl in H; [discriminate|].
  destruct n as [|n].
  - injection H as <-. reflexivity.
  - destruct (lookup Γ n) as [[σ' y]|] eqn:E; [|discriminate].
    injection H as <-. simpl. f_equal. apply (IH n (existT _ σ' y)). exact E.
Qed.

Local Ltac inj H := apply (inj_pair2_eq_dec _ srt_eq_dec) in H.

(** Adéquation : un terme brut qui s'élabore est l'effacement de son
    élaboration. *)
Lemma erase_elab_mut :
  (forall t Γ s (u : tm Sym Γ s), elab Γ t = Some (existT _ s u) -> erase u = t) /\
  (forall a Γ Θ (b : args Sym Γ Θ), elab_args Γ Θ a = Some b -> erase_args b = a).
Proof.
  apply rtm_rargs_ind.
  - intros n a IH Γ s u H. simpl in H.
    destruct (lookup Γ n) as [[σ x]|] eqn:E; [|discriminate].
    destruct (elab_args Γ (dom σ) a) as [a'|] eqn:Ea; [|discriminate].
    injection H as Hs H. subst s. inj H. subst u. simpl.
    f_equal; [apply (lookup_some (existT _ σ x)); exact E | apply IH; exact Ea].
  - intros f a IH Γ s u H. simpl in H.
    destruct (elab_args Γ (dom (rspec f)) a) as [a'|] eqn:Ea; [|discriminate].
    injection H as Hs H. subst s. inj H. subst u. simpl.
    f_equal; [apply renc_rsym | apply IH; exact Ea].
  - intros Γ Θ b H. destruct Θ; simpl in H; [|discriminate].
    injection H as <-. reflexivity.
  - intros t IHt a IHa Γ Θ b H. destruct Θ as [|σ Θ]; simpl in H; [discriminate|].
    destruct (elab (dom σ ++ Γ) t) as [[s u]|] eqn:Et; [|discriminate].
    destruct (elab_args Γ Θ a) as [r|] eqn:Er; [|discriminate].
    destruct (srt_eq_dec s (cod σ)) as [e|]; [|discriminate].
    injection H as <-. subst s. simpl.
    f_equal; [apply IHt; exact Et | apply IHa; exact Er].
Qed.

Theorem erase_elab {Γ s} (t : rtm RSym) (u : tm Sym Γ s) :
  elab Γ t = Some (existT _ s u) -> erase u = t.
Proof. apply erase_elab_mut. Qed.

End Erase.
