(** * Théorie des ensembles : opérations comme termes, déduction modulo

    Deux sortes : V (ensembles) et P (propositions). Les constructions
    ensemblistes sont des symboles de terme, éventuellement lieurs :

      ∈     : [V, V] -> P            ∅, ω : V
      pair  : [V, V] -> V            ⋃, 𝒫 : [V] -> V
      compr : [V, [V] -> P] -> V     { x ∈ a | φ(x) }
      repl  : [V, [V] -> V] -> V     { F(x) | x ∈ a }
      ι     : [[V] -> P] -> V        description (« le x tel que φ »)

    À la Dowek–Miquel, les axiomes d'appartenance deviennent des règles du
    système de calcul : x ∈ c(…) se réécrit en sa définition. Le système
    engendré n'est pas terminant (la règle de ω se déplie indéfiniment) ;
    c'est permis, car un système de calcul est seulement une congruence.
    L'extensionnalité et la description, qui ne sont pas des équivalences
    de propositions atomiques, restent des règles de déduction. *)

From Stdlib Require Import List.
Import ListNotations.
From SF.Syntax Require Import Spec Terms Renaming Traversal Eta Composition Vectors.
From SF.Calculus Require Import System Rules.
From SF.Logic Require Import Judgment Propositional.
From SF.Functional Require Import Arrow.
From SF.Quantifiers Require Import Quant.

Local Notation ι a := (Spec [] a).

(** ** Lemmes de substitution pour les symboles du premier ordre *)

Section Aux.
Context {Srt : Type} {Sym : spec Srt -> Type}.

Lemma vsubst_tsym1 {a c} (f : Sym (Spec [ι a] c)) {Θ Γ} (t : Terms.tm Sym Θ a) (v : vec Sym Θ Γ) :
  @vsubst _ Sym Θ c (@tsym _ Sym Θ _ f (@acons _ Sym Θ (ι a) _ t anil)) Γ v
  = @tsym _ Sym Γ _ f (@acons _ Sym Γ (ι a) _ (vsubst t v) anil).
Proof.
  transitivity (@tsym _ Sym Γ _ f (@acons _ Sym Γ (ι a) _ (vsubst_tms (σ := ι a) t v) anil));
    [reflexivity|rewrite vsubst_tms_nil; reflexivity].
Qed.

Lemma vsubst_tsym2 {a b c} (f : Sym (Spec [ι a; ι b] c)) {Θ Γ}
  (t : Terms.tm Sym Θ a) (u : Terms.tm Sym Θ b) (v : vec Sym Θ Γ) :
  @vsubst _ Sym Θ c (@tsym _ Sym Θ _ f (@acons _ Sym Θ (ι a) _ t (@acons _ Sym Θ (ι b) _ u anil))) Γ v
  = @tsym _ Sym Γ _ f (@acons _ Sym Γ (ι a) _ (vsubst t v) (@acons _ Sym Γ (ι b) _ (vsubst u v) anil)).
Proof.
  transitivity (@tsym _ Sym Γ _ f (@acons _ Sym Γ (ι a) _ (vsubst_tms (σ := ι a) t v)
                                     (@acons _ Sym Γ (ι b) _ (vsubst_tms (σ := ι b) u v) anil)));
    [reflexivity|rewrite !vsubst_tms_nil; reflexivity].
Qed.

(** Sous un lieur : la variable 0 reste en place, les autres sont affaiblies. *)
Lemma aget_vup_vz {Θ Γ a} (v : vec Sym Θ Γ) :
  vsubst (var0 (Sym := Sym) (Θ := ι a :: Θ) vz) (vup [ι a] v) = var0 vz.
Proof. rewrite vsubst_var0; reflexivity. Qed.

Lemma aget_vup_vs {Θ Γ a b} (x : var Θ (ι b)) (v : vec Sym Θ Γ) :
  vsubst (var0 (Sym := Sym) (Θ := ι a :: Θ) (vs x)) (vup [ι a] v) = ren_tm (aget x v) (wk [ι a]).
Proof.
  rewrite vsubst_var0. unfold vup, vren; cbn [vcat ahd atl aget vmap].
  rewrite aget_vmap. apply ren_tms_nil.
Qed.

Lemma vsubst_app1_gen' {P s Θ Γ} (x : var Θ (Spec [ι s] P)) (t : Terms.tm Sym Θ s) (v : vec Sym Θ Γ) :
  vsubst (app1 x t) v = vsubst (aget x v) (inst1 (vsubst t v)).
Proof.
  change (happ (Spec [ι s] P) (aget x v) (@acons _ Sym Γ (ι s) _ (vsubst_tms (σ := ι s) t v) anil)
          = vsubst (aget x v) (inst1 (vsubst t v))).
  rewrite vsubst_tms_nil, happ_vsubst; reflexivity.
Qed.

Lemma vsubst_shift_inst1' {Γ} a b (u : Terms.tm Sym (ι a :: Γ) b) :
  vsubst (ren_tms (σ := Spec [ι a] b) u (wk [ι a])) (inst1 (var0 vz)) = u.
Proof.
  unfold ren_tms; rewrite vsubst_ren. rewrite <- (vsubst_vid u) at 2. f_equal.
  apply vec_ext; intros σ x; unfold vget; rewrite aget_vpre.
  vcase x; autorewrite with vsimpl; [|reflexivity].
  revert σ z. refine (var_inv _ _ _); [reflexivity|intros σ' y; destruct (var_nil y)].
Qed.

Lemma vsubst_tsym_eta {D c d} (f : Sym (Spec [Spec D c] d)) {Θ Γ} (x : var Θ (Spec D c)) (v : vec Sym Θ Γ) :
  @vsubst _ Sym Θ d (@tsym _ Sym Θ _ f (@acons _ Sym Θ (Spec D c) _ (eta (Spec D c) x) anil)) Γ v
  = @tsym _ Sym Γ _ f (@acons _ Sym Γ (Spec D c) _ (aget x v) anil).
Proof.
  transitivity (@tsym _ Sym Γ _ f (@acons _ Sym Γ (Spec D c) _ (vsubst_tms (eta (Spec D c) x) v) anil));
    [reflexivity|rewrite vsubst_eta; reflexivity].
Qed.

Lemma vsubst_tsym2_eta {a D c d} (f : Sym (Spec [ι a; Spec D c] d)) {Θ Γ}
  (t : Terms.tm Sym Θ a) (x : var Θ (Spec D c)) (v : vec Sym Θ Γ) :
  @vsubst _ Sym Θ d (@tsym _ Sym Θ _ f (@acons _ Sym Θ (ι a) _ t
                       (@acons _ Sym Θ (Spec D c) _ (eta (Spec D c) x) anil))) Γ v
  = @tsym _ Sym Γ _ f (@acons _ Sym Γ (ι a) _ (vsubst t v) (@acons _ Sym Γ (Spec D c) _ (aget x v) anil)).
Proof.
  transitivity (@tsym _ Sym Γ _ f (@acons _ Sym Γ (ι a) _ (vsubst_tms (σ := ι a) t v)
                  (@acons _ Sym Γ (Spec D c) _ (vsubst_tms (eta (Spec D c) x) v) anil)));
    [reflexivity|rewrite vsubst_tms_nil, vsubst_eta; reflexivity].
Qed.

(** Les mêmes, quand le contexte étendu apparaît sous la forme [ι a :: Θ]
    (instanciation d'une prémisse [premx]). *)
Lemma aget_vup_vz' {Θ Γ a} (v : vec Sym Θ Γ) :
  @vsubst _ Sym (ι a :: Θ) a (var0 (Sym := Sym) (Θ := ι a :: Θ) vz) (ι a :: Γ) (vup [ι a] v) = var0 vz.
Proof. exact (aget_vup_vz v). Qed.

Lemma aget_vup_vs' {Θ Γ a b} (x : var Θ (ι b)) (v : vec Sym Θ Γ) :
  @vsubst _ Sym (ι a :: Θ) b (var0 (Sym := Sym) (Θ := ι a :: Θ) (vs x)) (ι a :: Γ) (vup [ι a] v)
  = ren_tm (aget x v) (wk [ι a]).
Proof. exact (aget_vup_vs x v). Qed.

End Aux.

(** ** Signature ensembliste *)

Section Sig.

Context {Srt : Type} (Sym : spec Srt -> Type) (P V : Srt).

Local Notation σP := (Spec [ι V] P).
Local Notation σF := (Spec [ι V] V).

Class SetSig := {
  s_mem : Sym (Spec [ι V; ι V] P);
  s_empty : Sym (ι V);
  s_omega : Sym (ι V);
  s_pair : Sym (Spec [ι V; ι V] V);
  s_union : Sym (Spec [ι V] V);
  s_power : Sym (Spec [ι V] V);
  s_compr : Sym (Spec [ι V; σP] V);
  s_repl : Sym (Spec [ι V; σF] V);
  s_iota : Sym (Spec [σP] V)
}.

Context `{SetSig}.
Local Notation tm := (Terms.tm Sym).

Definition Mem {Γ} (x a : tm Γ V) : tm Γ P :=
  @tsym _ Sym Γ _ s_mem (@acons _ Sym Γ (ι V) _ x (@acons _ Sym Γ (ι V) _ a anil)).
Definition Empty {Γ} : tm Γ V := @tsym _ Sym Γ (ι V) s_empty anil.
Definition Omega {Γ} : tm Γ V := @tsym _ Sym Γ (ι V) s_omega anil.
Definition Pair {Γ} (a b : tm Γ V) : tm Γ V :=
  @tsym _ Sym Γ _ s_pair (@acons _ Sym Γ (ι V) _ a (@acons _ Sym Γ (ι V) _ b anil)).
Definition Union {Γ} (a : tm Γ V) : tm Γ V := @tsym _ Sym Γ _ s_union (@acons _ Sym Γ (ι V) _ a anil).
Definition Power {Γ} (a : tm Γ V) : tm Γ V := @tsym _ Sym Γ _ s_power (@acons _ Sym Γ (ι V) _ a anil).
(** [Compr a φ] : { x ∈ a | φ }, où x est la variable 0 de φ. *)
Definition Compr {Γ} (a : tm Γ V) (φ : tm (ι V :: Γ) P) : tm Γ V :=
  @tsym _ Sym Γ _ s_compr (@acons _ Sym Γ (ι V) _ a (@acons _ Sym Γ σP _ φ anil)).
(** [Repl a F] : { F(x) | x ∈ a }. *)
Definition Repl {Γ} (a : tm Γ V) (F : tm (ι V :: Γ) V) : tm Γ V :=
  @tsym _ Sym Γ _ s_repl (@acons _ Sym Γ (ι V) _ a (@acons _ Sym Γ σF _ F anil)).
(** [Iota φ] : le x tel que φ(x). *)
Definition Iota {Γ} (φ : tm (ι V :: Γ) P) : tm Γ V := @tsym _ Sym Γ _ s_iota (@acons _ Sym Γ σP _ φ anil).

(** Le singleton et le successeur de von Neumann. *)
Definition Sing {Γ} (a : tm Γ V) : tm Γ V := Pair a a.
Definition Suc {Γ} (a : tm Γ V) : tm Γ V := Union (Pair a (Sing a)).

End Sig.

Arguments SetSig {Srt} Sym P V.
Arguments s_mem {Srt Sym P V _}.
Arguments s_empty {Srt Sym P V _}.
Arguments s_omega {Srt Sym P V _}.
Arguments s_pair {Srt Sym P V _}.
Arguments s_union {Srt Sym P V _}.
Arguments s_power {Srt Sym P V _}.
Arguments s_compr {Srt Sym P V _}.
Arguments s_repl {Srt Sym P V _}.
Arguments s_iota {Srt Sym P V _}.
Arguments Mem {Srt Sym P V _ Γ} x a.
Arguments Empty {Srt Sym P V _ Γ}.
Arguments Omega {Srt Sym P V _ Γ}.
Arguments Pair {Srt Sym P V _ Γ} a b.
Arguments Union {Srt Sym P V _ Γ} a.
Arguments Power {Srt Sym P V _ Γ} a.
Arguments Compr {Srt Sym P V _ Γ} a φ.
Arguments Repl {Srt Sym P V _ Γ} a F.
Arguments Iota {Srt Sym P V _ Γ} φ.
Arguments Sing {Srt Sym P V _ Γ} a.
Arguments Suc {Srt Sym P V _ Γ} a.

(** ** Les règles d'appartenance (système de calcul) *)

Section MemRules.

Context {Srt : Type} {Sym : spec Srt -> Type} {P V : Srt} `{SetSig Srt Sym P V}.
Context {HI : HasImp Sym P} {HA : HasAnd Sym P} {HO : HasOr Sym P} {HB : HasBot Sym P}.
Context {HF : HasForall Sym P V} {HE : HasExists Sym P V} {HQ : HasEq Sym P V}.

Local Notation σP := (Spec [ι V] P).
Local Notation σF := (Spec [ι V] V).
Local Notation x0 := (var0 vz).
Local Notation x1 := (var0 (vs vz)).
Local Notation x2 := (var0 (vs (vs vz))).

Definition mrule (Θ : ctx Srt) (l r : Terms.tm Sym Θ P) : rule Sym :=
  {| r_ctx := Θ; r_sort := P; r_lhs := l; r_rhs := r |}.

Inductive mem_idx := MEmpty | MPair | MUnion | MPower | MOmega | MCompr | MRepl.

Definition mem_rules (i : mem_idx) : rule Sym :=
  match i with
  (* x ∈ ∅  ~  ⊥ *)
  | MEmpty => mrule [ι V] (Mem x0 Empty) Bot
  (* x ∈ {a, b}  ~  x = a ∨ x = b *)
  | MPair => mrule [ι V; ι V; ι V] (Mem x0 (Pair x1 x2)) (Or (Eq V x0 x1) (Eq V x0 x2))
  (* x ∈ ⋃a  ~  ∃y. y ∈ a ∧ x ∈ y *)
  | MUnion => mrule [ι V; ι V] (Mem x0 (Union x1)) (Ex V (And (Mem x0 x2) (Mem x1 x0)))
  (* x ∈ 𝒫a  ~  ∀z. z ∈ x ⇒ z ∈ a *)
  | MPower => mrule [ι V; ι V] (Mem x0 (Power x1)) (All V (Imp (Mem x0 x1) (Mem x0 x2)))
  (* x ∈ ω  ~  x = ∅ ∨ ∃y. y ∈ ω ∧ x = S(y) *)
  | MOmega => mrule [ι V] (Mem x0 Omega)
                (Or (Eq V x0 Empty) (Ex V (And (Mem x0 Omega) (Eq V x1 (Suc x0)))))
  (* x ∈ {z ∈ a | φ}  ~  x ∈ a ∧ φ(x) *)
  | MCompr => mrule [ι V; ι V; σP]
                (Mem x0 (Compr x1 (eta σP (Γ := [ι V; ι V; σP]) (vs (vs vz)))))
                (And (Mem x0 x1) (app1 (s := V) (vs (vs vz)) x0))
  (* y ∈ {F(x) | x ∈ a}  ~  ∃x. x ∈ a ∧ y = F(x) *)
  | MRepl => mrule [ι V; ι V; σF]
               (Mem x0 (Repl x1 (eta σF (Γ := [ι V; ι V; σF]) (vs (vs vz)))))
               (Ex V (And (Mem x0 x2)
                          (Eq V x1 (@tvar _ Sym _ σF (vs (vs (vs vz)))
                                      (@acons _ Sym _ (ι V) _ x0 anil)))))
  end.

End MemRules.

Arguments mem_rules {Srt Sym P V _ _ _ _ _ _ _ _} i.

(** ** Règles de déduction : extensionnalité et description *)

Section DedRules.

Context {Srt : Type} {Sym : spec Srt -> Type} {P V : Srt} `{SetSig Srt Sym P V}.
Context {HQ : HasEq Sym P V}.

Local Notation σP := (Spec [ι V] P).
Local Notation x0 := (var0 vz).
Local Notation x1 := (var0 (vs vz)).
Local Notation x2 := (var0 (vs (vs vz))).

Inductive set_idx := Ext | Descr.

Definition set_rules (i : set_idx) : drule Sym P :=
  match i with
  (* (z ∈ a ⊢ z ∈ b)   (z ∈ b ⊢ z ∈ a)    z frais
     ------------------------------------------
                       a = b                      *)
  | Ext => mkr Sym P [ι V; ι V]
             [premx (P := P) (Θ := [ι V; ι V]) [ι V] [Mem x0 x1] (Mem x0 x2);
              premx (P := P) (Θ := [ι V; ι V]) [ι V] [Mem x0 x2] (Mem x0 x1)]
             (Eq V x0 x1)
  (* φ(t)    (φ(w) ⊢ w = t)   w frais
     --------------------------------
                 φ(ι φ)                *)
  | Descr => mkr Sym P [σP; ι V]
               [prem (P := P) (Θ := [σP; ι V]) [] (app1 vz x1);
                premx (P := P) (Θ := [σP; ι V]) [ι V] [app1 (vs vz) x0] (Eq V x0 x2)]
               (app1 vz (Iota (eta σP (Γ := [σP; ι V]) vz)))
  end.

End DedRules.

Arguments set_rules {Srt Sym P V _ _} i.

(** ** Conversions dérivées *)

Section Conv.

Context {Srt : Type} {Sym : spec Srt -> Type} {P V : Srt} `{SetSig Srt Sym P V}.
Context {HI : HasImp Sym P} {HA : HasAnd Sym P} {HO : HasOr Sym P} {HB : HasBot Sym P}.
Context {HF : HasForall Sym P V} {HE : HasExists Sym P V} {HQ : HasEq Sym P V}.
Context {J : Type} (R : J -> rule Sym) {HR : CIncludes R mem_rules}.

Local Notation tm := (Terms.tm Sym).
Local Notation σP := (Spec [ι V] P).
Local Notation σF := (Spec [ι V] V).
Local Notation "t ~ u" := (conv (generated R) t u) (at level 70).
Local Notation wkV t := (ren_tm t (wk [ι V])).

Ltac set_simpl :=
  unfold Mem, Empty, Omega, Pair, Union, Power, Compr, Repl, Suc, Sing, Or, And, Imp, Bot, All, Ex in *;
  rewrite ?vsubst_tsym1, ?vsubst_tsym2, ?vsubst_Bin, ?vsubst_Cst, ?vsubst_Eq, ?vsubst_Qnt in *.

Theorem mem_empty {Γ} (x : tm Γ V) : Mem x Empty ~ Bot.
Proof.
  pose proof (generated_included R mem_rules MEmpty (@acons _ Sym Γ (ι V) _ x anil)) as Hr.
  cbn [mem_rules mrule r_lhs r_rhs r_ctx r_sort] in Hr.
  unfold Mem, Bot in Hr. rewrite vsubst_tsym2, vsubst_var0, vsubst_Cst in Hr. exact Hr.
Qed.

Theorem mem_pair {Γ} (x a b : tm Γ V) : Mem x (Pair a b) ~ Or (Eq V x a) (Eq V x b).
Proof.
  pose proof (generated_included R mem_rules MPair
                (@acons _ Sym Γ (ι V) _ x (@acons _ Sym Γ (ι V) _ a (@acons _ Sym Γ (ι V) _ b anil)))) as Hr.
  cbn [mem_rules mrule r_lhs r_rhs r_ctx r_sort] in Hr.
  unfold Mem, Pair, Or in Hr. rewrite !vsubst_tsym2, vsubst_Bin, !vsubst_Eq, !vsubst_var0 in Hr.
  exact Hr.
Qed.

Theorem mem_compr {Γ} (x a : tm Γ V) (φ : tm (ι V :: Γ) P) :
  Mem x (Compr a φ) ~ And (Mem x a) (vsubst φ (inst1 x)).
Proof.
  pose proof (generated_included R mem_rules MCompr
                (@acons _ Sym Γ (ι V) _ x (@acons _ Sym Γ (ι V) _ a (@acons _ Sym Γ σP _ φ anil)))) as Hr.
  cbn [mem_rules mrule r_lhs r_rhs r_ctx r_sort] in Hr.
  unfold And in Hr. rewrite vsubst_Bin in Hr. unfold Mem in Hr. rewrite !vsubst_tsym2, !vsubst_var0 in Hr.
  rewrite (vsubst_app1 (s := V) (vs (vs vz)) vz) in Hr.
  unfold Compr in Hr. rewrite vsubst_tsym2_eta, vsubst_var0 in Hr. exact Hr.
Qed.

Theorem mem_power {Γ} (x a : tm Γ V) :
  Mem x (Power a) ~ All V (Imp (Mem (var0 vz) (wkV x)) (Mem (var0 vz) (wkV a))).
Proof.
  pose proof (generated_included R mem_rules MPower
                (@acons _ Sym Γ (ι V) _ x (@acons _ Sym Γ (ι V) _ a anil))) as Hr.
  cbn [mem_rules mrule r_lhs r_rhs r_ctx r_sort] in Hr.
  unfold All, Imp, Mem, Power in Hr. rewrite vsubst_tsym2, vsubst_tsym1, !vsubst_var0, vsubst_Qnt in Hr.
  rewrite (vsubst_tms_vup (σ := σP)) in Hr. cbn [dom cod] in Hr.
  rewrite vsubst_Bin, !vsubst_tsym2, aget_vup_vz, !aget_vup_vs in Hr. exact Hr.
Qed.

Theorem mem_union {Γ} (x a : tm Γ V) :
  Mem x (Union a) ~ Ex V (And (Mem (var0 vz) (wkV a)) (Mem (wkV x) (var0 vz))).
Proof.
  pose proof (generated_included R mem_rules MUnion
                (@acons _ Sym Γ (ι V) _ x (@acons _ Sym Γ (ι V) _ a anil))) as Hr.
  cbn [mem_rules mrule r_lhs r_rhs r_ctx r_sort] in Hr.
  unfold Ex, And, Mem, Union in Hr. rewrite vsubst_tsym2, vsubst_tsym1, !vsubst_var0, vsubst_Qnt in Hr.
  rewrite (vsubst_tms_vup (σ := σP)) in Hr. cbn [dom cod] in Hr.
  rewrite vsubst_Bin, !vsubst_tsym2, aget_vup_vz, !aget_vup_vs in Hr. exact Hr.
Qed.

Theorem mem_omega {Γ} (x : tm Γ V) :
  Mem x Omega ~ Or (Eq V x Empty) (Ex V (And (Mem (var0 vz) Omega) (Eq V (wkV x) (Suc (var0 vz))))).
Proof.
  pose proof (generated_included R mem_rules MOmega (@acons _ Sym Γ (ι V) _ x anil)) as Hr.
  cbn [mem_rules mrule r_lhs r_rhs r_ctx r_sort] in Hr.
  unfold Or, Ex, And, Mem in Hr. rewrite vsubst_tsym2, vsubst_Bin, vsubst_Eq, !vsubst_var0, vsubst_Qnt in Hr.
  rewrite (vsubst_tms_vup (σ := σP)) in Hr. cbn [dom cod] in Hr.
  rewrite vsubst_Bin, vsubst_tsym2, vsubst_Eq, aget_vup_vz, aget_vup_vs in Hr.
  unfold Suc, Sing, Union, Pair in Hr. rewrite vsubst_tsym1, !vsubst_tsym2, aget_vup_vz in Hr. exact Hr.
Qed.

End Conv.

(** ** Règles dérivées *)

Section Derived.

Context {Srt : Type} {Sym : spec Srt -> Type} {P V : Srt} `{SetSig Srt Sym P V} {HQ : HasEq Sym P V}.
Context (C : system Sym) {I : Type} (R : I -> drule Sym P) {HS : Includes R set_rules}.

Local Notation tm := (Terms.tm Sym).
Local Notation form := (form Sym P).
Local Notation σP := (Spec [ι V] P).
Local Notation "Ξ ⊢ φ" := (deriv C P R _ Ξ φ) (at level 70).
Local Notation wkV t := (ren_tm t (wk [ι V])).

(** Extensionnalité : si z ∈ a et z ∈ b sont interdérivables pour z frais,
    alors a = b. *)
Theorem extensionality {Γ} (Ξ : list (form Γ)) (a b : tm Γ V) :
  deriv C P R (ι V :: Γ) (Mem (var0 vz) (wkV a) :: wk_list [ι V] Ξ) (Mem (var0 vz) (wkV b)) ->
  deriv C P R (ι V :: Γ) (Mem (var0 vz) (wkV b) :: wk_list [ι V] Ξ) (Mem (var0 vz) (wkV a)) ->
  Ξ ⊢ Eq V a b.
Proof.
  intros H1 H2.
  apply (rule_inc C P R set_rules Ext Ξ (@acons _ Sym Γ (ι V) _ a (@acons _ Sym Γ (ι V) _ b anil)));
    cbn [set_rules mkr d_ctx d_concl d_prems].
  - rewrite vsubst_Eq, !vsubst_var0; reflexivity.
  - intros p [<-|[<-|[]]]; unfold inst_hyps, inst_goal, vsubst_list;
      cbn [p_ext p_hyps p_goal premx d_ctx map app]; unfold Mem; rewrite !vsubst_tsym2;
      rewrite aget_vup_vz', !aget_vup_vs'; cbn [aget ahd atl]; assumption.
Qed.

(** Description : si t vérifie φ et que tout w vérifiant φ est égal à t,
    alors ι φ vérifie φ. *)
Theorem description {Γ} (Ξ : list (form Γ)) (φ : form (ι V :: Γ)) (t : tm Γ V) :
  Ξ ⊢ vsubst φ (inst1 t) ->
  deriv C P R (ι V :: Γ) (φ :: wk_list [ι V] Ξ) (Eq V (var0 vz) (wkV t)) ->
  Ξ ⊢ vsubst φ (inst1 (Iota φ)).
Proof.
  intros H1 H2.
  apply (rule_inc C P R set_rules Descr Ξ (@acons _ Sym Γ σP _ φ (@acons _ Sym Γ (ι V) _ t anil)));
    cbn [set_rules mkr d_ctx d_concl d_prems].
  - rewrite vsubst_app1_gen'. unfold Iota. rewrite vsubst_tsym_eta. reflexivity.
  - intros p [<-|[<-|[]]]; unfold inst_hyps, inst_goal, vsubst_list;
      cbn [p_ext p_hyps p_goal prem premx d_ctx map app].
    + rewrite vup_nil, wk_list_nil, (vsubst_app1 (s := V) vz (vs vz)). exact H1.
    + eapply deriv_eq2; [| |exact H2].
      * f_equal. rewrite (vsubst_app1 (s := V) (vs vz) vz). unfold vup, vren; cbn [vcat ahd atl aget vmap].
        cbn [vcat ahd atl aget etas eta vl vr]. symmetry; apply vsubst_shift_inst1'.
      * rewrite vsubst_Eq, aget_vup_vz', aget_vup_vs'. reflexivity.
Qed.

End Derived.
