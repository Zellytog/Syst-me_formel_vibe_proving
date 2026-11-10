(** * Systèmes arithmétiques

    Une signature arithmétique contient une sorte N, 0 ∈ Symb(N),
    S ∈ Symb([N] -> N) et des récurseurs

      rec_s ∈ Symb([s, [N, s] -> s, N] -> s).

    Le paramètre [r] borne la hauteur des récurseurs, indépendamment de
    l'ordre logique (n,p) : rec_s n'existe que si s est de grade (m,0) avec
    m < r. Avec r = 1, on n'a que des récurseurs aux sortes de base : les
    fonctions récursives primitives. La hauteur propositionnelle nulle exclut
    l'élimination forte (pas de propositions définies par récursion).

    Côté calcul : les deux règles de rec. Côté logique : le schéma de
    récurrence (sans quantificateur : il conclut φ(t) pour tout terme t) et
    l'axiome S t ≠ 0. *)

From Stdlib Require Import List.
Import ListNotations.
From SF.Syntax Require Import Spec Terms Renaming Traversal Eta Composition Vectors.
From SF.Calculus Require Import System Rules.
From SF.Logic Require Import Judgment Propositional.
From SF.Functional Require Import Arrow Graded.
From SF.Quantifiers Require Import Quant.

Local Notation ι a := (Spec [] a).

Section Arith.

Context {Srt : Type} (Sym : spec Srt -> Type) `{Functional Srt Sym} {G : Graded Sym}.
Context (N : Srt) (r : bound).

Local Notation tm := (Terms.tm Sym).

(** Les sortes cibles autorisées pour les récurseurs. *)
Definition rec_ok (s : Srt) : Prop := blt (fst (gr s)) r /\ snd (gr s) = 0.

Definition rec_spec (s : Srt) : spec Srt := Spec [ι s; Spec [ι N; ι s] s; ι N] s.

Class Arithmetic := {
  a_zero : Sym (ι N);
  a_succ : Sym (Spec [ι N] N);
  a_rec : forall s, rec_ok s -> Sym (rec_spec s)
}.

Context `{Arithmetic}.

Definition Zero {Γ} : tm Γ N := @tsym _ Sym Γ (ι N) a_zero anil.
Definition Succ {Γ} (t : tm Γ N) : tm Γ N :=
  @tsym _ Sym Γ (Spec [ι N] N) a_succ (@acons _ Sym Γ (ι N) _ t anil).

(** [Rec s h z st n] : rec(z, (k, a). st, n). Dans [st], k est la variable 0
    (le prédécesseur) et a la variable 1 (la valeur précédente). *)
Definition Rec s (h : rec_ok s) {Γ} (z : tm Γ s) (st : tm (ι N :: ι s :: Γ) s) (n : tm Γ N) : tm Γ s :=
  @tsym _ Sym Γ (rec_spec s) (a_rec s h)
    (@acons _ Sym Γ (ι s) _ z
       (@acons _ Sym Γ (Spec [ι N; ι s] s) _ st
          (@acons _ Sym Γ (ι N) _ n anil))).

(** ** Règles de calcul de rec *)

Local Notation σst s := (Spec [ι N; ι s] s).

Definition rec0_rule s (h : rec_ok s) : rule Sym := {|
  r_ctx := [ι s; σst s];
  r_sort := s;
  r_lhs := Rec s h (var0 vz) (eta (σst s) (Γ := [ι s; σst s]) (vs vz)) Zero;
  r_rhs := var0 vz
|}.

Definition recS_rule s (h : rec_ok s) : rule Sym := {|
  r_ctx := [ι s; σst s; ι N];
  r_sort := s;
  r_lhs := Rec s h (var0 vz) (eta (σst s) (Γ := [ι s; σst s; ι N]) (vs vz)) (Succ (var0 (vs (vs vz))));
  r_rhs := @tvar _ Sym [ι s; σst s; ι N] (σst s) (vs vz)
             (@acons _ Sym _ (ι N) _ (var0 (vs (vs vz)))
                (@acons _ Sym _ (ι s) _
                   (Rec s h (var0 vz) (eta (σst s) (Γ := [ι s; σst s; ι N]) (vs vz))
                      (var0 (vs (vs vz)))) anil))
|}.

Definition rec_idx : Type := ({ s : Srt & rec_ok s } * bool)%type.

Definition rec_rules (k : rec_idx) : rule Sym :=
  match k with
  | (existT _ s h, false) => rec0_rule s h
  | (existT _ s h, true) => recS_rule s h
  end.

(** Le système de calcul arithmétique : les règles de rec. *)
Definition arith_system : system Sym := generated rec_rules.

End Arith.

Arguments rec_ok {Srt Sym _ G} r s.
Arguments Arithmetic {Srt} Sym {_ G} N r.
Arguments a_zero {Srt Sym _ G N r _}.
Arguments a_succ {Srt Sym _ G N r _}.
Arguments a_rec {Srt Sym _ G N r _} s h.
Arguments Zero {Srt Sym _ G N r _ Γ}.
Arguments Succ {Srt Sym _ G N r _ Γ} t.
Arguments Rec {Srt Sym _ G N r _} s h {Γ} z st n.
Arguments rec_rules {Srt Sym _ G N r _} k.
Arguments arith_system {Srt} Sym {_ G} N r {_}.

(** ** Conversions dérivées *)

Section RecConv.

Context {Srt : Type} {Sym : spec Srt -> Type} `{Functional Srt Sym} {G : Graded Sym}.
Context {N : Srt} {r : bound} {AR : Arithmetic Sym N r}.
Context {I : Type} (R : I -> rule Sym) {HR : CIncludes R rec_rules}.

Local Notation tm := (Terms.tm Sym).
Local Notation σst s := (Spec [ι N; ι s] s).

Lemma vsubst_Zero {Θ Γ} (v : vec Sym Θ Γ) : vsubst (Zero (N := N)) v = Zero.
Proof. reflexivity. Qed.

Lemma vsubst_Succ {Θ Γ} (t : tm Θ N) (v : vec Sym Θ Γ) : vsubst (Succ t) v = Succ (vsubst t v).
Proof.
  unfold Succ.
  transitivity (@tsym _ Sym Γ _ a_succ (@acons _ Sym Γ (ι N) _ (vsubst_tms (σ := ι N) t v) anil));
    [reflexivity|].
  rewrite vsubst_tms_nil; reflexivity.
Qed.

Lemma vsubst_Rec s h {Θ Γ} (z : tm Θ s) st (n : tm Θ N) (v : vec Sym Θ Γ) :
  vsubst (Rec s h z st n) v = Rec s h (vsubst z v) (vsubst_tms (σ := σst s) st v) (vsubst n v).
Proof.
  unfold Rec.
  transitivity (@tsym _ Sym Γ _ (a_rec s h)
                  (@acons _ Sym Γ (ι s) _ (vsubst_tms (σ := ι s) z v)
                     (@acons _ Sym Γ (σst s) _ (vsubst_tms (σ := σst s) st v)
                        (@acons _ Sym Γ (ι N) _ (vsubst_tms (σ := ι N) n v) anil))));
    [reflexivity|].
  rewrite !vsubst_tms_nil; reflexivity.
Qed.

Theorem rec_zero_conv s h {Γ} (z : tm Γ s) (st : tm (ι N :: ι s :: Γ) s) :
  conv (generated R) (Rec s h z st Zero) z.
Proof.
  pose proof (generated_included R rec_rules (existT _ s h, false)
                (@acons _ Sym Γ (ι s) _ z (@acons _ Sym Γ (σst s) _ st anil))) as Hr.
  cbn [rec_rules rec0_rule r_lhs r_rhs r_ctx] in Hr.
  rewrite vsubst_Rec, !vsubst_var0, vsubst_eta, vsubst_Zero in Hr. exact Hr.
Qed.

Theorem rec_succ_conv s h {Γ} (z : tm Γ s) (st : tm (ι N :: ι s :: Γ) s) (m : tm Γ N) :
  conv (generated R) (Rec s h z st (Succ m))
    (vsubst st (@acons _ Sym Γ (ι N) _ m (@acons _ Sym Γ (ι s) _ (Rec s h z st m) (vid Γ)))).
Proof.
  pose proof (generated_included R rec_rules (existT _ s h, true)
                (@acons _ Sym Γ (ι s) _ z (@acons _ Sym Γ (σst s) _ st
                   (@acons _ Sym Γ (ι N) _ m anil)))) as Hr.
  cbn [rec_rules recS_rule r_lhs r_rhs r_ctx] in Hr.
  rewrite vsubst_Rec, vsubst_Succ, !vsubst_var0, vsubst_eta in Hr. cbn [aget ahd atl] in Hr.
  eapply conv_trans; [exact Hr|].
  change (conv (generated R)
            (happ (σst s) st
               (@acons _ Sym Γ (ι N) _ (vsubst_tms (σ := ι N) (var0 (vs (vs vz)))
                    (@acons _ Sym Γ (ι s) _ z (@acons _ Sym Γ (σst s) _ st (@acons _ Sym Γ (ι N) _ m anil))))
                  (@acons _ Sym Γ (ι s) _ (vsubst_tms (σ := ι s)
                       (Rec s h (var0 vz) (eta (σst s) (Γ := [ι s; σst s; ι N]) (vs vz)) (var0 (vs (vs vz))))
                    (@acons _ Sym Γ (ι s) _ z (@acons _ Sym Γ (σst s) _ st (@acons _ Sym Γ (ι N) _ m anil))))
                  anil)))
            (vsubst st (@acons _ Sym Γ (ι N) _ m (@acons _ Sym Γ (ι s) _ (Rec s h z st m) (vid Γ))))).
  rewrite !vsubst_tms_nil, vsubst_Rec, !vsubst_var0, vsubst_eta, happ_vsubst. cbn [aget ahd atl vcat].
  apply conv_refl.
Qed.

End RecConv.

(** ** Règles logiques : récurrence et S ≠ 0 *)

Section Logic.

Context {Srt : Type} {Sym : spec Srt -> Type} `{Functional Srt Sym} {G : Graded Sym}.
Context {N : Srt} {r : bound} {AR : Arithmetic Sym N r} (P : Srt).

Local Notation σφ := (Spec [ι N] P).
Local Notation form := (form Sym P).

Definition mkr' (Θ : ctx Srt) (ps : list (premise Sym P Θ)) (c : form Θ) : drule Sym P :=
  {| d_ctx := Θ; d_prems := ps; d_concl := c |}.

(** Récurrence : φ(0), et φ(x) ⊢ φ(S x) pour x frais, donnent φ(t). *)
Definition ind_rule : drule Sym P :=
  mkr' [σφ; ι N]
    [prem (P := P) (Θ := [σφ; ι N]) [] (app1 (s := N) vz Zero);
     premx (P := P) [ι N] [app1 (s := N) (vs vz) (var0 vz)] (app1 (s := N) (vs vz) (Succ (var0 vz)))]
    (app1 (s := N) vz (var0 (vs vz))).

Definition ind_rules (u : unit) : drule Sym P := ind_rule.

(** S t ≠ 0. *)
Definition peano_rules {HQ : HasEq Sym P N} {HB : HasBot Sym P} (u : unit) : drule Sym P :=
  mkr' [ι N] [prem (P := P) (Θ := [ι N]) [] (Eq N (Succ (var0 vz)) Zero)] Bot.

End Logic.

Arguments ind_rules {Srt Sym _ G N r _} P u.
Arguments peano_rules {Srt Sym _ G N r _} P {_ _} u.

Section LogicDerived.

Context {Srt : Type} {Sym : spec Srt -> Type} `{Functional Srt Sym} {G : Graded Sym}.
Context {N : Srt} {r : bound} {AR : Arithmetic Sym N r} {P : Srt}.
Context (C : system Sym) {I : Type} (R : I -> drule Sym P).

Local Notation σφ := (Spec [ι N] P).
Local Notation form := (form Sym P).
Local Notation tm := (Terms.tm Sym).
Local Notation "Ξ ⊢ φ" := (deriv C P R _ Ξ φ) (at level 70).

Lemma vsubst_app1_gen {Θ Γ} (x : var Θ σφ) (t : tm Θ N) (v : vec Sym Θ Γ) :
  vsubst (app1 x t) v = vsubst (aget x v) (inst1 (vsubst t v)).
Proof.
  change (happ σφ (aget x v) (@acons _ Sym Γ (ι N) _ (vsubst_tms (σ := ι N) t v) anil)
          = vsubst (aget x v) (inst1 (vsubst t v))).
  rewrite vsubst_tms_nil, happ_vsubst; reflexivity.
Qed.

(** Affaiblir sous le lieur, puis remettre la variable 0 : identité. *)
Lemma vsubst_shift_inst1 {Γ} a b (u : tm (ι a :: Γ) b) :
  vsubst (ren_tms (σ := Spec [ι a] b) u (wk [ι a])) (inst1 (var0 vz)) = u.
Proof.
  unfold ren_tms; rewrite vsubst_ren. rewrite <- (vsubst_vid u) at 2. f_equal.
  apply vec_ext; intros σ x; unfold vget; rewrite aget_vpre.
  vcase x; autorewrite with vsimpl; [|reflexivity].
  revert σ z. refine (var_inv _ _ _); [reflexivity|intros σ' y; destruct (var_nil y)].
Qed.

Section Ind.
Context {HI : Includes R (ind_rules P)}.

(** Récurrence. La seconde prémisse est le pas : dans le contexte x :: Γ,
    sous l'hypothèse φ(x), dériver φ(S x). *)
Theorem induction {Γ} (Ξ : list (form Γ)) (φ : form (ι N :: Γ)) (t : tm Γ N) :
  Ξ ⊢ vsubst φ (inst1 Zero) ->
  deriv C P R (ι N :: Γ) (φ :: wk_list [ι N] Ξ)
    (vsubst (ren_tms (σ := σφ) φ (wk [ι N])) (inst1 (Succ (var0 vz)))) ->
  Ξ ⊢ vsubst φ (inst1 t).
Proof.
  intros H0 HS.
  apply (rule_inc C P R (ind_rules P) tt Ξ (@acons _ Sym Γ σφ _ φ (@acons _ Sym Γ (ι N) _ t anil)));
    cbn [ind_rules ind_rule mkr' d_ctx d_concl d_prems].
  - rewrite vsubst_app1; reflexivity.
  - intros p [<-|[<-|[]]]; unfold inst_hyps, inst_goal, vsubst_list;
      cbn [p_ext p_hyps p_goal prem premx d_ctx map app].
    + rewrite vup_nil, wk_list_nil, vsubst_app1_gen. exact H0.
    + eapply deriv_eq2; [| |exact HS].
      * f_equal. rewrite vsubst_app1_gen. unfold vup, vren; cbn [vcat ahd atl aget vmap].
        rewrite vsubst_var0. cbn [vcat ahd atl aget etas eta vl vr].
        symmetry; apply vsubst_shift_inst1.
      * rewrite vsubst_app1_gen. unfold vup, vren; cbn [vcat ahd atl aget vmap].
        rewrite vsubst_Succ, vsubst_var0. reflexivity.
Qed.
End Ind.

Section Peano.
Context {HQ : HasEq Sym P N} {HB : HasBot Sym P} {HP : Includes R (peano_rules P)}.

Theorem succ_neq_zero {Γ} (Ξ : list (form Γ)) (t : tm Γ N) : Ξ ⊢ Eq N (Succ t) Zero -> Ξ ⊢ Bot.
Proof.
  intros Ht.
  apply (rule_inc C P R (peano_rules P) tt Ξ (@acons _ Sym Γ (ι N) _ t anil));
    cbn [peano_rules mkr' d_ctx d_concl d_prems].
  - reflexivity.
  - intros p [<-|[]]; unfold inst_hyps, inst_goal, vsubst_list;
      cbn [p_ext p_hyps p_goal prem premx d_ctx map app].
    rewrite vup_nil, wk_list_nil, vsubst_Eq, vsubst_Succ, vsubst_var0, vsubst_Zero. exact Ht.
Qed.
End Peano.

End LogicDerived.
