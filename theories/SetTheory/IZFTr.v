(** * Traduction de IZF⁻ε dans IZF (élimination des définitions)

    Un terme t de sorte V dans Γ est traduit par son **graphe**
    D_t : une formule de IZF dans ι V :: Γ, où la variable 0 est la valeur
    (« y est la valeur de t »). Une formule est traduite en une formule.
    ε et ∈ deviennent ∈, ⊆ l'inclusion, ≃ et = l'égalité. Chaque symbole
    est traduit par un **gabarit**, appliqué aux traductions de ses
    arguments. *)

From Stdlib Require Import List.
Import ListNotations.
From SF.Syntax Require Import Spec Terms Renaming Eta Vectors.
From SF.Calculus Require Import System Rules.
From SF.Logic Require Import Judgment Propositional.
From SF.Functional Require Import Arrow.
From SF.Quantifiers Require Import Quant Order.
From SF.SetTheory Require Import IZFe IZF.

Local Notation ι a := (Spec [] a).

(** ** Types des traductions *)

Definition Tr (b : isort) (Γ : ctx isort) : Type :=
  zform (match b with V => ι V :: Γ | Pr => Γ end).

Fixpoint TArgs (Γ : ctx isort) (Θ : list (spec isort)) : Type :=
  match Θ with
  | [] => unit
  | σ :: Θ' => (Tr (cod σ) (dom σ ++ Γ) * TArgs Γ Θ')%type
  end.

Definition dflt (b : isort) (Γ : ctx isort) : Tr b Γ :=
  match b with V => Bot | Pr => Bot end.

(** ** Gabarits

    Un gabarit est une formule de IZF dont les métavariables (de
    spécification [V] → Pr) reçoivent les traductions des arguments ; les
    gabarits des termes ont en plus la variable 0, la valeur. La
    traduction d'un symbole est l'instance de son gabarit, ce qui rend
    génériques la congruence et la commutation aux renommages. *)

Local Notation X1 := (vs (vs vz)).
Local Notation X2 := (vs (vs (vs (vs vz)))).

(** Une relation entre valeurs : ∃a. D₁(a) ∧ ∃b. D₂(b) ∧ R(a, b)   (contexte [D₁; D₂]). *)
Definition Frel (R : zform [ι V; ι V; σP; σP]) : zform [σP; σP] :=
  zEx (And (app1 (s := V) (vs vz) x0) (zEx (And (app1 (s := V) (vs (vs (vs vz))) x0) R))).

Definition subR : zform [ι V; ι V; σP; σP] := zAll (Imp (zMem x0 x2) (zMem x0 x1)).

(** Les graphes des constructions, la valeur étant la variable 0. *)
Definition Fpair : zform [ι V; σP; σP] :=
  zEx (And (app1 (s := V) X1 x0)
           (zEx (And (app1 (s := V) X2 x0) (zAll (zIff (zMem x0 x3) (Or (zEq x0 x2) (zEq x0 x1))))))).

Definition Funion : zform [ι V; σP] :=
  zEx (And (app1 (s := V) X1 x0) (zAll (zIff (zMem x0 x2) (zEx (And (zMem x1 x0) (zMem x0 x2)))))).

Definition Fpower : zform [ι V; σP] :=
  zEx (And (app1 (s := V) X1 x0) (zAll (zIff (zMem x0 x2) (zAll (Imp (zMem x0 x1) (zMem x0 x2)))))).

(** {α ε a | P(α)} : métavariables [D; P]. *)
Definition Fsep : zform [ι V; σP; σP] :=
  zEx (And (app1 (s := V) X1 x0) (zAll (zIff (zMem x0 x2) (And (zMem x0 x1) (app1 (s := V) X2 x0))))).

(** {ψ(α) | α ε a}, par la construction totale de 1.5.11 : métavariables [D; R],
    y ≜ {z | (∀α ∈ a. ∃!β. R(α, β)) ∧ ∃α ∈ a. R(α, z)}. *)
(** ∀α ∈ a. ∃!β. R(α, β)   et   ∃α ∈ a. R(α, z). *)
Definition FnAt {Γ} (a : var Γ (ι V)) (R : var Γ σR) : zform Γ :=
  zAll (Imp (zMem x0 (var0 (vs a)))
            (zEx (And (zapp2 (vs (vs R)) x1 x0) (zAll (Imp (zapp2 (vs (vs (vs R))) x2 x0) (zEq x0 x1)))))).
Definition ExIn {Γ} (a : var Γ (ι V)) (R : var Γ σR) (z : var Γ (ι V)) : zform Γ :=
  zEx (And (zMem x0 (var0 (vs a))) (zapp2 (vs R) x0 (var0 (vs z)))).

Definition Frepl : zform [ι V; σP; σR] :=
  zEx (And (app1 (s := V) X1 x0)
           (zAll (zIff (zMem x0 x2) (And (FnAt (vs vz) (vs (vs (vs (vs vz))))) (ExIn (vs vz) (vs (vs (vs (vs vz)))) vz))))).

(** rec_{φ,ψ}(a), par la construction totale : un **essai** est un ensemble
    f de couples ⟨b, v⟩ (de Kuratowski), fonctionnel, clos vers le bas
    (si f(b) est défini et c ∈ b, f(c) l'est) et correct : f(b) est
    l'ensemble de remplacement total de 1.5.11 pour la relation
    R_f(α, β) ≜ ∃u. f(α) = u ∧ ψ(u, β). Alors
    y ≜ {z | ∃f. f essai ∧ ∃v. f(a) = v ∧ z ∈ v}.
    L'argument φ ne sert pas. *)
Section RecDefs.
Context {Γ : ctx isort}.
(** x = {b}   et   x = {b, v}. *)
Definition Sg (x b : var Γ (ι V)) : zform Γ := zAll (zIff (zMem x0 (var0 (vs x))) (zEq x0 (var0 (vs b)))).
Definition Db (x b v : var Γ (ι V)) : zform Γ :=
  zAll (zIff (zMem x0 (var0 (vs x))) (Or (zEq x0 (var0 (vs b))) (zEq x0 (var0 (vs v))))).
End RecDefs.

(** p = ⟨b, v⟩ = {{b}, {b, v}}. *)
Definition OP {Γ} (p b v : var Γ (ι V)) : zform Γ :=
  zAll (zIff (zMem x0 (var0 (vs p))) (Or (Sg vz (vs b)) (Db vz (vs b) (vs v)))).
(** ⟨b, v⟩ ∈ f. *)
Definition InF {Γ} (f b v : var Γ (ι V)) : zform Γ := zEx (And (zMem x0 (var0 (vs f))) (OP vz (vs b) (vs v))).
(** R_f(α, β) ≜ ∃u. ⟨α, u⟩ ∈ f ∧ ψ(u, β). *)
Definition RF {Γ} (f : var Γ (ι V)) (ψ : var Γ σR) (α β : var Γ (ι V)) : zform Γ :=
  zEx (And (InF (vs f) (vs α) vz) (zapp2 (vs ψ) x0 (var0 (vs β)))).
(** ∀α ∈ b. ∃!β. R_f(α, β)   et   ∃α ∈ b. R_f(α, z). *)
Definition FnR {Γ} (b f : var Γ (ι V)) (ψ : var Γ σR) : zform Γ :=
  zAll (Imp (zMem x0 (var0 (vs b)))
            (zEx (And (RF (vs (vs f)) (vs (vs ψ)) (vs vz) vz)
                      (zAll (Imp (RF (vs (vs (vs f))) (vs (vs (vs ψ))) (vs (vs vz)) vz) (zEq x0 x1)))))).
Definition ExR {Γ} (b f : var Γ (ι V)) (ψ : var Γ σR) (z : var Γ (ι V)) : zform Γ :=
  zEx (And (zMem x0 (var0 (vs b))) (RF (vs f) (vs ψ) vz (vs z))).
(** v est la valeur correcte en b : ∀β. β ∈ v ↔ Fn ∧ ∃α ∈ b. R_f(α, β). *)
Definition StepEq {Γ} (v b f : var Γ (ι V)) (ψ : var Γ σR) : zform Γ :=
  zAll (zIff (zMem x0 (var0 (vs v))) (And (FnR (vs b) (vs f) (vs ψ)) (ExR (vs b) (vs f) (vs ψ) vz))).
Definition AttFn {Γ} (f : var Γ (ι V)) : zform Γ :=
  zAll (zAll (zAll (Imp (InF (vs (vs (vs f))) (vs (vs vz)) (vs vz)) (Imp (InF (vs (vs (vs f))) (vs (vs vz)) vz) (zEq x1 x0))))).
Definition AttDc {Γ} (f : var Γ (ι V)) : zform Γ :=
  zAll (zAll (Imp (InF (vs (vs f)) (vs vz) vz)
                  (zAll (Imp (zMem x0 x2) (zEx (InF (vs (vs (vs (vs f)))) (vs vz) vz)))))).
Definition AttCr {Γ} (f : var Γ (ι V)) (ψ : var Γ σR) : zform Γ :=
  zAll (zAll (Imp (InF (vs (vs f)) (vs vz) vz) (StepEq vz (vs vz) (vs (vs f)) (vs (vs ψ))))).
Definition Att {Γ} (f : var Γ (ι V)) (ψ : var Γ σR) : zform Γ := And (AttFn f) (And (AttDc f) (AttCr f ψ)).
(** z ∈ rec(a) : ∃f. f essai ∧ ∃v. ⟨a, v⟩ ∈ f ∧ z ∈ v. *)
Definition RecV {Γ} (a : var Γ (ι V)) (ψ : var Γ σR) (z : var Γ (ι V)) : zform Γ :=
  zEx (And (Att vz (vs ψ)) (zEx (And (InF (vs vz) (vs (vs a)) vz) (zMem (var0 (vs (vs z))) x0)))).

(** Métavariables [P; R; D] (P, l'argument φ, ne sert pas). *)
Definition Frec : zform [ι V; σP; σR; σP] :=
  zEx (And (app1 (s := V) X2 x0) (zAll (zIff (zMem x0 x2) (RecV (vs vz) (vs (vs (vs (vs vz)))) vz)))).

Section Closed.
Context {Γ : ctx isort}.

Definition emptyT : zform (ι V :: Γ) := zAll (Neg (zMem x0 x1)).

Definition omegaT : zform (ι V :: Γ) :=
  zAll (zIff (zMem x0 x1)
             (Or (zAll (Neg (zMem x0 x1)))
                 (zEx (And (zMem x0 x2) (zAll (zIff (zMem x0 x2) (Or (zMem x0 x1) (zEq x0 x1)))))))).

End Closed.

Definition v1 {Γ} (D : zform (ι V :: Γ)) : vec zsym [σP] Γ := @acons _ zsym Γ σP _ D anil.
Definition v2 {Γ} (D1 D2 : zform (ι V :: Γ)) : vec zsym [σP; σP] Γ :=
  @acons _ zsym Γ σP _ D1 (@acons _ zsym Γ σP _ D2 anil).
Definition vPR {Γ} (D : zform (ι V :: Γ)) (R : zform (ι V :: ι V :: Γ)) : vec zsym [σP; σR] Γ :=
  @acons _ zsym Γ σP _ D (@acons _ zsym Γ σR _ R anil).
Definition vrec {Γ} (P : zform (ι V :: Γ)) (R : zform (ι V :: ι V :: Γ)) (D : zform (ι V :: Γ)) : vec zsym [σP; σR; σP] Γ :=
  @acons _ zsym Γ σP _ P (@acons _ zsym Γ σR _ R (@acons _ zsym Γ σP _ D anil)).

(** ** Traduction des symboles et des variables *)

Definition tsymT {Γ σ} (c : isym σ) : TArgs Γ (dom σ) -> Tr (cod σ) Γ :=
  match c in isym σ0 return TArgs Γ (dom σ0) -> Tr (cod σ0) Γ with
  | i_imp => fun '(A, (B, _)) => Imp A B
  | i_and => fun '(A, (B, _)) => And A B
  | i_or => fun '(A, (B, _)) => Or A B
  | i_top => fun _ => Top
  | i_bot => fun _ => Bot
  | i_all => fun '(A, _) => zAll A
  | i_ex => fun '(A, _) => zEx A
  | i_eq => fun '(D1, (D2, _)) => vsubst (Frel (zEq x1 x0)) (v2 D1 D2)
  | i_eps => fun '(D1, (D2, _)) => vsubst (Frel (zMem x1 x0)) (v2 D1 D2)
  | i_mem => fun '(D1, (D2, _)) => vsubst (Frel (zMem x1 x0)) (v2 D1 D2)
  | i_sub => fun '(D1, (D2, _)) => vsubst (Frel subR) (v2 D1 D2)
  | i_eqv => fun '(D1, (D2, _)) => vsubst (Frel (zEq x1 x0)) (v2 D1 D2)
  | i_empty => fun _ => emptyT
  | i_omega => fun _ => omegaT
  | i_pair => fun '(D1, (D2, _)) => vsubst Fpair (vup [ι V] (v2 D1 D2))
  | i_union => fun '(D, _) => vsubst Funion (vup [ι V] (v1 D))
  | i_power => fun '(D, _) => vsubst Fpower (vup [ι V] (v1 D))
  | i_sep => fun '(D, (P, _)) => vsubst Fsep (vup [ι V] (v2 D P))
  | i_repl => fun '(D, (R, _)) => vsubst Frepl (vup [ι V] (vPR D R))
  | i_rec => fun '(P, (R, (D, _))) => vsubst Frec (vup [ι V] (vrec P R D))
  end.

Definition tvarT {Γ σ} : var Γ σ -> TArgs Γ (dom σ) -> Tr (cod σ) Γ :=
  match σ as σ0 return var Γ σ0 -> TArgs Γ (dom σ0) -> Tr (cod σ0) Γ with
  | Spec [] V => fun x _ => zEq x0 (var0 (vs x))
  | Spec [] Pr => fun x _ => @tvar _ zsym Γ (ι Pr) x anil
  | Spec _ b => fun _ _ => dflt b Γ
  end.

Fixpoint ttm {Γ s} (t : tm Γ s) {struct t} : Tr s Γ :=
  match t in Terms.tm _ Γ0 s0 return Tr s0 Γ0 with
  | tvar x a => tvarT x (targs a)
  | tsym c a => tsymT c (targs a)
  end
with targs {Γ Θ} (a : args isym Γ Θ) {struct a} : TArgs Γ Θ :=
  match a in args _ Γ0 Θ0 return TArgs Γ0 Θ0 with
  | anil => tt
  | acons u a' => (ttm u, targs a')
  end.

Definition tr {Γ} (φ : form Γ) : zform Γ := ttm φ.

(** ** Commutation aux renommages *)

Definition renT {Γ Δ} (b : isort) : Tr b Γ -> ren Γ Δ -> Tr b Δ :=
  match b as b0 return Tr b0 Γ -> ren Γ Δ -> Tr b0 Δ with
  | V => fun A ρ => ren_tm A (upr [ι V] ρ)
  | Pr => fun A ρ => ren_tm A ρ
  end.

Fixpoint renA {Γ Δ} (Θ : list (spec isort)) : TArgs Γ Θ -> ren Γ Δ -> TArgs Δ Θ :=
  match Θ as Θ0 return TArgs Γ Θ0 -> ren Γ Δ -> TArgs Δ Θ0 with
  | [] => fun _ _ => tt
  | σ :: Θ' => fun X ρ => (renT (cod σ) (fst X) (upr (dom σ) ρ), renA Θ' (snd X) ρ)
  end.

Lemma vren_vup Λ {Δ Γ Γ'} (w : vec zsym Δ Γ) (ξ : ren Γ Γ') :
  vren (vup Λ w) (upr Λ ξ) = vup Λ (vren w ξ).
Proof.
  apply vec_ext; intros σ x; unfold vget, vup, vren. rewrite !aget_vmap. vcase x.
  - rewrite !aget_vcat_l, !aget_etas, eta_ren, upr_vl. reflexivity.
  - rewrite !aget_vcat_r, !aget_vmap, !ren_tms_ren. apply ren_tms_ext. intros ρ y. unfold rcomp, wk.
    rewrite upr_vr. reflexivity.
Qed.

Lemma ren_vsubst_vup {Θ Γ Δ} (F : zform (ι V :: Θ)) (v : vec zsym Θ Γ) (ρ : ren Γ Δ) :
  @ren_tm _ zsym (ι V :: Γ) Pr (vsubst F (vup [ι V] v)) (ι V :: Δ) (upr [ι V] ρ) = vsubst F (vup [ι V] (vren v ρ)).
Proof. rewrite ren_vsubst. f_equal. exact (vren_vup [ι V] v ρ). Qed.

Lemma tvarT_ren {Γ Δ σ} (x : var Γ σ) (X : TArgs Γ (dom σ)) (ρ : ren Γ Δ) :
  tvarT (ρ σ x) (renA (dom σ) X ρ) = renT (cod σ) (tvarT x X) ρ.
Proof. destruct σ as [[|σ1 D] [|]]; reflexivity. Qed.

Ltac tren1 := etransitivity; [|symmetry; apply ren_vsubst_vup]; reflexivity.

Lemma tsymT_ren {Γ Δ σ} (c : isym σ) (X : TArgs Γ (dom σ)) (ρ : ren Γ Δ) :
  tsymT c (renA (dom σ) X ρ) = renT (cod σ) (tsymT c X) ρ.
Proof.
  destruct c; cbn [TArgs dom cod app] in X; repeat match goal with p : (_ * _)%type |- _ => destruct p end;
    cbn [tsymT renA renT fst snd dom cod];
    first [ tren1 | (rewrite ?ren_vsubst; reflexivity) ].
Qed.

Lemma ttm_ren_mut :
  (forall Γ s (t : tm Γ s) Δ (ρ : ren Γ Δ), ttm (ren_tm t ρ) = renT s (ttm t) ρ) /\
  (forall Γ Θ (a : args isym Γ Θ) Δ (ρ : ren Γ Δ), targs (ren_args a ρ) = renA Θ (targs a) ρ).
Proof.
  apply tm_args_ind.
  - intros Γ σ x a IH Δ ρ. cbn. rewrite IH. apply tvarT_ren.
  - intros Γ σ c a IH Δ ρ. cbn. rewrite IH. apply tsymT_ren.
  - reflexivity.
  - intros Γ σ Θ u IHu a IHa Δ ρ. cbn. rewrite IHu, IHa. reflexivity.
Qed.

Lemma tr_ren {Γ Δ} (φ : form Γ) (ρ : ren Γ Δ) : tr (ren_tm φ ρ) = ren_tm (tr φ) ρ.
Proof. exact (proj1 ttm_ren_mut Γ Pr φ Δ ρ). Qed.

Lemma ttmV_ren {Γ Δ} (t : tm Γ V) (ρ : ren Γ Δ) : ttm (ren_tm t ρ) = ren_tm (ttm t) (upr [ι V] ρ).
Proof. exact (proj1 ttm_ren_mut Γ V t Δ ρ). Qed.
