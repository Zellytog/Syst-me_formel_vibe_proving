(** * IZFε : la théorie des ensembles intensionnelle intuitionniste

    D'après les notes « Notes on IZFε » (T. Leclercq). Deux sortes : V (les
    ensembles) et Pr (les propositions). Le langage :

      ε, ∈, ⊆, ≃ : [V, V] → Pr        (ε primitive, les autres définies)
      ∅, ω : V      {_, _} : [V, V] → V      ⋃, P : [V] → V
      Sep  : [V, [V] → Pr] → V          {α ε a | φ(α)}
      Repl : [V, [V, V] → Pr] → V       {ψ(α) | α ε a}  (ψ(α, β) : β image de α)
      Rec  : [[V] → Pr, [V, V] → Pr, V] → V   rec_{φ,ψ}(a)

    Dans les notes, les schémas sont skolémisés par une hiérarchie de
    langages Lₙ (un symbole par formule). Ici, ce sont des **lieurs** : la
    formule est un argument du symbole, et les paramètres sont les
    variables du contexte. La hiérarchie disparaît.

    La logique est la logique intuitionniste du premier ordre sur V (ordre
    (1,1) : on quantifie sur V, pas sur Pr), avec l'égalité de Leibniz =
    sur V, l'égalité intensionnelle. Les axiomes sont des règles sans
    prémisse, les schémas des règles à métavariables de formule :
    - [izfm_rules] : IZF⁻ε (définition 1.3.2) ;
    - [izfe_extra] : les axiomes supplémentaires de IZFε (définition 1.3.3).

    Les axiomes sont des règles de **déduction**, pas des conversions : dans
    les modèles de réalisabilité, ils ne valent qu'à équivalence uniforme
    près. *)

From Stdlib Require Import List Arith Lia.
Import ListNotations.
From SF.Syntax Require Import Spec Terms Vectors.
From SF.Calculus Require Import System Rules.
From SF.Logic Require Import Judgment Propositional.
From SF.Functional Require Import Arrow Graded.
From SF.Quantifiers Require Import Quant Order.

Inductive isort := V | Pr.

Local Notation ι a := (Spec [] a).
Notation σP := (Spec [ι V] Pr).
Notation σR := (Spec [ι V; ι V] Pr).

Inductive isym : spec isort -> Type :=
| i_imp : isym (Spec [ι Pr; ι Pr] Pr)
| i_and : isym (Spec [ι Pr; ι Pr] Pr)
| i_or  : isym (Spec [ι Pr; ι Pr] Pr)
| i_top : isym (ι Pr)
| i_bot : isym (ι Pr)
| i_all : isym (Spec [σP] Pr)
| i_ex  : isym (Spec [σP] Pr)
| i_eq  : isym (Spec [ι V; ι V] Pr)
| i_eps : isym (Spec [ι V; ι V] Pr)
| i_mem : isym (Spec [ι V; ι V] Pr)
| i_sub : isym (Spec [ι V; ι V] Pr)
| i_eqv : isym (Spec [ι V; ι V] Pr)
| i_empty : isym (ι V)
| i_omega : isym (ι V)
| i_pair : isym (Spec [ι V; ι V] V)
| i_union : isym (Spec [ι V] V)
| i_power : isym (Spec [ι V] V)
| i_sep : isym (Spec [ι V; σP] V)
| i_repl : isym (Spec [ι V; σR] V)
| i_rec : isym (Spec [σP; σR; ι V] V).

#[export] Instance i_hasimp : HasImp isym Pr := {| c_imp := i_imp |}.
#[export] Instance i_hasand : HasAnd isym Pr := {| c_and := i_and |}.
#[export] Instance i_hasor  : HasOr isym Pr  := {| c_or := i_or |}.
#[export] Instance i_hastop : HasTop isym Pr := {| c_top := i_top |}.
#[export] Instance i_hasbot : HasBot isym Pr := {| c_bot := i_bot |}.

#[export] Instance i_functional : Functional isym := {|
  Arr := fun _ _ _ => Empty_set;
  s_lam := fun a b c w => match w with end;
  s_app := fun a b c w => match w with end
|}.

Definition i_grade (s : isort) : grade := match s with V => (0, 0) | Pr => (0, 1) end.

Lemma i_gr_arr a b c (w : @Arr _ isym i_functional a b c) : i_grade c = garr (i_grade a) (i_grade b).
Proof. destruct w. Qed.

#[export] Instance i_graded : Graded isym := {| gr := i_grade; gr_arr := i_gr_arr |}.

Lemma hV : quantifiable (Sym := isym) 1 1 V.
Proof. split; cbn; lia. Qed.
Lemma Pr_not_q : ~ quantifiable (Sym := isym) 1 1 Pr.
Proof. intros [_ H]; cbn in H; lia. Qed.

Definition qa (s : isort) : quantifiable (Sym := isym) 1 1 s -> isym (Spec [Spec [ι s] Pr] Pr) :=
  match s with V => fun _ => i_all | Pr => fun h => False_rect _ (Pr_not_q h) end.
Definition qe (s : isort) : quantifiable (Sym := isym) 1 1 s -> isym (Spec [Spec [ι s] Pr] Pr) :=
  match s with V => fun _ => i_ex | Pr => fun h => False_rect _ (Pr_not_q h) end.
Definition qq (s : isort) : quantifiable (Sym := isym) 1 1 s -> isym (Spec [ι s; ι s] Pr) :=
  match s with V => fun _ => i_eq | Pr => fun h => False_rect _ (Pr_not_q h) end.

#[export] Instance i_quant : Quantifiers isym Pr 1 1 := {| q_all := qa; q_ex := qe; q_eq := qq |}.

#[export] Instance i_forallV : HasForall isym Pr V := qall_inst (existT _ V hV).
#[export] Instance i_existsV : HasExists isym Pr V := qex_inst (existT _ V hV).
#[export] Instance i_eqV : HasEq isym Pr V := qeq_inst (existT _ V hV).

(** ** Les termes *)

Notation tm := (Terms.tm isym).
Notation form Γ := (Judgment.form isym Pr Γ).

Section Syn.
Context {Γ : ctx isort}.

Definition rel2 (c : isym (Spec [ι V; ι V] Pr)) (x y : tm Γ V) : form Γ :=
  @tsym _ isym Γ _ c (@acons _ isym Γ (ι V) _ x (@acons _ isym Γ (ι V) _ y anil)).

Definition Eps := rel2 i_eps.
Definition Mem := rel2 i_mem.
Definition Sub := rel2 i_sub.
Definition Eqv := rel2 i_eqv.
Definition EqV (x y : tm Γ V) : form Γ := Eq V x y.

Definition Empty : tm Γ V := @tsym _ isym Γ (ι V) i_empty anil.
Definition Omega : tm Γ V := @tsym _ isym Γ (ι V) i_omega anil.
Definition Pair (a b : tm Γ V) : tm Γ V :=
  @tsym _ isym Γ _ i_pair (@acons _ isym Γ (ι V) _ a (@acons _ isym Γ (ι V) _ b anil)).
Definition Union (a : tm Γ V) : tm Γ V := @tsym _ isym Γ _ i_union (@acons _ isym Γ (ι V) _ a anil).
Definition Power (a : tm Γ V) : tm Γ V := @tsym _ isym Γ _ i_power (@acons _ isym Γ (ι V) _ a anil).
(** {α ε a | φ}, où α est la variable 0 de φ. *)
Definition Sep (a : tm Γ V) (φ : tm (ι V :: Γ) Pr) : tm Γ V :=
  @tsym _ isym Γ _ i_sep (@acons _ isym Γ (ι V) _ a (@acons _ isym Γ σP _ φ anil)).
(** {ψ(α) | α ε a}, où, dans ψ, α est la variable 0 et β la variable 1. *)
Definition Repl (a : tm Γ V) (ψ : tm (ι V :: ι V :: Γ) Pr) : tm Γ V :=
  @tsym _ isym Γ _ i_repl (@acons _ isym Γ (ι V) _ a (@acons _ isym Γ σR _ ψ anil)).
(** rec_{φ,ψ}(a) ; dans ψ, la valeur récursive f est la variable 0 et β la variable 1. *)
Definition Rec (φ : tm (ι V :: Γ) Pr) (ψ : tm (ι V :: ι V :: Γ) Pr) (a : tm Γ V) : tm Γ V :=
  @tsym _ isym Γ _ i_rec (@acons _ isym Γ σP _ φ (@acons _ isym Γ σR _ ψ (@acons _ isym Γ (ι V) _ a anil))).

Definition Sing (a : tm Γ V) : tm Γ V := Pair a a.
(** Le successeur : S x ≜ ⋃{x, {x, x}} (définition 1.4.1). *)
Definition Suc (a : tm Γ V) : tm Γ V := Union (Pair a (Sing a)).
(** Le couple ⟨a, b⟩ ≜ {{a, a}, {a, b}} (définition 1.4.3). *)
Definition OPair (a b : tm Γ V) : tm Γ V := Pair (Sing a) (Pair a b).

Definition Iff (φ ψ : form Γ) : form Γ := And (Imp φ ψ) (Imp ψ φ).

(** Application d'une métavariable binaire. *)
Definition app2 (x : var Γ σR) (t u : tm Γ V) : form Γ :=
  @tvar _ isym Γ σR x (@acons _ isym Γ (ι V) _ t (@acons _ isym Γ (ι V) _ u anil)).

End Syn.

Notation All := (All V).
Notation Ex := (Ex V).
Notation x0 := (var0 vz).
Notation x1 := (var0 (vs vz)).
Notation x2 := (var0 (vs (vs vz))).
Notation x3 := (var0 (vs (vs (vs vz)))).
Notation x4 := (var0 (vs (vs (vs (vs vz))))).

(** ∃!β. χ(β) := ∃β. χ(β) ∧ ∀β'. χ(β') → β' = β. *)
Definition ExU {Γ} (χ : form (ι V :: Γ)) : form Γ :=
  Ex (And χ (All (Imp (vsubst χ (@acons _ isym _ (ι V) _ x0 (vren (vid _) (wk [ι V; ι V]))))
                      (EqV x0 x1)))).

(** ** Les axiomes de IZF⁻ε (définition 1.3.2) *)

Definition ax (Θ : ctx isort) (φ : form Θ) : drule isym Pr :=
  {| d_ctx := Θ; d_prems := []; d_concl := φ |}.

Inductive izfm_idx :=
| A_mem | A_sub | A_eqv | A_pair | A_union | A_power | A_coll | A_sep | A_empty | A_omega | A_ind.

(** Les métavariables : ensembles x, y, … (variable 0 en tête), puis les
    métavariables de formule. *)
Definition izfm_rules (i : izfm_idx) : drule isym Pr :=
  match i with
  (* x ∈ y ↔ ∃a. x ≃ a ∧ a ε y *)
  | A_mem => ax [ι V; ι V] (Iff (Mem x0 x1) (Ex (And (Eqv x1 x0) (Eps x0 x2))))
  (* x ⊆ y ↔ ∀a. a ε x → a ∈ y *)
  | A_sub => ax [ι V; ι V] (Iff (Sub x0 x1) (All (Imp (Eps x0 x1) (Mem x0 x2))))
  (* x ≃ y ↔ x ⊆ y ∧ y ⊆ x *)
  | A_eqv => ax [ι V; ι V] (Iff (Eqv x0 x1) (And (Sub x0 x1) (Sub x1 x0)))
  (* z ε {x, y} ↔ z = x ∨ z = y *)
  | A_pair => ax [ι V; ι V; ι V] (Iff (Eps x0 (Pair x1 x2)) (Or (EqV x0 x1) (EqV x0 x2)))
  (* z ε ⋃x ↔ ∃b. z ε b ∧ b ε x *)
  | A_union => ax [ι V; ι V] (Iff (Eps x0 (Union x1)) (Ex (And (Eps x1 x0) (Eps x0 x2))))
  (* ∃b. b ε P(x) ∧ ∀z. z ε b ↔ z ε x ∧ z ε a   (x, a) *)
  | A_power => ax [ι V; ι V]
      (Ex (And (Eps x0 (Power x1)) (All (Iff (Eps x0 x1) (And (Eps x0 x2) (Eps x0 x3))))))
  (* (∀α. α ε a → ∃β. ψ(α, β)) → ∃b. ∀α. α ε a → ∃β. β ε b ∧ ψ(α, β)   (a, ψ) *)
  | A_coll => ax [ι V; σR]
      (Imp (All (Imp (Eps x0 x1) (Ex (app2 (vs (vs (vs vz))) x1 x0))))
           (Ex (All (Imp (Eps x0 x2) (Ex (And (Eps x0 x2) (app2 (vs (vs (vs (vs vz)))) x1 x0)))))))
  (* α ε {α ε a | φ} ↔ α ε a ∧ φ(α)   (α, a, φ) *)
  | A_sep => ax [ι V; ι V; σP]
      (Iff (Eps x0 (Sep x1 (eta σP (Γ := [ι V; ι V; σP]) (vs (vs vz)))))
           (And (Eps x0 x1) (app1 (s := V) (vs (vs vz)) x0)))
  (* ¬ (x ε ∅) *)
  | A_empty => ax [ι V] (Neg (Eps x0 Empty))
  (* a ε ω ↔ a = ∅ ∨ ∃b. b ε ω ∧ a = S b *)
  | A_omega => ax [ι V] (Iff (Eps x0 Omega) (Or (EqV x0 Empty) (Ex (And (Eps x0 Omega) (EqV x1 (Suc x0))))))
  (* (∀a. (∀b. b ε a → φ(b)) → φ(a)) → ∀a. φ(a)   (φ) *)
  | A_ind => ax [σP]
      (Imp (All (Imp (All (Imp (Eps x0 x1) (app1 (s := V) (vs (vs vz)) x0))) (app1 (s := V) (vs vz) x0)))
           (All (app1 (s := V) (vs vz) x0)))
  end.

(** ** Les axiomes supplémentaires de IZFε (définition 1.3.3) *)

Inductive izfe_idx := A_rec | A_repl | A_sep_power | A_power_sub.

(** rec_{φ,ψ}(α) dans un contexte où φ et ψ sont des métavariables. *)
Definition RecM {Γ} (xφ : var Γ σP) (xψ : var Γ σR) (t : tm Γ V) : tm Γ V :=
  Rec (eta σP xφ) (eta σR xψ) t.

Definition izfe_extra (i : izfe_idx) : drule isym Pr :=
  match i with
  (* (∀a. φ(a) → ∀α. α ε a → φ(α) ∧ ∃!β. ψ(rec α, β))
     → ∀a. φ(a) → ∀β. β ε rec(a) ↔ ∃α. α ε a ∧ ψ(rec α, β)     (φ, ψ) *)
  | A_rec => ax [σP; σR]
      (Imp (All (Imp (app1 (s := V) (vs vz) x0)
                     (All (Imp (Eps x0 x1)
                               (And (app1 (s := V) (vs (vs vz)) x0)
                                    (ExU (app2 (vs (vs (vs (vs vz))))
                                               (RecM (vs (vs (vs vz))) (vs (vs (vs (vs vz)))) x1) x0)))))))
           (All (Imp (app1 (s := V) (vs vz) x0)
                     (All (Iff (Eps x0 (RecM (vs (vs vz)) (vs (vs (vs vz))) x1))
                               (Ex (And (Eps x0 x2)
                                        (app2 (vs (vs (vs (vs vz))))
                                              (RecM (vs (vs (vs vz))) (vs (vs (vs (vs vz)))) x0) x1))))))))
  (* (∀α. α ε a → ∃!β. ψ(α, β)) → ∀β. β ε {ψ(α) | α ε a} ↔ ∃α. α ε a ∧ ψ(α, β)   (a, ψ) *)
  | A_repl => ax [ι V; σR]
      (Imp (All (Imp (Eps x0 x1) (ExU (app2 (vs (vs (vs vz))) x1 x0))))
           (All (Iff (Eps x0 (Repl x1 (eta σR (Γ := ι V :: ι V :: σR :: []) (vs (vs vz)))
                                       ))
                     (Ex (And (Eps x0 x2) (app2 (vs (vs (vs vz))) x0 x1))))))
  (* {α ε a | φ} ε P(a)   (a, φ) *)
  | A_sep_power => ax [ι V; σP] (Eps (Sep x0 (eta σP (Γ := [ι V; σP]) (vs vz))) (Power x0))
  (* a ε P(x) → ∃b. ∀α. α ε a ↔ α ε x ∧ α ε b   (x, a) *)
  | A_power_sub => ax [ι V; ι V]
      (Imp (Eps x1 (Power x0)) (Ex (All (Iff (Eps x0 x3) (And (Eps x0 x2) (Eps x0 x1))))))
  end.

(** ** Les deux théories *)

Definition C : system isym := generated (fun e : Empty_set => match e with end).

Definition RIZFm := rsum (iorder_rules (Sym := isym) (P := Pr) (n := 1) (p := 1)) izfm_rules.
Definition RIZFe := rsum RIZFm izfe_extra.

#[export] Typeclasses Transparent RIZFm RIZFe.
#[export] Hint Unfold RIZFm RIZFe : typeclass_instances.

Notation IZFm Γ Ξ φ := (deriv C Pr RIZFm Γ Ξ φ).
Notation IZFe Γ Ξ φ := (deriv C Pr RIZFe Γ Ξ φ).
