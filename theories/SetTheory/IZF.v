(** * IZF, théorie à part

    La signature n'a qu'un symbole non logique, ∈ ; l'égalité est
    l'égalité de Leibniz de la logique d'ordre (1,1) sur V. Les axiomes
    sont ceux que [IZFeIZF.v] dérive dans IZF⁻ε (l'égalité ≃ y devient =) :
    extensionnalité, paire, réunion, parties, infini, séparation,
    collection, ∈-induction. *)

From Stdlib Require Import List Lia.
Import ListNotations.
From SF.Syntax Require Import Spec Terms Vectors.
From SF.Calculus Require Import System Rules.
From SF.Logic Require Import Judgment Propositional.
From SF.Functional Require Import Arrow Graded.
From SF.Quantifiers Require Import Quant Order.
From SF.SetTheory Require Import IZFe.

Local Notation ι a := (Spec [] a).

Inductive zsym : spec isort -> Type :=
| z_imp : zsym (Spec [ι Pr; ι Pr] Pr)
| z_and : zsym (Spec [ι Pr; ι Pr] Pr)
| z_or  : zsym (Spec [ι Pr; ι Pr] Pr)
| z_top : zsym (ι Pr)
| z_bot : zsym (ι Pr)
| z_all : zsym (Spec [σP] Pr)
| z_ex  : zsym (Spec [σP] Pr)
| z_eq  : zsym (Spec [ι V; ι V] Pr)
| z_mem : zsym (Spec [ι V; ι V] Pr).

#[export] Instance z_hasimp : HasImp zsym Pr := {| c_imp := z_imp |}.
#[export] Instance z_hasand : HasAnd zsym Pr := {| c_and := z_and |}.
#[export] Instance z_hasor  : HasOr zsym Pr  := {| c_or := z_or |}.
#[export] Instance z_hastop : HasTop zsym Pr := {| c_top := z_top |}.
#[export] Instance z_hasbot : HasBot zsym Pr := {| c_bot := z_bot |}.

#[export] Instance z_functional : Functional zsym := {|
  Arr := fun _ _ _ => Empty_set;
  s_lam := fun a b c w => match w with end;
  s_app := fun a b c w => match w with end
|}.

Lemma z_gr_arr a b c (w : @Arr _ zsym z_functional a b c) : i_grade c = garr (i_grade a) (i_grade b).
Proof. destruct w. Qed.

#[export] Instance z_graded : Graded zsym := {| gr := i_grade; gr_arr := z_gr_arr |}.

Lemma hZ : quantifiable (Sym := zsym) 1 1 V.
Proof. split; cbn; lia. Qed.

Lemma Pr_not_qz : ~ quantifiable (Sym := zsym) 1 1 Pr.
Proof. intros [_ H]; cbn in H; lia. Qed.

Definition zqa (s : isort) : quantifiable (Sym := zsym) 1 1 s -> zsym (Spec [Spec [ι s] Pr] Pr) :=
  match s with V => fun _ => z_all | Pr => fun h => False_rect _ (Pr_not_qz h) end.
Definition zqe (s : isort) : quantifiable (Sym := zsym) 1 1 s -> zsym (Spec [Spec [ι s] Pr] Pr) :=
  match s with V => fun _ => z_ex | Pr => fun h => False_rect _ (Pr_not_qz h) end.
Definition zqq (s : isort) : quantifiable (Sym := zsym) 1 1 s -> zsym (Spec [ι s; ι s] Pr) :=
  match s with V => fun _ => z_eq | Pr => fun h => False_rect _ (Pr_not_qz h) end.

#[export] Instance z_quant : Quantifiers zsym Pr 1 1 := {| q_all := zqa; q_ex := zqe; q_eq := zqq |}.
#[export] Instance z_forallV : HasForall zsym Pr V := qall_inst (existT _ V hZ).
#[export] Instance z_existsV : HasExists zsym Pr V := qex_inst (existT _ V hZ).
#[export] Instance z_eqV : HasEq zsym Pr V := qeq_inst (existT _ V hZ).

Notation ztm := (Terms.tm zsym).
Notation zform Γ := (Judgment.form zsym Pr Γ).

Section Syn.
Context {Γ : ctx isort}.
Definition zMem (x y : ztm Γ V) : zform Γ :=
  @tsym _ zsym Γ _ z_mem (@acons _ zsym Γ (ι V) _ x (@acons _ zsym Γ (ι V) _ y anil)).
Definition zEq (x y : ztm Γ V) : zform Γ := Eq V x y.
Definition zIff (φ ψ : zform Γ) : zform Γ := And (Imp φ ψ) (Imp ψ φ).
Definition zapp2 (x : var Γ σR) (t u : ztm Γ V) : zform Γ :=
  @tvar _ zsym Γ σR x (@acons _ zsym Γ (ι V) _ t (@acons _ zsym Γ (ι V) _ u anil)).
End Syn.

Notation zAll := (Quant.All (Sym := zsym) V).
Notation zEx := (Quant.Ex (Sym := zsym) V).

(** ** Les axiomes *)

Definition zax (Θ : ctx isort) (φ : zform Θ) : drule zsym Pr :=
  {| d_ctx := Θ; d_prems := []; d_concl := φ |}.

Inductive izf_idx := Z_ext | Z_pair | Z_union | Z_power | Z_inf | Z_sep | Z_coll | Z_ind.

Definition izf_rules (i : izf_idx) : drule zsym Pr :=
  match i with
  (* ∀x y. (∀z. z ∈ x ↔ z ∈ y) → x = y *)
  | Z_ext => zax [] (zAll (zAll (Imp (zAll (zIff (zMem x0 x2) (zMem x0 x1))) (zEq x1 x0))))
  (* ∀x y. ∃p. ∀z. z ∈ p ↔ z = x ∨ z = y *)
  | Z_pair => zax [] (zAll (zAll (zEx (zAll (zIff (zMem x0 x1) (Or (zEq x0 x3) (zEq x0 x2)))))))
  (* ∀x. ∃u. ∀z. z ∈ u ↔ ∃b. z ∈ b ∧ b ∈ x *)
  | Z_union => zax [] (zAll (zEx (zAll (zIff (zMem x0 x1) (zEx (And (zMem x1 x0) (zMem x0 x3)))))))
  (* ∀x. ∃p. ∀a. (∀z. z ∈ a → z ∈ x) → a ∈ p *)
  | Z_power => zax [] (zAll (zEx (zAll (Imp (zAll (Imp (zMem x0 x1) (zMem x0 x3))) (zMem x0 x1)))))
  (* ∃w. (∃e. e ∈ w ∧ ∀z. ¬ z ∈ e) ∧ ∀n. n ∈ w → ∃m. m ∈ w ∧ ∀z. z ∈ m ↔ z ∈ n ∨ z = n *)
  | Z_inf => zax []
      (zEx (And (zEx (And (zMem x0 x1) (zAll (Neg (zMem x0 x1)))))
                (zAll (Imp (zMem x0 x1) (zEx (And (zMem x0 x2) (zAll (zIff (zMem x0 x1) (Or (zMem x0 x2) (zEq x0 x2))))))))))
  (* ∀a. ∃s. ∀b. b ∈ s ↔ b ∈ a ∧ φ(b)   (φ) *)
  | Z_sep => zax [σP] (zAll (zEx (zAll (zIff (zMem x0 x1) (And (zMem x0 x2) (app1 (s := V) (vs (vs (vs vz))) x0))))))
  (* ∀a. (∀α. α ∈ a → ∃β. ψ(α, β)) → ∃c. ∀α. α ∈ a → ∃β. β ∈ c ∧ ψ(α, β)   (ψ) *)
  | Z_coll => zax [σR]
      (zAll (Imp (zAll (Imp (zMem x0 x1) (zEx (zapp2 (vs (vs (vs vz))) x1 x0))))
                 (zEx (zAll (Imp (zMem x0 x2) (zEx (And (zMem x0 x2) (zapp2 (vs (vs (vs (vs vz)))) x1 x0))))))))
  (* (∀a. (∀b. b ∈ a → φ(b)) → φ(a)) → ∀a. φ(a)   (φ) *)
  | Z_ind => zax [σP]
      (Imp (zAll (Imp (zAll (Imp (zMem x0 x1) (app1 (s := V) (vs (vs vz)) x0))) (app1 (s := V) (vs vz) x0)))
           (zAll (app1 (s := V) (vs vz) x0)))
  end.

Definition ZC : system zsym := generated (fun e : Empty_set => match e with end).
Definition RIZF := rsum (iorder_rules (Sym := zsym) (P := Pr) (n := 1) (p := 1)) izf_rules.
#[export] Typeclasses Transparent RIZF.
#[export] Hint Unfold RIZF : typeclass_instances.

Notation IZF Γ Ξ φ := (deriv ZC Pr RIZF Γ Ξ φ).

Lemma zaxm (i : izf_idx) {Γ} (Ξ : list (zform Γ)) (v : vec zsym (d_ctx (izf_rules i)) Γ) :
  IZF Γ Ξ (vsubst (d_concl (izf_rules i)) v).
Proof. apply (rule_inc ZC Pr RIZF izf_rules i Ξ v _ eq_refl). destruct i; intros p []. Qed.
