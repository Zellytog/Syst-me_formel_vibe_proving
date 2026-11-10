(** * Le modèle syntaxique d'une logique d'ordre (n,p)

    Le modèle syntaxique porte, pour chaque sorte, une structure d'égalité :
    E_Γ := (x₁ = x₀) est vrai le long de la diagonale par réflexivité, et
    c'est le plus petit tel prédicat par le transport de Leibniz
    ([syn_eqstruct]). Avec [syn_qstruct], le modèle syntaxique de la
    logique intuitionniste d'ordre (n,p) est donc un modèle au sens
    *structurel* ([syn_order_structure]), d'où la complétude pour les
    structures d'ordre (n,p) ([order_completeness]). *)

From Category Require Import Lib Theory.Category Theory.Functor
  Structure.Terminal Structure.Cartesian Structure.Cartesian.Closed.
From Stdlib Require Import List.
Import ListNotations.
From SF.Syntax Require Import Spec Terms Renaming Traversal Eta Vectors Syn.
From SF.Calculus Require Import System SynConv.
From SF.Logic Require Import Judgment Propositional.
From SF.Functional Require Import Arrow Graded.
From SF.Quantifiers Require Import Quant Order.
From SF.Models Require Import Calculus Hyperdoctrine Logic Completeness Quantifiers Equality Order.

Local Notation ι a := (Spec [] a).

Set Default Proof Using "All".

(** ** Vecteurs auxiliaires *)

Section Vecs.
Context {Srt : Type} {Sym : spec Srt -> Type} (s : Srt).

Local Notation tm := (Terms.tm Sym).
Local Notation x0 := (var0 (Sym := Sym) vz).
Local Notation x1 := (var0 (Sym := Sym) (vs vz)).

(** [q(z, x₁)] dans ι s :: ι s :: ι s :: Γ : la variable 0 de q reçoit z. *)
Definition vtr Γ : vec Sym (ι s :: ι s :: Γ) (ι s :: ι s :: ι s :: Γ) :=
  @acons _ Sym _ (ι s) _ (var0 vz)
    (@acons _ Sym _ (ι s) _ (var0 (vs (vs vz))) (sexl Sym Γ [ι s; ι s; ι s])).

Local Ltac vec3 :=
  apply vec_ext; intros σ x; unfold vget; revert σ x;
  refine (var_inv _ _ _); [|intros σ y; revert σ y; refine (var_inv _ _ _); [|intros σ y]];
  repeat first
    [ rewrite aget_vcomp | rewrite vsubst_tms_nil | rewrite vsubst_var0
    | rewrite aget_etas | rewrite vsubst_eta
    | progress unfold sexl, wkv, vid
    | progress cbn [vr app aget ahd atl vsel inst1 vtr vdiag]
    | progress cbn [etas] ];
  try reflexivity.

Lemma vdiag_vsel1 Γ :
  vcomp (vdiag s Γ) (vsel s (Γ := Γ) (vs vz)) =
  @acons _ Sym _ (ι s) _ x1 (@acons _ Sym _ (ι s) _ x1 (sexl Sym Γ [ι s; ι s])).
Proof. vec3. Qed.

Lemma vtr_inst1_x1 Γ :
  vcomp (vtr Γ) (inst1 x1) =
  @acons _ Sym _ (ι s) _ x1 (@acons _ Sym _ (ι s) _ x1 (sexl Sym Γ [ι s; ι s])).
Proof. vec3. Qed.

Lemma vtr_inst1_x0 Γ : vcomp (vtr Γ) (inst1 x0) = vid (ι s :: ι s :: Γ).
Proof. vec3. Qed.

End Vecs.

(** ** La structure d'égalité syntaxique *)

Section SynEq.
Context {Srt : Type} {Sym : spec Srt -> Type} (L : logic Sym).

Local Notation P := (l_prop Sym L).
Local Notation CS := (l_calc Sym L).
Local Notation R := (l_rules Sym L).
Local Notation form := (form Sym P).
Local Notation "Ξ ⊢ φ" := (deriv CS P R _ Ξ φ) (at level 70).
Local Notation SM := (syn_model CS).

Context {HI : HasImp Sym P} {HA : HasAnd Sym P} {HO : HasOr Sym P} {HT : HasTop Sym P} {HB : HasBot Sym P}.
Context {HR : Includes R ipc_rules}.
Context (s : Srt) {HQ : HasEq Sym P s} {HRQ : Includes R (eq_rules s)}.

Local Notation HD := (syn_hd L (HR := HR)).
Local Notation TT := (syn_truth L).
Local Notation x0 := (var0 (Sym := Sym) vz).
Local Notation x1 := (var0 (Sym := Sym) (vs vz)).

Definition syn_e Γ : form (ι s :: ι s :: Γ) := Eq s x1 x0.

Lemma syn_e_diag Γ : vsubst (syn_e Γ) (vdiag s Γ) = Eq s (var0 vz) (var0 vz).
Proof. unfold syn_e. rewrite vsubst_Eq, !vsubst_var0. reflexivity. Qed.

Definition syn_eqstruct : eqstruct L (SynConv CS) SM HD s.
Proof.
  refine (@Build_eqstruct _ _ L (SynConv CS) _ _ _ SM HD s syn_e _ _).
  - intros Γ. change (deriv CS P R (ι s :: Γ) [Top] (vsubst (syn_e Γ) (vdiag s Γ))).
    rewrite syn_e_diag. apply (eq_refl_d CS P R s).
  - intros Γ q K.
    change (deriv CS P R (ι s :: Γ) [Top] (vsubst q (vdiag s Γ))) in K.
    change (deriv CS P R (ι s :: ι s :: Γ) [syn_e Γ] q).
    (* q(x₁, x₁) *)
    pose proof (deriv_subst CS P R K _ (vsel s (Γ := Γ) (vs vz))) as K1.
    cbn [vsubst_list map] in K1. unfold Top in K1.
    rewrite vsubst_Cst, vsubst_vsubst in K1.
    change (deriv CS P R (ι s :: ι s :: Γ) [Top]
              (vsubst (q : form (ι s :: ι s :: Γ)) (vcomp (vdiag s Γ) (vsel s (Γ := Γ) (vs vz))))) in K1.
    rewrite vdiag_vsel1 in K1.
    (* transport le long de x₁ = x₀ dans q(x₁, z) *)
    enough (Hq : deriv CS P R _ [syn_e Γ] (vsubst (vsubst q (vtr s Γ)) (inst1 x0)))
      by (refine (eq_rect _ (fun ψ => deriv CS P R _ _ ψ) Hq _ _); rewrite vsubst_vsubst;
          etransitivity; [exact (f_equal (vsubst q) (vtr_inst1_x0 s Γ))|apply vsubst_vid]).
    apply (eq_subst CS P R s _ (vsubst q (vtr s Γ)) x1 x0).
    + apply d_ax; left; reflexivity.
    + refine (eq_rect _ (fun ψ => deriv CS P R _ _ ψ) _ _
                (eq_sym (eq_trans (vsubst_vsubst _ _ _) (f_equal (vsubst q) (vtr_inst1_x1 s Γ))))).
      apply (deriv_cut CS P R (φ := Top)); [exact (@top_max _ HD _ (syn_e Γ))|].
      eapply deriv_weaken; [exact K1|]. intros x [<-|[]]; left; reflexivity.
Defined.

Lemma syn_eq_compat : eq_compat L (SynConv CS) SM HD TT s syn_eqstruct.
Proof.
  intros Γ t u. rewrite syn_interp. cbn [e_pred syn_eqstruct].
  assert (E : vsubst (syn_e Γ) (vpair s t u) = Eq s t u) by (unfold syn_e; rewrite vsubst_Eq, !vsubst_var0; reflexivity).
  split; (eapply (eq_rect _ (fun ψ => deriv CS P R _ _ ψ)); [apply d_ax; left; reflexivity|]);
    [symmetry; exact E|exact E].
Qed.

End SynEq.

(** ** Le modèle syntaxique de la logique d'ordre (n,p) *)

Section SynOrder.
Context {Srt : Type} {Sym : spec Srt -> Type} {FS : Functional Sym} {G : Graded Sym}.
Context (CS : system Sym) (P : Srt) {n p : bound} {QI : Quantifiers Sym P n p}.
Context {HI : HasImp Sym P} {HA : HasAnd Sym P} {HO : HasOr Sym P} {HT : HasTop Sym P} {HB : HasBot Sym P}.

Local Notation L := (order_logic CS P (n := n) (p := p)).
Local Notation SM := (syn_model CS).
Local Notation HD := (syn_hd L).
Local Notation TT := (syn_truth L).

Lemma syn_bin_compat c (op : forall X, pred HD X -> pred HD X -> pred HD X) :
  (forall Γ (a b : Judgment.form Sym P Γ), op Γ a b = Bin c a b) -> bin_compat L (SynConv CS) SM HD TT c op.
Proof.
  intros Hop Γ a b. rewrite !syn_interp, Hop. split; apply d_ax; left; reflexivity.
Qed.

Lemma syn_cst_compat c (k : forall X, pred HD X) :
  (forall Γ, k Γ = Cst (Γ := Γ) c) -> cst_compat L (SynConv CS) SM HD TT c k.
Proof. intros Hk Γ. rewrite syn_interp, Hk. split; apply d_ax; left; reflexivity. Qed.

Definition syn_order_structure : order_structure L (SynConv CS) SM HD TT.
Proof.
  refine {| os_q := fun k => @syn_qstruct _ _ L _ _ _ _ _ _ (projT1 k) (qall_inst k) (qex_inst k) _ _;
            os_e := fun k => @syn_eqstruct _ _ L _ _ _ _ _ _ (projT1 k) (qeq_inst k) _ |}.
  all: try (destruct k as [s h]; typeclasses eauto).
  - apply syn_bin_compat; reflexivity.
  - apply syn_bin_compat; reflexivity.
  - apply syn_bin_compat; reflexivity.
  - apply syn_cst_compat; reflexivity.
  - apply syn_cst_compat; reflexivity.
  - intros k. apply syn_all_compat.
  - intros k. apply syn_ex_compat.
  - intros k. apply syn_eq_compat.
Defined.

(** Complétude pour les structures d'ordre (n,p) : un jugement valide dans
    tout modèle muni d'une structure d'ordre (n,p) est prouvable dans la
    logique intuitionniste d'ordre (n,p). *)
Theorem order_completeness Γ Ξ φ :
  (forall (C : Category) (CT : @Terminal C) (CC : @Cartesian C) (CL : @Closed C CC)
          (M : cmodel (l_calc Sym L) C) (H : hyperdoctrine C) (T : pred H (M [ι P])),
      order_structure L C M H T -> mvalid M H T Γ Ξ φ) ->
  provable L Γ Ξ φ.
Proof.
  intros Hv. apply (syn_valid_iff L). apply (Hv _ _ _ _ SM HD TT syn_order_structure).
Qed.

End SynOrder.
