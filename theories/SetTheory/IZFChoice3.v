(** * CC dans IZF : le théorème

    IZFε + CC (schéma ε, [IZFeCC.v]) prouve le choix dénombrable de IZF
    énoncé dans L_IZF ([IZF_cc], [IZFChoice2.v]), pour toute formule de
    L_IZF ([izf_cc_lizf]). *)

From Stdlib Require Import List.
Import ListNotations.
From SF.Syntax Require Import Spec Terms Renaming Vectors.
From SF.Calculus Require Import System Rules.
From SF.Logic Require Import Judgment Propositional.
From SF.Functional Require Import Arrow.
From SF.Quantifiers Require Import Quant Order.
From SF.Extensions Require Import RuleExt.
From SF.SetTheory Require Import IZFe IZFeBasic IZFeExt IZFeIZF IZFeCC IZFeDC IZFChoice IZFChoice2.

Local Notation ι a := (Spec [] a).
Tactic Notation "qap" uconstr(t) := eapply t; try typeclasses eauto.
Ltac hyp := apply d_ax; simpl; auto 20.
Ltac hypc := apply d_ax; repeat (first [left; reflexivity | right]).

(** ** L'extensionnalité en le second argument, pour une formule de L_IZF *)

Lemma extR2_inst {Γ} (Ξ : list (form Γ)) (ψ : form (ι V :: ι V :: Γ)) :
  lizf _ ψ -> IZFm Γ Ξ (vsubst ExtR2 (vR1 ψ)).
Proof.
  intros Hl. unfold ExtR2, Quant.All.
  rewrite vsubst_Qnt, (vsubst_tms_vup (σ := σP)), vsubst_Qnt, (vsubst_tms_vup (σ := σP)),
    vsubst_Qnt, (vsubst_tms_vup (σ := σP)).
  cbn [dom app]. unfold Imp; rewrite !vsubst_Bin, !vsubst_app2. rsimpl.
  set (w := vup [ι V] (vup [ι V] (vup [ι V] (vR1 ψ)))).
  assert (Hl' : lizf _ (ahd (atl (atl (atl w))))).
  { subst w. unfold vup, vren. cbn [vcat ahd atl aget vmap app]. unfold ren_tms.
    cbn [dom app]. apply lizf_ren, lizf_ren, lizf_ren, Hl. }
  qap (qall_I C RIZFm V hV). qap (qall_I C RIZFm V hV). qap (qall_I C RIZFm V hV).
  qap (imp_I C Pr RIZFm). qap (imp_I C Pr RIZFm).
  refine (ext_lizf _ Hl' _ _
    (@acons _ isym _ (ι V) _ (ahd (atl (atl w))) (@acons _ isym _ (ι V) _ (ahd (atl w)) (vid _)))
    (@acons _ isym _ (ι V) _ (ahd (atl (atl w))) (@acons _ isym _ (ι V) _ (ahd w) (vid _))) _ _).
  - apply erel_cons; [apply eqv_refl_gen|]. apply erel_cons; [hyp|apply erel_refl].
  - hyp.
Qed.

(** ** De IZF⁻ε à IZFε + CC *)

Lemma liftC {Γ Ξ φ} : IZFm Γ Ξ φ -> IZFeC Γ Ξ φ.
Proof. apply (deriv_mono _ C C RIZFm RIZFeC); [apply sys_le_refl|typeclasses eauto]. Qed.

Lemma useC {Γ0 Ξ0 φ} (H : IZFeC Γ0 Ξ0 φ) {Γ} (w : vec isym Γ0 Γ) (Ξ : list (form Γ)) :
  (forall χ, In χ Ξ0 -> IZFeC Γ Ξ (vsubst χ w)) -> IZFeC Γ Ξ (vsubst φ w).
Proof.
  intros Hh. apply (deriv_cut_gen _ _ _ (deriv_subst _ _ _ H Γ w)).
  intros χ Hχ. unfold vsubst_list in Hχ. apply in_map_iff in Hχ as (χ0 & <- & Hχ0). apply Hh, Hχ0.
Qed.

Tactic Notation "usesC0" constr(H) :=
  refine (deriv_cut_gen _ _ _ (liftC H) _ _); [intros ? Hin; repeat (destruct Hin as [<-|Hin]); try contradiction].

Lemma axmC {Γ} (Ξ : list (form Γ)) (v : vec isym [ι V; σR] Γ) : IZFeC Γ Ξ (vsubst (d_concl A_cc) v).
Proof. apply (rule_inc C Pr RIZFeC (fun _ : unit => A_cc) tt Ξ v _ eq_refl). intros p []. Qed.

(** ** IZFε + CC prouve le choix dénombrable de IZF *)

Theorem izf_cc : IZFeC [σR] [ExtR; ExtR2] IZF_cc.
Proof.
  unfold IZF_cc. qap (qall_I C RIZFeC V hV). qap (imp_I C Pr RIZFeC).
  qap (qall_I C RIZFeC V hV). qap (imp_I C Pr RIZFeC).
  (* [X; w; φ] *)
  qap (qex_E C RIZFeC V hV _ (And TOTe (And FUNe SUBe))).
  { qap (imp_E C Pr RIZFeC _ EPSe).
    - exact (axmC _ (vVR x0 (eta σR (Γ := [ι V; ι V; σR]) (vs (vs vz))))).
    - usesC0 epshyp_l; hypc. }
  (* [f; X; w; φ] *)
  qap (qex_I C RIZFeC V hV _ _ x0). qap (and_I C Pr RIZFeC); [|qap (and_I C Pr RIZFeC)].
  - usesC0 cc_tot_l; [hypc|hypc|]. qap (and_E1 C Pr RIZFeC _ _ (And FUNe SUBe)). hypc.
  - usesC0 cc_fun_l.
    + qap (and_E1 C Pr RIZFeC _ _ SUBe). qap (and_E2 C Pr RIZFeC _ TOTe). hypc.
    + qap (and_E2 C Pr RIZFeC _ FUNe). qap (and_E2 C Pr RIZFeC _ TOTe). hypc.
  - usesC0 cc_sub_l; [hypc|]. qap (and_E2 C Pr RIZFeC _ FUNe). qap (and_E2 C Pr RIZFeC _ TOTe). hypc.
Qed.

(** Pour toute formule φ(n, y) de L_IZF (avec paramètres), le choix
    dénombrable de IZF est un théorème de IZFε + CC. *)
Theorem izf_cc_lizf {Γ} (ψ : form (ι V :: ι V :: Γ)) :
  lizf _ ψ -> IZFeC Γ [] (vsubst IZF_cc (vR1 ψ)).
Proof.
  intros Hl. refine (useC izf_cc (vR1 ψ) [] _).
  intros χ [<-|[<-|[]]]; apply liftC; [apply extR_inst, Hl|apply extR2_inst, Hl].
Qed.
