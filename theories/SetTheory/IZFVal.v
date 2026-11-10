(** * Les valeurs des termes dans IZF : existence et unicité

    Le graphe D d'un terme est **total** (∃y. D(y)) et **fonctionnel**
    (D(y) → D(y′) → y = y′). On le prouve pour chaque gabarit, les
    métavariables (les graphes des arguments) étant supposées totales et
    fonctionnelles. *)

From Stdlib Require Import List.
Import ListNotations.
From SF.Syntax Require Import Spec Terms Renaming Eta Vectors.
From SF.Calculus Require Import System Rules.
From SF.Logic Require Import Judgment Propositional.
From SF.Functional Require Import Arrow.
From SF.Quantifiers Require Import Quant Order.
From SF.SetTheory Require Import Sets IZFe IZF IZFTr IZFLog.

Local Notation ι a := (Spec [] a).

Notation φ2 := (vs (vs vz)).
Notation φ3 := (vs (vs (vs vz))).
Notation φ4 := (vs (vs (vs (vs vz)))).
Notation φ5 := (vs (vs (vs (vs (vs vz))))).
Notation φ6 := (vs (vs (vs (vs (vs (vs vz)))))).
Notation φ7 := (vs (vs (vs (vs (vs (vs (vs vz))))))).
Notation φ8 := (vs (vs (vs (vs (vs (vs (vs (vs vz)))))))).
Notation φ9 := (vs (vs (vs (vs (vs (vs (vs (vs (vs vz))))))))).
Notation x5 := (var0 (vs (vs (vs (vs (vs vz)))))).
Notation x6 := (var0 (vs (vs (vs (vs (vs (vs vz))))))).
Notation x7 := (var0 (vs (vs (vs (vs (vs (vs (vs vz)))))))).
Notation x8 := (var0 (vs (vs (vs (vs (vs (vs (vs (vs vz))))))))).

Notation zap1 x t := (app1 (Sym := zsym) (P := Pr) (s := V) x t).

(** ** Totalité et fonctionnalité *)

Definition FunP : zform [σP] := zAll (Imp (zap1 (vs vz) x0) (zAll (Imp (zap1 φ2 x0) (zEq x1 x0)))).

Definition Tot {Γ} (D : zform (ι V :: Γ)) : zform Γ := zEx D.
Definition Fun {Γ} (D : zform (ι V :: Γ)) : zform Γ := vsubst FunP (v1 D).

Lemma Fun_vsubst {Θ Γ} (D : zform (ι V :: Θ)) (v : vec zsym Θ Γ) :
  vsubst (Fun D) v = Fun (vsubst D (vup [ι V] v)).
Proof. unfold Fun. rewrite vsubst_vsubst. f_equal. unfold v1, vcomp; cbn [vmap]. f_equal. exact (vsubst_tms_vup (σ := σP) D v). Qed.

Lemma Tot_vsubst {Θ Γ} (D : zform (ι V :: Θ)) (v : vec zsym Θ Γ) :
  vsubst (Tot D) v = Tot (vsubst D (vup [ι V] v)).
Proof. unfold Tot. change (zEx (vsubst_tms (σ := σP) D v) = zEx (vsubst D (vup [ι V] v))). f_equal. exact (vsubst_tms_vup (σ := σP) D v). Qed.

(** ** Une forme générale : ∃a. X(a) ∧ ∀z. z ∈ y ↔ Ψ(z, a)

    Contexte [X; Ψ]. Réunion, parties et séparation sont de cette forme. *)

Definition S1 : zform [ι V; σP; σR] :=
  zEx (And (zap1 φ2 x0) (zAll (zIff (zMem x0 x2) (zapp2 φ4 x0 x1)))).

Lemma fun_S1 : IZF [σP; σR] [Fun (eta σP (Γ := [σP; σR]) vz)] (Fun S1).
Proof.
  unfold Fun at 2, FunP. zap zall_I. zap zimp_I. zap zall_I. zap zimp_I.
  (* [y'; y; X; Ψ] *)
  zap (zex_E _ (And (zap1 φ3 x0) (zAll (zIff (zMem x0 x3) (zapp2 φ5 x0 x1))))); [zhyp|].
  (* [a; y'; y; X; Ψ] *)
  zap (zex_E _ (And (zap1 φ4 x0) (zAll (zIff (zMem x0 x3) (zapp2 φ6 x0 x1))))); [zhyp|].
  (* [a'; a; y'; y; X; Ψ] ; but y = y' *)
  apply (deriv_cut ZC Pr RIZF (φ := zEq x1 x0)).
  { zap (zimp_E _ (zap1 φ4 x0)).
    - zap (zall_E _ (Imp (zap1 φ5 x0) (zEq x2 x0)) x0).
      zap (zimp_E _ (zap1 φ4 x1)).
      + zap (zall_E _ (Imp (zap1 φ5 x0) (zAll (Imp (zap1 φ6 x0) (zEq x1 x0)))) x1). zhyp.
      + zap (zand_E1 _ _ (zAll (zIff (zMem x0 x4) (zapp2 φ6 x0 x2)))). zhyp.
    - zap (zand_E1 _ _ (zAll (zIff (zMem x0 x3) (zapp2 φ6 x0 x1)))). zhyp. }
  zap (zimp_E _ (zAll (zIff (zMem x0 x4) (zMem x0 x3)))).
  - zap (zall_E _ (Imp (zAll (zIff (zMem x0 x5) (zMem x0 x1))) (zEq x4 x0)) x2).
    zap (zall_E _ (zAll (Imp (zAll (zIff (zMem x0 x2) (zMem x0 x1))) (zEq x1 x0))) x3).
    exact (zaxm Z_ext _ anil).
  - zap zall_I.
    (* [z; a'; a; y'; y; X; Ψ] *)
    apply (ziff_trans _ _ (zapp2 φ6 x0 x2)).
    { zap (zall_E _ (zIff (zMem x0 x5) (zapp2 φ7 x0 x3)) x0).
      zap (zand_E2 _ (zap1 φ5 x2)). zhyp. }
    apply (ziff_trans _ _ (zapp2 φ6 x0 x1)).
    2:{ apply ziff_sym. zap (zall_E _ (zIff (zMem x0 x4) (zapp2 φ7 x0 x2)) x0).
        zap (zand_E2 _ (zap1 φ5 x1)). zhyp. }
    apply ziff_I.
    + zap (zeq_subst _ (zapp2 φ7 x1 x0) x2 x1); zhyp.
    + zap (zeq_subst _ (zapp2 φ7 x1 x0) x1 x2); [|zhyp]. zap zeq_sym. zhyp.
Qed.

Lemma fun_pair : IZF [σP; σP] [Fun (eta σP (Γ := [σP; σP]) vz); Fun (eta σP (Γ := [σP; σP]) (vs vz))] (Fun Fpair).
Proof.
  unfold Fun at 3, FunP. zap zall_I. zap zimp_I. zap zall_I. zap zimp_I.
  (* [y'; y; X1; X2] *)
  zap (zex_E _ (And (zap1 φ3 x0) (zEx (And (zap1 φ5 x0) (zAll (zIff (zMem x0 x4) (Or (zEq x0 x2) (zEq x0 x1)))))))); [zhyp|].
  apply zand_L.
  zap (zex_E _ (And (zap1 φ5 x0) (zAll (zIff (zMem x0 x4) (Or (zEq x0 x2) (zEq x0 x1)))))); [zhyp|].
  apply zand_L.
  zap (zex_E _ (And (zap1 φ5 x0) (zEx (And (zap1 φ7 x0) (zAll (zIff (zMem x0 x5) (Or (zEq x0 x2) (zEq x0 x1)))))))); [zhyp|].
  apply zand_L.
  zap (zex_E _ (And (zap1 φ7 x0) (zAll (zIff (zMem x0 x5) (Or (zEq x0 x2) (zEq x0 x1)))))); [zhyp|].
  apply zand_L. cbn.
  (* [b'; a'; b; a; y'; y; X1; X2] *)
  apply (deriv_cut ZC Pr RIZF (φ := zEq x3 x1)).
  { zap (zimp_E _ (zap1 φ6 x1)); [|zhyp].
    zap (zall_E _ (Imp (zap1 φ7 x0) (zEq x4 x0)) x1).
    zap (zimp_E _ (zap1 φ6 x3)); [|zhyp].
    zap (zall_E _ (Imp (zap1 φ7 x0) (zAll (Imp (zap1 φ8 x0) (zEq x1 x0)))) x3). zhyp. }
  apply (deriv_cut ZC Pr RIZF (φ := zEq x2 x0)).
  { zap (zimp_E _ (zap1 φ7 x0)); [|zhyp].
    zap (zall_E _ (Imp (zap1 φ8 x0) (zEq x3 x0)) x0).
    zap (zimp_E _ (zap1 φ7 x2)); [|zhyp].
    zap (zall_E _ (Imp (zap1 φ8 x0) (zAll (Imp (zap1 φ9 x0) (zEq x1 x0)))) x2). zhyp. }
  zap (zimp_E _ (zAll (zIff (zMem x0 x6) (zMem x0 x5)))).
  - zap (zall_E _ (Imp (zAll (zIff (zMem x0 x7) (zMem x0 x1))) (zEq x6 x0)) x4).
    zap (zall_E _ (zAll (Imp (zAll (zIff (zMem x0 x2) (zMem x0 x1))) (zEq x1 x0))) x5).
    exact (zaxm Z_ext _ anil).
  - zap zall_I.
    (* [z; b'; a'; b; a; y'; y; X1; X2] *)
    apply (ziff_trans _ _ (Or (zEq x0 x4) (zEq x0 x3))).
    { zap (zall_E _ (zIff (zMem x0 x7) (Or (zEq x0 x5) (zEq x0 x4))) x0). zhyp. }
    apply (ziff_trans _ _ (Or (zEq x0 x2) (zEq x0 x1))).
    2:{ apply ziff_sym. zap (zall_E _ (zIff (zMem x0 x6) (Or (zEq x0 x3) (zEq x0 x2))) x0). zhyp. }
    apply ziff_or; apply ziff_I.
    + zap (zeq_trans _ x0 x4 x2); zhyp.
    + zap (zeq_trans _ x0 x2 x4); [zhyp|zap zeq_sym; zhyp].
    + zap (zeq_trans _ x0 x3 x1); zhyp.
    + zap (zeq_trans _ x0 x1 x3); [zhyp|zap zeq_sym; zhyp].
Qed.

(** Réunion, parties, séparation : instances de [S1]. *)
Definition PsiU : zform [ι V; ι V; σP] := zEx (And (zMem x1 x0) (zMem x0 x2)).
Definition PsiP : zform [ι V; ι V; σP] := zAll (Imp (zMem x0 x1) (zMem x0 x2)).
Definition PsiS : zform [ι V; ι V; σP; σP] := And (zMem x0 x1) (zap1 φ3 x0).

Definition wS {Θ} (X : var Θ σP) (Ψ : zform (ι V :: ι V :: Θ)) : vec zsym [σP; σR] Θ :=
  @acons _ zsym Θ σP _ (eta σP X) (@acons _ zsym Θ σR _ Ψ anil).

Lemma fun_S1_inst {Θ} (X : var Θ σP) (Ψ : zform (ι V :: ι V :: Θ)) :
  IZF Θ [Fun (eta σP X)] (Fun (vsubst S1 (vup [ι V] (wS X Ψ)))).
Proof.
  pose proof (deriv_subst _ _ _ fun_S1 Θ (wS X Ψ)) as K. rewrite Fun_vsubst in K.
  unfold vsubst_list in K. cbn [map] in K. rewrite Fun_vsubst in K.
  assert (E : vsubst (eta σP (Γ := [σP; σR]) vz) (vup [ι V] (wS X Ψ)) = eta σP X).
  { rewrite <- (vsubst_tms_vup (σ := σP)). exact (vsubst_eta (σ := σP) vz (wS X Ψ)). }
  exact (eq_rect _ (fun D => IZF Θ [Fun D] _) K _ E).
Qed.

Lemma fun_union : IZF [σP] [Fun (eta σP (Γ := [σP]) vz)] (Fun Funion).
Proof. exact (fun_S1_inst vz PsiU). Qed.

Lemma fun_power : IZF [σP] [Fun (eta σP (Γ := [σP]) vz)] (Fun Fpower).
Proof. exact (fun_S1_inst vz PsiP). Qed.

Lemma fun_sep : IZF [σP; σP] [Fun (eta σP (Γ := [σP; σP]) vz)] (Fun Fsep).
Proof. exact (fun_S1_inst vz PsiS). Qed.

(** ∀E par conversion du but (plus robuste que l'unification). *)
Tactic Notation "zinst" uconstr(φ) uconstr(t) :=
  match goal with |- IZF ?G ?X _ =>
    refine (_ : IZF G X (vsubst (Γ := ι V :: G) φ (inst1 t))); zap (zall_E X _ t) end.

(** ** Totalité *)

Lemma tot_pair : IZF [σP; σP] [Tot (eta σP (Γ := [σP; σP]) vz); Tot (eta σP (Γ := [σP; σP]) (vs vz))] (Tot Fpair).
Proof.
  zap (zex_E _ (zap1 (vs vz) x0)); [zhyp|].
  zap (zex_E _ (zap1 φ3 x0)); [zhyp|].
  (* [b; a; X1; X2] *)
  zap (zex_E _ (zAll (zIff (zMem x0 x1) (Or (zEq x0 x3) (zEq x0 x2))))).
  { zap (zall_E _ (zEx (zAll (zIff (zMem x0 x1) (Or (zEq x0 x4) (zEq x0 x2))))) x0).
    zap (zall_E _ (zAll (zEx (zAll (zIff (zMem x0 x1) (Or (zEq x0 x3) (zEq x0 x2)))))) x1).
    exact (zaxm Z_pair _ anil). }
  (* [p; b; a; X1; X2] *)
  zap (zex_I _ _ x0). zap (zex_I _ _ x2). zap zand_I; [zhyp|].
  zap (zex_I _ _ x1). zap zand_I; zhyp.
Qed.

Lemma tot_union : IZF [σP] [Tot (eta σP (Γ := [σP]) vz)] (Tot Funion).
Proof.
  zap (zex_E _ (zap1 (vs vz) x0)); [zhyp|].
  zap (zex_E _ (zAll (zIff (zMem x0 x1) (zEx (And (zMem x1 x0) (zMem x0 x3)))))).
  { zap (zall_E _ (zEx (zAll (zIff (zMem x0 x1) (zEx (And (zMem x1 x0) (zMem x0 x3)))))) x0).
    exact (zaxm Z_union _ anil). }
  zap (zex_I _ _ x0). zap (zex_I _ _ x1). zap zand_I; zhyp.
Qed.

Lemma tot_power : IZF [σP] [Tot (eta σP (Γ := [σP]) vz)] (Tot Fpower).
Proof.
  zap (zex_E _ (zap1 (vs vz) x0)); [zhyp|].
  (* [a; X] *)
  zap (zex_E _ (zAll (Imp (zAll (Imp (zMem x0 x1) (zMem x0 x3))) (zMem x0 x1)))).
  { zap (zall_E _ (zEx (zAll (Imp (zAll (Imp (zMem x0 x1) (zMem x0 x3))) (zMem x0 x1)))) x0).
    exact (zaxm Z_power _ anil). }
  (* [p; a; X] *)
  zap (zex_E _ (zAll (zIff (zMem x0 x1) (And (zMem x0 x2) (zAll (Imp (zMem x0 x1) (zMem x0 x4))))))).
  { zap (zall_E _ (zEx (zAll (zIff (zMem x0 x1) (And (zMem x0 x2) (zAll (Imp (zMem x0 x1) (zMem x0 x5))))))) x0).
    exact (zaxm Z_sep _ (v1 (zAll (Imp (zMem x0 x1) (zMem x0 x3))))). }
  (* [s; p; a; X] *)
  zap (zex_I _ _ x0). zap (zex_I _ _ x2). zap zand_I; [zhyp|].
  zap zall_I. cbn. apply ziff_I.
  - zap (zand_E2 _ (zMem x0 x2)). apply (ziff_E1 _ (zMem x0 x1)); [|zhyp].
    zinst (zIff (zMem x0 x2) (And (zMem x0 x3) (zAll (Imp (zMem x0 x1) (zMem x0 x5))))) x0. zhyp.
  - apply (ziff_E2 _ (zMem x0 x1) (And (zMem x0 x2) (zAll (Imp (zMem x0 x1) (zMem x0 x4))))).
    + zinst (zIff (zMem x0 x2) (And (zMem x0 x3) (zAll (Imp (zMem x0 x1) (zMem x0 x5))))) x0. zhyp.
    + zap zand_I; [|zhyp].
      zap (zimp_E _ (zAll (Imp (zMem x0 x1) (zMem x0 x4)))); [|zhyp].
      zinst (Imp (zAll (Imp (zMem x0 x1) (zMem x0 x5))) (zMem x0 x3)) x0. zhyp.
Qed.

Lemma tot_sep : IZF [σP; σP] [Tot (eta σP (Γ := [σP; σP]) vz)] (Tot Fsep).
Proof.
  zap (zex_E _ (zap1 (vs vz) x0)); [zhyp|].
  (* [a; X1; P] *)
  zap (zex_E _ (zAll (zIff (zMem x0 x1) (And (zMem x0 x2) (zap1 φ4 x0))))).
  { zap (zall_E _ (zEx (zAll (zIff (zMem x0 x1) (And (zMem x0 x2) (zap1 φ5 x0))))) x0).
    exact (zaxm Z_sep _ (v1 (eta σP (Γ := [ι V; σP; σP]) φ2))). }
  zap (zex_I _ _ x0). zap (zex_I _ _ x1). zap zand_I; zhyp.
Qed.


(** ** Remplacement : la construction totale *)

Local Notation φ10 := (vs φ9).
Local Notation φ11 := (vs φ10).

Definition PsiR : zform [ι V; ι V; σP; σR] := And (FnAt (vs vz) φ3) (ExIn (vs vz) φ3 vz).

Lemma fun_repl : IZF [σP; σR] [Fun (eta σP (Γ := [σP; σR]) vz)] (Fun Frepl).
Proof. exact (fun_S1_inst vz PsiR). Qed.

Lemma tot_repl : IZF [σP; σR] [Tot (eta σP (Γ := [σP; σR]) vz)] (Tot Frepl).
Proof.
  zap (zex_E _ (zap1 (vs vz) x0)); [zhyp|].
  (* [a; X; R] : A = {α ∈ a | Fn(a)} *)
  zap (zex_E _ (zAll (zIff (zMem x0 x1) (And (zMem x0 x2) (FnAt φ2 φ4))))).
  { zinst (zEx (zAll (zIff (zMem x0 x1) (And (zMem x0 x2) (FnAt φ3 φ5))))) x0.
    exact (zaxm Z_sep _ (v1 (FnAt (vs vz) φ3))). }
  (* [A; a; X; R] : collection sur A *)
  zap (zex_E _ (zAll (Imp (zMem x0 x2) (zEx (And (zMem x0 x2) (zapp2 φ6 x1 x0)))))).
  { zap (zimp_E _ (zAll (Imp (zMem x0 x1) (zEx (zapp2 φ5 x1 x0))))).
    - zinst (Imp (zAll (Imp (zMem x0 x1) (zEx (zapp2 φ6 x1 x0))))
                 (zEx (zAll (Imp (zMem x0 x2) (zEx (And (zMem x0 x2) (zapp2 φ7 x1 x0))))))) x0.
      exact (zaxm Z_coll _ (@acons _ zsym _ σR _ (eta σR (Γ := [ι V; ι V; σP; σR]) φ3) anil)).
    - zap zall_I. zap zimp_I.
      (* [α; A; a; X; R] *)
      apply (deriv_cut ZC Pr RIZF (φ := And (zMem x0 x2) (FnAt φ2 φ4))).
      { apply (ziff_E1 _ (zMem x0 x1)); [|zhyp].
        zinst (zIff (zMem x0 x2) (And (zMem x0 x3) (FnAt φ3 φ5))) x0. zhyp. }
      apply zand_L.
      zap (zex_E _ (And (zapp2 φ5 x1 x0) (zAll (Imp (zapp2 φ6 x2 x0) (zEq x0 x1))))).
      { zap (zimp_E _ (zMem x0 x2)); [|zhyp].
        zinst (Imp (zMem x0 x3) (zEx (And (zapp2 φ6 x1 x0) (zAll (Imp (zapp2 φ7 x2 x0) (zEq x0 x1)))))) x0. zhyp. }
      apply zand_L. zap (zex_I _ _ x0). zhyp. }
  (* [c; A; a; X; R] : y = {z ∈ c | Fn(a) ∧ ∃α ∈ a. R(α, z)} *)
  zap (zex_E _ (zAll (zIff (zMem x0 x1) (And (zMem x0 x2) (And (FnAt φ4 φ6) (ExIn φ4 φ6 vz)))))).
  { zinst (zEx (zAll (zIff (zMem x0 x1) (And (zMem x0 x2) (And (FnAt φ5 φ7) (ExIn φ5 φ7 vz)))))) x0.
    exact (zaxm Z_sep _ (v1 (And (FnAt φ3 φ5) (ExIn φ3 φ5 vz)))). }
  (* [y; c; A; a; X; R] *)
  zap (zex_I _ _ x0). zap (zex_I _ _ x3). zap zand_I; [zhyp|].
  zap zall_I. apply ziff_I.
  - zap (zand_E2 _ (zMem x0 x2)). apply (ziff_E1 _ (zMem x0 x1)); [|zhyp].
    zinst (zIff (zMem x0 x2) (And (zMem x0 x3) (And (FnAt φ5 φ7) (ExIn φ5 φ7 vz)))) x0. zhyp.
  - apply zand_L.
    apply (ziff_E2 _ _ (And (zMem x0 x2) (And (FnAt φ4 φ6) (ExIn φ4 φ6 vz)))).
    { zinst (zIff (zMem x0 x2) (And (zMem x0 x3) (And (FnAt φ5 φ7) (ExIn φ5 φ7 vz)))) x0. zhyp. }
    zap zand_I; [|zap zand_I; zhyp].
    (* z ∈ c *)
    zap (zex_E _ (And (zMem x0 x5) (zapp2 φ7 x0 x1))); [zhyp|]. apply zand_L.
    (* [α; z; y; c; A; a; X; R] *)
    apply (deriv_cut ZC Pr RIZF (φ := zMem x0 x4)).
    { apply (ziff_E2 _ _ (And (zMem x0 x5) (FnAt φ5 φ7))).
      - zinst (zIff (zMem x0 x5) (And (zMem x0 x6) (FnAt φ6 φ8))) x0. zhyp.
      - zap zand_I; zhyp. }
    zap (zex_E _ (And (zMem x0 x4) (zapp2 φ8 x1 x0))).
    { zap (zimp_E _ (zMem x0 x4)); [|zhyp].
      zinst (Imp (zMem x0 x5) (zEx (And (zMem x0 x5) (zapp2 φ9 x1 x0)))) x0. zhyp. }
    apply zand_L.
    (* [β; α; z; y; c; A; a; X; R] *)
    zap (zex_E _ (And (zapp2 φ9 x2 x0) (zAll (Imp (zapp2 φ10 x3 x0) (zEq x0 x1))))).
    { zap (zimp_E _ (zMem x1 x6)); [|zhyp].
      zinst (Imp (zMem x0 x7) (zEx (And (zapp2 φ10 x1 x0) (zAll (Imp (zapp2 φ11 x2 x0) (zEq x0 x1)))))) x1. zhyp. }
    apply zand_L.
    (* [β0; β; α; z; y; c; A; a; X; R] *)
    zap (zeq_subst _ (zMem x0 x6) x1 x3); [|zhyp].
    zap (zeq_trans _ x1 x0 x3).
    + zap (zimp_E _ (zapp2 φ9 x2 x1)); [|zhyp]. zinst (Imp (zapp2 φ10 x3 x0) (zEq x0 x1)) x1. zhyp.
    + zap zeq_sym. zap (zimp_E _ (zapp2 φ9 x2 x3)); [|zhyp]. zinst (Imp (zapp2 φ10 x3 x0) (zEq x0 x1)) x3. zhyp.
Qed.

Lemma tot_empty {Γ} (Ξ : list (zform Γ)) : IZF Γ Ξ (Tot emptyT).
Proof.
  zap (zex_E _ (And (zEx (And (zMem x0 x1) (zAll (Neg (zMem x0 x1)))))
                    (zAll (Imp (zMem x0 x1) (zEx (And (zMem x0 x2) (zAll (zIff (zMem x0 x1) (Or (zMem x0 x2) (zEq x0 x2)))))))))).
  { exact (zaxm Z_inf _ anil). }
  apply zand_L.
  zap (zex_E _ (And (zMem x0 x1) (zAll (Neg (zMem x0 x1))))); [zhyp|].
  apply zand_L. zap (zex_I _ _ x0). zhyp.
Qed.

Lemma fun_empty {Γ} (Ξ : list (zform Γ)) : IZF Γ Ξ (Fun emptyT).
Proof.
  unfold Fun, FunP. zap zall_I. zap zimp_I. zap zall_I. zap zimp_I.
  zap (zimp_E _ (zAll (zIff (zMem x0 x2) (zMem x0 x1)))).
  - zap (zall_E _ (Imp (zAll (zIff (zMem x0 x3) (zMem x0 x1))) (zEq x2 x0)) x0).
    zap (zall_E _ (zAll (Imp (zAll (zIff (zMem x0 x2) (zMem x0 x1))) (zEq x1 x0))) x1).
    exact (zaxm Z_ext _ anil).
  - zap zall_I. apply ziff_I.
    + zap (bot_E ZC Pr RIZF). zap (zimp_E _ (zMem x0 x2)); [|zhyp].
      zap (zall_E _ (Neg (zMem x0 x3)) x0). zhyp.
    + zap (bot_E ZC Pr RIZF). zap (zimp_E _ (zMem x0 x1)); [|zhyp].
      zap (zall_E _ (Neg (zMem x0 x2)) x0). zhyp.
Qed.

(** ** ω *)

(** Les deux formules auxiliaires de [omegaT] : z vide, z = S(b). *)
Notation zEmp1 := (zAll (Neg (zMem x0 x1))).
Notation zSuc21 := (zAll (zIff (zMem x0 x2) (Or (zMem x0 x1) (zEq x0 x1)))).

(** Unicité de ω, par ∈-induction : z ∈ y ↔ z ∈ y′. *)
Lemma fun_omega0 : IZF [] [] (Fun (omegaT (Γ := []))).
Proof.
  unfold Fun, FunP. zap zall_I. zap zimp_I. zap zall_I. zap zimp_I. cbn.
  (* [y'; y] *)
  zap (zimp_E _ (zAll (zIff (zMem x0 x2) (zMem x0 x1)))).
  { zinst (Imp (zAll (zIff (zMem x0 x3) (zMem x0 x1))) (zEq x2 x0)) x0.
    zinst (zAll (Imp (zAll (zIff (zMem x0 x2) (zMem x0 x1))) (zEq x1 x0))) x1.
    exact (zaxm Z_ext _ anil). }
  zap (zimp_E _ (zAll (Imp (zAll (Imp (zMem x0 x1) (zIff (zMem x0 x3) (zMem x0 x2)))) (zIff (zMem x0 x2) (zMem x0 x1))))).
  { exact (zaxm Z_ind _ (v1 (zIff (zMem x0 x2) (zMem x0 x1)))). }
  zap zall_I. zap zimp_I. cbn.
  (* [z; y'; y] ; IH : ∀b. b ∈ z → (b ∈ y ↔ b ∈ y') *)
  apply ziff_I.
  - zap (zor_E _ zEmp1 (zEx (And (zMem x0 x3) zSuc21))).
    { apply (ziff_E1 _ (zMem x0 x2)); [|zhyp].
      zinst (zIff (zMem x0 x3) (Or zEmp1 (zEx (And (zMem x0 x4) zSuc21)))) x0. zhyp. }
    + apply (ziff_E2 _ _ (Or zEmp1 (zEx (And (zMem x0 x2) zSuc21)))).
      * zinst (zIff (zMem x0 x2) (Or zEmp1 (zEx (And (zMem x0 x3) zSuc21)))) x0. zhyp.
      * zap zor_I1. zhyp.
    + zap (zex_E _ (And (zMem x0 x3) zSuc21)); [zhyp|]. apply zand_L. cbn.
      (* [b; z; y'; y] *)
      apply (ziff_E2 _ _ (Or (zAll (Neg (zMem x0 x2))) (zEx (And (zMem x0 x3) (zAll (zIff (zMem x0 x3) (Or (zMem x0 x1) (zEq x0 x1)))))))).
      * zinst (zIff (zMem x0 x3) (Or zEmp1 (zEx (And (zMem x0 x4) zSuc21)))) x1. zhyp.
      * zap zor_I2. zap (zex_I _ _ x0). zap zand_I; [|zhyp].
        apply (ziff_E1 _ (zMem x0 x3)); [|zhyp].
        zap (zimp_E _ (zMem x0 x1)).
        -- zinst (Imp (zMem x0 x2) (zIff (zMem x0 x4) (zMem x0 x3))) x0. zhyp.
        -- apply (ziff_E2 _ _ (Or (zMem x0 x0) (zEq x0 x0))).
           ++ zinst (zIff (zMem x0 x2) (Or (zMem x0 x1) (zEq x0 x1))) x0. zhyp.
           ++ zap zor_I2. zap zeq_refl.
  - zap (zor_E _ zEmp1 (zEx (And (zMem x0 x2) zSuc21))).
    { apply (ziff_E1 _ (zMem x0 x1)); [|zhyp].
      zinst (zIff (zMem x0 x2) (Or zEmp1 (zEx (And (zMem x0 x3) zSuc21)))) x0. zhyp. }
    + apply (ziff_E2 _ _ (Or zEmp1 (zEx (And (zMem x0 x3) zSuc21)))).
      * zinst (zIff (zMem x0 x3) (Or zEmp1 (zEx (And (zMem x0 x4) zSuc21)))) x0. zhyp.
      * zap zor_I1. zhyp.
    + zap (zex_E _ (And (zMem x0 x2) zSuc21)); [zhyp|]. apply zand_L. cbn.
      (* [b; z; y'; y] *)
      apply (ziff_E2 _ _ (Or (zAll (Neg (zMem x0 x2))) (zEx (And (zMem x0 x4) (zAll (zIff (zMem x0 x3) (Or (zMem x0 x1) (zEq x0 x1)))))))).
      * zinst (zIff (zMem x0 x4) (Or zEmp1 (zEx (And (zMem x0 x5) zSuc21)))) x1. zhyp.
      * zap zor_I2. zap (zex_I _ _ x0). zap zand_I; [|zhyp].
        apply (ziff_E2 _ _ (zMem x0 x2)); [|zhyp].
        zap (zimp_E _ (zMem x0 x1)).
        -- zinst (Imp (zMem x0 x2) (zIff (zMem x0 x4) (zMem x0 x3))) x0. zhyp.
        -- apply (ziff_E2 _ _ (Or (zMem x0 x0) (zEq x0 x0))).
           ++ zinst (zIff (zMem x0 x2) (Or (zMem x0 x1) (zEq x0 x1))) x0. zhyp.
           ++ zap zor_I2. zap zeq_refl.
Qed.

Section OmegaAux.
Context {Γ : ctx isort}.
Definition EmpAt (e : var Γ (ι V)) : zform Γ := zAll (Neg (zMem x0 (var0 (vs e)))).
Definition SucAt (m n : var Γ (ι V)) : zform Γ :=
  zAll (zIff (zMem x0 (var0 (vs m))) (Or (zMem x0 (var0 (vs n))) (zEq x0 (var0 (vs n))))).
End OmegaAux.

Definition IndAt {Γ} (W : var Γ (ι V)) : zform Γ :=
  And (zEx (And (zMem x0 (var0 (vs W))) (EmpAt vz)))
      (zAll (Imp (zMem x0 (var0 (vs W))) (zEx (And (zMem x0 (var0 (vs (vs W)))) (SucAt vz (vs vz)))))).

(** Application d'un lemme ouvert de IZF par un vecteur de variables. *)
Lemma zuse {Γ0 Ξ0 φ} (H : IZF Γ0 Ξ0 φ) {Γ} (w : vec zsym Γ0 Γ) (Ξ : list (zform Γ)) :
  (forall χ, In χ Ξ0 -> IZF Γ Ξ (vsubst χ w)) -> IZF Γ Ξ (vsubst φ w).
Proof.
  intros Hh. apply (deriv_cut_gen _ _ _ (deriv_subst _ _ _ H Γ w)).
  intros χ Hχ. unfold vsubst_list in Hχ. apply in_map_iff in Hχ as (χ0 & <- & Hχ0). apply Hh, Hχ0.
Qed.

Tactic Notation "zuses" constr(H) uconstr(w) :=
  refine (zuse H w _ _); [intros ? Hin; repeat (destruct Hin as [<-|Hin]); try contradiction].

Definition zv2 {Γ} (a b : ztm Γ V) : vec zsym [ι V; ι V] Γ :=
  @acons _ zsym Γ (ι V) _ a (@acons _ zsym Γ (ι V) _ b anil).
Definition zv3 {Γ} (a b c : ztm Γ V) : vec zsym [ι V; ι V; ι V] Γ :=
  @acons _ zsym Γ (ι V) _ a (zv2 b c).

(** Deux ensembles vides sont égaux   (contexte [e; e′]). *)
Lemma emp_eq : IZF [ι V; ι V] [EmpAt vz; EmpAt (vs vz)] (zEq x0 x1).
Proof.
  zap (zimp_E _ (zAll (zIff (zMem x0 x1) (zMem x0 x2)))).
  { zinst (Imp (zAll (zIff (zMem x0 x2) (zMem x0 x1))) (zEq x1 x0)) x1.
    zinst (zAll (Imp (zAll (zIff (zMem x0 x2) (zMem x0 x1))) (zEq x1 x0))) x0.
    exact (zaxm Z_ext _ anil). }
  zap zall_I. apply ziff_I.
  - zap (bot_E ZC Pr RIZF). zap (zimp_E _ (zMem x0 x1)); [|zhyp].
    zinst (Neg (zMem x0 x2)) x0. zhyp.
  - zap (bot_E ZC Pr RIZF). zap (zimp_E _ (zMem x0 x2)); [|zhyp].
    zinst (Neg (zMem x0 x3)) x0. zhyp.
Qed.

(** Deux successeurs de n sont égaux   (contexte [m; m′; n]). *)
Lemma suc_eq : IZF [ι V; ι V; ι V] [SucAt vz φ2; SucAt (vs vz) φ2] (zEq x0 x1).
Proof.
  zap (zimp_E _ (zAll (zIff (zMem x0 x1) (zMem x0 x2)))).
  { zinst (Imp (zAll (zIff (zMem x0 x2) (zMem x0 x1))) (zEq x1 x0)) x1.
    zinst (zAll (Imp (zAll (zIff (zMem x0 x2) (zMem x0 x1))) (zEq x1 x0))) x0.
    exact (zaxm Z_ext _ anil). }
  zap zall_I.
  apply (ziff_trans _ _ (Or (zMem x0 x3) (zEq x0 x3))).
  - zinst (zIff (zMem x0 x2) (Or (zMem x0 x4) (zEq x0 x4))) x0. zhyp.
  - apply ziff_sym. zinst (zIff (zMem x0 x3) (Or (zMem x0 x4) (zEq x0 x4))) x0. zhyp.
Qed.
