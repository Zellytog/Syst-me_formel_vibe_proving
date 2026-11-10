(** * rec dans IZF : les essais

    Unicité (deux essais s'accordent, par ∈-induction), existence d'un
    essai défini en tout a (par ∈-induction : collection, réunion, ajout
    d'un couple), d'où la totalité et la fonctionnalité du graphe de rec. *)

From Stdlib Require Import List.
Import ListNotations.
From SF.Syntax Require Import Spec Terms Renaming Eta Vectors.
From SF.Calculus Require Import System Rules.
From SF.Logic Require Import Judgment Propositional.
From SF.Functional Require Import Arrow.
From SF.Quantifiers Require Import Quant Order.
From SF.SetTheory Require Import Sets IZFe IZF IZFTr IZFLog IZFVal.

Local Notation ι a := (Spec [] a).

(** ** Outils *)

Lemma zex_E_r {Γ} (Ξ : list (zform Γ)) (φ : zform (ι V :: Γ)) χ :
  IZF Γ Ξ (@tsym _ zsym Γ _ z_ex (@acons _ zsym Γ σP _ φ anil)) ->
  IZF (ι V :: Γ) (φ :: wk_list [ι V] Ξ) (ren_tm χ (wk [ι V])) -> IZF Γ Ξ χ.
Proof. intros H1 H2. exact (zex_E Ξ φ χ H1 H2). Qed.

Lemma zand_L2 {Γ} (Ξ : list (zform Γ)) A B C D : IZF Γ (A :: B :: C :: Ξ) D -> IZF Γ (A :: And B C :: Ξ) D.
Proof.
  intros H. apply (deriv_cut_gen _ _ _ H). intros χ [<-|[<-|[<-|Hχ]]].
  - zhyp.
  - zap (zand_E1 _ _ C). zhyp.
  - zap (zand_E2 _ B). zhyp.
  - zhyp.
Qed.

(** Élimination de l'hypothèse de tête ∃x. φ (sans déplier φ), puis
    décomposition d'une conjonction. *)
Ltac zdes :=
  match goal with |- IZF _ (?h :: _) _ =>
    let h' := eval hnf in h in
    match h' with @tsym _ _ _ _ _ (@acons _ _ _ _ _ ?φ _) =>
      refine (zex_E_r _ φ _ _ _); [apply d_ax; left; reflexivity|]; try apply zand_L end end.
Ltac zdes2 :=
  match goal with |- IZF _ (_ :: ?h :: _) _ =>
    let h' := eval hnf in h in
    match h' with @tsym _ _ _ _ _ (@acons _ _ _ _ _ ?φ _) =>
      refine (zex_E_r _ φ _ _ _); [apply d_ax; right; left; reflexivity|]; try apply zand_L end end.

Definition PsiRec : zform [ι V; ι V; σP; σR; σP] := RecV (vs vz) φ3 vz.

Lemma fun_rec : IZF [σP; σR; σP] [Fun (eta σP (Γ := [σP; σR; σP]) φ2)] (Fun Frec).
Proof. exact (fun_S1_inst φ2 PsiRec). Qed.

(** L'ensemble de remplacement total existe : instance de [tot_repl]   (contexte [b; f; ψ]). *)
Lemma step_ex : IZF [ι V; ι V; σR] [] (zEx (StepEq vz (vs vz) φ2 φ3)).
Proof.
  pose proof (zuse tot_repl (vPR (zEq x0 x1 : zform [ι V; ι V; ι V; σR]) (RF φ3 φ4 vz (vs vz))) []) as K.
  cbn [vsubst_list map] in K.
  zap (zex_E _ (zEx (And (zEq x0 x2) (zAll (zIff (zMem x0 x2) (And (FnR (vs vz) φ4 φ5) (ExR (vs vz) φ4 φ5 vz))))))).
  { apply K. intros χ [<-|[]]. refine (_ : IZF _ _ (zEx (zEq x0 x1))). zap (zex_I _ _ x0). zap zeq_refl. }
  zdes.
  (* [a; y; b; f; ψ] *)
  refine (_ : IZF _ _ (zEx (StepEq vz φ3 φ4 φ5))). zap (zex_I _ _ x1).
  refine (_ : IZF _ _ (StepEq (vs vz) φ2 φ3 φ4)).
  zap (zeq_subst _ (StepEq φ2 vz φ4 φ5) x0 x2); zhyp.
Qed.

(** ** Couples de Kuratowski *)

(** {b} existe   (contexte [b]). *)
Lemma sg_ex : IZF [ι V] [] (zEx (Sg vz (vs vz))).
Proof.
  zap (zex_E _ (zAll (zIff (zMem x0 x1) (Or (zEq x0 x2) (zEq x0 x2))))).
  { zinst (zEx (zAll (zIff (zMem x0 x1) (Or (zEq x0 x3) (zEq x0 x2))))) x0.
    zinst (zAll (zEx (zAll (zIff (zMem x0 x1) (Or (zEq x0 x3) (zEq x0 x2)))))) x0.
    exact (zaxm Z_pair _ anil). }
  (* [s; b] *)
  refine (_ : IZF _ _ (zEx (Sg vz φ2))). zap (zex_I _ _ x0).
  refine (_ : IZF _ _ (Sg vz (vs vz))). unfold Sg. zap zall_I.
  (* [z; s; b] *)
  apply ziff_I.
  - zap (zor_E _ (zEq x0 x2) (zEq x0 x2)); [|zhyp|zhyp].
    apply (ziff_E1 _ (zMem x0 x1)); [|zhyp].
    zinst (zIff (zMem x0 x2) (Or (zEq x0 x3) (zEq x0 x3))) x0. zhyp.
  - apply (ziff_E2 _ _ (Or (zEq x0 x2) (zEq x0 x2))).
    { zinst (zIff (zMem x0 x2) (Or (zEq x0 x3) (zEq x0 x3))) x0. zhyp. }
    zap zor_I1. zhyp.
Qed.

(** {b, v} existe   (contexte [b; v]). *)
Lemma db_ex : IZF [ι V; ι V] [] (zEx (Db vz (vs vz) φ2)).
Proof.
  zinst (zEx (zAll (zIff (zMem x0 x1) (Or (zEq x0 x3) (zEq x0 x2))))) x1.
  zinst (zAll (zEx (zAll (zIff (zMem x0 x1) (Or (zEq x0 x3) (zEq x0 x2)))))) x0.
  exact (zaxm Z_pair _ anil).
Qed.

Definition zv1 {Γ} (a : ztm Γ V) : vec zsym [ι V] Γ := @acons _ zsym Γ (ι V) _ a anil.
Definition zv4 {Γ} (a b c d : ztm Γ V) : vec zsym [ι V; ι V; ι V; ι V] Γ := @acons _ zsym Γ (ι V) _ a (zv3 b c d).
Definition zv5 {Γ} (a b c d e : ztm Γ V) : vec zsym [ι V; ι V; ι V; ι V; ι V] Γ := @acons _ zsym Γ (ι V) _ a (zv4 b c d e).

(** b ∈ {b}, et c ∈ {b} → c = b   (contexte [x; b; c]). *)
Lemma mem_sg : IZF [ι V; ι V] [Sg vz (vs vz)] (zMem x1 x0).
Proof.
  apply (ziff_E2 _ _ (zEq x1 x1)); [zinst (zIff (zMem x0 x1) (zEq x0 x2)) x1; zhyp|zap zeq_refl].
Qed.

Lemma sg_eq : IZF [ι V; ι V; ι V] [Sg vz (vs vz); zMem x2 x0] (zEq x2 x1).
Proof. apply (ziff_E1 _ (zMem x2 x0)); [zinst (zIff (zMem x0 x1) (zEq x0 x2)) x2; zhyp|zhyp]. Qed.

(** b, v ∈ {b, v}, et c ∈ {b, v} → c = b ∨ c = v   (contexte [x; b; v; c]). *)
Lemma db_mem1 : IZF [ι V; ι V; ι V] [Db vz (vs vz) φ2] (zMem x1 x0).
Proof.
  apply (ziff_E2 _ _ (Or (zEq x1 x1) (zEq x1 x2))).
  { zinst (zIff (zMem x0 x1) (Or (zEq x0 x2) (zEq x0 x3))) x1. zhyp. }
  zap zor_I1. zap zeq_refl.
Qed.

Lemma db_mem2 : IZF [ι V; ι V; ι V] [Db vz (vs vz) φ2] (zMem x2 x0).
Proof.
  apply (ziff_E2 _ _ (Or (zEq x2 x1) (zEq x2 x2))).
  { zinst (zIff (zMem x0 x1) (Or (zEq x0 x2) (zEq x0 x3))) x2. zhyp. }
  zap zor_I2. zap zeq_refl.
Qed.

Lemma db_eq : IZF [ι V; ι V; ι V; ι V] [Db vz (vs vz) φ2; zMem x3 x0] (Or (zEq x3 x1) (zEq x3 x2)).
Proof.
  apply (ziff_E1 _ (zMem x3 x0)); [|zhyp].
  zinst (zIff (zMem x0 x1) (Or (zEq x0 x2) (zEq x0 x3))) x3. zhyp.
Qed.

(** Les éléments de ⟨b, v⟩   (contexte [p; b; v; x]). *)
Lemma op_in_sg : IZF [ι V; ι V; ι V; ι V] [OP vz (vs vz) φ2; Sg φ3 (vs vz)] (zMem x3 x0).
Proof.
  apply (ziff_E2 _ _ (Or (Sg φ3 (vs vz)) (Db φ3 (vs vz) φ2))).
  { zinst (zIff (zMem x0 x1) (Or (Sg vz φ2) (Db vz φ2 φ3))) x3. zhyp. }
  zap zor_I1. zhyp.
Qed.

Lemma op_in_db : IZF [ι V; ι V; ι V; ι V] [OP vz (vs vz) φ2; Db φ3 (vs vz) φ2] (zMem x3 x0).
Proof.
  apply (ziff_E2 _ _ (Or (Sg φ3 (vs vz)) (Db φ3 (vs vz) φ2))).
  { zinst (zIff (zMem x0 x1) (Or (Sg vz φ2) (Db vz φ2 φ3))) x3. zhyp. }
  zap zor_I2. zhyp.
Qed.

Lemma op_mem : IZF [ι V; ι V; ι V; ι V] [OP vz (vs vz) φ2; zMem x3 x0] (Or (Sg φ3 (vs vz)) (Db φ3 (vs vz) φ2)).
Proof.
  apply (ziff_E1 _ (zMem x3 x0)); [|zhyp].
  zinst (zIff (zMem x0 x1) (Or (Sg vz φ2) (Db vz φ2 φ3))) x3. zhyp.
Qed.

(** Injectivité : ⟨b, v⟩ = ⟨b', v'⟩ → b = b' ∧ v = v'   (contexte [p; b; v; b'; v']). *)
Lemma op_inj : IZF [ι V; ι V; ι V; ι V; ι V] [OP vz (vs vz) φ2; OP vz φ3 φ4] (And (zEq x1 x3) (zEq x2 x4)).
Proof.
  apply (deriv_cut ZC Pr RIZF (φ := zEq x1 x3)).
  { zap (zex_E _ (Sg vz φ2)); [zuses sg_ex (zv1 x1)|].
    (* [s; p; b; v; b'; v'] *)
    refine (_ : IZF _ _ (zEq x2 x4)).
    apply (deriv_cut ZC Pr RIZF (φ := zMem x0 x1)); [zuses op_in_sg (zv4 x1 x2 x3 x0); zhyp|].
    zap (zor_E _ (Sg vz φ4) (Db vz φ4 φ5)); [zuses op_mem (zv4 x1 x4 x5 x0); zhyp| |].
    - zuses sg_eq (zv3 x0 x4 x2); [zhyp|]. zuses mem_sg (zv2 x0 x2); zhyp.
    - zap zeq_sym. zuses sg_eq (zv3 x0 x2 x4); [zhyp|]. zuses db_mem1 (zv3 x0 x4 x5); zhyp. }
  zap zand_I; [zhyp|].
  (* v = b ∨ v = v' *)
  apply (deriv_cut ZC Pr RIZF (φ := Or (zEq x2 x1) (zEq x2 x4))).
  { zap (zex_E _ (Db vz φ2 φ3)); [zuses db_ex (zv2 x1 x2)|].
    (* [t; p; b; v; b'; v'] *)
    refine (_ : IZF _ _ (Or (zEq x3 x2) (zEq x3 x5))).
    apply (deriv_cut ZC Pr RIZF (φ := zMem x0 x1)); [zuses op_in_db (zv4 x1 x2 x3 x0); zhyp|].
    apply (deriv_cut ZC Pr RIZF (φ := zMem x3 x0)); [zuses db_mem2 (zv3 x0 x2 x3); zhyp|].
    zap (zor_E _ (Sg vz φ4) (Db vz φ4 φ5)); [zuses op_mem (zv4 x1 x4 x5 x0); zhyp| |].
    - zap zor_I1. zap (zeq_trans _ x3 x4 x2); [|zap zeq_sym; zhyp].
      zuses sg_eq (zv3 x0 x4 x3); zhyp.
    - zap (zor_E _ (zEq x3 x4) (zEq x3 x5)); [zuses db_eq (zv4 x0 x4 x5 x3); zhyp| |].
      + zap zor_I1. zap (zeq_trans _ x3 x4 x2); [zhyp|zap zeq_sym; zhyp].
      + zap zor_I2. zhyp. }
  (* v' = b ∨ v' = v *)
  apply (deriv_cut ZC Pr RIZF (φ := Or (zEq x4 x1) (zEq x4 x2))).
  { zap (zex_E _ (Db vz φ4 φ5)); [zuses db_ex (zv2 x3 x4)|].
    (* [t'; p; b; v; b'; v'] *)
    refine (_ : IZF _ _ (Or (zEq x5 x2) (zEq x5 x3))).
    apply (deriv_cut ZC Pr RIZF (φ := zMem x0 x1)); [zuses op_in_db (zv4 x1 x4 x5 x0); zhyp|].
    apply (deriv_cut ZC Pr RIZF (φ := zMem x5 x0)); [zuses db_mem2 (zv3 x0 x4 x5); zhyp|].
    zap (zor_E _ (Sg vz φ2) (Db vz φ2 φ3)); [zuses op_mem (zv4 x1 x2 x3 x0); zhyp| |].
    - zap zor_I1. zuses sg_eq (zv3 x0 x2 x5); zhyp.
    - zuses db_eq (zv4 x0 x2 x3 x5); zhyp. }
  zap (zor_E _ (zEq x2 x1) (zEq x2 x4)); [zhyp| |zhyp].
  zap (zor_E _ (zEq x4 x1) (zEq x4 x2)); [zhyp| |].
  - zap (zeq_trans _ x2 x1 x4); [zhyp|zap zeq_sym; zhyp].
  - zap zeq_sym. zhyp.
Qed.

(** Unicité de {b} et de {b, v}   (contextes [x; y; b] et [x; y; b; v]). *)
Lemma sg_uniq : IZF [ι V; ι V; ι V] [Sg vz φ2; Sg (vs vz) φ2] (zEq x0 x1).
Proof.
  zap (zimp_E _ (zAll (zIff (zMem x0 x1) (zMem x0 x2)))).
  { zinst (Imp (zAll (zIff (zMem x0 x2) (zMem x0 x1))) (zEq x1 x0)) x1.
    zinst (zAll (Imp (zAll (zIff (zMem x0 x2) (zMem x0 x1))) (zEq x1 x0))) x0.
    exact (zaxm Z_ext _ anil). }
  zap zall_I. apply (ziff_trans _ _ (zEq x0 x3)).
  - zinst (zIff (zMem x0 x2) (zEq x0 x4)) x0. zhyp.
  - apply ziff_sym. zinst (zIff (zMem x0 x3) (zEq x0 x4)) x0. zhyp.
Qed.

Lemma db_uniq : IZF [ι V; ι V; ι V; ι V] [Db vz φ2 φ3; Db (vs vz) φ2 φ3] (zEq x0 x1).
Proof.
  zap (zimp_E _ (zAll (zIff (zMem x0 x1) (zMem x0 x2)))).
  { zinst (Imp (zAll (zIff (zMem x0 x2) (zMem x0 x1))) (zEq x1 x0)) x1.
    zinst (zAll (Imp (zAll (zIff (zMem x0 x2) (zMem x0 x1))) (zEq x1 x0))) x0.
    exact (zaxm Z_ext _ anil). }
  zap zall_I. apply (ziff_trans _ _ (Or (zEq x0 x3) (zEq x0 x4))).
  - zinst (zIff (zMem x0 x2) (Or (zEq x0 x4) (zEq x0 x5))) x0. zhyp.
  - apply ziff_sym. zinst (zIff (zMem x0 x3) (Or (zEq x0 x4) (zEq x0 x5))) x0. zhyp.
Qed.

(** ⟨b, v⟩ existe   (contexte [b; v]). *)
Lemma op_ex : IZF [ι V; ι V] [] (zEx (OP vz (vs vz) φ2)).
Proof.
  zap (zex_E _ (Sg vz (vs vz))); [zuses sg_ex (zv1 x0)|].
  zap (zex_E _ (Db vz φ2 φ3)); [zuses db_ex (zv2 x1 x2)|].
  (* [t; s; b; v] *)
  zap (zex_E _ (zAll (zIff (zMem x0 x1) (Or (zEq x0 x3) (zEq x0 x2))))).
  { zinst (zEx (zAll (zIff (zMem x0 x1) (Or (zEq x0 x4) (zEq x0 x2))))) x0.
    zinst (zAll (zEx (zAll (zIff (zMem x0 x1) (Or (zEq x0 x3) (zEq x0 x2)))))) x1.
    exact (zaxm Z_pair _ anil). }
  (* [p; t; s; b; v] *)
  refine (_ : IZF _ _ (zEx (OP vz φ4 φ5))). zap (zex_I _ _ x0).
  refine (_ : IZF _ _ (OP vz φ3 φ4)). unfold OP. zap zall_I.
  (* [x; p; t; s; b; v] *)
  apply ziff_I.
  - zap (zor_E _ (zEq x0 x3) (zEq x0 x2)).
    { apply (ziff_E1 _ (zMem x0 x1)); [|zhyp]. zinst (zIff (zMem x0 x2) (Or (zEq x0 x4) (zEq x0 x3))) x0. zhyp. }
    + zap zor_I1. zap (zeq_subst _ (Sg vz φ5) x3 x0); [zap zeq_sym; zhyp|zhyp].
    + zap zor_I2. zap (zeq_subst _ (Db vz φ5 φ6) x2 x0); [zap zeq_sym; zhyp|zhyp].
  - apply (ziff_E2 _ _ (Or (zEq x0 x3) (zEq x0 x2))).
    { zinst (zIff (zMem x0 x2) (Or (zEq x0 x4) (zEq x0 x3))) x0. zhyp. }
    zap (zor_E _ (Sg vz φ4) (Db vz φ4 φ5)); [zhyp| |].
    + zap zor_I1. zuses sg_uniq (zv3 x0 x3 x4); zhyp.
    + zap zor_I2. zuses db_uniq (zv4 x0 x2 x4 x5); zhyp.
Qed.

(** ** Relations égales sur b *)

(** ∀α ∈ b. ∀β. R(α, β) ↔ R'(α, β). *)
Definition RelEqOn {Γ} (b : var Γ (ι V)) (R R' : var Γ σR) : zform Γ :=
  zAll (Imp (zMem x0 (var0 (vs b))) (zAll (zIff (zapp2 (vs (vs R)) x1 x0) (zapp2 (vs (vs R')) x1 x0)))).
(** v = {β | Fn(b, R) ∧ ∃α ∈ b. R(α, β)}. *)
Definition StepG {Γ} (v b : var Γ (ι V)) (R : var Γ σR) : zform Γ :=
  zAll (zIff (zMem x0 (var0 (vs v))) (And (FnAt (vs b) (vs R)) (ExIn (vs b) (vs R) vz))).

Definition wRR {Γ} (b : ztm Γ V) (R R' : var Γ σR) : vec zsym [ι V; σR; σR] Γ :=
  @acons _ zsym Γ (ι V) _ b (@acons _ zsym Γ σR _ (eta σR R) (@acons _ zsym Γ σR _ (eta σR R') anil)).
Definition wVRR {Γ} (z b : ztm Γ V) (R R' : var Γ σR) : vec zsym [ι V; ι V; σR; σR] Γ :=
  @acons _ zsym Γ (ι V) _ z (wRR b R R').

(** Contexte [b; R; R']. *)
Lemma releq_sym : IZF [ι V; σR; σR] [RelEqOn vz (vs vz) φ2] (RelEqOn vz φ2 (vs vz)).
Proof.
  refine (_ : IZF _ _ (zAll (Imp (zMem x0 x1) (zAll (zIff (zapp2 φ4 x1 x0) (zapp2 φ3 x1 x0)))))).
  zap zall_I. zap zimp_I. zap zall_I.
  (* [β; α; b; R; R'] *)
  apply ziff_sym. zinst (zIff (zapp2 φ4 x2 x0) (zapp2 φ5 x2 x0)) x0.
  zap (zimp_E _ (zMem x1 x2)); [|zhyp].
  zinst (Imp (zMem x0 x3) (zAll (zIff (zapp2 φ5 x1 x0) (zapp2 φ6 x1 x0)))) x1. zhyp.
Qed.

Lemma fn_cong1 : IZF [ι V; σR; σR] [RelEqOn vz (vs vz) φ2; FnAt vz (vs vz)] (FnAt vz φ2).
Proof.
  refine (_ : IZF _ _ (zAll (Imp (zMem x0 x1) (zEx (And (zapp2 φ4 x1 x0) (zAll (Imp (zapp2 φ5 x2 x0) (zEq x0 x1)))))))).
  zap zall_I. zap zimp_I.
  (* [α; b; R; R'] *)
  zap (zex_E _ (And (zapp2 φ3 x1 x0) (zAll (Imp (zapp2 φ4 x2 x0) (zEq x0 x1))))).
  { zap (zimp_E _ (zMem x0 x1)); [|zhyp].
    zinst (Imp (zMem x0 x2) (zEx (And (zapp2 φ4 x1 x0) (zAll (Imp (zapp2 φ5 x2 x0) (zEq x0 x1)))))) x0. zhyp. }
  apply zand_L.
  (* [β; α; b; R; R'] *)
  refine (_ : IZF _ _ (zEx (And (zapp2 φ5 x2 x0) (zAll (Imp (zapp2 φ6 x3 x0) (zEq x0 x1)))))).
  zap (zex_I _ _ x0). refine (_ : IZF _ _ (And (zapp2 φ4 x1 x0) (zAll (Imp (zapp2 φ5 x2 x0) (zEq x0 x1))))).
  zap zand_I.
  - apply (ziff_E1 _ (zapp2 φ3 x1 x0)); [|zhyp].
    zinst (zIff (zapp2 φ4 x2 x0) (zapp2 φ5 x2 x0)) x0. zap (zimp_E _ (zMem x1 x2)); [|zhyp].
    zinst (Imp (zMem x0 x3) (zAll (zIff (zapp2 φ5 x1 x0) (zapp2 φ6 x1 x0)))) x1. zhyp.
  - zap zall_I. zap zimp_I.
    (* [β'; β; α; b; R; R'] *)
    zap (zimp_E _ (zapp2 φ4 x2 x0)); [zinst (Imp (zapp2 φ5 x3 x0) (zEq x0 x2)) x0; zhyp|].
    apply (ziff_E2 _ _ (zapp2 φ5 x2 x0)); [|zhyp].
    zinst (zIff (zapp2 φ5 x3 x0) (zapp2 φ6 x3 x0)) x0. zap (zimp_E _ (zMem x2 x3)); [|zhyp].
    zinst (Imp (zMem x0 x4) (zAll (zIff (zapp2 φ6 x1 x0) (zapp2 φ7 x1 x0)))) x2. zhyp.
Qed.

Lemma fn_cong : IZF [ι V; σR; σR] [RelEqOn vz (vs vz) φ2] (zIff (FnAt vz (vs vz)) (FnAt vz φ2)).
Proof.
  apply ziff_I.
  - zuses fn_cong1 (wRR x0 (vs vz) φ2); zhyp.
  - zuses fn_cong1 (wRR x0 φ2 (vs vz)); [|zhyp]. zuses releq_sym (wRR x0 (vs vz) φ2). zhyp.
Qed.

(** Contexte [z; b; R; R']. *)
Lemma ex_cong1 : IZF [ι V; ι V; σR; σR] [RelEqOn (vs vz) φ2 φ3; ExIn (vs vz) φ2 vz] (ExIn (vs vz) φ3 vz).
Proof.
  zap (zex_E _ (And (zMem x0 x2) (zapp2 φ3 x0 x1))); [zhyp|]. apply zand_L.
  (* [α; z; b; R; R'] *)
  refine (_ : IZF _ _ (zEx (And (zMem x0 x3) (zapp2 φ5 x0 x2)))).
  zap (zex_I _ _ x0). refine (_ : IZF _ _ (And (zMem x0 x2) (zapp2 φ4 x0 x1))). zap zand_I; [zhyp|].
  apply (ziff_E1 _ (zapp2 φ3 x0 x1)); [|zhyp].
  zinst (zIff (zapp2 φ4 x1 x0) (zapp2 φ5 x1 x0)) x1. zap (zimp_E _ (zMem x0 x2)); [|zhyp].
  zinst (Imp (zMem x0 x3) (zAll (zIff (zapp2 φ5 x1 x0) (zapp2 φ6 x1 x0)))) x0. zhyp.
Qed.

Lemma ex_cong : IZF [ι V; ι V; σR; σR] [RelEqOn (vs vz) φ2 φ3] (zIff (ExIn (vs vz) φ2 vz) (ExIn (vs vz) φ3 vz)).
Proof.
  apply ziff_I.
  - zuses ex_cong1 (wVRR x0 x1 φ2 φ3); zhyp.
  - zuses ex_cong1 (wVRR x0 x1 φ3 φ2); [|zhyp]. zuses releq_sym (wRR x1 φ2 φ3). zhyp.
Qed.

(** Contexte [v; b; R; R']. *)
Lemma step_cong : IZF [ι V; ι V; σR; σR] [RelEqOn (vs vz) φ2 φ3; StepG vz (vs vz) φ2] (StepG vz (vs vz) φ3).
Proof.
  refine (_ : IZF _ _ (zAll (zIff (zMem x0 x1) (And (FnAt φ2 φ4) (ExIn φ2 φ4 vz))))).
  zap zall_I.
  (* [z; v; b; R; R'] *)
  apply (ziff_trans _ _ (And (FnAt φ2 φ3) (ExIn φ2 φ3 vz))).
  - zinst (zIff (zMem x0 x2) (And (FnAt φ3 φ4) (ExIn φ3 φ4 vz))) x0. zhyp.
  - apply ziff_and.
    + zuses fn_cong (wRR x2 φ3 φ4). zhyp.
    + zuses ex_cong (wVRR x0 x2 φ3 φ4). zhyp.
Qed.

(** Contexte [v; w; b; R]. *)
Lemma step_uniq : IZF [ι V; ι V; ι V; σR] [StepG vz φ2 φ3; StepG (vs vz) φ2 φ3] (zEq x0 x1).
Proof.
  zap (zimp_E _ (zAll (zIff (zMem x0 x1) (zMem x0 x2)))).
  { zinst (Imp (zAll (zIff (zMem x0 x2) (zMem x0 x1))) (zEq x1 x0)) x1.
    zinst (zAll (Imp (zAll (zIff (zMem x0 x2) (zMem x0 x1))) (zEq x1 x0))) x0.
    exact (zaxm Z_ext _ anil). }
  zap zall_I. apply (ziff_trans _ _ (And (FnAt φ3 φ4) (ExIn φ3 φ4 vz))).
  - zinst (zIff (zMem x0 x2) (And (FnAt φ4 φ5) (ExIn φ4 φ5 vz))) x0. zhyp.
  - apply ziff_sym. zinst (zIff (zMem x0 x3) (And (FnAt φ4 φ5) (ExIn φ4 φ5 vz))) x0. zhyp.
Qed.

(** ** Unicité des essais *)

Local Notation φ10 := (vs φ9).
Local Notation φ11 := (vs φ10).
Local Notation φ12 := (vs φ11).
Local Notation x9 := (var0 φ9).
Local Notation x10 := (var0 φ10).
Local Notation x11 := (var0 φ11).

(** R_f comme argument de spécification σR (α variable 0, β variable 1). *)
Definition wRF {Γ} (f : var Γ (ι V)) (ψ : var Γ σR) : zform (ι V :: ι V :: Γ) := RF (vs (vs f)) (vs (vs ψ)) vz (vs vz).
Definition wSC {Γ} (v b : ztm Γ V) (R R' : zform (ι V :: ι V :: Γ)) : vec zsym [ι V; ι V; σR; σR] Γ :=
  @acons _ zsym Γ (ι V) _ v (@acons _ zsym Γ (ι V) _ b (@acons _ zsym Γ σR _ R (@acons _ zsym Γ σR _ R' anil))).
Definition wSU {Γ} (v w b : ztm Γ V) (R : zform (ι V :: ι V :: Γ)) : vec zsym [ι V; ι V; ι V; σR] Γ :=
  @acons _ zsym Γ (ι V) _ v (@acons _ zsym Γ (ι V) _ w (@acons _ zsym Γ (ι V) _ b (@acons _ zsym Γ σR _ R anil))).
Definition wVR {Γ} (f : ztm Γ V) (ψ : var Γ σR) : vec zsym [ι V; σR] Γ :=
  @acons _ zsym Γ (ι V) _ f (@acons _ zsym Γ σR _ (eta σR ψ) anil).

(** ∀α ∈ b. ∀β. R_f(α, β) ↔ R_g(α, β). *)
Definition RFeq {Γ} (b f g : var Γ (ι V)) (ψ : var Γ σR) : zform Γ :=
  zAll (Imp (zMem x0 (var0 (vs b)))
            (zAll (zIff (RF (vs (vs f)) (vs (vs ψ)) (vs vz) vz) (RF (vs (vs g)) (vs (vs ψ)) (vs vz) vz)))).

(** P(b) : ∀v w. ⟨b, v⟩ ∈ f → ⟨b, w⟩ ∈ g → v = w. *)
Definition Pu {Γ} (b f g : var Γ (ι V)) : zform Γ :=
  zAll (zAll (Imp (InF (vs (vs f)) (vs (vs b)) (vs vz)) (Imp (InF (vs (vs g)) (vs (vs b)) vz) (zEq x1 x0)))).

Lemma att_fn : IZF [ι V; σR] [Att vz (vs vz)] (AttFn vz).
Proof. zap (zand_E1 _ _ (And (AttDc vz) (AttCr vz (vs vz)))). zhyp. Qed.
Lemma att_dc : IZF [ι V; σR] [Att vz (vs vz)] (AttDc vz).
Proof. zap (zand_E1 _ _ (AttCr vz (vs vz))). zap (zand_E2 _ (AttFn vz)). zhyp. Qed.
Lemma att_cr : IZF [ι V; σR] [Att vz (vs vz)] (AttCr vz (vs vz)).
Proof. zap (zand_E2 _ (AttDc vz)). zap (zand_E2 _ (AttFn vz)). zhyp. Qed.

(** Deux essais s'accordent   (contexte [f; g; ψ]). *)
Lemma att_uniq : IZF [ι V; ι V; σR] [AttDc vz; AttCr vz φ2; AttDc (vs vz); AttCr (vs vz) φ2] (zAll (Pu vz (vs vz) φ2)).
Proof.
  zap (zimp_E _ (zAll (Imp (zAll (Imp (zMem x0 x1) (Pu vz φ2 φ3))) (Pu vz (vs vz) φ2)))).
  { exact (zaxm Z_ind _ (v1 (Pu vz (vs vz) φ2))). }
  zap zall_I. zap zimp_I.
  (* [b; f; g; ψ] *)
  refine (_ : IZF _ _ (Pu vz (vs vz) φ2)). unfold Pu at 2. zap zall_I. zap zall_I. zap zimp_I. zap zimp_I.
  (* [w; v; b; f; g; ψ] *)
  (* R_f = R_g sur b *)
  apply (deriv_cut ZC Pr RIZF (φ := RFeq φ2 φ3 φ4 φ5)).
  { refine (_ : IZF _ _ (zAll (Imp (zMem x0 x3) (zAll (zIff (RF φ5 φ7 (vs vz) vz) (RF φ6 φ7 (vs vz) vz)))))).
    zap zall_I. zap zimp_I. zap zall_I.
    (* [β; α; w; v; b; f; g; ψ] *)
    apply ziff_I.
    - zdes.
      (* [u; β; α; w; v; b; f; g; ψ] *)
      zap (zex_E _ (InF φ8 φ3 vz)).
      { zap (zimp_E _ (zMem x2 x5)); [|zhyp].
        zinst (Imp (zMem x0 x6) (zEx (InF φ9 (vs vz) vz))) x2.
        zap (zimp_E _ (InF φ7 φ5 φ3)); [|zhyp].
        zinst (Imp (InF φ8 φ6 vz) (zAll (Imp (zMem x0 x7) (zEx (InF φ10 (vs vz) vz))))) x3.
        zinst (zAll (Imp (InF φ9 (vs vz) vz) (zAll (Imp (zMem x0 x2) (zEx (InF φ11 (vs vz) vz)))))) x5.
        zhyp. }
      (* [u'; u; β; α; w; v; b; f; g; ψ] *)
      apply (deriv_cut ZC Pr RIZF (φ := zEq x1 x0)).
      { zap (zimp_E _ (InF φ8 φ3 vz)); [|zhyp].
        zap (zimp_E _ (InF φ7 φ3 (vs vz))); [|zhyp].
        zinst (Imp (InF φ8 φ4 (vs (vs vz))) (Imp (InF φ9 φ4 vz) (zEq x2 x0))) x0.
        zinst (zAll (Imp (InF φ9 φ5 (vs vz)) (Imp (InF φ10 φ5 vz) (zEq x1 x0)))) x1.
        zap (zimp_E _ (zMem x3 x6)); [|zhyp].
        zinst (Imp (zMem x0 x7) (Pu vz φ8 φ9)) x3. zhyp. }
      refine (_ : IZF _ _ (RF φ8 φ9 φ3 φ2)). zap (zex_I _ _ x0).
      refine (_ : IZF _ _ (And (InF φ8 φ3 vz) (zapp2 φ9 x0 x2))). zap zand_I; [zhyp|].
      zap (zeq_subst _ (zapp2 φ10 x0 x3) x1 x0); zhyp.
    - zdes.
      (* [u; β; α; w; v; b; f; g; ψ] *)
      zap (zex_E _ (InF φ7 φ3 vz)).
      { zap (zimp_E _ (zMem x2 x5)); [|zhyp].
        zinst (Imp (zMem x0 x6) (zEx (InF φ8 (vs vz) vz))) x2.
        zap (zimp_E _ (InF φ6 φ5 φ4)); [|zhyp].
        zinst (Imp (InF φ7 φ6 vz) (zAll (Imp (zMem x0 x7) (zEx (InF φ9 (vs vz) vz))))) x4.
        zinst (zAll (Imp (InF φ8 (vs vz) vz) (zAll (Imp (zMem x0 x2) (zEx (InF φ10 (vs vz) vz)))))) x5.
        zhyp. }
      (* [u'; u; β; α; w; v; b; f; g; ψ] *)
      apply (deriv_cut ZC Pr RIZF (φ := zEq x0 x1)).
      { zap (zimp_E _ (InF φ8 φ3 (vs vz))); [|zhyp].
        zap (zimp_E _ (InF φ7 φ3 vz)); [|zhyp].
        zinst (Imp (InF φ8 φ4 (vs vz)) (Imp (InF φ9 φ4 vz) (zEq x1 x0))) x1.
        zinst (zAll (Imp (InF φ9 φ5 (vs vz)) (Imp (InF φ10 φ5 vz) (zEq x1 x0)))) x0.
        zap (zimp_E _ (zMem x3 x6)); [|zhyp].
        zinst (Imp (zMem x0 x7) (Pu vz φ8 φ9)) x3. zhyp. }
      refine (_ : IZF _ _ (RF φ7 φ9 φ3 φ2)). zap (zex_I _ _ x0).
      refine (_ : IZF _ _ (And (InF φ7 φ3 vz) (zapp2 φ9 x0 x2))). zap zand_I; [zhyp|].
      zap (zeq_subst _ (zapp2 φ10 x0 x3) x1 x0); [zap zeq_sym; zhyp|zhyp]. }
  (* les deux valeurs sont correctes *)
  apply (deriv_cut ZC Pr RIZF (φ := StepEq (vs vz) φ2 φ3 φ5)).
  { zap (zimp_E _ (InF φ3 φ2 (vs vz))); [|zhyp].
    zinst (Imp (InF φ4 φ3 vz) (StepEq vz φ3 φ4 φ6)) x1.
    zinst (zAll (Imp (InF φ5 (vs vz) vz) (StepEq vz (vs vz) φ5 φ7))) x2. zhyp. }
  apply (deriv_cut ZC Pr RIZF (φ := StepEq vz φ2 φ4 φ5)).
  { zap (zimp_E _ (InF φ4 φ2 vz)); [|zhyp].
    zinst (Imp (InF φ5 φ3 vz) (StepEq vz φ3 φ5 φ6)) x0.
    zinst (zAll (Imp (InF φ6 (vs vz) vz) (StepEq vz (vs vz) φ6 φ7))) x2. zhyp. }
  zuses step_uniq (wSU x1 x0 x2 (wRF φ4 φ5)); [|zhyp].
  zuses step_cong (wSC x1 x2 (wRF φ3 φ5) (wRF φ4 φ5)); zhyp.
Qed.

(** ** Construire un essai *)

(** h ⊑ g : ∀c w. ⟨c, w⟩ ∈ h → ⟨c, w⟩ ∈ g. *)
Definition Sub {Γ} (h g : var Γ (ι V)) : zform Γ :=
  zAll (zAll (Imp (InF (vs (vs h)) (vs vz) vz) (InF (vs (vs g)) (vs vz) vz))).
(** h est défini sur b : ∀c ∈ b. ∃w. ⟨c, w⟩ ∈ h. *)
Definition DcAt {Γ} (h b : var Γ (ι V)) : zform Γ :=
  zAll (Imp (zMem x0 (var0 (vs b))) (zEx (InF (vs (vs h)) (vs vz) vz))).
(** Chaque ⟨b, w⟩ ∈ g est justifié par un h ⊑ g défini sur b où w est correct. *)
Definition Wit {Γ} (g : var Γ (ι V)) (ψ : var Γ σR) : zform Γ :=
  zAll (zAll (Imp (InF (vs (vs g)) (vs vz) vz)
                  (zEx (And (Sub vz (vs (vs (vs g)))) (And (DcAt vz φ2) (StepEq (vs vz) φ2 vz (vs (vs (vs ψ))))))))).

(** Contexte [g; ψ]. *)
Lemma att_intro : IZF [ι V; σR] [AttFn vz; Wit vz (vs vz)] (Att vz (vs vz)).
Proof.
  zap zand_I; [zhyp|]. zap zand_I.
  - refine (_ : IZF _ _ (zAll (zAll (Imp (InF φ2 (vs vz) vz) (zAll (Imp (zMem x0 x2) (zEx (InF φ4 (vs vz) vz)))))))).
    zap zall_I. zap zall_I. zap zimp_I. zap zall_I. zap zimp_I.
    (* [c; v; b; g; ψ] *)
    zap (zex_E _ (And (Sub vz φ4) (And (DcAt vz φ3) (StepEq φ2 φ3 vz φ5)))).
    { zap (zimp_E _ (InF φ3 φ2 (vs vz))); [|zhyp].
      zinst (Imp (InF φ4 φ3 vz) (zEx (And (Sub vz φ5) (And (DcAt vz φ4) (StepEq (vs vz) φ4 vz φ6))))) x1.
      zinst (zAll (Imp (InF φ5 (vs vz) vz) (zEx (And (Sub vz φ6) (And (DcAt vz φ2) (StepEq (vs vz) φ2 vz φ7)))))) x2.
      zhyp. }
    apply zand_L. apply zand_L2.
    (* [h; c; v; b; g; ψ] *)
    refine (_ : IZF _ _ (zEx (InF φ5 φ2 vz))).
    zap (zex_E _ (InF (vs vz) φ2 vz)).
    { zap (zimp_E _ (zMem x1 x3)); [|zhyp]. zinst (Imp (zMem x0 x4) (zEx (InF φ2 (vs vz) vz))) x1. zhyp. }
    (* [w'; h; c; v; b; g; ψ] *)
    zap (zex_I _ _ x0). refine (_ : IZF _ _ (InF φ5 φ2 vz)).
    zap (zimp_E _ (InF (vs vz) φ2 vz)); [|zhyp].
    zinst (Imp (InF φ2 φ3 vz) (InF φ6 φ3 vz)) x0.
    zinst (zAll (Imp (InF φ3 (vs vz) vz) (InF φ7 (vs vz) vz))) x2. zhyp.
  - refine (_ : IZF _ _ (zAll (zAll (Imp (InF φ2 (vs vz) vz) (StepEq vz (vs vz) φ2 φ3))))).
    zap zall_I. zap zall_I. zap zimp_I.
    (* [v; b; g; ψ] *)
    zap (zex_E _ (And (Sub vz φ3) (And (DcAt vz φ2) (StepEq (vs vz) φ2 vz φ4)))).
    { zap (zimp_E _ (InF φ2 (vs vz) vz)); [|zhyp].
      zinst (Imp (InF φ3 φ2 vz) (zEx (And (Sub vz φ4) (And (DcAt vz φ3) (StepEq (vs vz) φ3 vz φ5))))) x0.
      zinst (zAll (Imp (InF φ4 (vs vz) vz) (zEx (And (Sub vz φ5) (And (DcAt vz φ2) (StepEq (vs vz) φ2 vz φ6)))))) x1.
      zhyp. }
    apply zand_L. apply zand_L2.
    (* [h; v; b; g; ψ] *)
    refine (_ : IZF _ _ (StepEq (vs vz) φ2 φ3 φ4)).
    zuses step_cong (wSC x1 x2 (wRF vz φ4) (wRF φ3 φ4)); [|zhyp].
    refine (_ : IZF _ _ (zAll (Imp (zMem x0 x3) (zAll (zIff (RF φ2 φ6 (vs vz) vz) (RF φ5 φ6 (vs vz) vz)))))).
    zap zall_I. zap zimp_I. zap zall_I.
    (* [β; α; h; v; b; g; ψ] *)
    apply ziff_I.
    + zdes.
      (* [u; β; α; h; v; b; g; ψ] *)
      refine (_ : IZF _ _ (RF φ6 φ7 φ2 (vs vz))). zap (zex_I _ _ x0).
      refine (_ : IZF _ _ (And (InF φ6 φ2 vz) (zapp2 φ7 x0 x1))). zap zand_I; [|zhyp].
      zap (zimp_E _ (InF φ3 φ2 vz)); [|zhyp].
      zinst (Imp (InF φ4 φ3 vz) (InF φ7 φ3 vz)) x0.
      zinst (zAll (Imp (InF φ5 (vs vz) vz) (InF φ8 (vs vz) vz))) x2. zhyp.
    + zdes.
      (* [u; β; α; h; v; b; g; ψ] *)
      zap (zex_E _ (InF φ4 φ3 vz)).
      { zap (zimp_E _ (zMem x2 x5)); [|zhyp]. zinst (Imp (zMem x0 x6) (zEx (InF φ5 (vs vz) vz))) x2. zhyp. }
      (* [u'; u; β; α; h; v; b; g; ψ] *)
      apply (deriv_cut ZC Pr RIZF (φ := InF φ7 φ3 vz)).
      { zap (zimp_E _ (InF φ4 φ3 vz)); [|zhyp].
        zinst (Imp (InF φ5 φ4 vz) (InF φ8 φ4 vz)) x0.
        zinst (zAll (Imp (InF φ6 (vs vz) vz) (InF φ9 (vs vz) vz))) x3. zhyp. }
      apply (deriv_cut ZC Pr RIZF (φ := zEq x1 x0)).
      { zap (zimp_E _ (InF φ7 φ3 vz)); [|zhyp]. zap (zimp_E _ (InF φ7 φ3 (vs vz))); [|zhyp].
        zinst (Imp (InF φ8 φ4 (vs (vs vz))) (Imp (InF φ8 φ4 vz) (zEq x2 x0))) x0.
        zinst (zAll (Imp (InF φ9 φ5 (vs vz)) (Imp (InF φ9 φ5 vz) (zEq x1 x0)))) x1.
        zinst (zAll (zAll (Imp (InF φ10 (vs (vs vz)) (vs vz)) (Imp (InF φ10 (vs (vs vz)) vz) (zEq x1 x0))))) x3.
        zhyp. }
      refine (_ : IZF _ _ (RF φ4 φ8 φ3 φ2)). zap (zex_I _ _ x0).
      refine (_ : IZF _ _ (And (InF φ4 φ3 vz) (zapp2 φ8 x0 x2))). zap zand_I; [zhyp|].
      zap (zeq_subst _ (zapp2 φ9 x0 x3) x1 x0); zhyp.
Qed.

(** ** Réunion d'essais *)

(** g = ⋃S, vu à travers les couples : ⟨c, w⟩ ∈ g ↔ ∃f ∈ S. ⟨c, w⟩ ∈ f. *)
Definition ChUn {Γ} (g S : var Γ (ι V)) : zform Γ :=
  zAll (zAll (zIff (InF (vs (vs g)) (vs vz) vz) (zEx (And (zMem x0 (var0 (vs (vs (vs S))))) (InF vz φ2 (vs vz)))))).
Definition AllAtt {Γ} (S : var Γ (ι V)) (ψ : var Γ σR) : zform Γ :=
  zAll (Imp (zMem x0 (var0 (vs S))) (Att vz (vs ψ))).

Definition wVVR {Γ} (f g : ztm Γ V) (ψ : var Γ σR) : vec zsym [ι V; ι V; σR] Γ :=
  @acons _ zsym Γ (ι V) _ f (wVR g ψ).

(** Contexte [S]. *)
Lemma un_build : IZF [ι V] [] (zEx (ChUn vz (vs vz))).
Proof.
  zap (zex_E _ (zAll (zIff (zMem x0 x1) (zEx (And (zMem x1 x0) (zMem x0 x3)))))).
  { zinst (zEx (zAll (zIff (zMem x0 x1) (zEx (And (zMem x1 x0) (zMem x0 x3)))))) x0. exact (zaxm Z_union _ anil). }
  (* [g; S] *)
  refine (_ : IZF _ _ (zEx (ChUn vz φ2))). zap (zex_I _ _ x0). refine (_ : IZF _ _ (ChUn vz (vs vz))).
  unfold ChUn. zap zall_I. zap zall_I.
  (* [w; c; g; S] *)
  apply ziff_I.
  - zdes.
    (* [q; w; c; g; S] *)
    apply (deriv_cut ZC Pr RIZF (φ := zEx (And (zMem x1 x0) (zMem x0 x5)))).
    { apply (ziff_E1 _ (zMem x0 x3)); [|zhyp]. zinst (zIff (zMem x0 x4) (zEx (And (zMem x1 x0) (zMem x0 x6)))) x0. zhyp. }
    zdes.
    (* [b; q; w; c; g; S] *)
    refine (_ : IZF _ _ (zEx (And (zMem x0 x6) (InF vz φ4 φ3)))). zap (zex_I _ _ x0).
    refine (_ : IZF _ _ (And (zMem x0 x5) (InF vz φ3 φ2))). zap zand_I; [zhyp|].
    refine (_ : IZF _ _ (zEx (And (zMem x0 x1) (OP vz φ4 φ3)))). zap (zex_I _ _ x1).
    refine (_ : IZF _ _ (And (zMem x1 x0) (OP (vs vz) φ3 φ2))). zap zand_I; zhyp.
  - zdes. zdes2.
    (* [q; f; w; c; g; S] *)
    refine (_ : IZF _ _ (InF φ4 φ3 φ2)). refine (_ : IZF _ _ (zEx (And (zMem x0 x5) (OP vz φ4 φ3)))).
    zap (zex_I _ _ x0). refine (_ : IZF _ _ (And (zMem x0 x4) (OP vz φ3 φ2))). zap zand_I; [|zhyp].
    apply (ziff_E2 _ _ (zEx (And (zMem x1 x0) (zMem x0 x6)))).
    { zinst (zIff (zMem x0 x5) (zEx (And (zMem x1 x0) (zMem x0 x7)))) x0. zhyp. }
    refine (_ : IZF _ _ (zEx (And (zMem x1 x0) (zMem x0 x6)))). zap (zex_I _ _ x1).
    refine (_ : IZF _ _ (And (zMem x0 x1) (zMem x1 x5))). zap zand_I; zhyp.
Qed.

(** Une réunion d'essais est un essai   (contexte [g; S; ψ]). *)
Lemma un_att : IZF [ι V; ι V; σR] [AllAtt (vs vz) φ2; ChUn vz (vs vz)] (Att vz φ2).
Proof.
  zuses att_intro (wVR x0 φ2).
  - refine (_ : IZF _ _ (zAll (zAll (zAll (Imp (InF φ3 φ2 (vs vz)) (Imp (InF φ3 φ2 vz) (zEq x1 x0))))))).
    zap zall_I. zap zall_I. zap zall_I. zap zimp_I. zap zimp_I.
    (* [w; v; b; g; S; ψ] *)
    zap (zex_E _ (And (zMem x0 x5) (InF vz φ3 φ2))).
    { apply (ziff_E1 _ (InF φ3 φ2 (vs vz))); [|zhyp].
      zinst (zIff (InF φ4 φ3 vz) (zEx (And (zMem x0 x6) (InF vz φ4 (vs vz))))) x1.
      zinst (zAll (zIff (InF φ5 (vs vz) vz) (zEx (And (zMem x0 x7) (InF vz φ2 (vs vz)))))) x2. zhyp. }
    apply zand_L.
    (* [f1; w; v; b; g; S; ψ] *)
    zap (zex_E _ (And (zMem x0 x6) (InF vz φ4 φ2))).
    { apply (ziff_E1 _ (InF φ4 φ3 (vs vz))); [|zhyp].
      zinst (zIff (InF φ5 φ4 vz) (zEx (And (zMem x0 x7) (InF vz φ5 (vs vz))))) x1.
      zinst (zAll (zIff (InF φ6 (vs vz) vz) (zEx (And (zMem x0 x8) (InF vz φ2 (vs vz)))))) x3. zhyp. }
    apply zand_L.
    (* [f2; f1; w; v; b; g; S; ψ] *)
    apply (deriv_cut ZC Pr RIZF (φ := Att (vs vz) φ7)).
    { zap (zimp_E _ (zMem x1 x6)); [|zhyp]. zinst (Imp (zMem x0 x7) (Att vz φ8)) x1. zhyp. }
    apply (deriv_cut ZC Pr RIZF (φ := Att vz φ7)).
    { zap (zimp_E _ (zMem x0 x6)); [|zhyp]. zinst (Imp (zMem x0 x7) (Att vz φ8)) x0. zhyp. }
    refine (_ : IZF _ _ (zEq x3 x2)).
    zap (zimp_E _ (InF vz φ4 φ2)); [|zhyp]. zap (zimp_E _ (InF (vs vz) φ4 φ3)); [|zhyp].
    zinst (Imp (InF φ2 φ5 φ4) (Imp (InF (vs vz) φ5 vz) (zEq x4 x0))) x2.
    zinst (zAll (Imp (InF φ3 φ6 (vs vz)) (Imp (InF φ2 φ6 vz) (zEq x1 x0)))) x3.
    zinst (Pu vz φ2 (vs vz)) x4.
    zuses att_uniq (wVVR x1 x0 φ7).
    + zuses att_dc (wVR x1 φ7). zhyp.
    + zuses att_cr (wVR x1 φ7). zhyp.
    + zuses att_dc (wVR x0 φ7). zhyp.
    + zuses att_cr (wVR x0 φ7). zhyp.
  - refine (_ : IZF _ _ (zAll (zAll (Imp (InF φ2 (vs vz) vz) (zEx (And (Sub vz φ3) (And (DcAt vz φ2) (StepEq (vs vz) φ2 vz φ5)))))))).
    zap zall_I. zap zall_I. zap zimp_I.
    (* [w; b; g; S; ψ] *)
    zap (zex_E _ (And (zMem x0 x4) (InF vz φ2 (vs vz)))).
    { apply (ziff_E1 _ (InF φ2 (vs vz) vz)); [|zhyp].
      zinst (zIff (InF φ3 φ2 vz) (zEx (And (zMem x0 x5) (InF vz φ3 (vs vz))))) x0.
      zinst (zAll (zIff (InF φ4 (vs vz) vz) (zEx (And (zMem x0 x6) (InF vz φ2 (vs vz)))))) x1. zhyp. }
    apply zand_L.
    (* [f; w; b; g; S; ψ] *)
    apply (deriv_cut ZC Pr RIZF (φ := Att vz φ5)).
    { zap (zimp_E _ (zMem x0 x4)); [|zhyp]. zinst (Imp (zMem x0 x5) (Att vz φ6)) x0. zhyp. }
    refine (_ : IZF _ _ (zEx (And (Sub vz φ4) (And (DcAt vz φ3) (StepEq φ2 φ3 vz φ6))))).
    zap (zex_I _ _ x0). refine (_ : IZF _ _ (And (Sub vz φ3) (And (DcAt vz φ2) (StepEq (vs vz) φ2 vz φ5)))).
    zap zand_I; [|zap zand_I].
    + refine (_ : IZF _ _ (zAll (zAll (Imp (InF φ2 (vs vz) vz) (InF φ5 (vs vz) vz))))).
      zap zall_I. zap zall_I. zap zimp_I.
      (* [w'; c; f; w; b; g; S; ψ] *)
      apply (ziff_E2 _ _ (zEx (And (zMem x0 x7) (InF vz φ2 (vs vz))))).
      { zinst (zIff (InF φ6 φ2 vz) (zEx (And (zMem x0 x8) (InF vz φ3 (vs vz))))) x0.
        zinst (zAll (zIff (InF φ7 (vs vz) vz) (zEx (And (zMem x0 x9) (InF vz φ2 (vs vz)))))) x1. zhyp. }
      refine (_ : IZF _ _ (zEx (And (zMem x0 x7) (InF vz φ2 (vs vz))))). zap (zex_I _ _ x2).
      refine (_ : IZF _ _ (And (zMem x2 x6) (InF φ2 (vs vz) vz))). zap zand_I; zhyp.
    + zap (zimp_E _ (InF vz φ2 (vs vz))); [|zhyp].
      zinst (Imp (InF (vs vz) φ3 vz) (zAll (Imp (zMem x0 x4) (zEx (InF φ3 (vs vz) vz))))) x1.
      zinst (zAll (Imp (InF φ2 (vs vz) vz) (zAll (Imp (zMem x0 x2) (zEx (InF φ4 (vs vz) vz)))))) x2.
      zuses att_dc (wVR x0 φ5). zhyp.
    + zap (zimp_E _ (InF vz φ2 (vs vz))); [|zhyp].
      zinst (Imp (InF (vs vz) φ3 vz) (StepEq vz φ3 (vs vz) φ6)) x1.
      zinst (zAll (Imp (InF φ2 (vs vz) vz) (StepEq vz (vs vz) φ2 φ7))) x2.
      zuses att_cr (wVR x0 φ5). zhyp.
Qed.
