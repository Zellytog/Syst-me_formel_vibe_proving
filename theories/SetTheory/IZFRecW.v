(** * rec dans IZF : existence des essais, valeurs de rec

    Ajout d'un couple à un essai, existence d'un essai défini en tout a
    (∈-induction), d'où la totalité du graphe de rec. *)

From Stdlib Require Import List.
Import ListNotations.
From SF.Syntax Require Import Spec Terms Renaming Eta Vectors.
From SF.Calculus Require Import System Rules.
From SF.Logic Require Import Judgment Propositional.
From SF.Functional Require Import Arrow.
From SF.Quantifiers Require Import Quant Order.
From SF.SetTheory Require Import Sets IZFe IZF IZFTr IZFLog IZFVal IZFRecV.

Local Notation ι a := (Spec [] a).
Local Notation φ10 := (vs φ9).
Local Notation φ11 := (vs φ10).
Local Notation φ12 := (vs φ11).
Local Notation x9 := (var0 φ9).
Local Notation x10 := (var0 φ10).
Local Notation x11 := (var0 φ11).

Definition zv6 {Γ} (a b c d e f : ztm Γ V) : vec zsym [ι V; ι V; ι V; ι V; ι V; ι V] Γ := @acons _ zsym Γ (ι V) _ a (zv5 b c d e f).
Definition zv7R {Γ} (a b c d e f g : ztm Γ V) (ψ : var Γ σR) : vec zsym [ι V; ι V; ι V; ι V; ι V; ι V; ι V; σR] Γ :=
  @acons _ zsym Γ (ι V) _ a (@acons _ zsym Γ (ι V) _ b (@acons _ zsym Γ (ι V) _ c (@acons _ zsym Γ (ι V) _ d
    (@acons _ zsym Γ (ι V) _ e (@acons _ zsym Γ (ι V) _ f (@acons _ zsym Γ (ι V) _ g (@acons _ zsym Γ σR _ (eta σR ψ) anil))))))).

(** La fonctionnalité d'un essai, appliquée   (contexte [b; v; w; g]). *)
Lemma fn_use : IZF [ι V; ι V; ι V; ι V] [AttFn φ3; InF φ3 vz (vs vz); InF φ3 vz φ2] (zEq x1 x2).
Proof.
  zap (zimp_E _ (InF φ3 vz φ2)); [|zhyp]. zap (zimp_E _ (InF φ3 vz (vs vz))); [|zhyp].
  zinst (Imp (InF φ4 (vs vz) φ2) (Imp (InF φ4 (vs vz) vz) (zEq x2 x0))) x2.
  zinst (zAll (Imp (InF φ5 φ2 (vs vz)) (Imp (InF φ5 φ2 vz) (zEq x1 x0)))) x1.
  zinst (zAll (zAll (Imp (InF φ6 (vs (vs vz)) (vs vz)) (Imp (InF φ6 (vs (vs vz)) vz) (zEq x1 x0))))) x0.
  zhyp.
Qed.

(** ** Ajout d'un couple *)

(** ⟨c, w⟩ ∈ g' ↔ ⟨c, w⟩ ∈ g ∨ (c = a ∧ w = v). *)
Definition ChExt {Γ} (g' v g a : var Γ (ι V)) : zform Γ :=
  zAll (zAll (zIff (InF (vs (vs g')) (vs vz) vz)
                   (Or (InF (vs (vs g)) (vs vz) vz) (And (zEq x1 (var0 (vs (vs a)))) (zEq x0 (var0 (vs (vs v)))))))).

(** Contexte [c; w; g'; v; g; a]. *)
Lemma chext_E : IZF [ι V; ι V; ι V; ι V; ι V; ι V] [ChExt φ2 φ3 φ4 φ5; InF φ2 vz (vs vz)]
                  (Or (InF φ4 vz (vs vz)) (And (zEq x0 x5) (zEq x1 x3))).
Proof.
  apply (ziff_E1 _ (InF φ2 vz (vs vz))); [|zhyp].
  zinst (zIff (InF φ3 (vs vz) vz) (Or (InF φ5 (vs vz) vz) (And (zEq x1 x6) (zEq x0 x4)))) x1.
  zinst (zAll (zIff (InF φ4 (vs vz) vz) (Or (InF φ6 (vs vz) vz) (And (zEq x1 x7) (zEq x0 x5))))) x0. zhyp.
Qed.

Lemma chext_I1 : IZF [ι V; ι V; ι V; ι V; ι V; ι V] [ChExt φ2 φ3 φ4 φ5; InF φ4 vz (vs vz)] (InF φ2 vz (vs vz)).
Proof.
  apply (ziff_E2 _ _ (Or (InF φ4 vz (vs vz)) (And (zEq x0 x5) (zEq x1 x3)))); [|zap zor_I1; zhyp].
  zinst (zIff (InF φ3 (vs vz) vz) (Or (InF φ5 (vs vz) vz) (And (zEq x1 x6) (zEq x0 x4)))) x1.
  zinst (zAll (zIff (InF φ4 (vs vz) vz) (Or (InF φ6 (vs vz) vz) (And (zEq x1 x7) (zEq x0 x5))))) x0. zhyp.
Qed.

Lemma chext_I2 : IZF [ι V; ι V; ι V; ι V; ι V; ι V] [ChExt φ2 φ3 φ4 φ5; zEq x0 x5; zEq x1 x3] (InF φ2 vz (vs vz)).
Proof.
  apply (ziff_E2 _ _ (Or (InF φ4 vz (vs vz)) (And (zEq x0 x5) (zEq x1 x3)))); [|zap zor_I2; zap zand_I; zhyp].
  zinst (zIff (InF φ3 (vs vz) vz) (Or (InF φ5 (vs vz) vz) (And (zEq x1 x6) (zEq x0 x4)))) x1.
  zinst (zAll (zIff (InF φ4 (vs vz) vz) (Or (InF φ6 (vs vz) vz) (And (zEq x1 x7) (zEq x0 x5))))) x0. zhyp.
Qed.

(** g ∪ {⟨a, v⟩} existe   (contexte [v; g; a]). *)
Lemma ext_build : IZF [ι V; ι V; ι V] [] (zEx (ChExt vz (vs vz) φ2 φ3)).
Proof.
  zap (zex_E _ (OP vz φ3 (vs vz))); [zuses op_ex (zv2 x2 x0)|].
  zap (zex_E _ (Sg vz (vs vz))); [zuses sg_ex (zv1 x0)|].
  zap (zex_E _ (Db vz φ4 (vs vz))); [zuses db_ex (zv2 x3 x0)|].
  zap (zex_E _ (zAll (zIff (zMem x0 x1) (zEx (And (zMem x1 x0) (zMem x0 x3)))))).
  { zinst (zEx (zAll (zIff (zMem x0 x1) (zEx (And (zMem x1 x0) (zMem x0 x3)))))) x0. exact (zaxm Z_union _ anil). }
  (* [g'; t; s; p; v; g; a] *)
  apply (deriv_cut ZC Pr RIZF (φ := zAll (zIff (zMem x0 x1) (Or (zMem x0 x6) (zEq x0 x4))))).
  { zap zall_I.
    (* [q; g'; t; s; p; v; g; a] *)
    apply ziff_I.
    - apply (deriv_cut ZC Pr RIZF (φ := zEx (And (zMem x1 x0) (zMem x0 x3)))).
      { apply (ziff_E1 _ (zMem x0 x1)); [|zhyp]. zinst (zIff (zMem x0 x2) (zEx (And (zMem x1 x0) (zMem x0 x4)))) x0. zhyp. }
      zdes.
      (* [b; q; g'; t; s; p; v; g; a] *)
      refine (_ : IZF _ _ (Or (zMem x1 x7) (zEq x1 x5))).
      zap (zor_E _ (zEq x0 x7) (zEq x0 x4)); [zuses db_eq (zv4 x3 x7 x4 x0); zhyp| |].
      + zap zor_I1. zap (zeq_subst _ (zMem x2 x0) x0 x7); zhyp.
      + zap zor_I2. zuses sg_eq (zv3 x4 x5 x1); [zhyp|]. zap (zeq_subst _ (zMem x2 x0) x0 x4); zhyp.
    - apply (ziff_E2 _ _ (zEx (And (zMem x1 x0) (zMem x0 x3)))).
      { zinst (zIff (zMem x0 x2) (zEx (And (zMem x1 x0) (zMem x0 x4)))) x0. zhyp. }
      zap (zor_E _ (zMem x0 x6) (zEq x0 x4)); [zhyp| |].
      + refine (_ : IZF _ _ (zEx (And (zMem x1 x0) (zMem x0 x3)))). zap (zex_I _ _ x6).
        refine (_ : IZF _ _ (And (zMem x0 x6) (zMem x6 x2))). zap zand_I; [zhyp|].
        zuses db_mem1 (zv3 x2 x6 x3). zhyp.
      + refine (_ : IZF _ _ (zEx (And (zMem x1 x0) (zMem x0 x3)))). zap (zex_I _ _ x3).
        refine (_ : IZF _ _ (And (zMem x0 x3) (zMem x3 x2))). zap zand_I.
        * zap (zeq_subst _ (zMem x0 x4) x4 x0); [zap zeq_sym; zhyp|]. zuses mem_sg (zv2 x3 x4). zhyp.
        * zuses db_mem2 (zv3 x2 x6 x3). zhyp. }
  refine (_ : IZF _ _ (zEx (ChExt vz φ5 φ6 φ7))). zap (zex_I _ _ x0).
  refine (_ : IZF _ _ (ChExt vz φ4 φ5 φ6)). unfold ChExt. zap zall_I. zap zall_I.
  (* [w; c; g'; t; s; p; v; g; a] *)
  apply ziff_I.
  - zdes.
    (* [q; w; c; g'; t; s; p; v; g; a] *)
    zap (zor_E _ (zMem x0 x8) (zEq x0 x6)).
    { apply (ziff_E1 _ (zMem x0 x3)); [|zhyp]. zinst (zIff (zMem x0 x4) (Or (zMem x0 x9) (zEq x0 x7))) x0. zhyp. }
    + zap zor_I1. refine (_ : IZF _ _ (zEx (And (zMem x0 x9) (OP vz φ3 φ2)))). zap (zex_I _ _ x0).
      refine (_ : IZF _ _ (And (zMem x0 x8) (OP vz φ2 (vs vz)))). zap zand_I; zhyp.
    + zap zor_I2.
      apply (deriv_cut ZC Pr RIZF (φ := And (zEq x9 x2) (zEq x7 x1))).
      { zuses op_inj (zv5 x6 x9 x7 x2 x1); [zhyp|]. zap (zeq_subst _ (OP vz φ3 φ2) x0 x6); zhyp. }
      apply zand_L. zap zand_I; zap zeq_sym; zhyp.
  - zap (zor_E _ (InF φ7 (vs vz) vz) (And (zEq x1 x8) (zEq x0 x6))); [zhyp| |].
    + zdes.
      (* [q; w; c; g'; t; s; p; v; g; a] *)
      refine (_ : IZF _ _ (zEx (And (zMem x0 x4) (OP vz φ3 φ2)))). zap (zex_I _ _ x0).
      refine (_ : IZF _ _ (And (zMem x0 x3) (OP vz φ2 (vs vz)))). zap zand_I; [|zhyp].
      apply (ziff_E2 _ _ (Or (zMem x0 x8) (zEq x0 x6))); [|zap zor_I1; zhyp].
      zinst (zIff (zMem x0 x4) (Or (zMem x0 x9) (zEq x0 x7))) x0. zhyp.
    + apply zand_L.
      refine (_ : IZF _ _ (zEx (And (zMem x0 x3) (OP vz φ2 (vs vz))))). zap (zex_I _ _ x5).
      refine (_ : IZF _ _ (And (zMem x5 x2) (OP φ5 (vs vz) vz))). zap zand_I.
      * apply (ziff_E2 _ _ (Or (zMem x5 x7) (zEq x5 x5))); [|zap zor_I2; zap zeq_refl].
        zinst (zIff (zMem x0 x3) (Or (zMem x0 x8) (zEq x0 x6))) x5. zhyp.
      * zap (zeq_subst _ (OP φ6 φ2 vz) x6 x0); [zap zeq_sym; zhyp|]. refine (_ : IZF _ _ (OP φ5 (vs vz) φ6)).
        zap (zeq_subst _ (OP φ6 vz φ7) x8 x1); [zap zeq_sym; zhyp|zhyp].
Qed.

(** Un couple de g' en un point où g est défini est dans g
    (contexte [u; u'; α; g'; v; g; a; ψ]). *)
Lemma ext_K : IZF [ι V; ι V; ι V; ι V; ι V; ι V; ι V; σR]
                [InF φ3 φ2 vz; InF φ5 φ2 (vs vz); ChExt φ3 φ4 φ5 φ6; AttCr φ5 φ7; StepEq φ4 φ6 φ5 φ7]
                (InF φ5 φ2 vz).
Proof.
  zap (zor_E _ (InF φ5 φ2 vz) (And (zEq x2 x6) (zEq x0 x4))); [zuses chext_E (zv6 x2 x0 x3 x4 x5 x6); zhyp|zhyp|].
  apply zand_L.
  zap (zeq_subst _ (InF φ6 φ3 vz) x1 x0); [|refine (_ : IZF _ _ (InF φ5 φ2 (vs vz))); zhyp].
  zap (zeq_trans _ x1 x4 x0); [|zap zeq_sym; zhyp].
  zuses step_uniq (wSU x1 x4 x6 (wRF φ5 φ7)); [|zhyp].
  refine (_ : IZF _ _ (StepEq (vs vz) φ6 φ5 φ7)).
  zap (zeq_subst _ (StepEq φ2 vz φ6 φ8) x2 x6); [zhyp|].
  refine (_ : IZF _ _ (StepEq (vs vz) φ2 φ5 φ7)).
  zap (zimp_E _ (InF φ5 φ2 (vs vz))); [|zhyp].
  zinst (Imp (InF φ6 φ3 vz) (StepEq vz φ3 φ6 φ8)) x1.
  zinst (zAll (Imp (InF φ7 (vs vz) vz) (StepEq vz (vs vz) φ7 φ9))) x2. zhyp.
Qed.

(** g ∪ {⟨a, v⟩} est un essai si g en est un, défini sur a, et si v est
    correct en a   (contexte [g'; v; g; a; ψ]). *)
Lemma ext_att : IZF [ι V; ι V; ι V; ι V; σR]
                  [Att φ2 φ4; DcAt φ2 φ3; StepEq (vs vz) φ3 φ2 φ4; ChExt vz (vs vz) φ2 φ3]
                  (Att vz φ4).
Proof.
  apply (deriv_cut ZC Pr RIZF (φ := AttFn φ2)); [zuses att_fn (wVR x2 φ4); zhyp|].
  apply (deriv_cut ZC Pr RIZF (φ := AttCr φ2 φ4)); [zuses att_cr (wVR x2 φ4); zhyp|].
  zuses att_intro (wVR x0 φ4).
  - refine (_ : IZF _ _ (zAll (zAll (zAll (Imp (InF φ3 φ2 (vs vz)) (Imp (InF φ3 φ2 vz) (zEq x1 x0))))))).
    zap zall_I. zap zall_I. zap zall_I. zap zimp_I. zap zimp_I.
    (* [w; v'; b; g'; v; g; a; ψ] *)
    zap (zor_E _ (InF φ5 φ2 (vs vz)) (And (zEq x2 x6) (zEq x1 x4))); [zuses chext_E (zv6 x2 x1 x3 x4 x5 x6); zhyp| |].
    + zuses fn_use (zv4 x2 x1 x0 x5); [zhyp|zhyp|].
      zuses ext_K (zv7R x0 x1 x2 x3 x4 x5 x6 φ7); zhyp.
    + apply zand_L.
      zap (zor_E _ (InF φ5 φ2 vz) (And (zEq x2 x6) (zEq x0 x4))); [zuses chext_E (zv6 x2 x0 x3 x4 x5 x6); zhyp| |].
      * zuses fn_use (zv4 x2 x1 x0 x5); [zhyp| |zhyp].
        zuses ext_K (zv7R x1 x0 x2 x3 x4 x5 x6 φ7); zhyp.
      * apply zand_L. zap (zeq_trans _ x1 x4 x0); [zhyp|zap zeq_sym; zhyp].
  - refine (_ : IZF _ _ (zAll (zAll (Imp (InF φ2 (vs vz) vz) (zEx (And (Sub vz φ3) (And (DcAt vz φ2) (StepEq (vs vz) φ2 vz φ7)))))))).
    zap zall_I. zap zall_I. zap zimp_I.
    (* [w; b; g'; v; g; a; ψ] *)
    refine (_ : IZF _ _ (zEx (And (Sub vz φ3) (And (DcAt vz φ2) (StepEq (vs vz) φ2 vz φ7))))).
    zap (zex_I _ _ x4).
    refine (_ : IZF _ _ (And (Sub φ4 φ2) (And (DcAt φ4 (vs vz)) (StepEq vz (vs vz) φ4 φ6)))).
    zap zand_I.
    + refine (_ : IZF _ _ (zAll (zAll (Imp (InF φ6 (vs vz) vz) (InF φ4 (vs vz) vz))))).
      zap zall_I. zap zall_I. zap zimp_I.
      (* [w'; c; w; b; g'; v; g; a; ψ] *)
      zuses chext_I1 (zv6 x1 x0 x4 x5 x6 x7); zhyp.
    + zap (zor_E _ (InF φ4 (vs vz) vz) (And (zEq x1 x5) (zEq x0 x3))); [zuses chext_E (zv6 x1 x0 x2 x3 x4 x5); zhyp| |].
      * zap zand_I.
        -- zap (zimp_E _ (InF φ4 (vs vz) vz)); [|zhyp].
           zinst (Imp (InF φ5 φ2 vz) (zAll (Imp (zMem x0 x3) (zEx (InF φ7 (vs vz) vz))))) x0.
           zinst (zAll (Imp (InF φ6 (vs vz) vz) (zAll (Imp (zMem x0 x2) (zEx (InF φ8 (vs vz) vz)))))) x1.
           zuses att_dc (wVR x4 φ6). zhyp.
        -- zap (zimp_E _ (InF φ4 (vs vz) vz)); [|zhyp].
           zinst (Imp (InF φ5 φ2 vz) (StepEq vz φ2 φ5 φ7)) x0.
           zinst (zAll (Imp (InF φ6 (vs vz) vz) (StepEq vz (vs vz) φ6 φ8))) x1. zhyp.
      * apply zand_L. zap zand_I.
        -- zap (zeq_subst _ (DcAt φ5 vz) x5 x1); [zap zeq_sym; zhyp|]. refine (_ : IZF _ _ (DcAt φ4 φ5)). zhyp.
        -- zap (zeq_subst _ (StepEq vz φ2 φ5 φ7) x3 x0); [zap zeq_sym; zhyp|].
           refine (_ : IZF _ _ (StepEq φ3 (vs vz) φ4 φ6)).
           zap (zeq_subst _ (StepEq φ4 vz φ5 φ7) x5 x1); [zap zeq_sym; zhyp|].
           refine (_ : IZF _ _ (StepEq φ3 φ5 φ4 φ6)). zhyp.
Qed.

(** ** Existence d'un essai défini en a *)

(** ∃f. f essai ∧ ∃v. ⟨a, v⟩ ∈ f. *)
Definition Pe {Γ} (a : var Γ (ι V)) (ψ : var Γ σR) : zform Γ :=
  zEx (And (Att vz (vs ψ)) (zEx (InF (vs vz) (vs (vs a)) vz))).

Definition Qform : zform [ι V; ι V; ι V; σR] := And (Att (vs vz) φ3) (zEx (InF φ2 (vs vz) vz)).

Definition wV4R {Γ} (a b c d : ztm Γ V) (ψ : var Γ σR) : vec zsym [ι V; ι V; ι V; ι V; σR] Γ :=
  @acons _ zsym Γ (ι V) _ a (@acons _ zsym Γ (ι V) _ b (@acons _ zsym Γ (ι V) _ c (@acons _ zsym Γ (ι V) _ d
    (@acons _ zsym Γ σR _ (eta σR ψ) anil)))).

(** Par ∈-induction   (contexte [ψ]). *)
Lemma att_ex : IZF [σR] [] (zAll (Pe vz (vs vz))).
Proof.
  zap (zimp_E _ (zAll (Imp (zAll (Imp (zMem x0 x1) (Pe vz φ2))) (Pe vz (vs vz))))).
  { exact (zaxm Z_ind _ (v1 (Pe vz (vs vz)))). }
  zap zall_I. zap zimp_I.
  (* [a; ψ] : collection des essais *)
  zap (zex_E _ (zAll (Imp (zMem x0 x2) (zEx (And (zMem x0 x2) (And (Att vz φ4) (zEx (InF (vs vz) φ2 vz)))))))).
  { zap (zimp_E _ (zAll (Imp (zMem x0 x1) (zEx (And (Att vz φ3) (zEx (InF (vs vz) φ2 vz))))))).
    - zinst (Imp (zAll (Imp (zMem x0 x1) (zEx (And (Att vz φ4) (zEx (InF (vs vz) φ2 vz))))))
                 (zEx (zAll (Imp (zMem x0 x2) (zEx (And (zMem x0 x2) (And (Att vz φ5) (zEx (InF (vs vz) φ2 vz))))))))) x0.
      exact (zaxm Z_coll _ (@acons _ zsym _ σR _ Qform anil)).
    - zap zall_I. zap zimp_I.
      zap (zimp_E _ (zMem x0 x1)); [|zhyp]. zinst (Imp (zMem x0 x2) (Pe vz φ3)) x0. zhyp. }
  (* [S; a; ψ] : S' = {f ∈ S | f essai} *)
  zap (zex_E _ (zAll (zIff (zMem x0 x1) (And (zMem x0 x2) (Att vz φ4))))).
  { zinst (zEx (zAll (zIff (zMem x0 x1) (And (zMem x0 x2) (Att vz φ5))))) x0.
    exact (zaxm Z_sep _ (v1 (Att vz φ3))). }
  (* [S'; S; a; ψ] : g = ⋃S' *)
  zap (zex_E _ (ChUn vz (vs vz))); [zuses un_build (zv1 x0)|].
  (* [g; S'; S; a; ψ] *)
  apply (deriv_cut ZC Pr RIZF (φ := Att vz φ4)).
  { zuses un_att (wVVR x0 x1 φ4); [|zhyp].
    refine (_ : IZF _ _ (zAll (Imp (zMem x0 x2) (Att vz φ5)))). zap zall_I. zap zimp_I.
    zap (zand_E2 _ (zMem x0 x3)). apply (ziff_E1 _ (zMem x0 x2)); [|zhyp].
    zinst (zIff (zMem x0 x3) (And (zMem x0 x4) (Att vz φ6))) x0. zhyp. }
  apply (deriv_cut ZC Pr RIZF (φ := DcAt vz φ3)).
  { refine (_ : IZF _ _ (zAll (Imp (zMem x0 x4) (zEx (InF φ2 (vs vz) vz))))). zap zall_I. zap zimp_I.
    (* [α; g; S'; S; a; ψ] *)
    zap (zex_E _ (And (zMem x0 x4) (And (Att vz φ6) (zEx (InF (vs vz) φ2 vz))))).
    { zap (zimp_E _ (zMem x0 x4)); [|zhyp].
      zinst (Imp (zMem x0 x5) (zEx (And (zMem x0 x5) (And (Att vz φ7) (zEx (InF (vs vz) φ2 vz)))))) x0. zhyp. }
    apply zand_L. apply zand_L2.
    zap (zex_E _ (InF (vs vz) φ2 vz)); [zhyp|].
    (* [v; f; α; g; S'; S; a; ψ] *)
    refine (_ : IZF _ _ (zEx (InF φ4 φ3 vz))). zap (zex_I _ _ x0).
    refine (_ : IZF _ _ (InF φ3 φ2 vz)).
    apply (ziff_E2 _ _ (zEx (And (zMem x0 x5) (InF vz φ3 (vs vz))))).
    { zinst (zIff (InF φ4 φ3 vz) (zEx (And (zMem x0 x6) (InF vz φ4 (vs vz))))) x0.
      zinst (zAll (zIff (InF φ5 (vs vz) vz) (zEx (And (zMem x0 x7) (InF vz φ2 (vs vz)))))) x2. zhyp. }
    refine (_ : IZF _ _ (zEx (And (zMem x0 x5) (InF vz φ3 (vs vz))))). zap (zex_I _ _ x1).
    refine (_ : IZF _ _ (And (zMem x1 x4) (InF (vs vz) φ2 vz))). zap zand_I; [|zhyp].
    apply (ziff_E2 _ _ (And (zMem x1 x5) (Att (vs vz) φ7))); [|zap zand_I; zhyp].
    zinst (zIff (zMem x0 x5) (And (zMem x0 x6) (Att vz φ8))) x1. zhyp. }
  (* la valeur en a *)
  zap (zex_E _ (StepEq vz φ4 (vs vz) φ5)); [zuses step_ex (wVVR x3 x0 φ4)|].
  (* [v0; g; S'; S; a; ψ] *)
  zap (zex_E _ (ChExt vz (vs vz) φ2 φ5)); [zuses ext_build (zv3 x0 x1 x4)|].
  (* [g'; v0; g; S'; S; a; ψ] *)
  refine (_ : IZF _ _ (zEx (And (Att vz φ7) (zEx (InF (vs vz) φ7 vz))))). zap (zex_I _ _ x0).
  refine (_ : IZF _ _ (And (Att vz φ6) (zEx (InF (vs vz) φ6 vz)))). zap zand_I.
  - zuses ext_att (wV4R x0 x1 x2 x5 φ6); zhyp.
  - zap (zex_I _ _ x1). refine (_ : IZF _ _ (InF vz φ5 (vs vz))).
    zuses chext_I2 (zv6 x5 x1 x0 x1 x2 x5); [zhyp|zap zeq_refl|zap zeq_refl].
Qed.

(** ** Totalité du graphe de rec   (contexte [P; R; D]) *)

Lemma tot_rec : IZF [σP; σR; σP] [Tot (eta σP (Γ := [σP; σR; σP]) φ2)] (Tot Frec).
Proof.
  zap (zex_E _ (zap1 φ3 x0)); [zhyp|].
  (* [a; P; R; D] *)
  apply (deriv_cut ZC Pr RIZF (φ := Pe vz φ2)).
  { zinst (Pe vz φ3) x0. zuses att_ex (@acons _ zsym _ σR _ (eta σR φ2) anil). }
  zdes. zdes2.
  (* [v; f; a; P; R; D] *)
  refine (_ : IZF _ _ (zEx (zEx (And (zap1 φ7 x0) (zAll (zIff (zMem x0 x2) (RecV (vs vz) φ7 vz))))))).
  zap (zex_I _ _ x0).
  refine (_ : IZF _ _ (zEx (And (zap1 φ6 x0) (zAll (zIff (zMem x0 x2) (RecV (vs vz) φ6 vz)))))).
  zap (zex_I _ _ x2).
  refine (_ : IZF _ _ (And (zap1 φ5 x2) (zAll (zIff (zMem x0 x1) (RecV φ3 φ5 vz))))).
  zap zand_I; [zhyp|]. zap zall_I.
  (* [z; v; f; a; P; R; D] *)
  apply ziff_I.
  - refine (_ : IZF _ _ (zEx (And (Att vz φ6) (zEx (And (InF (vs vz) φ5 vz) (zMem x2 x0)))))).
    zap (zex_I _ _ x2).
    refine (_ : IZF _ _ (And (Att φ2 φ5) (zEx (And (InF φ3 φ4 vz) (zMem x1 x0))))). zap zand_I; [zhyp|].
    zap (zex_I _ _ x1). refine (_ : IZF _ _ (And (InF φ2 φ3 (vs vz)) (zMem x0 x1))). zap zand_I; zhyp.
  - zdes. zdes2.
    (* [v'; f'; z; v; f; a; P; R; D] *)
    refine (_ : IZF _ _ (zMem x2 x3)).
    zap (zeq_subst _ (zMem x3 x0) x0 x3); [|refine (_ : IZF _ _ (zMem x2 x0)); zhyp].
    zap (zimp_E _ (InF φ4 φ5 φ3)); [|zhyp]. zap (zimp_E _ (InF (vs vz) φ5 vz)); [|zhyp].
    zinst (Imp (InF φ2 φ6 (vs vz)) (Imp (InF φ5 φ6 vz) (zEq x1 x0))) x3.
    zinst (zAll (Imp (InF φ3 φ7 (vs vz)) (Imp (InF φ6 φ7 vz) (zEq x1 x0)))) x0.
    zinst (Pu vz φ2 φ5) x5.
    zuses att_uniq (wVVR x1 x4 φ7).
    + zuses att_dc (wVR x1 φ7). zhyp.
    + zuses att_cr (wVR x1 φ7). zhyp.
    + zuses att_dc (wVR x4 φ7). zhyp.
    + zuses att_cr (wVR x4 φ7). zhyp.
Qed.
