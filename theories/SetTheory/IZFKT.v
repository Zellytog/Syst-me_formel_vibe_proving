(** * La récursion sur ℕ par Knaster–Tarski, dans IZF⁻ε (sans rec)

    Étant donnés un ensemble B, un point de départ a ε B et une fonction
    g : B → B (un symbole de terme en métavariable), le graphe de la suite
    f(0) = a, f(n + 1) = g(f(n)) est le plus petit ensemble L ⊆ A clos par
    ⟨∅, a⟩ et ⟨n, y⟩ ↦ ⟨S(n), g(y)⟩, où A contient tous les ⟨n, y⟩ avec
    n ε ω, y ε B (obtenu par collection) :

      L ≜ {z ε A ∣ ∀X. X ε P(A) → Cl(X) → z ε X}.

    Le faible powerset suffit : le principe d'induction n'est utilisé que
    pour des ensembles définis par séparation, dont l'axiome [A_power]
    fournit un représentant dans P(A) ([lfp_ind]). On en déduit la clôture,
    l'inversion (tout élément de L est ⟨∅, a⟩ ou un successeur), la totalité
    sur ω et la fonctionnalité **au sens de Leibniz**, par ε-induction, avec
    l'injectivité de Leibniz du couple et du successeur. Tout est dans
    IZF⁻ε, donc sans rec ([kt_rec]). *)

From Stdlib Require Import List.
Import ListNotations.
From SF.Syntax Require Import Spec Terms Renaming Vectors.
From SF.Calculus Require Import System Rules.
From SF.Logic Require Import Judgment Propositional.
From SF.Functional Require Import Arrow.
From SF.Quantifiers Require Import Quant Order.
From SF.SetTheory Require Import IZFe IZFeBasic IZFeExt.

Local Notation ι a := (Spec [] a).
Tactic Notation "qap" uconstr(t) := eapply t; try typeclasses eauto.
Ltac hyp := apply d_ax; simpl; auto 20.
Ltac hypc := solve [apply d_ax; repeat (first [left; reflexivity | right])].

(** ** Injectivité de Leibniz, au niveau de ε *)

(** u ε {a, a} → u = a   (contexte [u; a]). *)
Lemma sing_inj : IZFm [ι V; ι V] [Eps x0 (Sing x1)] (EqV x0 x1).
Proof.
  qap (or_E C Pr RIZFm _ (EqV x0 x1) (EqV x0 x1)); [|hyp|hyp].
  qap iff_E1; [exact (axm A_pair _ (vV3 x0 x1 x1))|hyp].
Qed.

Lemma eps_pair_l : IZFm [ι V; ι V] [] (Eps x0 (Pair x0 x1)).
Proof.
  qap iff_E2; [exact (axm A_pair _ (vV3 x0 x0 x1))|]. qap (or_I1 C Pr RIZFm). qap (qeq_refl C RIZFm V hV).
Qed.

Lemma eps_pair_r : IZFm [ι V; ι V] [] (Eps x1 (Pair x0 x1)).
Proof.
  qap iff_E2; [exact (axm A_pair _ (vV3 x1 x0 x1))|]. qap (or_I2 C Pr RIZFm). qap (qeq_refl C RIZFm V hV).
Qed.

(** Transport de ε le long de l'égalité du contenant   (contexte [u; x; y]). *)
Lemma eps_tr : IZFm [ι V; ι V; ι V] [EqV x1 x2; Eps x0 x1] (Eps x0 x2).
Proof. qap (qeq_subst C RIZFm V hV _ (Eps x1 x0) x1 x2); hyp. Qed.

(** ⟨a, b⟩ = ⟨a′, b′⟩ → a = a′   (contexte [a; b; a′; b′]). *)
Lemma opair_inj1 : IZFm [ι V; ι V; ι V; ι V] [EqV (OPair x0 x1) (OPair x2 x3)] (EqV x0 x2).
Proof.
  qap (qeq_sym C RIZFm V hV).
  qap (or_E C Pr RIZFm _ (EqV (Sing x0) (Sing x2)) (EqV (Sing x0) (Pair x2 x3))).
  - qap iff_E1; [exact (axm A_pair _ (vV3 (Sing x0) (Sing x2) (Pair x2 x3)))|].
    uses eps_tr (vV3 (Sing x0) (OPair x0 x1) (OPair x2 x3)); [hyp|]. uses eps_pair_l (vV2 (Sing x0) (Pair x0 x1)).
  - uses sing_inj (vV2 x2 x0).
    uses eps_tr (vV3 x2 (Sing x2) (Sing x0)); [qap (qeq_sym C RIZFm V hV); hyp|]. uses eps_pair_l (vV2 x2 x2).
  - uses sing_inj (vV2 x2 x0).
    uses eps_tr (vV3 x2 (Pair x2 x3) (Sing x0)); [qap (qeq_sym C RIZFm V hV); hyp|]. uses eps_pair_l (vV2 x2 x3).
Qed.

(** ⟨a, b⟩ = ⟨a′, b′⟩ → b = b′   (contexte [a; b; a′; b′]). *)
Lemma opair_inj2 : IZFm [ι V; ι V; ι V; ι V] [EqV (OPair x0 x1) (OPair x2 x3)] (EqV x1 x3).
Proof.
  (* b = a′ ∨ b = b′, car {a, b} ε ⟨a′, b′⟩ *)
  qap (or_E C Pr RIZFm _ (EqV x1 x2) (EqV x1 x3)); [| |hyp].
  - qap (or_E C Pr RIZFm _ (EqV (Pair x0 x1) (Sing x2)) (EqV (Pair x0 x1) (Pair x2 x3))).
    + qap iff_E1; [exact (axm A_pair _ (vV3 (Pair x0 x1) (Sing x2) (Pair x2 x3)))|].
      uses eps_tr (vV3 (Pair x0 x1) (OPair x0 x1) (OPair x2 x3)); [hyp|]. uses eps_pair_r (vV2 (Sing x0) (Pair x0 x1)).
    + qap (or_I1 C Pr RIZFm). uses sing_inj (vV2 x1 x2).
      uses eps_tr (vV3 x1 (Pair x0 x1) (Sing x2)); [hyp|]. uses eps_pair_r (vV2 x0 x1).
    + qap iff_E1; [exact (axm A_pair _ (vV3 x1 x2 x3))|].
      uses eps_tr (vV3 x1 (Pair x0 x1) (Pair x2 x3)); [hyp|]. uses eps_pair_r (vV2 x0 x1).
  - (* b = a′ : alors b′ = a′ = b, car {a′, b′} ε ⟨a, b⟩ *)
    qap (qeq_sym C RIZFm V hV).
    qap (or_E C Pr RIZFm _ (EqV (Pair x2 x3) (Sing x0)) (EqV (Pair x2 x3) (Pair x0 x1))).
    + qap iff_E1; [exact (axm A_pair _ (vV3 (Pair x2 x3) (Sing x0) (Pair x0 x1)))|].
      uses eps_tr (vV3 (Pair x2 x3) (OPair x2 x3) (OPair x0 x1)); [qap (qeq_sym C RIZFm V hV); hyp|].
      uses eps_pair_r (vV2 (Sing x2) (Pair x2 x3)).
    + (* b′ = a = a′ = b *)
      qap (qeq_trans C RIZFm V hV _ x3 x0 x1).
      * uses sing_inj (vV2 x3 x0).
        uses eps_tr (vV3 x3 (Pair x2 x3) (Sing x0)); [hyp|]. uses eps_pair_r (vV2 x2 x3).
      * qap (qeq_trans C RIZFm V hV _ x0 x2 x1); [|qap (qeq_sym C RIZFm V hV); hyp].
        uses opair_inj1 (vV4 x0 x1 x2 x3). hyp.
    + qap (or_E C Pr RIZFm _ (EqV x3 x0) (EqV x3 x1)); [| |hyp].
      * qap iff_E1; [exact (axm A_pair _ (vV3 x3 x0 x1))|].
        uses eps_tr (vV3 x3 (Pair x2 x3) (Pair x0 x1)); [hyp|]. uses eps_pair_r (vV2 x2 x3).
      * qap (qeq_trans C RIZFm V hV _ x3 x0 x1); [hyp|].
        qap (qeq_trans C RIZFm V hV _ x0 x2 x1); [|qap (qeq_sym C RIZFm V hV); hyp].
        uses opair_inj1 (vV4 x0 x1 x2 x3). hyp.
Qed.

(** ** Le successeur *)

Lemma eps_suc_self : IZFm [ι V] [] (Eps x0 (Suc x0)).
Proof.
  qap iff_E2; [exact (axm A_union _ (vV2 x0 (Pair x0 (Sing x0))))|].
  qap (qex_I C RIZFm V hV _ _ (Sing x0)). qap (and_I C Pr RIZFm).
  - uses eps_pair_l (vV2 x0 x0).
  - uses eps_pair_r (vV2 x0 (Sing x0)).
Qed.

(** z ε S(m) → z ε m ∨ z = m   (contexte [z; m]). *)
Lemma eps_suc_inv : IZFm [ι V; ι V] [Eps x0 (Suc x1)] (Or (Eps x0 x1) (EqV x0 x1)).
Proof.
  qap (qex_E C RIZFm V hV _ (And (Eps x1 x0) (Eps x0 (Pair x2 (Sing x2))))).
  { qap iff_E1; [exact (axm A_union _ (vV2 x0 (Pair x1 (Sing x1))))|hyp]. }
  (* [b; z; m] *)
  qap (or_E C Pr RIZFm _ (EqV x0 x2) (EqV x0 (Sing x2))).
  - qap iff_E1; [exact (axm A_pair _ (vV3 x0 x2 (Sing x2)))|]. qap (and_E2 C Pr RIZFm _ (Eps x1 x0)). hyp.
  - qap (or_I1 C Pr RIZFm). uses eps_tr (vV3 x1 x0 x2); [hyp|]. qap (and_E1 C Pr RIZFm _ _ (Eps x0 (Pair x2 (Sing x2)))). hyp.
  - qap (or_I2 C Pr RIZFm). uses sing_inj (vV2 x1 x2).
    uses eps_tr (vV3 x1 x0 (Sing x2)); [hyp|]. qap (and_E1 C Pr RIZFm _ _ (Eps x0 (Pair x2 (Sing x2)))). hyp.
Qed.

(** Pas de 2-cycle pour ε (ε-induction)   (contexte [a; b]). *)
Lemma eps_cycle : IZFm [ι V; ι V] [Eps x0 x1; Eps x1 x0] Bot.
Proof.
  qap (imp_E C Pr RIZFm _ (Eps x1 x0)); [|hyp].
  qap (imp_E C Pr RIZFm _ (Eps x0 x1)); [|hyp].
  qap (qall_E C RIZFm V hV _ (Imp (Eps x1 x0) (Imp (Eps x0 x1) Bot)) x1).
  qap (qall_E C RIZFm V hV _ (All (Imp (Eps x1 x0) (Imp (Eps x0 x1) Bot))) x0).
  qap (imp_E C Pr RIZFm); [exact (axm A_ind _ (vP1 (All (Imp (Eps x1 x0) (Imp (Eps x0 x1) Bot)))))|].
  qap (qall_I C RIZFm V hV). qap (imp_I C Pr RIZFm).
  qap (qall_I C RIZFm V hV). qap (imp_I C Pr RIZFm). qap (imp_I C Pr RIZFm).
  (* [d; c; a; b] : c ε d, d ε c ; l'hypothèse en d (d ε c) avec c *)
  qap (imp_E C Pr RIZFm _ (Eps x1 x0)); [|hyp].
  qap (imp_E C Pr RIZFm _ (Eps x0 x1)); [|hyp].
  qap (qall_E C RIZFm V hV _ (Imp (Eps x1 x0) (Imp (Eps x0 x1) Bot)) x1).
  qap (imp_E C Pr RIZFm _ (Eps x0 x1)); [|hyp].
  qap (qall_E C RIZFm V hV _ (Imp (Eps x0 x2) (All (Imp (Eps x1 x0) (Imp (Eps x0 x1) Bot)))) x0). hyp.
Qed.

(** S(m) = S(m′) → m = m′   (contexte [m; m′]). *)
Lemma suc_inj : IZFm [ι V; ι V] [EqV (Suc x0) (Suc x1)] (EqV x0 x1).
Proof.
  qap (or_E C Pr RIZFm _ (Eps x0 x1) (EqV x0 x1)); [| |hyp].
  - uses eps_suc_inv (vV2 x0 x1). uses eps_tr (vV3 x0 (Suc x0) (Suc x1)); [hyp|]. uses eps_suc_self (vV1 x0).
  - qap (or_E C Pr RIZFm _ (Eps x1 x0) (EqV x1 x0)).
    + uses eps_suc_inv (vV2 x1 x0). uses eps_tr (vV3 x1 (Suc x1) (Suc x0)); [qap (qeq_sym C RIZFm V hV); hyp|].
      uses eps_suc_self (vV1 x1).
    + qap (bot_E C Pr RIZFm). uses eps_cycle (vV2 x0 x1); hyp.
    + qap (qeq_sym C RIZFm V hV). hyp.
Qed.

(** S(m) ≠ ∅   (contexte [m]). *)
Lemma suc_empty : IZFm [ι V] [EqV (Suc x0) Empty] Bot.
Proof.
  qap (imp_E C Pr RIZFm _ (Eps x0 Empty)); [exact (axm A_empty _ (vV1 x0))|].
  uses eps_tr (vV3 x0 (Suc x0) Empty); [hyp|]. uses eps_suc_self (vV1 x0).
Qed.

Lemma suc_omega : IZFm [ι V] [Eps x0 Omega] (Eps (Suc x0) Omega).
Proof.
  qap iff_E2; [exact (axm A_omega _ (vV1 (Suc x0)))|].
  qap (or_I2 C Pr RIZFm). qap (qex_I C RIZFm V hV _ _ x0). qap (and_I C Pr RIZFm); [hyp|].
  qap (qeq_refl C RIZFm V hV).
Qed.

Lemma empty_omega : IZFm [] [] (Eps Empty Omega).
Proof.
  qap iff_E2; [exact (axm A_omega _ (vV1 Empty))|]. qap (or_I1 C Pr RIZFm). qap (qeq_refl C RIZFm V hV).
Qed.

(** ** Le plus petit point fixe *)

Local Notation x5 := (var0 (vs (vs (vs (vs (vs vz)))))).
Local Notation x6 := (var0 (vs (vs (vs (vs (vs (vs vz))))))).
Local Notation x7 := (var0 (vs (vs (vs (vs (vs (vs (vs vz)))))))).
Local Notation x8 := (var0 (vs (vs (vs (vs (vs (vs (vs (vs vz))))))))).
Local Notation x9 := (var0 (vs (vs (vs (vs (vs (vs (vs (vs (vs vz)))))))))).
Local Notation x10 := (var0 (vs (vs (vs (vs (vs (vs (vs (vs (vs (vs vz))))))))))).
Local Notation x11 := (var0 (vs (vs (vs (vs (vs (vs (vs (vs (vs (vs (vs vz)))))))))))).
Local Notation x12 := (var0 (vs (vs (vs (vs (vs (vs (vs (vs (vs (vs (vs (vs vz))))))))))))).
Local Notation x13 := (var0 (vs (vs (vs (vs (vs (vs (vs (vs (vs (vs (vs (vs (vs vz)))))))))))))).
Local Notation x14 := (var0 (vs (vs (vs (vs (vs (vs (vs (vs (vs (vs (vs (vs (vs (vs vz))))))))))))))).
Local Notation x15 := (var0 (vs (vs (vs (vs (vs (vs (vs (vs (vs (vs (vs (vs (vs (vs (vs vz)))))))))))))))).

(** Les fonctions g : V → V sont des métavariables de terme. *)
Notation σG := (Spec [ι V] V).

Definition appg {Γ} (x : var Γ σG) (t : tm Γ V) : tm Γ V :=
  @tvar _ isym Γ σG x (@acons _ isym Γ (ι V) _ t anil).

Definition vVVP {Γ} (a b : tm Γ V) (φ : tm (ι V :: Γ) Pr) : vec isym [ι V; ι V; σP] Γ :=
  @acons _ isym Γ (ι V) _ a (@acons _ isym Γ (ι V) _ b (@acons _ isym Γ σP _ φ anil)).

(** Le principe d'induction de L ≜ {z ε A ∣ ∀X ε P(A). Cl(X) → z ε X}, pour un
    prédicat P (contexte [P; L; A; a; B; g]) : si P(⟨∅, a⟩) et P passe de
    ⟨n, y⟩ à ⟨S(n), g(y)⟩, alors P vaut sur L. On applique la définition de L
    à l'élément b ε P(A) qui représente {z ε A ∣ P(z)} ([A_power]). *)
Lemma lfp_ind : IZFm [σP; ι V; ι V; ι V; ι V; σG]
  [(All (Imp (Eps x0 Omega) (All (Imp (Eps x0 x6) (Eps (OPair x1 x0) x4))))); (All (Imp (Eps x0 x5) (Eps (appg (vs (vs (vs (vs (vs (vs vz)))))) x0) x5))); (Eps x3 x4); (All (Iff (Eps x0 x2) (And (Eps x0 x3) (All (Imp (Eps x0 (Power x4)) (Imp (And (Eps (OPair Empty x5) x0) (All (All (Imp (Eps x1 Omega) (Imp (Eps x0 x8) (Imp (Eps (OPair x1 x0) x2) (Eps (OPair (Suc x1) (appg (vs (vs (vs (vs (vs (vs (vs (vs (vs vz))))))))) x0)) x2))))))) (Eps x1 x0))))))); (app1 (s := V) vz (OPair Empty x3)); (All (All (Imp (Eps x1 Omega) (Imp (Eps x0 x6) (Imp (app1 (s := V) (vs (vs vz)) (OPair x1 x0)) (app1 (s := V) (vs (vs vz)) (OPair (Suc x1) (appg (vs (vs (vs (vs (vs (vs (vs vz))))))) x0))))))))]
  (All (Imp (Eps x0 x2) (app1 (s := V) (vs vz) x0))).
Proof.
  qap (qall_I C RIZFm V hV). qap (imp_I C Pr RIZFm).
  (* [z; P; L; A; a; B; g] : b ε P(A) représente {z ε A ∣ P(z)} *)
  qap (qex_E C RIZFm V hV _ (And (Eps x0 (Power x4)) (All (Iff (Eps x0 x1) (And (Eps x0 x5) (Eps x0 (Sep x5 (app1 (s := V) (vs (vs (vs (vs vz)))) x0)))))))).
  { exact (axm A_power _ (vV2 x3 (Sep x3 (app1 (s := V) (vs (vs vz)) x0)))). }
  (* [b; z; P; L; A; a; B; g] *)
  qap (and_E2 C Pr RIZFm _ (Eps x1 x4)). qap iff_E1; [exact (axm A_sep _ (vVVP x1 x4 (app1 (s := V) (vs (vs (vs vz))) x0)))|].
  qap (and_E2 C Pr RIZFm _ (Eps x1 x4)).
  qap iff_E1; [refine (qall_E C RIZFm V hV _ (Iff (Eps x0 x1) (And (Eps x0 x5) (Eps x0 (Sep x5 (app1 (s := V) (vs (vs (vs (vs vz)))) x0))))) x1 _); qap (and_E2 C Pr RIZFm _ (Eps x0 (Power x4))); hypc|].
  (* z ε b, par la définition de L appliquée à b *)
  qap (imp_E C Pr RIZFm _ (And (Eps (OPair Empty x5) x0) (All (All (Imp (Eps x1 Omega) (Imp (Eps x0 x8) (Imp (Eps (OPair x1 x0) x2) (Eps (OPair (Suc x1) (appg (vs (vs (vs (vs (vs (vs (vs (vs (vs vz))))))))) x0)) x2)))))))).
  - qap (imp_E C Pr RIZFm _ (Eps x0 (Power x4))); [|qap (and_E1 C Pr RIZFm _ _ (All (Iff (Eps x0 x1) (And (Eps x0 x5) (Eps x0 (Sep x5 (app1 (s := V) (vs (vs (vs (vs vz)))) x0))))))); hypc].
    refine (qall_E C RIZFm V hV _ (Imp (Eps x0 (Power x5)) (Imp (And (Eps (OPair Empty x6) x0) (All (All (Imp (Eps x1 Omega) (Imp (Eps x0 x9) (Imp (Eps (OPair x1 x0) x2) (Eps (OPair (Suc x1) (appg (vs (vs (vs (vs (vs (vs (vs (vs (vs (vs vz)))))))))) x0)) x2))))))) (Eps x2 x0))) x0 _).
    qap (and_E2 C Pr RIZFm _ (Eps x1 x4)).
    qap iff_E1; [refine (qall_E C RIZFm V hV _ (Iff (Eps x0 x4) (And (Eps x0 x5) (All (Imp (Eps x0 (Power x6)) (Imp (And (Eps (OPair Empty x7) x0) (All (All (Imp (Eps x1 Omega) (Imp (Eps x0 x10) (Imp (Eps (OPair x1 x0) x2) (Eps (OPair (Suc x1) (appg (vs (vs (vs (vs (vs (vs (vs (vs (vs (vs (vs vz))))))))))) x0)) x2))))))) (Eps x1 x0)))))) x1 _); hypc|hypc].
  - (* b est clos *)
    qap (and_I C Pr RIZFm).
    + qap iff_E2; [refine (qall_E C RIZFm V hV _ (Iff (Eps x0 x1) (And (Eps x0 x5) (Eps x0 (Sep x5 (app1 (s := V) (vs (vs (vs (vs vz)))) x0))))) (OPair Empty x5) _); qap (and_E2 C Pr RIZFm _ (Eps x0 (Power x4))); hypc|].
      qap (and_I C Pr RIZFm).
      * qap (imp_E C Pr RIZFm _ (Eps x5 x6)); [|hypc].
        refine (qall_E C RIZFm V hV _ (Imp (Eps x0 x7) (Eps (OPair Empty x0) x5)) x5 _).
        qap (imp_E C Pr RIZFm _ (Eps Empty Omega)); [|exact (use0 empty_omega _)].
        refine (qall_E C RIZFm V hV _ (Imp (Eps x0 Omega) (All (Imp (Eps x0 x8) (Eps (OPair x1 x0) x6)))) Empty _). hypc.
      * qap iff_E2; [exact (axm A_sep _ (vVVP (OPair Empty x5) x4 (app1 (s := V) (vs (vs (vs vz))) x0)))|].
        qap (and_I C Pr RIZFm); [|hypc].
        qap (imp_E C Pr RIZFm _ (Eps x5 x6)); [|hypc].
        refine (qall_E C RIZFm V hV _ (Imp (Eps x0 x7) (Eps (OPair Empty x0) x5)) x5 _).
        qap (imp_E C Pr RIZFm _ (Eps Empty Omega)); [|exact (use0 empty_omega _)].
        refine (qall_E C RIZFm V hV _ (Imp (Eps x0 Omega) (All (Imp (Eps x0 x8) (Eps (OPair x1 x0) x6)))) Empty _). hypc.
    + qap (qall_I C RIZFm V hV). qap (qall_I C RIZFm V hV).
      qap (imp_I C Pr RIZFm). qap (imp_I C Pr RIZFm). qap (imp_I C Pr RIZFm).
      (* [y; n; b; z; P; L; A; a; B; g] *)
      qap iff_E2; [refine (qall_E C RIZFm V hV _ (Iff (Eps x0 x3) (And (Eps x0 x7) (Eps x0 (Sep x7 (app1 (s := V) (vs (vs (vs (vs (vs (vs vz)))))) x0))))) (OPair (Suc x1) (appg (vs (vs (vs (vs (vs (vs (vs (vs (vs vz))))))))) x0)) _); qap (and_E2 C Pr RIZFm _ (Eps x2 (Power x6))); hypc|].
      qap (and_I C Pr RIZFm).
      * qap (imp_E C Pr RIZFm _ (Eps (appg (vs (vs (vs (vs (vs (vs (vs (vs (vs vz))))))))) x0) x8)).
        { refine (qall_E C RIZFm V hV _ (Imp (Eps x0 x9) (Eps (OPair (Suc x2) x0) x7)) (appg (vs (vs (vs (vs (vs (vs (vs (vs (vs vz))))))))) x0) _).
          qap (imp_E C Pr RIZFm _ (Eps (Suc x1) Omega)); [|uses suc_omega (vV1 x1); hypc].
          refine (qall_E C RIZFm V hV _ (Imp (Eps x0 Omega) (All (Imp (Eps x0 x10) (Eps (OPair x1 x0) x8)))) (Suc x1) _). hypc. }
        qap (imp_E C Pr RIZFm _ (Eps x0 x8)); [|hypc]. refine (qall_E C RIZFm V hV _ (Imp (Eps x0 x9) (Eps (appg (vs (vs (vs (vs (vs (vs (vs (vs (vs (vs vz)))))))))) x0) x9)) x0 _). hypc.
      * qap iff_E2; [exact (axm A_sep _ (vVVP (OPair (Suc x1) (appg (vs (vs (vs (vs (vs (vs (vs (vs (vs vz))))))))) x0)) x6 (app1 (s := V) (vs (vs (vs (vs (vs vz))))) x0)))|].
        qap (and_I C Pr RIZFm).
        -- qap (imp_E C Pr RIZFm _ (Eps (appg (vs (vs (vs (vs (vs (vs (vs (vs (vs vz))))))))) x0) x8)).
        { refine (qall_E C RIZFm V hV _ (Imp (Eps x0 x9) (Eps (OPair (Suc x2) x0) x7)) (appg (vs (vs (vs (vs (vs (vs (vs (vs (vs vz))))))))) x0) _).
          qap (imp_E C Pr RIZFm _ (Eps (Suc x1) Omega)); [|uses suc_omega (vV1 x1); hypc].
          refine (qall_E C RIZFm V hV _ (Imp (Eps x0 Omega) (All (Imp (Eps x0 x10) (Eps (OPair x1 x0) x8)))) (Suc x1) _). hypc. }
        qap (imp_E C Pr RIZFm _ (Eps x0 x8)); [|hypc]. refine (qall_E C RIZFm V hV _ (Imp (Eps x0 x9) (Eps (appg (vs (vs (vs (vs (vs (vs (vs (vs (vs (vs vz)))))))))) x0) x9)) x0 _). hypc.
        -- qap (imp_E C Pr RIZFm _ (app1 (s := V) (vs (vs (vs (vs vz)))) (OPair x1 x0))).
           ++ qap (imp_E C Pr RIZFm _ (Eps x0 x8)); [|hypc]. qap (imp_E C Pr RIZFm _ (Eps x1 Omega)); [|hypc].
              refine (qall_E C RIZFm V hV _ (Imp (Eps x2 Omega) (Imp (Eps x0 x9) (Imp (app1 (s := V) (vs (vs (vs (vs (vs vz))))) (OPair x2 x0)) (app1 (s := V) (vs (vs (vs (vs (vs vz))))) (OPair (Suc x2) (appg (vs (vs (vs (vs (vs (vs (vs (vs (vs (vs vz)))))))))) x0)))))) x0 _). refine (qall_E C RIZFm V hV _ (All (Imp (Eps x1 Omega) (Imp (Eps x0 x10) (Imp (app1 (s := V) (vs (vs (vs (vs (vs (vs vz)))))) (OPair x1 x0)) (app1 (s := V) (vs (vs (vs (vs (vs (vs vz)))))) (OPair (Suc x1) (appg (vs (vs (vs (vs (vs (vs (vs (vs (vs (vs (vs vz))))))))))) x0))))))) x1 _). hypc.
           ++ qap (and_E2 C Pr RIZFm _ (Eps (OPair x1 x0) x6)).
              qap iff_E1; [exact (axm A_sep _ (vVVP (OPair x1 x0) x6 (app1 (s := V) (vs (vs (vs (vs (vs vz))))) x0)))|].
              qap (and_E2 C Pr RIZFm _ (Eps (OPair x1 x0) x6)).
              qap iff_E1; [refine (qall_E C RIZFm V hV _ (Iff (Eps x0 x3) (And (Eps x0 x7) (Eps x0 (Sep x7 (app1 (s := V) (vs (vs (vs (vs (vs (vs vz)))))) x0))))) (OPair x1 x0) _); qap (and_E2 C Pr RIZFm _ (Eps x2 (Power x6))); hypc|hypc].
Qed.

Tactic Notation "usesG0" constr(H) :=
  refine (deriv_cut_gen _ _ _ H _ _); [intros ? Hin; repeat (destruct Hin as [<-|Hin]); try contradiction].

Definition vG {Γ} (L A a B : tm Γ V) (g : tm (ι V :: Γ) V) : vec isym [ι V; ι V; ι V; ι V; σG] Γ :=
  @acons _ isym Γ (ι V) _ L (@acons _ isym Γ (ι V) _ A (@acons _ isym Γ (ι V) _ a
    (@acons _ isym Γ (ι V) _ B (@acons _ isym Γ σG _ g anil)))).
Definition vYG {Γ} (y n L A a B : tm Γ V) (g : tm (ι V :: Γ) V) : vec isym [ι V; ι V; ι V; ι V; ι V; ι V; σG] Γ :=
  @acons _ isym Γ (ι V) _ y (@acons _ isym Γ (ι V) _ n (vG L A a B g)).
Definition vPG {Γ} (P : tm (ι V :: Γ) Pr) (L A a B : tm Γ V) (g : tm (ι V :: Γ) V) :
  vec isym [σP; ι V; ι V; ι V; ι V; σG] Γ := @acons _ isym Γ σP _ P (vG L A a B g).

(** ** Propriétés de L (contexte [L; A; a; B; g]) *)

(** ⟨∅, a⟩ ε L. *)
Lemma clos_start : IZFm [ι V; ι V; ι V; ι V; σG] [(All (Imp (Eps x0 Omega) (All (Imp (Eps x0 x5) (Eps (OPair x1 x0) x3))))); (All (Imp (Eps x0 x4) (Eps (appg (vs (vs (vs (vs (vs vz))))) x0) x4))); (Eps x2 x3); (All (Iff (Eps x0 x1) (And (Eps x0 x2) (All (Imp (Eps x0 (Power x3)) (Imp (And (Eps (OPair Empty x4) x0) (All (All (Imp (Eps x1 Omega) (Imp (Eps x0 x7) (Imp (Eps (OPair x1 x0) x2) (Eps (OPair (Suc x1) (appg (vs (vs (vs (vs (vs (vs (vs (vs vz)))))))) x0)) x2))))))) (Eps x1 x0)))))))] (Eps (OPair Empty x2) x0).
Proof.
  qap iff_E2; [refine (qall_E C RIZFm V hV _ (Iff (Eps x0 x1) (And (Eps x0 x2) (All (Imp (Eps x0 (Power x3)) (Imp (And (Eps (OPair Empty x4) x0) (All (All (Imp (Eps x1 Omega) (Imp (Eps x0 x7) (Imp (Eps (OPair x1 x0) x2) (Eps (OPair (Suc x1) (appg (vs (vs (vs (vs (vs (vs (vs (vs vz)))))))) x0)) x2))))))) (Eps x1 x0)))))) (OPair Empty x2) _); hypc|].
  qap (and_I C Pr RIZFm).
  - qap (imp_E C Pr RIZFm _ (Eps x2 x3)); [|hypc].
      refine (qall_E C RIZFm V hV _ (Imp (Eps x0 x4) (Eps (OPair Empty x0) x2)) x2 _).
      qap (imp_E C Pr RIZFm _ (Eps Empty Omega)); [|exact (use0 empty_omega _)].
      refine (qall_E C RIZFm V hV _ (Imp (Eps x0 Omega) (All (Imp (Eps x0 x5) (Eps (OPair x1 x0) x3)))) Empty _). hypc.
  - qap (qall_I C RIZFm V hV). qap (imp_I C Pr RIZFm). qap (imp_I C Pr RIZFm).
    qap (and_E1 C Pr RIZFm _ _ (All (All (Imp (Eps x1 Omega) (Imp (Eps x0 x6) (Imp (Eps (OPair x1 x0) x2) (Eps (OPair (Suc x1) (appg (vs (vs (vs (vs (vs (vs (vs vz))))))) x0)) x2))))))). hypc.
Qed.

(** ⟨n, y⟩ ε L → ⟨S(n), g(y)⟩ ε L   (contexte [y; n; L; A; a; B; g]). *)
Lemma clos_step : IZFm [ι V; ι V; ι V; ι V; ι V; ι V; σG] [(All (Imp (Eps x0 Omega) (All (Imp (Eps x0 x7) (Eps (OPair x1 x0) x5))))); (All (Imp (Eps x0 x6) (Eps (appg (vs (vs (vs (vs (vs (vs (vs vz))))))) x0) x6))); (Eps x4 x5); (All (Iff (Eps x0 x3) (And (Eps x0 x4) (All (Imp (Eps x0 (Power x5)) (Imp (And (Eps (OPair Empty x6) x0) (All (All (Imp (Eps x1 Omega) (Imp (Eps x0 x9) (Imp (Eps (OPair x1 x0) x2) (Eps (OPair (Suc x1) (appg (vs (vs (vs (vs (vs (vs (vs (vs (vs (vs vz)))))))))) x0)) x2))))))) (Eps x1 x0))))))); Eps x1 Omega; Eps x0 x5; Eps (OPair x1 x0) x2]
  (Eps (OPair (Suc x1) (appg (vs (vs (vs (vs (vs (vs vz)))))) x0)) x2).
Proof.
  qap iff_E2; [refine (qall_E C RIZFm V hV _ (Iff (Eps x0 x3) (And (Eps x0 x4) (All (Imp (Eps x0 (Power x5)) (Imp (And (Eps (OPair Empty x6) x0) (All (All (Imp (Eps x1 Omega) (Imp (Eps x0 x9) (Imp (Eps (OPair x1 x0) x2) (Eps (OPair (Suc x1) (appg (vs (vs (vs (vs (vs (vs (vs (vs (vs (vs vz)))))))))) x0)) x2))))))) (Eps x1 x0)))))) (OPair (Suc x1) (appg (vs (vs (vs (vs (vs (vs vz)))))) x0)) _); hypc|].
  qap (and_I C Pr RIZFm).
  - qap (imp_E C Pr RIZFm _ (Eps (appg (vs (vs (vs (vs (vs (vs vz)))))) x0) x5)).
    + refine (qall_E C RIZFm V hV _ (Imp (Eps x0 x6) (Eps (OPair (Suc x2) x0) x4)) (appg (vs (vs (vs (vs (vs (vs vz)))))) x0) _).
      qap (imp_E C Pr RIZFm _ (Eps (Suc x1) Omega)); [|uses suc_omega (vV1 x1); hypc].
      refine (qall_E C RIZFm V hV _ (Imp (Eps x0 Omega) (All (Imp (Eps x0 x7) (Eps (OPair x1 x0) x5)))) (Suc x1) _). hypc.
    + qap (imp_E C Pr RIZFm _ (Eps x0 x5)); [|hypc]. refine (qall_E C RIZFm V hV _ (Imp (Eps x0 x6) (Eps (appg (vs (vs (vs (vs (vs (vs (vs vz))))))) x0) x6)) x0 _). hypc.
  - qap (qall_I C RIZFm V hV). qap (imp_I C Pr RIZFm). qap (imp_I C Pr RIZFm).
    (* [X; y; n; L; A; a; B; g] *)
    qap (imp_E C Pr RIZFm _ (Eps (OPair x2 x1) x0)).
    + qap (imp_E C Pr RIZFm _ (Eps x1 x6)); [|hypc]. qap (imp_E C Pr RIZFm _ (Eps x2 Omega)); [|hypc].
      refine (qall_E C RIZFm V hV _ (Imp (Eps x3 Omega) (Imp (Eps x0 x7) (Imp (Eps (OPair x3 x0) x1) (Eps (OPair (Suc x3) (appg (vs (vs (vs (vs (vs (vs (vs (vs vz)))))))) x0)) x1)))) x1 _).
      refine (qall_E C RIZFm V hV _ (All (Imp (Eps x1 Omega) (Imp (Eps x0 x8) (Imp (Eps (OPair x1 x0) x2) (Eps (OPair (Suc x1) (appg (vs (vs (vs (vs (vs (vs (vs (vs (vs vz))))))))) x0)) x2))))) x2 _).
      qap (and_E2 C Pr RIZFm _ (Eps (OPair Empty x5) x0)). hypc.
    + qap (imp_E C Pr RIZFm _ (And (Eps (OPair Empty x5) x0) (All (All (Imp (Eps x1 Omega) (Imp (Eps x0 x8) (Imp (Eps (OPair x1 x0) x2) (Eps (OPair (Suc x1) (appg (vs (vs (vs (vs (vs (vs (vs (vs (vs vz))))))))) x0)) x2)))))))); [|hypc]. qap (imp_E C Pr RIZFm _ (Eps x0 (Power x4))); [|hypc].
      refine (qall_E C RIZFm V hV _ (Imp (Eps x0 (Power x5)) (Imp (And (Eps (OPair Empty x6) x0) (All (All (Imp (Eps x1 Omega) (Imp (Eps x0 x9) (Imp (Eps (OPair x1 x0) x2) (Eps (OPair (Suc x1) (appg (vs (vs (vs (vs (vs (vs (vs (vs (vs (vs vz)))))))))) x0)) x2))))))) (Eps (OPair x3 x2) x0))) x0 _).
      qap (and_E2 C Pr RIZFm _ (Eps (OPair x2 x1) x4)).
      qap iff_E1; [refine (qall_E C RIZFm V hV _ (Iff (Eps x0 x4) (And (Eps x0 x5) (All (Imp (Eps x0 (Power x6)) (Imp (And (Eps (OPair Empty x7) x0) (All (All (Imp (Eps x1 Omega) (Imp (Eps x0 x10) (Imp (Eps (OPair x1 x0) x2) (Eps (OPair (Suc x1) (appg (vs (vs (vs (vs (vs (vs (vs (vs (vs (vs (vs vz))))))))))) x0)) x2))))))) (Eps x1 x0)))))) (OPair x2 x1) _); hypc|hypc].
Qed.

(** Inversion : tout élément de L est ⟨∅, a⟩ ou ⟨S(n), g(y)⟩ avec ⟨n, y⟩ ε L. *)
Lemma inv_L : IZFm [ι V; ι V; ι V; ι V; σG] [(All (Imp (Eps x0 Omega) (All (Imp (Eps x0 x5) (Eps (OPair x1 x0) x3))))); (All (Imp (Eps x0 x4) (Eps (appg (vs (vs (vs (vs (vs vz))))) x0) x4))); (Eps x2 x3); (All (Iff (Eps x0 x1) (And (Eps x0 x2) (All (Imp (Eps x0 (Power x3)) (Imp (And (Eps (OPair Empty x4) x0) (All (All (Imp (Eps x1 Omega) (Imp (Eps x0 x7) (Imp (Eps (OPair x1 x0) x2) (Eps (OPair (Suc x1) (appg (vs (vs (vs (vs (vs (vs (vs (vs vz)))))))) x0)) x2))))))) (Eps x1 x0)))))))] (All (Imp (Eps x0 x1) (And (Eps x0 x1) (Or (EqV x0 (OPair Empty x3)) (Ex (Ex (And (Eps x1 Omega) (And (Eps x0 x6) (And (Eps (OPair x1 x0) x3) (EqV x2 (OPair (Suc x1) (appg (vs (vs (vs (vs (vs (vs (vs vz))))))) x0)))))))))))).
Proof.
  uses lfp_ind (vPG (And (Eps x0 x1) (Or (EqV x0 (OPair Empty x3)) (Ex (Ex (And (Eps x1 Omega) (And (Eps x0 x6) (And (Eps (OPair x1 x0) x3) (EqV x2 (OPair (Suc x1) (appg (vs (vs (vs (vs (vs (vs (vs vz))))))) x0)))))))))) x0 x1 x2 x3 (eta σG (Γ := [ι V; ι V; ι V; ι V; σG]) (vs (vs (vs (vs vz)))))); [hypc|hypc|hypc|hypc| |].
  - qap (and_I C Pr RIZFm); [usesG0 clos_start; hypc|]. qap (or_I1 C Pr RIZFm). qap (qeq_refl C RIZFm V hV).
  - qap (qall_I C RIZFm V hV). qap (qall_I C RIZFm V hV).
    qap (imp_I C Pr RIZFm). qap (imp_I C Pr RIZFm). qap (imp_I C Pr RIZFm).
    (* [y; n; L; A; a; B; g] *)
    qap (and_I C Pr RIZFm).
    + usesG0 clos_step; try hypc.
      qap (and_E1 C Pr RIZFm _ _ (Or (EqV (OPair x1 x0) (OPair Empty x4)) (Ex (Ex (And (Eps x1 Omega) (And (Eps x0 x7) (And (Eps (OPair x1 x0) x4) (EqV (OPair x3 x2) (OPair (Suc x1) (appg (vs (vs (vs (vs (vs (vs (vs (vs vz)))))))) x0)))))))))).
      hypc.
    + qap (or_I2 C Pr RIZFm). qap (qex_I C RIZFm V hV _ _ x1). qap (qex_I C RIZFm V hV _ _ x0).
      qap (and_I C Pr RIZFm); [hypc|]. qap (and_I C Pr RIZFm); [hypc|]. qap (and_I C Pr RIZFm).
      * qap (and_E1 C Pr RIZFm _ _ (Or (EqV (OPair x1 x0) (OPair Empty x4)) (Ex (Ex (And (Eps x1 Omega) (And (Eps x0 x7) (And (Eps (OPair x1 x0) x4) (EqV (OPair x3 x2) (OPair (Suc x1) (appg (vs (vs (vs (vs (vs (vs (vs (vs vz)))))))) x0)))))))))).
        hypc.
      * qap (qeq_refl C RIZFm V hV).
Qed.

(** Totalité : ∀n ε ω. ∃y ε B. ⟨n, y⟩ ε L, par ε-induction. *)
Lemma tot_L : IZFm [ι V; ι V; ι V; ι V; σG] [(All (Imp (Eps x0 Omega) (All (Imp (Eps x0 x5) (Eps (OPair x1 x0) x3))))); (All (Imp (Eps x0 x4) (Eps (appg (vs (vs (vs (vs (vs vz))))) x0) x4))); (Eps x2 x3); (All (Iff (Eps x0 x1) (And (Eps x0 x2) (All (Imp (Eps x0 (Power x3)) (Imp (And (Eps (OPair Empty x4) x0) (All (All (Imp (Eps x1 Omega) (Imp (Eps x0 x7) (Imp (Eps (OPair x1 x0) x2) (Eps (OPair (Suc x1) (appg (vs (vs (vs (vs (vs (vs (vs (vs vz)))))))) x0)) x2))))))) (Eps x1 x0)))))))] (All (Imp (Eps x0 Omega) (Ex (And (Eps x0 x5) (Eps (OPair x1 x0) x2))))).
Proof.
  qap (imp_E C Pr RIZFm); [exact (axm A_ind _ (vP1 (Imp (Eps x0 Omega) (Ex (And (Eps x0 x5) (Eps (OPair x1 x0) x2))))))|].
  qap (qall_I C RIZFm V hV). qap (imp_I C Pr RIZFm). qap (imp_I C Pr RIZFm).
  (* [n; L; A; a; B; g] *)
  qap (or_E C Pr RIZFm _ (EqV x0 Empty) (Ex (And (Eps x0 Omega) (EqV x1 (Suc x0))))).
  { qap iff_E1; [exact (axm A_omega _ (vV1 x0))|hypc]. }
  - qap (qex_I C RIZFm V hV _ _ x3). qap (and_I C Pr RIZFm); [hypc|].
    refine (qeq_subst C RIZFm V hV _ (Eps (OPair x0 x4) x2) Empty x0 _ _).
    + qap (qeq_sym C RIZFm V hV). hypc.
    + uses clos_start (vG x1 x2 x3 x4 (eta σG (Γ := [ι V; ι V; ι V; ι V; ι V; σG]) (vs (vs (vs (vs (vs vz))))))); hypc.
  - qap (qex_E C RIZFm V hV _ (And (Eps x0 Omega) (EqV x1 (Suc x0)))); [hypc|].
    (* [m; n; L; A; a; B; g] *)
    qap (qex_E C RIZFm V hV _ (And (Eps x0 x6) (Eps (OPair x1 x0) x3))).
    { qap (imp_E C Pr RIZFm _ (Eps x0 Omega)); [|qap (and_E1 C Pr RIZFm _ _ (EqV x1 (Suc x0))); hypc].
      qap (imp_E C Pr RIZFm _ (Eps x0 x1)).
      - refine (qall_E C RIZFm V hV _ (Imp (Eps x0 x2) (Imp (Eps x0 Omega) (Ex (And (Eps x0 x7) (Eps (OPair x1 x0) x4))))) x0 _). hypc.
      - refine (qeq_subst C RIZFm V hV _ (Eps x1 x0) (Suc x0) x1 _ _).
        + qap (qeq_sym C RIZFm V hV). qap (and_E2 C Pr RIZFm _ (Eps x0 Omega)). hypc.
        + uses eps_suc_self (vV1 x0). }
    (* [w; m; n; L; A; a; B; g] *)
    refine (qex_I C RIZFm V hV _ _ (appg (vs (vs (vs (vs (vs (vs (vs vz))))))) x0) _). qap (and_I C Pr RIZFm).
    + qap (imp_E C Pr RIZFm _ (Eps x0 x6)); [refine (qall_E C RIZFm V hV _ (Imp (Eps x0 x7) (Eps (appg (vs (vs (vs (vs (vs (vs (vs (vs vz)))))))) x0) x7)) x0 _); hypc|].
      qap (and_E1 C Pr RIZFm _ _ (Eps (OPair x1 x0) x3)). hypc.
    + refine (qeq_subst C RIZFm V hV _ (Eps (OPair x0 (appg (vs (vs (vs (vs (vs (vs (vs (vs vz)))))))) x1)) x4) (Suc x1) x2 _ _).
      * qap (qeq_sym C RIZFm V hV). qap (and_E2 C Pr RIZFm _ (Eps x1 Omega)). hypc.
      * uses clos_step (vYG x0 x1 x3 x4 x5 x6 (eta σG (Γ := [ι V; ι V; ι V; ι V; ι V; ι V; ι V; σG]) (vs (vs (vs (vs (vs (vs (vs vz))))))))); try hypc.
        -- qap (and_E1 C Pr RIZFm _ _ (EqV x2 (Suc x1))). hypc.
        -- qap (and_E1 C Pr RIZFm _ _ (Eps (OPair x1 x0) x3)). hypc.
        -- qap (and_E2 C Pr RIZFm _ (Eps x0 x6)). hypc.
Qed.

(** Inversion, sous forme d'égalités   (contexte [y; n; L; A; a; B; g]) :
    ⟨n, y⟩ ε L → (n = ∅ ∧ y = a) ∨ ∃m w. ⟨m, w⟩ ε L ∧ n = S(m) ∧ y = g(w). *)
Lemma inv2 : IZFm [ι V; ι V; ι V; ι V; ι V; ι V; σG] [(All (Imp (Eps x0 Omega) (All (Imp (Eps x0 x7) (Eps (OPair x1 x0) x5))))); (All (Imp (Eps x0 x6) (Eps (appg (vs (vs (vs (vs (vs (vs (vs vz))))))) x0) x6))); (Eps x4 x5); (All (Iff (Eps x0 x3) (And (Eps x0 x4) (All (Imp (Eps x0 (Power x5)) (Imp (And (Eps (OPair Empty x6) x0) (All (All (Imp (Eps x1 Omega) (Imp (Eps x0 x9) (Imp (Eps (OPair x1 x0) x2) (Eps (OPair (Suc x1) (appg (vs (vs (vs (vs (vs (vs (vs (vs (vs (vs vz)))))))))) x0)) x2))))))) (Eps x1 x0))))))); Eps (OPair x1 x0) x2]
  (Or (And (EqV x1 Empty) (EqV x0 x4)) (Ex (Ex (And (Eps (OPair x1 x0) x4) (And (EqV x3 (Suc x1)) (EqV x2 (appg (vs (vs (vs (vs (vs (vs (vs (vs vz)))))))) x0))))))).
Proof.
  set (W := (Ex (And (Eps x1 Omega) (And (Eps x0 x7) (And (Eps (OPair x1 x0) x4) (EqV (OPair x3 x2) (OPair (Suc x1) (appg (vs (vs (vs (vs (vs (vs (vs (vs vz)))))))) x0)))))))
         : form (ι V :: [ι V; ι V; ι V; ι V; ι V; ι V; σG])).
  qap (or_E C Pr RIZFm _ (EqV (OPair x1 x0) (OPair Empty x4)) (Ex W)).
  - qap (and_E2 C Pr RIZFm _ (Eps (OPair x1 x0) x2)).
    qap (imp_E C Pr RIZFm _ (Eps (OPair x1 x0) x2)); [|hypc].
    refine (qall_E C RIZFm V hV _ (Imp (Eps x0 x3) (And (Eps x0 x3) (Or (EqV x0 (OPair Empty x5)) (Ex (Ex (And (Eps x1 Omega) (And (Eps x0 x8) (And (Eps (OPair x1 x0) x5) (EqV x2 (OPair (Suc x1) (appg (vs (vs (vs (vs (vs (vs (vs (vs (vs vz))))))))) x0))))))))))) (OPair x1 x0) _).
    uses inv_L (vG x2 x3 x4 x5 (eta σG (Γ := [ι V; ι V; ι V; ι V; ι V; ι V; σG]) (vs (vs (vs (vs (vs (vs vz)))))))); hypc.
  - qap (or_I1 C Pr RIZFm). qap (and_I C Pr RIZFm).
    + uses opair_inj1 (vV4 x1 x0 Empty x4). hypc.
    + uses opair_inj2 (vV4 x1 x0 Empty x4). hypc.
  - qap (qex_E C RIZFm V hV _ W); [hypc|]. subst W.
    qap (qex_E C RIZFm V hV _ (And (Eps x1 Omega) (And (Eps x0 x7) (And (Eps (OPair x1 x0) x4) (EqV (OPair x3 x2) (OPair (Suc x1) (appg (vs (vs (vs (vs (vs (vs (vs (vs vz)))))))) x0))))))); [hypc|].
    (* [w; m; y; n; L; A; a; B; g] *)
    set (H := (And (Eps x1 Omega) (And (Eps x0 x7) (And (Eps (OPair x1 x0) x4) (EqV (OPair x3 x2) (OPair (Suc x1) (appg (vs (vs (vs (vs (vs (vs (vs (vs vz)))))))) x0))))))
         : form [ι V; ι V; ι V; ι V; ι V; ι V; ι V; ι V; σG]).
    assert (HE : forall Ξ, In H Ξ -> IZFm _ Ξ (EqV (OPair x3 x2) (OPair (Suc x1) (appg (vs (vs (vs (vs (vs (vs (vs (vs vz)))))))) x0)))).
    { intros Ξ Hi. qap (and_E2 C Pr RIZFm _ (Eps (OPair x1 x0) x4)). qap (and_E2 C Pr RIZFm _ (Eps x0 x7)).
      qap (and_E2 C Pr RIZFm _ (Eps x1 Omega)). apply d_ax, Hi. }
    qap (or_I2 C Pr RIZFm). qap (qex_I C RIZFm V hV _ _ x1). qap (qex_I C RIZFm V hV _ _ x0).
    qap (and_I C Pr RIZFm); [|qap (and_I C Pr RIZFm)].
    + qap (and_E1 C Pr RIZFm _ _ (EqV (OPair x3 x2) (OPair (Suc x1) (appg (vs (vs (vs (vs (vs (vs (vs (vs vz)))))))) x0)))). qap (and_E2 C Pr RIZFm _ (Eps x0 x7)).
      qap (and_E2 C Pr RIZFm _ (Eps x1 Omega)). hypc.
    + uses opair_inj1 (vV4 x3 x2 (Suc x1) (appg (vs (vs (vs (vs (vs (vs (vs (vs vz)))))))) x0)). apply HE. repeat (first [left; reflexivity | right]).
    + uses opair_inj2 (vV4 x3 x2 (Suc x1) (appg (vs (vs (vs (vs (vs (vs (vs (vs vz)))))))) x0)). apply HE. repeat (first [left; reflexivity | right]).
Qed.

(** Fonctionnalité, au sens de Leibniz, par ε-induction sur n. *)
Lemma fun_L : IZFm [ι V; ι V; ι V; ι V; σG] [(All (Imp (Eps x0 Omega) (All (Imp (Eps x0 x5) (Eps (OPair x1 x0) x3))))); (All (Imp (Eps x0 x4) (Eps (appg (vs (vs (vs (vs (vs vz))))) x0) x4))); (Eps x2 x3); (All (Iff (Eps x0 x1) (And (Eps x0 x2) (All (Imp (Eps x0 (Power x3)) (Imp (And (Eps (OPair Empty x4) x0) (All (All (Imp (Eps x1 Omega) (Imp (Eps x0 x7) (Imp (Eps (OPair x1 x0) x2) (Eps (OPair (Suc x1) (appg (vs (vs (vs (vs (vs (vs (vs (vs vz)))))))) x0)) x2))))))) (Eps x1 x0)))))))] (All (All (All (Imp (Eps (OPair x2 x1) x3) (Imp (Eps (OPair x2 x0) x3) (EqV x1 x0)))))).
Proof.
  qap (imp_E C Pr RIZFm); [exact (axm A_ind _ (vP1 (All (All (Imp (Eps (OPair x2 x1) x3) (Imp (Eps (OPair x2 x0) x3) (EqV x1 x0)))))))|].
  qap (qall_I C RIZFm V hV). qap (imp_I C Pr RIZFm).
  qap (qall_I C RIZFm V hV). qap (qall_I C RIZFm V hV). qap (imp_I C Pr RIZFm). qap (imp_I C Pr RIZFm).
  (* [y'; y; n; L; A; a; B; g] *)
  qap (or_E C Pr RIZFm _ (And (EqV x2 Empty) (EqV x1 x5)) (Ex (Ex (And (Eps (OPair x1 x0) x5) (And (EqV x4 (Suc x1)) (EqV x3 (appg (vs (vs (vs (vs (vs (vs (vs (vs (vs vz))))))))) x0))))))).
  { uses inv2 (vYG x1 x2 x3 x4 x5 x6 (eta σG (Γ := [ι V; ι V; ι V; ι V; ι V; ι V; ι V; σG]) (vs (vs (vs (vs (vs (vs (vs vz))))))))); hypc. }
  - qap (or_E C Pr RIZFm _ (And (EqV x2 Empty) (EqV x0 x5)) (Ex (Ex (And (Eps (OPair x1 x0) x5) (And (EqV x4 (Suc x1)) (EqV x2 (appg (vs (vs (vs (vs (vs (vs (vs (vs (vs vz))))))))) x0))))))).
    { uses inv2 (vYG x0 x2 x3 x4 x5 x6 (eta σG (Γ := [ι V; ι V; ι V; ι V; ι V; ι V; ι V; σG]) (vs (vs (vs (vs (vs (vs (vs vz))))))))); hypc. }
    + qap (qeq_trans C RIZFm V hV _ x1 x5 x0).
      * qap (and_E2 C Pr RIZFm _ (EqV x2 Empty)). hypc.
      * qap (qeq_sym C RIZFm V hV). qap (and_E2 C Pr RIZFm _ (EqV x2 Empty)). hypc.
    + qap (qex_E C RIZFm V hV _ (Ex (And (Eps (OPair x1 x0) x5) (And (EqV x4 (Suc x1)) (EqV x2 (appg (vs (vs (vs (vs (vs (vs (vs (vs (vs vz))))))))) x0)))))); [hypc|]. qap (qex_E C RIZFm V hV _ (And (Eps (OPair x1 x0) x5) (And (EqV x4 (Suc x1)) (EqV x2 (appg (vs (vs (vs (vs (vs (vs (vs (vs (vs vz))))))))) x0))))); [hypc|].
      (* [w'; m'; y'; y; n; …] *)
      qap (bot_E C Pr RIZFm). uses suc_empty (vV1 x1).
      qap (qeq_trans C RIZFm V hV _ (Suc x1) x4 Empty).
      * qap (qeq_sym C RIZFm V hV). qap (and_E1 C Pr RIZFm _ _ (EqV x2 (appg (vs (vs (vs (vs (vs (vs (vs (vs (vs vz))))))))) x0))).
        qap (and_E2 C Pr RIZFm _ (Eps (OPair x1 x0) x5)). hypc.
      * qap (and_E1 C Pr RIZFm _ _ (EqV x3 x7)). hypc.
  - qap (qex_E C RIZFm V hV _ (Ex (And (Eps (OPair x1 x0) x5) (And (EqV x4 (Suc x1)) (EqV x3 (appg (vs (vs (vs (vs (vs (vs (vs (vs (vs vz))))))))) x0)))))); [hypc|]. qap (qex_E C RIZFm V hV _ (And (Eps (OPair x1 x0) x5) (And (EqV x4 (Suc x1)) (EqV x3 (appg (vs (vs (vs (vs (vs (vs (vs (vs (vs vz))))))))) x0))))); [hypc|].
    (* [w; m; y'; y; n; L; A; a; B; g] *)
    qap (or_E C Pr RIZFm _ (And (EqV x4 Empty) (EqV x2 x7)) (Ex (Ex (And (Eps (OPair x1 x0) x7) (And (EqV x6 (Suc x1)) (EqV x4 (appg (vs (vs (vs (vs (vs (vs (vs (vs (vs (vs (vs vz))))))))))) x0))))))).
    { uses inv2 (vYG x2 x4 x5 x6 x7 x8 (eta σG (Γ := [ι V; ι V; ι V; ι V; ι V; ι V; ι V; ι V; ι V; σG]) (vs (vs (vs (vs (vs (vs (vs (vs (vs vz))))))))))); hypc. }
    + qap (bot_E C Pr RIZFm). uses suc_empty (vV1 x1).
      qap (qeq_trans C RIZFm V hV _ (Suc x1) x4 Empty).
      * qap (qeq_sym C RIZFm V hV). qap (and_E1 C Pr RIZFm _ _ (EqV x3 (appg (vs (vs (vs (vs (vs (vs (vs (vs (vs vz))))))))) x0))).
        qap (and_E2 C Pr RIZFm _ (Eps (OPair x1 x0) x5)). hypc.
      * qap (and_E1 C Pr RIZFm _ _ (EqV x2 x7)). hypc.
    + qap (qex_E C RIZFm V hV _ (Ex (And (Eps (OPair x1 x0) x7) (And (EqV x6 (Suc x1)) (EqV x4 (appg (vs (vs (vs (vs (vs (vs (vs (vs (vs (vs (vs vz))))))))))) x0)))))); [hypc|]. qap (qex_E C RIZFm V hV _ (And (Eps (OPair x1 x0) x7) (And (EqV x6 (Suc x1)) (EqV x4 (appg (vs (vs (vs (vs (vs (vs (vs (vs (vs (vs (vs vz))))))))))) x0))))); [hypc|].
      (* [w'; m'; w; m; y'; y; n; L; A; a; B; g] *)
      (* m = m′ *)
      assert (Hm : forall Ξ, In (And (Eps (OPair x3 x2) x7) (And (EqV x6 (Suc x3)) (EqV x5 (appg (vs (vs (vs (vs (vs (vs (vs (vs (vs (vs (vs vz))))))))))) x2)))) Ξ -> In (And (Eps (OPair x1 x0) x7) (And (EqV x6 (Suc x1)) (EqV x4 (appg (vs (vs (vs (vs (vs (vs (vs (vs (vs (vs (vs vz))))))))))) x0)))) Ξ -> IZFm [ι V; ι V; ι V; ι V; ι V; ι V; ι V; ι V; ι V; ι V; ι V; σG] Ξ (EqV x3 x1)).
      { intros Ξ H1 H2. uses suc_inj (vV2 x3 x1).
        qap (qeq_trans C RIZFm V hV _ (Suc x3) x6 (Suc x1)).
        - qap (qeq_sym C RIZFm V hV). qap (and_E1 C Pr RIZFm _ _ (EqV x5 (appg (vs (vs (vs (vs (vs (vs (vs (vs (vs (vs (vs vz))))))))))) x2))).
          qap (and_E2 C Pr RIZFm _ (Eps (OPair x3 x2) x7)). apply d_ax, H1.
        - qap (and_E1 C Pr RIZFm _ _ (EqV x4 (appg (vs (vs (vs (vs (vs (vs (vs (vs (vs (vs (vs vz))))))))))) x0))).
          qap (and_E2 C Pr RIZFm _ (Eps (OPair x1 x0) x7)). apply d_ax, H2. }
      (* y = g(w) = g(w′) = y′ *)
      qap (qeq_trans C RIZFm V hV _ x5 (appg (vs (vs (vs (vs (vs (vs (vs (vs (vs (vs (vs vz))))))))))) x2) x4).
      * qap (and_E2 C Pr RIZFm _ (EqV x6 (Suc x3))). qap (and_E2 C Pr RIZFm _ (Eps (OPair x3 x2) x7)). hypc.
      * qap (qeq_trans C RIZFm V hV _ (appg (vs (vs (vs (vs (vs (vs (vs (vs (vs (vs (vs vz))))))))))) x2) (appg (vs (vs (vs (vs (vs (vs (vs (vs (vs (vs (vs vz))))))))))) x0) x4).
        -- refine (qeq_subst C RIZFm V hV _ (EqV (appg (vs (vs (vs (vs (vs (vs (vs (vs (vs (vs (vs (vs vz)))))))))))) x3) (appg (vs (vs (vs (vs (vs (vs (vs (vs (vs (vs (vs (vs vz)))))))))))) x0)) x2 x0 _ _); [|qap (qeq_refl C RIZFm V hV)].
           (* w = w′, par l'hypothèse d'induction en m *)
           qap (imp_E C Pr RIZFm _ (Eps (OPair x3 x0) x7)).
           ++ qap (imp_E C Pr RIZFm _ (Eps (OPair x3 x2) x7)).
              ** refine (qall_E C RIZFm V hV _ (Imp (Eps (OPair x4 x3) x8) (Imp (Eps (OPair x4 x0) x8) (EqV x3 x0))) x0 _).
                 refine (qall_E C RIZFm V hV _ (All (Imp (Eps (OPair x5 x1) x9) (Imp (Eps (OPair x5 x0) x9) (EqV x1 x0)))) x2 _).
                 qap (imp_E C Pr RIZFm _ (Eps x3 x6)).
                 --- refine (qall_E C RIZFm V hV _ (Imp (Eps x0 x7) (All (All (Imp (Eps (OPair x2 x1) x10) (Imp (Eps (OPair x2 x0) x10) (EqV x1 x0)))))) x3 _).
                     hypc.
                 --- refine (qeq_subst C RIZFm V hV _ (Eps x4 x0) (Suc x3) x6 _ _).
                     +++ qap (qeq_sym C RIZFm V hV). qap (and_E1 C Pr RIZFm _ _ (EqV x5 (appg (vs (vs (vs (vs (vs (vs (vs (vs (vs (vs (vs vz))))))))))) x2))).
                         qap (and_E2 C Pr RIZFm _ (Eps (OPair x3 x2) x7)). hypc.
                     +++ uses eps_suc_self (vV1 x3).
              ** qap (and_E1 C Pr RIZFm _ _ (And (EqV x6 (Suc x3)) (EqV x5 (appg (vs (vs (vs (vs (vs (vs (vs (vs (vs (vs (vs vz))))))))))) x2)))). hypc.
           ++ refine (qeq_subst C RIZFm V hV _ (Eps (OPair x0 x1) x8) x1 x3 _ _).
              ** qap (qeq_sym C RIZFm V hV). apply Hm; repeat (first [left; reflexivity | right]).
              ** qap (and_E1 C Pr RIZFm _ _ (And (EqV x6 (Suc x1)) (EqV x4 (appg (vs (vs (vs (vs (vs (vs (vs (vs (vs (vs (vs vz))))))))))) x0)))). hypc.
        -- qap (qeq_sym C RIZFm V hV). qap (and_E2 C Pr RIZFm _ (EqV x6 (Suc x1))).
           qap (and_E2 C Pr RIZFm _ (Eps (OPair x1 x0) x7)). hypc.
Qed.

(** L ⊆ ω × B. *)
Lemma sub_L : IZFm [ι V; ι V; ι V; ι V; σG] [(All (Imp (Eps x0 Omega) (All (Imp (Eps x0 x5) (Eps (OPair x1 x0) x3))))); (All (Imp (Eps x0 x4) (Eps (appg (vs (vs (vs (vs (vs vz))))) x0) x4))); (Eps x2 x3); (All (Iff (Eps x0 x1) (And (Eps x0 x2) (All (Imp (Eps x0 (Power x3)) (Imp (And (Eps (OPair Empty x4) x0) (All (All (Imp (Eps x1 Omega) (Imp (Eps x0 x7) (Imp (Eps (OPair x1 x0) x2) (Eps (OPair (Suc x1) (appg (vs (vs (vs (vs (vs (vs (vs (vs vz)))))))) x0)) x2))))))) (Eps x1 x0)))))))]
  (All (Imp (Eps x0 x1) (Ex (Ex (And (Eps x1 Omega) (And (Eps x0 x6) (EqV x2 (OPair x1 x0)))))))).
Proof.
  qap (qall_I C RIZFm V hV). qap (imp_I C Pr RIZFm).
  (* [z; L; A; a; B; g] *)
  qap (or_E C Pr RIZFm _ (EqV x0 (OPair Empty x3)) (Ex (Ex (And (Eps x1 Omega) (And (Eps x0 x6) (And (Eps (OPair x1 x0) x3) (EqV x2 (OPair (Suc x1) (appg (vs (vs (vs (vs (vs (vs (vs vz))))))) x0))))))))).
  { qap (and_E2 C Pr RIZFm _ (Eps x0 x1)). qap (imp_E C Pr RIZFm _ (Eps x0 x1)); [|hypc].
    refine (qall_E C RIZFm V hV _ (Imp (Eps x0 x2) (And (Eps x0 x2) (Or (EqV x0 (OPair Empty x4)) (Ex (Ex (And (Eps x1 Omega) (And (Eps x0 x7) (And (Eps (OPair x1 x0) x4) (EqV x2 (OPair (Suc x1) (appg (vs (vs (vs (vs (vs (vs (vs (vs vz)))))))) x0))))))))))) x0 _).
    uses inv_L (vG x1 x2 x3 x4 (eta σG (Γ := [ι V; ι V; ι V; ι V; ι V; σG]) (vs (vs (vs (vs (vs vz))))))); hypc. }
  - qap (qex_I C RIZFm V hV _ _ Empty). qap (qex_I C RIZFm V hV _ _ x3).
    qap (and_I C Pr RIZFm); [exact (use0 empty_omega _)|]. qap (and_I C Pr RIZFm); hypc.
  - qap (qex_E C RIZFm V hV _ (Ex (And (Eps x1 Omega) (And (Eps x0 x6) (And (Eps (OPair x1 x0) x3) (EqV x2 (OPair (Suc x1) (appg (vs (vs (vs (vs (vs (vs (vs vz))))))) x0)))))))); [hypc|]. qap (qex_E C RIZFm V hV _ (And (Eps x1 Omega) (And (Eps x0 x6) (And (Eps (OPair x1 x0) x3) (EqV x2 (OPair (Suc x1) (appg (vs (vs (vs (vs (vs (vs (vs vz))))))) x0))))))); [hypc|].
    (* [w; m; z; L; A; a; B; g] *)
    refine (qex_I C RIZFm V hV _ _ (Suc x1) _). refine (qex_I C RIZFm V hV _ _ (appg (vs (vs (vs (vs (vs (vs (vs vz))))))) x0) _).
    qap (and_I C Pr RIZFm); [|qap (and_I C Pr RIZFm)].
    + uses suc_omega (vV1 x1). qap (and_E1 C Pr RIZFm _ _ (And (Eps x0 x6) (And (Eps (OPair x1 x0) x3) (EqV x2 (OPair (Suc x1) (appg (vs (vs (vs (vs (vs (vs (vs vz))))))) x0)))))). hypc.
    + qap (imp_E C Pr RIZFm _ (Eps x0 x6)); [refine (qall_E C RIZFm V hV _ (Imp (Eps x0 x7) (Eps (appg (vs (vs (vs (vs (vs (vs (vs (vs vz)))))))) x0) x7)) x0 _); hypc|].
      qap (and_E1 C Pr RIZFm _ _ (And (Eps (OPair x1 x0) x3) (EqV x2 (OPair (Suc x1) (appg (vs (vs (vs (vs (vs (vs (vs vz))))))) x0))))).
      qap (and_E2 C Pr RIZFm _ (Eps x1 Omega)). hypc.
    + qap (and_E2 C Pr RIZFm _ (Eps (OPair x1 x0) x3)). qap (and_E2 C Pr RIZFm _ (Eps x0 x6)).
      qap (and_E2 C Pr RIZFm _ (Eps x1 Omega)). hypc.
Qed.

(** ** L'ensemble ambiant A et l'ensemble L *)

Definition vVR {Γ} (a : tm Γ V) (ψ : tm (ι V :: ι V :: Γ) Pr) : vec isym [ι V; σR] Γ :=
  @acons _ isym Γ (ι V) _ a (@acons _ isym Γ σR _ ψ anil).

(** Il existe A contenant tous les ⟨n, y⟩, n ε ω, y ε B (collection deux fois,
    puis réunion)   (contexte [B]). *)
Lemma prod_ex : IZFm [ι V] [] (Ex (All (Imp (Eps x0 Omega) (All (Imp (Eps x0 x3) (Eps (OPair x1 x0) x2)))))).
Proof.
  qap (qex_E C RIZFm V hV _ (All (Imp (Eps x0 Omega) (Ex (And (Eps x0 x2) (All (Imp (Eps x0 x4) (Eps (OPair x2 x0) x1)))))))).
  { qap (imp_E C Pr RIZFm _ (All (Imp (Eps x0 Omega) (Ex (All (Imp (Eps x0 x3) (Eps (OPair x2 x0) x1))))))).
    - exact (axm A_coll _ (vVR Omega (All (Imp (Eps x0 x3) (Eps (OPair x1 x0) x2))))).
    - qap (qall_I C RIZFm V hV). qap (imp_I C Pr RIZFm).
      (* [n; B] : la collection des ⟨n, y⟩ *)
      qap (qex_E C RIZFm V hV _ (All (Imp (Eps x0 x3) (Ex (And (Eps x0 x2) (EqV x0 (OPair x3 x1))))))).
      { qap (imp_E C Pr RIZFm _ (All (Imp (Eps x0 x2) (Ex (EqV x0 (OPair x2 x1)))))).
        - exact (axm A_coll _ (vVR x1 (EqV x1 (OPair x2 x0)))).
        - qap (qall_I C RIZFm V hV). qap (imp_I C Pr RIZFm).
          refine (qex_I C RIZFm V hV _ _ (OPair x1 x0) _). qap (qeq_refl C RIZFm V hV). }
      (* [c; n; B] *)
      qap (qex_I C RIZFm V hV _ _ x0). qap (qall_I C RIZFm V hV). qap (imp_I C Pr RIZFm).
      (* [y; c; n; B] *)
      qap (qex_E C RIZFm V hV _ (And (Eps x0 x2) (EqV x0 (OPair x3 x1)))).
      { qap (imp_E C Pr RIZFm _ (Eps x0 x3)); [|hypc].
        refine (qall_E C RIZFm V hV _ (Imp (Eps x0 x4) (Ex (And (Eps x0 x3) (EqV x0 (OPair x4 x1))))) x0 _). hypc. }
      refine (qeq_subst C RIZFm V hV _ (Eps x0 x3) x0 (OPair x3 x1) _ _).
      + qap (and_E2 C Pr RIZFm _ (Eps x0 x2)). hypc.
      + qap (and_E1 C Pr RIZFm _ _ (EqV x0 (OPair x3 x1))). hypc. }
  (* [C; B] : A ≜ ⋃C *)
  refine (qex_I C RIZFm V hV _ _ (Union x0) _).
  qap (qall_I C RIZFm V hV). qap (imp_I C Pr RIZFm). qap (qall_I C RIZFm V hV). qap (imp_I C Pr RIZFm).
  (* [y; n; C; B] *)
  qap (qex_E C RIZFm V hV _ (And (Eps x0 x3) (All (Imp (Eps x0 x5) (Eps (OPair x3 x0) x1))))).
  { qap (imp_E C Pr RIZFm _ (Eps x1 Omega)); [|hypc].
    refine (qall_E C RIZFm V hV _ (Imp (Eps x0 Omega) (Ex (And (Eps x0 x4) (All (Imp (Eps x0 x6) (Eps (OPair x2 x0) x1)))))) x1 _).
    hypc. }
  (* [c; y; n; C; B] *)
  qap iff_E2; [exact (axm A_union _ (vV2 (OPair x2 x1) x3))|].
  qap (qex_I C RIZFm V hV _ _ x0). qap (and_I C Pr RIZFm).
  - qap (imp_E C Pr RIZFm _ (Eps x1 x4)); [|hypc].
    refine (qall_E C RIZFm V hV _ (Imp (Eps x0 x5) (Eps (OPair x3 x0) x1)) x1 _).
    qap (and_E2 C Pr RIZFm _ (Eps x0 x3)). hypc.
  - qap (and_E1 C Pr RIZFm _ _ (All (Imp (Eps x0 x5) (Eps (OPair x3 x0) x1)))). hypc.
Qed.

(** L ≜ {z ε A ∣ ∀X. X ε P(A) → Cl(X) → z ε X}   (contexte [A; a; B; g]). *)
Lemma sep_ex : IZFm [ι V; ι V; ι V; σG] [] (Ex (All (Iff (Eps x0 x1) (And (Eps x0 x2) (All (Imp (Eps x0 (Power x3)) (Imp (And (Eps (OPair Empty x4) x0) (All (All (Imp (Eps x1 Omega) (Imp (Eps x0 x7) (Imp (Eps (OPair x1 x0) x2) (Eps (OPair (Suc x1) (appg (vs (vs (vs (vs (vs (vs (vs (vs vz)))))))) x0)) x2))))))) (Eps x1 x0)))))))).
Proof.
  refine (qex_I C RIZFm V hV _ _ (Sep x0 (All (Imp (Eps x0 (Power x2)) (Imp (And (Eps (OPair Empty x3) x0) (All (All (Imp (Eps x1 Omega) (Imp (Eps x0 x6) (Imp (Eps (OPair x1 x0) x2) (Eps (OPair (Suc x1) (appg (vs (vs (vs (vs (vs (vs (vs vz))))))) x0)) x2))))))) (Eps x1 x0))))) _).
  qap (qall_I C RIZFm V hV). exact (axm A_sep _ (vVVP x0 x1 (All (Imp (Eps x0 (Power x3)) (Imp (And (Eps (OPair Empty x4) x0) (All (All (Imp (Eps x1 Omega) (Imp (Eps x0 x7) (Imp (Eps (OPair x1 x0) x2) (Eps (OPair (Suc x1) (appg (vs (vs (vs (vs (vs (vs (vs (vs vz)))))))) x0)) x2))))))) (Eps x1 x0)))))).
Qed.

(** ** La récursion sur ℕ, dans IZF⁻ε

    Dans le contexte [a; B; g] : si a ε B et g envoie B dans B, il existe L
    avec ⟨∅, a⟩ ε L, clos par ⟨n, y⟩ ↦ ⟨S(n), g(y)⟩, total sur ω,
    fonctionnel (Leibniz) et inclus dans ω × B. *)
Theorem kt_rec : IZFm [ι V; ι V; σG] [Eps x0 x1; All (Imp (Eps x0 x2) (Eps (appg (vs (vs (vs vz))) x0) x2))]
  (Ex (And (Eps (OPair Empty x1) x0) (And (All (All (Imp (Eps x1 Omega) (Imp (Eps x0 x4) (Imp (Eps (OPair x1 x0) x2) (Eps (OPair (Suc x1) (appg (vs (vs (vs (vs (vs vz))))) x0)) x2)))))) (And (All (Imp (Eps x0 Omega) (Ex (And (Eps x0 x4) (Eps (OPair x1 x0) x2))))) (And (All (All (All (Imp (Eps (OPair x2 x1) x3) (Imp (Eps (OPair x2 x0) x3) (EqV x1 x0)))))) (All (Imp (Eps x0 x1) (Ex (Ex (And (Eps x1 Omega) (And (Eps x0 x5) (EqV x2 (OPair x1 x0))))))))))))).
Proof.
  qap (qex_E C RIZFm V hV _ (All (Imp (Eps x0 Omega) (All (Imp (Eps x0 x4) (Eps (OPair x1 x0) x2)))))).
  { uses prod_ex (vV1 x1). }
  (* [A; a; B; g] *)
  qap (qex_E C RIZFm V hV _ (All (Iff (Eps x0 x1) (And (Eps x0 x2) (All (Imp (Eps x0 (Power x3)) (Imp (And (Eps (OPair Empty x4) x0) (All (All (Imp (Eps x1 Omega) (Imp (Eps x0 x7) (Imp (Eps (OPair x1 x0) x2) (Eps (OPair (Suc x1) (appg (vs (vs (vs (vs (vs (vs (vs (vs vz)))))))) x0)) x2))))))) (Eps x1 x0)))))))); [usesG0 sep_ex|].
  (* [L; A; a; B; g] *)
  qap (qex_I C RIZFm V hV _ _ x0).
  qap (and_I C Pr RIZFm); [|qap (and_I C Pr RIZFm); [|qap (and_I C Pr RIZFm); [|qap (and_I C Pr RIZFm)]]].
  - usesG0 clos_start; hypc.
  - qap (qall_I C RIZFm V hV). qap (qall_I C RIZFm V hV).
    qap (imp_I C Pr RIZFm). qap (imp_I C Pr RIZFm). qap (imp_I C Pr RIZFm).
    usesG0 clos_step; hypc.
  - usesG0 tot_L; hypc.
  - usesG0 fun_L; hypc.
  - usesG0 sub_L; hypc.
Qed.
