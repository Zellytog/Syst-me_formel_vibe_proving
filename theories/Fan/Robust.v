(** * Le théorème robuste de l'éventail

    Sous WKL et Markov (méta), tout EFdata avec recherche non bornée (sous
    forme de Markov interne), existentiel fort au type (N → B) → N et
    continuité partout réalise FT ([robust_fan_holds]).

    Le réalisateur, uniforme en B :
    1. de Mono(B) ∧ Bar(B), l'existentiel fort tire une fonctionnelle G
       (indice du ⋁), avec ⌜G⌝ et R := ∀α. ⌜α⌝ ⊃ B(α↾G(α)) ;
    2. la continuité donne [G continue] ; par le lemme méta, [h_G s'annule],
       où h_G(n) := 1 − C'_G(n) ; h_G est calculée à partir de ⌜G⌝ par
       récursion primitive ;
    3. la recherche donne n avec ⌜n⌝ et [h_G(n) = 0] ;
    4. pour α codé, on cherche (bornée) j ≤ n avec G(α↾j 0^∞) ≤ j, on
       applique R en β := α↾j 0^∞, ce qui donne B(α↾G(β)), puis Mono en α
       avec les longueurs codées G(β) et n − G(β) pour passer à B(α↾n). *)

From Stdlib Require Import List Arith Lia Bool.
Import ListNotations.
From SF.Models Require Import PSet Frame.
From SF.Fan Require Import Ent Statement PR Meta.

Section Robust.

Context (E : efdata).

Local Notation Φ := (pcar (fprop E)).
Local Notation "⌜ n ⌝" := (code (e := E) n).

(** Monter un fait d'un niveau de paramètres. *)
Lemma ent_lift {X Y} (C : X -> Φ) (D : X * Y -> Φ) (A : X -> Φ) :
  ENT C A -> ENT (fun t : X * Y => fand (C (fst t)) (D t)) (fun t => A (fst t)).
Proof. intros H. eapply ent_trans; [apply ent_fst|exact (ent_reindex fst _ _ H)]. Qed.

Lemma rz_lift {X Y} (C : X -> Φ) (D : X * Y -> Φ) (f : X -> nat) :
  RZ E C f -> RZ E (fun t : X * Y => fand (C (fst t)) (D t)) (fun t => f (fst t)).
Proof. exact (ent_lift C D (fun x => ⌜f x⌝)). Qed.

Lemma rz_top {X} (C : X -> Φ) : RZ E (fun t : X * nat => fand (C (fst t)) ⌜snd t⌝) snd.
Proof. apply ent_snd. Qed.

Lemma ent_meta_and {X} (P Q : X -> Prop) :
  ENT (F := E) (fun x => fand (fprop_of (P x)) (fprop_of (Q x))) (fun x => fprop_of (P x /\ Q x)).
Proof.
  apply (ent_meta_elim (F := E) Q (fun x => fprop_of (P x)) (fun x => fprop_of (P x /\ Q x))).
  exact (ent_meta_map (F := E) (fun d : { x | Q x } => P (proj1_sig d)) (fun d => P (proj1_sig d) /\ Q (proj1_sig d))
           (fun d HP => conj HP (proj2_sig d))).
Qed.

(** ** Les objets *)

Local Notation Pred := (list bool -> Φ).
Local Notation Fun2 := ((nat -> bool) -> nat).

Definition Rb (B : Pred) (G : Fun2) : Φ := fall (fun α => fimp (cpath E α) (B (pre α (G α)))).
Definition Kb (B : Pred) (G : Fun2) : Φ := fand (cfun2 E G) (Rb B G).
Definition G1 (p : Pred * Fun2) : Φ := fand (Mono E (fst p)) (Kb (fst p) (snd p)).

Definition hG (G : Fun2) (n : nat) : nat := 1 - Nat.b2n (Cp G n).

Lemma ent_G1_cfun2 : ENT G1 (fun p => cfun2 E (snd p)).
Proof. eapply ent_trans; [apply ent_snd|apply ent_fst]. Qed.

(** ** h_G est calculée à partir de ⌜G⌝ *)

(** Le code du chemin path k j, à partir de ⌜k⌝ et ⌜j⌝. *)
Lemma ent_path {X} (C : X -> Φ) (k j : X -> nat) :
  RZ E C k -> RZ E C j -> ENT C (fun x => cpath E (path (k x) (j x))).
Proof.
  intros Hk Hj. apply ent_cpath. unfold path.
  apply rz_band.
  - apply rz_ltb; [apply rz_top|apply rz_lift, Hj].
  - apply rz_testbit; [apply rz_lift, Hk|apply rz_top].
Qed.

Lemma ent_trunc {X} (C : X -> Φ) (α : X -> nat -> bool) (j : X -> nat) :
  ENT C (fun x => cpath E (α x)) -> RZ E C j -> ENT C (fun x => cpath E (trunc (α x) (j x))).
Proof.
  intros Ha Hj. apply ent_cpath. unfold trunc.
  apply rz_band.
  - apply rz_ltb; [apply rz_top|apply rz_lift, Hj].
  - apply (rz_call E _ (fun t n => Nat.b2n (α (fst t) n)) snd); [|apply rz_top].
    exact (ent_lift C _ (fun x => cpath E (α x)) Ha).
Qed.

Lemma rz_Cp {X} (C : X -> Φ) (G : X -> Fun2) (n : X -> nat) :
  ENT C (fun x => cfun2 E (G x)) -> RZ E C n -> RZ E C (fun x => Nat.b2n (Cp (G x) (n x))).
Proof.
  intros HG Hn. unfold Cp.
  apply (rz_ball E C (fun x => 2 ^ n x) (fun x k => bex (S (n x)) (Pk (G x) k))); [apply rz_pow2, Hn|].
  unfold RZP. set (C1 := fun t : X * nat => fand (C (fst t)) ⌜snd t⌝).
  apply (rz_bex E C1 (fun t => S (n (fst t))) (fun t j => Pk (G (fst t)) (snd t) j));
    [apply rz_succ, rz_lift, Hn|].
  unfold RZP, Pk. set (C2 := fun t : (X * nat) * nat => fand (C1 (fst t)) ⌜snd t⌝).
  apply rz_leb; [|apply rz_top].
  apply (rz_call2 E C2 (fun t => G (fst (fst t))) (fun t => path (snd (fst t)) (snd t))).
  - exact (ent_lift C1 _ _ (ent_lift C _ _ HG)).
  - apply ent_path; [apply rz_lift, rz_top|apply rz_top].
Qed.

Lemma ent_cfun_h : ENT G1 (fun p => cfun E (hG (snd p))).
Proof.
  apply ent_cfun. unfold hG. apply rz_sub; [apply rz_const|].
  apply rz_Cp; [exact (ent_lift G1 _ _ ent_G1_cfun2)|apply rz_top].
Qed.

(** ** La borne : recherche *)

Definition Cont (p : Pred * Fun2) : Prop := forall α, cont_at (snd p) α.

Lemma ent_cont (HCo : continuity E) : ENT G1 (fun p => fprop_of (Cont p)).
Proof.
  destruct HCo as [e He]. eapply ent_trans; [exact ent_G1_cfun2|]. exists e. intros p. apply He.
Qed.

Lemma ent_search (WKL : WKL_meta) (MP : MP_meta) (HS : search E) (HCo : continuity E) :
  ENT G1 (fun p => fex (fun n => fand ⌜n⌝ (fprop_of (hG (snd p) n = 0)))).
Proof.
  destruct HS as [e He].
  eapply ent_trans; [|exists e; intros p; apply He].
  apply ent_pair; [exact ent_cfun_h|].
  eapply ent_trans; [exact (ent_cont HCo)|].
  apply ent_meta_map. intros p Hc. destruct (fan_meta (snd p) WKL MP Hc) as [n Hn].
  exists n. unfold hG. rewrite Hn. reflexivity.
Qed.

(** ** Le réalisateur de la borne uniforme *)

(** Les paramètres de la dernière étape : (B, G), n, avec les faits méta. *)
Definition Dom : Type := { x : (Pred * Fun2) * nat | Cont (fst x) /\ hG (snd (fst x)) (snd x) = 0 }.

Definition dB (d : Dom) : Pred := fst (fst (proj1_sig d)).
Definition dG (d : Dom) : Fun2 := snd (fst (proj1_sig d)).
Definition dn (d : Dom) : nat := snd (proj1_sig d).

Definition jstar (d : Dom) (α : nat -> bool) : nat := blast (S (dn d)) (fun j => dG d (trunc α j) <=? j).
Definition beta (d : Dom) (α : nat -> bool) : nat -> bool := trunc α (jstar d α).

Lemma jstar_spec d α : jstar d α < S (dn d) /\ dG d (beta d α) <= jstar d α.
Proof.
  destruct d as [[[B G] n] [Hc Hh]]. unfold jstar, beta, dG, dn; cbn [fst snd proj1_sig] in *.
  assert (Hcp : Cp G n = true) by (unfold hG in Hh; destruct (Cp G n); [reflexivity|discriminate]).
  destruct (blast_spec _ _ (t0_meta G n Hc Hcp α)) as [H1 H2].
  split; [exact H1|]. apply Nat.leb_le, H2.
Qed.

Definition Cd (d : Dom) : Φ := fand (G1 (fst (proj1_sig d))) ⌜dn d⌝.
Definition Ct (t : Dom * (nat -> bool)) : Φ := fand (Cd (fst t)) (cpath E (snd t)).

Lemma t0_realizer : ENT Ct (fun t => dB (fst t) (pre (snd t) (dn (fst t)))).
Proof.
  (* Les composantes du contexte. *)
  assert (HG : ENT Ct (fun t => cfun2 E (dG (fst t)))).
  { eapply ent_trans; [apply ent_fst|]. eapply ent_trans; [apply ent_fst|].
    exact (ent_reindex (fun t : Dom * (nat -> bool) => fst (proj1_sig (fst t))) _ _ ent_G1_cfun2). }
  assert (Ha : ENT Ct (fun t => cpath E (snd t))) by apply ent_snd.
  assert (Hn : RZ E Ct (fun t => dn (fst t))).
  { eapply ent_trans; [apply ent_fst|apply ent_snd]. }
  assert (HR : ENT Ct (fun t => Rb (dB (fst t)) (dG (fst t)))).
  { eapply ent_trans; [apply ent_fst|]. eapply ent_trans; [apply ent_fst|].
    eapply ent_trans; [apply ent_snd|apply ent_snd]. }
  assert (HM : ENT Ct (fun t => Mono E (dB (fst t)))).
  { eapply ent_trans; [apply ent_fst|]. eapply ent_trans; [apply ent_fst|apply ent_fst]. }
  (* j* et le code de β = α↾j* 0^∞. *)
  assert (Hj : RZ E Ct (fun t => jstar (fst t) (snd t))).
  { unfold jstar.
    apply (rz_blast E Ct (fun t => S (dn (fst t))) (fun t j => dG (fst t) (trunc (snd t) j) <=? j));
      [apply rz_succ, Hn|].
    unfold RZP. apply rz_leb; [|apply rz_top].
    apply (rz_call2 E _ (fun s => dG (fst (fst s))) (fun s => trunc (snd (fst s)) (snd s))).
    - exact (ent_lift Ct _ _ HG).
    - apply ent_trunc; [exact (ent_lift Ct _ _ Ha)|apply rz_top]. }
  assert (Hb : ENT Ct (fun t => cpath E (beta (fst t) (snd t)))).
  { unfold beta. exact (ent_trunc Ct snd (fun t => jstar (fst t) (snd t)) Ha Hj). }
  (* R en β : B(β↾G(β)) = B(α↾G(β)), car G(β) ≤ j*. *)
  pose proof (ent_app _ _ _ (ent_inst _ _ (fun t => beta (fst t) (snd t)) HR) Hb) as HBb.
  assert (HBa : ENT Ct (fun t => dB (fst t) (pre (snd t) (dG (fst t) (beta (fst t) (snd t)))))).
  { eapply ent_eq_r; [|exact HBb]. intros [d α]. cbn [fst snd].
    destruct (jstar_spec d α) as [_ H2]. unfold beta at 1. rewrite pre_trunc by exact H2. apply peq_refl. }
  (* Mono en α, avec n₁ := G(β) et k := n − G(β). *)
  assert (Hg : RZ E Ct (fun t => dG (fst t) (beta (fst t) (snd t)))) by (apply rz_call2; assumption).
  assert (Hk : RZ E Ct (fun t => dn (fst t) - dG (fst t) (beta (fst t) (snd t)))) by (apply rz_sub; assumption).
  pose proof (ent_app _ _ _ (ent_inst _ _ snd HM) Ha) as K1.
  pose proof (ent_app _ _ _ (ent_inst _ _ (fun t => dG (fst t) (beta (fst t) (snd t))) K1) Hg) as K2.
  pose proof (ent_app _ _ _ (ent_inst _ _ (fun t => dn (fst t) - dG (fst t) (beta (fst t) (snd t))) K2) Hk) as K3.
  pose proof (ent_app _ _ _ K3 HBa) as K4.
  eapply ent_eq_r; [|exact K4]. intros [d α]. cbn [fst snd].
  destruct (jstar_spec d α) as [H1 H2]. replace (dG d (beta d α) + (dn d - dG d (beta d α))) with (dn d) by lia.
  apply peq_refl.
Qed.

Lemma unif_realizer : ENT Cd (fun d => Unif E (dB d)).
Proof.
  unfold Unif. apply (ent_exI (I := nat) _ _ dn). apply ent_pair; [apply ent_snd|].
  apply (ent_gen (I := nat -> bool)). apply ent_lam. exact t0_realizer.
Qed.

(** ** Assemblage *)

Theorem fan_realized (WKL : WKL_meta) (MP : MP_meta) (HS : search E) (HCh : choice E) (HCo : continuity E) :
  exists e, fent ftop e (FT E).
Proof.
  (* Mono ∧ Bar ≤ Mono ∧ ⋁_G K(B, G). *)
  assert (H1 : ENT (fun B => fand (Mono E B) (Bar E B))
                   (fun B => fand (Mono E B) (fex (fun G => Kb B G)))).
  { apply ent_pair; [apply ent_fst|]. eapply ent_trans; [apply ent_snd|].
    destruct HCh as [e He]. exists e. intros B. exact (He (fun α n => B (pre α n))). }
  (* Pour (B, G) : G1 ≤ Unif. *)
  assert (H2 : ENT G1 (fun p => Unif E (fst p))).
  { assert (K : ENT G1 (fun p => fand (fand (G1 p) (fprop_of (Cont p)))
                                       (fex (fun n => fand ⌜n⌝ (fprop_of (hG (snd p) n = 0)))))).
    { apply ent_pair; [apply ent_pair; [apply ent_refl|exact (ent_cont HCo)]|exact (ent_search WKL MP HS HCo)]. }
    eapply ent_trans; [exact K|]. apply ent_exE.
    set (P := fun x : (Pred * Fun2) * nat => Cont (fst x) /\ hG (snd (fst x)) (snd x) = 0).
    assert (K2 : ENT (fun x : (Pred * Fun2) * nat =>
                        fand (fand (G1 (fst x)) (fprop_of (Cont (fst x))))
                             (fand ⌜snd x⌝ (fprop_of (hG (snd (fst x)) (snd x) = 0))))
                     (fun x => fand (fand (G1 (fst x)) ⌜snd x⌝) (fprop_of (P x)))).
    { apply ent_pair.
      - apply ent_pair; [eapply ent_trans; [apply ent_fst|apply ent_fst]|eapply ent_trans; [apply ent_snd|apply ent_fst]].
      - eapply ent_trans; [|apply ent_meta_and]. apply ent_pair.
        + eapply ent_trans; [apply ent_fst|apply ent_snd].
        + eapply ent_trans; [apply ent_snd|apply ent_snd]. }
    eapply ent_trans; [exact K2|]. apply ent_meta_elim. exact unif_realizer. }
  (* Assemblage : élimination de ⋁_G, puis λ et ⋀_B. *)
  assert (H3 : ENT (fun B => fand (Mono E B) (fex (fun G => Kb B G))) (fun B => Unif E B)).
  { apply ent_exE. exact H2. }
  assert (H4 : ENT (fun B : Pred => ftop) (fun B => fimp (fand (Mono E B) (Bar E B)) (Unif E B))).
  { apply ent_lam. eapply ent_trans; [apply ent_snd|]. eapply ent_trans; [exact H1|exact H3]. }
  destruct H4 as [e He]. exists (e_gen e). apply f_gen. exact He.
Qed.

End Robust.

(** Le théorème 41, sous la forme de [Statement.v]. *)
Theorem robust_fan_holds : WKL_meta -> MP_meta -> robust_fan.
Proof. intros WKL MP E HS HCh HCo. exact (fan_realized E WKL MP HS HCh HCo). Qed.
