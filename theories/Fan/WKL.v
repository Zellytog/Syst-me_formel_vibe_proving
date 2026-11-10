(** * WKL dans HA_ω^{ω,ω} + listes, et sa réfutation abstraite

    WKL s'énonce comme FT ([FT.v]), le long des chemins : pour T : L → O,
      Tree(T) := ∀α:N→N. ∀n. T(α↾(n+1)) ⇒ T(α↾n),
      Inf(T)  := ∀n. ∃β:N→N. T(β↾n),
      WKL     := ∀T. Tree(T) ⇒ Inf(T) ⇒ ∃α. ∀n. T(α↾n).
    (Tout mot binaire étant un préfixe d'un chemin, Tree est la clôture par
    préfixe et Inf l'existence de mots de toute longueur.)

    [wkl_reduce] : sur une donnée d'entiers E, si un prédicat méta K sur
    les mots est clos par préfixe et a, pour tout n, un témoin ℓₙ de
    longueur n, et si ces témoins sont *uniformément réalisés*
    (⊤ ≤ ∀n. ⌜n⌝ ⊃ ⌜ℓₙ⌝), alors un réalisateur de ⟦WKL⟧ fournit un
    réalisateur de ∃α. ⌜α⌝ ∧ ∀n. ⌜n⌝ ⊃ [K(α↾n)] : on applique WKL au
    prédicat T(ℓ) := [K(ℓ)]. *)

From Stdlib Require Import List Arith Lia Bool.
Import ListNotations.
From SF.Syntax Require Import Spec Terms Vectors.
From SF.Calculus Require Import System Rules.
From SF.Logic Require Import Judgment Propositional.
From SF.Functional Require Import Arrow Graded.
From SF.Quantifiers Require Import Quant Order.
From SF.Arithmetic Require Import Arith Inductive.
From SF.Extensions Require Import Same.
From SF.Models Require Import PSet Frame Semantics Tarski FrameTarski.
From SF.HA Require Import Signature Model.
From SF.Fan Require Import Ent Statement PR Terms FT.

Set Universe Polymorphism.

Local Notation ι a := (Spec [] a).
Local Notation form := (Judgment.form hL tO).

Definition TreeW : form [ι LO] :=
  All NN (All tN (Imp (ap v2 (ap (ap pret v1) (Succ v0))) (ap v2 (ap (ap pret v1) v0)))).
Definition InfW : form [ι LO] := All tN (Ex NN (ap v2 (ap (ap pret v0) v1))).
Definition PathW : form [ι LO] := Ex NN (All tN (ap v2 (ap (ap pret v1) v0))).
Definition WKL : form [] := All LO (Imp TreeW (Imp InfW PathW)).

Definition TreeWD : form [ι LO] :=
  RA NN (RA tN (Imp (ap v2 (ap (ap pret v1) (Succ v0))) (ap v2 (ap (ap pret v1) v0)))).
Definition InfWD : form [ι LO] := RA tN (RE NN (ap v2 (ap (ap pret v0) v1))).
Definition PathWD : form [ι LO] := RE NN (RA tN (ap v2 (ap (ap pret v1) v0))).
Definition WKLD : form [] := RA LO (Imp TreeWD (Imp InfWD PathWD)).

Lemma ltr_WKL : ltr (Rel (dsc := dL)) WKL = WKLD.
Proof. reflexivity. Qed.

Section Sem.

Context (F : frame).

Local Notation So := (So F (Ind := unit)).
Local Notation sv := (sval So (Iy F (dsc := dL))).
Local Notation Φ := (pcar (fprop F)).

Definition TreeS (B : So LO) : Φ :=
  fall (fun α : So NN => fimp (Dsem F NN α) (fall (fun n : So tN => fimp (Dsem F tN n)
    (fimp (Bp F B α (S n)) (Bp F B α n))))).
Definition InfS (B : So LO) : Φ :=
  fall (fun n : So tN => fimp (Dsem F tN n) (fex (fun β : So NN => fand (Dsem F NN β) (Bp F B β n)))).
Definition PathS (B : So LO) : Φ :=
  fex (fun α : So NN => fand (Dsem F NN α) (fall (fun n : So tN => fimp (Dsem F tN n) (Bp F B α n)))).
Definition WKLS : Φ :=
  fall (fun B : So LO => fimp (Dsem F LO B) (fimp (TreeS B) (fimp (InfS B) (PathS B)))).

Lemma sv_WKLD : sv WKLD tt ≡ WKLS.
Proof.
  unfold WKLD, WKLS. eapply peq_trans; [apply sv_RA|]. apply (fall_proper F). intros B.
  apply (fimp_proper F); [apply peq_refl|]. eapply peq_trans; [apply sv_Imp|]. apply (fimp_proper F).
  { unfold TreeWD, TreeS. eapply peq_trans; [apply sv_RA|]. apply (fall_proper F). intros α.
    apply (fimp_proper F); [apply peq_refl|]. eapply peq_trans; [apply sv_RA|]. apply (fall_proper F). intros n.
    apply (fimp_proper F); [apply peq_refl|]. eapply peq_trans; [apply sv_Imp|]. apply (fimp_proper F);
      exact (sv_Bp F _ _ _ _). }
  eapply peq_trans; [apply sv_Imp|]. apply (fimp_proper F).
  - unfold InfWD, InfS. eapply peq_trans; [apply sv_RA|]. apply (fall_proper F). intros n.
    apply (fimp_proper F); [apply peq_refl|]. eapply peq_trans; [apply sv_RE|].
    refine (@fex_proper F (pcar (So NN)) _ _ _). intros β.
    apply (fand_proper F); [apply peq_refl|exact (sv_Bp F _ _ _ _)].
  - unfold PathWD, PathS. eapply peq_trans; [apply sv_RE|].
    refine (@fex_proper F (pcar (So NN)) _ _ _). intros α.
    apply (fand_proper F); [apply peq_refl|]. eapply peq_trans; [apply sv_RA|]. apply (fall_proper F). intros n.
    apply (fimp_proper F); [apply peq_refl|exact (sv_Bp F _ _ _ _)].
Qed.

End Sem.

(** ** Décodage des listes *)

Fixpoint dec_list (t : wtree) : list nat :=
  match t with wnode 1 [x] [t'] => x :: dec_list t' | _ => [] end.

Lemma dec_enc l : dec_list (enc l) = l.
Proof. induction l as [|x l IH]; [reflexivity|]. cbn. rewrite IH. reflexivity. Qed.

Lemma pre_S (b : nat -> bool) n : pre b (S n) = pre b n ++ [b n].
Proof. unfold pre. rewrite seq_S, map_app. reflexivity. Qed.

(** ** La réduction *)

Section Reduce.

Context (E : efdata).

Local Notation F := (ef E).
Local Notation So := (So F (Ind := unit)).
Local Notation Φ := (pcar (fprop F)).
Local Notation "⌜ n ⌝" := (code (e := E) n).
Local Notation V a := (pexp punit (So a)).

Context (K : list nat -> Prop) (lw : nat -> nat -> bool).
Context (HK : forall l x, K (l ++ [x]) -> K l).
Context (Hlw : forall n, K (map Nat.b2n (pre (lw n) n))).
Context (HU : exists e, fent ftop e (fall (fun n => fimp ⌜n⌝ (cpath E (lw n))))).

Definition T0 : So LO.
Proof.
  refine (Build_pmor (pprod punit (V tL)) (fprop F) (fun q => fprop_of (F := F) (K (dec_list ((snd q : pmor _ _) tt)))) _).
  intros q q' Eq. cbn in Eq.
  exact (match proj2 Eq tt in _ = z return fprop_of (K (dec_list ((snd q : pmor _ _) tt))) ≡ fprop_of (K (dec_list z))
         with eq_refl => peq_refl _ end).
Defined.

Lemma Bp_T0 α n : Bp F T0 α n = fprop_of (F := F) (K (map Nat.b2n (pre (sgb F α) n))).
Proof. unfold Bp. cbn [pfun T0 snd]. unfold kv, kst. cbn. rewrite dec_enc. reflexivity. Qed.

Lemma K_pre (b : nat -> bool) n : K (map Nat.b2n (pre b (S n))) -> K (map Nat.b2n (pre b n)).
Proof. rewrite pre_S, map_app. apply HK. Qed.

Theorem wkl_reduce :
  (exists e, fent ftop e (sval So (Iy F (dsc := dL)) (ltr (Rel (dsc := dL)) WKL) tt)) ->
  exists e, fent ftop e (fex (fun α : So NN => fand (cpath E (sgb F α))
                               (fall (fun n => fimp ⌜n⌝ (fprop_of (F := F) (K (map Nat.b2n (pre (sgb F α) n)))))))).
Proof.
  intros [e He]. rewrite ltr_WKL in He. apply (fent_eq_r _ _ _ _ (sv_WKLD F)) in He.
  assert (H0 : ENT (fun _ : unit => ftop) (fun _ => WKLS F)) by (exists e; intros _; exact He).
  set (C := fun _ : unit => ftop (F := F)).
  pose proof (ent_inst C (fun _ B => fimp (Dsem F LO B) (fimp (TreeS F B) (fimp (InfS F B) (PathS F B)))) (fun _ => T0) H0) as K1.
  cbv beta in K1.
  (* D_{L→O}(T0) *)
  assert (HD : ENT C (fun _ => Dsem F LO T0)).
  { eapply ent_eq_r; [intros; apply peq_sym, (Dsem_arr F)|].
    apply (ent_gen _ (fun _ (l : So tL) => fimp (Dsem F tL l) (Dsem F tO (pfun T0 (tt, Terms.kv F l))))).
    apply ent_lam. eapply ent_eq_r; [|apply ent_top]. intros; apply peq_refl. }
  (* Tree(T0) *)
  assert (HT : ENT C (fun _ => TreeS F T0)).
  { unfold TreeS. apply (ent_gen _ (fun _ (α : So NN) => fimp (Dsem F NN α) _)). apply ent_lam.
    apply (ent_gen _ (fun p (n : So tN) => fimp (Dsem F tN n) _)). apply ent_lam. apply ent_lam.
    apply (ent_eq_r _ (fun q : (unit * So NN) * So tN => fprop_of (F := F) (K (map Nat.b2n (pre (sgb F (snd (fst q))) (snd q))))));
      [intros q; rewrite Bp_T0; apply peq_refl|].
    eapply ent_trans; [apply ent_snd|].
    apply (ent_eq_l (fun q : (unit * So NN) * So tN => fprop_of (F := F) (K (map Nat.b2n (pre (sgb F (snd (fst q))) (S (snd q)))))));
      [intros q; rewrite Bp_T0; apply peq_refl|].
    apply ent_meta_map. intros q. apply K_pre. }
  (* Inf(T0) *)
  assert (HI : ENT C (fun _ => InfS F T0)).
  { unfold InfS. apply (ent_gen _ (fun _ (n : So tN) => fimp (Dsem F tN n) _)). apply ent_lam.
    set (C2 := fun p : unit * So tN => fand (C (fst p)) (Dsem F tN (snd p))).
    apply (ent_exI C2 _ (fun p => lb E (lw (snd p)))). apply ent_pair.
    - apply cpath_D. destruct HU as [eu Hu].
      assert (KU : ENT C2 (fun _ => fall (fun n => fimp ⌜n⌝ (cpath E (lw n))))).
      { eapply ent_trans; [apply ent_top|]. exists eu. intros _. exact Hu. }
      eapply ent_app; [exact (ent_inst _ (fun _ n => fimp ⌜n⌝ (cpath E (lw n))) snd KU)|].
      apply (D_rz E), ent_snd.
    - apply (ent_eq_r _ (fun p : unit * So tN => fprop_of (F := F) (K (map Nat.b2n (pre (lw (snd p)) (snd p))))));
        [intros p; rewrite Bp_T0, (pre_lb E); apply peq_refl|].
      apply ent_meta_intro. intros p. apply Hlw. }
  pose proof (ent_app _ _ _ (ent_app _ _ _ (ent_app _ _ _ K1 HD) HT) HI) as KP.
  (* ∃α. ⌜α⌝ ∧ ∀n. ⌜n⌝ ⊃ [K(α↾n)] *)
  assert (KF : ENT C (fun _ => fex (fun α : So NN => fand (cpath E (sgb F α))
                 (fall (fun n => fimp ⌜n⌝ (fprop_of (F := F) (K (map Nat.b2n (pre (sgb F α) n))))))))).
  { eapply ent_trans; [exact KP|]. unfold PathS. apply (ex_map E). apply ent_pair.
    - apply (D_cpath E). apply ent_fst.
    - apply (ent_gen _ (fun p n => fimp ⌜n⌝ (fprop_of (F := F) (K (map Nat.b2n (pre (sgb F (snd p)) n)))))). apply ent_lam.
      apply (ent_eq_r _ (fun q : (unit * So NN) * nat => Bp F T0 (snd (fst q)) (snd q))); [intros q; rewrite Bp_T0; apply peq_refl|].
      eapply ent_app.
      + exact (ent_inst _ (fun q (n : So tN) => fimp (Dsem F tN n) (Bp F T0 (snd (fst q)) n)) snd
                 (ent_trans _ _ _ (ent_fst _ _) (ent_snd _ _))).
      + apply (rz_D E), ent_snd. }
  destruct KF as [e' He']. exists e'. exact (He' tt).
Qed.

End Reduce.
