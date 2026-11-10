(** * HA_ω^{ω,ω} avec des listes d'entiers : les termes du théorème de l'éventail

    On instancie la famille de types inductifs par une seule sorte L, les
    listes d'entiers (constructeurs nil et cons). Ce fichier définit les
    termes (récursion primitive de Gödel, plus la récursion sur L pour
    [snoc]) dont la preuve de réalisabilité de FT a besoin, et calcule leur
    valeur dans le modèle de [HA/Model.v] : chaque terme clos s'interprète
    par une fonction méta, qu'on identifie. *)

From Stdlib Require Import List Arith Lia Bool.
Import ListNotations.
From SF.Syntax Require Import Spec Terms Vectors.
From SF.Calculus Require Import System Rules.
From SF.Logic Require Import Judgment Propositional.
From SF.Functional Require Import Arrow Graded.
From SF.Quantifiers Require Import Quant Order.
From SF.Arithmetic Require Import Arith Inductive.
From SF.Models Require Import PSet Frame Semantics Tarski FrameTarski.
From SF.HA Require Import Signature Model.
From SF.Fan Require Import Bounded Statement Meta.

Set Universe Polymorphism.

Local Notation ι a := (Spec [] a).

(** ** La signature *)

Definition dL : unit -> list (list bool) := fun _ => [[]; [true; false]].

Notation T := (ty unit).
Notation tL := (@tW unit tt).
Notation hL := (hsym dL).
Local Notation tm := (Terms.tm hL).
Notation NN := (tarr tN tN).

Definition rok (s : T) (h : snd (tgr s) = 0) : rec_ok (Sym := hL) omega s := conj I h.

Definition ap {Γ} {a b : T} (f : tm Γ (tarr a b)) (u : tm Γ a) : tm Γ b := App (w_ab a b) f u.
Definition lam {Γ} {a b : T} (t : tm (ι a :: Γ) b) : tm Γ (tarr a b) := Lam (w_ab a b) t.
Definition recN {Γ} (s : T) (h : snd (tgr s) = 0) (z : tm Γ s) (st : tm (ι tN :: ι s :: Γ) s) (n : tm Γ tN) : tm Γ s :=
  Rec s (rok s h) z st n.

Notation v0 := (var0 vz).
Notation v1 := (var0 (vs vz)).
Notation v2 := (var0 (vs (vs vz))).
Notation v3 := (var0 (vs (vs (vs vz)))).
Notation one := (Succ Zero).

Definition Nil {Γ} : tm Γ tL := Con (dsc := dL) tt [] mz anil.
Definition Cons {Γ} (x : tm Γ tN) (l : tm Γ tL) : tm Γ tL :=
  Con (dsc := dL) tt [true; false] (ms mz) (@acons _ hL Γ (ι tN) _ x (@acons _ hL Γ (ι tL) _ l anil)).

(** ** Arithmétique *)

Definition sgt {Γ} : tm Γ NN := lam (recN tN eq_refl Zero one v0).
Definition iszt {Γ} : tm Γ NN := lam (recN tN eq_refl one Zero v0).
Definition predt {Γ} : tm Γ NN := lam (recN tN eq_refl Zero v0 v0).
(** add x y, sub x y, and x y (y si x ≠ 0, 0 sinon) *)
Definition addt {Γ} : tm Γ (tarr tN NN) := lam (lam (recN tN eq_refl v1 (Succ v1) v0)).
Definition subt {Γ} : tm Γ (tarr tN NN) := lam (lam (recN tN eq_refl v1 (ap predt v1) v0)).
Definition andt {Γ} : tm Γ (tarr tN NN) := lam (lam (recN tN eq_refl Zero v2 v1)).
Definition ort {Γ} : tm Γ (tarr tN NN) := lam (lam (ap sgt (ap (ap addt v1) v0))).
(** leb x y = 1 si x ≤ y ; ltb x y = 1 si x < y *)
Definition lebt {Γ} : tm Γ (tarr tN NN) := lam (lam (ap iszt (ap (ap subt v1) v0))).
Definition ltbt {Γ} : tm Γ (tarr tN NN) := lam (lam (ap (ap lebt (Succ v1)) v0)).

(** odd n, div2 n, testbit k i, 2ⁿ *)
Definition oddt {Γ} : tm Γ NN := lam (recN tN eq_refl Zero (ap iszt v1) v0).
Definition div2t {Γ} : tm Γ NN := lam (recN tN eq_refl Zero (ap (ap addt v1) (ap oddt v0)) v0).
Definition testbitt {Γ} : tm Γ (tarr tN NN) := lam (lam (ap oddt (recN tN eq_refl v1 (ap div2t v1) v0))).
Definition pow2t {Γ} : tm Γ NN := lam (recN tN eq_refl one (ap (ap addt v1) v1) v0).

(** ite c x y = x si c ≠ 0, y sinon *)
Definition ite {Γ} (c x y : tm Γ tN) : tm Γ tN :=
  recN tN eq_refl y (Terms.ren_tm x (wk [ι tN; ι tN])) c.

(** Quantificateurs bornés et recherche bornée : ball N P, bex N P, blast N P. *)
Notation NNN := (tarr NN tN).
Definition ballt {Γ} : tm Γ (tarr tN NNN) :=
  lam (lam (recN tN eq_refl one (ap (ap andt v1) (ap v2 v0)) v1)).
Definition bext {Γ} : tm Γ (tarr tN NNN) :=
  lam (lam (recN tN eq_refl Zero (ap (ap ort v1) (ap v2 v0)) v1)).
Definition blastt {Γ} : tm Γ (tarr tN NNN) :=
  lam (lam (recN tN eq_refl Zero (ite (ap v2 v0) v0 v1) v1)).

(** path k j := λi. (i < j) ∧ bit_i(k) ; trunc α j := λi. (i < j) ∧ sg(α i) *)
Definition patht {Γ} : tm Γ (tarr tN (tarr tN NN)) :=
  lam (lam (lam (ap (ap andt (ap (ap ltbt v0) v1)) (ap (ap testbitt v2) v0)))).
Definition trunct {Γ} : tm Γ (tarr NN (tarr tN NN)) :=
  lam (lam (lam (ap (ap andt (ap (ap ltbt v0) v1)) (ap sgt (ap v2 v0))))).

Notation FF := (tarr NN tN).
(** cp G n = 1 ssi tout mot k < 2ⁿ a un préfixe j ≤ n avec G(path k j) ≤ j. *)
Definition cpt {Γ} : tm Γ (tarr FF NN) :=
  lam (lam (ap (ap ballt (ap pow2t v0))
              (lam (ap (ap bext (Succ v1)) (lam (ap (ap lebt (ap v3 (ap (ap patht v1) v0))) v0)))))).
(** jst G α n : un j ≤ n tel que G(trunc α j) ≤ j. *)
Definition jstt {Γ} : tm Γ (tarr FF (tarr NN NN)) :=
  lam (lam (lam (ap (ap blastt (Succ v0)) (lam (ap (ap lebt (ap v3 (ap (ap trunct v2) v0))) v0))))).

(** snoc l x (par récursion sur L) et pre α n = [sg(α 0); …; sg(α (n-1))]. *)
Definition snoct {Γ} : tm Γ (tarr tL (tarr tN tL)) :=
  lam (lam (WRec tt tL (rok tL eq_refl) v1
              (@acons _ hL _ (Spec [] tL) _ (Cons v0 Nil)
                 (@acons _ hL _ (Spec [ι tN; ι tL; ι tL] tL) _ (Cons v0 v2) anil)))).
Definition pret {Γ} : tm Γ (tarr NN (tarr tN tL)) :=
  lam (lam (recN tL eq_refl Nil (ap (ap snoct v1) (ap sgt (ap v3 v0))) v0)).

Section Sem.
Context (F : frame).
Local Notation So := (So F (Ind := unit)).
Local Notation sv := (sval So (Iy F (dsc := dL))).

Definition kn (x : nat) : pexp punit (So tN) := kst F (Ind := unit) (s := tN) x.
(** Application d'une valeur fonctionnelle à un entier. *)
Notation ev f x := (pfun f (tt, kn x)).
Notation ev1 f x := (pfun f (tt, kn x)).
Notation ev2 f x y := (pfun (pfun f (tt, kn x)) (tt, kn y)).

Definition sgf (x : nat) : nat := match x with 0 => 0 | _ => 1 end.

Lemma sg_sem Γ γ x : ev1 (sv (sgt (Γ := Γ)) γ) x = sgf x.
Proof. destruct x; reflexivity. Qed.

Lemma isz_sem Γ γ x : ev1 (sv (iszt (Γ := Γ)) γ) x = Nat.b2n (x =? 0).
Proof. destruct x; reflexivity. Qed.

Lemma pred_sem Γ γ x : ev1 (sv (predt (Γ := Γ)) γ) x = Nat.pred x.
Proof. destruct x; reflexivity. Qed.

Lemma add_sem Γ γ x y : ev2 (sv (addt (Γ := Γ)) γ) x y = x + y.
Proof.
  cbn.
  lazymatch goal with |- nat_rect ?P ?z ?st y = _ =>
    assert (H : forall m, nat_rect P z st m = x + m) by (induction m as [|m IH]; cbn in *; lia) end.
  apply H.
Qed.

Definition andf (a b : nat) : nat := match a with 0 => 0 | _ => b end.

(** *** Valeurs des constructions de termes *)

Local Notation ictx := (ictx PSet So).
Local Notation V a := (pexp punit (So a)).
Definition kv {a : T} (x : So a) : V a := kst F (Ind := unit) x.

Lemma sv_lam {Γ} {a b : T} (t : tm (ι a :: Γ) b) (γ : ictx Γ) (v : V a) :
  (sv (lam t) γ : pmor _ _) (tt, v) ≡ sv t (γ, v).
Proof.
  set (h := Build_pmor (pprod (ictx Γ) (pprod punit (V a))) (pprod (ictx Γ) (V a))
              (fun q : pcar (pprod (ictx Γ) (pprod punit (V a))) => (fst q, snd (snd q)))
              (fun q q' E => conj (proj1 E) (proj2 (proj2 E)))).
  assert (He : env_eq PSet So (ext PSet So [ι a] (penv PSet So Γ)) (env_comp PSet So (penv PSet So (ι a :: Γ)) h)).
  { refine (var_inv _ _ _); [|intros σ y]; intros q; apply peq_refl. }
  pose proof (stm_ext PSet So (Iy F (dsc := dL)) t _ _ He (γ, (tt, v))) as E1.
  pose proof (stm_nat PSet So (Iy F (dsc := dL)) t (penv PSet So _) h (γ, (tt, v))) as E2.
  exact (peq_trans E1 (peq_sym E2)).
Qed.

Lemma sv_ap {Γ} {a b : T} (f : tm Γ (tarr a b)) (u : tm Γ a) (γ : ictx Γ) :
  sv (ap f u) γ ≡ (sv f γ : pmor _ _) (tt, kv (sv u γ)).
Proof.
  change ((stms PSet So (Iy F (dsc := dL)) (σ := ι (tarr a b)) f (penv PSet So Γ) γ tt : pmor _ _)
            (tt, stms PSet So (Iy F (dsc := dL)) (σ := ι a) u (penv PSet So Γ) γ)
          ≡ (sv f γ : pmor _ _) (tt, kv (sv u γ))).
  eapply peq_trans; [exact (stms0_at F (b := tarr a b) f γ tt _)|].
  apply pfun_proper. split; [exact I|]. intros t. exact (stms0_at F (b := a) u γ t).
Qed.

Lemma sv_v0 {Γ} {a : T} (γ : ictx Γ) (v : V a) : sv (var0 (Sym := hL) (@vz T Γ (ι a))) (γ, v) ≡ (v : pmor _ _) tt.
Proof. apply peq_refl. Qed.

Lemma sv_v1 {Γ} {a b : T} (γ : ictx Γ) (v : V a) (w : V b) :
  sv (var0 (Sym := hL) (vs (τ := ι b) (@vz T Γ (ι a)))) (γ, v, w) ≡ (v : pmor _ _) tt.
Proof. apply peq_refl. Qed.

Lemma sv_v2 {Γ} {a b c : T} (γ : ictx Γ) (v : V a) (w : V b) (x : V c) :
  sv (var0 (Sym := hL) (vs (τ := ι c) (vs (τ := ι b) (@vz T Γ (ι a))))) (γ, v, w, x) ≡ (v : pmor _ _) tt.
Proof. apply peq_refl. Qed.

(** Un corps sous deux lieurs, évalué. *)
Lemma stms_at2 {Γ} {a b c : T} (t : tm (ι a :: ι b :: Γ) c) (γ : ictx Γ) (v : V b) (w : V a) :
  (stms PSet So (Iy F (dsc := dL)) (σ := Spec [ι a; ι b] c) t (penv PSet So Γ) γ : pmor _ _) (tt, v, w)
  ≡ sv t (γ, v, w).
Proof.
  set (h := Build_pmor (pprod (ictx Γ) (pprod (pprod punit (V b)) (V a))) (pprod (pprod (ictx Γ) (V b)) (V a))
              (fun q : pcar (pprod (ictx Γ) (pprod (pprod punit (V b)) (V a))) => (fst q, snd (fst (snd q)), snd (snd q)))
              (fun q q' E => conj (conj (proj1 E) (proj2 (proj1 (proj2 E)))) (proj2 (proj2 E)))).
  assert (He : env_eq PSet So (ext PSet So [ι a; ι b] (penv PSet So Γ)) (env_comp PSet So (penv PSet So (ι a :: ι b :: Γ)) h)).
  { refine (var_inv _ _ _); [|refine (var_inv _ _ _); [|intros σ y]]; intros q; apply peq_refl. }
  pose proof (stm_ext PSet So (Iy F (dsc := dL)) t _ _ He (γ, (tt, v, w))) as E1.
  pose proof (stm_nat PSet So (Iy F (dsc := dL)) t (penv PSet So _) h (γ, (tt, v, w))) as E2.
  exact (peq_trans E1 (peq_sym E2)).
Qed.

Lemma sv_rec {Γ} (s : T) h (z : tm Γ s) (st : tm (ι tN :: ι s :: Γ) s) (n : tm Γ tN) (γ : ictx Γ) :
  sv (recN s h z st n) γ
  ≡ nat_rect (fun _ => pcar (So s)) (sv z γ) (fun k acc => sv st (γ, kv acc, kn k)) (sv n γ).
Proof.
  change (rec_val F s (stms PSet So (Iy F (dsc := dL)) (σ := ι s) z (penv PSet So Γ) γ tt)
            (stms PSet So (Iy F (dsc := dL)) (σ := Spec [ι tN; ι s] s) st (penv PSet So Γ) γ)
            (stms PSet So (Iy F (dsc := dL)) (σ := ι tN) n (penv PSet So Γ) γ tt)
          ≡ nat_rect (fun _ => pcar (So s)) (sv z γ) (fun k acc => sv st (γ, kv acc, kn k)) (sv n γ)).
  rewrite (stms0_at F (b := tN) n γ tt). unfold rec_val.
  apply nat_rect_ext'; [exact (stms0_at F (b := s) z γ tt)|].
  intros k x x' E. eapply peq_trans; [|exact (stms_at2 st γ (kv x') (kn k))].
  apply pfun_proper. split; [split; [exact I|intros t; exact E]|intros t; apply peq_refl].
Qed.


Lemma sub_sem Γ γ x y : ev2 (sv (subt (Γ := Γ)) γ) x y = x - y.
Proof.
  cbn.
  lazymatch goal with |- nat_rect ?P ?z ?st y = _ =>
    assert (H : forall m, nat_rect P z st m = x - m) by (induction m as [|m IH]; cbn in *; [lia|rewrite IH; destruct (x - m) eqn:E; cbn; lia]) end.
  apply H.
Qed.

Lemma and_sem Γ γ x y : ev2 (sv (andt (Γ := Γ)) γ) x y = andf x y.
Proof. destruct x; reflexivity. Qed.

Lemma or_sem Γ γ x y : ev2 (sv (ort (Γ := Γ)) γ) x y = sgf (x + y).
Proof.
  cbn -[Nat.add].
  pose proof (add_sem (ι tN :: ι tN :: Γ) (γ, kn x, kn y) x y) as E. 
  cbn -[Nat.add] in E. rewrite E. destruct (x + y); reflexivity.
Qed.

Lemma sv_wk2 {Γ} {a b c : T} (x : tm Γ c) (γ : ictx Γ) (v : V a) (w : V b) :
  sv (Terms.ren_tm x (wk [ι b; ι a])) (γ, v, w) ≡ sv x γ.
Proof.
  set (h := Build_pmor (pprod (pprod (ictx Γ) (V a)) (V b)) (ictx Γ) (fun q => fst (fst q))
              (fun q q' E => proj1 (proj1 E))).
  assert (He : env_eq PSet So (env_ren PSet So (wk [ι b; ι a]) (penv PSet So (ι b :: ι a :: Γ)))
                 (env_comp PSet So (penv PSet So Γ) h)) by (intros σ y q; apply peq_refl).
  pose proof (stm_ren PSet So (Iy F (dsc := dL)) x (wk [ι b; ι a]) (penv PSet So _) (γ, v, w)) as E0.
  pose proof (stm_ext PSet So (Iy F (dsc := dL)) x _ _ He (γ, v, w)) as E1.
  pose proof (stm_nat PSet So (Iy F (dsc := dL)) x (penv PSet So _) h (γ, v, w)) as E2.
  exact (peq_trans E0 (peq_trans E1 (peq_sym E2))).
Qed.

(** Application à un argument quelconque. *)
Notation evs f v := (pfun f (tt, kv v)).

Lemma evs_proper {a b : T} (f f' : So (tarr a b)) (v v' : So a) : f ≡ f' -> v ≡ v' -> evs f v ≡ evs f' v'.
Proof.
  intros Ef Ev. eapply peq_trans; [exact (Ef (tt, kv v))|]. apply pfun_proper. split; [exact I|intros t; exact Ev].
Qed.

Lemma sv_ap' {Γ} {a b : T} (f : tm Γ (tarr a b)) (u : tm Γ a) (γ : ictx Γ) :
  sv (ap f u) γ ≡ evs (sv f γ) (sv u γ).
Proof. exact (sv_ap f u γ). Qed.

Lemma sv_lam' {Γ} {a b : T} (t : tm (ι a :: Γ) b) (γ : ictx Γ) (x : So a) :
  evs (sv (lam t) γ) x ≡ sv t (γ, kv x).
Proof. exact (sv_lam t γ (kv x)). Qed.

(** Les valeurs entières : ≡ est l'égalité. *)
Lemma evN_eq {a : T} (f f' : So (tarr a tN)) (v v' : So a) : f ≡ f' -> v ≡ v' -> evs f v = evs f' v'.
Proof. intros Ef Ev. exact (evs_proper f f' v v' Ef Ev). Qed.


Lemma sv_recN {Γ} h (z : tm Γ tN) (st : tm (ι tN :: ι tN :: Γ) tN) (n : tm Γ tN) (γ : ictx Γ) :
  sv (recN tN h z st n) γ = nat_rect (fun _ => pcar (So tN)) (sv z γ) (fun k acc => sv st (γ, kv acc, kn k)) (sv n γ).
Proof. exact (sv_rec tN h z st n γ). Qed.

Definition oddf (n : nat) : nat := Nat.b2n (Nat.odd n).

Lemma ite_sem {Γ} (c x y : tm Γ tN) (γ : ictx Γ) :
  sv (ite c x y) γ = match sv c γ with 0 => sv y γ | _ => sv x γ end.
Proof.
  unfold ite. rewrite sv_recN. destruct (sv c γ) as [|k]; [reflexivity|]. cbn [nat_rect].
  exact (sv_wk2 x γ _ _).
Qed.

Lemma sv_apN {Γ} (f : tm Γ NN) (u : tm Γ tN) (γ : ictx Γ) : sv (ap f u) γ = ev1 (sv f γ) (sv u γ).
Proof. exact (sv_ap f u γ). Qed.

Lemma sv_ap2N {Γ} (f : tm Γ (tarr tN NN)) (u w : tm Γ tN) (γ : ictx Γ) :
  sv (ap (ap f u) w) γ = ev2 (sv f γ) (sv u γ) (sv w γ).
Proof.
  exact (peq_trans (sv_ap (ap f u) w γ) (sv_ap f u γ (tt, kv (sv w γ)))).
Qed.

Lemma ev1_lam {Γ} (B : tm (ι tN :: Γ) tN) (γ : ictx Γ) x : ev1 (sv (lam B) γ) x = sv B (γ, kn x).
Proof. exact (sv_lam B γ (kn x)). Qed.

Lemma ev2_lam {Γ} (B : tm (ι tN :: ι tN :: Γ) tN) (γ : ictx Γ) x y :
  ev2 (sv (lam (lam B)) γ) x y = sv B (γ, kn x, kn y).
Proof. exact (peq_trans ((sv_lam (lam B) γ (kn x)) (tt, kn y)) (sv_lam B (γ, kn x) (kn y))). Qed.

Lemma sv_v1N {Γ} (γ : ictx Γ) (a k : nat) :
  sv (var0 (Sym := hL) (vs (τ := ι tN) (@vz T Γ (ι tN)))) (γ, kv (a := tN) a, kn k) = a.
Proof. reflexivity. Qed.

Lemma sv_v0N {Γ} (γ : ictx Γ) (k : nat) : sv (var0 (Sym := hL) (@vz T Γ (ι tN))) (γ, kn k) = k.
Proof. reflexivity. Qed.

(** Évaluer les variables dans un environnement explicite. *)
Ltac svvar :=
  repeat match goal with |- context [sval ?So ?Iy (var0 ?x) ?env] =>
    let t := eval cbn in (sval So Iy (var0 x) env) in change (sval So Iy (var0 x) env) with t
  end.

Ltac natgen' f :=
  lazymatch goal with |- context [nat_rect ?P ?z ?st ?n] =>
    let H := fresh "H" in let m := fresh "m" in
    assert (H : forall m, nat_rect P z st m = f m); [intros m; induction m; cbn [nat_rect]|rewrite H]
  end.

Ltac natgen f :=
  lazymatch goal with |- nat_rect ?P ?z ?st ?n = _ =>
    let H := fresh "H" in let m := fresh "m" in
    assert (H : forall m, nat_rect P z st m = f m); [intros m; induction m; cbn [nat_rect]|rewrite H; reflexivity]
  end.

Lemma odd_sem Γ γ x : ev1 (sv (oddt (Γ := Γ)) γ) x = oddf x.
Proof.
  unfold oddt. rewrite ev1_lam, sv_recN. set (e := (γ, kn x)).
  natgen oddf; [reflexivity|]. rewrite sv_apN, isz_sem, sv_v1N, IHm.
  unfold oddf. rewrite Nat.odd_succ, <- Nat.negb_odd. destruct (Nat.odd m); reflexivity.
Qed.

Lemma div2_sem Γ γ x : ev1 (sv (div2t (Γ := Γ)) γ) x = Nat.div2 x.
Proof.
  unfold div2t. rewrite ev1_lam, sv_recN. set (e := (γ, kn x)).
  natgen Nat.div2; [reflexivity|]. rewrite sv_ap2N, add_sem, sv_apN, odd_sem, IHm. svvar.
  unfold oddf. clear. induction m as [m IH] using lt_wf_ind. destruct m as [|[|m]]; [reflexivity|reflexivity|].
  cbn [Nat.div2]. rewrite Nat.odd_succ_succ. specialize (IH m ltac:(lia)). cbn [Nat.div2] in *. lia.
Qed.

Definition testbitf (k i : nat) : nat := Nat.b2n (Nat.testbit k i).

Lemma testbit_sem Γ γ k i : ev2 (sv (testbitt (Γ := Γ)) γ) k i = testbitf k i.
Proof.
  unfold testbitt. rewrite ev2_lam, sv_apN, odd_sem, sv_recN.
  natgen' (fun m => Nat.iter m Nat.div2 k); [reflexivity|rewrite sv_apN, div2_sem, IHm; reflexivity|].
  svvar. unfold testbitf, oddf. f_equal. clear.
  assert (Hc : forall j x, Nat.iter j Nat.div2 (Nat.div2 x) = Nat.div2 (Nat.iter j Nat.div2 x)).
  { induction j as [|j IH]; intros x; [reflexivity|]. rewrite !Nat.iter_succ, IH. reflexivity. }
  revert k. induction i as [|i IH]; intros k; [reflexivity|].
  cbn [Nat.testbit]. rewrite <- IH, Hc. reflexivity.
Qed.

Lemma pow2_sem Γ γ n : ev1 (sv (pow2t (Γ := Γ)) γ) n = 2 ^ n.
Proof.
  unfold pow2t. rewrite ev1_lam, sv_recN. set (e := (γ, kn n)).
  natgen (fun m => 2 ^ m); [reflexivity|]. rewrite sv_ap2N, add_sem, sv_v1N, IHm. cbn. lia.
Qed.

Lemma leb_sem Γ γ x y : ev2 (sv (lebt (Γ := Γ)) γ) x y = Nat.b2n (x <=? y).
Proof.
  unfold lebt. rewrite ev2_lam, sv_apN, isz_sem, sv_ap2N, sub_sem. svvar.
  destruct (Nat.leb_spec x y); [replace (x - y) with 0 by lia; reflexivity|].
  destruct (x - y) eqn:E; [lia|reflexivity].
Qed.

Lemma ltb_sem Γ γ x y : ev2 (sv (ltbt (Γ := Γ)) γ) x y = Nat.b2n (x <? y).
Proof.
  unfold ltbt. rewrite ev2_lam, sv_ap2N, leb_sem. reflexivity.
Qed.

(** *** Fonctions en argument *)

Definition pmN (g : nat -> nat) : So NN :=
  Build_pmor (pprod punit (V tN)) (disc nat) (fun q => g ((snd q : pmor _ _) tt))
    (fun q q' E => f_equal g (proj2 E tt)).

Lemma pm_at (f : So NN) (q : pcar (pprod punit (V tN))) : (f : pmor _ _) q = ev1 f ((snd q : pmor _ _) tt).
Proof.
  exact (pfun_proper (f : pmor (pprod punit (V tN)) (disc nat)) (x := q) (x' := (tt, kn ((snd q : pmor _ _) tt)))
           (conj I (fun t => match t with tt => eq_refl end))).
Qed.

Lemma pmN_eq (f : So NN) (g : nat -> nat) : (forall i, ev1 f i = g i) -> f ≡ pmN g.
Proof. intros H q. rewrite pm_at. apply H. Qed.

Lemma evF_lam {Γ} {a : T} (B : tm (ι a :: ι tN :: Γ) tN) (γ : ictx Γ) n (x : So a) :
  evs (ev (sv (lam (lam B)) γ) n) x = sv B (γ, kn n, kv x).
Proof. exact (peq_trans ((sv_lam (lam B) γ (kn n)) (tt, kv x)) (sv_lam B (γ, kn n) (kv x))). Qed.

Lemma evF_lam' {Γ} {a : T} (B : tm (ι tN :: ι a :: Γ) tN) (γ : ictx Γ) (x : So a) n :
  ev1 (evs (sv (lam (lam B)) γ) x) n = sv B (γ, kv x, kn n).
Proof. exact (peq_trans ((sv_lam (lam B) γ (kv x)) (tt, kn n)) (sv_lam B (γ, kv x) (kn n))). Qed.

Lemma ev3_lam {Γ} {a : T} (B : tm (ι tN :: ι tN :: ι a :: Γ) tN) (γ : ictx Γ) (x : So a) j i :
  ev1 (ev (evs (sv (lam (lam (lam B))) γ) x) j) i = sv B (γ, kv x, kn j, kn i).
Proof.
  
  exact (peq_trans (((sv_lam (lam (lam B)) γ (kv x)) (tt, kn j)) (tt, kn i))
           (peq_trans ((sv_lam (lam B) (γ, kv x) (kn j)) (tt, kn i)) (sv_lam B (γ, kv x, kn j) (kn i)))).
Qed.

Lemma ev3_lamN {Γ} (B : tm (ι tN :: ι tN :: ι tN :: Γ) tN) (γ : ictx Γ) k j i :
  ev1 (ev (ev (sv (lam (lam (lam B))) γ) k) j) i = sv B (γ, kn k, kn j, kn i).
Proof.
  
  exact (peq_trans (((sv_lam (lam (lam B)) γ (kn k)) (tt, kn j)) (tt, kn i))
           (peq_trans ((sv_lam (lam B) (γ, kn k) (kn j)) (tt, kn i)) (sv_lam B (γ, kn k, kn j) (kn i)))).
Qed.

Lemma sv_apF {Γ} {a : T} (f : tm Γ (tarr tN (tarr a tN))) (u : tm Γ tN) (w : tm Γ a) (γ : ictx Γ) :
  sv (ap (ap f u) w) γ = evs (ev (sv f γ) (sv u γ)) (sv w γ).
Proof. exact (peq_trans (sv_ap (ap f u) w γ) (sv_ap f u γ (tt, kv (sv w γ)))). Qed.

Lemma sv_apS {Γ} {a : T} (f : tm Γ (tarr a tN)) (u : tm Γ a) (γ : ictx Γ) :
  sv (ap f u) γ = evs (sv f γ) (sv u γ).
Proof. exact (sv_ap f u γ). Qed.

Definition ballf N (p : nat -> nat) : nat := nat_rect (fun _ => nat) 1 (fun k a => andf a (p k)) N.
Definition bexf N (p : nat -> nat) : nat := nat_rect (fun _ => nat) 0 (fun k a => sgf (a + p k)) N.
Definition blastf N (p : nat -> nat) : nat := nat_rect (fun _ => nat) 0 (fun k a => match p k with 0 => a | _ => k end) N.

Lemma ball_sem Γ γ N (P : So NN) : evs (ev (sv (ballt (Γ := Γ)) γ) N) P = ballf N (fun k => ev1 P k).
Proof.
  unfold ballt. rewrite evF_lam, sv_recN.
  natgen' (fun m => ballf m (fun k => ev1 P k)); [reflexivity|rewrite sv_ap2N, and_sem, sv_apN, IHm; svvar; reflexivity|].
  svvar. reflexivity.
Qed.

Lemma bex_sem Γ γ N (P : So NN) : evs (ev (sv (bext (Γ := Γ)) γ) N) P = bexf N (fun k => ev1 P k).
Proof.
  unfold bext. rewrite evF_lam, sv_recN.
  natgen' (fun m => bexf m (fun k => ev1 P k)); [reflexivity|rewrite sv_ap2N, or_sem, sv_apN, IHm; svvar; reflexivity|].
  svvar. reflexivity.
Qed.

Lemma blast_sem Γ γ N (P : So NN) : evs (ev (sv (blastt (Γ := Γ)) γ) N) P = blastf N (fun k => ev1 P k).
Proof.
  unfold blastt. rewrite evF_lam, sv_recN.
  natgen' (fun m => blastf m (fun k => ev1 P k)); [reflexivity|rewrite ite_sem, sv_apN, IHm; svvar; reflexivity|].
  svvar. reflexivity.
Qed.

Lemma ballf_spec N p q : (forall k, p k = Nat.b2n (q k)) -> ballf N p = Nat.b2n (ball N q).
Proof.
  intros H. induction N as [|N IH]; [reflexivity|].
  change (andf (ballf N p) (p N) = Nat.b2n (ball N q && q N)). rewrite IH, H. destruct (ball N q), (q N); reflexivity.
Qed.

Lemma bexf_spec N p q : (forall k, p k = Nat.b2n (q k)) -> bexf N p = Nat.b2n (bex N q).
Proof.
  intros H. induction N as [|N IH]; [reflexivity|].
  change (sgf (bexf N p + p N) = Nat.b2n (bex N q || q N)). rewrite IH, H. destruct (bex N q), (q N); reflexivity.
Qed.

Lemma blastf_spec N p q : (forall k, p k = Nat.b2n (q k)) -> blastf N p = blast N q.
Proof.
  intros H. induction N as [|N IH]; [reflexivity|].
  change (match p N with 0 => blastf N p | _ => N end = if q N then N else blast N q). rewrite IH, H. destruct (q N); reflexivity.
Qed.

Definition pathf (k j : nat) : nat -> bool := fun i => (i <? j) && Nat.testbit k i.
Definition truncf (α : nat -> nat) (j : nat) : nat -> bool := fun i => (i <? j) && negb (α i =? 0).

Lemma andf_b2n a b : andf (Nat.b2n a) (Nat.b2n b) = Nat.b2n (a && b).
Proof. destruct a, b; reflexivity. Qed.

Lemma path_sem Γ γ k j i : ev1 (ev (ev (sv (patht (Γ := Γ)) γ) k) j) i = Nat.b2n (pathf k j i).
Proof.
  unfold patht. rewrite ev3_lamN, sv_ap2N, and_sem, !sv_ap2N, ltb_sem, testbit_sem. svvar.
  unfold testbitf. apply andf_b2n.
Qed.

Lemma trunc_sem Γ γ (α : So NN) j i :
  ev1 (ev (evs (sv (trunct (Γ := Γ)) γ) α) j) i = Nat.b2n (truncf (fun k => ev1 α k) j i).
Proof.
  unfold trunct. rewrite ev3_lam, sv_ap2N, and_sem, sv_ap2N, ltb_sem, sv_apN, sg_sem, sv_apN. svvar.
  unfold truncf. rewrite <- andf_b2n. f_equal. destruct (ev1 α i); reflexivity.
Qed.

Lemma sv_ap2NN {Γ} {a : T} (f : tm Γ (tarr a (tarr tN NN))) (u : tm Γ a) (w : tm Γ tN) (γ : ictx Γ) :
  sv (ap (ap f u) w) γ ≡ ev (evs (sv f γ) (sv u γ)) (sv w γ).
Proof. exact (fun q => peq_trans (sv_ap (ap f u) w γ q) (sv_ap f u γ (tt, kv (sv w γ)) q)). Qed.

Lemma sv_ap2NN_N {Γ} (f : tm Γ (tarr tN (tarr tN NN))) (u w : tm Γ tN) (γ : ictx Γ) :
  sv (ap (ap f u) w) γ ≡ ev (ev (sv f γ) (sv u γ)) (sv w γ).
Proof. exact (fun q => peq_trans (sv_ap (ap f u) w γ q) (sv_ap f u γ (tt, kv (sv w γ)) q)). Qed.

Lemma path_ap {Γ} (u w : tm Γ tN) (e : ictx Γ) i :
  ev1 (sv (ap (ap patht u) w) e) i = Nat.b2n (pathf (sv u e) (sv w e) i).
Proof.
  assert (E1 : ev1 (sv (ap (ap patht u) w) e) i = ev2 (ev1 (sv patht e) (sv u e)) (sv w e) i)
    by exact (sv_ap2NN_N patht u w e (tt, kn i)).
  rewrite E1. exact (path_sem _ e (sv u e) (sv w e) i).
Qed.

(** La fonctionnelle G, sur les chemins booléens. *)
Definition Gb (G : So FF) (b : nat -> bool) : nat := evs G (pmN (fun i => Nat.b2n (b i))).

Lemma Gb_eq (G : So FF) (f : So NN) (b : nat -> bool) :
  (forall i, ev1 f i = Nat.b2n (b i)) -> evs G f = Gb G b.
Proof. intros H. apply evN_eq; [apply peq_refl|apply pmN_eq, H]. Qed.

Lemma cp_sem Γ γ (G : So FF) n : ev1 (evs (sv (cpt (Γ := Γ)) γ) G) n = Nat.b2n (Cp (Gb G) n).
Proof.
  unfold cpt. rewrite evF_lam', (sv_apF (a := NN)), ball_sem, sv_apN, pow2_sem. svvar.
  unfold Cp. apply ballf_spec. intros k. rewrite ev1_lam, (sv_apF (a := NN)), bex_sem. svvar.
  change (sv (Succ v1) _) with (S n). apply bexf_spec. intros j. rewrite ev1_lam, sv_ap2N, leb_sem. svvar.
  unfold Pk. do 2 f_equal. rewrite sv_apS. svvar. apply Gb_eq. intros i.
  rewrite path_ap. svvar. reflexivity.
Qed.

Lemma sv_ap2NN_F {Γ} (f : tm Γ (tarr NN (tarr tN NN))) (u : tm Γ NN) (w : tm Γ tN) (γ : ictx Γ) :
  sv (ap (ap f u) w) γ ≡ ev (evs (sv f γ) (sv u γ)) (sv w γ).
Proof. exact (fun q => peq_trans (sv_ap (ap f u) w γ q) (sv_ap f u γ (tt, kv (sv w γ)) q)). Qed.

Lemma trunc_ap {Γ} (u : tm Γ NN) (w : tm Γ tN) (e : ictx Γ) i :
  ev1 (sv (ap (ap trunct u) w) e) i = Nat.b2n (truncf (fun k => ev1 (sv u e) k) (sv w e) i).
Proof.
  assert (E1 : ev1 (sv (ap (ap trunct u) w) e) i = ev1 (ev (evs (sv trunct e) (sv u e)) (sv w e)) i)
    by exact (sv_ap2NN_F trunct u w e (tt, kn i)).
  rewrite E1. exact (trunc_sem _ e (sv u e) (sv w e) i).
Qed.

Lemma ev3_lamG {Γ} (B : tm (ι tN :: ι NN :: ι FF :: Γ) tN) (γ : ictx Γ) (G : So FF) (α : So NN) n :
  ev1 (evs (evs (sv (lam (lam (lam B))) γ) G) α) n = sv B (γ, kv G, kv α, kn n).
Proof.
  exact (peq_trans (((sv_lam (lam (lam B)) γ (kv G)) (tt, kv α)) (tt, kn n))
           (peq_trans ((sv_lam (lam B) (γ, kv G) (kv α)) (tt, kn n)) (sv_lam B (γ, kv G, kv α) (kn n)))).
Qed.

Lemma jst_sem Γ γ (G : So FF) (α : So NN) n :
  ev1 (evs (evs (sv (jstt (Γ := Γ)) γ) G) α) n
  = blast (S n) (fun j => Gb G (truncf (fun k => ev1 α k) j) <=? j).
Proof.
  unfold jstt. rewrite ev3_lamG, (sv_apF (a := NN)), blast_sem. svvar.
  change (sv (Succ v0) _) with (S n). apply blastf_spec. intros j. rewrite ev1_lam, sv_ap2N, leb_sem. svvar.
  do 2 f_equal. rewrite sv_apS. svvar. apply Gb_eq. intros i. rewrite trunc_ap. svvar. reflexivity.
Qed.

(** *** Listes *)

Fixpoint enc (l : list nat) : wtree :=
  match l with [] => wnode 0 [] [] | x :: l => wnode 1 [x] [enc l] end.

Lemma ev2_lamL {Γ} (B : tm (ι tN :: ι tL :: Γ) tL) (γ : ictx Γ) (l : So tL) x :
  ev (evs (sv (lam (lam B)) γ) l) x = sv B (γ, kv l, kn x).
Proof. exact (peq_trans ((sv_lam (lam B) γ (kv l)) (tt, kn x)) (sv_lam B (γ, kv l) (kn x))). Qed.

Lemma snoc_sem Γ γ l x : ev (evs (sv (snoct (Γ := Γ)) γ) (enc l : So tL)) x = enc (l ++ [x]).
Proof.
  unfold snoct. rewrite ev2_lamL.
  change (wrec_val F (dsc := dL) tt tL (sargs PSet So (Iy F (dsc := dL))
            (@acons _ hL (ι tN :: ι tL :: Γ) (Spec [] tL) _ (Cons v0 Nil)
               (@acons _ hL (ι tN :: ι tL :: Γ) (Spec [ι tN; ι tL; ι tL] tL) _ (Cons v0 v2) anil))
            (penv PSet So (ι tN :: ι tL :: Γ)) (γ, kv (a := tL) (enc l), kn x)) (enc l) = enc (l ++ [x])).
  set (Q := sargs PSet So (Iy F (dsc := dL)) _ _ _).
  assert (H : forall l', wrec_val F (dsc := dL) tt tL Q (enc l') = enc (l' ++ [x])).
  { induction l' as [|y l' IH]; [reflexivity|]. cbn -[Q]. rewrite IH. reflexivity. }
  apply H.
Qed.

Definition sgb (α : So NN) : nat -> bool := fun i => negb (ev1 α i =? 0).

Lemma sv_apL2 {Γ} (f : tm Γ (tarr tL (tarr tN tL))) (u : tm Γ tL) (w : tm Γ tN) (γ : ictx Γ) :
  sv (ap (ap f u) w) γ = ev (evs (sv f γ) (sv u γ)) (sv w γ).
Proof. exact (peq_trans (sv_ap (ap f u) w γ) (sv_ap f u γ (tt, kv (sv w γ)))). Qed.

Lemma ev2_lamA {Γ} (B : tm (ι tN :: ι NN :: Γ) tL) (γ : ictx Γ) (α : So NN) n :
  ev (evs (sv (lam (lam B)) γ) α) n = sv B (γ, kv α, kn n).
Proof. exact (peq_trans ((sv_lam (lam B) γ (kv α)) (tt, kn n)) (sv_lam B (γ, kv α) (kn n))). Qed.

Lemma sv_recL {Γ} h (z : tm Γ tL) (st : tm (ι tN :: ι tL :: Γ) tL) (n : tm Γ tN) (γ : ictx Γ) :
  sv (recN tL h z st n) γ = nat_rect (fun _ => pcar (So tL)) (sv z γ) (fun k acc => sv st (γ, kv acc, kn k)) (sv n γ).
Proof. exact (sv_rec tL h z st n γ). Qed.

Lemma pre_sem Γ γ (α : So NN) n :
  ev (evs (sv (pret (Γ := Γ)) γ) α) n = enc (map Nat.b2n (pre (sgb α) n)).
Proof.
  unfold pret. rewrite ev2_lamA, sv_recL.
  natgen' (fun m => enc (map Nat.b2n (pre (sgb α) m))); [reflexivity| |svvar; reflexivity].
  rewrite sv_apL2, IHm, sv_apN, sg_sem, sv_apN. svvar. rewrite snoc_sem.
  unfold pre. rewrite seq_S, map_app, map_app. cbn [map Nat.add]. unfold sgb. destruct (ev1 α m); reflexivity.
Qed.
End Sem.
