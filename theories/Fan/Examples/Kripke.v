(** * Le modèle de réalisabilité de Kripke à oracles

    Paramètres : des constantes C (avec une étiquette entière), des mondes
    (W, ≼) et, pour chaque monde, une interprétation des constantes
    O(w) : C → option (N → B), monotone. Une fonction [fresh] fournit, au-
    dessus de tout monde, une constante d'étiquette aussi grande que voulue
    interprétée par un chemin donné. ESAT (mondes = listes d'oracles) et la
    variante « oracles partout » (un seul monde) en sont des instances.

    L'EF (proposition 31 de l'article, en version relationnelle) :
    - Φ : familles A(w) de termes clos *bien formés en w* (leurs oracles sont
      interprétés en w), croissantes en w ;
    - E : termes clos sans oracle ;
    - e ⊩ A ≤ B : pour tout w et u ∈ A(w), e u se réduit (en w) dans B(w) ;
    - A ⇒ B en w : réalisateurs qui, en tout w' ≽ w, envoient A(w') dans
      B(w') ; ∧ par les projections ; ⋀ par réalisateurs retardés (a 0).
    Codes des entiers : ⌜n⌝(w) = termes qui se réduisent vers n̄.

    On prouve les trois hypothèses du théorème robuste :
    - la recherche, par l'opérateur μ écrit avec le combinateur de Turing ;
    - la continuité partout : un oracle frais pour α, une réduction n'en
      lit qu'un nombre fini de valeurs, on la rejoue avec β ;
    - l'existentiel fort : on substitue l'oracle frais par un code
      quelconque de α ([replay]), ce qui rend la valeur calculée par la
      barre indépendante du code ; la confluence identifie les témoins. *)

From Stdlib Require Import List Arith Lia Bool.
Import ListNotations.
From SF.Models Require Import PSet Frame.
From SF.Fan Require Import Ent Statement Robust.
From SF.Fan.Examples Require Import Lam Confluence Reach.

(** ** Rejouer une réduction en remplaçant un oracle *)

Section Replay.

Context {C : Type} (tag : C -> nat).

Local Notation tm := (tm C).
Local Notation csub := (csub tag).

Lemma replay_step (O1 : C -> option (nat -> bool)) k α (t u : tm) :
  step O1 t u ->
  (forall d, occ d t -> tag d = k -> O1 d = Some α) ->
  exists m, forall (O2 : C -> option (nat -> bool)) s,
    (forall d f, occ d t -> tag d <> k -> O1 d = Some f -> O2 d = Some f) ->
    closed s -> (forall n, n < m -> red O2 (App s (num n)) (num (Nat.b2n (α n)))) ->
    red O2 (csub k s t) (csub k s u).
Proof.
  induction 1; intros Hk;
    try (destruct IHstep as [m Hm]; [intros d Hd; apply Hk; cbn; tauto|];
         exists m; intros O2 s Ho Hs Hsim; cbn;
         first [apply red_lam | apply red_app | apply red_pair | apply red_p1 | apply red_p2
               | apply red_succ | apply red_rec];
         try apply r_refl; apply Hm; auto; intros; apply Ho; cbn; tauto).
  - exists 0. intros O2 s _ Hs _. cbn. rewrite csub_beta by exact Hs. apply red_one, s_beta.
  - exists 0. intros O2 s _ _ _. apply red_one, s_p1.
  - exists 0. intros O2 s _ _ _. apply red_one, s_p2.
  - exists 0. intros O2 s _ _ _. apply red_one, s_rec0.
  - exists 0. intros O2 s _ _ _. apply red_one, s_recS.
  - destruct (Nat.eqb_spec (tag c) k) as [E|E].
    + exists (S n). intros O2 s _ Hs Hsim. cbn. rewrite (proj2 (Nat.eqb_eq _ _) E), csub_num, csub_num.
      assert (f = α) as -> by (rewrite (Hk c (or_introl eq_refl) E) in H; congruence).
      apply Hsim. lia.
    + exists 0. intros O2 s Ho _ _. cbn. rewrite (proj2 (Nat.eqb_neq _ _) E), csub_num, csub_num.
      apply red_one, s_orc. apply (Ho c f); [cbn; tauto|exact E|exact H].
Qed.

Theorem replay (O1 : C -> option (nat -> bool)) k α (t v : tm) :
  red O1 t v ->
  (forall d, occ d t -> tag d = k -> O1 d = Some α) ->
  exists m, forall (O2 : C -> option (nat -> bool)) s,
    (forall d f, occ d t -> tag d <> k -> O1 d = Some f -> O2 d = Some f) ->
    closed s -> (forall n, n < m -> red O2 (App s (num n)) (num (Nat.b2n (α n)))) ->
    red O2 (csub k s t) (csub k s v).
Proof.
  induction 1 as [t|t u v H H' IH]; intros Hk.
  - exists 0. intros. apply r_refl.
  - destruct (replay_step O1 k α t u H Hk) as [m1 Hm1].
    destruct IH as [m2 Hm2]; [intros d Hd; apply Hk, (step_occ _ _ _ _ H Hd)|].
    exists (Nat.max m1 m2). intros O2 s Ho Hs Hsim. eapply red_trans.
    + apply Hm1; auto. intros n Hn; apply Hsim; lia.
    + apply Hm2; auto; [|intros n Hn; apply Hsim; lia].
      intros d f Hd. apply Ho, (step_occ _ _ _ _ H Hd).
Qed.

End Replay.

(** ** Le modèle *)

Section Kripke.

Context {C : Type} (tag : C -> nat).
Context (W : Type) (le : W -> W -> Prop).
Context (le_refl : forall w, le w w) (le_trans : forall a b c, le a b -> le b c -> le a c).
Context (O : W -> C -> option (nat -> bool)).
Context (O_mono : forall w w' c f, le w w' -> O w c = Some f -> O w' c = Some f).
Context (fresh : W -> nat -> (nat -> bool) -> W * C).
Context (fresh_le : forall w N α, le w (fst (fresh w N α))).
Context (fresh_tag : forall w N α, N <= tag (snd (fresh w N α))).
Context (fresh_O : forall w N α, O (fst (fresh w N α)) (snd (fresh w N α)) = Some α).

Local Notation tm := (tm C).
Local Notation R w := (red (O w)).

Lemma R_mono w w' (t u : tm) : le w w' -> R w t u -> R w' t u.
Proof. intros H. apply red_mono. intros c f. apply O_mono, H. Qed.

(** Termes clos bien formés en w. *)
Definition good (w : W) (t : tm) : Prop := closed t /\ forall c, occ c t -> exists f, O w c = Some f.

Lemma good_mono w w' t : le w w' -> good w t -> good w' t.
Proof.
  intros H [H1 H2]. split; [exact H1|]. intros c Hc. destruct (H2 c Hc) as [f Hf].
  exists f. apply (O_mono w), Hf; exact H.
Qed.

Lemma good_red w t u : R w t u -> good w t -> good w u.
Proof.
  intros H [H1 H2]. split; [exact (red_wf _ 0 _ _ H H1)|]. intros c Hc. apply H2, (red_occ _ _ _ _ H Hc).
Qed.

(** Les évidences : termes clos sans oracle. *)
Definition cl0 (t : tm) : Prop := closed t /\ forall c, ~ occ c t.
Definition ev : Type := { t : tm | cl0 t }.

Lemma ev_closed (e : ev) : closed (proj1_sig e).
Proof. exact (proj1 (proj2_sig e)). Qed.

Lemma ev_noocc (e : ev) c : ~ occ c (proj1_sig e).
Proof. exact (proj2 (proj2_sig e) c). Qed.

Lemma wf_closed k (t : tm) : closed t -> wf k t.
Proof. intros H. apply (wf_mono 0); [exact H|lia]. Qed.

Lemma closed_wf0 (t : tm) : wf 0 t -> closed t.
Proof. exact (fun H => H). Qed.

#[local] Hint Resolve ev_closed num_closed wf_closed : cl.

Ltac bsimp :=
  unfold beta; cbn [subst ups scons ren upr];
  repeat match goal with |- context [ren ?ξ ?t] => rewrite (ren_closed ξ t) by (eauto with cl) end;
  repeat match goal with |- context [subst ?σ ?t] => rewrite (subst_closed σ t) by (eauto with cl) end;
  repeat match goal with |- context [ren ?ξ ?t] => rewrite (ren_closed ξ t) by (eauto with cl) end.

(** Prouver qu'un terme composé est bien formé. *)
Ltac good_tac :=
  match goal with
  | |- good _ _ => split; [cbn; repeat split; try lia; eauto with cl|]
  end;
  let c := fresh "c" in let Hc := fresh "Hc" in
  intros c Hc; cbn in Hc; repeat (destruct Hc as [Hc|Hc]);
  try contradiction;
  try (exfalso; eapply ev_noocc; exact Hc);
  try (exfalso; eapply occ_num; exact Hc);
  match goal with H : good _ _ |- _ => apply (proj2 H); exact Hc end.

Ltac cl0_tac :=
  split; [cbn; repeat split; try lia; eauto with cl|];
  let c := fresh "c" in let Hc := fresh "Hc" in
  intros c Hc; cbn in Hc; repeat (destruct Hc as [Hc|Hc]); try contradiction;
  eapply ev_noocc; exact Hc.

(** *** Les propositions *)

Record kprop := {
  kp :> W -> tm -> Prop;
  kp_mono : forall w w' t, le w w' -> kp w t -> kp w' t;
  kp_good : forall w t, kp w t -> good w t
}.

Program Definition KP : pset := {| pcar := kprop; peq := fun A B => forall w t, A w t <-> B w t |}.
Next Obligation. reflexivity. Qed.
Next Obligation. symmetry; auto. Qed.
Next Obligation. etransitivity; eauto. Qed.

Definition rent (A : kprop) (e : ev) (B : kprop) : Prop :=
  forall w u, A w u -> exists v, R w (App (proj1_sig e) u) v /\ B w v.

Definition ktop : kprop.
Proof. refine {| kp := good |}; [intros w w' t H Ht; eapply good_mono; eauto|intros w t H; exact H]. Defined.

Definition kand (A B : kprop) : kprop.
Proof.
  refine {| kp := fun w p => good w p /\ (exists a, R w (P1 p) a /\ A w a) /\ (exists b, R w (P2 p) b /\ B w b) |}.
  - intros w w' t H (Hg & (a & Ha & HA) & (b & Hb & HB)). split; [eapply good_mono; eauto|split].
    + exists a. split; [eapply R_mono; eauto|eapply kp_mono; eauto].
    + exists b. split; [eapply R_mono; eauto|eapply kp_mono; eauto].
  - intros w t H; apply H.
Defined.

Definition kimp (A B : kprop) : kprop.
Proof.
  refine {| kp := fun w f => good w f /\ forall w', le w w' -> forall u, A w' u -> exists v, R w' (App f u) v /\ B w' v |}.
  - intros w w' t H (Hg & Hf). split; [eapply good_mono; eauto|]. intros w'' H' u Hu. apply Hf; [eauto|exact Hu].
  - intros w t H; apply H.
Defined.

Definition kall {I : Type} (F : I -> kprop) : kprop.
Proof.
  refine {| kp := fun w a => good w a /\ forall i, exists b, R w (App a Zero) b /\ F i w b |}.
  - intros w w' t H (Hg & Ha). split; [eapply good_mono; eauto|]. intros i. destruct (Ha i) as (b & Hb & Hi).
    exists b. split; [eapply R_mono; eauto|eapply kp_mono; eauto].
  - intros w t H; apply H.
Defined.

(** *** Les évidences *)

Program Definition e_idk : ev := Lam (Var 0).
Next Obligation. cl0_tac. Qed.

Program Definition e_compk (e1 e2 : ev) : ev := Lam (App (proj1_sig e2) (App (proj1_sig e1) (Var 0))).
Next Obligation. cl0_tac. Qed.

Program Definition e_topk : ev := Lam Zero.
Next Obligation. cl0_tac. Qed.

Program Definition e_fstk : ev := Lam (P1 (Var 0)).
Next Obligation. cl0_tac. Qed.
Program Definition e_sndk : ev := Lam (P2 (Var 0)).
Next Obligation. cl0_tac. Qed.

Program Definition e_pairk (e1 e2 : ev) : ev :=
  Lam (Pair (App (proj1_sig e1) (Var 0)) (App (proj1_sig e2) (Var 0))).
Next Obligation. cl0_tac. Qed.

Program Definition e_lamk (e : ev) : ev := Lam (Lam (App (proj1_sig e) (Pair (Var 1) (Var 0)))).
Next Obligation. cl0_tac. Qed.

Program Definition e_evalk : ev := Lam (App (P1 (Var 0)) (P2 (Var 0))).
Next Obligation. cl0_tac. Qed.

Program Definition e_genk (e : ev) : ev := Lam (Lam (App (proj1_sig e) (Var 1))).
Next Obligation. cl0_tac. Qed.

Program Definition e_instk : ev := Lam (App (Var 0) Zero).
Next Obligation. cl0_tac. Qed.

(** *** Correction des évidences *)

Lemma rent_beta (A B : kprop) (e : ev) b :
  proj1_sig e = Lam b -> (forall w u, A w u -> exists v, R w (beta b u) v /\ B w v) -> rent A e B.
Proof.
  intros E H w u Hu. destruct (H w u Hu) as (v & Hv & HB). exists v. split; [|exact HB].
  rewrite E. eapply r_step; [apply s_beta|exact Hv].
Qed.

Lemma r_idk A : rent A e_idk A.
Proof. eapply rent_beta; [reflexivity|]. intros w u Hu. bsimp. exists u. split; [apply r_refl|exact Hu]. Qed.

Lemma r_compk A B D e1 e2 : rent A e1 B -> rent B e2 D -> rent A (e_compk e1 e2) D.
Proof.
  intros H1 H2. eapply rent_beta; [reflexivity|]. intros w u Hu.
  pose proof (kp_good _ _ _ Hu) as [Hcu _]. bsimp.
  destruct (H1 w u Hu) as (v1 & Hv1 & HB). destruct (H2 w v1 HB) as (v2 & Hv2 & HD).
  exists v2. split; [|exact HD]. eapply red_trans; [apply red_app; [apply r_refl|exact Hv1]|exact Hv2].
Qed.

Lemma r_topk A : rent A e_topk ktop.
Proof.
  eapply rent_beta; [reflexivity|]. intros w u Hu. bsimp. exists Zero. split; [apply r_refl|].
  split; [exact Logic.I|intros c []].
Qed.

Lemma r_fstk A B : rent (kand A B) e_fstk A.
Proof.
  eapply rent_beta; [reflexivity|]. intros w u (Hg & (a & Ha & HA) & _).
  pose proof (proj1 Hg). bsimp. exists a. split; [exact Ha|exact HA].
Qed.

Lemma r_sndk A B : rent (kand A B) e_sndk B.
Proof.
  eapply rent_beta; [reflexivity|]. intros w u (Hg & _ & (b & Hb & HB)).
  pose proof (proj1 Hg). bsimp. exists b. split; [exact Hb|exact HB].
Qed.

Lemma r_pairk A B D e1 e2 : rent A e1 B -> rent A e2 D -> rent A (e_pairk e1 e2) (kand B D).
Proof.
  intros H1 H2. eapply rent_beta; [reflexivity|]. intros w u Hu.
  pose proof (kp_good _ _ _ Hu) as Hg. pose proof (proj1 Hg). bsimp.
  eexists. split; [apply r_refl|]. split; [good_tac|split].
  - destruct (H1 w u Hu) as (v & Hv & HB). exists v. split; [|exact HB].
    eapply r_step; [apply s_p1|exact Hv].
  - destruct (H2 w u Hu) as (v & Hv & HD). exists v. split; [|exact HD].
    eapply r_step; [apply s_p2|exact Hv].
Qed.

Lemma r_lamk A B D e : rent (kand A B) e D -> rent A (e_lamk e) (kimp B D).
Proof.
  intros H. eapply rent_beta; [reflexivity|]. intros w u Hu.
  pose proof (kp_good _ _ _ Hu) as Hg. pose proof (proj1 Hg). bsimp.
  eexists. split; [apply r_refl|]. split; [good_tac|].
  intros w' Hw v Hv. pose proof (kp_good _ _ _ Hv) as Hgv. pose proof (proj1 Hgv).
  assert (Hp : kand A B w' (Pair u v)).
  { apply (good_mono w w') in Hg; [|exact Hw]. split; [good_tac|split].
    - exists u. split; [apply red_one, s_p1|eapply kp_mono; eauto].
    - exists v. split; [apply red_one, s_p2|exact Hv]. }
  destruct (H w' _ Hp) as (z & Hz & HD). exists z. split; [|exact HD].
  eapply r_step; [apply s_beta|]. bsimp. exact Hz.
Qed.

Lemma r_evalk B D : rent (kand (kimp B D) B) e_evalk D.
Proof.
  eapply rent_beta; [reflexivity|]. intros w u (Hg & (f & Hf & Hfi) & (a & Ha & HB)).
  pose proof (proj1 Hg). bsimp.
  destruct (proj2 Hfi w (le_refl w) a HB) as (v & Hv & HD). exists v. split; [|exact HD].
  eapply red_trans; [apply red_app; [exact Hf|exact Ha]|exact Hv].
Qed.

Lemma r_genk {I} A (F : I -> kprop) e : (forall i, rent A e (F i)) -> rent A (e_genk e) (kall F).
Proof.
  intros H. eapply rent_beta; [reflexivity|]. intros w u Hu.
  pose proof (kp_good _ _ _ Hu) as Hg. pose proof (proj1 Hg). bsimp.
  eexists. split; [apply r_refl|]. split; [good_tac|].
  intros i. destruct (H i w u Hu) as (v & Hv & HF). exists v. split; [|exact HF].
  eapply r_step; [apply s_beta|]. bsimp. exact Hv.
Qed.

Lemma r_instk {I} (F : I -> kprop) i : rent (kall F) e_instk (F i).
Proof.
  eapply rent_beta; [reflexivity|]. intros w u (Hg & Hu).
  pose proof (proj1 Hg). bsimp. exact (Hu i).
Qed.

(** *** Le cadre *)

Lemma rent_proper (A A' : kprop) e (B B' : kprop) :
  (forall w t, A w t <-> A' w t) -> (forall w t, B w t <-> B' w t) -> rent A e B -> rent A' e B'.
Proof.
  intros E1 E2 H w u Hu. destruct (H w u (proj2 (E1 w u) Hu)) as (v & Hv & HB).
  exists v. split; [exact Hv|apply E2, HB].
Qed.

Lemma kand_proper (A A' B B' : kprop) : (forall w t, A w t <-> A' w t) -> (forall w t, B w t <-> B' w t) ->
  forall w t, kand A B w t <-> kand A' B' w t.
Proof.
  intros E1 E2 w t. cbn. split; intros (Hg & (a & Ha & HA) & (b & Hb & HB));
    (split; [exact Hg|split; [exists a; split; [exact Ha|apply E1, HA]|exists b; split; [exact Hb|apply E2, HB]]]).
Qed.

Lemma kimp_proper (A A' B B' : kprop) : (forall w t, A w t <-> A' w t) -> (forall w t, B w t <-> B' w t) ->
  forall w t, kimp A B w t <-> kimp A' B' w t.
Proof.
  intros E1 E2 w t. cbn. split; intros (Hg & H); (split; [exact Hg|]); intros w' Hw u Hu;
    [destruct (H w' Hw u (proj2 (E1 w' u) Hu)) as (v & Hv & HB)|destruct (H w' Hw u (proj1 (E1 w' u) Hu)) as (v & Hv & HB)];
    exists v; (split; [exact Hv|apply E2, HB]).
Qed.

Lemma kall_proper I (F G : I -> kprop) : (forall i w t, F i w t <-> G i w t) ->
  forall w t, kall F w t <-> kall G w t.
Proof.
  intros E w t. cbn. split; intros (Hg & H); (split; [exact Hg|]); intros i; destruct (H i) as (b & Hb & Hi);
    exists b; (split; [exact Hb|apply E, Hi]).
Qed.

Definition kallP (S : KP -> Prop) : kprop := kall (I := {ψ : KP | S ψ}) (fun p => proj1_sig p).

Lemma kallP_proper (S T : KP -> Prop) : (forall ψ, S ψ <-> T ψ) -> forall w t, kallP S w t <-> kallP T w t.
Proof.
  intros E w t. unfold kallP. cbn. split; intros (Hg & H); (split; [exact Hg|]); intros [ψ Hψ].
  - exact (H (exist _ ψ (proj2 (E ψ) Hψ))).
  - exact (H (exist _ ψ (proj1 (E ψ) Hψ))).
Qed.

Lemma r_genkP (S : KP -> Prop) A e : (forall ψ, S ψ -> rent A e ψ) -> rent A (e_genk e) (kallP S).
Proof. intros H. apply r_genk. intros [ψ Hψ]. exact (H ψ Hψ). Qed.

Lemma r_instkP (S : KP -> Prop) ψ : S ψ -> rent (kallP S) e_instk ψ.
Proof. intros H. exact (r_instk (fun p : {ψ : KP | S ψ} => proj1_sig p) (exist _ ψ H)). Qed.

Definition kframe : frame := {|
  fprop := KP;
  fev := ev;
  fent := rent;
  fent_proper := rent_proper;
  e_id := e_idk; f_id := r_idk;
  e_comp := e_compk; f_comp := r_compk;
  ftop := ktop; e_top := e_topk; f_top := r_topk;
  fand := kand; fand_proper := kand_proper;
  e_fst := e_fstk; f_fst := r_fstk; e_snd := e_sndk; f_snd := r_sndk;
  e_pair := e_pairk; f_pair := r_pairk;
  fimp := kimp; fimp_proper := kimp_proper;
  e_lam := e_lamk; f_lam := r_lamk; e_eval := e_evalk; f_eval := r_evalk;
  fallP := kallP; fallP_proper := kallP_proper;
  e_gen := e_genk; f_genP := r_genkP; e_inst := e_instk; f_instP := r_instkP
|}.

(** *** Les entiers *)

Local Notation KF := kframe.
Local Notation Φ := (pcar (fprop KF)).

Definition kcode (n : nat) : kprop.
Proof.
  refine {| kp := fun w t => good w t /\ R w t (num n) |}.
  - intros w w' t H [Hg Hr]. split; [eapply good_mono; eauto|eapply R_mono; eauto].
  - intros w t H; apply H.
Defined.

Lemma num_code w n : kcode n w (num n).
Proof. split; [split; [apply num_closed|intros c Hc; exfalso; exact (occ_num _ _ Hc)]|apply r_refl]. Qed.

Program Definition e0k : ev := Lam Zero.
Next Obligation. cl0_tac. Qed.

Program Definition eSk : ev := Lam (Succ (Var 0)).
Next Obligation. cl0_tac. Qed.

Definition Ss (s : tm) : tm := Lam (Lam (App (App (App s Zero) (Var 1)) (Var 0))).

Program Definition ereck : ev :=
  Lam (Lam (Lam (Lam (Lam (Rec (Var 3) (Lam (Lam (App (App (App (Var 4) Zero) (Var 1)) (Var 0)))) (Var 0)))))).
Next Obligation. cl0_tac. Qed.

Lemma r_e0 : rent ktop e0k (kcode 0).
Proof.
  eapply rent_beta; [reflexivity|]. intros w u Hu. bsimp. exists Zero. split; [apply r_refl|apply (num_code w 0)].
Qed.

Lemma r_eS n : rent (kcode n) eSk (kcode (S n)).
Proof.
  eapply rent_beta; [reflexivity|]. intros w u [Hg Hr]. pose proof (proj1 Hg). bsimp.
  exists (Succ u). split; [apply r_refl|]. split; [good_tac|apply red_succ, Hr].
Qed.

Lemma rec_num (f : nat -> kprop) w1 w2 w3 z s :
  le w1 w2 -> le w2 w3 -> f 0 w1 z ->
  kall (fun n => kimp (kcode n) (kimp (f n) (f (S n)))) w2 s ->
  forall n, exists v, R w3 (Rec z (Ss s) (num n)) v /\ f n w3 v.
Proof.
  intros H12 H23 Hz Hs. pose proof (proj1 (kp_good _ _ _ Hz)) as Cz. pose proof (proj1 (proj1 Hs)) as Cs.
  induction n as [|n (v & Hv & Hfv)].
  - exists z. split; [apply red_one, s_rec0|]. apply (kp_mono _ w1); eauto.
  - destruct (proj2 Hs n) as (b & Hb & Hbi).
    apply (kp_mono _ w2 w3) in Hbi; [|exact H23]. apply (R_mono w2 w3) in Hb; [|exact H23].
    destruct (proj2 Hbi w3 (le_refl _) (num n) (num_code w3 n)) as (c & Hc & Hci).
    destruct (proj2 Hci w3 (le_refl _) v Hfv) as (r & Hr & Hfr).
    exists r. split; [|exact Hfr].
    eapply r_step; [apply s_recS|].
    eapply r_step; [apply s_appl, s_beta|]. bsimp.
    eapply r_step; [apply s_beta|]. bsimp.
    eapply red_trans; [apply red_app; [apply red_app; [exact Hb|apply r_refl]|exact Hv]|].
    eapply red_trans; [apply red_app; [exact Hc|apply r_refl]|exact Hr].
Qed.

Lemma r_erec (f : nat -> kprop) :
  rent ktop ereck (kimp (f 0) (kimp (kall (fun n => kimp (kcode n) (kimp (f n) (f (S n)))))
                                  (kall (fun n => kimp (kcode n) (f n))))).
Proof.
  eapply rent_beta; [reflexivity|]. intros w d Hd. bsimp. eexists. split; [apply r_refl|].
  split; [cl0_tac|]. intros w1 H1 z Hz. pose proof (kp_good _ _ _ Hz) as Gz. pose proof (proj1 Gz) as Cz.
  eexists. split; [apply red_one, s_beta|]. bsimp.
  split; [good_tac|]. intros w2 H2 s Hs. pose proof (kp_good _ _ _ Hs) as Gs. pose proof (proj1 Gs) as Cs.
  pose proof (good_mono w1 w2 z H2 Gz) as Gz2.
  eexists. split; [apply red_one, s_beta|]. bsimp.
  split; [clear Gz; good_tac|].
  intros n. eexists. split; [apply red_one, s_beta|]. bsimp.
  split; [clear Gz; good_tac|].
  intros w3 H3 a [Hga Hra]. pose proof (proj1 Hga) as Ca.
  destruct (rec_num f w1 w2 w3 z s H2 H3 Hz Hs n) as (v & Hv & Hfv).
  exists v. split; [|exact Hfv].
  eapply r_step; [apply s_beta|]. bsimp. fold (Ss s).
  eapply red_trans; [apply red_rec; [apply r_refl|apply r_refl|exact Hra]|exact Hv].
Qed.

(** Le ⋀ dérivé de [kframe] et [kall] coïncident. *)
Lemma kall_fall {I : Type} (F : I -> kprop) : forall w t, kall F w t <-> @fall KF I F w t.
Proof.
  intros w t. unfold fall. cbn. split; intros (Hg & H); (split; [exact Hg|]).
  - intros [ψ [i Hi]]. destruct (H i) as (b & Hb & Hf). exists b. split; [exact Hb|apply Hi, Hf].
  - intros i. destruct (H (exist _ (F i) (ex_intro _ i (fun w t => iff_refl _)))) as (b & Hb & Hf).
    exists b. split; [exact Hb|exact Hf].
Qed.

Lemma r_erec' (f : nat -> kprop) :
  rent ktop ereck (kimp (f 0) (kimp (@fall KF nat (fun n => kimp (kcode n) (kimp (f n) (f (S n)))))
                                  (@fall KF nat (fun n => kimp (kcode n) (f n))))).
Proof.
  eapply rent_proper; [intros w t; reflexivity| |apply r_erec].
  apply kimp_proper; [intros w t; reflexivity|].
  apply kimp_proper; apply kall_fall.
Qed.

Definition kE : efdata := {|
  ef := KF; code := kcode;
  c0 := ex_intro _ e0k r_e0; cS := ex_intro _ eSk r_eS; crec := ex_intro _ ereck r_erec'
|}.

(** *** La vérité méta *)

Definition kconst (P : Prop) : kprop.
Proof.
  refine {| kp := fun w t => good w t /\ P |}.
  - intros w w' t H [Hg HP]. split; [eapply good_mono; eauto|exact HP].
  - intros w t H; apply H.
Defined.

Program Definition IDX : ev := Lam (Lam (Var 0)).
Next Obligation. cl0_tac. Qed.

Lemma meta_true (P : Prop) w t : fprop_of (F := KF) P w t -> P.
Proof.
  intros [Hg Ht]. destruct (Ht (fall_idx (F := KF) _ (kconst P))) as (b & Hb & Hbi).
  assert (HI : kall (fun _ : P => kimp ktop (kconst P)) w (proj1_sig IDX)).
  { split; [cl0_tac|]. intros p. eexists. split; [apply red_one, s_beta|]. bsimp.
    split; [cl0_tac|]. intros w' _ u Hu. pose proof (proj1 Hu).
    exists u. split; [eapply r_step; [apply s_beta|]; bsimp; apply r_refl|]. split; [exact Hu|exact p]. }
  destruct (proj2 Hbi w (le_refl w) _ (proj1 (kall_fall _ w _) HI)) as (v & _ & _ & HP). exact HP.
Qed.

Local Notation EXI := (proj1_sig (e_exI (F := KF))).

Lemma exi_ok {I} (f : I -> kprop) i w u : f i w u -> exists v, R w (App EXI u) v /\ fex (F := KF) f w v.
Proof. intros H. exact (f_exI (F := KF) I f i w u H). Qed.

Lemma meta_intro (P : Prop) w : P -> exists v, R w (App EXI Zero) v /\ fprop_of (F := KF) P w v.
Proof.
  intros HP. apply (exi_ok (fun _ : P => ktop) HP). split; [exact Logic.I|intros c []].
Qed.

(** *** Recherche non bornée *)

Definition Ath : tm := Lam (Lam (App (Var 0) (App (App (Var 1) (Var 1)) (Var 0)))).
Definition Th : tm := App Ath Ath.
Definition Fs : tm := Lam (Lam (App (Var 3) (Succ (Var 2)))).
Definition Gs (c : tm) : tm := Lam (Lam (Rec (Var 0) Fs (App (App c Zero) (Var 0)))).

Program Definition MU : ev := Lam (App (App Th (Lam (Lam (Rec (Var 0) Fs (App (App (Var 2) Zero) (Var 0)))))) Zero).
Next Obligation. cl0_tac. Qed.

Lemma Th_step w g : closed g -> R w (App Th g) (App g (App Th g)).
Proof.
  intros Cg. unfold Th at 1. eapply r_step; [apply s_appl, s_beta|]. bsimp.
  eapply r_step; [apply s_beta|]. bsimp. apply r_refl.
Qed.

Lemma search_loop w c (f : nat -> nat) :
  closed c -> (forall k, R w (App (App c Zero) (num k)) (num (f k))) ->
  forall d k, (exists n, k <= n /\ n <= k + d /\ f n = 0) ->
  exists m, f m = 0 /\ R w (App (App Th (Gs c)) (num k)) (num m).
Proof.
  intros Cc Hc. assert (CG : closed (Gs c)) by (cbn; repeat split; try lia; eauto with cl).
  induction d as [|d IH]; intros k (n & Hn1 & Hn2 & Hn).
  - exists k. assert (n = k) as -> by lia. split; [exact Hn|].
    eapply red_trans; [apply red_app; [apply Th_step, CG|apply r_refl]|].
    eapply r_step; [apply s_appl, s_beta|]. bsimp.
    eapply r_step; [apply s_beta|]. bsimp.
    eapply red_trans; [apply red_rec; [apply r_refl|apply r_refl|apply Hc]|]. rewrite Hn. apply red_one, s_rec0.
  - destruct (f k) eqn:Ek.
    + exists k. split; [exact Ek|].
      eapply red_trans; [apply red_app; [apply Th_step, CG|apply r_refl]|].
      eapply r_step; [apply s_appl, s_beta|]. bsimp.
      eapply r_step; [apply s_beta|]. bsimp.
      eapply red_trans; [apply red_rec; [apply r_refl|apply r_refl|apply Hc]|]. rewrite Ek. apply red_one, s_rec0.
    + destruct (IH (S k)) as (m & Hm & Hr).
      { exists n. assert (n <> k) by (intros ->; congruence). repeat split; lia || exact Hn. }
      exists m. split; [exact Hm|].
      eapply red_trans; [apply red_app; [apply Th_step, CG|apply r_refl]|].
      eapply r_step; [apply s_appl, s_beta|]. bsimp.
      eapply r_step; [apply s_beta|]. bsimp.
      eapply red_trans; [apply red_rec; [apply r_refl|apply r_refl|apply Hc]|]. rewrite Ek.
      eapply r_step; [apply s_recS|].
      eapply r_step; [apply s_appl, s_beta|]. bsimp.
      eapply r_step; [apply s_beta|]. bsimp. exact Hr.
Qed.

Lemma cfun_apply w c (f : nat -> nat) : cfun kE f w c -> forall k, R w (App (App c Zero) (num k)) (num (f k)).
Proof.
  intros H k. destruct (proj2 (kall_fall _ w c) H) as [Hg Hc]. destruct (Hc k) as (b & Hb & Hbi).
  destruct (proj2 Hbi w (le_refl w) (num k) (num_code w k)) as (v & Hv & [_ Hvn]).
  eapply red_trans; [apply red_app; [exact Hb|apply r_refl]|]. eapply red_trans; [exact Hv|exact Hvn].
Qed.

Program Definition e_srch : ev :=
  Lam (App EXI (Pair (App (proj1_sig MU) (P1 (Var 0))) (App EXI Zero))).
Next Obligation. cl0_tac. Qed.

Theorem k_search : search kE.
Proof.
  exists e_srch. intros f. eapply rent_beta; [reflexivity|]. intros w p (Hg & (c & Hc & Hcf) & (t & _ & Ht)).
  pose proof (proj1 Hg) as Cp. pose proof (proj1 (kp_good _ _ _ Hcf)) as Cc.
  destruct (meta_true _ _ _ Ht) as [n0 Hn0].
  destruct (search_loop w c f Cc (cfun_apply w c f Hcf) n0 0) as (m & Hm & Hr).
  { exists n0. repeat split; lia || exact Hn0. }
  destruct (meta_intro (f m = 0) w Hm) as (y & Hy & Hyi).
  assert (Hpair : kand (kcode m) (fprop_of (F := KF) (f m = 0)) w
                       (Pair (App (proj1_sig MU) (P1 p)) (App EXI Zero))).
  { split; [good_tac|split].
    - exists (num m). split; [|apply num_code].
      eapply r_step; [apply s_p1|]. eapply red_trans; [apply red_app; [apply r_refl|exact Hc]|].
      eapply r_step; [apply s_beta|]. bsimp. exact Hr.
    - exists y. split; [eapply r_step; [apply s_p2|exact Hy]|exact Hyi]. }
  destruct (exi_ok (fun n => kand (kcode n) (fprop_of (F := KF) (f n = 0))) m w _ Hpair) as (v & Hv & Hvi).
  exists v. split; [|exact Hvi]. bsimp. exact Hv.
Qed.

(** *** Codes de chemins à partir d'un simulateur *)

Definition Q (s : tm) : tm := Lam (Lam (App s (Var 0))).
Arguments Q /.

Lemma Q_path w α s : good w s ->
  (forall w' n, le w w' -> R w' (App s (num n)) (num (Nat.b2n (α n)))) -> cpath kE α w (Q s).
Proof.
  intros Hs Hsim. pose proof (proj1 Hs) as Cs. apply (proj1 (kall_fall _ w _)). split; [good_tac|]. intros n.
  eexists. split; [apply red_one, s_beta|]. bsimp. split; [good_tac|].
  intros w' Hw a [Hga Hra]. pose proof (proj1 Hga).
  exists (num (Nat.b2n (α n))). split; [|apply num_code].
  eapply r_step; [apply s_beta|]. bsimp.
  eapply red_trans; [apply red_app; [apply r_refl|exact Hra]|]. apply Hsim, Hw.
Qed.

Lemma orc_sim w c α : O w c = Some α -> forall w' n, le w w' -> R w' (App (Orc c) (num n)) (num (Nat.b2n (α n))).
Proof. intros H w' n Hw. apply red_one, s_orc. eapply O_mono; eauto. Qed.

Lemma orc_good w c α : O w c = Some α -> good w (Orc c).
Proof. intros H. split; [exact Logic.I|]. intros d Hd; cbn in Hd; subst. exists α; exact H. Qed.

Lemma use_cfun2 w u (G : (nat -> bool) -> nat) w' α P : cfun2 kE G w u -> le w w' -> cpath kE α w' P ->
  R w' (App (App u Zero) P) (num (G α)).
Proof.
  intros Hu Hw HP. apply (kp_mono _ w w') in Hu; [|exact Hw]. destruct (proj2 (proj2 (kall_fall _ w' _) Hu) α) as (d & Hd & Hdi).
  destruct (proj2 Hdi w' (le_refl _) P HP) as (v & Hv & [_ Hvn]).
  eapply red_trans; [apply red_app; [exact Hd|apply r_refl]|]. eapply red_trans; [exact Hv|exact Hvn].
Qed.

(** Les constantes d'un terme bien formé en w gardent leur sens au-dessus de w. *)
Lemma agree w w1 w2 (t : tm) : good w t -> le w w1 -> le w w2 ->
  forall d f, occ d t -> O w1 d = Some f -> O w2 d = Some f.
Proof.
  intros [_ Hg] H1 H2 d f Hd Hf. destruct (Hg d Hd) as [g Hgd].
  rewrite (O_mono w w1 d g H1 Hgd) in Hf. injection Hf as <-. exact (O_mono w w2 d g H2 Hgd).
Qed.

Lemma csub_Q k s c : tag c = k -> csub tag k s (Q (Orc c)) = Q s.
Proof. intros E. cbn. rewrite (proj2 (Nat.eqb_eq _ _) E). reflexivity. Qed.

Lemma csub_small k s (t : tm) : maxtag tag t < k -> csub tag k s t = t.
Proof. intros H. apply csub_id. intros c Hc. pose proof (occ_maxtag tag c t Hc). lia. Qed.

(** *** Continuité partout *)

Lemma cfun2_cont w u G : cfun2 kE G w u -> forall α, cont_at G α.
Proof.
  intros Hu α. pose proof (kp_good _ _ _ Hu) as Hgu. pose proof (proj1 Hgu) as Cu.
  set (N := S (maxtag tag u)).
  set (w1 := fst (fresh w N α)). set (c1 := snd (fresh w N α)). set (k := tag c1).
  assert (Hk : N <= k) by apply fresh_tag. assert (Hc1 : O w1 c1 = Some α) by apply fresh_O.
  assert (Hw1 : le w w1) by apply fresh_le.
  set (T := App (App u Zero) (Q (Orc c1))).
  assert (HT : R w1 T (num (G α))).
  { apply (use_cfun2 w u G w1 α); [exact Hu|exact Hw1|].
    apply Q_path; [apply (orc_good w1 c1 α Hc1)|apply orc_sim, Hc1]. }
  destruct (replay tag (O w1) k α T _ HT) as [m Hm].
  { intros d Hd Ek. cbn in Hd. destruct Hd as [[Hd|[]]|[Hd|[]]]; [|subst; exact Hc1].
    pose proof (occ_maxtag tag d u Hd). lia. }
  exists m. intros β Hβ.
  set (w2 := fst (fresh w N β)). set (c2 := snd (fresh w N β)).
  assert (Hc2 : O w2 c2 = Some β) by apply fresh_O. assert (Hw2 : le w w2) by apply fresh_le.
  assert (H2 : R w2 (csub tag k (Orc c2) T) (csub tag k (Orc c2) (num (G α)))).
  { apply Hm.
    - intros d f Hd Ek Hf. cbn in Hd. destruct Hd as [[Hd|[]]|[Hd|[]]]; [|subst; contradiction].
      exact (agree w w1 w2 u Hgu Hw1 Hw2 d f Hd Hf).
    - exact Logic.I.
    - intros n Hn. rewrite <- (Hβ n Hn). apply red_one, s_orc, Hc2. }
  unfold T in H2. cbn [csub] in H2. rewrite csub_small in H2 by lia.
  rewrite (csub_Q k (Orc c2) c1 eq_refl), csub_num in H2.
  assert (H3 : R w2 (App (App u Zero) (Q (Orc c2))) (num (G β))).
  { apply (use_cfun2 w u G w2 β); [exact Hu|exact Hw2|].
    apply Q_path; [apply (orc_good w2 c2 β Hc2)|apply orc_sim, Hc2]. }
  exact (num_unique _ _ _ _ H3 H2).
Qed.

Program Definition e_cont : ev := Lam (App EXI Zero).
Next Obligation. cl0_tac. Qed.

Theorem k_continuity : continuity kE.
Proof.
  exists e_cont. intros G. eapply rent_beta; [reflexivity|]. intros w u Hu. bsimp.
  exact (meta_intro _ w (cfun2_cont w u G Hu)).
Qed.

(** *** Localité : un fait méta se lit sur les réalisateurs *)

Theorem k_locality : exists e, forall (φ : kprop) (P : (nat -> bool) -> Prop),
  (forall α, exists e', fent (F := KF) φ e' (fprop_of (F := KF) (P α))) ->
  fent (F := KF) φ e (fprop_of (F := KF) (forall α, P α)).
Proof.
  exists e_cont. intros φ P H. eapply rent_beta; [reflexivity|]. intros w u Hu. bsimp.
  apply meta_intro. intros α. destruct (H α) as [e' He']. destruct (He' w u Hu) as (v & _ & Hv).
  exact (meta_true _ w v Hv).
Qed.

(** *** Existentiel fort *)

Definition EXT (y : tm) : tm := App (App y Zero) (proj1_sig IDX).
Arguments EXT /.

Lemma ext_ok (f : nat -> kprop) w y : fex (F := KF) f w y -> exists v n, R w (EXT y) v /\ f n w v.
Proof.
  intros [Hg Hy].
  set (Xi := {| kp := fun w t => good w t /\ exists n, f n w t;
                kp_mono := fun w w' t H Ht => conj (good_mono w w' t H (proj1 Ht))
                             (match proj2 Ht with ex_intro _ n Hn => ex_intro _ n (kp_mono _ _ _ _ H Hn) end);
                kp_good := fun w t H => proj1 H |} : kprop).
  destruct (Hy (fall_idx (F := KF) _ Xi)) as (b & Hb & Hbi).
  assert (HI : kall (fun n => kimp (f n) Xi) w (proj1_sig IDX)).
  { split; [cl0_tac|]. intros n. eexists. split; [apply red_one, s_beta|]. bsimp.
    split; [cl0_tac|]. intros w' _ a Ha. pose proof (proj1 (kp_good _ _ _ Ha)).
    exists a. split; [eapply r_step; [apply s_beta|]; bsimp; apply r_refl|].
    split; [exact (kp_good _ _ _ Ha)|exists n; exact Ha]. }
  destruct (proj2 Hbi w (le_refl w) _ (proj1 (kall_fall _ w _) HI)) as (v & Hv & _ & n & Hn).
  exists v, n. split; [|exact Hn]. unfold EXT. eapply red_trans; [apply red_app; [exact Hb|apply r_refl]|exact Hv].
Qed.

Section Choice.

Variable φ : (nat -> bool) -> nat -> Φ.

Definition SRC : kprop :=
  kall (fun α => kimp (cpath kE α) (fex (F := KF) (fun n => kand (kcode n) (φ α n)))).

Lemma use_src w x w' α P : SRC w x -> le w w' -> cpath kE α w' P ->
  exists v n, R w' (EXT (App (App x Zero) P)) v /\ kand (kcode n) (φ α n) w' v.
Proof.
  intros Hx Hw HP. apply (kp_mono _ w w') in Hx; [|exact Hw]. destruct (proj2 Hx α) as (d & Hd & Hdi).
  destruct (proj2 Hdi w' (le_refl _) P HP) as (y & Hy & Hyi).
  destruct (ext_ok _ w' y Hyi) as (v & n & Hv & Hn). exists v, n. split; [|exact Hn].
  unfold EXT. eapply red_trans; [apply red_app; [apply red_app; [|apply r_refl]|apply r_refl]|exact Hv].
  eapply red_trans; [apply red_app; [exact Hd|apply r_refl]|exact Hy].
Qed.

Lemma kand_num w n (A : kprop) v : kand (kcode n) A w v -> R w (P1 v) (num n).
Proof. intros (_ & (a & Ha & [_ Han]) & _). eapply red_trans; [exact Ha|exact Han]. Qed.

Definition SP (P : tm) : tm := Lam (App (App P Zero) (Var 0)).
Arguments SP /.

Lemma SP_sim w α P : cpath kE α w P -> forall w' n, le w w' -> R w' (App (SP P) (num n)) (num (Nat.b2n (α n))).
Proof.
  intros HP w' n Hw. pose proof (proj1 (kp_good _ _ _ HP)) as CP.
  eapply r_step; [apply s_beta|]. bsimp. apply (kp_mono _ w w') in HP; [|exact Hw].
  exact (cfun_apply w' P (fun n => Nat.b2n (α n)) HP n).
Qed.

Lemma SP_good w P : good w P -> good w (SP P).
Proof. intros H. pose proof (proj1 H). good_tac. Qed.

Lemma SP_path w α P : cpath kE α w P -> cpath kE α w (Q (SP P)).
Proof. intros HP. apply Q_path; [apply SP_good, (kp_good _ _ _ HP)|apply SP_sim, HP]. Qed.

Lemma k_choice_at w x : SRC w x ->
  exists G : (nat -> bool) -> nat,
    (forall w' α P, le w w' -> cpath kE α w' P ->
       R w' (P1 (EXT (App (App x Zero) (Q (SP P))))) (num (G α))).
Proof.
  intros Hx. pose proof (kp_good _ _ _ Hx) as Hgx. pose proof (proj1 Hgx) as Cx.
  set (N := S (maxtag tag x)).
  set (T1 := fun α => P1 (EXT (App (App x Zero) (Q (Orc (snd (fresh w N α))))))).
  assert (HT : forall α, exists n, red (O (fst (fresh w N α))) (T1 α) (num n)).
  { intros α. destruct (use_src w x (fst (fresh w N α)) α (Q (Orc (snd (fresh w N α)))) Hx (fresh_le _ _ _))
      as (v & n & Hv & Hn).
    - apply Q_path; [apply (orc_good _ _ α), fresh_O|apply orc_sim, fresh_O].
    - exists n. eapply red_trans; [apply red_p1, Hv|exact (kand_num _ _ _ _ Hn)]. }
  exists (fun α => eval_num (O (fst (fresh w N α))) (T1 α) (HT α)).
  intros w' α P Hw HP.
  pose proof (eval_num_spec (O (fst (fresh w N α))) (T1 α) (HT α)) as Hspec.
  set (n := eval_num _ _ (HT α)) in *.
  set (w1 := fst (fresh w N α)) in *. set (c1 := snd (fresh w N α)) in *.
  assert (Hk : N <= tag c1) by apply fresh_tag. assert (Hc1 : O w1 c1 = Some α) by apply fresh_O.
  assert (Hw1 : le w w1) by apply fresh_le.
  destruct (replay tag (O w1) (tag c1) α (T1 α) _ Hspec) as [m Hm].
  { intros d Hd Ek. unfold T1, EXT in Hd. cbn in Hd.
    repeat match goal with H : _ \/ _ |- _ => destruct H as [H|H] end; try contradiction;
      [pose proof (occ_maxtag tag d x Hd); lia|subst; exact Hc1]. }
  pose proof (proj1 (kp_good _ _ _ HP)) as CP.
  assert (H2 := Hm (O w') (SP P)). unfold T1, EXT in H2. cbn [csub] in H2.
  rewrite csub_small in H2 by lia. change (snd (fresh w N α)) with c1 in H2.
  rewrite (csub_Q (tag c1) (SP P) c1 eq_refl), csub_num in H2.
  try rewrite (csub_id tag (tag c1) (SP P) (proj1_sig IDX)) in H2 by (intros c Hc; exfalso; eapply ev_noocc; exact Hc).
  apply H2.
  - intros d f Hd Ek Hf. unfold T1, EXT in Hd. cbn in Hd.
    repeat match goal with H : _ \/ _ |- _ => destruct H as [H|H] end; try contradiction;
      [exact (agree w w1 w' x Hgx Hw1 Hw d f Hd Hf)|subst; contradiction].
  - cbn. repeat split; auto with cl.
  - intros k0 _. apply (SP_sim w' α P HP), le_refl.
Qed.

Program Definition e_ch : ev :=
  Lam (App EXI (Pair
    (Lam (Lam (P1 (App (App (App (App (Var 2) Zero) (Lam (Lam (App (Lam (App (App (Var 3) Zero) (Var 0))) (Var 0))))) Zero) (proj1_sig IDX)))))
    (Lam (Lam (P2 (App (App (App (App (Var 2) Zero) (Lam (Lam (App (Lam (App (App (Var 3) Zero) (Var 0))) (Var 0))))) Zero) (proj1_sig IDX))))))).
Next Obligation. cl0_tac. Qed.

End Choice.

(** *** Extraction d'un chemin réalisé (pour la réfutation de WKL)

    Un réalisateur clos de ∃i. ⌜b_i⌝ ∧ ∀n. ⌜n⌝ ⊃ [P i n] donne, dans tout
    monde w, un indice i avec ∀n. P i n et un terme bien formé en w qui
    calcule b_i : un chemin réalisé est calculable avec les oracles de w. *)

Lemma ext_okI {I : Type} (f : I -> kprop) w y : fex (F := KF) f w y -> exists v i, R w (EXT y) v /\ f i w v.
Proof.
  intros [Hg Hy].
  set (Xi := {| kp := fun w t => good w t /\ exists i, f i w t;
                kp_mono := fun w w' t H Ht => conj (good_mono w w' t H (proj1 Ht))
                             (match proj2 Ht with ex_intro _ i Hi => ex_intro _ i (kp_mono _ _ _ _ H Hi) end);
                kp_good := fun w t H => proj1 H |} : kprop).
  destruct (Hy (fall_idx (F := KF) _ Xi)) as (b & Hb & Hbi).
  assert (HI : kall (fun i => kimp (f i) Xi) w (proj1_sig IDX)).
  { split; [cl0_tac|]. intros i. eexists. split; [apply red_one, s_beta|]. bsimp.
    split; [cl0_tac|]. intros w' _ a Ha. pose proof (proj1 (kp_good _ _ _ Ha)).
    exists a. split; [eapply r_step; [apply s_beta|]; bsimp; apply r_refl|].
    split; [exact (kp_good _ _ _ Ha)|exists i; exact Ha]. }
  destruct (proj2 Hbi w (le_refl w) _ (proj1 (kall_fall _ w _) HI)) as (v & Hv & _ & i & Hi).
  exists v, i. split; [|exact Hi]. unfold EXT. eapply red_trans; [apply red_app; [exact Hb|apply r_refl]|exact Hv].
Qed.

Theorem k_extract {I : Type} (b : I -> nat -> bool) (P : I -> nat -> Prop) e w :
  fent (F := KF) ftop e (fex (F := KF) (fun i => fand (F := KF) (cpath kE (b i))
                                          (fall (F := KF) (fun n => fimp (F := KF) (code (e := kE) n) (fprop_of (F := KF) (P i n)))))) ->
  exists i s, (forall n, P i n) /\ good w s /\ forall n, R w (App s (num n)) (num (Nat.b2n (b i n))).
Proof.
  intros He. destruct (He w Zero (conj Logic.I (fun c (H : occ c Zero) => match H with end))) as (v & _ & Hv).
  destruct (ext_okI _ w v Hv) as (v' & i & _ & Hi).
  destruct Hi as (_ & (a & _ & Ha) & (bb & _ & Hb)).
  exists i, (SP a). split; [|split].
  - intros n. destruct (proj2 (proj2 (kall_fall _ w bb) Hb) n) as (d & _ & Hd).
    destruct (proj2 Hd w (le_refl w) (num n) (num_code w n)) as (x & _ & Hx).
    exact (meta_true _ w x Hx).
  - exact (SP_good w a (kp_good _ _ _ Ha)).
  - intros n. exact (SP_sim w (b i) a Ha w n (le_refl w)).
Qed.

Lemma good_from w (t x : tm) : closed t -> (forall c, occ c t -> occ c x) -> good w x -> good w t.
Proof. intros Ct H [_ Hx]. split; [exact Ct|]. intros c Hc. apply Hx, H, Hc. Qed.

Ltac occ_x := intros ? Hc; cbn in Hc; repeat match goal with H : _ \/ _ |- _ => destruct H as [H|H] end;
  try contradiction; try (exfalso; eapply ev_noocc; exact Hc); try exact Hc.

Theorem k_choice : choice kE.
Proof.
  exists e_ch. intros φ. eapply rent_beta; [reflexivity|]. intros w x Hx0.
  pose proof (proj2 (kall_fall _ w x) Hx0) as Hx.
  pose proof (kp_good _ _ _ Hx) as Hgx. pose proof (proj1 Hgx) as Cx.
  destruct (k_choice_at φ w x Hx) as [G HG]. bsimp.
  set (A1 := Lam (Lam (P1 (App (App (App (App x Zero) (Lam (Lam (App (Lam (App (App (Var 3) Zero) (Var 0))) (Var 0))))) Zero) (proj1_sig IDX))))).
  set (A2 := Lam (Lam (P2 (App (App (App (App x Zero) (Lam (Lam (App (Lam (App (App (Var 3) Zero) (Var 0))) (Var 0))))) Zero) (proj1_sig IDX))))).
  assert (CA1 : closed A1) by (cbn; repeat split; try lia; eauto with cl).
  assert (CA2 : closed A2) by (cbn; repeat split; try lia; eauto with cl).
  assert (GA1 : good w A1) by (apply (good_from w A1 x CA1); [unfold A1; occ_x|exact Hgx]).
  assert (GA2 : good w A2) by (apply (good_from w A2 x CA2); [unfold A2; occ_x|exact Hgx]).
  assert (HA1 : cfun2 kE G w A1).
  { apply (proj1 (kall_fall _ w _)). split; [exact GA1|]. intros α. eexists. split; [apply red_one, s_beta|]. bsimp. split; [good_tac|].
    intros w' Hw P HP. pose proof (proj1 (kp_good _ _ _ HP)) as CP.
    exists (num (G α)). split; [|apply num_code].
    eapply r_step; [apply s_beta|]. bsimp. exact (HG w' α P Hw HP). }
  assert (HA2 : kall (fun α => kimp (cpath kE α) (φ α (G α))) w A2).
  { split; [exact GA2|]. intros α. eexists. split; [apply red_one, s_beta|]. bsimp. split; [good_tac|].
    intros w' Hw P HP. pose proof (proj1 (kp_good _ _ _ HP)) as CP.
    destruct (use_src φ w x w' α (Q (SP P)) Hx Hw (SP_path w' α P HP)) as (v & n & Hv & Hn).
    assert (n = G α) as ->.
    { apply (num_unique (O w') (P1 (EXT (App (App x Zero) (Q (SP P)))))).
      - eapply red_trans; [apply red_p1, Hv|exact (kand_num _ _ _ _ Hn)].
      - exact (HG w' α P Hw HP). }
    destruct Hn as (_ & _ & (r & Hr & Hri)). exists r. split; [|exact Hri].
    eapply r_step; [apply s_beta|]. bsimp. eapply red_trans; [apply red_p2, Hv|exact Hr]. }
  assert (Hpair : kand (cfun2 kE G) (kall (fun α => kimp (cpath kE α) (φ α (G α)))) w (Pair A1 A2)).
  { split; [good_tac|split].
    - exists A1. split; [apply red_one, s_p1|exact HA1].
    - exists A2. split; [apply red_one, s_p2|exact HA2]. }
  destruct (exi_ok (fun G => kand (cfun2 kE G) (kall (fun α => kimp (cpath kE α) (φ α (G α))))) G w _ Hpair)
    as (v & Hv & Hvi).
  exists v. split; [exact Hv|].
  refine (proj1 (fex_proper (F := KF) _ _ _ _ w v) Hvi).
  intros G' w' t'. apply kand_proper; [intros; reflexivity|apply kall_fall].
Qed.

(** ** Le modèle n'est pas dégénéré : ⊥ n'est pas réalisé *)

Definition kempty : kprop.
Proof. refine {| kp := fun _ _ => False |}; intros; contradiction. Defined.

Theorem k_consistent (w0 : W) : ~ exists e, fent (F := KF) ftop e fbot.
Proof.
  intros (e & He). destruct (He w0 Zero (conj Logic.I (fun c (H : occ c Zero) => match H with end))) as (v & _ & _ & Hv).
  destruct (Hv (fall_idx (F := KF) (fun φ => φ) kempty)) as (b & _ & []).
Qed.

(** ** FT est réalisé *)

Theorem kripke_hyps : search kE /\ choice kE /\ continuity kE.
Proof. exact (conj k_search (conj k_choice k_continuity)). Qed.

Theorem kripke_fan : WKL_meta -> MP_meta -> exists e, fent ftop e (FT kE).
Proof. intros WKL MP. exact (Robust.robust_fan_holds WKL MP kE k_search k_choice k_continuity). Qed.

End Kripke.
