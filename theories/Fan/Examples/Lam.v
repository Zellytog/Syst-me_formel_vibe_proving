(** * Le λ-calcul à oracles (« Oracles just for Fan », définitions 6 et 9)

    Termes de de Bruijn : variables, λ, application, couples et projections,
    0, S, récurseur recNat, et des *oracles* Orc c, pour c dans un ensemble
    de constantes C. La réduction est paramétrée par une interprétation des
    constantes O : C → option (N → B) ; la règle des oracles est
    c n̄ ↦ b̄ où b = O(c)(n) (codé 0/1). Les booléens et les listes de
    l'article ne servent pas ici et sont omis.

    Outils : renommages et substitutions parallèles avec leurs lois, termes
    clos ([wf]), occurrences de constantes, *substitution d'une constante
    par un terme* ([csub], étiquetée par un entier [tag]) qui commute aux
    substitutions, congruences et monotonie de la réduction. *)

From Stdlib Require Import List Arith Lia Bool.
Import ListNotations.

Section Lam.

Context {C : Type}.

Inductive tm : Type :=
| Var (n : nat)
| Lam (t : tm)
| App (t u : tm)
| Pair (t u : tm)
| P1 (t : tm)
| P2 (t : tm)
| Zero
| Succ (t : tm)
| Rec (t u v : tm)
| Orc (c : C).

(** ** Renommages et substitutions *)

Definition upr (ξ : nat -> nat) : nat -> nat := fun n => match n with 0 => 0 | S n => S (ξ n) end.

Fixpoint ren (ξ : nat -> nat) (t : tm) : tm :=
  match t with
  | Var n => Var (ξ n)
  | Lam t => Lam (ren (upr ξ) t)
  | App t u => App (ren ξ t) (ren ξ u)
  | Pair t u => Pair (ren ξ t) (ren ξ u)
  | P1 t => P1 (ren ξ t)
  | P2 t => P2 (ren ξ t)
  | Zero => Zero
  | Succ t => Succ (ren ξ t)
  | Rec t u v => Rec (ren ξ t) (ren ξ u) (ren ξ v)
  | Orc c => Orc c
  end.

Definition ups (σ : nat -> tm) : nat -> tm := fun n => match n with 0 => Var 0 | S n => ren S (σ n) end.

Fixpoint subst (σ : nat -> tm) (t : tm) : tm :=
  match t with
  | Var n => σ n
  | Lam t => Lam (subst (ups σ) t)
  | App t u => App (subst σ t) (subst σ u)
  | Pair t u => Pair (subst σ t) (subst σ u)
  | P1 t => P1 (subst σ t)
  | P2 t => P2 (subst σ t)
  | Zero => Zero
  | Succ t => Succ (subst σ t)
  | Rec t u v => Rec (subst σ t) (subst σ u) (subst σ v)
  | Orc c => Orc c
  end.

Definition scons (u : tm) (σ : nat -> tm) : nat -> tm := fun n => match n with 0 => u | S n => σ n end.
Definition beta (t u : tm) : tm := subst (scons u Var) t.

Lemma ren_ext ξ ζ t : (forall n, ξ n = ζ n) -> ren ξ t = ren ζ t.
Proof.
  revert ξ ζ; induction t; intros ξ ζ H; cbn; f_equal; auto.
  apply IHt. intros [|n]; cbn; [reflexivity|f_equal; apply H].
Qed.

Lemma subst_ext σ τ t : (forall n, σ n = τ n) -> subst σ t = subst τ t.
Proof.
  revert σ τ; induction t; intros σ τ H; cbn; f_equal; auto.
  apply IHt. intros [|n]; cbn; [reflexivity|f_equal; apply H].
Qed.

Lemma ren_ren ξ ζ t : ren ξ (ren ζ t) = ren (fun n => ξ (ζ n)) t.
Proof.
  revert ξ ζ; induction t; intros ξ ζ; cbn; f_equal; auto.
  rewrite IHt. apply ren_ext. intros [|n]; reflexivity.
Qed.

Lemma subst_ren σ ξ t : subst σ (ren ξ t) = subst (fun n => σ (ξ n)) t.
Proof.
  revert σ ξ; induction t; intros σ ξ; cbn; f_equal; auto.
  rewrite IHt. apply subst_ext. intros [|n]; reflexivity.
Qed.

Lemma ren_subst ξ σ t : ren ξ (subst σ t) = subst (fun n => ren ξ (σ n)) t.
Proof.
  revert ξ σ; induction t; intros ξ σ; cbn; f_equal; auto.
  rewrite IHt. apply subst_ext. intros [|n]; cbn; [reflexivity|].
  rewrite !ren_ren. apply ren_ext. reflexivity.
Qed.

Lemma subst_subst τ σ t : subst τ (subst σ t) = subst (fun n => subst τ (σ n)) t.
Proof.
  revert τ σ; induction t; intros τ σ; cbn; f_equal; auto.
  rewrite IHt. apply subst_ext. intros [|n]; cbn; [reflexivity|].
  rewrite ren_subst, subst_ren. apply subst_ext. reflexivity.
Qed.

Lemma subst_var t : subst Var t = t.
Proof.
  enough (H : forall σ, (forall n, σ n = Var n) -> subst σ t = t) by (apply H; reflexivity).
  induction t; intros σ H; cbn; f_equal; auto.
  apply IHt. intros [|n]; cbn; [reflexivity|]. rewrite H. reflexivity.
Qed.

(** ** Termes clos *)

Fixpoint wf (k : nat) (t : tm) : Prop :=
  match t with
  | Var n => n < k
  | Lam t => wf (S k) t
  | App t u | Pair t u => wf k t /\ wf k u
  | P1 t | P2 t | Succ t => wf k t
  | Zero | Orc _ => True
  | Rec t u v => wf k t /\ wf k u /\ wf k v
  end.

Definition closed (t : tm) : Prop := wf 0 t.

Lemma wf_ren k k' ξ t : wf k t -> (forall n, n < k -> ξ n < k') -> wf k' (ren ξ t).
Proof.
  revert k k' ξ; induction t; intros k k' ξ Ht H; cbn in *; intuition eauto.
  apply (IHt (S k)); [exact Ht|]. intros [|n] Hn; cbn; [lia|]. specialize (H n). lia.
Qed.

Lemma wf_subst k k' σ t : wf k t -> (forall n, n < k -> wf k' (σ n)) -> wf k' (subst σ t).
Proof.
  revert k k' σ; induction t; intros k k' σ Ht H; cbn in *; intuition eauto.
  apply (IHt (S k)); [exact Ht|]. intros [|n] Hn; cbn; [lia|].
  apply (wf_ren k'); [apply H; lia|lia].
Qed.

Lemma wf_mono k k' t : wf k t -> k <= k' -> wf k' t.
Proof.
  intros H Hk. rewrite <- (subst_var t). apply (wf_subst k); [exact H|]. intros n Hn; cbn; lia.
Qed.

Lemma subst_wf_id k σ t : wf k t -> (forall n, n < k -> σ n = Var n) -> subst σ t = t.
Proof.
  revert k σ; induction t; intros k σ Ht H; cbn in *; f_equal; intuition eauto.
  apply (IHt (S k)); [exact Ht|]. intros [|n] Hn; cbn; [reflexivity|]. rewrite H by lia. reflexivity.
Qed.

Lemma ren_wf_id k ξ t : wf k t -> (forall n, n < k -> ξ n = n) -> ren ξ t = t.
Proof.
  revert k ξ; induction t; intros k ξ Ht H; cbn in *; f_equal; intuition eauto.
  apply (IHt (S k)); [exact Ht|]. intros [|n] Hn; cbn; [reflexivity|]. rewrite H by lia. reflexivity.
Qed.

Lemma subst_closed σ t : closed t -> subst σ t = t.
Proof. intros H. apply (subst_wf_id 0); [exact H|lia]. Qed.

Lemma ren_closed ξ t : closed t -> ren ξ t = t.
Proof. intros H. apply (ren_wf_id 0); [exact H|lia]. Qed.

Lemma wf_beta k t u : wf (S k) t -> wf k u -> wf k (beta t u).
Proof. intros Ht Hu. apply (wf_subst (S k)); [exact Ht|]. intros [|n] Hn; cbn; [exact Hu|lia]. Qed.

(** ** Numéraux *)

Fixpoint num (n : nat) : tm := match n with 0 => Zero | S n => Succ (num n) end.

Lemma num_closed n : closed (num n).
Proof. induction n; cbn; auto. Qed.

Lemma num_inj n m : num n = num m -> n = m.
Proof. revert m; induction n; intros [|m] H; cbn in H; try discriminate; auto. injection H; auto. Qed.

(** ** Constantes *)

Fixpoint occ (c : C) (t : tm) : Prop :=
  match t with
  | Var _ | Zero => False
  | Lam t | P1 t | P2 t | Succ t => occ c t
  | App t u | Pair t u => occ c t \/ occ c u
  | Rec t u v => occ c t \/ occ c u \/ occ c v
  | Orc d => d = c
  end.

Lemma occ_num c n : ~ occ c (num n).
Proof. induction n; cbn; auto. Qed.

Lemma occ_ren c ξ t : occ c (ren ξ t) -> occ c t.
Proof. revert ξ; induction t; intros ξ; cbn; intuition eauto. Qed.

Lemma occ_subst c σ t : occ c (subst σ t) -> occ c t \/ exists n, occ c (σ n).
Proof.
  revert σ; induction t; intros σ H; cbn in *; try tauto.
  - right; exists n; exact H.
  - destruct (IHt _ H) as [|(n & Hn)]; [left; exact H0|].
    destruct n; cbn in Hn; [contradiction|right; exists n; exact (occ_ren _ _ _ Hn)].
  - destruct H as [H|H]; [destruct (IHt1 _ H)|destruct (IHt2 _ H)]; tauto.
  - destruct H as [H|H]; [destruct (IHt1 _ H)|destruct (IHt2 _ H)]; tauto.
  - destruct (IHt _ H); tauto.
  - destruct (IHt _ H); tauto.
  - destruct (IHt _ H); tauto.
  - destruct H as [H|[H|H]]; [destruct (IHt1 _ H)|destruct (IHt2 _ H)|destruct (IHt3 _ H)]; tauto.
Qed.

Lemma occ_beta c t u : occ c (beta t u) -> occ c t \/ occ c u.
Proof.
  intros H. destruct (occ_subst _ _ _ H) as [|(n & Hn)]; [left; exact H0|].
  destruct n; cbn in Hn; [right; exact Hn|contradiction].
Qed.

Section Tags.
Context (tag : C -> nat).

Fixpoint maxtag (t : tm) : nat :=
  match t with
  | Var _ | Zero => 0
  | Lam t | P1 t | P2 t | Succ t => maxtag t
  | App t u | Pair t u => Nat.max (maxtag t) (maxtag u)
  | Rec t u v => Nat.max (maxtag t) (Nat.max (maxtag u) (maxtag v))
  | Orc d => tag d
  end.

Lemma occ_maxtag c t : occ c t -> tag c <= maxtag t.
Proof. induction t; cbn; intros H; try contradiction; intuition (subst; lia). Qed.

(** Substitution des constantes d'étiquette k par le terme s. *)
Fixpoint csub (k : nat) (s : tm) (t : tm) : tm :=
  match t with
  | Var n => Var n
  | Lam t => Lam (csub k s t)
  | App t u => App (csub k s t) (csub k s u)
  | Pair t u => Pair (csub k s t) (csub k s u)
  | P1 t => P1 (csub k s t)
  | P2 t => P2 (csub k s t)
  | Zero => Zero
  | Succ t => Succ (csub k s t)
  | Rec t u v => Rec (csub k s t) (csub k s u) (csub k s v)
  | Orc d => if tag d =? k then s else Orc d
  end.

Lemma csub_num k s n : csub k s (num n) = num n.
Proof. induction n; cbn; congruence. Qed.

Lemma csub_ren k s ξ t : closed s -> csub k s (ren ξ t) = ren ξ (csub k s t).
Proof.
  intros Hs. revert ξ; induction t; intros ξ; cbn; f_equal; auto.
  match goal with |- context [tag ?d =? k] => destruct (tag d =? k) end; [symmetry; apply ren_closed, Hs|reflexivity].
Qed.

Lemma csub_subst k s σ t : closed s -> csub k s (subst σ t) = subst (fun n => csub k s (σ n)) (csub k s t).
Proof.
  intros Hs. revert σ; induction t; intros σ; cbn; f_equal; auto.
  - rewrite IHt. apply subst_ext. intros [|n]; cbn; [reflexivity|]. apply csub_ren, Hs.
  - match goal with |- context [tag ?d =? k] => destruct (tag d =? k) end; [symmetry; apply subst_closed, Hs|reflexivity].
Qed.

Lemma csub_beta k s t u : closed s -> csub k s (beta t u) = beta (csub k s t) (csub k s u).
Proof.
  intros Hs. unfold beta. rewrite csub_subst by exact Hs. apply subst_ext. intros [|n]; reflexivity.
Qed.

Lemma csub_id k s t : (forall c, occ c t -> tag c <> k) -> csub k s t = t.
Proof.
  induction t as [n|t IH|t IH1 u IH2|t IH1 u IH2|t IH|t IH| |t IH|t IH1 u IH2 v IH3|d]; cbn; intros H;
    try reflexivity;
    try (rewrite IH by (intros; apply H; tauto); reflexivity);
    try (rewrite IH1, IH2 by (intros; apply H; tauto); reflexivity).
  - rewrite IH1, IH2, IH3 by (intros; apply H; tauto); reflexivity.
  - destruct (Nat.eqb_spec (tag d) k) as [e|]; [exfalso; exact (H d eq_refl e)|reflexivity].
Qed.

Lemma wf_csub k0 k s t : closed s -> wf k0 t -> wf k0 (csub k s t).
Proof.
  intros Hs. revert k0; induction t; intros k0 H; cbn in *; intuition auto.
  match goal with |- context [tag ?d =? k] => destruct (tag d =? k) end; [apply (wf_mono 0); [exact Hs|lia]|exact Logic.I].
Qed.

Lemma occ_csub c k s t : occ c (csub k s t) -> (occ c t /\ tag c <> k) \/ occ c s.
Proof.
  induction t as [n|t IH|t IH1 u IH2|t IH1 u IH2|t IH|t IH| |t IH|t IH1 u IH2 v IH3|d]; cbn; intros H.
  - contradiction.
  - exact (IH H).
  - destruct H as [H|H]; [destruct (IH1 H)|destruct (IH2 H)]; tauto.
  - destruct H as [H|H]; [destruct (IH1 H)|destruct (IH2 H)]; tauto.
  - exact (IH H).
  - exact (IH H).
  - contradiction.
  - exact (IH H).
  - destruct H as [H|[H|H]]; [destruct (IH1 H)|destruct (IH2 H)|destruct (IH3 H)]; tauto.
  - destruct (Nat.eqb_spec (tag d) k); [right; exact H|left; cbn in H; subst; split; auto].
Qed.

End Tags.

(** ** Réduction *)

Section Red.

Context (O : C -> option (nat -> bool)).

Inductive step : tm -> tm -> Prop :=
| s_beta t u : step (App (Lam t) u) (beta t u)
| s_p1 t u : step (P1 (Pair t u)) t
| s_p2 t u : step (P2 (Pair t u)) u
| s_rec0 t u : step (Rec t u Zero) t
| s_recS t u v : step (Rec t u (Succ v)) (App (App u v) (Rec t u v))
| s_orc c f n : O c = Some f -> step (App (Orc c) (num n)) (num (Nat.b2n (f n)))
| s_lam t t' : step t t' -> step (Lam t) (Lam t')
| s_appl t t' u : step t t' -> step (App t u) (App t' u)
| s_appr t u u' : step u u' -> step (App t u) (App t u')
| s_pairl t t' u : step t t' -> step (Pair t u) (Pair t' u)
| s_pairr t u u' : step u u' -> step (Pair t u) (Pair t u')
| s_p1c t t' : step t t' -> step (P1 t) (P1 t')
| s_p2c t t' : step t t' -> step (P2 t) (P2 t')
| s_succ t t' : step t t' -> step (Succ t) (Succ t')
| s_rec1 t t' u v : step t t' -> step (Rec t u v) (Rec t' u v)
| s_rec2 t u u' v : step u u' -> step (Rec t u v) (Rec t u' v)
| s_rec3 t u v v' : step v v' -> step (Rec t u v) (Rec t u v').

Inductive red : tm -> tm -> Prop :=
| r_refl t : red t t
| r_step t u v : step t u -> red u v -> red t v.

Lemma red_one t u : step t u -> red t u.
Proof. intros H. eapply r_step; [exact H|apply r_refl]. Qed.

Lemma red_trans t u v : red t u -> red u v -> red t v.
Proof. induction 1; intros; [assumption|eapply r_step; eauto]. Qed.

Lemma red_ctx (f : tm -> tm) : (forall t t', step t t' -> step (f t) (f t')) ->
  forall t t', red t t' -> red (f t) (f t').
Proof. intros Hf t t' H; induction H; [apply r_refl|eapply r_step; [apply Hf; eassumption|assumption]]. Qed.

Lemma red_lam t t' : red t t' -> red (Lam t) (Lam t').
Proof. apply red_ctx. intros; constructor; auto. Qed.
Lemma red_app t t' u u' : red t t' -> red u u' -> red (App t u) (App t' u').
Proof.
  intros H1 H2. eapply red_trans.
  - apply (red_ctx (fun x => App x u)); [intros; constructor; auto|exact H1].
  - apply (red_ctx (fun x => App t' x)); [intros; constructor; auto|exact H2].
Qed.
Lemma red_pair t t' u u' : red t t' -> red u u' -> red (Pair t u) (Pair t' u').
Proof.
  intros H1 H2. eapply red_trans.
  - apply (red_ctx (fun x => Pair x u)); [intros; constructor; auto|exact H1].
  - apply (red_ctx (fun x => Pair t' x)); [intros; constructor; auto|exact H2].
Qed.
Lemma red_p1 t t' : red t t' -> red (P1 t) (P1 t').
Proof. apply red_ctx. intros; constructor; auto. Qed.
Lemma red_p2 t t' : red t t' -> red (P2 t) (P2 t').
Proof. apply red_ctx. intros; constructor; auto. Qed.
Lemma red_succ t t' : red t t' -> red (Succ t) (Succ t').
Proof. apply red_ctx. intros; constructor; auto. Qed.
Lemma red_rec t t' u u' v v' : red t t' -> red u u' -> red v v' -> red (Rec t u v) (Rec t' u' v').
Proof.
  intros H1 H2 H3. eapply red_trans; [|eapply red_trans].
  - apply (red_ctx (fun x => Rec x u v)); [intros; constructor; auto|exact H1].
  - apply (red_ctx (fun x => Rec t' x v)); [intros; constructor; auto|exact H2].
  - apply (red_ctx (fun x => Rec t' u' x)); [intros; constructor; auto|exact H3].
Qed.

Lemma red_succ_num t n : red t (num n) -> red (Succ t) (num (S n)).
Proof. apply red_succ. Qed.

Lemma step_wf k t u : step t u -> wf k t -> wf k u.
Proof.
  intros H; revert k; induction H; intros k Hw; cbn in *; intuition auto.
  - apply wf_beta; assumption.
  - apply (wf_mono 0); [apply num_closed|lia].
Qed.

Lemma red_wf k t u : red t u -> wf k t -> wf k u.
Proof. induction 1; intros; eauto using step_wf. Qed.

Lemma step_occ c t u : step t u -> occ c u -> occ c t.
Proof.
  induction 1; cbn; intros Ho; try tauto.
  - destruct (occ_beta _ _ _ Ho); tauto.
  - exfalso; exact (occ_num _ _ Ho).
Qed.

Lemma red_occ c t u : red t u -> occ c u -> occ c t.
Proof. induction 1; intros; eauto using step_occ. Qed.

End Red.

(** Monotonie en l'interprétation des oracles. *)
Lemma step_mono (O O' : C -> option (nat -> bool)) t u :
  (forall c f, O c = Some f -> O' c = Some f) -> step O t u -> step O' t u.
Proof. intros HO H; induction H; constructor; auto. Qed.

Lemma red_mono (O O' : C -> option (nat -> bool)) t u :
  (forall c f, O c = Some f -> O' c = Some f) -> red O t u -> red O' t u.
Proof. intros HO H; induction H; [apply r_refl|eapply r_step; [eapply step_mono|]; eauto]. Qed.

End Lam.

Arguments tm C : clear implicits.
