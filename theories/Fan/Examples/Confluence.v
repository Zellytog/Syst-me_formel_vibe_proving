(** * Confluence du λ-calcul à oracles

    Méthode de Tait–Martin-Löf–Takahashi : réduction parallèle [par],
    développement complet [cd], et t ⇒ u implique u ⇒ cd(t). La règle des
    oracles ne crée pas de paire critique, car son argument est un numéral,
    forme normale. Conséquence utilisée partout : un terme se réduit vers au
    plus un numéral ([num_unique]). *)

From Stdlib Require Import List Arith Lia Bool.
From SF.Fan.Examples Require Import Lam.

Section Confluence.

Context {C : Type} (O : C -> option (nat -> bool)).

Local Notation tm := (tm C).

Fixpoint isnum (t : tm) : option nat :=
  match t with Zero => Some 0 | Succ t => option_map S (isnum t) | _ => None end.

Lemma isnum_num n : isnum (num n) = Some n.
Proof. induction n; cbn; [reflexivity|rewrite IHn; reflexivity]. Qed.

Lemma isnum_spec t n : isnum t = Some n -> t = num n.
Proof.
  revert n; induction t; intros m H; cbn in H; try discriminate.
  - injection H; intros <-; reflexivity.
  - destruct (isnum t) eqn:E; cbn in H; [|discriminate]. injection H; intros <-. cbn. f_equal. apply IHt; reflexivity.
Qed.

Inductive par : tm -> tm -> Prop :=
| p_var n : par (Var n) (Var n)
| p_zero : par Zero Zero
| p_orc c : par (Orc c) (Orc c)
| p_lam t t' : par t t' -> par (Lam t) (Lam t')
| p_app t t' u u' : par t t' -> par u u' -> par (App t u) (App t' u')
| p_pair t t' u u' : par t t' -> par u u' -> par (Pair t u) (Pair t' u')
| p_p1 t t' : par t t' -> par (P1 t) (P1 t')
| p_p2 t t' : par t t' -> par (P2 t) (P2 t')
| p_succ t t' : par t t' -> par (Succ t) (Succ t')
| p_rec t t' u u' v v' : par t t' -> par u u' -> par v v' -> par (Rec t u v) (Rec t' u' v')
| p_beta t t' u u' : par t t' -> par u u' -> par (App (Lam t) u) (beta t' u')
| p_pr1 t t' u : par t t' -> par (P1 (Pair t u)) t'
| p_pr2 t u u' : par u u' -> par (P2 (Pair t u)) u'
| p_rec0 t t' u : par t t' -> par (Rec t u Zero) t'
| p_recS t t' u u' v v' : par t t' -> par u u' -> par v v' ->
    par (Rec t u (Succ v)) (App (App u' v') (Rec t' u' v'))
| p_orcr c f n : O c = Some f -> par (App (Orc c) (num n)) (num (Nat.b2n (f n))).

Lemma par_refl (t : tm) : par t t.
Proof. induction t; constructor; auto. Qed.

Lemma par_num n (u : tm) : par (num n) u -> u = num n.
Proof.
  revert u; induction n; intros u H; cbn in H; inversion H; subst; [reflexivity|].
  cbn. f_equal. apply IHn. assumption.
Qed.

Lemma step_par (t u : tm) : step O t u -> par t u.
Proof. induction 1; try (constructor; auto using par_refl); econstructor; eauto using par_refl. Qed.

Lemma par_red (t u : tm) : par t u -> red O t u.
Proof.
  induction 1; auto using r_refl, red_lam, red_app, red_pair, red_p1, red_p2, red_succ, red_rec.
  - eapply red_trans; [apply red_app; [apply red_lam; eassumption|eassumption]|]. apply red_one, s_beta.
  - eapply red_trans; [apply red_p1, red_pair; [eassumption|apply r_refl]|]. apply red_one, s_p1.
  - eapply red_trans; [apply red_p2, red_pair; [apply r_refl|eassumption]|]. apply red_one, s_p2.
  - eapply red_trans; [apply red_rec; [eassumption|apply r_refl|apply r_refl]|]. apply red_one, s_rec0.
  - eapply red_trans; [apply red_rec; [eassumption|eassumption|apply red_succ; eassumption]|].
    apply red_one, s_recS.
  - apply red_one, s_orc; assumption.
Qed.

(** ** Renommage et substitution *)

Lemma ren_num ξ n : ren ξ (num (C := C) n) = num n.
Proof. induction n; cbn; congruence. Qed.

Lemma subst_num (σ : nat -> tm) n : subst σ (num n) = num n.
Proof. induction n; cbn; congruence. Qed.

Lemma ren_beta ξ (t u : tm) : ren ξ (beta t u) = beta (ren (upr ξ) t) (ren ξ u).
Proof.
  unfold beta. rewrite ren_subst, subst_ren. apply subst_ext. intros [|n]; reflexivity.
Qed.

Lemma subst_beta (σ : nat -> tm) (t u : tm) : subst σ (beta t u) = beta (subst (ups σ) t) (subst σ u).
Proof.
  unfold beta. rewrite !subst_subst. apply subst_ext. intros [|n]; cbn; [reflexivity|].
  rewrite subst_ren. cbn. rewrite subst_var. reflexivity.
Qed.

Lemma par_ren ξ (t t' : tm) : par t t' -> par (ren ξ t) (ren ξ t').
Proof.
  intros H; revert ξ; induction H; intros ξ; cbn; try (constructor; auto).
  - rewrite ren_beta. constructor; auto.
  - rewrite ren_num, ren_num. constructor. assumption.
Qed.

Lemma par_ups (σ σ' : nat -> tm) : (forall n, par (σ n) (σ' n)) -> forall n, par (ups σ n) (ups σ' n).
Proof. intros H [|n]; cbn; [constructor|apply par_ren, H]. Qed.

Lemma par_subst (σ σ' : nat -> tm) (t t' : tm) : par t t' -> (forall n, par (σ n) (σ' n)) -> par (subst σ t) (subst σ' t').
Proof.
  intros H; revert σ σ'; induction H; intros σ σ' Hs; cbn; try (constructor; auto using par_ups).
  - apply Hs.
  - rewrite subst_beta. constructor; auto using par_ups.
  - rewrite subst_num, subst_num. constructor. assumption.
Qed.

Lemma par_beta (t t' u u' : tm) : par t t' -> par u u' -> par (beta t u) (beta t' u').
Proof. intros H1 H2. apply par_subst; [exact H1|]. intros [|n]; cbn; [exact H2|constructor]. Qed.

(** ** Développement complet *)

Fixpoint cd (t : tm) : tm :=
  match t with
  | Var n => Var n
  | Zero => Zero
  | Orc c => Orc c
  | Lam t => Lam (cd t)
  | App t u =>
      match t with
      | Lam b => beta (cd b) (cd u)
      | Orc c =>
          match isnum u, O c with
          | Some n, Some f => num (Nat.b2n (f n))
          | _, _ => App (Orc c) (cd u)
          end
      | _ => App (cd t) (cd u)
      end
  | Pair t u => Pair (cd t) (cd u)
  | P1 t => match t with Pair a _ => cd a | _ => P1 (cd t) end
  | P2 t => match t with Pair _ b => cd b | _ => P2 (cd t) end
  | Succ t => Succ (cd t)
  | Rec t u v =>
      match v with
      | Zero => cd t
      | Succ w => App (App (cd u) (cd w)) (Rec (cd t) (cd u) (cd w))
      | _ => Rec (cd t) (cd u) (cd v)
      end
  end.

Lemma par_cd (t u : tm) : par t u -> par u (cd t).
Proof.
  induction 1; cbn; try assumption; try (constructor; auto; fail).
  - (* App *)
    destruct t as [| b | | | | | | | |c]; try (constructor; auto; fail).
    + inversion H; subst. inversion IHpar1; subst. constructor; assumption.
    + inversion H; subst. destruct (isnum u) eqn:Eu; [destruct (O c) eqn:Ec|].
      * apply isnum_spec in Eu; subst. apply par_num in H0; subst. constructor. assumption.
      * constructor; auto.
      * constructor; auto.
  - (* P1 *)
    destruct t; try (constructor; auto; fail).
    inversion H; subst. inversion IHpar; subst. apply p_pr1. assumption.
  - (* P2 *)
    destruct t; try (constructor; auto; fail).
    inversion H; subst. inversion IHpar; subst. apply p_pr2. assumption.
  - (* Rec *)
    destruct v; try (constructor; auto; fail).
    + inversion H1; subst. apply p_rec0. assumption.
    + inversion H1; subst. inversion IHpar3; subst. apply p_recS; assumption.
  - (* β *)
    apply par_beta; assumption.
  - (* recS *)
    constructor; [constructor|constructor]; assumption.
  - (* oracle *)
    rewrite isnum_num, H. apply par_refl.
Qed.

Lemma par_diamond (t u v : tm) : par t u -> par t v -> exists w, par u w /\ par v w.
Proof. intros H1 H2. exists (cd t). split; apply par_cd; assumption. Qed.

(** ** Confluence *)

Inductive pstar : tm -> tm -> Prop :=
| ps_refl t : pstar t t
| ps_step t u v : par t u -> pstar u v -> pstar t v.

Lemma red_pstar (t u : tm) : red O t u -> pstar t u.
Proof. induction 1; [constructor|econstructor; [apply step_par; eassumption|assumption]]. Qed.

Lemma pstar_red (t u : tm) : pstar t u -> red O t u.
Proof. induction 1; [apply r_refl|eapply red_trans; [apply par_red; eassumption|assumption]]. Qed.

Lemma strip (t u v : tm) : par t u -> pstar t v -> exists w, pstar u w /\ par v w.
Proof.
  intros H1 H2; revert u H1; induction H2 as [t|t t' v H H' IH]; intros u Hu.
  - exists u. split; [constructor|assumption].
  - destruct (par_diamond _ _ _ Hu H) as (w & Hw1 & Hw2).
    destruct (IH w Hw2) as (z & Hz1 & Hz2). exists z. split; [econstructor; eassumption|assumption].
Qed.

Theorem confluence (t u v : tm) : red O t u -> red O t v -> exists w, red O u w /\ red O v w.
Proof.
  intros H1 H2. apply red_pstar in H1, H2. revert v H2.
  induction H1 as [t|t t' u H H' IH]; intros v Hv.
  - exists v. split; [apply pstar_red; assumption|apply r_refl].
  - destruct (strip _ _ _ H Hv) as (w & Hw1 & Hw2).
    destruct (IH w Hw1) as (z & Hz1 & Hz2). exists z. split; [assumption|].
    eapply red_trans; [apply par_red; eassumption|assumption].
Qed.

Lemma red_num n (u : tm) : red O (num n) u -> u = num n.
Proof.
  intros H. apply red_pstar in H. remember (num n) as a eqn:Ea.
  induction H as [t|t t' v H _ IH]; subst; [reflexivity|].
  apply par_num in H; subst. apply IH; reflexivity.
Qed.

Theorem num_unique (t : tm) n m : red O t (num n) -> red O t (num m) -> n = m.
Proof.
  intros H1 H2. destruct (confluence _ _ _ H1 H2) as (w & Hw1 & Hw2).
  apply red_num in Hw1, Hw2. rewrite Hw1 in Hw2. exact (num_inj (C := C) _ _ Hw2).
Qed.

End Confluence.
