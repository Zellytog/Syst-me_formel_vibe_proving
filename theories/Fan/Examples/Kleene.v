(** * Le théorème 29 : ESAT ne réalise pas WKL (modulo l'interpréteur universel)

    L'arbre de Kleene diagonalise contre les termes sans oracle : un mot ℓ
    est dans K si, pour tout e < |ℓ|, quand le e-ième terme appliqué à e se
    réduit en au plus |ℓ| pas vers un numéral v, ℓ(e) ≠ v. Les termes sont
    énumérés par [tm_of] (surjective), les réduits bornés calculés par
    [Reach.reach]. K est clos par préfixe ([K_prefix]) et a, pour tout n,
    un témoin ℓₙ de longueur n ([K_witness]).

    La seule hypothèse est [kleene_realized] : la famille des témoins est
    uniformément réalisée dans ESAT, ⊤ ≤ ∀n. ⌜n⌝ ⊃ ⌜ℓₙ⌝. Elle demande un
    λ-terme qui exécute les termes codés pendant n pas (un interpréteur
    universel), que l'on ne construit pas ici.

    Preuve ([esat_not_wkl]) : par [wkl_reduce], un réalisateur de WKL donne
    un réalisateur clos de ∃α. ⌜sg∘α⌝ ∧ ∀n. ⌜n⌝ ⊃ [K(α↾n)] ; dans le monde
    vide, [k_extract] en tire un chemin β = sg∘α dans K et un terme sans
    oracle qui calcule β ; ce terme est le e-ième pour un certain e, et
    β(e) contredit la diagonale. *)

From Stdlib Require Import List Arith Lia Bool Cantor.
Import ListNotations.
From SF.Models Require Import PSet Frame Tarski.
From SF.Logic Require Import Judgment Propositional.
From SF.Extensions Require Import Same.
From SF.HA Require Import Signature Model.
From SF.Fan Require Import Ent Statement Meta Terms FT WKL.
From SF.Fan.Examples Require Import Lam Confluence Reach Kripke Instances.

Set Universe Polymorphism.

Local Notation tmn := (tm nat).

(** ** Énumération des termes *)

Fixpoint terms (b k : nat) : list tmn :=
  match k with
  | 0 => []
  | S k =>
      let l := terms b k in
      map Var (seq 0 b) ++ [Zero] ++ map Orc (seq 0 b) ++ map Lam l ++ map Succ l ++ map P1 l ++ map P2 l
      ++ map (fun p => App (fst p) (snd p)) (list_prod l l)
      ++ map (fun p => Pair (fst p) (snd p)) (list_prod l l)
      ++ map (fun p => Rec (fst (fst p)) (snd (fst p)) (snd p)) (list_prod (list_prod l l) l)
  end.

Fixpoint depth (t : tmn) : nat :=
  match t with
  | Var _ | Zero | Orc _ => 1
  | Lam t | Succ t | P1 t | P2 t => S (depth t)
  | App t u | Pair t u => S (Nat.max (depth t) (depth u))
  | Rec t u v => S (Nat.max (depth t) (Nat.max (depth u) (depth v)))
  end.

Fixpoint bnd (t : tmn) : nat :=
  match t with
  | Var n | Orc n => S n
  | Zero => 0
  | Lam t | Succ t | P1 t | P2 t => bnd t
  | App t u | Pair t u => Nat.max (bnd t) (bnd u)
  | Rec t u v => Nat.max (bnd t) (Nat.max (bnd u) (bnd v))
  end.

Tactic Notation "br" int_or_var(j) := do j (apply in_or_app; right); try (apply in_or_app; left).

Lemma terms_complete (t : tmn) : forall b k, depth t <= k -> bnd t <= b -> In t (terms b k).
Proof.
  induction t as [n|t IH|t IHt u IHu|t IHt u IHu|t IH|t IH|
                  |t IH|t IHt u IHu v IHv|c]; intros b [|k] Hd Hb; cbn in Hd; try lia; cbn [terms].
  - apply in_or_app; left. apply in_map, in_seq. cbn in Hb. lia.
  - br 3. apply in_map, IH; cbn in *; lia.
  - br 7. apply (in_map (fun p => App (fst p) (snd p)) _ (t, u)), in_prod; [apply IHt|apply IHu]; cbn in *; lia.
  - br 8. apply (in_map (fun p => Pair (fst p) (snd p)) _ (t, u)), in_prod; [apply IHt|apply IHu]; cbn in *; lia.
  - br 5. apply in_map, IH; cbn in *; lia.
  - br 6. apply in_map, IH; cbn in *; lia.
  - br 1. left. reflexivity.
  - br 4. apply in_map, IH; cbn in *; lia.
  - br 9. apply (in_map (fun p => Rec (fst (fst p)) (snd (fst p)) (snd p)) _ ((t, u), v)).
    apply in_prod; [apply in_prod|]; [apply IHt|apply IHu|apply IHv]; cbn in *; lia.
  - br 2. apply in_map, in_seq. cbn in Hb. lia.
Qed.

Definition tm_of (n : nat) : tmn := let (p, i) := of_nat n in nth i (terms p p) Zero.

Lemma tm_of_surj (t : tmn) : exists n, tm_of n = t.
Proof.
  set (p := Nat.max (depth t) (bnd t)).
  assert (H : In t (terms p p)) by (apply terms_complete; lia).
  destruct (In_nth _ _ Zero H) as (i & _ & Hi).
  exists (to_nat (p, i)). unfold tm_of. rewrite cancel_of_to. exact Hi.
Qed.

(** ** L'arbre de Kleene *)

Definition O0 : nat -> option (nat -> bool) := esat_O [].

Definition diag (e : nat) : tmn := App (tm_of e) (num e).

Definition K (l : list nat) : Prop :=
  forall e v, e < length l -> In (num v) (reach O0 (length l) (diag e)) -> nth e l 0 <> v.

Definition lw (n e : nat) : bool :=
  (e <? n) && match find_num (reach O0 n (diag e)) with Some 0 => true | _ => false end.

Lemma reach_le s s' (t u : tmn) : s <= s' -> In u (reach O0 s t) -> In u (reach O0 s' t).
Proof. induction 1; [auto|]. intros Hr. apply reach_mono, IHle, Hr. Qed.

Lemma K_prefix l x : K (l ++ [x]) -> K l.
Proof.
  intros H e v He Hin. rewrite <- (app_nth1 l [x] 0 He). apply H.
  - rewrite length_app. cbn. lia.
  - rewrite length_app. cbn. apply (reach_le (length l)); [lia|exact Hin].
Qed.

Lemma nth_b2n_pre (b : nat -> bool) n e : e < n -> nth e (map Nat.b2n (pre b n)) 0 = Nat.b2n (b e).
Proof. intros He. change 0 with (Nat.b2n false). rewrite map_nth, nth_pre by exact He. reflexivity. Qed.

Lemma K_witness n : K (map Nat.b2n (pre (lw n) n)).
Proof.
  intros e v He Hin. rewrite length_map, length_pre in *. rewrite nth_b2n_pre by exact He.
  unfold lw. replace (e <? n) with true by (symmetry; apply Nat.ltb_lt, He). cbn [andb].
  destruct (find_num_complete _ _ Hin) as (m & Hm). rewrite Hm.
  assert (Ev : v = m).
  { apply (num_unique O0 (diag e)); apply (reach_sound O0 n); [exact Hin|apply find_num_spec, Hm]. }
  subst m. destruct v; cbn; lia.
Qed.

(** ** L'hypothèse : les témoins sont uniformément réalisés *)

Definition kleene_realized : Prop :=
  exists e, fent (F := ESAT) ftop e (fall (fun n => fimp (code (e := ESAT) n) (cpath ESAT (lw n)))).

(** ** Le théorème 29 *)

Theorem esat_not_wkl : kleene_realized ->
  ~ exists e, fent (F := ESAT) ftop e (sval (So ESAT) (Iy ESAT (dsc := dL)) (ltr (Rel (dsc := dL)) WKL) tt).
Proof.
  intros HU HW.
  destruct (wkl_reduce ESAT K lw K_prefix K_witness HU HW) as [e He].
  destruct (k_extract (list (nat -> bool)) prefix_le prefix_refl prefix_trans esat_O esat_mono
              (fun α => sgb ESAT α) (fun α n => K (map Nat.b2n (pre (sgb ESAT α) n))) e [] He)
    as (α & s & HK & [_ Hs] & Hcomp).
  set (β := sgb ESAT α) in *.
  destruct (tm_of_surj s) as (e0 & Ee0).
  destruct (reach_complete O0 _ _ (Hcomp e0)) as (k & Hk).
  set (N := S (Nat.max e0 k)).
  apply (HK N e0 (Nat.b2n (β e0))).
  - rewrite length_map, length_pre. lia.
  - rewrite length_map, length_pre. unfold diag. rewrite Ee0. apply (reach_le k); [lia|exact Hk].
  - apply nth_b2n_pre. lia.
Qed.

(** HA_ω^{ω,ω} + listes ne prouve pas WKL ; avec [esat_ft], ESAT sépare FT
    de WKL. *)
Corollary ha_not_proves_WKL : kleene_realized -> ~ provable (HA (dsc := dL)) [] [] WKL.
Proof.
  intros HU H. apply (esat_not_wkl HU). exact (ha_sound_closed ESAT (dsc := dL) WKL H).
Qed.

Corollary esat_separates : WKL_meta -> MP_meta -> kleene_realized ->
  (exists e, fent (F := ESAT) ftop e (sval (So ESAT) (Iy ESAT (dsc := dL)) (ltr (Rel (dsc := dL)) FT.FT) tt)) /\
  ~ exists e, fent (F := ESAT) ftop e (sval (So ESAT) (Iy ESAT (dsc := dL)) (ltr (Rel (dsc := dL)) WKL) tt).
Proof. intros WKL MP HU. exact (conj (esat_ft WKL MP) (esat_not_wkl HU)). Qed.
