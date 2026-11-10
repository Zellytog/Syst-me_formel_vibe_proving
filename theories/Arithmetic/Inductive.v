(** * Types inductifs à arités finies

    Une signature à types inductifs contient, pour chaque indice i d'un
    type [Ind], une sorte Wᵢ décrite par une liste de constructeurs ; un
    constructeur est une liste de booléens : [true] pour un paramètre de
    sorte N, [false] pour un argument récursif de sorte Wᵢ. Exemples :
    - les listes d'entiers : [[]; [true; false]] (nil, cons) ;
    - les booléens : [[]; []] ;
    - les arbres binaires étiquetés : [[true]; [false; true; false]].

    Symboles :
    - les constructeurs c : [args] → Wᵢ ;
    - les récurseurs rec_{i,s} : [Wᵢ, pas₁, …, pasₙ] → s, pour les sortes s
      autorisées par la borne [r] (comme [rec_s], fichier [Arith.v]) ; le
      pas d'un constructeur reçoit, pour chaque argument récursif, le
      sous-terme y et la valeur de l'appel récursif sur y.

    Règles :
    - de calcul ([wrec_rules]) : rec(c(x⃗), pas⃗) ~ pas_c(x⃗, rec(y⃗)) ;
    - de déduction : la récurrence sur Wᵢ ([wind_rules]) et, pour la
      version « équationnelle », les mêmes équations comme règles
      ([weq_rules]) : ⊢ rec(c(x⃗), pas⃗) = pas_c(x⃗, rec(y⃗)). *)

From Stdlib Require Import List.
Import ListNotations.
From SF.Syntax Require Import Spec Terms Renaming Traversal Eta Composition Vectors.
From SF.Calculus Require Import System Rules.
From SF.Logic Require Import Judgment Propositional.
From SF.Functional Require Import Arrow Graded.
From SF.Quantifiers Require Import Quant.
From SF.Arithmetic Require Import Arith.

Local Notation ι a := (Spec [] a).

(** ** Appartenance à une liste, avec position *)

Inductive mem {A : Type} : list A -> A -> Type :=
| mz {a l} : mem (a :: l) a
| ms {a b l} : mem l a -> mem (b :: l) a.

Fixpoint mvar {A Srt} (f : A -> spec Srt) {l a} (m : mem l a) : var (map f l) (f a) :=
  match m in mem l0 a0 return var (map f l0) (f a0) with
  | mz => vz
  | ms m' => vs (mvar f m')
  end.

Fixpoint mindex {A} {l : list A} {a} (m : mem l a) : nat :=
  match m with mz => 0 | ms m' => S (mindex m') end.

Fixpoint mems {A} (l : list A) : list {a & mem l a} :=
  match l as l0 return list {a & mem l0 a} with
  | [] => []
  | a :: l' => existT _ a mz :: map (fun p => existT (fun x => mem (a :: l') x) (projT1 p) (ms (projT2 p))) (mems l')
  end.

Lemma mems_complete {A} (l : list A) a (m : mem l a) : In (existT _ a m) (mems l).
Proof.
  induction m as [a l|a b l m IH]; cbn; [left; reflexivity|right].
  apply (in_map (fun p => existT (fun x => mem (b :: l) x) (projT1 p) (ms (projT2 p))) _ _ IH).
Qed.

Lemma mindex_lt {A} {l : list A} {a} (m : mem l a) : mindex m < length l.
Proof. induction m; cbn; [apply PeanoNat.Nat.lt_0_succ|apply (proj1 (PeanoNat.Nat.succ_lt_mono _ _)); assumption]. Qed.

Lemma mindex_nth {A} {l : list A} {a} (m : mem l a) d : nth (mindex m) l d = a.
Proof. induction m; cbn; [reflexivity|assumption]. Qed.

(** ** Les symboles *)

Section Inductive.
Context {Srt : Type} (Sym : spec Srt -> Type) `{Functional Srt Sym} {G : Graded Sym}.
Context (N : Srt) (r : bound) {Ind : Type} (W : Ind -> Srt) (dsc : Ind -> list (list bool)).

Local Notation tm := (Terms.tm Sym).
Local Notation args := (Terms.args Sym).

Definition asrt i (b : bool) : Srt := if b then N else W i.

(** Les arguments d'un constructeur. *)
Definition cargs i (bs : list bool) : ctx Srt := map (fun b => ι (asrt i b)) bs.

(** Les arguments du pas d'un constructeur : chaque argument récursif est
    suivi de la valeur de l'appel récursif. *)
Fixpoint sargs i s (bs : list bool) : ctx Srt :=
  match bs with
  | [] => []
  | true :: bs => ι N :: sargs i s bs
  | false :: bs => ι (W i) :: ι s :: sargs i s bs
  end.

Definition con_spec i bs : spec Srt := Spec (cargs i bs) (W i).
Definition step_spec i s bs : spec Srt := Spec (sargs i s bs) s.
Definition steps i s : ctx Srt := map (step_spec i s) (dsc i).
Definition wrec_spec i s : spec Srt := Spec (ι (W i) :: steps i s) s.

Class Inductives := {
  a_con : forall i bs, mem (dsc i) bs -> Sym (con_spec i bs);
  a_wrec : forall i s, rec_ok r s -> Sym (wrec_spec i s)
}.

Context `{Inductives}.

Definition Con i bs (c : mem (dsc i) bs) {Γ} (a : args Γ (cargs i bs)) : tm Γ (W i) :=
  @tsym _ Sym Γ (con_spec i bs) (a_con i bs c) a.

(** [WRec i s h t st] : rec(t, st). *)
Definition WRec i s (h : rec_ok r s) {Γ} (t : tm Γ (W i)) (st : args Γ (steps i s)) : tm Γ s :=
  @tsym _ Sym Γ (wrec_spec i s) (a_wrec i s h) (@acons _ Sym Γ (ι (W i)) _ t st).

(** Les arguments du pas, à partir des arguments du constructeur et d'une
    fonction [R] pour les appels récursifs. *)
Fixpoint sbuild i s {Θ} (R : tm Θ (W i) -> tm Θ s) (bs : list bool) :
  args Θ (cargs i bs) -> args Θ (sargs i s bs) :=
  match bs as bs0 return args Θ (cargs i bs0) -> args Θ (sargs i s bs0) with
  | [] => fun _ => anil
  | b :: bs' =>
      match b as b0 return args Θ (cargs i (b0 :: bs')) -> args Θ (sargs i s (b0 :: bs')) with
      | true => fun a => @acons _ Sym Θ (ι N) _ (ahd a) (sbuild i s R bs' (atl a))
      | false => fun a => @acons _ Sym Θ (ι (W i)) _ (ahd a)
                          (@acons _ Sym Θ (ι s) _ (R (ahd a)) (sbuild i s R bs' (atl a)))
      end
  end.

(** Les variables d'un contexte Λ, dans Λ ++ Γ. *)
Definition lvars Λ Γ : args (Λ ++ Γ) Λ := etas Λ (fun ρ z => vl Γ z).
Definition rvars Λ Γ : args (Λ ++ Γ) Γ := etas Γ (fun ρ z => vr Λ z).

(** ** Règles de calcul *)

Section Rule.
Variables (i : Ind) (s : Srt) (h : rec_ok r s) (bs : list bool) (c : mem (dsc i) bs).

Definition wΘ : ctx Srt := steps i s ++ cargs i bs.

Definition wrec_lhs : tm wΘ s :=
  WRec i s h (Con i bs c (rvars (steps i s) (cargs i bs))) (lvars (steps i s) (cargs i bs)).

Definition wrec_rhs : tm wΘ s :=
  @tvar _ Sym wΘ (step_spec i s bs) (vl (cargs i bs) (mvar (step_spec i s) c))
    (sbuild i s (fun y => WRec i s h y (lvars (steps i s) (cargs i bs))) bs (rvars (steps i s) (cargs i bs))).

Definition wrec_rule : rule Sym := {| r_ctx := wΘ; r_sort := s; r_lhs := wrec_lhs; r_rhs := wrec_rhs |}.
End Rule.

Definition wrec_idx : Type := { i : Ind & { s : Srt & { h : rec_ok r s & { bs : list bool & mem (dsc i) bs } } } }.

Definition wrec_rules (k : wrec_idx) : rule Sym :=
  match k with existT _ i (existT _ s (existT _ h (existT _ bs c))) => wrec_rule i s h bs c end.

End Inductive.

Arguments asrt {Srt} N {Ind} W i b.
Arguments cargs {Srt} N {Ind} W i bs.
Arguments sargs {Srt} N {Ind} W i s bs.
Arguments con_spec {Srt} N {Ind} W i bs.
Arguments step_spec {Srt} N {Ind} W i s bs.
Arguments steps {Srt} N {Ind} W dsc i s.
Arguments wrec_spec {Srt} N {Ind} W dsc i s.
Arguments Inductives {Srt} Sym {_ G} N r {Ind} W dsc.
Arguments a_con {Srt Sym _ G N r Ind W dsc _} i bs c.
Arguments a_wrec {Srt Sym _ G N r Ind W dsc _} i s h.
Arguments Con {Srt Sym _ G N r Ind W dsc _} i bs c {Γ} a.
Arguments WRec {Srt Sym _ G N r Ind W dsc _} i s h {Γ} t st.
Arguments sbuild {Srt Sym N Ind W} i s {Θ} R bs a.
Arguments lvars {Srt Sym} Λ Γ.
Arguments rvars {Srt Sym} Λ Γ.
Arguments wΘ {Srt} N {Ind} W dsc i s bs.
Arguments wrec_lhs {Srt Sym _ G N r Ind W dsc _} i s h bs c.
Arguments wrec_rhs {Srt Sym _ G N r Ind W dsc _} i s h bs c.
Arguments wrec_rule {Srt Sym _ G N r Ind W dsc _} i s h bs c.
Arguments wrec_idx {Srt Sym _ G} r {Ind} dsc.
Arguments wrec_rules {Srt Sym _ G N r Ind W dsc _} k.

(** ** Calculs de substitution et conversions dérivées *)

Section Conv.
Context {Srt : Type} {Sym : spec Srt -> Type} `{Functional Srt Sym} {G : Graded Sym}.
Context {N : Srt} {r : bound} {Ind : Type} {W : Ind -> Srt} {dsc : Ind -> list (list bool)}.
Context {IN : Inductives Sym N r W dsc}.
Local Notation tm := (Terms.tm Sym).
Local Notation args := (Terms.args Sym).

Lemma aget_vsubst_args {Γ Θ σ} (z : var Θ σ) (a : args Γ Θ) {Δ} (v : vec Sym Γ Δ) :
  aget z (vsubst_args a v) = vsubst_tms (aget z a) v.
Proof. unfold vsubst_args, vsubst_tms. apply aget_subst_args. Qed.

Lemma vsubst_lvars Λ {Γ Δ} (a : args Δ Λ) (b : args Δ Γ) :
  vsubst_args (lvars Λ Γ) (vcat Λ a b) = a.
Proof.
  apply vec_ext; intros σ x; unfold vget, lvars.
  rewrite aget_vsubst_args, aget_etas, vsubst_eta, aget_vcat_l. reflexivity.
Qed.

Lemma vsubst_rvars Λ {Γ Δ} (a : args Δ Λ) (b : args Δ Γ) :
  vsubst_args (rvars Λ Γ) (vcat Λ a b) = b.
Proof.
  apply vec_ext; intros σ x; unfold vget, rvars.
  rewrite aget_vsubst_args, aget_etas, vsubst_eta, aget_vcat_r. reflexivity.
Qed.

Lemma vsubst_Con i bs c {Θ Γ} (a : args Θ (cargs N W i bs)) (v : vec Sym Θ Γ) :
  vsubst (Con i bs c a) v = Con i bs c (vsubst_args a v).
Proof. reflexivity. Qed.

Lemma vsubst_WRec i s h {Θ Γ} (t : tm Θ (W i)) (st : args Θ (steps N W dsc i s)) (v : vec Sym Θ Γ) :
  vsubst (WRec i s h t st) v = WRec i s h (vsubst t v) (vsubst_args st v).
Proof.
  transitivity (@tsym _ Sym Γ (wrec_spec N W dsc i s) (a_wrec i s h)
                  (@acons _ Sym Γ (ι (W i)) _ (vsubst_tms (σ := ι (W i)) t v) (vsubst_args st v))); [reflexivity|].
  rewrite vsubst_tms_nil. reflexivity.
Qed.

Lemma ren_Con i bs c {Γ Δ} (a : args Γ (cargs N W i bs)) (ξ : ren Γ Δ) :
  ren_tm (Con i bs c a) ξ = Con i bs c (ren_args a ξ).
Proof. reflexivity. Qed.

Lemma ren_WRec i s h {Γ Δ} (t : tm Γ (W i)) (st : args Γ (steps N W dsc i s)) (ξ : ren Γ Δ) :
  ren_tm (WRec i s h t st) ξ = WRec i s h (ren_tm t ξ) (ren_args st ξ).
Proof. reflexivity. Qed.

Lemma ahd_vsubst {Θ Γ σ L} (a : args Θ (σ :: L)) (v : vec Sym Θ Γ) :
  ahd (vsubst_args a v) = vsubst_tms (ahd a) v.
Proof.
  refine (match a as a0 in Terms.args _ Θ0 L0 return
            forall v : vec Sym Θ0 Γ, match L0 return args Θ0 L0 -> Prop with
            | [] => fun _ => True
            | σ0 :: L1 => fun a1 => ahd (vsubst_args a1 v) = vsubst_tms (ahd a1) v
            end a0 with
          | anil => fun _ => I
          | acons u a' => fun _ => eq_refl
          end v).
Qed.

Lemma atl_vsubst {Θ Γ σ L} (a : args Θ (σ :: L)) (v : vec Sym Θ Γ) :
  atl (vsubst_args a v) = vsubst_args (atl a) v.
Proof.
  refine (match a as a0 in Terms.args _ Θ0 L0 return
            forall v : vec Sym Θ0 Γ, match L0 return args Θ0 L0 -> Prop with
            | [] => fun _ => True
            | σ0 :: L1 => fun a1 => atl (vsubst_args a1 v) = vsubst_args (atl a1) v
            end a0 with
          | anil => fun _ => I
          | acons u a' => fun _ => eq_refl
          end v).
Qed.

Lemma ahd_ren {Θ Γ σ L} (a : args Θ (σ :: L)) (ξ : ren Θ Γ) :
  ahd (ren_args a ξ) = ren_tms (ahd a) ξ.
Proof.
  refine (match a as a0 in Terms.args _ Θ0 L0 return
            forall ξ : ren Θ0 Γ, match L0 return args Θ0 L0 -> Prop with
            | [] => fun _ => True
            | σ0 :: L1 => fun a1 => ahd (ren_args a1 ξ) = ren_tms (ahd a1) ξ
            end a0 with
          | anil => fun _ => I
          | acons u a' => fun _ => eq_refl
          end ξ).
Qed.

Lemma atl_ren {Θ Γ σ L} (a : args Θ (σ :: L)) (ξ : ren Θ Γ) :
  atl (ren_args a ξ) = ren_args (atl a) ξ.
Proof.
  refine (match a as a0 in Terms.args _ Θ0 L0 return
            forall ξ : ren Θ0 Γ, match L0 return args Θ0 L0 -> Prop with
            | [] => fun _ => True
            | σ0 :: L1 => fun a1 => atl (ren_args a1 ξ) = ren_args (atl a1) ξ
            end a0 with
          | anil => fun _ => I
          | acons u a' => fun _ => eq_refl
          end ξ).
Qed.

Lemma vsubst_sbuild i s {Θ Γ} (R : tm Θ (W i) -> tm Θ s) (R' : tm Γ (W i) -> tm Γ s) (v : vec Sym Θ Γ) :
  (forall y, vsubst (R y) v = R' (vsubst y v)) ->
  forall bs (a : args Θ (cargs N W i bs)),
  vsubst_args (sbuild i s R bs a) v = sbuild i s R' bs (vsubst_args a v).
Proof.
  intros HR bs. induction bs as [|[|] bs IH]; intros a; cbn [sbuild].
  - reflexivity.
  - change (args Θ (ι N :: cargs N W i bs)) in a.
    change (acons (vsubst_tms (σ := ι N) (ahd a) v) (vsubst_args (sbuild i s R bs (atl a)) v)
            = acons (ahd (vsubst_args a v)) (sbuild i s R' bs (atl (vsubst_args a v)))).
    rewrite IH. f_equal.
    + symmetry. apply (ahd_vsubst (σ := ι N) (L := cargs N W i bs)).
    + f_equal. symmetry. apply (atl_vsubst (σ := ι N) (L := cargs N W i bs)).
  - change (args Θ (ι (W i) :: cargs N W i bs)) in a.
    change (acons (vsubst_tms (σ := ι (W i)) (ahd a) v)
              (acons (vsubst_tms (σ := ι s) (R (ahd a)) v) (vsubst_args (sbuild i s R bs (atl a)) v))
            = acons (ahd (vsubst_args a v))
                (@acons _ Sym Γ (ι s) _ (R' (ahd (vsubst_args a v))) (sbuild i s R' bs (atl (vsubst_args a v))))).
    assert (E1 : ahd (vsubst_args a v) = vsubst_tms (σ := ι (W i)) (ahd a) v)
      by apply (ahd_vsubst (σ := ι (W i)) (L := cargs N W i bs)).
    assert (E2 : atl (vsubst_args a v) = vsubst_args (atl a) v)
      by apply (atl_vsubst (σ := ι (W i)) (L := cargs N W i bs)).
    rewrite E1, E2, IH, (vsubst_tms_nil s), HR, vsubst_tms_nil. reflexivity.
Qed.

Lemma ren_sbuild i s {Θ Γ} (R : tm Θ (W i) -> tm Θ s) (R' : tm Γ (W i) -> tm Γ s) (ξ : ren Θ Γ) :
  (forall y, ren_tm (R y) ξ = R' (ren_tm y ξ)) ->
  forall bs (a : args Θ (cargs N W i bs)),
  ren_args (sbuild i s R bs a) ξ = sbuild i s R' bs (ren_args a ξ).
Proof.
  intros HR bs. induction bs as [|[|] bs IH]; intros a; cbn [sbuild].
  - reflexivity.
  - change (args Θ (ι N :: cargs N W i bs)) in a.
    change (acons (ren_tms (σ := ι N) (ahd a) ξ) (ren_args (sbuild i s R bs (atl a)) ξ)
            = acons (ahd (ren_args a ξ)) (sbuild i s R' bs (atl (ren_args a ξ)))).
    rewrite IH. f_equal.
    + symmetry. apply (ahd_ren (σ := ι N) (L := cargs N W i bs)).
    + f_equal. symmetry. apply (atl_ren (σ := ι N) (L := cargs N W i bs)).
  - change (args Θ (ι (W i) :: cargs N W i bs)) in a.
    change (acons (ren_tms (σ := ι (W i)) (ahd a) ξ)
              (acons (ren_tms (σ := ι s) (R (ahd a)) ξ) (ren_args (sbuild i s R bs (atl a)) ξ))
            = acons (ahd (ren_args a ξ))
                (@acons _ Sym Γ (ι s) _ (R' (ahd (ren_args a ξ))) (sbuild i s R' bs (atl (ren_args a ξ))))).
    assert (E1 : ahd (ren_args a ξ) = ren_tms (σ := ι (W i)) (ahd a) ξ)
      by apply (ahd_ren (σ := ι (W i)) (L := cargs N W i bs)).
    assert (E2 : atl (ren_args a ξ) = ren_args (atl a) ξ)
      by apply (atl_ren (σ := ι (W i)) (L := cargs N W i bs)).
    rewrite E1, E2, IH. change (ren_tms (σ := ι s) (R (ahd a)) ξ) with (ren_tm (R (ahd a)) ξ).
    rewrite HR. reflexivity.
Qed.

Context {I : Type} (R : I -> rule Sym) {HR : CIncludes R (wrec_rules (N := N) (r := r) (W := W) (dsc := dsc))}.

(** rec(c(a⃗), st⃗) ~ st_c(a⃗, rec(y⃗, st⃗)). *)
Theorem wrec_conv i s h bs (c : mem (dsc i) bs) {Γ} (a : args Γ (cargs N W i bs)) (st : args Γ (steps N W dsc i s)) :
  conv (generated R) (WRec i s h (Con i bs c a) st)
    (happ (step_spec N W i s bs) (aget (mvar (step_spec N W i s) c) st) (sbuild i s (fun y => WRec i s h y st) bs a)).
Proof.
  pose proof (generated_included R wrec_rules (existT _ i (existT _ s (existT _ h (existT _ bs c))))
                (vcat (steps N W dsc i s) st a)) as Hr.
  cbn [wrec_rules wrec_rule r_lhs r_rhs r_ctx] in Hr.
  unfold wrec_lhs, wrec_rhs in Hr.
  rewrite vsubst_WRec, vsubst_Con, vsubst_lvars, vsubst_rvars in Hr.
  eapply conv_trans; [exact Hr|].
  change (conv (generated R)
            (happ (step_spec N W i s bs) (aget (vl (cargs N W i bs) (mvar (step_spec N W i s) c)) (vcat (steps N W dsc i s) st a))
               (vsubst_args (sbuild i s (fun y => WRec i s h y (lvars (steps N W dsc i s) (cargs N W i bs))) bs
                              (rvars (steps N W dsc i s) (cargs N W i bs))) (vcat (steps N W dsc i s) st a)))
            (happ (step_spec N W i s bs) (aget (mvar (step_spec N W i s) c) st) (sbuild i s (fun y => WRec i s h y st) bs a))).
  rewrite aget_vcat_l.
  rewrite (vsubst_sbuild i s _ (fun y => WRec i s h y st)), vsubst_rvars; [apply conv_refl|].
  intros y. rewrite vsubst_WRec, vsubst_lvars. reflexivity.
Qed.

End Conv.

(** ** Règles de déduction *)

Section Logic.
Context {Srt : Type} {Sym : spec Srt -> Type} `{Functional Srt Sym} {G : Graded Sym}.
Context {N : Srt} {r : bound} {Ind : Type} {W : Ind -> Srt} {dsc : Ind -> list (list bool)}.
Context {IN : Inductives Sym N r W dsc} (P : Srt).
Local Notation tm := (Terms.tm Sym).
Local Notation args := (Terms.args Sym).
Local Notation form := (form Sym P).
Local Notation σφ i := (Spec [ι (W i)] P).

(** Les hypothèses de récurrence : Φ(y) pour chaque argument récursif y. *)
Fixpoint ihyps i {Γ} (Φ : tm Γ (W i) -> form Γ) (bs : list bool) : args Γ (cargs N W i bs) -> list (form Γ) :=
  match bs as bs0 return args Γ (cargs N W i bs0) -> list (form Γ) with
  | [] => fun _ => []
  | b :: bs' =>
      match b as b0 return args Γ (cargs N W i (b0 :: bs')) -> list (form Γ) with
      | true => fun a => ihyps i Φ bs' (atl a)
      | false => fun a => Φ (ahd a) :: ihyps i Φ bs' (atl a)
      end
  end.

Definition iΘ i : ctx Srt := [σφ i; ι (W i)].

(** La prémisse d'un constructeur : dans le contexte des arguments x⃗,
    sous les hypothèses φ(y) pour les arguments récursifs, φ(c(x⃗)). *)
Definition ind_prem i (p : {bs & mem (dsc i) bs}) : premise Sym P (iΘ i) :=
  premx (cargs N W i (projT1 p))
    (ihyps i (fun y => app1 (s := W i) (vr (cargs N W i (projT1 p)) vz) y) (projT1 p) (lvars _ (iΘ i)))
    (app1 (s := W i) (vr (cargs N W i (projT1 p)) vz) (Con i (projT1 p) (projT2 p) (lvars _ (iΘ i)))).

Definition wind_rule i : drule Sym P :=
  {| d_ctx := iΘ i;
     d_prems := map (ind_prem i) (mems (dsc i));
     d_concl := app1 (s := W i) vz (var0 (vs vz)) |}.

Definition wind_rules (i : Ind) : drule Sym P := wind_rule i.

(** Les équations de rec comme règles de déduction. *)
Definition weq_rule {HQ : forall s, HasEq Sym P s} i s h bs (c : mem (dsc i) bs) : drule Sym P :=
  {| d_ctx := wΘ N W dsc i s bs; d_prems := [];
     d_concl := Eq s (wrec_lhs i s h bs c) (wrec_rhs i s h bs c) |}.

Definition weq_rules {HQ : forall s, HasEq Sym P s} (k : wrec_idx r dsc) : drule Sym P :=
  match k with existT _ i (existT _ s (existT _ h (existT _ bs c))) => weq_rule i s h bs c end.

Lemma vsubst_ihyps i {Θ Γ} (Φ : tm Θ (W i) -> form Θ) (Φ' : tm Γ (W i) -> form Γ) (v : vec Sym Θ Γ) :
  (forall y, vsubst (Φ y) v = Φ' (vsubst y v)) ->
  forall bs (a : args Θ (cargs N W i bs)),
  vsubst_list (ihyps i Φ bs a) v = ihyps i Φ' bs (vsubst_args a v).
Proof.
  intros HΦ bs. induction bs as [|[|] bs IH]; intros a; cbn [ihyps].
  - reflexivity.
  - change (args Θ (ι N :: cargs N W i bs)) in a.
    rewrite IH. f_equal. symmetry. apply (atl_vsubst (σ := ι N) (L := cargs N W i bs)).
  - change (args Θ (ι (W i) :: cargs N W i bs)) in a.
    change (vsubst (Φ (ahd a)) v :: vsubst_list (ihyps i Φ bs (atl a)) v
            = Φ' (ahd (vsubst_args a v)) :: ihyps i Φ' bs (atl (vsubst_args a v))).
    rewrite IH, HΦ, (ahd_vsubst (σ := ι (W i)) (L := cargs N W i bs)),
      (atl_vsubst (σ := ι (W i)) (L := cargs N W i bs)), vsubst_tms_nil. reflexivity.
Qed.

Lemma ihyps_ext i {Γ} (Φ Φ' : tm Γ (W i) -> form Γ) :
  (forall y, Φ y = Φ' y) -> forall bs (a : args Γ (cargs N W i bs)), ihyps i Φ bs a = ihyps i Φ' bs a.
Proof.
  intros E bs. induction bs as [|[|] bs IH]; intros a; cbn [ihyps]; [reflexivity|apply IH|].
  rewrite E, IH. reflexivity.
Qed.

Section Derived.
Context (C : system Sym) {J : Type} (R : J -> drule Sym P).
Local Notation "Ξ ⊢ φ" := (deriv C P R _ Ξ φ) (at level 70).

(** Les variables d'un constructeur, dans son contexte étendu. *)
Definition cvars i bs Γ : args (cargs N W i bs ++ Γ) (cargs N W i bs) := lvars (cargs N W i bs) Γ.

Lemma vsubst_lvars_up Λ {Θ Γ} (v : vec Sym Θ Γ) : vsubst_args (lvars Λ Θ) (vup Λ v) = lvars Λ Γ.
Proof.
  apply vec_ext; intros σ x; unfold vget, lvars, vup.
  rewrite aget_vsubst_args, !aget_etas, vsubst_eta, aget_vcat_l, aget_etas. reflexivity.
Qed.

Lemma aget_vup_r Λ {Θ Γ σ} (y : var Θ σ) (v : vec Sym Θ Γ) :
  aget (vr Λ y) (vup Λ v) = ren_tms (aget y v) (wk Λ).
Proof. unfold vup, vren. rewrite aget_vcat_r, aget_vmap. reflexivity. Qed.

Section Ind.
Context {HI : Includes R (wind_rules)}.

(** Récurrence sur Wᵢ : pour chaque constructeur, dans le contexte de ses
    arguments et sous les hypothèses φ(y) des arguments récursifs, φ(c(x⃗)). *)
Theorem windI i {Γ} (Ξ : list (form Γ)) (φ : form (ι (W i) :: Γ)) (t : tm Γ (W i)) :
  (forall bs (c : mem (dsc i) bs),
     deriv C P R (cargs N W i bs ++ Γ)
       (ihyps i (fun y => vsubst (ren_tms (σ := σφ i) φ (wk (cargs N W i bs))) (inst1 y)) bs (cvars i bs Γ)
        ++ wk_list (cargs N W i bs) Ξ)
       (vsubst (ren_tms (σ := σφ i) φ (wk (cargs N W i bs))) (inst1 (Con i bs c (cvars i bs Γ))))) ->
  Ξ ⊢ vsubst φ (inst1 t).
Proof.
  intros Hc.
  apply (rule_inc C P R wind_rules i Ξ (@acons _ Sym Γ (σφ i) _ φ (@acons _ Sym Γ (ι (W i)) _ t anil)));
    cbn [wind_rules wind_rule d_ctx d_concl d_prems].
  - rewrite vsubst_app1. reflexivity.
  - intros p Hp. apply in_map_iff in Hp. destruct Hp as [[bs c] [<- _]].
    unfold inst_hyps, inst_goal, ind_prem. cbn [p_ext p_hyps p_goal premx projT1 projT2].
    set (v := @acons _ Sym Γ (σφ i) _ φ (@acons _ Sym Γ (ι (W i)) _ t anil)).
    assert (EΦ : forall y, vsubst (app1 (s := W i) (vr (cargs N W i bs) vz) y) (vup (cargs N W i bs) v)
                      = vsubst (ren_tms (σ := σφ i) φ (wk (cargs N W i bs))) (inst1 (vsubst y (vup (cargs N W i bs) v)))).
    { intros y. rewrite vsubst_app1_gen, aget_vup_r. reflexivity. }
    rewrite (vsubst_ihyps i _ (fun y => vsubst (ren_tms (σ := σφ i) φ (wk (cargs N W i bs))) (inst1 y)) _ EΦ),
      EΦ, vsubst_Con.
    unfold iΘ in *. rewrite !vsubst_lvars_up.
    exact (Hc bs c).
Qed.
End Ind.

End Derived.
End Logic.

