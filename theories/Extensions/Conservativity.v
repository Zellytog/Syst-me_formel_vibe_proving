(** * Extensions, traductions et conservativité : le cadre abstrait

    On raisonne sur des systèmes logiques quelconques ([logic], dans
    [SF.Logic.Judgment]), éventuellement sur des signatures différentes. Un
    jugement est un triplet Γ | Ξ ⊢ φ, et il est valide s'il est dérivable.

    - Une **traduction** de L1 vers L2 est une application des jugements de
      L1 vers ceux de L2. Elle est **saine** si elle préserve la validité.
    - Une **extension** de L vers L' est une traduction saine (en pratique,
      l'inclusion de la syntaxe).
    - Une extension est **conservative sur une classe K** de jugements de L
      si, pour tout j ∈ K, la validité de l'image de j dans L' entraîne celle
      de j dans L. Elle est **conservative** si c'est vrai pour tous les
      jugements.

    La conservativité partielle permet de traiter des résultats comme la
    Π₂-conservativité de PA sur HA (Friedman) : K est alors la classe des
    énoncés Π₂ clos.

    Les deux méthodes de preuve sont abstraites ici :
    - la **rétraction** : une traduction saine T de L' vers L telle que
      T(E(j)) valide entraîne j valide, pour j ∈ K (relativisation,
      interprétations) ;
    - la **famille de traductions** : une traduction saine T_j pour chaque
      j ∈ K, choisie selon j (c'est le cas de la A-traduction de Friedman,
      où A dépend de l'énoncé Π₂). *)

From Stdlib Require Import List.
Import ListNotations.
From SF.Syntax Require Import Spec Terms Vectors.
From SF.Calculus Require Import System.
From SF.Logic Require Import Judgment.

(** ** Jugements *)

Section Judg.
Context {Srt : Type} (Sym : spec Srt -> Type) (P : Srt).

Record judg := mkJ {
  j_ctx : ctx Srt;
  j_hyps : list (form Sym P j_ctx);
  j_goal : form Sym P j_ctx
}.
End Judg.

Arguments mkJ {Srt Sym P} j_ctx j_hyps j_goal.
Arguments j_ctx {Srt Sym P} j.
Arguments j_hyps {Srt Sym P} j.
Arguments j_goal {Srt Sym P} j.

Section Defs.
Context {Srt : Type} {Sym : spec Srt -> Type}.

Definition ljudg (L : logic Sym) := judg Sym (l_prop Sym L).

Definition valid (L : logic Sym) (j : ljudg L) : Prop :=
  provable L (j_ctx j) (j_hyps j) (j_goal j).

(** Une classe de jugements. *)
Definition jclass (L : logic Sym) := ljudg L -> Prop.

Definition jall {L : logic Sym} : jclass L := fun _ => True.
Definition jincl {L : logic Sym} (K K' : jclass L) := forall j, K j -> K' j.
Definition junion {L : logic Sym} (K K' : jclass L) : jclass L := fun j => K j \/ K' j.

(** Classe des jugements sans hypothèse dont la conclusion vérifie Φ, par
    exemple les énoncés clos Π₂. *)
Definition jgoals {L : logic Sym} (Φ : forall Γ, form Sym (l_prop Sym L) Γ -> Prop) : jclass L :=
  fun j => j_hyps j = [] /\ Φ (j_ctx j) (j_goal j).

(** Deux jugements sont équivalents s'ils sont valides en même temps. *)
Definition jequiv (L : logic Sym) (j j' : ljudg L) := valid L j <-> valid L j'.

End Defs.

(** ** Traductions *)

Section Trans.
Context {S1 S2 : Type} {Sym1 : spec S1 -> Type} {Sym2 : spec S2 -> Type}.

Definition translation (L1 : logic Sym1) (L2 : logic Sym2) := ljudg L1 -> ljudg L2.

Definition sound {L1 : logic Sym1} {L2 : logic Sym2} (T : translation L1 L2) :=
  forall j, valid L1 j -> valid L2 (T j).

(** Forme usuelle d'une traduction : on traduit le contexte et les
    formules, et on ajoute des hypothèses qui ne dépendent que du contexte
    (pour la relativisation : P(x) pour chaque variable x d'une sorte
    relativisée). *)
Definition strans {L1 : logic Sym1} {L2 : logic Sym2}
  (tc : ctx S1 -> ctx S2)
  (tf : forall Γ, form Sym1 (l_prop Sym1 L1) Γ -> form Sym2 (l_prop Sym2 L2) (tc Γ))
  (extra : forall Γ, list (form Sym2 (l_prop Sym2 L2) (tc Γ))) : translation L1 L2 :=
  fun j => mkJ (tc (j_ctx j)) (extra (j_ctx j) ++ map (tf (j_ctx j)) (j_hyps j)) (tf _ (j_goal j)).

End Trans.

Section Comp.
Context {S1 S2 S3 : Type} {Sym1 : spec S1 -> Type} {Sym2 : spec S2 -> Type} {Sym3 : spec S3 -> Type}.
Context {L1 : logic Sym1} {L2 : logic Sym2} {L3 : logic Sym3}.

Definition tcomp (T2 : translation L2 L3) (T1 : translation L1 L2) : translation L1 L3 :=
  fun j => T2 (T1 j).

Lemma sound_comp T2 T1 : sound T2 -> sound T1 -> sound (tcomp T2 T1).
Proof. intros H2 H1 j Hj; apply H2, H1, Hj. Qed.

End Comp.

Lemma sound_id {Srt} {Sym : spec Srt -> Type} (L : logic Sym) : sound (L1 := L) (L2 := L) (fun j => j).
Proof. intros j Hj; exact Hj. Qed.

(** ** Extensions *)

Record extension {S1 S2 : Type} {Sym1 : spec S1 -> Type} {Sym2 : spec S2 -> Type}
  (L : logic Sym1) (L' : logic Sym2) := {
  e_tr : translation L L';
  e_sound : sound e_tr
}.

Arguments e_tr {S1 S2 Sym1 Sym2 L L'} e j.
Arguments e_sound {S1 S2 Sym1 Sym2 L L'} e.

Definition ext_id {Srt} {Sym : spec Srt -> Type} (L : logic Sym) : extension L L :=
  {| e_tr := fun j => j; e_sound := sound_id L |}.

Definition ext_comp {S1 S2 S3 : Type} {Sym1 : spec S1 -> Type} {Sym2 : spec S2 -> Type}
  {Sym3 : spec S3 -> Type} {L1 : logic Sym1} {L2 : logic Sym2} {L3 : logic Sym3}
  (E2 : extension L2 L3) (E1 : extension L1 L2) : extension L1 L3 :=
  {| e_tr := tcomp (e_tr E2) (e_tr E1); e_sound := sound_comp _ _ (e_sound E2) (e_sound E1) |}.

(** ** Conservativité *)

Section Cons.
Context {S1 S2 : Type} {Sym1 : spec S1 -> Type} {Sym2 : spec S2 -> Type}.
Context {L : logic Sym1} {L' : logic Sym2}.

Definition conservative_on (E : extension L L') (K : jclass L) :=
  forall j, K j -> valid L' (e_tr E j) -> valid L j.

Definition conservative (E : extension L L') := conservative_on E jall.

(** Pour j ∈ K, j et son image sont alors équivalents. *)
Lemma conservative_on_equiv E K j : conservative_on E K -> K j -> (valid L j <-> valid L' (e_tr E j)).
Proof. intros HC Hj; split; [apply (e_sound E)|apply HC, Hj]. Qed.

Lemma conservative_on_all E : conservative E <-> forall K, conservative_on E K.
Proof. split; [intros H K j _; apply H; exact Logic.I|intros H; apply H]. Qed.

Lemma conservative_on_mono E (K K' : jclass L) :
  jincl K K' -> conservative_on E K' -> conservative_on E K.
Proof. intros Hi H j Hj; apply H, Hi, Hj. Qed.

Lemma conservative_on_union E (K K' : jclass L) :
  conservative_on E K -> conservative_on E K' -> conservative_on E (junion K K').
Proof. intros H H' j [Hj|Hj]; [apply H|apply H']; exact Hj. Qed.

(** Toute extension est conservative sur les jugements déjà valides, et sur
    toute classe close par équivalence dont elle reflète un représentant. *)
Lemma conservative_on_valid E : conservative_on E (valid L).
Proof. intros j Hj _; exact Hj. Qed.

(** *** Méthode 1 : rétraction par une traduction saine *)
Theorem conservative_by_retraction (E : extension L L') (T : translation L' L) (K : jclass L) :
  sound T ->
  (forall j, K j -> valid L (T (e_tr E j)) -> valid L j) ->
  conservative_on E K.
Proof. intros HT Hr j Hj Hv; apply Hr; [exact Hj|apply HT, Hv]. Qed.

(** Cas usuel : T ∘ E est l'identité à équivalence près. *)
Corollary conservative_by_inverse (E : extension L L') (T : translation L' L) :
  sound T -> (forall j, valid L (T (e_tr E j)) -> valid L j) -> conservative E.
Proof. intros HT Hr; apply (conservative_by_retraction E T); [exact HT|intros j _; apply Hr]. Qed.

(** *** Méthode 2 : une famille de traductions, choisie selon le jugement

    C'est la forme de l'argument de Friedman : pour un énoncé Π₂
    ∀x ∃y φ₀(x, y), on traduit par la A-traduction avec A := ∃y φ₀(x, y). *)
Theorem conservative_by_translations (E : extension L L') (K : jclass L) :
  (forall j, K j -> exists T : translation L' L, sound T /\ (valid L (T (e_tr E j)) -> valid L j)) ->
  conservative_on E K.
Proof. intros HT j Hj Hv; destruct (HT j Hj) as (T & HsT & Hr); apply Hr, HsT, Hv. Qed.

End Cons.

(** ** Composition *)

Section ConsComp.
Context {S1 S2 S3 : Type} {Sym1 : spec S1 -> Type} {Sym2 : spec S2 -> Type} {Sym3 : spec S3 -> Type}.
Context {L1 : logic Sym1} {L2 : logic Sym2} {L3 : logic Sym3}.

(** Si E1 est K1-conservative, envoie K1 dans K2, et si E2 est
    K2-conservative, alors E2 ∘ E1 est K1-conservative. *)
Theorem conservative_on_comp (E2 : extension L2 L3) (E1 : extension L1 L2) K1 K2 :
  conservative_on E1 K1 ->
  (forall j, K1 j -> K2 (e_tr E1 j)) ->
  conservative_on E2 K2 ->
  conservative_on (ext_comp E2 E1) K1.
Proof. intros H1 Hm H2 j Hj Hv; apply H1; [exact Hj|apply H2; [apply Hm, Hj|exact Hv]]. Qed.

Corollary conservative_comp (E2 : extension L2 L3) (E1 : extension L1 L2) :
  conservative E1 -> conservative E2 -> conservative (ext_comp E2 E1).
Proof.
  intros H1 H2; apply (conservative_on_comp E2 E1 jall jall); [exact H1|intros; exact Logic.I|exact H2].
Qed.

(** Réciproquement, si E2 ∘ E1 est K-conservative, E1 l'est (E2 est saine). *)
Theorem conservative_on_comp_inv (E2 : extension L2 L3) (E1 : extension L1 L2) K :
  conservative_on (ext_comp E2 E1) K -> conservative_on E1 K.
Proof. intros H j Hj Hv; apply H; [exact Hj|apply (e_sound E2), Hv]. Qed.

End ConsComp.
