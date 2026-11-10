(** * Cadres d'évidence (evidenced frames)

    D'après Cohen, Miquey et Tate (« Evidenced Frames: A Unifying Framework
    Broadening Realizability Models », LICS 2021). Un cadre d'évidence est
    la donnée :
    - d'un sétoïde Φ de *propositions* ;
    - d'un type E d'*évidences* ;
    - d'une relation φ —e→ ψ (« e est une évidence que φ entraîne ψ ») ;
    avec des évidences pour l'identité, la composition, ⊤, ∧, ⇒ et les
    conjonctions ⋀S des parties S de Φ (comme dans l'article).

    Chaque évidence construite ne dépend que des évidences données, pas des
    propositions. C'est ce qui rend l'ordre *uniforme* du tripos associé
    (φ ≤ ψ sur X s'il existe e telle que φ(x) —e→ ψ(x) pour tout x)
    stable par les constructions logiques ([FrameModel.v]).

    Différences de présentation avec l'article :
    - l'implication universelle φ ⊃ ⋀Φ' de l'article est scindée ici en
      ⇒ et ⋀ ;
    - une partie de Φ est un prédicat Φ → Prop ; la conjonction indexée
      par un type, ⋀ᵢ f(i) := ⋀{ψ ∣ ∃i. ψ ≡ f(i)}, est dérivée ([fall]).
      Par imprédicativité de Prop, I peut être dans n'importe quel
      univers : le cadre ne fixe aucun univers d'index ;
    - Φ est un sétoïde, ce qui évite l'extensionnalité (pour la
      réalisabilité, Φ est un ensemble de parties de E, comparées par
      double inclusion).

    ⊥, ∨ et ∃ ne sont pas primitifs : ils sont codés imprédicativement, en
    quantifiant sur Φ lui-même ([fbot], [for_], [fex]). L'ordre intuitionniste
    est le cas Φ = Prop, E = unit ([prop_frame]). *)

From SF.Models Require Import PSet.

Record frame := {
  fprop :> pset;
  fev : Type;
  fent : fprop -> fev -> fprop -> Prop;
  fent_proper : forall φ φ' e ψ ψ', φ ≡ φ' -> ψ ≡ ψ' -> fent φ e ψ -> fent φ' e ψ';

  e_id : fev;
  f_id : forall φ, fent φ e_id φ;
  e_comp : fev -> fev -> fev;
  f_comp : forall φ ψ χ e1 e2, fent φ e1 ψ -> fent ψ e2 χ -> fent φ (e_comp e1 e2) χ;

  ftop : fprop;
  e_top : fev;
  f_top : forall φ, fent φ e_top ftop;

  fand : fprop -> fprop -> fprop;
  fand_proper : forall φ φ' ψ ψ', φ ≡ φ' -> ψ ≡ ψ' -> fand φ ψ ≡ fand φ' ψ';
  e_fst : fev;
  f_fst : forall φ ψ, fent (fand φ ψ) e_fst φ;
  e_snd : fev;
  f_snd : forall φ ψ, fent (fand φ ψ) e_snd ψ;
  e_pair : fev -> fev -> fev;
  f_pair : forall φ ψ χ e1 e2, fent φ e1 ψ -> fent φ e2 χ -> fent φ (e_pair e1 e2) (fand ψ χ);

  fimp : fprop -> fprop -> fprop;
  fimp_proper : forall φ φ' ψ ψ', φ ≡ φ' -> ψ ≡ ψ' -> fimp φ ψ ≡ fimp φ' ψ';
  e_lam : fev -> fev;
  f_lam : forall φ ψ χ e, fent (fand φ ψ) e χ -> fent φ (e_lam e) (fimp ψ χ);
  e_eval : fev;
  f_eval : forall ψ χ, fent (fand (fimp ψ χ) ψ) e_eval χ;

  fallP : (fprop -> Prop) -> fprop;
  fallP_proper : forall S T : fprop -> Prop, (forall ψ, S ψ <-> T ψ) -> fallP S ≡ fallP T;
  e_gen : fev -> fev;
  f_genP : forall (S : fprop -> Prop) φ e, (forall ψ, S ψ -> fent φ e ψ) -> fent φ (e_gen e) (fallP S);
  e_inst : fev;
  f_instP : forall (S : fprop -> Prop) ψ, S ψ -> fent (fallP S) e_inst ψ
}.

Arguments fent {F} φ e ψ : rename.
Arguments e_id {F} : rename.
Arguments e_comp {F} e1 e2 : rename.
Arguments ftop {F} : rename.
Arguments e_top {F} : rename.
Arguments fand {F} φ ψ : rename.
Arguments e_fst {F} : rename.
Arguments e_snd {F} : rename.
Arguments e_pair {F} e1 e2 : rename.
Arguments fimp {F} φ ψ : rename.
Arguments e_lam {F} e : rename.
Arguments e_eval {F} : rename.
Arguments fallP {F} S : rename.
Arguments e_gen {F} e : rename.
Arguments e_inst {F} : rename.

(** *** ⋀ indexé par un type, dérivé du ⋀ sur les parties

    ⋀ᵢ f(i) := ⋀ {ψ ∣ ∃i. ψ ≡ f(i)}. La partie est une proposition, quel
    que soit l'univers de I (imprédicativité de Prop) : le cadre ne fixe
    aucun univers d'index, et ces définitions sont polymorphes. *)

#[universes(polymorphic)]
Definition fall {F : frame} {I : Type} (f : I -> fprop F) : fprop F :=
  fallP (fun ψ => exists i, ψ ≡ f i).

#[universes(polymorphic)]
Lemma fall_proper (F : frame) I (f g : I -> fprop F) : (forall i, f i ≡ g i) -> fall f ≡ fall g.
Proof.
  intros H. apply fallP_proper. intros ψ. split; intros [i Hi]; exists i.
  - exact (peq_trans Hi (H i)).
  - exact (peq_trans Hi (peq_sym (H i))).
Qed.

#[universes(polymorphic)]
Lemma f_gen (F : frame) I (φ : fprop F) (f : I -> fprop F) e :
  (forall i, fent φ e (f i)) -> fent φ (e_gen e) (fall f).
Proof.
  intros H. apply f_genP. intros ψ [i Hi].
  exact (fent_proper F φ φ e (f i) ψ (peq_refl φ) (peq_sym Hi) (H i)).
Qed.

(** Un élément i de I, vu comme élément de la partie {ψ ∣ ∃j. ψ ≡ f(j)}. *)
#[universes(polymorphic)]
Definition fall_idx {F : frame} {I : Type} (f : I -> fprop F) (i : I) : {ψ : fprop F | exists j, ψ ≡ f j} :=
  exist _ (f i) (ex_intro _ i (peq_refl (f i))).

#[universes(polymorphic)]
Lemma f_inst (F : frame) I (f : I -> fprop F) i : fent (fall f) e_inst (f i).
Proof. apply f_instP. exists i. apply peq_refl. Qed.

Section Derived.

Context {F : frame}.

Local Notation "φ —[ e ]→ ψ" := (fent (F := F) φ e ψ) (at level 70).

Lemma fent_eq φ φ' e ψ : φ ≡ φ' -> φ —[e]→ ψ -> φ' —[e]→ ψ.
Proof. intros H. apply fent_proper; [exact H|apply peq_refl]. Qed.

Lemma fent_eq_r φ e ψ ψ' : ψ ≡ ψ' -> φ —[e]→ ψ -> φ —[e]→ ψ'.
Proof. intros H. apply fent_proper; [apply peq_refl|exact H]. Qed.

(** Une équivalence de propositions est une évidence (l'identité). *)
Lemma fent_of_eq (φ ψ : F) : φ ≡ ψ -> φ —[e_id]→ ψ.
Proof. intros H. apply (fent_eq_r φ e_id φ ψ H), f_id. Qed.

(** *** Évidences dérivées pour ⇒ et ∧ *)

(** Appliquer une évidence sous une conjonction (à droite). *)
Definition e_mapr (e : fev F) : fev F := e_pair e_fst (e_comp e_snd e).

Lemma f_mapr φ ψ ψ' e : ψ —[e]→ ψ' -> fand φ ψ —[e_mapr e]→ fand φ ψ'.
Proof. intros H. apply f_pair; [apply f_fst|eapply f_comp; [apply f_snd|exact H]]. Qed.

(** Défaire une implication : de φ —e→ (ψ ⇒ χ), on tire φ ∧ ψ —·→ χ. *)
Definition e_unlam (e : fev F) : fev F := e_comp (e_pair (e_comp e_fst e) e_snd) e_eval.

Lemma f_unlam φ ψ χ e : φ —[e]→ fimp ψ χ -> fand φ ψ —[e_unlam e]→ χ.
Proof.
  intros H. eapply f_comp; [|apply f_eval].
  apply f_pair; [eapply f_comp; [apply f_fst|exact H]|apply f_snd].
Qed.

(** Une évidence close (de ⊤) donne une évidence depuis n'importe quoi. *)
Definition e_const (e : fev F) : fev F := e_comp e_top e.

Lemma f_const φ ψ e : ftop —[e]→ ψ -> φ —[e_const e]→ ψ.
Proof. intros H. eapply f_comp; [apply f_top|exact H]. Qed.

(** *** ⊥ *)

Definition fbot : F := fall (I := pcar F) (fun φ => φ).

Lemma f_bot φ : fbot —[e_inst]→ φ.
Proof. apply (f_inst _ _ (fun φ => φ) φ). Qed.

(** *** ∨, codée : φ ∨ ψ := ⋀_χ ((φ ⇒ χ) ∧ (ψ ⇒ χ)) ⇒ χ *)

Definition for_ (φ ψ : F) : F :=
  fall (I := pcar F) (fun χ => fimp (fand (fimp φ χ) (fimp ψ χ)) χ).

Lemma for_proper φ φ' ψ ψ' : φ ≡ φ' -> ψ ≡ ψ' -> for_ φ ψ ≡ for_ φ' ψ'.
Proof.
  intros H1 H2. apply fall_proper. intros χ.
  apply fimp_proper; [|apply peq_refl]. apply fand_proper; apply fimp_proper; (assumption || apply peq_refl).
Qed.

Definition e_inl : fev F := e_gen (e_lam (e_comp (e_pair (e_comp e_snd e_fst) e_fst) e_eval)).
Definition e_inr : fev F := e_gen (e_lam (e_comp (e_pair (e_comp e_snd e_snd) e_fst) e_eval)).

Lemma f_inl φ ψ : φ —[e_inl]→ for_ φ ψ.
Proof.
  apply f_gen. intros χ. apply f_lam. eapply f_comp; [|apply f_eval].
  apply f_pair; [eapply f_comp; [apply f_snd|apply f_fst]|apply f_fst].
Qed.

Lemma f_inr φ ψ : ψ —[e_inr]→ for_ φ ψ.
Proof.
  apply f_gen. intros χ. apply f_lam. eapply f_comp; [|apply f_eval].
  apply f_pair; [eapply f_comp; [apply f_snd|apply f_snd]|apply f_fst].
Qed.

Definition e_case (e1 e2 : fev F) : fev F :=
  e_comp (e_pair e_inst (e_pair (e_lam (e_comp e_snd e1)) (e_lam (e_comp e_snd e2)))) e_eval.

Lemma f_case φ ψ χ e1 e2 : φ —[e1]→ χ -> ψ —[e2]→ χ -> for_ φ ψ —[e_case e1 e2]→ χ.
Proof.
  intros H1 H2. eapply f_comp; [|apply f_eval]. apply f_pair.
  - apply (f_inst _ _ (fun χ0 => fimp (fand (fimp φ χ0) (fimp ψ χ0)) χ0) χ).
  - apply f_pair; apply f_lam; (eapply f_comp; [apply f_snd|eassumption]).
Qed.

(** *** ∃, codé : ⋁ᵢ φᵢ := ⋀_χ (⋀ᵢ (φᵢ ⇒ χ)) ⇒ χ *)

Definition fex {I : Type} (f : I -> F) : F :=
  fall (I := pcar F) (fun χ => fimp (fall (fun i => fimp (f i) χ)) χ).

Lemma fex_proper I (f g : I -> F) : (forall i, f i ≡ g i) -> fex f ≡ fex g.
Proof.
  intros H. apply fall_proper. intros χ. apply fimp_proper; [|apply peq_refl].
  apply fall_proper. intros i. apply fimp_proper; [apply H|apply peq_refl].
Qed.

Definition e_exI : fev F := e_gen (e_lam (e_comp (e_pair (e_comp e_snd e_inst) e_fst) e_eval)).

Lemma f_exI I (f : I -> F) i : f i —[e_exI]→ fex f.
Proof.
  apply f_gen. intros χ. apply f_lam. eapply f_comp; [|apply f_eval].
  apply f_pair; [|apply f_fst].
  eapply f_comp; [apply f_snd|]. apply (f_inst _ _ (fun j => fimp (f j) χ) i).
Qed.

Definition e_exE (e : fev F) : fev F :=
  e_comp (e_pair e_inst (e_const (e_gen (e_lam (e_comp e_snd e))))) e_eval.

Lemma f_exE I (f : I -> F) ψ e : (forall i, f i —[e]→ ψ) -> fex f —[e_exE e]→ ψ.
Proof.
  intros H. eapply f_comp; [|apply f_eval]. apply f_pair.
  - apply (f_inst _ _ (fun χ => fimp (fall (fun i => fimp (f i) χ)) χ) ψ).
  - apply f_const. apply f_gen. intros i. apply f_lam. eapply f_comp; [apply f_snd|apply H].
Qed.

End Derived.

(** ** Le cadre de Prop *)

Program Definition prop_frame : frame := {|
  fprop := PropS;
  fev := unit;
  fent := fun φ _ ψ => φ -> ψ;
  e_id := tt; e_comp := fun _ _ => tt;
  ftop := True; e_top := tt;
  fand := and; e_fst := tt; e_snd := tt; e_pair := fun _ _ => tt;
  fimp := fun A B => A -> B; e_lam := fun _ => tt; e_eval := tt;
  fallP := fun S => forall ψ : Prop, S ψ -> ψ; e_gen := fun _ => tt; e_inst := tt
|}.
Solve All Obligations with (cbn in *; firstorder).

(** Dans [prop_frame], le ⋀ dérivé est le ∀ de Prop. *)
Lemma prop_fall {I : Type} (f : I -> Prop) : @fall prop_frame I f <-> forall i, f i.
Proof.
  unfold fall; cbn. split.
  - intros H i. apply (H (f i)). exists i. split; auto.
  - intros H ψ [i Hi]. apply (proj2 Hi), H.
Qed.

(** ** Changement d'index *)

Section Reindex.

Context {F : frame}.

Local Notation "φ —[ e ]→ ψ" := (fent (F := F) φ e ψ) (at level 70).

(** ⋀ᵢ fᵢ entraîne ⋀ⱼ gⱼ dès que chaque gⱼ est un f_{h j}. *)
Lemma f_fall_map {I J : Type} (f : I -> F) (g : J -> F) (h : J -> I) :
  (forall j, f (h j) ≡ g j) -> fall f —[e_gen e_inst]→ fall g.
Proof.
  intros H. apply f_gen. intros j. apply (fent_eq_r _ _ _ _ (H j)), (f_inst F _ f (h j)).
Qed.

(** ⋁ᵢ fᵢ entraîne ⋁ⱼ gⱼ dès que chaque fᵢ est un g_{h i}. *)
Lemma f_fex_map {I J : Type} (f : I -> F) (g : J -> F) (h : I -> J) :
  (forall i, f i ≡ g (h i)) -> fex f —[e_exE e_exI]→ fex g.
Proof.
  intros H. apply f_exE. intros i. apply (fent_eq _ _ _ _ (peq_sym (H i))), (f_exI _ g (h i)).
Qed.

End Reindex.
