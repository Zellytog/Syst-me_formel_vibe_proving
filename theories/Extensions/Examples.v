(** * Exemples d'extensions

    - IPC ⊆ CPC est une extension (par règles) ;
    - IPC + (φ ⊢ ¬¬φ) est une extension **conservative** de IPC, car la
      nouvelle règle est admissible ;
    - un morphisme de signatures (ajout d'un atome), le calcul de la
      traduction associée, et la **correction** de l'interprétation de IPC
      dans IPC sur la signature agrandie, vérifiée règle par règle par le
      critère schématique [srule_sound]. *)

From Stdlib Require Import List.
Import ListNotations.
From SF.Syntax Require Import Spec Terms Vectors.
From SF.Calculus Require Import System Rules.
From SF.Logic Require Import Judgment Propositional Examples.
From SF.Extensions Require Import Conservativity RuleExt Interpretation Commute Soundness.

Local Notation ι := (Spec [] Pr).

(** ** IPC ⊆ CPC *)

Definition IPC : logic psym := mklogic Pr triv ipc_rules.
Definition CPC : logic psym := mklogic Pr triv cpc_rules.

Definition ipc_cpc : extension IPC CPC :=
  rule_extension Pr triv triv ipc_rules cpc_rules (sys_le_refl triv) ltac:(typeclasses eauto).

(** ** Une extension conservative : la double négation introduite *)

Inductive dni_idx := DNI.

Definition dni_rules (i : dni_idx) : drule psym Pr :=
  match i with
  | DNI => {| d_ctx := [ι];
              d_prems := [prem (P := Pr) (Θ := [ι]) [] (mv vz)];
              d_concl := Neg (Neg (mv vz)) |}
  end.

Definition IPC_dni : logic psym := mklogic Pr triv (rsum ipc_rules dni_rules).

Definition ipc_dni : extension IPC IPC_dni :=
  rule_extension Pr triv triv ipc_rules (rsum ipc_rules dni_rules) (sys_le_refl triv)
    ltac:(typeclasses eauto).

(** La règle φ ⊢ ¬¬φ est admissible dans IPC. *)
Lemma dni_admissible : admissible Pr triv ipc_rules (dni_rules DNI).
Proof.
  intros Γ Ξ v Hp.
  assert (Hφ : deriv triv Pr ipc_rules Γ Ξ (aget vz v)).
  { generalize (Hp _ (or_introl eq_refl)). prop_simpl. exact (fun H => H). }
  cbn [dni_rules d_concl]. prop_simpl.
  nd (imp_I triv Pr ipc_rules).
  nd (imp_E triv Pr ipc_rules _ (aget vz v)).
  - apply d_ax; left; reflexivity.
  - apply (deriv_weaken _ _ _ Hφ). intros x Hx; right; exact Hx.
Qed.

Theorem dni_conservative : conservative ipc_dni.
Proof.
  apply admissible_conservative; [apply sys_le_refl|].
  intros [i|[]]; [exact (admissible_rule Pr triv ipc_rules i)|apply dni_admissible].
Qed.

(** Conséquence : ce que IPC + DNI dérive, IPC le dérive. *)
Corollary dni_reflect Γ Ξ φ : provable IPC_dni Γ Ξ φ -> provable IPC Γ Ξ φ.
Proof. intros H; exact (dni_conservative (mkJ Γ Ξ φ) Logic.I H). Qed.

(** ** Un morphisme de signatures : ajout d'un atome *)

Inductive psym2 : spec psort -> Type :=
| t_imp : psym2 (Spec [ι; ι] Pr)
| t_and : psym2 (Spec [ι; ι] Pr)
| t_or  : psym2 (Spec [ι; ι] Pr)
| t_top : psym2 ι
| t_bot : psym2 ι
| t_atom : psym2 ι.

#[export] Instance psym2_imp : HasImp psym2 Pr := {| c_imp := t_imp |}.
#[export] Instance psym2_and : HasAnd psym2 Pr := {| c_and := t_and |}.
#[export] Instance psym2_or  : HasOr psym2 Pr  := {| c_or := t_or |}.
#[export] Instance psym2_top : HasTop psym2 Pr := {| c_top := t_top |}.
#[export] Instance psym2_bot : HasBot psym2 Pr := {| c_bot := t_bot |}.

Definition incl_sym {σ} (c : psym σ) : psym2 (smap (fun s => s) σ) :=
  match c in psym σ0 return psym2 (smap (fun s => s) σ0) with
  | s_imp => t_imp
  | s_and => t_and
  | s_or => t_or
  | s_top => t_top
  | s_bot => t_bot
  end.

Definition incl : morphism psym psym2 := {| m_srt := fun s => s; m_sym := @incl_sym |}.

(** La traduction se calcule : l'interprétation de ⇒ est le symbole ⇒
    appliqué à ses arguments, et la substitution héréditaire la ramène à
    la même formule. *)
Example tr_incl :
  tr (morph_interp incl) (Γ := [ι]) (Imp (mv vz) Top) = Imp (Sym := psym2) (mv vz) Top.
Proof. reflexivity. Qed.

(** ** Correction de l'interprétation IPC ↪ IPC(Σ + atome) *)

Definition triv2 : system psym2 := generated (fun e : Empty_set => match e with end).
Definition IPC2 : logic psym2 := mklogic Pr triv2 ipc_rules.

(** Pas de relativisation : D_σ := ⊤. *)
Definition Fincl : linterp IPC IPC2 :=
  @Build_linterp _ _ _ _ IPC IPC2 (morph_interp incl) eq_refl (fun σ => Top).

(** Les règles de IPC, vues comme règles simples. *)
Local Notation MA := (mv vz).
Local Notation MB := (mv (vs vz)).
Local Notation MC := (mv (vs (vs vz))).

Definition ipc_s (i : imp_idx + (and_idx + (or_idx + (top_idx + bot_idx)))) : srule psym Pr :=
  match i with
  | inl ImpI => {| s_ctx := [ι; ι]; s_prems := [([MA], MB)]; s_concl := Imp MA MB |}
  | inl ImpE => {| s_ctx := [ι; ι]; s_prems := [([], Imp MA MB); ([], MA)]; s_concl := MB |}
  | inr (inl AndI) => {| s_ctx := [ι; ι]; s_prems := [([], MA); ([], MB)]; s_concl := And MA MB |}
  | inr (inl AndE1) => {| s_ctx := [ι; ι]; s_prems := [([], And MA MB)]; s_concl := MA |}
  | inr (inl AndE2) => {| s_ctx := [ι; ι]; s_prems := [([], And MA MB)]; s_concl := MB |}
  | inr (inr (inl OrI1)) => {| s_ctx := [ι; ι]; s_prems := [([], MA)]; s_concl := Or MA MB |}
  | inr (inr (inl OrI2)) => {| s_ctx := [ι; ι]; s_prems := [([], MB)]; s_concl := Or MA MB |}
  | inr (inr (inl OrE)) => {| s_ctx := [ι; ι; ι];
                              s_prems := [([], Or MA MB); ([MA], MC); ([MB], MC)]; s_concl := MC |}
  | inr (inr (inr (inl TopI))) => {| s_ctx := []; s_prems := []; s_concl := Top |}
  | inr (inr (inr (inr BotE))) => {| s_ctx := [ι]; s_prems := [([], Bot)]; s_concl := MA |}
  end.

Lemma ipc_s_eq i : ipc_rules i = to_drule (ipc_s i).
Proof. destruct i as [[]|[[]|[[]|[[]|[]]]]]; reflexivity. Qed.

(** La traduction de chaque règle est la même règle sur la signature
    agrandie : le calcul le vérifie. *)
Lemma ipc_s_tr i : l_rules psym2 IPC2 i = to_drule (tr_srule IPC IPC2 Fincl (ipc_s i)).
Proof. destruct i as [[]|[[]|[[]|[[]|[]]]]]; reflexivity. Qed.

Theorem incl_sound : linterp_sound IPC IPC2 Fincl.
Proof.
  apply interp_sound.
  - intros Γ s t u. apply (interp_conv (li_sig Fincl) triv2 (fun e : Empty_set => match e with end)).
    intros [].
  - intros i. cbn [l_rules IPC mklogic]. rewrite ipc_s_eq.
    apply srule_sound. exists i. apply ipc_s_tr.
Qed.

(** L'inclusion des formules de IPC dans celles de IPC(Σ + atome) est donc
    une extension. *)
Definition atom_extension : extension IPC IPC2 := linterp_extension IPC IPC2 Fincl incl_sound.
