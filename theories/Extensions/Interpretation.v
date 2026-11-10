(** * Interprétations entre signatures

    Une **interprétation** d'une signature Σ₁ dans Σ₂ envoie chaque sorte
    sur une sorte et chaque symbole f : σ sur un **terme** de Σ₂ de la
    spécification traduite, dans le contexte de ses arguments. Un **morphisme
    de signatures** (symbole ↦ symbole) en est le cas particulier où le terme
    est le symbole appliqué à ses arguments η-expansés.

    La traduction des termes remplace chaque symbole par son interprétation
    et normalise par substitution héréditaire (dans [vsubst]). Elle est
    paramétrée par une application des variables, ce qui permet de passer
    sous les lieurs sans transport le long de [map_app].

    Les spécifications sont traduites par [smap]. Pour σ variable,
    [smap σ] ne se réduit pas ; la traduction fait donc une analyse de cas
    sur σ (motif « convoy ») là où le type doit se réduire, ce qui la rend
    bien typée sans aucune réécriture.

    La relativisation ajoute, pour chaque variable du contexte, une
    hypothèse D_σ(x) ([rel_hyps]). Ce fichier fournit les traductions de
    jugements correspondantes ; la preuve générale de leur correction (le
    lemme de commutation avec la substitution) est l'étape suivante. *)

From Stdlib Require Import List.
Import ListNotations.
From SF.Syntax Require Import Spec Terms Vectors.
From SF.Calculus Require Import System.
From SF.Logic Require Import Judgment.
From SF.Extensions Require Import Conservativity.

(** ** Traduction des sortes, spécifications et contextes *)

Section SMap.
Context {S1 S2 : Type} (f : S1 -> S2).

Fixpoint smap (σ : spec S1) : spec S2 :=
  match σ with Spec D c => Spec (map smap D) (f c) end.

Definition cmap (Γ : ctx S1) : ctx S2 := map smap Γ.

Fixpoint cvar {Γ σ} (x : var Γ σ) : var (cmap Γ) (smap σ) :=
  match x in var Γ0 σ0 return var (cmap Γ0) (smap σ0) with
  | vz => vz
  | vs y => vs (cvar y)
  end.

(** Passage sous un lieur D. *)
Definition vlift {Γ Γ'} (D : ctx S1) (ρ : forall σ, var Γ σ -> var Γ' (smap σ)) :
  forall σ, var (D ++ Γ) σ -> var (cmap D ++ Γ') (smap σ) :=
  fun σ x => match vsplit D x with
             | inl z => vl Γ' (cvar z)
             | inr y => vr (cmap D) (ρ σ y)
             end.

Lemma cmap_app (Γ Δ : ctx S1) : cmap (Γ ++ Δ) = cmap Γ ++ cmap Δ.
Proof. apply map_app. Qed.

End SMap.

Arguments smap {S1 S2} f σ.
Arguments cmap {S1 S2} f Γ.
Arguments cvar {S1 S2} f {Γ σ} x.
Arguments vlift {S1 S2} f {Γ Γ'} D ρ σ x.

(** ** Interprétations *)

Section Interp.
Context {S1 S2 : Type} (Sym1 : spec S1 -> Type) (Sym2 : spec S2 -> Type).

Record interp := {
  i_srt : S1 -> S2;
  i_sym : forall σ, Sym1 σ -> Terms.tm Sym2 (cmap i_srt (dom σ)) (i_srt (cod σ))
}.

Record morphism := {
  m_srt : S1 -> S2;
  m_sym : forall σ, Sym1 σ -> Sym2 (smap m_srt σ)
}.

(** Un morphisme est une interprétation : f ↦ f(x₁, …, xₙ), les
    arguments étant les variables η-expansées. *)
Definition morph_interp (M : morphism) : interp := {|
  i_srt := m_srt M;
  i_sym := fun σ f =>
    match σ as σ0 return Sym2 (smap (m_srt M) σ0) -> Terms.tm Sym2 (cmap (m_srt M) (dom σ0)) (m_srt M (cod σ0)) with
    | Spec D c => fun g => @tsym _ Sym2 (cmap (m_srt M) D) (smap (m_srt M) (Spec D c)) g
                             (vid (Sym := Sym2) (cmap (m_srt M) D))
    end (m_sym M σ f)
|}.

Context (F : interp).
Local Notation fs := (i_srt F).
Local Notation sm := (smap fs).
Local Notation cm := (cmap fs).

Fixpoint itm {Γ s} (t : Terms.tm Sym1 Γ s) {struct t} :
  forall Γ', (forall σ, var Γ σ -> var Γ' (sm σ)) -> Terms.tm Sym2 Γ' (fs s) :=
  match t in Terms.tm _ Γ0 s0
        return forall Γ', (forall σ, var Γ0 σ -> var Γ' (sm σ)) -> Terms.tm Sym2 Γ' (fs s0) with
  | @tvar _ _ Γ0 σ x a => fun Γ' ρ =>
      match σ as σ0 return var Γ0 σ0 -> args Sym1 Γ0 (dom σ0) -> Terms.tm Sym2 Γ' (fs (cod σ0)) with
      | Spec D c => fun x a => @tvar _ Sym2 Γ' (sm (Spec D c)) (ρ _ x) (iargs a Γ' ρ)
      end x a
  | tsym c a => fun Γ' ρ => vsubst (i_sym F _ c) (iargs a Γ' ρ)
  end
with iargs {Γ Θ} (a : args Sym1 Γ Θ) {struct a} :
  forall Γ', (forall σ, var Γ σ -> var Γ' (sm σ)) -> args Sym2 Γ' (cm Θ) :=
  match a in args _ Γ0 Θ0
        return forall Γ', (forall σ, var Γ0 σ -> var Γ' (sm σ)) -> args Sym2 Γ' (cm Θ0) with
  | anil => fun Γ' ρ => anil
  | @acons _ _ Γ0 σ _ u a' => fun Γ' ρ =>
      @acons _ Sym2 Γ' (sm σ) _
        (match σ as σ0 return Terms.tm Sym1 (dom σ0 ++ Γ0) (cod σ0) ->
                               Terms.tm Sym2 (dom (sm σ0) ++ Γ') (cod (sm σ0)) with
         | Spec D c => fun u => itm u (cm D ++ Γ') (vlift fs D ρ)
         end u)
        (iargs a' Γ' ρ)
  end.

(** Traduction d'un terme dans son contexte traduit. *)
Definition tr {Γ s} (t : Terms.tm Sym1 Γ s) : Terms.tm Sym2 (cm Γ) (fs s) := itm t (cm Γ) (fun σ x => cvar fs x).

End Interp.

Arguments i_srt {S1 S2 Sym1 Sym2} i s.
Arguments i_sym {S1 S2 Sym1 Sym2} i {σ} c.
Arguments m_srt {S1 S2 Sym1 Sym2} m s.
Arguments m_sym {S1 S2 Sym1 Sym2} m {σ} c.
Arguments morph_interp {S1 S2 Sym1 Sym2} M.
Arguments itm {S1 S2 Sym1 Sym2} F {Γ s} t Γ' ρ.
Arguments iargs {S1 S2 Sym1 Sym2} F {Γ Θ} a Γ' ρ.
Arguments tr {S1 S2 Sym1 Sym2} F {Γ s} t.

(** ** Interprétations de systèmes logiques *)

Section Logics.
Context {S1 S2 : Type} {Sym1 : spec S1 -> Type} {Sym2 : spec S2 -> Type}.
Context (L1 : logic Sym1) (L2 : logic Sym2).

Local Notation P1 := (l_prop Sym1 L1).
Local Notation P2 := (l_prop Sym2 L2).

(** Une interprétation de L1 dans L2 envoie la sorte des propositions de L1
    sur celle de L2, et fournit pour chaque spécification σ un prédicat de
    relativisation D_σ sur une variable de spécification traduite. Pour une
    interprétation sans relativisation, D_σ vaut ⊤. *)
Record linterp := {
  li_sig : interp Sym1 Sym2;
  li_prop : i_srt li_sig P1 = P2;
  li_rel : forall σ, form Sym2 P2 [smap (i_srt li_sig) σ]
}.

Context (F : linterp).
Local Notation fs := (i_srt (li_sig F)).

Definition pcast {Γ} (t : Terms.tm Sym2 Γ (fs P1)) : form Sym2 P2 Γ :=
  match li_prop F in _ = Q return Terms.tm Sym2 Γ Q with eq_refl => t end.

Definition ltr {Γ} (φ : form Sym1 P1 Γ) : form Sym2 P2 (cmap fs Γ) := pcast (tr (li_sig F) φ).

(** Les hypothèses de relativisation du contexte : D_σ(x) pour chaque
    variable x : σ de Γ. *)
Fixpoint rel_hyps (Γ : ctx S1) : list (form Sym2 P2 (cmap fs Γ)) :=
  match Γ return list (form Sym2 P2 (cmap fs Γ)) with
  | [] => []
  | σ :: Γ0 => ren_tm (li_rel F σ) (fun τ (z : var [smap fs σ] τ) => vl (cmap fs Γ0) z)
               :: wk_list [smap fs σ] (rel_hyps Γ0)
  end.

(** La traduction des jugements : Γ | Ξ ⊢ φ ↦ ⟦Γ⟧ | D(Γ), ⟦Ξ⟧ ⊢ ⟦φ⟧. *)
Definition jtr : translation L1 L2 := strans (cmap fs) (fun Γ => ltr) rel_hyps.

(** **Correction** : la traduction est saine. C'est la propriété à établir
    pour chaque interprétation ; elle donne alors une extension. *)
Definition linterp_sound := sound jtr.

Definition linterp_extension (H : linterp_sound) : extension L1 L2 :=
  {| e_tr := jtr; e_sound := H |}.

End Logics.

Arguments li_sig {S1 S2 Sym1 Sym2 L1 L2} l.
Arguments li_prop {S1 S2 Sym1 Sym2 L1 L2} l.
Arguments li_rel {S1 S2 Sym1 Sym2 L1 L2} l σ.
Arguments ltr {S1 S2 Sym1 Sym2 L1 L2} F {Γ} φ.
Arguments rel_hyps {S1 S2 Sym1 Sym2 L1 L2} F Γ.
Arguments jtr {S1 S2 Sym1 Sym2 L1 L2} F j.
