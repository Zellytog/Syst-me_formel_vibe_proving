(** * Spécifications, contextes et variables

    Pour un ensemble de sortes [S], les S-spécifications sont définies par
    [Spec(S) := List Spec(S) * S]. On note [Spec Δ s] la spécification
    [Δ -> s]. Un contexte est une liste de spécifications ; les variables
    sont des indices de de Bruijn *typés*.

    Convention : dans [Θ ++ Γ], les variables de [Θ] sont les plus récentes
    (indices les plus petits). Le corps d'un argument de spécification
    [Spec Θ b] dans le contexte [Γ] vit donc dans [Θ ++ Γ], et le premier
    élément de [Θ] est l'indice 0. *)

From Stdlib Require Import List Arith Lia.
Import ListNotations.

Section Spec.

Context {Srt : Type}.

Inductive spec : Type := Spec (dom : list spec) (cod : Srt).

Definition dom (σ : spec) : list spec := match σ with Spec Θ _ => Θ end.
Definition cod (σ : spec) : Srt := match σ with Spec _ b => b end.

Definition ctx := list spec.

(** ** Variables typées *)

Inductive var : ctx -> spec -> Type :=
| vz {Γ σ} : var (σ :: Γ) σ
| vs {Γ σ τ} : var Γ σ -> var (τ :: Γ) σ.

(** Inversion « small inversion » d'une variable dans [τ :: Γ]. Elle
    calcule sur les constructeurs, sans axiome. *)
Definition var_inv {τ Γ} (P : forall σ, var (τ :: Γ) σ -> Type)
  (pz : P τ vz) (ps : forall σ (y : var Γ σ), P σ (vs y)) :
  forall σ (x : var (τ :: Γ) σ), P σ x :=
  fun σ x =>
  match x as x0 in var Δ σ0 return
    (match Δ as Δ0 return var Δ0 σ0 -> Type with
     | [] => fun _ => unit
     | τ' :: Γ' => fun x1 => forall P' : forall σ, var (τ' :: Γ') σ -> Type,
                     P' τ' vz -> (forall σ (y : var Γ' σ), P' σ (vs y)) -> P' σ0 x1
     end x0)
  with
  | vz => fun P' pz' _ => pz'
  | vs y => fun P' _ ps' => ps' _ y
  end P pz ps.

Lemma var_nil {σ} (x : var [] σ) : False.
Proof.
  refine (match x in var Δ _ return match Δ with [] => False | _ => True end with
          | vz => I | vs _ => I end).
Qed.

(** ** Variables et concaténation *)

(** Injection à gauche : une variable de [Θ] vue dans [Θ ++ Γ]. *)
Fixpoint vl {Θ σ} Γ (z : var Θ σ) : var (Θ ++ Γ) σ :=
  match z in var Θ0 σ0 return var (Θ0 ++ Γ) σ0 with
  | vz => vz
  | vs z' => vs (vl Γ z')
  end.

(** Injection à droite (affaiblissement) : une variable de [Γ] vue dans [Θ ++ Γ]. *)
Fixpoint vr (Θ : ctx) {Γ σ} (y : var Γ σ) : var (Θ ++ Γ) σ :=
  match Θ return var (Θ ++ Γ) σ with
  | [] => y
  | τ :: Θ' => vs (vr Θ' y)
  end.

(** Séparation d'une variable de [Θ ++ Γ]. *)
Fixpoint vsplit (Θ : ctx) {Γ σ} : var (Θ ++ Γ) σ -> var Θ σ + var Γ σ :=
  match Θ return var (Θ ++ Γ) σ -> var Θ σ + var Γ σ with
  | [] => fun x => inr x
  | τ :: Θ' => fun x =>
      var_inv (fun σ' _ => (var (τ :: Θ') σ' + var Γ σ')%type)
        (inl vz)
        (fun σ' y => match vsplit Θ' y with
                     | inl z => inl (vs z)
                     | inr y' => inr y'
                     end) σ x
  end.

Lemma vsplit_vl {Θ} Γ {σ} (z : var Θ σ) : vsplit Θ (vl Γ z) = inl z.
Proof.
  induction z as [Γ0 σ0|Γ0 σ0 τ0 z IH]; cbn; [reflexivity|].
  rewrite IH; reflexivity.
Qed.

Lemma vsplit_vr Θ {Γ σ} (y : var Γ σ) : vsplit Θ (vr Θ y) = inr y.
Proof.
  induction Θ as [|τ Θ IH]; cbn; [reflexivity|].
  rewrite IH; reflexivity.
Qed.

(** Toute variable de [Θ ++ Γ] est de la forme [vl z] ou [vr Θ y]. *)
Lemma vsplit_case Θ {Γ σ} (x : var (Θ ++ Γ) σ) :
  {z : var Θ σ | x = vl Γ z /\ vsplit Θ x = inl z} +
  {y : var Γ σ | x = vr Θ y /\ vsplit Θ x = inr y}.
Proof.
  revert σ x; induction Θ as [|τ Θ IH]; intros σ x.
  - right; exists x; split; reflexivity.
  - revert σ x.
    refine (var_inv _ _ _).
    + left; exists vz; split; reflexivity.
    + intros σ y; destruct (IH σ y) as [[z [-> E]]|[y' [-> E]]].
      * left; exists (vs z); cbn; rewrite E; split; reflexivity.
      * right; exists y'; cbn; rewrite E; split; reflexivity.
Qed.

(** ** Familles indexées par une liste de spécifications *)

Fixpoint All (P : spec -> Type) (Θ : list spec) : Type :=
  match Θ with
  | [] => unit
  | σ :: Θ' => (P σ * All P Θ')%type
  end.

Fixpoint all_get {P : spec -> Type} {Θ σ} (z : var Θ σ) : All P Θ -> P σ :=
  match z in var Θ0 σ0 return All P Θ0 -> P σ0 with
  | vz => fun p => fst p
  | vs z' => fun p => all_get z' (snd p)
  end.

(** ** Principe d'induction sur les spécifications

    L'hypothèse de récurrence porte sur les spécifications du domaine,
    désignées par des variables. *)
Fixpoint spec_rect' (P : spec -> Type)
  (H : forall Θ b, (forall σ, var Θ σ -> P σ) -> P (Spec Θ b)) (σ : spec) : P σ :=
  match σ with
  | Spec Θ b =>
      H Θ b (fun σ' z =>
        all_get z ((fix go (Θ0 : list spec) : All P Θ0 :=
                      match Θ0 with
                      | [] => tt
                      | τ :: Θ1 => (spec_rect' P H τ, go Θ1)
                      end) Θ))
  end.

(** ** Profondeur *)

Fixpoint depth (σ : spec) : nat :=
  match σ with
  | Spec Θ _ => S ((fix go (Θ0 : list spec) : nat :=
                     match Θ0 with
                     | [] => 0
                     | τ :: Θ1 => Nat.max (depth τ) (go Θ1)
                     end) Θ)
  end.

Fixpoint depths (Θ : list spec) : nat :=
  match Θ with
  | [] => 0
  | τ :: Θ1 => Nat.max (depth τ) (depths Θ1)
  end.

Lemma depth_Spec Θ b : depth (Spec Θ b) = S (depths Θ).
Proof. reflexivity. Qed.

Lemma depth_var {Θ σ} (z : var Θ σ) : depth σ <= depths Θ.
Proof. induction z; cbn; lia. Qed.

Lemma depth_dom {Θ} b {σ} (z : var Θ σ) : depth σ < depth (Spec Θ b).
Proof. rewrite depth_Spec; pose proof (depth_var z); lia. Qed.

End Spec.

Arguments spec Srt : clear implicits.
Arguments ctx Srt : clear implicits.
Arguments Spec {Srt} dom cod.
Arguments dom {Srt} σ.
Arguments cod {Srt} σ.
Arguments vz {Srt Γ σ}.
Arguments vs {Srt Γ σ τ} y.
Arguments vl {Srt Θ σ} Γ z.
Arguments vr {Srt} Θ {Γ σ} y.
Arguments vsplit {Srt} Θ {Γ σ} x.
Arguments All {Srt} P Θ.
Arguments all_get {Srt P Θ σ} z p.
