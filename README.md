# Système formel — formalisation Rocq

Ce projet formalise en Rocq la couche syntaxique du framework : signatures à
spécifications d'ordre supérieur, termes en forme η-longue, contextes de de
Bruijn typés, renommages, η-expansion, substitution héréditaire et
substitution par des vecteurs. Il fournit aussi un σ-calcul à la Autosubst
pour les égalités de substitutions.

Dépôt : <https://github.com/Zellytog/Syst-me_formel_vibe_proving> (branche `main`).

Toutes les preuves sont complètes : aucun `Admitted`, et **aucun axiome**,
pas même l'extensionnalité fonctionnelle. Les vecteurs sont des objets finis
(des listes d'arguments), donc deux vecteurs dont les composantes coïncident
sont égaux par un simple lemme (`args_ext`).

## Compilation

Dépendances (testé avec ces versions) :

- Rocq 9.1.1 et la Stdlib Rocq 9.1.0 ;
- Equations 1.3.1 (`rocq-equations`) ;
- category-theory de John Wiegley, **version de développement** (testé au
  commit `db71856b9d4bc1e8964e38f9786270e0472fd6e1`, octobre 2026), installée
  de sorte que `From Category Require Import ...` fonctionne.

Les versions publiées de `coq-category-theory` sur le dépôt opam sont
anciennes et demandent un vieux Coq (d'où des contraintes comme
`ocaml < 4.12`). Il faut épingler le dépôt GitHub, dont le fichier opam
accepte Coq/Rocq ≥ 8.19 et < 9.2 et Equations 1.2 à 1.3 :

```sh
opam pin add -y coq-category-theory \
  "git+https://github.com/jwiegley/category-theory.git#db71856b9d4bc1e8964e38f9786270e0472fd6e1"
```

ou, sans opam pour cette bibliothèque (Equations doit être installée) :

```sh
git clone https://github.com/jwiegley/category-theory.git
cd category-theory && git checkout db71856b9d4bc1e8964e38f9786270e0472fd6e1
make -j && make install
```

```sh
make
```

**Temps de compilation.** La plupart des fichiers compilent en quelques
secondes, mais `theories/SetTheory/` (IZFε et sa conservativité sur IZF)
demande à lui seul **une quinzaine de minutes** sur une machine ordinaire
(compilation séquentielle) : `IZFSound.v`, `IZFSchema.v`, `IZFCons.v`,
`IZFRepl.v`, `IZFRecW.v`, `IZFRecX.v` et `IZFRec.v` prennent chacun de une
à trois minutes. Les dérivations y sont faites dans la syntaxe profonde,
et les vérifications de conversion entre instances des gros gabarits
(celui de rec en particulier) sont coûteuses. `make -j` aide peu, la chaîne
étant presque linéaire. Le modèle V(E) (`theories/VE/`) compile en une
vingtaine de secondes, dont une quinzaine pour `Sound.v`. Les extensions par définition
(`Extensions/Definitional.v` et `DefSound.v`) compilent en environ huit
secondes (deux et six).

## Organisation

Le développement est découpé en couches, chacune dans son dossier et
n'important que les couches inférieures. Les chemins logiques suivent les
dossiers : `SF.Syntax.Terms`, `SF.Calculus.System`, `SF.Logic.Judgment`, `SF.Functional.Arrow`, `SF.Quantifiers.Order`, `SF.Arithmetic.Arith`, `SF.SetTheory.Sets`, `SF.Extensions.Conservativity`, `SF.Models.Logic`, `SF.HA.Translation`, `SF.Fan.FT`, `SF.VE.Sound`.

### `theories/Syntax/` : la syntaxe

| Fichier | Contenu |
|---|---|
| `Spec.v` | `spec Srt := Spec (list spec) Srt`, contextes, variables typées `var Γ σ`, opérations `vl` / `vr` / `vsplit` sur `Θ ++ Γ`, principe d'induction `spec_rect'`, profondeur |
| `Terms.v` | signature, termes `tm Γ s` et arguments `args Γ Θ` (mutuels), renommages, affaiblissement `wk`, kits et traversée `trav`, application héréditaire `happ`, η-expansion `eta`, substitutions fonctionnelles internes `sub`, `subst` et leurs compositions |
| `Renaming.v` | calcul sur les variables (base `vsimpl`, tactiques `vcase` et `vsimp`), lois des renommages |
| `Traversal.v` | extensionnalité des kits, interaction traversée/renommage, naturalité de `happ` |
| `Eta.v` | lois η de l'application héréditaire, substitution identité, `eta_subst`, `happ_subst`, `ren_as_subst` |
| `Composition.v` | composition des traversées, **lemme de substitution héréditaire** `happ_commutes`, associativité `subst_subst` |
| `Vectors.v` | **vecteurs** `vec Γ Δ := args Δ Γ`, `vsubst`, `vcomp`, `vid`, `vcat`, `vup`, `vren`, `vpre`, leur algèbre par de vraies égalités, tactique `asimpl` |
| `Syn.v` | **la catégorie syntaxique** (instance `Category` de category-theory) et sa structure cartésienne fermée : `Syn_Terminal`, `Syn_Cartesian`, `Syn_Closed` |
| `Examples.v` | le λ-calcul comme signature, la règle β écrite avec des métavariables et instanciée par un vecteur, un exemple de substitution réellement héréditaire |

### `theories/Calculus/` : les systèmes de calcul

| Fichier | Contenu |
|---|---|
| `System.v` | relations entre termes (`trel`) et leur extension aux vecteurs (`arel`) ; **système de calcul** : relation d'équivalence `conv` telle que `t ~ t'` et `v ≃ v'` impliquent `t[v] ~ t'[v']` ; décidabilité ; propriétés dérivées (stabilité par renommage, congruence pour les symboles et les variables, compatibilité avec `happ` et `vcomp`) |
| `Rules.v` | règles (couples de termes dans un contexte de métavariables), système **engendré** par une famille de règles, instances, minimalité (`generated_least`) |
| `SynConv.v` | **la catégorie syntaxique modulo un système de calcul**, cartésienne fermée : `SynConv`, `SynConv_Terminal`, `SynConv_Cartesian`, `SynConv_Closed` |
| `Examples.v` | le λ-calcul modulo β : une instance de β, la conversion sous un lieur, la CCC `Lambda_beta` |

### `theories/Logic/` : les systèmes logiques

| Fichier | Contenu |
|---|---|
| `Judgment.v` | formules (termes de sorte `P`), **règles de déduction** (contexte de métavariables, prémisses pouvant étendre le contexte de termes et les hypothèses, conclusion), **dérivabilité** `deriv C P R Γ Ξ φ` (axiome, conversion modulo `C`, instances de règles), méta-théorèmes génériques : affaiblissement des hypothèses `deriv_weaken`, réindexation `deriv_subst` (dont l'affaiblissement du contexte `deriv_wk`), coupure `deriv_cut` ; systèmes logiques `logic` |
| `Propositional.v` | classes de connecteurs `HasImp`, `HasAnd`, `HasOr`, `HasTop`, `HasBot` ; familles de règles par connecteur, tiers exclu ; combinaison `rsum` et inclusion `Includes` ; `ipc_rules`, `cpc_rules` ; règles dérivées de déduction naturelle (`imp_I`, `imp_E`, `and_I`, `and_E1`, `and_E2`, `or_I1`, `or_I2`, `or_E`, `top_I`, `bot_E`, `excluded_middle`) |
| `Examples.v` | une signature propositionnelle, des dérivations en logique intuitionniste et classique (¬¬A ⊢ A), réindexation et coupure en action |

### `theories/Functional/` : la couche fonctionnelle

| Fichier | Contenu |
|---|---|
| `Arrow.v` | classe `Functional` : **relation** `Arr a b c` (« c est une sorte flèche de a vers b ») au lieu d'une opération partielle, symboles `s_lam`, `s_app` indexés par un témoin ; schémas β et η, familles `beta_rules`, `eta_rules`, systèmes `beta_system`, `beta_eta_system` ; conversions dérivées `beta_conv` (app(λx.t, u) ~ t[u/x]) et `eta_conv` |
| `Graded.v` | **bornes** `bound` : un entier (coercion `fin`) ou `omega`, avec `blt`/`ble` ; graduation (n,p) comme donnée `gr`, cohérence avec `Arr` (`garr`), systèmes d'ordre (n,p) (`Bounded` : sortes sous la borne, flèches du bord présentes), sortes `quantifiable`, grade de `P` ; `predicate_sort` : les prédicats sur une sorte quantifiable existent |
| `Examples.v` | le λ-calcul simplement typé (β, η, graduation) ; un système **tronqué** d'ordre (1,0), avec N et les N^k → N, sans sorte (N → N) → N |

### `theories/Quantifiers/` : quantificateurs et logiques d'ordre (n,p)

| Fichier | Contenu |
|---|---|
| `Quant.v` | classes `HasForall s`, `HasExists s`, `HasEq s` (lieurs `Spec [Spec [ι s] P] P` et égalité) ; schémas ∀I/∀E, ∃I/∃E, réflexivité et transport ; règles dérivées `all_I`, `all_E`, `ex_I`, `ex_E`, `eq_refl_d`, `eq_subst`, `eq_sym_d`, `eq_trans_d` |
| `Order.v` | classe `Quantifiers n p` : symboles ∀, ∃, = **indexés par une preuve de quantifiabilité** ; familles de règles restreintes aux sortes quantifiables ; `iorder_rules`, `corder_rules` ; règles dérivées `qall_I`, `qall_E`, `qex_I`, `qex_E`, `qeq_refl`, `qeq_subst`, `qeq_sym`, `qeq_trans` |
| `Examples.v` | une logique du premier ordre vue comme logique d'ordre (1,1) : D quantifiable, Pr non ; instanciation, échange de ∀, ∃∀ ⊢ ∀∃, chaîne d'égalités |

### `theories/Arithmetic/` : systèmes arithmétiques

| Fichier | Contenu |
|---|---|
| `Arith.v` | classe `Arithmetic N r` : 0, S et des récurseurs `rec_s : [s, [N, s] → s, N] → s` **indexés par une preuve de `rec_ok r s`** (grade (m,0) avec m < r) ; règles de calcul rec(z, st, 0) ~ z et rec(z, st, S m) ~ st[m, rec(z, st, m)], système `arith_system` ; conversions dérivées `rec_zero_conv`, `rec_succ_conv` ; règles de déduction : schéma de récurrence (`ind_rules`) et S t ≠ 0 (`peano_rules`) ; règles dérivées `induction` et `succ_neq_zero` |
| `Inductive.v` | **types inductifs à arités finies** : une famille de sortes Wᵢ indexée par un type quelconque, chaque Wᵢ décrite par une liste de constructeurs, chaque constructeur par une liste de booléens (`true` : paramètre de sorte N, `false` : argument récursif) ; classe `Inductives` (constructeurs, récurseurs rec_{i,s} dont le pas reçoit chaque sous-terme et la valeur de l'appel récursif) ; règles de calcul `wrec_rules` et conversion dérivée `wrec_conv` ; récurrence `wind_rules` et règle dérivée `windI` ; les équations de rec comme règles de déduction (`weq_rules`) |
| `Examples.v` | une arithmétique d'ordre (1,1) à récursion de hauteur 1 (seul rec_N existe : récursion primitive) ; prédécesseur et addition, leurs calculs, injectivité de S, 1 ≠ 0, et 0 + t = t par récurrence |

### `theories/SetTheory/` : théorie des ensembles en déduction modulo

| Fichier | Contenu |
|---|---|
| `Sets.v` | classe `SetSig` : ∈, ∅, ω, paire, ⋃, 𝒫, compréhension `[V, [V] → P] → V`, remplacement `[V, [V] → V] → V`, description ι `[[V] → P] → V` ; **les axiomes d'appartenance sont des règles de calcul** (`mem_rules` : x ∈ ∅ ~ ⊥, x ∈ {a,b} ~ x = a ∨ x = b, x ∈ ⋃a ~ ∃y. y ∈ a ∧ x ∈ y, x ∈ 𝒫a ~ ∀z. z ∈ x ⇒ z ∈ a, x ∈ ω ~ x = ∅ ∨ ∃y. y ∈ ω ∧ x = S(y), x ∈ {z ∈ a ∣ φ} ~ x ∈ a ∧ φ(x), y ∈ {F(x) ∣ x ∈ a} ~ ∃x. x ∈ a ∧ y = F(x)) ; conversions dérivées `mem_empty`, `mem_pair`, `mem_union`, `mem_power`, `mem_omega`, `mem_compr` ; règles de déduction extensionnalité et description (`set_rules`), règles dérivées `extensionality`, `description` |
| `Examples.v` | une théorie des ensembles d'ordre (1,1) : ∅ est vide, a ∈ {a, b}, {z ∈ a ∣ φ} ⊆ a, a ∈ 𝒫(a), **Russell restreint** ({z ∈ a ∣ z ∉ z} ∉ a, preuve intuitionniste), {z ∈ a ∣ ⊤} = a par extensionnalité, ι z.(z = a) = a par description |
| `IZFe.v` | **IZFε** (d'après les notes « Notes on IZFε ») : sortes V, Pr ; ε primitive, ∈, ⊆, ≃ définies par axiomes ; ∅, ω, paire, ⋃, P faible ; la séparation, le remplacement et rec sont des **lieurs** (Sep : [V, [V] → Pr] → V, Repl : [V, [V, V] → Pr] → V, Rec : [[V] → Pr, [V, V] → Pr, V] → V), ce qui remplace la hiérarchie de langages Lₙ ; logique intuitionniste du premier ordre sur V avec l'égalité de Leibniz (intensionnelle) ; les axiomes sont des règles sans prémisse, les schémas des règles à métavariables de formule : **IZF⁻ε** (`izfm_rules`, déf. 1.3.2) et **IZFε** (`izfe_extra`, déf. 1.3.3) |
| `IZFeBasic.v` | premiers développements dans IZF⁻ε : instances d'axiomes (`axm`), application d'un lemme ouvert par un vecteur de termes (`use`) ; lemmes 1.5.1 à 1.5.6 : x ⊆ x par ε-induction (`sub_refl`), a ε x → a ∈ x (`eps_mem`), (∀a. a ∈ x → a ∈ y) → x ⊆ y (`sub_of_mem`), 1.5.4 sans récurrence (`sub_mem_trans`), **transitivité de ⊆ par ε-induction sur le terme du milieu** (`sub_trans_all`, `sub_trans`), ≃ symétrique et transitive (`eqv_sym`, `eqv_trans`), x ⊆ y ↔ ∀a. a ∈ x → a ∈ y (`mem_of_sub`, `sub_iff_mem`) |
| `IZFeExt.v` | axiome/lemme 1.5.8 : extensionnalité pour les formules de L_IZF (prédicat `lizf` : ∈, ⊆, ≃ entre variables, connecteurs, ∀/∃ sur V). Congruence de ∈, ⊆, ≃ pour ≃ (`congr_gen`) ; relation `erel` entre substitutions, stable par affaiblissement et par passage sous un lieur (`erel_up`) ; **théorème `ext_lizf`** : si w ≃ w′ point par point, Ξ ⊢ φ[w] entraîne Ξ ⊢ φ[w′], par récurrence sur φ (le cas ⇒ utilise la récurrence dans l'autre sens) ; corollaire `ext_lizf1` : a ≃ b, φ(a) ⊢ φ(b). Aucun axiome |
| `IZFeIZF.v` | **théorème 1.5.9 : IZF⁻ε étend IZF** (`izfm_extends_izf`), IZF étant lu dans L_IZF avec ≃ pour égalité : réflexivité et transport de l'égalité (`izf_refl`, `ext_lizf1`) ; extensionnalité, paire, réunion, parties (a ⊆ x → a ∈ p, par séparation puis partie faible), vide, infini (successeur caractérisé par z ∈ m ↔ z ∈ n ∨ z ≃ n), chacun comme formule close (`izf_ext`, `izf_pair`, `izf_union`, `izf_power`, `izf_empty`, `izf_inf`) ; séparation, collection et ∈-induction prouvées pour une métavariable **extensionnelle** (`izf_sep`, `izf_coll`, `izf_ind` sous `ExtP`, `ExtR`), puis instanciées par toute formule de L_IZF avec paramètres (`izf_sep_lizf`, `izf_coll_lizf`, `izf_ind_lizf`), l'hypothèse venant de 1.5.8 (`ext_inst`, `extR_inst`) ; stabilité de L_IZF par renommage (`lizf_ren`). Aucun axiome |
| `IZF.v` | **IZF comme théorie à part** : signature `zsym` (∈ seul, connecteurs, ∀/∃ sur V, égalité de Leibniz sur V), logique intuitionniste d'ordre (1,1), axiomes `izf_rules` : extensionnalité, paire, réunion, parties (a ⊆ x → a ∈ p), infini (ensemble inductif), séparation, collection, ∈-induction (schémas à métavariable de formule) |
| `IZFTr.v` | **traduction τ de IZF⁻ε dans IZF** (élimination des définitions) : un terme t de sorte V devient son **graphe** D_t (une formule à variable 0 pour la valeur), une formule une formule ; ε et ∈ deviennent ∈, ⊆ l'inclusion, ≃ et = l'égalité ; chaque symbole est l'instance d'un **gabarit** (`Frel`, `Fpair`, `Funion`, `Fpower` (ensemble des parties), `Fsep`, `emptyT`, `omegaT` (plus petit point fixe z ∈ y ↔ z vide ∨ ∃b ∈ y. z = S(b)), `Frepl`) ; Repl est traduit par la **construction totale** de 1.5.11, y ≜ {z ∣ (∀α ∈ a. ∃!β. R(α, β)) ∧ ∃α ∈ a. R(α, z)} (`FnAt`, `ExIn`), Rec par la **construction des essais**, y ≜ {z ∣ ∃f. f essai ∧ ∃v. ⟨a, v⟩ ∈ f ∧ z ∈ v} (`Frec` ; un essai est un ensemble de couples de Kuratowski fonctionnel, clos vers le bas et correct : f(b) est l'ensemble de remplacement total pour R_f(α, β) ≜ ψ(f(α), β) ; l'argument φ ne sert pas) ; commutation aux renommages (`tr_ren`) |
| `IZFLog.v` | outils de dérivation dans IZF : règles sur ↔, ∀E/∃I en la variable 0, instanciation de deux variables (`inst2`, `zall2_E`), et **théorème de remplacement** (`repl`) : remplacer les prédicats unaires et binaires d'un gabarit par des prédicats équivalents donne une formule équivalente |
| `IZFVal.v` | **les graphes sont totaux et fonctionnels** dans IZF (`Tot`, `Fun`) : pour chaque gabarit, sous l'hypothèse que ceux de ses arguments le sont ; unicité de ∅, de S(n) et de ω (par ∈-induction) ; **existence de l'ensemble de remplacement** sans hypothèse (`tot_repl` : séparation de {α ∈ a ∣ Fn}, collection sur cet ensemble, puis séparation) |
| `IZFOmega.v` | **existence de ω** dans IZF : à partir d'un ensemble inductif w, N ≜ {n ∈ w ∣ n appartient à tout ensemble inductif} est le plus petit point fixe (`tot_omega`) |
| `IZFRecV.v` | **rec dans IZF, première partie** : couples de Kuratowski (existence `op_ex`, injectivité `op_inj`, intuitionniste) ; congruence de l'ensemble de remplacement total pour des relations égales sur b (`fn_cong`, `ex_cong`, `step_cong`, `step_uniq`) ; **unicité des essais** : deux essais s'accordent partout (`att_uniq`, par ∈-induction) ; un critère pour être un essai (`att_intro`) ; une réunion d'essais est un essai (`un_build`, `un_att`) ; fonctionnalité du graphe de rec (`fun_rec`) |
| `IZFRecW.v` | **rec dans IZF, seconde partie** : ajout d'un couple ⟨a, v⟩ à un essai défini sur a, v étant la valeur correcte (`ext_build`, `ext_att`) ; **existence d'un essai défini en tout a** (`att_ex`, par ∈-induction : collection des essais, séparation, réunion, ajout du couple) ; totalité du graphe de rec (`tot_rec`) |
| `IZFTrSem.v` | sémantique de la traduction dans les contextes d'ensembles (`vctx`) : le graphe de tout terme est total et fonctionnel (`tf_term`) ; **lemme de substitution** (`subst_tr`) : si chaque variable x est la valeur de w(x), τ(t[w]) ↔ τ(t) |
| `IZFSound.v` | correction des règles traduites : quantificateurs (`allE_sound`, `exI_sound`, via τ(φ[t]) ↔ ∃y. D_t(y) ∧ τ(φ)(y)), égalité (`eqR_sound`, `eqS_sound`) ; **clôture universelle** des métavariables d'ensembles (`closure_inst`) ; formules de L_IZF : la traduction équivaut à la lecture directe (`pcanon`, `pcanon_tr`) ; les axiomes sans métavariable de formule, prouvés dans IZF : appartenance, inclusion, ≃, paire, réunion, parties, vide, ω (`ax_mem0` … `ax_omega0`, avec le graphe du successeur `suc_graph`) |
| `IZFSchema.v` | correction des **schémas** (séparation, collection, ∈-induction) : après clôture, la métavariable de formule n'est appliquée qu'à des variables, et τ commute **exactement** avec ces substitutions, qui sont des renommages (`tr_inst_var`) ; relation `schP` entre un schéma et son gabarit dans IZF (ensembles : variables, Sep, P, Repl, Rec), `sch_tr` : τ(ψ[W]) = gabarit[τ(W)] ; gabarits prouvés une fois pour toutes (`tmpl_sep`, `tmpl_coll`, `tmpl_ind`) |
| `IZFCons.v` | **théorème 1.5.13 pour IZF⁻ε** : toute dérivation de IZF⁻ε dans un contexte d'ensembles se traduit en une dérivation de IZF (`izfm_sound`, par récurrence sur la dérivation, règle par règle) ; **IZF⁻ε est conservative sur IZF** (`izfm_conservative`, `izfm_conservative_closed`) : une formule de L_IZF (∈, ⊆, ≃, ainsi que ε et l'égalité de Leibniz) prouvée dans IZF⁻ε, lue dans IZF, y est prouvée. Aucun axiome |
| `IZFRepl.v` | **conservativité, étape 2** : IZF⁻ε plus les axiomes de IZFε autres que rec (remplacement, {α ε a ∣ φ} ε P(a), a ε P(x) → a ⊑ x), la théorie `RIZFr`, est conservative sur IZF (`izfr_sound`, `izfr_conservative`, `izfr_conservative_closed`) ; gabarits et preuves dans IZF pour le remplacement (`tmpl_repl`, qui utilise la construction totale) et la partie séparée (`tmpl_sp`), axiome clos des parties (`ax_power_sub0`). Aucun axiome |
| `IZFRecX.v` | le graphe de rec lu sur un essai f défini en a, de valeur v : z ∈ v ↔ z ∈ rec(a) (`recv_iff`), w = rec(a) ↔ w = v (`eqr_iff`), β ε rec(a) ↔ β ∈ v (`epsr_iff`), et (∃w. w = rec(α) ∧ ψ(w, β)) ↔ R_f(α, β) (`chi_rf`) |
| `IZFRec.v` | **conservativité, étape 3 : IZFε tout entier est conservative sur IZF** (`izfe_sound`, `izfe_conservative`, `izfe_conservative_closed`, théorème 1.5.13). Dans l'axiome de rec, ψ est appliquée au terme rec(α) : on passe par une variante (`ArecV`) où ψ(rec α, β) devient ∃w. w = rec(α) ∧ ψ(w, β), qui entraîne l'axiome en logique pure (`rec_var`, avec `eqL` et la monotonie de ∃!, `exu_mono`) et dont la traduction est l'instance d'un gabarit de IZF (`sch_rec`, `tmpl_rec`). Aucun axiome |

### `theories/Extensions/` : extensions et conservativité

| Fichier | Contenu |
|---|---|
| `Conservativity.v` | le cadre **abstrait**, pour des systèmes logiques sur des signatures quelconques : jugements `judg` (Γ, Ξ, φ), validité, classes de jugements (`jall`, `jincl`, `junion`, `jgoals`) ; **traductions** de jugements, traductions saines, forme structurée `strans` (contexte, formules, hypothèses ajoutées) ; **extensions** (traductions saines), identité et composition ; **conservativité** `conservative` et **conservativité partielle** `conservative_on E K` ; monotonie, union, composition et sa réciproque ; deux méthodes de preuve : `conservative_by_retraction` (une traduction saine en sens inverse) et `conservative_by_translations` (une traduction par jugement, comme la A-traduction de Friedman) |
| `RuleExt.v` | extensions par règles sur une même signature : inclusion de systèmes de calcul `sys_le`, monotonie de la dérivabilité `deriv_mono`, extension identité `rule_extension` ; **règles admissibles** et `admissible_conservative` (des règles admissibles donnent une extension conservative) |
| `Interpretation.v` | **interprétations** de signatures (sortes ↦ sortes, symboles ↦ termes), morphismes de signatures comme cas particulier ; traduction des spécifications `smap`, des contextes `cmap`, des termes `itm`/`tr` (par substitution héréditaire) ; interprétations de systèmes logiques avec **prédicats de relativisation** D_σ, hypothèses de relativisation `rel_hyps`, traduction des jugements `jtr` ; une interprétation saine donne une extension |
| `Commute.v` | **commutation de la traduction avec la substitution** : `tr_vsubst` (⟦t[v]⟧ = ⟦t⟧[⟦v⟧]) et `itm_happ` (⟦happ σ u b⟧ = happ ⟦σ⟧ ⟦u⟧ ⟦b⟧) ; lemme de traversée pour des kits reliés par la traduction (`ktr`, `itm_trav_mut`), récurrence sur la profondeur (`itm_happ_all`) ; renommages (`itm_ren_mut`, `ren_itm_mut`) et extensionnalité |
| `Soundness.v` | **correction des interprétations** : le système de L2 tiré en arrière (`pullback`) est un système de calcul, d'où la préservation des conversions dès qu'elle vaut sur les règles génératrices (`interp_conv`) ; `interp_sound` : conversions et règles préservées ⇒ traduction des jugements saine ; critère schématique `srule_sound` pour les règles dont les prémisses n'étendent pas le contexte |
| `Criterion.v` | **critère schématique général** : traduction d'une règle (`tr_rule`), dont les prémisses à variables propres deviennent des prémisses sur ⟦Λ⟧ avec les hypothèses de relativisation D(x) des nouvelles variables (`rel_ext`) ; `rule_tr_sound` : si la traduction d'une règle de L1 est une règle de L2, ses instances traduites sont admissibles ; transport des dérivations de ⟦Λ ++ Γ⟧ vers ⟦Λ⟧ ++ ⟦Γ⟧ (`deriv_ren`, `capp`), traduction des η-expansés (`itms_eta`) |
| `Admissible.v` | **correction par admissibilité** sur une classe de contextes Q : `tr_rule_adm F Q r` (la règle traduite est admissible dans L2 pour les contextes de Q, sous les hypothèses de relativisation) ; une règle de L2 l'est pour elle-même (`tr_rule_adm_rule`) ; `interp_sound_on` : conversions préservées, Q stable par les extensions des prémisses, toutes les règles traduites admissibles ⇒ tout jugement prouvable de contexte dans Q a une traduction prouvable |
| `Same.v` | **interprétations qui ne changent pas les sortes** : la même chaîne (traduction, commutation avec la substitution et l'application héréditaire, préservation des conversions, traduction des règles avec relativisation, correction par admissibilité `interp_sound_on`) sans `smap` ni `cmap`, donc sans rien à réduire quand les spécifications des symboles sont génériques ; les termes sans quantificateur sont traduits en eux-mêmes (`tr_pure`) |
| `Definitional.v` | **extensions par définition, la traduction** : signature étendue `xsym` (Sym + un symbole f : Df → b), plongement `emb` ; traduction par **continuations syntaxiques** `tr t Δ r w sp K` (la valeur de t, sous l'environnement w et appliquée à la pile sp, est passée à la formule à trou K ; f(u⃗) devient ∃y. φ(u⃗*, y) ∧ K[y]) ; positions « flottantes » (termes sans lieur, l'existentielle remonte) et « locales » (formules, traduites sur place) ; **couche du bord** : une vue des symboles (`symview` : lambda, app, autre) et une **pile d'arguments en attente** (`spine`) : app(F, u) évalue u puis traduit F avec sa valeur en attente, un lambda devant une pile non vide lie sa variable à la valeur de tête (le β-redex est contracté), toute autre tête reçoit la pile appliquée (`spK`, `apps`) ; commutation avec la substitution de l'environnement (`tr_vsubst`) ; une formule de L est traduite en sa forme β-réduite, convertible à elle-même si le calcul de L contient β (`tr_emb`, `el_emb`) |
| `DefSound.v` | **conservativité d'une extension par définition** : congruence des continuations (`tr_cong`), remplacement des équivalents dans une formule de L (`repl`), **ouverture** d'une valeur par la totalité et l'unicité (`open_mut`, avec pile ; `ex_det`), **lemme de substitution** comme relation logique (`hoistA_mut` pour des composantes termes, `hoistF_mut` avec des composantes formules), traduction des dérivations (`el_sound`) ; théorème `definitional_conservative` : si L ⊢ ∃y φ(x⃗, y) et L ⊢ φ(x⃗, y), φ(x⃗, y') ⇒ y = y', alors L + f + φ(x⃗, f(x⃗)) est conservative sur L pour les jugements de contexte du premier ordre, λ et app compris, sous l'hypothèse `HC'` (la traduction respecte le calcul de L') ; **le calcul de L'** : réécriture en contexte (`cstep`, `cconv`, contenue dans le calcul engendré : `cconv_generated`), respect de β (`beta_TRel`), de η (`eta_TRel`), des règles de calcul de L à métavariables du premier ordre (`rule_TRel`) et congruence (`TRel_tsym`, `TRel_tvar`), d'où `cconv_eqv` et le théorème `definitional_conservative_cc`, sans hypothèse sur la traduction ; congruences `cong_atom`, `cong_and`, `cong_ex` ; calcul trivial (`triv_conv`) |
| `Examples.v` | IPC ⊆ CPC ; IPC + (φ ⊢ ¬¬φ) est conservative sur IPC par admissibilité ; un morphisme de signatures (ajout d'un atome), le calcul de sa traduction, et la **correction** de l'interprétation de IPC dans IPC sur la signature agrandie (`incl_sound`), vérifiée règle par règle |

### `theories/Models/` : modèles

| Fichier | Contenu |
|---|---|
| `Calculus.v` | **modèle d'un système de calcul** dans une CCC : un morphisme de CCC depuis `SynConv` (`CartesianFunctor` et `ClosedFunctor` de category-theory, objet terminal préservé) ; interprétation dérivée des sortes (`sort_obj`), des symboles (`sym_mor`) et des termes (`sem`) ; deux termes convertibles ont la même interprétation (`sem_conv`), la substitution est la composition (`sem_vsubst`, `sem_tsym`) ; le **modèle syntaxique** (`syn_model`) |
| `Hyperdoctrine.v` | **hyperdoctrines de Heyting** : préordres de prédicats indexés par les objets, opérations ⊤ ⊥ ∧ ∨ ⇒, réindexation monotone, fonctorielle et compatible avec la structure de Heyting ; calcul dans une fibre |
| `Logic.v` | **modèle d'un système logique** (`lmodel`) : un modèle du calcul, une hyperdoctrine, un **prédicat générique** T au-dessus de ⟦P⟧ ; interprétation ⟦φ⟧ := M(φ)*(T), validité ⋀⟦Ξ⟧ ≤ ⟦φ⟧ ; **correction** (`soundness`) ; compatibilité des connecteurs avec la structure de Heyting (`bin_compat`, vérifiable sur la formule générique : `bin_compat_generic`) ; les règles de IPC sont saines dans tout modèle compatible (`ipc_sound`), le tiers exclu dans tout modèle booléen (`em_sound`) |
| `Quantifiers.v` | **structures de quantification** sur une sorte s (`qstruct`) : ∀_Γ et ∃_Γ adjoints à droite et à gauche à la réindexation le long de la projection M(Γ × [ι s]) → M Γ, avec Beck–Chevalley ; compatibilité des symboles (`all_compat`, `ex_compat`) ; correction de ∀I, ∀E, ∃I, ∃E (`all_sound`, `ex_sound`), Frobenius pour ∃E étant une conséquence ; le modèle syntaxique porte ces structures (`syn_qstruct`) |
| `Equality.v` | **égalité à la Lawvere** (`eqstruct`) : E_Γ, plus petit prédicat vrai le long de la diagonale δ : Γ × [ι s] → Γ × [ι s] × [ι s] ; ⟦t = u⟧ ≡ ⟨t, u⟩*(E_Γ) ; correction de la réflexivité et du transport (`eq_sound`) |
| `Order.v` | **modèles des logiques d'ordre (n,p)** : connecteurs compatibles, et une structure de quantification et d'égalité *pour chaque sorte quantifiable seulement* (`order_structure`) ; toutes les règles de la logique intuitionniste d'ordre (n,p) sont saines (`iorder_sound`), et celles de la logique classique dans un modèle booléen (`corder_sound`) ; `order_lmodel` |
| `Completeness.v` | le **modèle syntaxique** d'une logique contenant IPC : fibres = formules préordonnées par la prouvabilité, réindexation = substitution, T = la variable de [ι P] ; toute règle y est saine ; **complétude** (`completeness`) et équivalence entre prouvabilité et validité dans tous les modèles (`sound_complete`) |
| `SynOrder.v` | la **structure d'égalité du modèle syntaxique** : E_Γ := (x₁ = x₀), vraie le long de la diagonale par réflexivité, minimale par le transport (`syn_eqstruct`, `syn_eq_compat`) ; le modèle syntaxique de la logique intuitionniste d'ordre (n,p) porte une structure d'ordre (n,p) (`syn_order_structure`), d'où la **complétude structurelle** : valide dans tout modèle muni d'une structure d'ordre (n,p) ⇒ prouvable (`order_completeness`) |
| `Semantics.v` | **sémantique des termes dans une CCC** à partir de données concrètes (un objet par sorte, un morphisme ⟦dom σ⟧ → ⟦cod σ⟧ par symbole) : ⟦Θ → b⟧ := ⟦b⟧^⟦Θ⟧ (`ispec`), ⟦Γ⟧ := produit (`ictx`), ⟦t⟧ρ relatif à un environnement (`stm`, `sargs`, `stms`) ; extensionnalité, naturalité, renommage, η (`stms_eta`, `sargs_vid`) ; **lemme de substitution** ⟦t[v]⟧ρ ≈ ⟦t⟧ ∘ ⟦v⟧ρ (`stm_vsubst`), via un lemme de traversée pour les kits corrects et la correction de `happ` par récurrence sur la profondeur (`good_happ`) |
| `LLS.v` | **théorème de Lawvere–Lambek–Scott** : des données concrètes qui valident le calcul s'étendent en un morphisme de CCC `SynConv` → C (`lls_model`) ; foncteur (`lls_fun`), préservation du terminal, des produits (`sp_iso` : ⟦D ++ Γ⟧ ≅ ⟦Γ⟧ × ⟦D⟧, `lls_cartesian`) et des exponentielles (`eiso` : ⟦Γ^Δ⟧ ≅ ⟦Γ⟧^⟦Δ⟧, `lls_closed`) ; le modèle étend les données : `lls_sem` (un terme s'interprète par sa sémantique) et `lls_sym` (un symbole par le morphisme donné), à l'isomorphisme M[ι b] ≅ ⟦b⟧ près |
| `PSet.v` | **la catégorie `PSet` des setoïdes propositionnels** (équivalence à valeurs dans `Prop`), cartésienne fermée sans axiome ; objets discrets `disc A` (égalité de Leibniz), `PropS` (les propositions modulo ↔) |
| `SetModels.v` | **set-modèles** : l'hyperdoctrine des prédicats `phd` sur `PSet` (prédicats respectueux, implication point par point) ; pour tout modèle du calcul dans `PSet` et **toute** sorte, une structure de quantification (`set_qstruct`) et une structure d'égalité E⟨γ, a, b⟩ := a ≡ b (`set_eqstruct`) |
| `Tarski.v` | set-modèles **à partir de données** (un setoïde par sorte, un morphisme par symbole) : valeur ponctuelle `sval` ; pour un système **engendré par des règles, il suffit de valider les règles** (`pset_generated`) ; symboles logiques standard ⇒ modèle de la logique intuitionniste d'ordre (n,p) (`tarski_lmodel`) et correction tarskienne (`tarski_sound`) |
| `SetExamples.v` | le modèle standard de l'arithmétique d'ordre (1,1) de `Arithmetic/Examples.v` (N ↦ nat, rec_N ↦ `nat_rect`) ; 1 = 0 n'est pas prouvable, cohérence |
| `Frame.v` | **cadres d'évidence** (d'après Cohen–Miquey–Tate) : setoïde Φ de propositions, évidences, φ —e→ ψ ; identité, composition, ⊤, ∧, ⇒, ⋀ sur les **parties de Φ** (prédicats Φ → Prop, comme dans l'article) ; ⋀ indexé par un type **dérivé** (`fall` : ⋀ᵢ f(i) := ⋀{ψ ∣ ∃i. ψ ≡ f(i)}, polymorphe en univers, sans univers d'index fixé par le cadre) ; ⊥, ∨, ∃ **codés imprédicativement** avec leurs évidences ; changement d'index ; le cadre `prop_frame` (Φ = Prop, `prop_fall`) |
| `FrameModel.v` | **le tripos d'un cadre** (`fhd`) : prédicats X → Φ, ordre **uniforme** (une même évidence pour tous les points) ; pour tout modèle du calcul dans `PSet` et toute sorte, quantification ⋀/⋁ (`fqstruct`) et égalité de Leibniz E := ⋀_ψ (ψ a ⇒ ψ b) (`feqstruct`) |
| `FrameTarski.v` | modèles standard **à valeurs dans un cadre** : symboles logiques standard à ≡ près dans Φ (pour ⊥ et =, à **équivalence uniforme** près : `fequiv`) ⇒ modèle de la logique intuitionniste d'ordre (n,p) (`frame_lmodel`) ; correction **en réalisabilité** : une preuve donne une évidence uniforme (`frame_sound`, `frame_sound_closed`) |
| `FrameExamples.v` | le modèle standard de l'arithmétique repassé par la construction générique avec `prop_frame` ; cohérence par `frame_sound_closed` |
| `PCA.v` | **le cadre d'évidence d'une PCA** (`pca_frame`) : PCA donnée par une application partielle relationnelle et K, S (dont les applications partielles sont des fonctions, pour calculer les réalisateurs) ; expressions, évaluation, **abstraction** en S et K (`lam`, `lval`, `lam_ap`) ; identité, couples, projections ; Φ := parties de A, φ —e→ ψ := e envoie φ dans ψ, ⋀ par réalisateurs retardés (a·K) |
| `K1.v` | **K1, la PCA de Kleene sur ℕ** : les réalisateurs sont des codes de programmes d'un petit langage universel (entrée, constantes, couples de Cantor et projections, successeur, test à zéro, **appel universel**), exécutés par un interprète à carburant (`eval`) ; a·b ↓ c := le programme a sur b s'arrête sur c ; monotonie en carburant, **déterminisme** (`ap_det` : PCA au sens strict) ; K et S sont des programmes qui fabriquent des codes (gabarits `tpl`) ; l'équivalence avec les fonctions μ-récursives n'est pas prouvée |

### `theories/HA/` : HA_ω^{ω,ω} avec types inductifs, sa traduction dans le système libre, ses modèles

Tout le dossier est paramétré par une famille de types inductifs (un type d'indices `Ind` et des descriptions `dsc`) ; HA_ω^{ω,ω} au sens strict est le cas `Ind = ∅`.

| Fichier | Contenu |
|---|---|
| `Signature.v` | les types simples sur N, O et les Wᵢ (`ty`), leur graduation ; la signature (`hsym` : λ, app, 0, S, rec_s pour toute sorte de hauteur propositionnelle nulle, connecteurs, ∀_s, ∃_s, =_s pour toute sorte, constructeurs et récurseurs des Wᵢ) ; **HA** (logique d'ordre (ω,ω), β + règles de rec et de rec_W comme conversions, récurrence sur N et sur chaque Wᵢ, S t ≠ 0), **HAE** (la version équationnelle : les équations de rec_W sont des règles de déduction) et **Free**, le système « libre » (ω,ω,ω) : même logique, mêmes conversions plus la réécriture S t = 0 ~ ⊥, aucune règle arithmétique ; la relativisation D_N(x) := ∀X. X(0) ⇒ (∀n. X(n) ⇒ X(S n)) ⇒ X(x), D_W(x) := ∀X. Cl₁(X) ⇒ … ⇒ Clₙ(X) ⇒ X(x) (X clos par chaque constructeur), D_O := ⊤, D_{a→b}(f) := ∀x. D_a(x) ⇒ D_b(f x) ; l'interprétation `Rel` (identité sauf ∀/∃, relativisés), dans le cadre « même sorte » |
| `Closure.v` | **lemme de clôture** dans Free : sous D(x₁), …, D(xₖ), tout terme t : s vérifie D_s(t) (`closure`), par un lemme fondamental sur les vecteurs (`fundamental`) ; les cas λ/app par la définition de D_{a→b} et β, 0/S par celle de D_N, rec par la récurrence contenue dans D_N (X := λm. D_N(m) ∧ D_s(rec(z, st, m))) ; les constructeurs par celle de D_W (`DW_con`), rec_W par la récurrence contenue dans D_W (X := λy. D_W(y) ∧ D_s(rec(y, st⃗))), avec la conversion `wrec_conv` |
| `Translation.v` | **traduction de HA dans Free** : préservation des conversions (`HC`, les règles de calcul étant sans quantificateur), admissibilité de chaque règle traduite pour les contextes de sortes (`adm_allI`, `adm_allE`, `adm_exI`, `adm_exE`, `adm_ind`, `adm_peano`, `adm_wind`, `adm_all`) ; `ha_to_free` : Γ ∣ Ξ ⊢_HA φ ⇒ Γ ∣ D(Γ), Ξ^D ⊢_Free φ^D ; cas clos `ha_to_free_closed` |
| `Equational.v` | tout théorème de HAE est un théorème de HA (`hae_to_ha`) : chaque équation de rec_W se prouve par réflexivité modulo la conversion |
| `Model.v` | **un modèle de HA dans tout cadre d'évidence** : données N ↦ nat, O ↦ Φ, a → b ↦ ⟦b⟧^⟦a⟧, Wᵢ ↦ arbres finis (`wtree`), constructeurs et rec_W ↦ construction et récursion sur les arbres (validation de rec_W : `wrec_valid`), rec_s ↦ `nat_rect`, ∀/∃ ↦ ⋀/⋁, = ↦ Leibniz, sauf =_N ↦ « (a =? b) = true » et ⊥ ↦ « false = true » (Leibniz sur bool), pour valider S t = 0 ~ ⊥ à égalité près ; validation du calcul (β, rec, S t = 0 ~ ⊥ : `calc_valid`) ; modèle de Free (`free_model`, `free_sound`) ; **modèle de HA par composition** avec la traduction (`ha_sound`, `ha_sound_closed`) ; **cohérence de HA_ω^{ω,ω}** avec n'importe quelle famille de types inductifs (`ha_consistent`, cadre `prop_frame`), et de HAE (`hae_sound_closed`, `hae_consistent`) |
| `Realizability.v` | instanciation avec `pca_frame` : **tout théorème clos de HA est réalisé** dans toute PCA (`ha_realizable`) ; ⊥ n'est pas réalisé, d'où la cohérence (`ha_consistent_pca`) ; instances : la PCA triviale, et **K1** : tout théorème clos de HA est réalisé par un code (`kleene_realizable`) |

### `theories/Fan/` : le théorème de l'éventail (« Oracles just for Fan », section 5), énoncé dans HA_ω^{ω,ω} + listes

| Fichier | Contenu |
|---|---|
| `Ent.v` | **entailments uniformes** `ENT Γ Δ` (une évidence pour tous les paramètres) et leur logique : coupure, ⊤, ∧, λ et application, ⋀ (généralisation, instanciation), ∃ (introduction, élimination avec contexte), réindexation ; **vérité méta** [P] := ⋁_{p:P} ⊤ (`fprop_of`), introduction, transport, élimination |
| `Statement.v` | EFdata (codes ⌜n⌝ et, sous forme d'existentiels, les évidences de 0, S et de la récurrence) ; codes de fonctions, chemins, fonctionnelles ; Mono (le long des chemins codés, longueurs codées), Bar, Unif, **FT** ; les trois hypothèses en entailments uniformes : **recherche** (Markov interne : ⌜f⌝ ∧ [∃n, f n = 0] ≤ ∃n. ⌜n⌝ ∧ [f n = 0]), **existentiel fort** au type (N→B)→N (AC₁,₀ sur les codes), **continuité partout** (⌜F⌝ ≤ [F continue en tout α]) ; WKL et Markov méta ; énoncé `robust_fan` |
| `PR.v` | **récursion primitive avec oracles** dans tout EFdata : `RZ Γ f`, constantes, S, récursion (`rz_rec`), appel d'oracles, abstraction en codes de fonctions et de chemins ; arithmétique réalisée et corrigée : +, pred, −, ×, tests, ≤, <, parité, div2, bits, 2ⁿ, ∧ |
| `Bounded.v` | quantificateurs bornés `ball`, `bex` et recherche bornée `blast`, avec leurs spécifications |
| `Meta.v` | le **lemme méta** (`fan_meta`) : sous WKL et Markov, une fonctionnelle continue partout a une borne uniforme décidable C'_G(n) ; `t0_meta` : ce que cherche le réalisateur |
| `Robust.v` | **le théorème robuste abstrait** (`fan_realized`, `robust_fan_holds`) : tout EFdata avec recherche, existentiel fort et continuité réalise FT ; réalisateur explicite, uniforme en B ; la monotonie sert en α, avec les longueurs codées G(β) et n − G(β) |
| `Terms.v` | la signature de HA_ω^{ω,ω} avec **une sorte de listes d'entiers** L (nil, cons) ; termes de Gödel (sg, isz, pred, +, −, tests, ≤, <, parité, div2, bits, 2ⁿ, quantificateurs et recherche bornés, path, trunc, C'_G, j*) et sur L (`snoct` par rec_L, `pret` : α ↦ n ↦ sg∘α↾n) ; **leur valeur dans le modèle** de tout cadre (`pre_sem`, `cp_sem`, `jst_sem`…) |
| `FT.v` | **FT dans HA_ω^{ω,ω} + listes** : B : L → O, Mono (B(α↾n) ⇒ B(α↾(n+k))), Bar, Unif, sur α : N → N ; sa relativisée calculée (`ltr_FT : ltr Rel FT = FT^D`, par `reflexivity`) ; sémantique des formules (`sv_All`, `sv_Ex`, `sv_Imp`, `sv_And`, `sv_Dat`, `Dsem_arr`, `Dsem_N`, `sv_FTD`) ; **D_N est une donnée d'entiers sur tout cadre** (`efD`) ; transfert : les codes d'une EFdata quelconque et D_N sont uniformément équivalents (`code_N`, `N_code`), d'où FT(E) ≤ ⟦FT^D⟧ (`FT_FTS`) ; **le théorème** `ft_realized` (et `ft_realized_frame` sur un cadre quelconque avec D_N) ; `ha_not_refutes_FT` : sur une EF cohérente qui satisfait les hypothèses, HA + listes ⊬ ¬FT |
| `Worlds.v` | **le théorème 41 avec des mondes** : morphismes stricts d'EFdata (définition 35 : préservation des entailments, de ⊤, ∧, ⇒, ⋀ et des codes ; `smor_cfun`, `smor_cpath`, `smor_cfun2`), préordre de mondes avec minimum et foncteur W → EFdata ; conditions **en contexte** : recherche non bornée (définition 39, `search_of_unbounded`), choix dans E, continuité en contexte ⌜G⌝ ∧ ⌜α⌝ ≤ [G continue en α] sur un ensemble dense de mondes, tout α codé dans un monde futur (`paths`), **localité** (un fait méta entraîné dans un monde futur pour chaque α est entraîné dans E) ; `continuity_of_worlds`, puis `fan_worlds` : FT est réalisé dans le modèle de HA + listes sur E |
| `WKL.v` | **WKL dans HA_ω^{ω,ω} + listes**, le long des chemins : Tree(T) := ∀α ∀n. T(α↾(n+1)) ⇒ T(α↾n), Inf(T) := ∀n ∃β. T(β↾n), WKL := ∀T. Tree(T) ⇒ Inf(T) ⇒ ∃α ∀n. T(α↾n) ; relativisée calculée (`ltr_WKL`) et sémantique (`sv_WKLD`) ; **réduction abstraite** `wkl_reduce` : si un prédicat méta K sur les mots est clos par préfixe et a des témoins ℓₙ uniformément réalisés (⊤ ≤ ∀n. ⌜n⌝ ⊃ ⌜ℓₙ⌝), un réalisateur de WKL donne un réalisateur de ∃α. ⌜sg∘α⌝ ∧ ∀n. ⌜n⌝ ⊃ [K(α↾n)] (WKL appliqué à T(ℓ) := [K(ℓ)]) |

### `theories/Fan/Examples/` : deux modèles qui réalisent FT

| Fichier | Contenu |
|---|---|
| `Lam.v` | **le λ-calcul à oracles** de l'article (définitions 6 et 9, sans booléens ni listes) : termes de de Bruijn, renommages et substitutions parallèles et leurs lois, termes clos, numéraux, occurrences de constantes, **substitution d'un oracle par un terme** (`csub`), réduction paramétrée par l'interprétation des oracles, congruences, monotonie |
| `Confluence.v` | **confluence** (Tait–Martin-Löf–Takahashi : réduction parallèle, développement complet) ; un terme se réduit vers au plus un numéral (`num_unique`) |
| `Reach.v` | énumération des réduits, accessibilité bornée décidable, **extraction constructive** du numéral calculé (`eval_num`) |
| `Kripke.v` | **le modèle de réalisabilité de Kripke à oracles**, pour des mondes et une interprétation des oracles quelconques avec oracles frais : l'EF (familles croissantes de termes bien formés, évidences = termes clos sans oracle), l'EFdata (récurseur natif), ⊥ non réalisé ; **rejeu** d'une réduction en remplaçant un oracle (`replay`) ; les trois hypothèses : recherche (combinateur de Turing), continuité partout (oracle frais, rejeu, confluence), existentiel fort (substitution de l'oracle frais par un code quelconque) ; la localité de `Worlds.v` pour un seul monde (`k_locality`) ; **un chemin réalisé est calculable** avec les oracles du monde (`k_extract`) ; `kripke_fan` |
| `Instances.v` | **ESAT** (mondes = listes d'oracles, ordre préfixe) et la variante **« oracles partout »** (un monde, un oracle étiqueté par fonction, qui tient le rôle de K2) ; dans les deux, ⊥ n'est pas réalisé et FT est réalisé, sous la forme abstraite (`esat_fan`, `oracles_fan`) comme dans le modèle de HA + listes (`esat_ft`, `oracles_ft`) ; **HA + listes ne réfute pas FT** (`ha_not_refutes_FT_esat`, sous WKL et Markov méta) |
| `Kleene.v` | **le théorème 29** : énumération surjective des termes (`tm_of`), arbre de Kleene K (diagonale contre les termes sans oracle, réduits bornés par `Reach.reach`), clos par préfixe (`K_prefix`) et infini (`K_witness`) ; sous l'hypothèse `kleene_realized` (les témoins ℓₙ sont uniformément réalisés dans ESAT, ce qui demande un interpréteur universel écrit comme λ-terme), **ESAT ne réalise pas WKL** (`esat_not_wkl`), HA + listes ne prouve pas WKL (`ha_not_proves_WKL`), et ESAT sépare FT de WKL (`esat_separates`) |

### `theories/VE/` : les modèles V(E) de IZFε sur un cadre d'évidence (section 2.2)

Les ensembles sont des **arbres à la Aczel** à deux étages : une *forme*
(`shape := node (T : Type) (T → shape)`) et des *étiquettes* dans Φ en
chaque nœud. L'égalité de V(E) (le setoïde `Vset`) est : même forme (au
sens de Leibniz) et étiquettes ≡ point par point. Comme les cadres ne sont
pas invariants par bijection des index, les ⋁ indexés par les branches ne
sont propres que si les formes des constructions ne dépendent que des
formes des arguments : chaque construction donne sa forme explicitement,
ce qui évite toute extensionnalité fonctionnelle.

| Fichier | Contenu |
|---|---|
| `Trees.v` | formes, étiquettes (`lab`), V = Σ forme. étiquettes, `leq`, `teq`, le setoïde `Vset` ; accès aux branches au niveau des formes (`idxS`, `subS`, `labS`), `mk` |
| `Base.v` | α = β (Leibniz de Φ sur `Vset`), α ε a := ⋁ₜ aₜ ∧ α = a(t), et ⊆, ≃, ∈ bornés, définis par récurrence sur la forme du premier argument (une paire ⊆/⊇, `subP`, avec la symétrie `subP_swap`) : pas besoin de point fixe |
| `ND.v` | règles de déduction naturelle en contexte pour les évidences (`n_app`, `n_lam`, `n_exE`, `n_leib`, `n_sym`, `n_trans`, …) : les réalisateurs sont inférés, uniformes |
| `Real1.v` | réalisateurs des définitions de ∈ et ⊆ |
| `Cons.v` | ∅, {a, b} (étiquettes « booléens de Church » tagT/tagF), ⋃, séparation (étiquettes aₜ ∧ φ(a(t))), puissance (indexée par idx x → Φ₀, Φ étant **essentiellement petit** : `enc`, `dec`), successeur, ω |
| `Real2.v` | réalisateurs : vide, paire, réunion, séparation, puissance (les deux formes de IZFε), ω |
| `Ind.v` | la **ε-induction**, avec un combinateur de point fixe `yfix` en hypothèse nommée, sur des expressions d'évidence (`eexp`, définition 2.1.2) |
| `Coll.v` | la **collection** en hypothèse nommée (`coll`, propre, de spécification `coll_spec`, sur une famille indexée) ; l'ensemble de remplacement `vrepl`, `vrec` par récurrence sur la forme ; réalisateurs de la collection, du remplacement et de rec (`coll_real`, `W_to`, `W_from`) |
| `Model.v` | l'interprétation des sortes (V ↦ `Vset`, Pr ↦ Φ) et des symboles de IZFε ; les lieurs reçoivent des morphismes de setoïdes (`b1`, `b2`) |
| `Axioms.v` | chaque axiome de IZF⁻ε et de IZFε, sous forme sémantique « propre », est réalisé uniformément (`R_mem`, …, `R_rec`, `R_power_sub`) |
| `Sound.v` | **V(E) ⊨ IZFε** (théorème 2.2.2, `ve_sound`) : règles logiques par `FrameTarski`, axiomes par `fax_sound` et la tactique `psolve` (valeur calculée ≡ forme propre, en ne réduisant la valeur que par unification de tête, pour que le noyau ne compare jamais de gros termes réduits) ; dans `prop_frame`, **IZFε est cohérente** relativement à la collection (`izfe_consistent`) |
| `PCAFix.v` | **le point fixe dans toute PCA** : chaque expression de l'opérade a un point fixe (`pfix`, `pfix_spec`), le combinateur de Turing paresseux δδ avec δ := λw.λx. H (w w) x, où H calcule eeval en interne (`qexp`, `lq`) ; Φ = parties de A est petit (Φ₀ := A → Prop) ; d'où **V(A) ⊨ IZFε pour toute PCA sous la seule collection** (`ve_sound_pca`), et la réalisabilité de Kleene pour IZFε (`ve_sound_K1`) |

## Choix de conception

**Typage intrinsèque.** Un terme `t : tm Γ s` est bien typé par construction.
Une variable `x : var Γ σ` est un indice de de Bruijn qui porte sa
spécification.

```coq
Inductive tm : ctx -> Srt -> Type :=
| tvar {Γ σ} : var Γ σ -> args Γ (dom σ) -> tm Γ (cod σ)
| tsym {Γ σ} : Sym σ -> args Γ (dom σ) -> tm Γ (cod σ)
with args : ctx -> list spec -> Type :=
| anil {Γ} : args Γ []
| acons {Γ σ Θ} : tm (dom σ ++ Γ) (cod σ) -> args Γ Θ -> args Γ (σ :: Θ).
```

**Convention de de Bruijn.** Dans `Θ ++ Γ`, les variables de `Θ` sont les
plus récentes. Le corps d'un argument de spécification `Spec Θ b` vit dans
`Θ ++ Γ`, et le premier élément de `Θ` est l'indice 0. Le terme d'une
spécification σ dans Γ est `tms Γ σ := tm (dom σ ++ Γ) (cod σ)`.

**Vecteurs.** Un vecteur de Γ = [σ1,…,σn] vers Δ est une liste de termes
[t1,…,tn] avec `ti : tms Δ σi`, c'est-à-dire exactement `args Δ Γ`.
`vsubst t v` fait passer de `tm Γ s` à `tm Δ s`. Dans la catégorie des
contextes, c'est un morphisme Δ → Γ. Les substitutions fonctionnelles
`sub Γ Δ` ne servent qu'en interne, dans des énoncés point par point.

**Kits.** Toutes les opérations (renommage, instanciation, substitution) sont
des instances d'une seule traversée `trav`, structurelle sur le terme. Un kit
envoie chaque variable soit sur une variable, soit sur un corps accompagné
d'une fonction d'application.

**Substitution héréditaire.** `happ σ Ξ u a` instancie les variables liées
du corps `u : tms Ξ σ` par les arguments `a`. Elle est définie par
récursion structurelle sur σ : les appels récursifs portent sur les
spécifications de `dom σ`. Il n'y a ni carburant ni récursion bien fondée,
donc tout calcule par `reflexivity` (voir `Examples.v`).

**Termination des preuves.** Le lemme de substitution héréditaire
(`happ_commutes`) est prouvé par récurrence sur `depth σ + m`, où `m`
majore les profondeurs des spécifications substituées par le kit.

## La catégorie syntaxique (`Syn.v`)

- **Objets** : les contextes. **Morphismes** Γ ~> Δ : les vecteurs `args Γ Δ`
  (des termes de Γ pour les variables de Δ). Identité `vid`, composition
  `vcomp`. Les homs sont des setoïdes ; pour l'instant leur relation est
  l'égalité de Leibniz. La catégorie modulo conversion s'obtiendra en
  changeant seulement cette relation.
- **Terminal** : le contexte vide `[]`.
- **Produit** : `Γ × Δ := Δ ++ Γ` (les variables du second facteur sont les
  plus récentes). Appariement `vcat`, projections par vecteurs de variables
  η-expansées.
- **Exponentielle** : `Γ^Δ` remplace chaque spécification `Spec D c` de Γ par
  `Spec (D ++ Δ) c`. La curryfication est le renommage de réassociation
  `D ++ (Δ ++ Ξ) ≃ (D ++ Δ) ++ Ξ`. La propriété universelle découle de la
  naturalité de la décurryfication (`vuncurry_nat`).

Les quatre instances sont prouvées **sans axiome** (`Print Assumptions`).

## Systèmes de calcul (`Calculus/`)

- **Définition minimale.** Un système de calcul est une relation
  d'équivalence `conv` sur les termes (même contexte, même sorte) qui vérifie
  une seule condition : si `t ~ t'` et si les vecteurs `v`, `v'` sont reliés
  composante par composante, alors `vsubst t v ~ vsubst t' v'`. La stabilité
  par substitution et la congruence pour les symboles et les variables en
  découlent (`conv_tsym`, `conv_tvar`). La décidabilité est une propriété à
  part.
- **Règles.** Une règle est un couple de termes dans un contexte de
  métavariables. Une famille de règles, indexée par un type quelconque pour
  couvrir les schémas, engendre le plus petit système qui la contient.
- **Catégorie modulo conversion.** Mêmes objets, mêmes morphismes et mêmes
  constructions que `Syn` ; seule la relation de setoïde des homs change.

## Systèmes logiques (`Logic/`)

- **Pas d'opération sur les sortes à ce niveau.** La logique propositionnelle
  ne demande qu'une sorte `P` et des symboles. Les flèches entre sortes
  viendront avec la couche fonctionnelle, sous forme de *relation*
  `Arr a b c` plutôt que de fonction partielle.
- **Structures sur une signature.** Chaque connecteur est une classe : la
  signature *contient* un symbole de la bonne arité. Les couches ultérieures
  (arithmétique, quantificateurs, ordres (n,p)) ajouteront leurs propres
  classes sans modifier les précédentes.
- **Règles schématiques.** Une règle est donnée dans un contexte de
  métavariables et instanciée par un vecteur. Les prémisses peuvent étendre
  le contexte de termes : c'est ce qui servira pour ∀I et sa variable propre.
- **Méta-théorèmes une fois pour toutes.** L'affaiblissement, la
  réindexation et la coupure valent pour toute famille de règles.
- **Modularité des fragments.** Les familles de règles se combinent par
  somme ; les règles dérivées valent pour toute famille qui contient celles
  du connecteur (classe `Includes`).

## Couche fonctionnelle (`Functional/`)

- **Une relation plutôt qu'une fonction partielle.** `Arr a b c` est une
  famille de types ; les symboles lambda et app prennent un témoin. Une sorte
  trop haute n'a pas de témoin, ce qui donne la troncature sans `option` ni
  preuves de bornes dans les sortes. L'unicité de c est une propriété à part
  (`arr_functional`).
- **β et η comme schémas.** Une règle par témoin ; le corps `t(x)` de β est
  l'η-expansé de la métavariable t, ce qui rend l'instanciation immédiate
  (`vsubst_eta`). Les familles de règles de calcul se combinent par `crsum`
  et `CIncludes` (dans `Calculus/Rules.v`).
- **La graduation est une donnée**, contrainte par `Arr`. La borne (n,p) et
  la clôture « au bord » sont une classe à part ; on ne quantifiera que sur
  les sortes strictement sous la borne.
- **Bornes infinies.** Les bornes n, p de l'ordre et la hauteur r des
  récurseurs sont des `bound` : un entier ou ω. Avec n = ω ou p = ω, toutes
  les sortes de hauteur finie correspondante sont quantifiables ; avec
  r = ω, il y a des récurseurs à toutes les sortes de hauteur
  propositionnelle nulle. Grâce à la coercion `fin`, les entiers s'écrivent
  tels quels (`(n := 1)`).

## Quantificateurs (`Quantifiers/`)

- **Les quantificateurs sont des lieurs** de spécification
  `Spec [Spec [ι s] P] P`, l'égalité un symbole `Spec [ι s; ι s] P`.
- **Variable propre structurelle.** La prémisse de ∀I étend le contexte de
  termes ; les hypothèses y sont affaiblies, donc la variable propre
  n'apparaît pas dans Ξ par construction. Dans le schéma, la formule φ(x) de
  la prémisse est l'η-expansé de la métavariable φ sous le nouveau lieur.
  ∃E suit le même principe.
- **Ordre (n,p).** Les symboles de quantification et d'égalité demandent une
  preuve que la sorte est quantifiable (grade strictement sous (n,p)). Les
  familles de règles sont indexées par les sortes quantifiables et
  contiennent, pour chacune, les règles génériques de `Quant.v`.

## Arithmétique (`Arithmetic/`)

- **Deux bornes indépendantes.** L'ordre logique (n,p) borne les
  quantifications ; la hauteur `r` borne les récurseurs : rec_s n'existe que
  pour les sortes de grade (m,0) avec m < r. Comme pour les quantificateurs,
  le symbole demande une preuve, donc une signature ne peut pas en contenir
  de trop haut. Une hauteur propositionnelle nulle exclut l'élimination forte.
- **Calcul et déduction séparés.** Les équations de rec sont des règles du
  système de calcul ; la récurrence et S t ≠ 0 sont des règles de déduction.
  Dans les preuves, les calculs passent par `d_conv`.
- **Récurrence sans quantificateur.** Le schéma conclut φ(t) pour tout
  terme t ; le pas est une prémisse qui étend le contexte par une variable
  propre x, sous l'hypothèse φ(x). Il vaut donc aussi pour les sortes
  non quantifiables.

## Théorie des ensembles (`SetTheory/`)

- **Opérations comme termes.** Compréhension, remplacement et description
  sont des lieurs de la signature : ils prennent une formule ou une fonction
  en argument. Ce ne sont pas des quantifications, donc ils ne dépendent pas
  de l'ordre (n,p).
- **Déduction modulo à la Dowek–Miquel.** Chaque axiome d'appartenance
  devient une règle de calcul sur `P`, et les preuves les utilisent par
  conversion. La règle de ω se déplie sans fin : le système engendré n'est
  pas terminant, ce que la définition (une simple congruence) autorise.
- **Le reste en déduction.** L'extensionnalité et la description ne sont pas
  des équivalences entre une proposition atomique et sa définition ; elles
  restent des règles de déduction, à prémisses avec variable propre.

## Extensions (`Extensions/`)

- **Deux niveaux.** La conservativité est définie abstraitement, sur des
  traductions de jugements quelconques ; les interprétations syntaxiques en
  sont une source. Les théorèmes génériques (composition, rétraction,
  famille de traductions) ne dépendent donc pas de la syntaxe.
- **Conservativité partielle.** Une classe K de jugements de la base ;
  l'extension est K-conservative si elle n'ajoute aucun jugement valide
  de K. La Π₂-conservativité est le cas où K est la classe des énoncés
  Π₂ clos. La méthode par famille de traductions couvre l'argument de
  Friedman, où la traduction dépend de l'énoncé.
- **Relativisation.** Une interprétation de systèmes logiques fournit, en
  plus des symboles, un prédicat D_σ par spécification ; la traduction d'un
  jugement ajoute D_σ(x) pour chaque variable x : σ du contexte. Pour un
  sous-type {x : S | P(x)}, D vaut P sur la nouvelle sorte et ⊤ ailleurs, et
  les quantificateurs relativisés ne sont que des interprétations de
  symboles.
- **Commutation avec la substitution.** Elle suit la preuve de
  `happ_commutes` : un lemme de traversée pour deux kits reliés par la
  traduction, dont le cas des variables substituées utilise la commutation
  avec `happ` à une profondeur plus petite, et une récurrence sur la
  profondeur. Les contextes ⟦D ++ Γ⟧ et ⟦D⟧ ++ ⟦Γ⟧, égaux mais pas
  définitionnellement, sont reliés par un renommage (`capp`).
- **Traduction bien typée sans transport.** `smap` ne se réduit pas sur une
  spécification variable ; la traduction des termes fait une analyse de cas
  sur σ là où le type doit se réduire, et prend l'environnement des
  variables après le filtrage (comme `ren_tm`).
- **Extensions par définition.** Pour éliminer un symbole f défini par
  ∀x⃗ ∃!y φ(x⃗, y), la traduction est écrite par continuation : chaque
  occurrence de f(u⃗) introduit ∃y. φ(u⃗, y) ∧ …, qui remonte jusqu'à la
  position de formule la plus proche. La difficulté est la substitution :
  t[u/x] traduit place une copie de l'existentielle de u à chaque
  occurrence de x, alors que l'instance de la règle dans L nomme une seule
  valeur. On la traite comme une relation logique : une composante terme
  est reliée à une valeur « déterminée » (`DetT` : pour toute
  continuation, la traduction équivaut à la continuation appliquée à la
  valeur), et l'ouverture (`open_mut`) fournit ces valeurs dans un contexte
  étendu, par la totalité, l'unicité donnant la détermination. Les
  formules de L respectent l'équivalence (`repl`) dès que les symboles de
  sorte P la respectent à leurs positions de formules : c'est le seul point
  où la logique du premier ordre intervient.
- **La couche du bord.** Un terme λ d'une sorte flèche non quantifiable
  n'a pas de valeur dans L (λx. f(x) n'est pas un terme de L), mais il
  n'apparaît qu'en tête d'une application. La traduction transporte donc
  une **pile** des valeurs des arguments en attente : un λ devant une pile
  non vide lie sa variable à la valeur de tête, ce qui contracte le
  β-redex au moment de la traduction. Les arguments de app étant de sorte
  non flèche, la valeur substituée ne crée jamais de nouveau redex : c'est
  « normaliser par β puis traduire », en une seule passe structurelle. Les
  valeurs déterminées (`DetS`) sont celles d'une application t·sp, et le
  lemme de substitution passe sous un λ en liant sa variable à la même
  valeur des deux côtés (`CRA_cons1`, `CRF_cons1`). La traduction d'une
  formule de L n'est plus elle-même mais sa forme β-réduite, d'où une
  conversion par β dans L. Pour η, il faut que la sorte flèche détermine son
  domaine, son codomaine et le témoin de `Arr` : λx. app(F, x) devant la
  pile v⃗ se traduit alors exactement comme F devant v⃗.

## Modèles (`Models/`)

- **Sémantique fonctorielle.** Un modèle du calcul est un morphisme de CCC
  depuis la catégorie syntaxique modulo conversion, à isomorphisme canonique
  près. La correction du calcul et l'interprétation de la substitution par
  la composition sont alors immédiates. Les données concrètes (objets pour
  les sortes, morphismes pour les symboles) s'en déduisent ; réciproquement
  (Lawvere–Lambek–Scott, `LLS.v`), des données concrètes qui valident le
  calcul s'étendent en un morphisme de CCC qui les redonne.
- **Lawvere–Lambek–Scott par environnements.** Un terme de Γ s'interprète
  relativement à un environnement ρ : ∀ σ, var Γ σ → X ~> ⟦σ⟧, et non
  directement sur ⟦Γ⟧ : sous les lieurs d'un argument, le contexte devient
  D ++ Γ, dont l'interprétation n'est pas définitionnellement ⟦Γ⟧ × ⟦D⟧.
  L'environnement relevé (`ext`) évite tout transport. La substitution étant
  héréditaire, le lemme de substitution suit `Commute.v` : un lemme de
  traversée pour les kits dont les fonctions d'application sont correctes,
  puis la correction de `happ σ` par récurrence sur la profondeur de σ.
- **Les isomorphismes canoniques sont explicites.** ⟦D ++ Γ⟧ ≅ ⟦Γ⟧ × ⟦D⟧ se
  prouve par la monomorphie conjointe des projections (`proj_ext`) ;
  ⟦b⟧^⟦D ++ Δ⟧ ≅ (⟦b⟧^⟦D⟧)^⟦Δ⟧ et ⟦Γ^Δ⟧ ≅ ⟦Γ⟧^⟦Δ⟧ sont construits à la
  main, car l'isomorphisme `exp_respects_iso` de la bibliothèque est opaque.
  La cohérence `fmap_curry` se déduit de `fmap_uncurry`, qui se calcule
  composante par composante sur Γ.
- **P représente les prédicats définissables.** Une formule est un
  morphisme Γ → [ι P] ; elle s'interprète par la réindexation du prédicat
  générique T. On ne demande pas que tout prédicat soit de cette forme : le
  modèle n'est pas forcément « plein », ce qui évite de retomber sur HOL.
- **Les règles sont des conditions sur le modèle.** Un modèle d'une logique
  est une structure où chaque règle est saine ; la correction en découle.
  Les propriétés structurelles (compatibilité des connecteurs, fibres
  booléennes) rendent saines les familles de règles correspondantes.
- **L'ordre (n,p) dans la sémantique.** Les quantificateurs sont des
  adjoints à la réindexation le long des projections Γ × [ι s] → Γ, et
  l'égalité un « ∃ le long de la diagonale » ; on ne les demande que pour
  les sortes quantifiables. Les sortes du bord sont interprétées, mais on
  ne peut ni quantifier ni comparer le long de leurs projections.
- **Complétude tautologique.** Le modèle syntaxique, dont les fibres sont
  les formules modulo prouvabilité, est un modèle de toute logique qui
  contient IPC ; un jugement valide partout y est valide, donc prouvable.
  Comme rien n'impose de modèle plein, cette sémantique est « à la Henkin ».
- **Set-modèles dans `PSet` plutôt que dans `Sets`.** La catégorie `Sets`
  de la bibliothèque est cartésienne fermée sans axiome, mais l'égalité de
  ses morphismes vit dans `Type`. Dans `PSet` (setoïdes à équivalence dans
  `Prop`), elle vit dans `Prop` ; on peut donc la prouver par récurrence sur
  une preuve de conversion, et un système engendré se valide en ne vérifiant
  que ses règles (`pset_generated`). Une catégorie des types nus demanderait
  l'extensionnalité fonctionnelle.
- **Cadres d'évidence et tripos.** Un prédicat sur X est une famille
  X → Φ ; l'ordre est uniforme : φ ≤ ψ s'il existe *une* évidence e avec
  φ(x) —e→ ψ(x) pour tout x. Les évidences dérivées (pour ∨, ∃, l'égalité,
  le changement d'index) ne dépendent que des évidences données, ce qui
  rend la construction stable. Φ est un setoïde, ce qui évite
  l'extensionnalité (pour la réalisabilité, des parties de E comparées par
  double inclusion, comme dans `PCA.v`). Seuls ⊤, ∧, ⇒ et ⋀ (sur les parties de Φ) sont primitifs ; ⊥, ∨ et ∃
  sont codés en quantifiant sur Φ lui-même. Le cas Φ = Prop redonne la
  sémantique tarskienne.
- **Complétude structurelle d'ordre (n,p).** Le modèle syntaxique porte aussi
  des structures de quantification et d'égalité pour chaque sorte
  quantifiable. Pour l'égalité, E_Γ est la formule x₁ = x₀ ; sa minimalité
  parmi les prédicats vrais le long de la diagonale est exactement le
  transport. La complétude vaut donc pour la notion *structurelle* de
  modèle d'ordre (n,p), et pas seulement pour « un modèle où chaque règle est
  saine ».

## HA et le système libre (`HA/`)

- **HA sans axiome arithmétique.** La récurrence n'est pas une règle de
  Free : elle est *contenue* dans la relativisation D_N, définie
  imprédicativement (ce qui demande X : N → O quantifiable, d'où l'ordre
  (ω,ω), ou au moins (2,1)). S t ≠ 0 devient la réécriture S t = 0 ~ ⊥.
- **Relativisation de toutes les sortes.** D est défini par récurrence sur
  les types : imprédicatif sur N, ⊤ sur O, héréditaire sur les flèches. Les
  conditions de clôture « s₁(t₁), …, sₙ(tₙ) ⇒ s(f(t⃗)) » ne sont pas des
  hypothèses : elles sont *prouvées* pour chaque symbole (`fundamental`).
- **Admissibilité plutôt qu'identité des règles.** Les règles
  propositionnelles et d'égalité se traduisent en elles-mêmes
  (`tr_rule_adm_rule`, par `reflexivity`) ; ∀I, ∀E, ∃I, ∃E, la récurrence
  et S t ≠ 0 se traduisent en règles seulement admissibles, et seulement
  pour les contextes de sortes (`sctx`), d'où `interp_sound_on`.
- **Modèle de HA par composition.** On ne construit pas de modèle de HA
  directement : on modélise Free, qui n'a aucune règle arithmétique, dans le
  tripos d'un cadre quelconque, et l'on pose ⟦φ⟧_HA := ⟦φ^D⟧_Free. La
  récurrence, qui ne vaut pas uniformément sur nat dans un cadre
  quelconque, est réalisée *à travers* D_N.
- **Règles de calcul à égalité près.** La réécriture S t = 0 ~ ⊥ demande
  ⟦S a = 0⟧ ≡ ⟦⊥⟧ dans Φ, ce que ne donnent pas l'égalité de Leibniz et le
  ⊥ codé. D'où =_N ↦ « (a =? b) = true » et ⊥ ↦ « false = true », qui se
  calculent l'un en l'autre, et une condition de compatibilité affaiblie en
  équivalence uniforme.

- **Types inductifs à arités finies.** Les paramètres sont de sorte N et
  les arguments récursifs de sorte Wᵢ, ce qui garde le modèle discret (des
  arbres finis). La relativisation D_W est imprédicative comme D_N ; la
  récurrence sur Wᵢ n'est donc pas une règle de Free, elle est contenue dans
  D_W. Les équations de rec_W existent en deux versions : des conversions
  (HA, la version d'usage) et des règles de déduction (HAE, la version que
  vise la conservativité par codage).
- **Interprétations « même sorte ».** Les spécifications des constructeurs
  et des récurseurs dépendent de la description, qui est un paramètre : la
  traduction générale, qui calcule ⟦σ⟧ par `smap`, ne se réduit plus. La
  relativisation ne change pas les sortes ; elle passe par la variante
  `Extensions/Same.v`, où une interprétation envoie f : σ sur un terme de
  spécification σ elle-même, et tous les symboles autres que ∀ et ∃ sont
  interprétés uniformément par f(x⃗).

## Le théorème de l'éventail (`Fan/`)

- **Tout en entailments.** Un EF n'a pas d'éléments : la preuve de
  l'article, qui raisonne sur *un* réalisateur de la barre, est reformulée
  sans points ni mondes. Les faits méta (« f s'annule », « F est continue »)
  sont portés par [P] := ⋁_{p:P} ⊤, sans contenu calculatoire, et produits
  dans l'entailment elle-même ; la recherche est donc une forme interne du
  principe de Markov.
- **La barre donne une fonctionnelle.** L'existentiel fort au type
  (N → B) → N remplace « regarder ce que calcule b » : tout dépend ensuite
  d'une fonctionnelle méta G, indice d'un ⋁.
- **Les oracles, c'est la continuité partout.** ⌜G⌝ ≤ [G continue en *tout*
  chemin] : dans ESAT, un réalisateur de ⌜G⌝ reste réalisateur dans le
  monde où α est un oracle. Les mondes de Kripke servent à prouver cette
  hypothèse, ils n'apparaissent plus dans le théorème.
- **Une barre décidable simple.** C_G(ℓ) :⇔ ∃ j ≤ |ℓ|, G(ℓ↾j 0^∞) ≤ j, sans
  énumération des mots ; les mots de longueur n sont les bits des k < 2ⁿ.
- **FT dans HA, sans EFdata imposée.** L'énoncé vit dans HA_ω^{ω,ω} +
  listes, et son interprétation est celle du modèle de HA sur un cadre
  quelconque (relativisation D). Les entiers de ce modèle (D_N) forment une
  EFdata sur tout cadre (`efD`) : les EFdata ne servent plus que de
  présentation des hypothèses. Le transfert ne dépend pas du choix des
  codes, car deux EFdata sur un même cadre ont des codes uniformément
  équivalents ; la preuve abstraite de `Robust.v` est donc réutilisée telle
  quelle. Deux ajustements à l'énoncé de l'article : la monotonie est
  énoncée le long des chemins (B(α↾n) ⇒ B(α↾(n+k)), avec α, n, k
  relativisés) et les chemins sont des α : N → N lus par sg.

- **Le théorème 41 en contexte.** Les conditions de l'article portent sur
  des réalisateurs (« pour tout t ⊩ ⊤ ≤ ⌜f⌝ »), alors qu'un EF abstrait n'a
  pas de points : on les énonce comme des entailments. Deux ingrédients
  implicites dans l'article deviennent des hypothèses : le **choix** (un
  réalisateur de ∀α. ∃n est un code de fonctionnelle) et la **localité**
  (ce qu'entraîne l'image de φ dans les mondes futurs, pour un fait méta,
  φ l'entraîne dans E), qui remplace le transport des réalisateurs le long
  des morphismes. Les EFdata restent nécessaires dans le foncteur : un
  morphisme strict préserve les codes, pas D_N (dont le ⋀ porte sur les
  prédicats de chaque fibre) ; le passage à HA se fait ensuite par
  l'équivalence des codes.

- **Les modèles à oracles.** L'application est la réduction quelconque
  (relationnelle) : les axiomes de l'EF ne demandent pas de stratégie. La
  confluence sert seulement à identifier les numéraux calculés. Un oracle
  *frais* (étiquette plus grande que toutes celles du réalisateur) donne à
  la fois la continuité (une réduction ne lit qu'un nombre fini de valeurs
  de l'oracle, on la rejoue avec un autre chemin) et l'existentiel fort (on
  substitue l'oracle par un code quelconque du même chemin : la valeur
  calculée par la barre ne dépend pas du code, ce que la preuve du
  théorème 28 utilise implicitement). Les réalisateurs d'un monde ne
  contiennent que des oracles interprétés dans ce monde.

## Résultats principaux

Sur les vecteurs (`Vectors.v`) :

- `vsubst_vid : vsubst t (vid Γ) = t`
- `vsubst_vsubst : vsubst (vsubst t v) w = vsubst t (vcomp v w)`
- `vcomp_assoc`, `vcomp_vid_l`, `vcomp_vid_r` : les vecteurs forment une catégorie
- `vcomp_vcat : vcomp (vcat Θ a v) w = vcat Θ (vsubst_args a w) (vcomp v w)`
- `happ_vsubst : happ σ u a = vsubst u (vcat (dom σ) a (vid Ξ))` (β comme substitution)
- `vsubst_happ : vsubst (happ σ u a) w = happ σ (vsubst_tms u w) (vsubst_args a w)`
- `vsubst_tms_vup`, `ren_vsubst`, `vsubst_ren`, `ren_as_vsubst`

Au niveau interne (`Eta.v`, `Composition.v`) : `subst_id`, `subst_subst`,
`subst_happ` (le lemme de substitution héréditaire), `happ_eta`, `eta_subst`.

## Limites actuelles

- `asimpl` est une base de réécriture, pas une procédure de décision complète
  comme celle d'Autosubst 2. Elle couvre les compositions usuelles.
- Les renommages restent des fonctions `ren Γ Δ`. Leurs lois sont énoncées
  sur les termes (`ren_ren`, `ren_id`), ce qui suffit pour `asimpl`. Si l'on
  veut aussi des égalités entre renommages, on pourra les représenter par des
  vecteurs de variables de la même façon.
- `apply` ne résout pas toujours l'instance `Includes` ; dans les exemples, la
  tactique `nd` enchaîne `eapply` et `typeclasses eauto`.
- Les règles dérivées de `Order.v` demandent les instances d'inclusion des
  familles de règles ; dans les exemples, la tactique `qap` enchaîne
  `eapply` et `typeclasses eauto`.
- Les règles dérivées n'agissent que sur le but. Pour utiliser une hypothèse
  modulo conversion, on dérive sa forme convertie par `d_conv` et l'axiome.
- Les conversions de `Sets.v` pour le remplacement ne sont pas encore
  énoncées comme lemmes dérivés : la règle est dans `mem_rules`, mais aucun
  exemple ne s'en sert.
- `smap f σ` ne se réduit pas pour σ variable, même si f est l'identité (pour
  les interprétations qui ne changent pas les sortes, la variante
  `Extensions/Same.v` contourne le problème) :
  l'interprétation d'un symbole de base « par lui-même » dans une signature
  agrandie ne se définit donc génériquement qu'avec un transport le long de
  l'égalité (propositionnelle) `smap g (smap Some σ) = σ`. C'est l'obstacle
  à lever pour énoncer génériquement les extensions par sous-sortes
  (seuls des exemples concrets, où les spécifications calculent, passent
  aujourd'hui par `reflexivity`).
- Extensions par définition (`DefSound.v`) : les positions d'arguments
  sont des termes sans lieur de sorte non flèche (autre que P), des
  formules liant de tels termes, ou les positions de λ et de app ; les
  symboles de sorte P doivent respecter l'équivalence à leurs positions de
  formules (`Hcong`, prouvée pour les prédicats, ∧ et ∃) ; les
  métavariables des règles sont des termes non flèches ou des formules à
  arguments de tels termes. Le bord est celui du premier ordre : les
  arguments de app sont de sorte non flèche, et les λ à valeur
  propositionnelle (b = P) ne sont pas traités. Pour un calcul de L'
  engendré par des règles, il reste à identifier ses conversions entre
  formules à la réécriture en contexte (`cconv`, dont l'inclusion dans le
  calcul engendré est prouvée, `cconv_generated`) : c'est un lemme
  générique sur les systèmes engendrés, indépendant de la traduction, qui
  demande une récurrence sur la profondeur des spécifications à cause de
  la substitution héréditaire. L'enveloppe dans le cadre abstrait
  (`extension`, qui demande la correction du plongement de L dans L')
  reste aussi à faire.
- Côté modèles, Lawvere–Lambek–Scott : l'existence du morphisme de CCC
  est prouvée, pas son **unicité** (à isomorphisme près) parmi les modèles
  qui redonnent les données. L'hypothèse de validation `Hc` porte sur toutes
  les conversions. Dans une CCC quelconque, on ne peut pas la déduire des
  seules règles génératrices : `gconv` est dans `Prop` et `≈` dans `Type`.
  Dans `PSet`, où `≈` est dans `Prop`, c'est fait (`pset_generated`).
- Cadres d'évidence : la définition est une reformulation (⇒ et ⋀ séparés,
  les parties de Φ étant des prédicats Φ → Prop) de celle de
  Cohen–Miquey–Tate, dont l'équivalence n'est pas prouvée. Le cadre de réalisabilité d'une PCA est construit
  (`PCA.v`). La correction ne couvre que la logique d'ordre (n,p) :
  le schéma de récurrence de l'arithmétique n'est pas validé directement
  dans le tripos d'un cadre quelconque (avec N ↦ nat et un ordre uniforme,
  il faudrait une évidence qui itère le pas). On le valide en passant par
  la relativisation à D_N (`HA/Model.v`).
- En dehors des cohérences obtenues par un modèle (l'arithmétique d'ordre
  (1,1) de l'exemple, HA_ω^{ω,ω} dans `HA/Model.v`, relativement à
  l'imprédicativité de `Prop`, et IZFε dans `VE/Sound.v`, relativement en
  plus à la collection), aucun résultat de cohérence ou de
  normalisation n'est prouvé. En particulier, rien n'est
  prouvé sur la terminaison des systèmes engendrés.
- Pour HA, la famille de relativisation D est **définie** sur la signature
  concrète `hsym`, et non prise en paramètre avec ses conditions de clôture
  en hypothèses : le schéma générique (une famille D_s quelconque, close par
  les symboles) reste à extraire de `Closure.v`. La traduction ne porte que
  sur les contextes de sortes. K1 est défini (`Models/K1.v`) par un langage
  universel à interprète ; son équivalence avec les fonctions μ-récursives
  (forme normale de Kleene) n'est pas prouvée, et l'extraction de
  programmes (un réalisateur de ∀x ∃y calcule une fonction) n'est pas
  encore énoncée.
- Types inductifs : la **conservativité** de HAE (équations de rec_W comme
  règles) sur HA_ω^{ω,ω} n'est pas encore prouvée (codage des Wᵢ dans N, pour
  des descriptions concrètes) ; celle de HA (équations comme conversions) sur
  HAE est ouverte : la réflexion des égalités en conversions rendrait
  l'extensionnalité dérivable.
- Pour FT (`Fan/`), ESAT et la variante « oracles partout » sont
  formalisés comme EFdata uniques ; le foncteur σ ↦ ESAT_σ de l'article
  (évidences pouvant contenir les oracles de σ), qui instancierait
  `fan_worlds`, ne l'est pas : seule la localité est vérifiée dans les
  modèles de Kripke (`k_locality`). La condition sur les chemins est la
  forme forte (tout α codé dans le futur), et non celle de l'article
  (chemins des arbres codés) ; une partie des termes de `Fan/Terms.v` (C'_G, j*, trunc,
  path, bornés) a sa sémantique calculée mais ne sert plus, la preuve
  abstraite construisant elle-même ces réalisateurs ; K2 littéral (l'algèbre de Kleene sur N^N) ne l'est pas, ni les
  booléens et listes du λ-calcul de l'article. La réfutation de WKL
  (théorème 29) repose sur l'hypothèse nommée `kleene_realized` : il
  faudrait, pour la lever, un codage des termes par des entiers et un
  λ-terme qui les exécute pendant n pas (un interpréteur universel), avec
  sa preuve de correction ; l'évaluation bornée méta est déjà là
  (`Reach.reach`). Le modèle utilise la
  réduction relationnelle plutôt que les ensembles saturés.
- Pour IZFε (`SetTheory/IZFe*.v`), la syntaxe, les deux théories,
  les lemmes 1.5.1 à 1.5.8, le théorème 1.5.9 et le théorème 1.5.13
  (IZFε est conservative sur IZF) sont formalisés. Pour 1.5.9,
  IZF n'est pas une théorie à part sur sa propre signature : ses axiomes
  sont énoncés dans L_IZF et prouvés dans IZF⁻ε, la logique étant la même ;
  la collection est la forme faible (sans ∀β ∈ c ∃α ∈ a), équivalente à la
  forte en présence de la séparation pleine. La conservativité est prouvée
  en trois étapes : IZF⁻ε (`IZFCons.v`), IZFε sans rec (`IZFRepl.v`),
  IZFε (`IZFRec.v`). Repl est traduit par la construction totale, le
  lemme 1.5.11 étant faux intuitionnistiquement dans le cas général ; rec
  par la construction des essais (une variante des fonctions héréditaires
  de 1.5.12, rendue totale de la même façon : la valeur en b est toujours
  l'ensemble de remplacement total, qui existe sans hypothèse), si bien
  que son graphe est total et fonctionnel sans hypothèse sur φ et ψ.
  Reste la section 1.4. La
  traduction ne porte que sur les contextes
  d'ensembles, et IZF n'est relié à `IZFeIZF.v` (1.5.9) que par la lecture
  des axiomes, pas par une traduction formelle.
- Pour V(E) (`VE/`), trois hypothèses nommées restent : Φ essentiellement
  petit (`enc`, `dec`, `dec_enc`), un combinateur de point fixe (`yfix`) et
  la collection (`coll`). La première ne vient pas de ⋀ (qui, sur les
  parties de Φ, n'impose aucun univers d'index), mais du modèle : V et Pr
  sont interprétés dans le même `PSet`, donc dans le même univers que Φ,
  alors que les branches de P(x), indexées par idx x → Φ₀, placent V
  strictement au-dessus de Φ₀. La collection ne se construit pas en Rocq sans
  axiome : il faudrait indexer par les témoins β ∈ V, d'un univers trop
  grand, et les choisir. Dans `prop_frame` et dans le cadre de toute PCA
  (`VE/PCAFix.v`, dont K1), Φ₀ et le point fixe sont fournis : seule la
  collection reste une hypothèse.
