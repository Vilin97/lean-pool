/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import LeanPool.InfinitaryLogic.Methods.LocalColimit
import LeanPool.InfinitaryLogic.Methods.LocalEMSupport
import Mathlib.ModelTheory.Encoding

/-!
# The countable local atom/deForm family `ΓEMlocal`

The size bottleneck of the EM re-base, resolved. The EM term model's `EMContext` needs a
tail-indiscernible family `Γ` containing every de-substituted atom (`atom_mem`/`rel_mem`) and the
deForms of the truth-lemma family (`DeFormClosedForGammaStar`); the tail extraction
(`MorleyHanfExtractionTail`) delivers indiscernibility only over a **countable** `Γ`. Over
`skolemColim L` the atom diagram is uncountable and the context cannot be instantiated; this file
builds the countable replacement over `localColim s₀`.

**The factoring insight**: a de-substituted atom/deForm over a support `S : Finset J` depends on
its `Λ[[J]]`-terms only *through* their de-substitutions to `Fin S.card`-variable `Λ`-terms. So
the family of ALL such formulas — over EVERY linear order `J`, every support, every closed term —
factors through the **canonical (J-free) seeds** indexed by `Σ m, Λ.Term (Fin m)`-data, which are
countable whenever `Λ` is. Concretely, the local `locDeEqAtom`/`locDeRelAtom`/`locDeForm` are
*defined* as canonical seeds applied to `locDeTermFin`-images, so factoring is definitional and
membership in the canonical seeds is by construction.

Contents:
* Canonical seeds over any `Λ : Language.{0,0}`: `canonEqAtom(s)`, `canonRelAtom(s)`,
  `canonDeForm(s)` + countability (`canonEqAtoms_countable` etc.) from countable symbol types.
* The `J`-side de-substitution pipeline over any `Λ` (mirroring the `skolemColim`-specific chain
  in `EMTermModel.lean`; the generic pieces `deepRank`/`Term.varFinset_relabel` live in the
  shared `LocalEMSupport.lean`): `locJConstOf`, `locJSupport`, `locDeTermPos`, `locDeTermFin`,
  and the local atoms/deForm `locDeEqAtom`/`locDeRelAtom`/`locDeForm` with membership in the
  canonical seeds.
* The assembled family `ΓEMlocal s₀ = ΓlocalColim ∪ eq-atoms ∪ rel-atoms ∪ deForms(ΓlocalColim)`
  over `localColim s₀`, with `ΓEMlocal_countable`, the membership interface the future local
  `EMContext` instantiation will discharge (`locDeEqAtom_mem_ΓEMlocal` = `atom_mem`,
  `locDeRelAtom_mem_ΓEMlocal` = `rel_mem`, `locDeForm_mem_ΓEMlocal` = the deForm closure), and
  the enumeration `exists_ΓEMlocalEnum` in the exact shape the tail extraction consumes.

The GENERIC semantic (realize) bridges live in `LocalEMContext.lean`; the old
`skolemColim`-specific ones remain in `EMTermModel.lean`. This file is deliberately purely
syntactic.
-/

namespace FirstOrder.Language

/-! ### Canonical (J-free) seeds over a countable language -/

variable (Λ : Language.{0, 0})

/-- The **canonical equality atom** of two `Fin m`-variable terms: the arity-`m` formula
`t = u` with the variables rebound. Every de-substituted equality atom (over any `J`, any
support) is definitionally of this shape. -/
def canonEqAtom {m : ℕ} (t u : Λ.Term (Fin m)) : Λ.BoundedFormulaω Empty m :=
  BoundedFormulaω.equal (t.relabel Sum.inr) (u.relabel Sum.inr)

/-- The **canonical equality-atom seed**: all canonical equality atoms, over all arities. -/
def canonEqAtoms : Set (Σ n, Λ.BoundedFormulaω Empty n) :=
  Set.range fun p : Σ m, Λ.Term (Fin m) × Λ.Term (Fin m) =>
    (⟨p.1, canonEqAtom Λ p.2.1 p.2.2⟩ : Σ n, Λ.BoundedFormulaω Empty n)

/-- The canonical equality-atom seed is countable when `Λ`'s function symbols are: it is the
range of a map from `Σ m, (Λ.Term (Fin m))²`, countable by Mathlib's term encoding. -/
private theorem canonEqAtoms_countable (hf : Countable (Σ n, Λ.Functions n)) :
    (canonEqAtoms Λ).Countable := by
  have := hf
  have : ∀ m : ℕ, Countable (Λ.Term (Fin m)) := fun _ => inferInstance
  exact Set.countable_range _

/-- The **canonical relation atom**: a relation symbol applied to rebound `Fin m`-variable
terms. -/
def canonRelAtom {m l : ℕ} (R : Λ.Relations l) (ts : Fin l → Λ.Term (Fin m)) :
    Λ.BoundedFormulaω Empty m :=
  BoundedFormulaω.rel R fun i => (ts i).relabel Sum.inr

/-- The **canonical relation-atom seed**: all canonical relation atoms, over all arities and all
relation symbols. -/
def canonRelAtoms : Set (Σ n, Λ.BoundedFormulaω Empty n) :=
  Set.range fun q : Σ (m l : ℕ), Λ.Relations l × (Fin l → Λ.Term (Fin m)) =>
    (⟨q.1, canonRelAtom Λ q.2.2.1 q.2.2.2⟩ : Σ n, Λ.BoundedFormulaω Empty n)

/-- The canonical relation-atom seed is countable when `Λ`'s symbol types are. -/
private theorem canonRelAtoms_countable (hf : Countable (Σ n, Λ.Functions n))
    (hr : Countable (Σ n, Λ.Relations n)) : (canonRelAtoms Λ).Countable := by
  have := hf
  have := hr
  have : ∀ m : ℕ, Countable (Λ.Term (Fin m)) := fun _ => inferInstance
  have : ∀ l : ℕ, Countable (Λ.Relations l) := fun _ => sigma_mk_injective.countable
  exact Set.countable_range _

/-- The **canonical deForm** of a formula `φ` (arity `n`) along a tuple of `Fin p`-variable
terms: open the bound variables, substitute the terms, rebind the `p` positions — the
`openBounds → subst → relabel` template of `EMTermModel.deForm`, with the `J`-dependence already
factored out. -/
def canonDeForm {n : ℕ} (φ : Λ.BoundedFormulaω Empty n) {p : ℕ} (g : Fin n → Λ.Term (Fin p)) :
    Λ.BoundedFormulaω Empty p :=
  (φ.openBounds.subst g).relabel Sum.inr

/-- The **canonical deForm closure** of a base family `Γc`: all canonical deForms of its members,
over all target arities and term tuples. -/
def canonDeForms (Γc : Set (Σ n, Λ.BoundedFormulaω Empty n)) :
    Set (Σ n, Λ.BoundedFormulaω Empty n) :=
  ⋃ q ∈ Γc, Set.range fun r : Σ p, Fin q.1 → Λ.Term (Fin p) =>
    (⟨r.1, canonDeForm Λ q.2 r.2⟩ : Σ n, Λ.BoundedFormulaω Empty n)

/-- The canonical deForm closure of a countable family is countable. -/
private theorem canonDeForms_countable {Γc : Set (Σ n, Λ.BoundedFormulaω Empty n)}
    (hΓc : Γc.Countable) (hf : Countable (Σ n, Λ.Functions n)) :
    (canonDeForms Λ Γc).Countable := by
  have := hf
  have : ∀ m : ℕ, Countable (Λ.Term (Fin m)) := fun _ => inferInstance
  exact hΓc.biUnion fun _ _ => Set.countable_range _

/-- Membership constructor for the canonical deForm closure. -/
theorem canonDeForm_mem_canonDeForms {Γc : Set (Σ n, Λ.BoundedFormulaω Empty n)} {n : ℕ}
    {φ : Λ.BoundedFormulaω Empty n} (hφ : (⟨n, φ⟩ : Σ n, Λ.BoundedFormulaω Empty n) ∈ Γc)
    {p : ℕ} (g : Fin n → Λ.Term (Fin p)) :
    (⟨p, canonDeForm Λ φ g⟩ : Σ n, Λ.BoundedFormulaω Empty n) ∈ canonDeForms Λ Γc :=
  Set.mem_biUnion hφ ⟨⟨p, g⟩, rfl⟩

/-! ### The `J`-side de-substitution pipeline

Mirrors the `skolemColim`-specific chain of `EMTermModel.lean` over an arbitrary `Λ` (the generic
pieces `deepRank`, `deepRank_lt_card`, `Term.varFinset_relabel` live in the shared
`LocalEMSupport.lean`). The `loc` prefix disambiguates from the `skolemColim` versions. -/

variable (J : Type) [LinearOrder J]

/-- The `J`-constant carried by a function symbol of `Λ[[J]]`: only an arity-`0` symbol from the
`constantsOn J` summand is a skeleton constant. -/
def locJConstOf : {n : ℕ} → Λ[[J]].Functions n → Finset J
  | 0, Sum.inr j => {j}
  | _, _ => ∅

/-- The finite set of `J`-constants (skeleton constants) mentioned in a `Λ[[J]]`-term. -/
def locJSupport {α : Type} : Λ[[J]].Term α → Finset J
  | .var _ => ∅
  | .func f ts => (Finset.univ.biUnion fun i => locJSupport (ts i)) ∪ locJConstOf Λ J f

/-- The de-substituted term `constantsToVars t` uses only the variables `Sum.inl j` for `j` a
skeleton constant of `t`. -/
theorem locConstantsToVars_varFinset_subset (t : Λ[[J]].Term Empty) :
    t.constantsToVars.varFinset ⊆ (locJSupport Λ J t).image Sum.inl := by
  induction t with
  | var e => exact e.elim
  | @func l f ts ih =>
    rcases l with _ | l
    · rcases f with f' | c
      · simp [Term.constantsToVars, Term.varFinset]
      · simp only [Term.constantsToVars, locJSupport, locJConstOf, Term.varFinset]; rfl
    · rcases f with f' | c
      · simp only [Term.constantsToVars, Term.varFinset, locJSupport,
          show locJConstOf Λ J (Sum.inl f' : Λ[[J]].Functions (l + 1)) = ∅ from rfl,
          Finset.union_empty]
        intro x hx
        simp only [Finset.mem_biUnion, Finset.mem_univ, true_and] at hx
        obtain ⟨i, hxi⟩ := hx
        obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp (ih i hxi)
        exact Finset.mem_image.mpr ⟨y, Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ i, hy⟩, rfl⟩
      · exact c.elim

/-- The **de-substituted term at ordered support positions**: each skeleton constant `c_j`
becomes the `ℕ`-variable `deepRank S j`. -/
def locDeTermPos (S : Finset J) (t : Λ[[J]].Term Empty) : Λ.Term ℕ :=
  t.constantsToVars.relabel (Sum.elim (fun j => deepRank J S j) Empty.elim)

/-- The ordered-position term uses only variables `< S.card` once `S` covers the term's skeleton
constants. -/
theorem locDeTermPos_varFinset_subset {S : Finset J} {t : Λ[[J]].Term Empty}
    (hsub : locJSupport Λ J t ⊆ S) :
    (locDeTermPos Λ J S t).varFinset ⊆ Finset.range S.card := by
  rw [locDeTermPos, Term.varFinset_relabel]
  intro n hn
  obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hn
  obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp (locConstantsToVars_varFinset_subset Λ J t hx)
  simp only [Sum.elim_inl]
  exact Finset.mem_range.mpr (deepRank_lt_card (J := J) (hsub hj))

/-- The **de-substituted term at `Fin S.card` positions**: `locDeTermPos` with its variables
packaged as genuine `Fin S.card` indices. The finite-variable term through which every
`J`-dependent atom/deForm factors. -/
def locDeTermFin (S : Finset J) (t : Λ[[J]].Term Empty) (hsub : locJSupport Λ J t ⊆ S) :
    Λ.Term (Fin S.card) :=
  (locDeTermPos Λ J S t).restrictVar
    (fun x => ⟨x.1, Finset.mem_range.mp (locDeTermPos_varFinset_subset (Λ := Λ) (J := J) hsub x.2)⟩)

/-! ### Local atoms and deForm — canonical seeds applied to de-substituted terms -/

/-- The **local de-substituted equality atom**: definitionally a canonical equality atom, so its
membership in `canonEqAtoms` is by construction. -/
def locDeEqAtom (S : Finset J) (t u : Λ[[J]].Term Empty)
    (ht : locJSupport Λ J t ⊆ S) (hu : locJSupport Λ J u ⊆ S) :
    Λ.BoundedFormulaω Empty S.card :=
  canonEqAtom Λ (locDeTermFin Λ J S t ht) (locDeTermFin Λ J S u hu)

/-- **Factoring, equality case**: every local equality atom lies in the canonical (J-free) seed. -/
private theorem locDeEqAtom_mem_canonEqAtoms (S : Finset J) (t u : Λ[[J]].Term Empty)
    (ht : locJSupport Λ J t ⊆ S) (hu : locJSupport Λ J u ⊆ S) :
    (⟨S.card, locDeEqAtom Λ J S t u ht hu⟩ : Σ n, Λ.BoundedFormulaω Empty n)
      ∈ canonEqAtoms Λ :=
  ⟨⟨S.card, (locDeTermFin Λ J S t ht, locDeTermFin Λ J S u hu)⟩, rfl⟩

/-- The **local de-substituted relation atom**: definitionally a canonical relation atom. -/
def locDeRelAtom (S : Finset J) {l : ℕ} (R : Λ.Relations l)
    (ts : Fin l → Λ[[J]].Term Empty) (ht : ∀ i, locJSupport Λ J (ts i) ⊆ S) :
    Λ.BoundedFormulaω Empty S.card :=
  canonRelAtom Λ R fun i => locDeTermFin Λ J S (ts i) (ht i)

/-- **Factoring, relation case**: every local relation atom lies in the canonical seed. -/
private theorem locDeRelAtom_mem_canonRelAtoms (S : Finset J) {l : ℕ} (R : Λ.Relations l)
    (ts : Fin l → Λ[[J]].Term Empty) (ht : ∀ i, locJSupport Λ J (ts i) ⊆ S) :
    (⟨S.card, locDeRelAtom Λ J S R ts ht⟩ : Σ n, Λ.BoundedFormulaω Empty n)
      ∈ canonRelAtoms Λ :=
  ⟨⟨S.card, l, (R, fun i => locDeTermFin Λ J S (ts i) (ht i))⟩, rfl⟩

/-- The **local general de-substituted formula**: definitionally a canonical deForm of `φ`. -/
def locDeForm (S : Finset J) {n : ℕ} (φ : Λ.BoundedFormulaω Empty n)
    (ts : Fin n → Λ[[J]].Term Empty) (hsub : ∀ i, locJSupport Λ J (ts i) ⊆ S) :
    Λ.BoundedFormulaω Empty S.card :=
  canonDeForm Λ φ fun i => locDeTermFin Λ J S (ts i) (hsub i)

/-- **Factoring, deForm case**: the local deForm of any member of a base family lies in that
family's canonical deForm closure. -/
private theorem locDeForm_mem_canonDeForms {Γc : Set (Σ n, Λ.BoundedFormulaω Empty n)}
    (S : Finset J) {n : ℕ} {φ : Λ.BoundedFormulaω Empty n}
    (hφ : (⟨n, φ⟩ : Σ n, Λ.BoundedFormulaω Empty n) ∈ Γc)
    (ts : Fin n → Λ[[J]].Term Empty) (hsub : ∀ i, locJSupport Λ J (ts i) ⊆ S) :
    (⟨S.card, locDeForm Λ J S φ ts hsub⟩ : Σ n, Λ.BoundedFormulaω Empty n)
      ∈ canonDeForms Λ Γc :=
  canonDeForm_mem_canonDeForms Λ hφ _

/-! ### The assembled family `ΓEMlocal` over the local colimit -/

variable (s₀ : LocalStage)

/-- **The extracted-family candidate**: the colimit family together with the full canonical atom
seeds and the canonical deForm closure of the colimit family — everything the local `EMContext`'s
`hind`/`atom_mem`/`rel_mem`/deForm-closure obligations will quantify over. -/
def ΓEMlocal : Set (Σ n, (localColim s₀).BoundedFormulaω Empty n) :=
  ΓlocalColim s₀ ∪ canonEqAtoms (localColim s₀) ∪ canonRelAtoms (localColim s₀)
    ∪ canonDeForms (localColim s₀) (ΓlocalColim s₀)

/-- **The size bottleneck, resolved**: `ΓEMlocal` is countable — the family the tail extraction
(`MorleyHanfExtractionTail`) can actually serve, in contrast to the uncountable `skolemColim`
atom diagram. -/
theorem ΓEMlocal_countable : (ΓEMlocal s₀).Countable :=
  (((ΓlocalColim_countable s₀).union
      (canonEqAtoms_countable _ (localColim_fun_countable s₀))).union
    (canonRelAtoms_countable _ (localColim_fun_countable s₀) (localColim_rel_countable s₀))).union
    (canonDeForms_countable _ (ΓlocalColim_countable s₀) (localColim_fun_countable s₀))

/-- The colimit family sits inside `ΓEMlocal`. -/
theorem ΓlocalColim_subset_ΓEMlocal : ΓlocalColim s₀ ⊆ ΓEMlocal s₀ := fun _ hx =>
  Or.inl (Or.inl (Or.inl hx))

/-- **`atom_mem` discharger**: every local equality atom — over every `J`, support, and pair of
closed terms — lies in `ΓEMlocal`. -/
theorem locDeEqAtom_mem_ΓEMlocal (S : Finset J) (t u : (localColim s₀)[[J]].Term Empty)
    (ht : locJSupport (localColim s₀) J t ⊆ S) (hu : locJSupport (localColim s₀) J u ⊆ S) :
    (⟨S.card, locDeEqAtom (localColim s₀) J S t u ht hu⟩ :
      Σ n, (localColim s₀).BoundedFormulaω Empty n) ∈ ΓEMlocal s₀ :=
  Or.inl (Or.inl (Or.inr (locDeEqAtom_mem_canonEqAtoms _ J S t u ht hu)))

/-- **`rel_mem` discharger**: every local relation atom lies in `ΓEMlocal`. -/
theorem locDeRelAtom_mem_ΓEMlocal (S : Finset J) {l : ℕ} (R : (localColim s₀).Relations l)
    (ts : Fin l → (localColim s₀)[[J]].Term Empty)
    (ht : ∀ i, locJSupport (localColim s₀) J (ts i) ⊆ S) :
    (⟨S.card, locDeRelAtom (localColim s₀) J S R ts ht⟩ :
      Σ n, (localColim s₀).BoundedFormulaω Empty n) ∈ ΓEMlocal s₀ :=
  Or.inl (Or.inr (locDeRelAtom_mem_canonRelAtoms _ J S R ts ht))

/-- **deForm-closure discharger**: the local deForm of every colimit-family member lies in
`ΓEMlocal` — the content of the future local `DeFormClosedForGammaStar`. -/
theorem locDeForm_mem_ΓEMlocal (S : Finset J) {n : ℕ}
    {φ : (localColim s₀).BoundedFormulaω Empty n}
    (hφ : (⟨n, φ⟩ : Σ n, (localColim s₀).BoundedFormulaω Empty n) ∈ ΓlocalColim s₀)
    (ts : Fin n → (localColim s₀)[[J]].Term Empty)
    (hsub : ∀ i, locJSupport (localColim s₀) J (ts i) ⊆ S) :
    (⟨S.card, locDeForm (localColim s₀) J S φ ts hsub⟩ :
      Σ n, (localColim s₀).BoundedFormulaω Empty n) ∈ ΓEMlocal s₀ :=
  Or.inr (locDeForm_mem_canonDeForms _ J S hφ ts hsub)

/-- `ΓEMlocal` is nonempty (the arity-`1` atom `x = x` is a canonical equality atom). -/
theorem ΓEMlocal_nonempty : (ΓEMlocal s₀).Nonempty :=
  ⟨⟨1, canonEqAtom (localColim s₀) (Term.var (0 : Fin 1)) (Term.var (0 : Fin 1))⟩,
    Or.inl (Or.inl (Or.inr ⟨⟨1, (Term.var 0, Term.var 0)⟩, rfl⟩))⟩

end FirstOrder.Language
