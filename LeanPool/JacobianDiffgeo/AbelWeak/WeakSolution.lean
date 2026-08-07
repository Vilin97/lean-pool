/-
Copyright (c) 2026 Rado Kirov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rado Kirov
-/

import Mathlib.Geometry.Manifold.ContMDiff.Atlas
import Mathlib.Analysis.Calculus.ContDiff.Operations
import LeanPool.JacobianDiffgeo.Surface.RealSmooth

/-!
# Weak solutions (`abel-weak-solutions`, D1 / Forster §20.1, §20.1's Lemma-20.1 multiplicativity)

Unit: abel-weak-solutions (`docs/design/abel-weak-solutions.md` §5). `IsWeakSolutionAt`/
`IsWeakSolutionOfPair`: bare `X → ℂ` functions, no `ℳ X`, no `Divisor X` (the pair-based
formulation is exactly what `abel-theorem` consumes).

**Deviation from the design's literal D1**: `IsWeakSolutionAt` is stated with the chart taken
existentially from `IsManifold.maximalAtlas 𝓘(ℂ) ω X` (matching the design closely) but the
local-model equation is a plain `f =ᶠ[𝓝 a] (...)` eventual equality (junk-free, no filter-sup
formula needed).

**SCOPE ADDITION** (per `docs/design/abel-theorem.md` §1.4/§4.1, its finding that Thm 21.4(b)
needs the `k`-point case, not just `k = 1`): `IsWeakSolutionOfFinset` and
`isWeakSolutionOfFinset_prod` package Forster's Lemma 20.1 ("weak solutions of `D₁, D₂` multiply
to a weak solution of `D₁ + D₂`") as a `Finset`-indexed product over `ι` pairwise-disjoint
two-point pairs — the degenerate, already-disjoint case `abel-theorem`'s own 21.4(a)
construction sets up (no general chain/homology bookkeeping needed).
-/

open scoped ContDiff Manifold
open IsManifold Filter Topology Set

noncomputable section

namespace RS.AbelWeak

variable {X : Type*} [TopologicalSpace X] [T2Space X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]

/-- Forster 20.1's local model at a single point `a`: `f` agrees, in some maximal-atlas chart
`e` at `a`, with `ψ (e ·) * (e · - e a) ^ k` near `a`, for `ψ` smooth and non-vanishing near
`e a`. `k : ℤ` ranges over all integers (a genuine `zpow`, allowing a pole `k < 0`). -/
def IsWeakSolutionAt (f : X → ℂ) (a : X) (k : ℤ) : Prop :=
  ∃ e : OpenPartialHomeomorph X ℂ, e ∈ IsManifold.maximalAtlas 𝓘(ℂ) ω X ∧ a ∈ e.source ∧
    ∃ ψ : ℂ → ℂ, (∀ᶠ z in 𝓝 (e a), ψ z ≠ 0) ∧ ContDiffAt ℝ ∞ ψ (e a) ∧
      f =ᶠ[𝓝 a] (fun x => ψ (e x) * (e x - e a) ^ k)

/-- The weak-solution predicate for the two-point pair `(P, Q)` this unit builds: `ℝ`-smooth
away from `Q`, weak-solution local model `+1` at `P` (a genuine `C^∞` zero), `-1` at `Q` (a
simple pole, excluded from the smoothness domain), non-vanishing everywhere else. -/
structure IsWeakSolutionOfPair (f : X → ℂ) (P Q : X) : Prop where
  contMDiffOn : ContMDiffOn 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) ∞ f {Q}ᶜ
  ne_zero_off : ∀ x, x ≠ P → x ≠ Q → f x ≠ 0
  weakAt_P : IsWeakSolutionAt f P 1
  weakAt_Q : IsWeakSolutionAt f Q (-1)

/-- **SCOPE ADDITION** (`abel-theorem`'s Thm 21.4(b) finding): the Finset-indexed
generalization — a weak solution of `k` pairwise-disjoint two-point pairs `(x i, a i)`,
`i : ι`, order `+1` at each `x i`, `-1` at each `a i`, matching the conclusion shape
`RS.Abel.exists_mero_of_periodVector_mem` needs. -/
structure IsWeakSolutionOfFinset {ι : Type*} (f : X → ℂ) (a x : ι → X) : Prop where
  contMDiffOn : ContMDiffOn 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) ∞ f (Set.range a)ᶜ
  ne_zero_off : ∀ z, (∀ i, z ≠ a i) → (∀ i, z ≠ x i) → f z ≠ 0
  weakAt_x : ∀ i, IsWeakSolutionAt f (x i) 1
  weakAt_a : ∀ i, IsWeakSolutionAt f (a i) (-1)

/-! ### Chart bridges: `ContMDiffAt 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ)` ↔ planar `ContDiffAt`/`ContDiffOn`

`ℂ`'s model `𝓘(ℝ, ℂ)` has no registered `ContMDiffMul` instance (mathlib only registers
`ContMDiffRing 𝓘(𝕜) n 𝕜`, i.e. the model over ITSELF, not `𝓘(ℝ, ℂ)` for the field `ℂ` viewed as
a real algebra) — so finite products of `ContMDiffAt 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ)` functions are built by
routing through `ContDiffAt ℝ` in a fixed chart (`RS.contMDiffAt_real_iff_contDiffAt`) and mathlib's
generic `contDiffAt_prod` (valid for any normed ring), then bridging back. -/

omit [T2Space X] in
/-- Finite pointwise products of `ContMDiffAt 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) ∞` functions are again
`ContMDiffAt 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) ∞` (Compat: no `ContMDiffMul 𝓘(ℝ, ℂ) ∞ ℂ` instance is registered,
so this routes through `ContDiffAt ℝ` in the chart `extChartAt 𝓘(ℂ) x`). -/
theorem contMDiffAt_finsetProd_real {ι : Type*} {t : Finset ι} {f : ι → X → ℂ} {x : X}
    (h : ∀ i ∈ t, ContMDiffAt 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) ∞ (f i) x) :
    ContMDiffAt 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) ∞ (fun z => ∏ i ∈ t, f i z) x := by
  rw [RS.contMDiffAt_real_iff_contDiffAt]
  have h' : ∀ i ∈ t, ContDiffAt ℝ ∞ (f i ∘ (extChartAt 𝓘(ℂ) x).symm) (extChartAt 𝓘(ℂ) x x) :=
    fun i hi => RS.contMDiffAt_real_iff_contDiffAt.1 (h i hi)
  have hp := contDiffAt_prod (𝕜 := ℝ) (t := t) h'
  have heq : (fun z => ∏ i ∈ t, f i z) ∘ (extChartAt 𝓘(ℂ) x).symm
      = fun y => ∏ i ∈ t, (f i ∘ (extChartAt 𝓘(ℂ) x).symm) y := by
    funext y; simp [Function.comp]
  rw [heq]
  exact hp

omit [T2Space X] in
/-- `ContMDiffOn` companion of `contMDiffAt_finsetProd_real`, for an OPEN set `s` (the only case
needed here: `s` is always a finite-set complement, open since `X` is `T2Space`). -/
theorem contMDiffOn_finsetProd_real {ι : Type*} {t : Finset ι} {f : ι → X → ℂ} {s : Set X}
    (hs : IsOpen s) (h : ∀ i ∈ t, ContMDiffOn 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) ∞ (f i) s) :
    ContMDiffOn 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) ∞ (fun z => ∏ i ∈ t, f i z) s := by
  intro z hz
  exact (contMDiffAt_finsetProd_real
    fun i hi => (h i hi).contMDiffAt (hs.mem_nhds hz)).contMDiffWithinAt

omit [T2Space X] [IsManifold 𝓘(ℂ, ℂ) ω X] in
/-- Compat bridge: composing a `ContMDiffAt 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) ∞` function `h` with the inverse of
ANY maximal-atlas chart `e` at `a` gives a `ContDiffAt ℝ ∞` planar function at `e a` (needed for
`IsWeakSolutionAt.mul_of_contMDiffAt`, which must reuse the *existing* witness chart of its
`IsWeakSolutionAt` argument rather than switch to `extChartAt`). -/
theorem contDiffAt_comp_symm_of_contMDiffAt {h : X → ℂ} {a : X}
    {e : OpenPartialHomeomorph X ℂ} (he : e ∈ IsManifold.maximalAtlas 𝓘(ℂ) ω X)
    (ha : a ∈ e.source) (hh : ContMDiffAt 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) ∞ h a) :
    ContDiffAt ℝ ∞ (h ∘ e.symm) (e a) := by
  have hsymm0 : ContMDiffAt 𝓘(ℂ) 𝓘(ℂ) ω (⇑e.symm) (e a) :=
    contMDiffAt_symm_of_mem_maximalAtlas he (e.map_source ha)
  have hsymm : ContMDiffAt 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) ∞ (⇑e.symm) (e a) :=
    RS.contMDiffAt_real_of_holomorphicAt hsymm0
  have heaa : e.symm (e a) = a := e.left_inv ha
  have hh' : ContMDiffAt 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) ∞ h (e.symm (e a)) := by rw [heaa]; exact hh
  exact (hh'.comp (e a) hsymm).contDiffAt

omit [T2Space X] [IsManifold 𝓘(ℂ, ℂ) ω X] in
/-- Compat bridge, the converse direction: a planar `ContDiffAt ℝ ∞` function `g` composed with
ANY maximal-atlas chart `e` (at a point `x ∈ e.source`) is `ContMDiffAt 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) ∞` as a
function on `X` (needed by `SingleChart.lean`'s construction, which builds its weak solution's
local formula directly in a `ChartChain`-supplied chart `e`, not `extChartAt`). -/
theorem contMDiffAt_comp_of_contDiffAt {g : ℂ → ℂ} {x : X} {e : OpenPartialHomeomorph X ℂ}
    (he : e ∈ IsManifold.maximalAtlas 𝓘(ℂ) ω X) (hx : x ∈ e.source)
    (hg : ContDiffAt ℝ ∞ g (e x)) :
    ContMDiffAt 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) ∞ (g ∘ e) x := by
  have he0 : ContMDiffAt 𝓘(ℂ) 𝓘(ℂ) ω (⇑e) x := contMDiffAt_of_mem_maximalAtlas he hx
  have he1 : ContMDiffAt 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) ∞ (⇑e) x := RS.contMDiffAt_real_of_holomorphicAt he0
  have hg1 : ContMDiffAt 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) ∞ g (e x) := contMDiffAt_iff_contDiffAt.2 hg
  exact hg1.comp x he1

/-! ### Multiplicativity (Forster's Lemma 20.1) -/

omit [T2Space X] [IsManifold 𝓘(ℂ, ℂ) ω X] in
/-- The core multiplicativity step: multiplying a weak solution at `a` by a smooth, non-vanishing
(at `a`) cofactor `h` preserves the local model (same order `k`, same witness chart). -/
theorem IsWeakSolutionAt.mul_of_contMDiffAt {f h : X → ℂ} {a : X} {k : ℤ}
    (hf : IsWeakSolutionAt f a k) (hh : ContMDiffAt 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) ∞ h a) (hha : h a ≠ 0) :
    IsWeakSolutionAt (fun x => f x * h x) a k := by
  obtain ⟨e, he, hae, ψ, hψne, hψdiff, hfeq⟩ := hf
  have hcompC : ContDiffAt ℝ ∞ (h ∘ e.symm) (e a) := contDiffAt_comp_symm_of_contMDiffAt he hae hh
  have heventually : ∀ᶠ x in 𝓝 a, e.symm (e x) = x := by
    filter_upwards [e.open_source.mem_nhds hae] with x hx using e.left_inv hx
  refine ⟨e, he, hae, fun z => ψ z * h (e.symm z), ?_, ?_, ?_⟩
  · have hcont : ContinuousAt h a := hh.continuousAt
    have hev2 : ∀ᶠ x in 𝓝 a, h x ≠ 0 := hcont.eventually_ne hha
    have heaa : e.symm (e a) = a := e.left_inv hae
    have hesymmcont : ContinuousAt e.symm (e a) :=
      (contMDiffAt_symm_of_mem_maximalAtlas he (e.map_source hae)).continuousAt
    have hev2' : ∀ᶠ y in 𝓝 (e.symm (e a)), h y ≠ 0 := by rw [heaa]; exact hev2
    have hev3 : ∀ᶠ z in 𝓝 (e a), h (e.symm z) ≠ 0 := hesymmcont.eventually hev2'
    filter_upwards [hψne, hev3] with z hz1 hz2
    exact mul_ne_zero hz1 hz2
  · exact hψdiff.mul hcompC
  · filter_upwards [hfeq, heventually] with x hx1 hx2
    show f x * h x = ψ (e x) * h (e.symm (e x)) * (e x - e a) ^ k
    rw [hx2, hx1]
    ring

/-- **Forster's Lemma 20.1, `k`-point/`Finset`-indexed form** (the `abel-theorem` scope
addition): the pointwise product of `k` pairwise-disjoint two-point weak solutions is a weak
solution of the whole `k`-point configuration. -/
theorem isWeakSolutionOfFinset_prod {ι : Type*} [Fintype ι]
    {f : ι → X → ℂ} {a x : ι → X} (ha : Function.Injective a) (hx : Function.Injective x)
    (hax : ∀ i j, a i ≠ x j) (hf : ∀ i, IsWeakSolutionOfPair (f i) (x i) (a i)) :
    IsWeakSolutionOfFinset (fun z => ∏ i, f i z) a x := by
  classical
  have hcof_smooth : ∀ (p : X) (S : Finset ι), (∀ j ∈ S, p ≠ a j) →
      ContMDiffAt 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) ∞ (fun z => ∏ j ∈ S, f j z) p := by
    intro p S hnej
    apply contMDiffAt_finsetProd_real
    intro j hj
    exact (hf j).contMDiffOn.contMDiffAt
      (IsOpen.mem_nhds isOpen_compl_singleton (hnej j hj))
  have hrangeOpen : IsOpen (Set.range a)ᶜ := (Set.finite_range a).isClosed.isOpen_compl
  refine ⟨?_, ?_, ?_, ?_⟩
  · apply contMDiffOn_finsetProd_real (t := Finset.univ) hrangeOpen
    intro i _
    apply (hf i).contMDiffOn.mono
    intro z hz
    simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
    intro hza
    exact hz (hza ▸ Set.mem_range_self i)
  · intro z hz1 hz2
    apply Finset.prod_ne_zero_iff.mpr
    intro i _
    exact (hf i).ne_zero_off z (hz2 i) (hz1 i)
  · intro i₀
    have hxa : ∀ j, x i₀ ≠ a j := fun j => (hax j i₀).symm
    have hxx : ∀ j ∈ Finset.univ.erase i₀, x i₀ ≠ x j := by
      intro j hj
      have hji : j ≠ i₀ := (Finset.mem_erase.mp hj).1
      exact fun h => hji.symm (hx h)
    have hcof := hcof_smooth (x i₀) (Finset.univ.erase i₀) (fun j _ => hxa j)
    have hcof_ne : (∏ j ∈ Finset.univ.erase i₀, f j (x i₀)) ≠ 0 := by
      apply Finset.prod_ne_zero_iff.mpr
      intro j hj
      exact (hf j).ne_zero_off (x i₀) (hxx j hj) (hxa j)
    have hmul := (hf i₀).weakAt_P.mul_of_contMDiffAt hcof hcof_ne
    have heq : (fun z => f i₀ z * ∏ j ∈ Finset.univ.erase i₀, f j z)
        = (fun z => ∏ i, f i z) := by
      funext z
      exact Finset.mul_prod_erase Finset.univ (fun i => f i z) (Finset.mem_univ i₀)
    rwa [heq] at hmul
  · intro i₀
    have hax' : ∀ j, a i₀ ≠ x j := fun j => hax i₀ j
    have haa : ∀ j ∈ Finset.univ.erase i₀, a i₀ ≠ a j := by
      intro j hj
      have hji : j ≠ i₀ := (Finset.mem_erase.mp hj).1
      exact fun h => hji.symm (ha h)
    have hcof := hcof_smooth (a i₀) (Finset.univ.erase i₀) (fun j hj => haa j hj)
    have hcof_ne : (∏ j ∈ Finset.univ.erase i₀, f j (a i₀)) ≠ 0 := by
      apply Finset.prod_ne_zero_iff.mpr
      intro j hj
      exact (hf j).ne_zero_off (a i₀) (hax' j) (haa j hj)
    have hmul := (hf i₀).weakAt_Q.mul_of_contMDiffAt hcof hcof_ne
    have heq : (fun z => f i₀ z * ∏ j ∈ Finset.univ.erase i₀, f j z)
        = (fun z => ∏ i, f i z) := by
      funext z
      exact Finset.mul_prod_erase Finset.univ (fun i => f i z) (Finset.mem_univ i₀)
    rwa [heq] at hmul

end RS.AbelWeak

end
