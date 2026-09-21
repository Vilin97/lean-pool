/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, Claude Opus 5
-/
module

public import LeanPool.DavisKahan.ForTauCeti.Analysis.InnerProductSpace.LinearPMap.SpectralSupport

/-!
# Form bounds from a half-line spectrum

A self-adjoint operator whose spectrum lies in `[c, ∞)` is bounded below by `c`
in the quadratic-form sense, and dually for `(-∞, c]`.  These are the two
semiboundedness facts the ordered branches of the unbounded Sylvester theorem
consume.

## Why there is no integral here

The obvious route is the one Spectra takes: the diagonal measure of `x` has
first moment `re ⟪x, A x⟫`, its support lies in the spectrum, and integrating
the pointwise inequality `c ≤ s` gives the bound.  That route needs the identity
function to be integrable against the diagonal measure, which needs a second
moment, which needs a monotone-convergence argument over the interval cutoffs.

None of it is necessary.  The *bounded* form bound
`re_inner_apply_bounds_of_subset_Icc` is already available on every spectral
range over a bounded set, and the interval cutoffs converge strongly
(`tendsto_specProjection_Icc`).  Applying the bounded bound on `[c, τ]` and
letting `τ → ∞` gives the half-line bound directly, because `E([c, τ])` acts as
`E([-τ, τ])` once `E([c, ∞)) = 1` — and that in turn is `E((-∞, c)) = 0`, which
is the support statement in `SpectralSupport.lean`.

## Sources

*Follows nothing in particular*: form bounds read off a half-line spectrum, in the shape
the consumer asked for — a form bound rather than a second moment.

## Provenance

*New.*  The Spectra endpoints are
`Spectra.QuantumMechanics.SpectralTheory.spectralPVM_integrable_id` together
with `bornExpectation_eq_inner`; the theorem *selection* is theirs, the route is
not — this file proves the consumer-facing statement and never states an
integrability fact at all.
-/

public section

open scoped InnerProductSpace
open MeasureTheory

attribute [local instance] IsStarNormal.instContinuousFunctionalCalculus

namespace TauCeti
namespace LinearPMap

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

section HalfLine

variable {A : H →ₗ.[ℂ] H} (hA : IsSelfAdjoint A)

/-- **The two-sided form bound on a spectral band**, compressed to that band.

On `Icc β α` the quadratic form of `A` is squeezed between `β‖·‖²` and `α‖·‖²`,
after compressing both arguments to the band.  Both half-line results below and
both of their `GramSpectralRank` counterparts are this lemma at a particular
band: `Icc c τ` with the lower half, `Icc (-τ) c` with the upper.  All four
wrote it out. -/
theorem re_inner_specProjection_Icc_bounds {α β : ℝ} (x : A.domain) :
    β * ‖specProjection hA (Set.Icc β α) measurableSet_Icc (x : H)‖ ^ 2 ≤
        (⟪specProjection hA (Set.Icc β α) measurableSet_Icc (A x),
          specProjection hA (Set.Icc β α) measurableSet_Icc (x : H)⟫_ℂ).re ∧
      (⟪specProjection hA (Set.Icc β α) measurableSet_Icc (A x),
          specProjection hA (Set.Icc β α) measurableSet_Icc (x : H)⟫_ℂ).re ≤
        α * ‖specProjection hA (Set.Icc β α) measurableSet_Icc (x : H)‖ ^ 2 := by
  set y : H := specProjection hA (Set.Icc β α) measurableSet_Icc (x : H) with hy
  have hyK : y ∈ specRange hA (Set.Icc β α) measurableSet_Icc :=
    specProjection_mem_specRange hA (Set.Icc β α) measurableSet_Icc (x : H)
  have hymem : y ∈ A.domain :=
    specProjection_mem_domain hA (Set.Icc β α) measurableSet_Icc x
  have hAy : A ⟨y, hymem⟩ =
      specProjection hA (Set.Icc β α) measurableSet_Icc (A x) :=
    specProjection_apply_domain hA (Set.Icc β α) measurableSet_Icc x
  have h := re_inner_apply_bounds_of_subset_Icc hA (Set.Icc β α) measurableSet_Icc
    (β := β) (α := α) Set.Subset.rfl hyK hymem
  rw [hAy] at h
  exact h

/-- If a half-line's complement carries no spectral projection, the half-line
carries the identity. -/
theorem specProjection_eq_one_of_compl_eq_zero {S : Set ℝ} (hS : MeasurableSet S)
    (hz : specProjection hA Sᶜ hS.compl = 0) :
    specProjection hA S hS = 1 := by
  have h1 : (spectralPVM hA).proj Sᶜ hS.compl
      = ContinuousLinearMap.id ℂ H - (spectralPVM hA).proj S hS :=
    (spectralPVM hA).proj_compl S hS
  rw [show (spectralPVM hA).proj Sᶜ hS.compl = specProjection hA Sᶜ hS.compl from by
      rw [specProjection_def], hz] at h1
  rw [show specProjection hA S hS = (spectralPVM hA).proj S hS from by rw [specProjection_def],
    -- states the goal with the definition unfolded, in the shape the next step needs;
    -- there is no `_apply` lemma to rewrite with here.
    show (1 : H →L[ℂ] H) = ContinuousLinearMap.id ℂ H from ContinuousLinearMap.one_def]
  linear_combination (norm := module) h1

/-- Once the half-line `[c, ∞)` carries the identity, its interval cutoffs are
the symmetric interval cutoffs. -/
theorem specProjection_Icc_eq_symm_of_Ici_eq_one {c τ : ℝ}
    (hone : specProjection hA (Set.Ici c) measurableSet_Ici = 1) (hτ : |c| ≤ τ) :
    specProjection hA (Set.Icc c τ) measurableSet_Icc
      = specProjection hA (Set.Icc (-τ) τ) measurableSet_Icc := by
  obtain ⟨hτ1, hτ2⟩ := abs_le.mp hτ
  have hset : Set.Ici c ∩ Set.Icc (-τ) τ = Set.Icc c τ := by
    ext s
    simp only [Set.mem_inter_iff, Set.mem_Ici, Set.mem_Icc]
    constructor
    · rintro ⟨h1, -, h3⟩; exact ⟨h1, h3⟩
    · rintro ⟨h1, h2⟩; exact ⟨h1, by linarith, h2⟩
  have hinter := (spectralPVM hA).proj_inter (Set.Ici c) (Set.Icc (-τ) τ)
    measurableSet_Ici measurableSet_Icc
  rw [show (spectralPVM hA).proj (Set.Ici c) measurableSet_Ici
      = specProjection hA (Set.Ici c) measurableSet_Ici from by
          rw [specProjection_def], hone, one_mul] at hinter
  rw [show specProjection hA (Set.Icc c τ) measurableSet_Icc
      = (spectralPVM hA).proj (Set.Icc c τ) measurableSet_Icc from by rw [specProjection_def],
    (spectralPVM hA).proj_congr hset.symm measurableSet_Icc
      (measurableSet_Ici.inter measurableSet_Icc),
    ← hinter, specProjection_def]

/-- The interval cutoffs of a spectral half-line converge strongly to the
identity. -/
theorem tendsto_specProjection_Icc_right {c : ℝ}
    (hone : specProjection hA (Set.Ici c) measurableSet_Ici = 1) (x : H) :
    Filter.Tendsto
      (fun τ : ℝ => specProjection hA (Set.Icc c τ) measurableSet_Icc x)
      Filter.atTop (nhds x) := by
  refine (tendsto_specProjection_Icc hA x).congr' ?_
  filter_upwards [Filter.eventually_ge_atTop |c|] with τ hτ
  exact congrArg (fun T : H →L[ℂ] H => T x)
    (specProjection_Icc_eq_symm_of_Ici_eq_one hA hone hτ).symm

/-- **Lower form bound from a half-line spectrum.** -/
theorem le_re_inner_of_specProjection_Iio_eq_zero {c : ℝ}
    (hz : specProjection hA (Set.Iio c) measurableSet_Iio = 0) (x : A.domain) :
    c * ‖(x : H)‖ ^ 2 ≤ (⟪A x, (x : H)⟫_ℂ).re := by
  have hcompl : (Set.Ici c)ᶜ = Set.Iio c := Set.compl_Ici
  have hz' : specProjection hA (Set.Ici c)ᶜ measurableSet_Ici.compl = 0 := by
    rw [show specProjection hA (Set.Ici c)ᶜ measurableSet_Ici.compl
        = (spectralPVM hA).proj (Set.Ici c)ᶜ measurableSet_Ici.compl from by
            rw [specProjection_def],
      (spectralPVM hA).proj_congr hcompl measurableSet_Ici.compl measurableSet_Iio,
      ← specProjection_def]
    exact hz
  have hone := specProjection_eq_one_of_compl_eq_zero hA measurableSet_Ici hz'
  -- the cut-off bound, for each `τ`
  have hbound : ∀ τ : ℝ,
      c * ‖specProjection hA (Set.Icc c τ) measurableSet_Icc (x : H)‖ ^ 2
        ≤ (⟪specProjection hA (Set.Icc c τ) measurableSet_Icc (A x),
            specProjection hA (Set.Icc c τ) measurableSet_Icc (x : H)⟫_ℂ).re :=
    fun τ => (re_inner_specProjection_Icc_bounds hA (α := τ) (β := c) x).1
  -- pass to the limit
  have hlx := tendsto_specProjection_Icc_right hA hone (x : H)
  have hlA := tendsto_specProjection_Icc_right hA hone (A x)
  have hleft : Filter.Tendsto
      (fun τ : ℝ => c * ‖specProjection hA (Set.Icc c τ) measurableSet_Icc (x : H)‖ ^ 2)
      Filter.atTop (nhds (c * ‖(x : H)‖ ^ 2)) :=
    ((hlx.norm).pow 2).const_mul c
  have hright : Filter.Tendsto
      (fun τ : ℝ => (⟪specProjection hA (Set.Icc c τ) measurableSet_Icc (A x),
          specProjection hA (Set.Icc c τ) measurableSet_Icc (x : H)⟫_ℂ).re)
      Filter.atTop (nhds ((⟪A x, (x : H)⟫_ℂ).re)) :=
    (Complex.continuous_re.tendsto _).comp (hlA.inner hlx)
  exact le_of_tendsto_of_tendsto' hleft hright hbound

/-- **Upper form bound from a half-line spectrum.** -/
theorem re_inner_le_of_specProjection_Ioi_eq_zero {c : ℝ}
    (hz : specProjection hA (Set.Ioi c) measurableSet_Ioi = 0) (x : A.domain) :
    (⟪A x, (x : H)⟫_ℂ).re ≤ c * ‖(x : H)‖ ^ 2 := by
  have hcompl : (Set.Iic c)ᶜ = Set.Ioi c := Set.compl_Iic
  have hz' : specProjection hA (Set.Iic c)ᶜ measurableSet_Iic.compl = 0 := by
    rw [show specProjection hA (Set.Iic c)ᶜ measurableSet_Iic.compl
        = (spectralPVM hA).proj (Set.Iic c)ᶜ measurableSet_Iic.compl from by
            rw [specProjection_def],
      (spectralPVM hA).proj_congr hcompl measurableSet_Iic.compl measurableSet_Ioi,
      ← specProjection_def]
    exact hz
  have hone := specProjection_eq_one_of_compl_eq_zero hA measurableSet_Iic hz'
  -- the symmetric cutoffs, intersected with `(-∞, c]`
  have hset : ∀ τ : ℝ, |c| ≤ τ → Set.Iic c ∩ Set.Icc (-τ) τ = Set.Icc (-τ) c := by
    intro τ hτ
    obtain ⟨hτ1, hτ2⟩ := abs_le.mp hτ
    ext s
    simp only [Set.mem_inter_iff, Set.mem_Iic, Set.mem_Icc]
    constructor
    · rintro ⟨h1, h2, -⟩; exact ⟨h2, h1⟩
    · rintro ⟨h1, h2⟩; exact ⟨h2, h1, by linarith⟩
  have hcut : ∀ τ : ℝ, |c| ≤ τ →
      specProjection hA (Set.Icc (-τ) c) measurableSet_Icc
        = specProjection hA (Set.Icc (-τ) τ) measurableSet_Icc := by
    intro τ hτ
    have hinter := (spectralPVM hA).proj_inter (Set.Iic c) (Set.Icc (-τ) τ)
      measurableSet_Iic measurableSet_Icc
    rw [show (spectralPVM hA).proj (Set.Iic c) measurableSet_Iic
        = specProjection hA (Set.Iic c) measurableSet_Iic from by rw [specProjection_def], hone,
      one_mul] at hinter
    rw [show specProjection hA (Set.Icc (-τ) c) measurableSet_Icc
        = (spectralPVM hA).proj (Set.Icc (-τ) c) measurableSet_Icc from by rw [specProjection_def],
      (spectralPVM hA).proj_congr (hset τ hτ).symm measurableSet_Icc
        (measurableSet_Iic.inter measurableSet_Icc),
      ← hinter, specProjection_def]
  have hlim : ∀ v : H, Filter.Tendsto
      (fun τ : ℝ => specProjection hA (Set.Icc (-τ) c) measurableSet_Icc v)
      Filter.atTop (nhds v) := by
    intro v
    refine (tendsto_specProjection_Icc hA v).congr' ?_
    filter_upwards [Filter.eventually_ge_atTop |c|] with τ hτ
    exact congrArg (fun T : H →L[ℂ] H => T v) (hcut τ hτ).symm
  have hbound : ∀ τ : ℝ,
      (⟪specProjection hA (Set.Icc (-τ) c) measurableSet_Icc (A x),
          specProjection hA (Set.Icc (-τ) c) measurableSet_Icc (x : H)⟫_ℂ).re
        ≤ c * ‖specProjection hA (Set.Icc (-τ) c) measurableSet_Icc (x : H)‖ ^ 2 :=
    fun τ => (re_inner_specProjection_Icc_bounds hA (α := c) (β := -τ) x).2
  have hleft : Filter.Tendsto
      (fun τ : ℝ => (⟪specProjection hA (Set.Icc (-τ) c) measurableSet_Icc (A x),
          specProjection hA (Set.Icc (-τ) c) measurableSet_Icc (x : H)⟫_ℂ).re)
      Filter.atTop (nhds ((⟪A x, (x : H)⟫_ℂ).re)) :=
    (Complex.continuous_re.tendsto _).comp ((hlim (A x)).inner (hlim (x : H)))
  have hright : Filter.Tendsto
      (fun τ : ℝ => c * ‖specProjection hA (Set.Icc (-τ) c) measurableSet_Icc (x : H)‖ ^ 2)
      Filter.atTop (nhds (c * ‖(x : H)‖ ^ 2)) :=
    (((hlim (x : H)).norm).pow 2).const_mul c
  exact le_of_tendsto_of_tendsto' hleft hright hbound

end HalfLine

end LinearPMap
end TauCeti
