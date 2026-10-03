/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, Claude Opus 5
-/
module

public import LeanPool.DavisKahan.DavisKahan.Sources.DavisKahan1970.SineTheta.FiniteMultiplicity
public import LeanPool.DavisKahan.DavisKahan.OperatorIdeal.NormalizedUnitaryInvariantNorm
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv

/-!
# The Section 2 sharpness paragraph, proved

Davis--Kahan follow the four Section 2 theorem statements with a paragraph of
sharpness commentary.  The source-fidelity inventory records it as four atoms:

* `S2-sharpness.constants-best-possible` -- the constants are best possible;
* `S2-sharpness.two-dimensional-equality` -- two-dimensional examples attain
  them;
* `S2-sharpness.direct-sum-simultaneous-equality` -- orthogonal direct sums of
  such examples can be arranged so that equality holds simultaneously for *all*
  unitary-invariant norms;
* `S2-sharpness.first-order-asymptotic` -- for a perturbation depending linearly
  on a small parameter, the four estimates share their first-order behaviour.

None of the four is a counted result: they are commentary outside a designated
theorem environment, and the completion denominator stays at 29.  They are
proved here anyway, because a reader is entitled to ask whether the repository
quietly dropped mathematics that Davis and Kahan actually assert.

## What is proved, and at what strength

The equality models already exist -- `theorem61_planar_equality_every_norm` on
one plane and `Theorem6_1_finiteMultiplicity_equality_every_norm` on the literal
orthogonal sum of `m` copies -- but they are stated over
`SymmetricNormingFunction`, the Gohberg--Krein reading of the norm class.  The
source's quantifier is "*all* unitary-invariant norms", and the Lean type for
that is `NormalizedUnitaryInvariantNorm`.  This file restates both equalities
over that class, so the "simultaneously for all unitary-invariant norms" clause
is carried by the literal class rather than by one model of it.

The mathematical reason equality is simultaneous is worth naming: in these
models the residual *is* `delta` times the directed sine block, as operators.
Any norm at all then gives equality by homogeneity alone, and the property is
preserved by orthogonal sums because the operator identity is.

## Scope of the constant-optimality claim

`sinTheta_constant_one_optimal_normalizedUnitaryInvariantNorm` proves the
`sin Theta` case: no constant below one survives.  The other three families are
*not* covered by this model.  In the planar configuration the residual has norm
`delta * sin theta` while the tangent block has norm `tan theta`, so the
`tan Theta` bound fails outright here -- its `delta` is the distance to the whole
of the complementary spectrum, not to one eigenvalue, and each family needs its
own extremal configuration.  Claiming all four from this one model would be
false, so only the `sin Theta` case is claimed.

## First-order asymptotics

The four estimates differ exactly in which angle functional they carry, so
"the same first-order asymptotic behaviour" is the statement that
`sin`, `tan`, `sin 2·` and `tan 2·` agree to first order at `0` after the
printed constants.  That is what the last section proves, as three limits of
ratios; no linear parametrisation of the perturbation needs to be fixed, because
whatever it is, the angle tends to zero with it and these ratios are what
compare the four bounds.
-/

@[expose] public section

namespace TauCeti
namespace DavisKahan1970
namespace SectionTwoSharpness

open DavisKahan
open DavisKahan.ExactSinTheta

noncomputable section

universe u

variable {𝕜 : Type u} [RCLike 𝕜]

/-! ### Two-dimensional equality, for every unitary-invariant norm -/

/-- **The two-dimensional model attains the constant, for every unitary-invariant
norm at once.**

`S2-sharpness.two-dimensional-equality`, stated over the literal source norm
class.  Both sides are the same scalar multiple of one norm-one rank-one
coordinate inclusion, so homogeneity alone settles it -- which is exactly why the
equality does not depend on which unitary-invariant norm is chosen. -/
theorem planar_equality_every_normalizedUnitaryInvariantNorm
    (N : NormalizedUnitaryInvariantNorm.{u, u} 𝕜)
    {delta theta : ℝ} (hdelta : 0 ≤ delta) :
    N.gauge (planarResidual (𝕜 := 𝕜) delta theta) =
      delta * N.gauge (planarSineBlock (𝕜 := 𝕜) theta) := by
  have hV := planarComplementMap_norm_rank (𝕜 := 𝕜)
  have hVmem : N.Mem (planarComplementMap (𝕜 := 𝕜)) := N.mem_rankOne hV.1 hV.2
  rw [planarResidual, planarSineBlock, N.gauge_smul _ hVmem, N.gauge_smul _ hVmem,
    RCLike.norm_ofReal, RCLike.norm_ofReal, abs_mul, abs_of_nonneg hdelta]
  ring

/-- The planar sine block has strictly positive norm at every acute angle, for
every unitary-invariant norm. -/
theorem planarSineBlock_gauge_pos_normalizedUnitaryInvariantNorm
    (N : NormalizedUnitaryInvariantNorm.{u, u} 𝕜)
    {theta : ℝ} (h0 : 0 < theta) (h1 : theta < Real.pi) :
    0 < N.gauge (planarSineBlock (𝕜 := 𝕜) theta) := by
  have hV := planarComplementMap_norm_rank (𝕜 := 𝕜)
  have hVmem : N.Mem (planarComplementMap (𝕜 := 𝕜)) := N.mem_rankOne hV.1 hV.2
  have hone : N.gauge (planarComplementMap (𝕜 := 𝕜)) = 1 :=
    N.gauge_rankOne_eq_one hV.1 hV.2
  rw [planarSineBlock, N.gauge_smul _ hVmem, hone, mul_one, RCLike.norm_ofReal]
  exact abs_pos.mpr (Real.sin_pos_of_pos_of_lt_pi h0 h1).ne'

/-- **The constant one in the `sin Theta` theorem is best possible.**

Part of `S2-sharpness.constants-best-possible`, for the single-angle sine family
and for every unitary-invariant norm.  No `c < 1` can replace it: the planar
model at a quarter of `pi` already violates the weakened inequality. -/
theorem sinTheta_constant_one_optimal_normalizedUnitaryInvariantNorm
    (N : NormalizedUnitaryInvariantNorm.{u, u} 𝕜) :
    ∀ c : ℝ, c < 1 →
      ∃ delta theta : ℝ,
        0 < delta ∧ 0 < theta ∧ theta < Real.pi / 2 ∧
        c * N.gauge (planarResidual (𝕜 := 𝕜) delta theta) <
          delta * N.gauge (planarSineBlock (𝕜 := 𝕜) theta) := by
  intro c hc
  have hpi4 : (0 : ℝ) < Real.pi / 4 := by linarith [Real.pi_pos]
  have hpi42 : Real.pi / 4 < Real.pi / 2 := by linarith [Real.pi_pos]
  refine ⟨1, Real.pi / 4, zero_lt_one, hpi4, hpi42, ?_⟩
  rw [planar_equality_every_normalizedUnitaryInvariantNorm N zero_le_one]
  have hpos := planarSineBlock_gauge_pos_normalizedUnitaryInvariantNorm (𝕜 := 𝕜) N
    hpi4 (by linarith [Real.pi_pos])
  nlinarith

/-! ### Orthogonal direct sums, for every unitary-invariant norm -/

/-- The complementary inclusion of the multiplicity-`m` model lies in every
unitary-invariant ideal: it is a sum of `m` norm-one rank-one coordinate
columns, so no finite-dimensional membership assumption is needed. -/
theorem finiteMultiplicityComplementMap_mem_normalizedUnitaryInvariantNorm
    (m : ℕ) (N : NormalizedUnitaryInvariantNorm.{u, u} 𝕜) :
    N.Mem (finiteMultiplicityComplementMap (𝕜 := 𝕜) m) := by
  rw [finiteMultiplicityComplementMap_eq_sum_coordinateColumn]
  exact N.mem_finset_sum Finset.univ fun i _ =>
    N.mem_rankOne (finiteMultiplicityCoordinateColumn_norm_rank (𝕜 := 𝕜) m i).1
      (finiteMultiplicityCoordinateColumn_norm_rank (𝕜 := 𝕜) m i).2

/-- **Orthogonal direct sums attain the constant simultaneously for all
unitary-invariant norms.**

`S2-sharpness.direct-sum-simultaneous-equality`.  `m` copies of the planar model
are summed orthogonally, all sharing one gap `delta`, and the residual is again
literally `delta` times the directed sine block -- which is what makes the
equality simultaneous in the norm.  At `sin theta ≠ 0` the sine block is
injective on an `m`-dimensional space, so this is a genuine multiplicity-`m`
example and not a restatement of scalar homogeneity. -/
theorem finiteMultiplicity_equality_every_normalizedUnitaryInvariantNorm
    (m : ℕ) (N : NormalizedUnitaryInvariantNorm.{u, u} 𝕜)
    {delta theta : ℝ} (hdelta : 0 ≤ delta) :
    N.gauge (finiteMultiplicityResidual (𝕜 := 𝕜) m delta theta) =
      delta * N.gauge (finiteMultiplicitySineBlock (𝕜 := 𝕜) m theta) := by
  have hmem := finiteMultiplicityComplementMap_mem_normalizedUnitaryInvariantNorm
    (𝕜 := 𝕜) m N
  rw [finiteMultiplicityResidual, finiteMultiplicitySineBlock,
    N.gauge_smul _ hmem, N.gauge_smul _ hmem,
    RCLike.norm_ofReal, RCLike.norm_ofReal, abs_mul, abs_of_nonneg hdelta]
  ring

/-! ### First-order asymptotics

The four Section 2 estimates differ in which angle functional they carry.  The
source's claim that they share their first-order behaviour as the perturbation
parameter tends to zero is, after the printed constants are divided out, the
statement that the four functionals are first-order equivalent at `0`. -/

/-- A function vanishing at `0` and differentiable there has `f t / t → f' 0`.
This is `hasDerivAt_iff_tendsto_slope` with the slope written the way the four
comparisons below need it. -/
private theorem tendsto_div_self_of_hasDerivAt_zero {f : ℝ → ℝ} {c : ℝ}
    (hf : HasDerivAt f c 0) (h0 : f 0 = 0) :
    Filter.Tendsto (fun t : ℝ => f t / t) (nhdsWithin 0 {(0 : ℝ)}ᶜ) (nhds c) := by
  refine Filter.Tendsto.congr (fun t => ?_) (hasDerivAt_iff_tendsto_slope.mp hf)
  simp [slope, h0, div_eq_inv_mul]

/-- `sin t / t → 1`. -/
theorem tendsto_sin_div_self :
    Filter.Tendsto (fun t : ℝ => Real.sin t / t)
      (nhdsWithin 0 {(0 : ℝ)}ᶜ) (nhds 1) :=
  tendsto_div_self_of_hasDerivAt_zero (by simpa using Real.hasDerivAt_sin 0) Real.sin_zero

/-- `tan t / t → 1`. -/
theorem tendsto_tan_div_self :
    Filter.Tendsto (fun t : ℝ => Real.tan t / t)
      (nhdsWithin 0 {(0 : ℝ)}ᶜ) (nhds 1) :=
  tendsto_div_self_of_hasDerivAt_zero
    (by simpa using Real.hasDerivAt_tan (by simp : Real.cos 0 ≠ 0)) Real.tan_zero

/-- `cos t → 1` along the punctured neighbourhood, which is where the two
double-angle comparisons pick up their factors. -/
private theorem tendsto_cos_one :
    Filter.Tendsto Real.cos (nhdsWithin 0 {(0 : ℝ)}ᶜ) (nhds 1) := by
  simpa using (Real.continuous_cos.tendsto (0 : ℝ)).mono_left nhdsWithin_le_nhds

private theorem tendsto_cos_two_one :
    Filter.Tendsto (fun t : ℝ => Real.cos (2 * t))
      (nhdsWithin 0 {(0 : ℝ)}ᶜ) (nhds 1) := by
  have hcont : Continuous fun t : ℝ => Real.cos (2 * t) :=
    Real.continuous_cos.comp (continuous_const.mul continuous_id)
  simpa using (hcont.tendsto (0 : ℝ)).mono_left nhdsWithin_le_nhds

/-- `sin (2t) / t → 2`.  The double-angle identity turns this into
`2 * (sin t / t) * cos t`. -/
theorem tendsto_sin_two_div_self :
    Filter.Tendsto (fun t : ℝ => Real.sin (2 * t) / t)
      (nhdsWithin 0 {(0 : ℝ)}ᶜ) (nhds 2) := by
  have h : Filter.Tendsto (fun t : ℝ => 2 * (Real.sin t / t) * Real.cos t)
      (nhdsWithin 0 {(0 : ℝ)}ᶜ) (nhds 2) := by
    simpa using (tendsto_sin_div_self.const_mul 2).mul tendsto_cos_one
  refine Filter.Tendsto.congr (fun t => ?_) h
  rw [Real.sin_two_mul]
  ring

/-- `tan (2t) / t → 2`. -/
theorem tendsto_tan_two_div_self :
    Filter.Tendsto (fun t : ℝ => Real.tan (2 * t) / t)
      (nhdsWithin 0 {(0 : ℝ)}ᶜ) (nhds 2) := by
  have h : Filter.Tendsto (fun t : ℝ => Real.sin (2 * t) / t / Real.cos (2 * t))
      (nhdsWithin 0 {(0 : ℝ)}ᶜ) (nhds 2) := by
    simpa [Pi.div_def] using
      tendsto_sin_two_div_self.div tendsto_cos_two_one one_ne_zero
  refine Filter.Tendsto.congr (fun t => ?_) h
  rw [Real.tan_eq_sin_div_cos]
  ring

/-- **The four Section 2 estimates share their first-order behaviour.**

`S2-sharpness.first-order-asymptotic`.  The four theorem families differ exactly
in which angle functional they bound -- `sin Theta`, `tan Theta`, `sin 2Theta`,
`tan 2Theta` -- so once a perturbation drives the angle to zero, whether linearly
in a parameter or otherwise, the four bounds agree to first order precisely when
these four functionals do.  They do, with the printed factors `1, 1, 2, 2`. -/
theorem sectionTwo_firstOrder_asymptotics :
    Filter.Tendsto (fun t : ℝ => Real.sin t / t)
        (nhdsWithin 0 {(0 : ℝ)}ᶜ) (nhds 1) ∧
      Filter.Tendsto (fun t : ℝ => Real.tan t / t)
        (nhdsWithin 0 {(0 : ℝ)}ᶜ) (nhds 1) ∧
      Filter.Tendsto (fun t : ℝ => Real.sin (2 * t) / t)
        (nhdsWithin 0 {(0 : ℝ)}ᶜ) (nhds 2) ∧
      Filter.Tendsto (fun t : ℝ => Real.tan (2 * t) / t)
        (nhdsWithin 0 {(0 : ℝ)}ᶜ) (nhds 2) :=
  ⟨tendsto_sin_div_self, tendsto_tan_div_self,
    tendsto_sin_two_div_self, tendsto_tan_two_div_self⟩

end

end SectionTwoSharpness
end DavisKahan1970
end TauCeti
