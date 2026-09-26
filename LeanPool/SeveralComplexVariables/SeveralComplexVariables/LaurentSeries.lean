/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import LeanPool.SeveralComplexVariables.SeveralComplexVariables.LaurentSeries.ProductExpansion
public import LeanPool.SeveralComplexVariables.SeveralComplexVariables.LaurentSeries.Uniqueness

/-!
# Multivariable analytic Laurent series

Coefficients are arbitrary families indexed by integer multi-indices, not algebraic
`LaurentSeries`, whose support is bounded below. Sums use finite subsets of the index type. The
main expansion theorem includes coordinate hyperplanes: coefficients with negative exponent in a
coordinate vanish when the domain meets that hyperplane. This makes the statement compatible
with Lean's totalized integer powers at zero.

The proof combines successive circle expansions, independence of coefficient tori, and summable
local geometric bounds. References: [Korevaar–Wiegerinck][KorevaarWiegerinck2017] (2017),
Theorem 2.7.1 and Lemma 2.8.1.

## Main results

`multivariableLaurent_expansion` is the expansion theorem on a connected open Reinhardt domain.
`hasSumUniformlyOn_multivariableLaurent` is uniform convergence on compact subsets of the
domain. `multivariableLaurentCoeff_eq_zero_of_not_nonneg` vanishes coefficients with a negative
exponent in a coordinate that meets a hyperplane. Supporting lemmas live in the `LaurentSeries`
submodules.

## References

* [J. Korevaar and J. Wiegerinck, *Several Complex Variables*][KorevaarWiegerinck2017]
-/

public noncomputable section

open Complex Set MeasureTheory
open scoped Real Topology

namespace SeveralComplexVariables

variable {n : ℕ} {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F] [CompleteSpace F]

/-- **Multivariable Laurent expansion on a connected Reinhardt domain.** The expansion is
absolutely and locally uniformly convergent, its coefficients are independent of the torus,
and they are unique. Negative exponents disappear in any coordinate whose hyperplane is met. -/
theorem multivariableLaurent_expansion {U : Set (Fin n → ℂ)} (ho : IsOpen U)
    (hc : IsPreconnected U) (hR : IsReinhardt U) {f : (Fin n → ℂ) → F}
    (hf : AnalyticOnNhd ℂ f U) {r : Fin n → ℝ} (hr : ∀ i, 0 < r i)
    (hrU : (fun i => (r i : ℂ)) ∈ U) :
    HasSumLocallyUniformlyOn (multivariableLaurentTerm (multivariableLaurentCoeff f r)) f U ∧
    (∀ z ∈ U, Summable (fun m => ‖multivariableLaurentTerm (multivariableLaurentCoeff f r) m z‖)) ∧
    (∀ (m : Fin n → ℤ) (i : Fin n), (∃ z ∈ U, z i = 0) → m i < 0 →
      multivariableLaurentCoeff f r m = 0) ∧
    (∀ s : Fin n → ℝ, (∀ i, 0 < s i) → (fun i => (s i : ℂ)) ∈ U →
      multivariableLaurentCoeff f s = multivariableLaurentCoeff f r) ∧
    (∀ c : (Fin n → ℤ) → F,
      HasSumLocallyUniformlyOn (multivariableLaurentTerm c) f U →
      c = multivariableLaurentCoeff f r) := by
  refine ⟨hasSumLocallyUniformlyOn_multivariableLaurent_of_pointwise ho hc hR hf hr hrU
    (fun z hz => hasSum_multivariableLaurent ho hc hR hf hr hrU hz),
    fun z hz => summable_norm_multivariableLaurent ho hc hR hf hr hrU hz,
    multivariableLaurentCoeff_neg_eq_zero ho hc hR hf hr hrU,
    fun s hs hsU => multivariableLaurentCoeff_eq_of_radii ho hc hR hf hr hs hrU hsU,
    fun c hs => eq_multivariableLaurentCoeff_of_hasSumLocallyUniformlyOn hf.continuousOn hr ?_ hs⟩
  intro z hz
  apply hR hrU
  intro i
  simpa [abs_of_pos (hr i)] using hz i

/-- Laurent expansion converges uniformly on compact subsets of the original domain. -/
theorem hasSumUniformlyOn_multivariableLaurent {U K : Set (Fin n → ℂ)}
    (ho : IsOpen U) (hc : IsPreconnected U) (hR : IsReinhardt U) {f : (Fin n → ℂ) → F}
    (hf : AnalyticOnNhd ℂ f U) {r : Fin n → ℝ} (hr : ∀ i, 0 < r i)
    (hrU : (fun i => (r i : ℂ)) ∈ U) (hK : IsCompact K) (hKU : K ⊆ U) :
    HasSumUniformlyOn (multivariableLaurentTerm (multivariableLaurentCoeff f r)) f K :=
  hasSumUniformlyOn_iff_tendstoUniformlyOn.mpr
    ((tendstoLocallyUniformlyOn_iff_tendstoUniformlyOn_of_compact hK).mp
      (((multivariableLaurent_expansion ho hc hR hf hr hrU).1).mono hKU))

/-- If a Reinhardt domain meets every coordinate hyperplane, only nonnegative exponents occur in its
Laurent expansion. This is Lemma 2.8.1 applied in each coordinate. -/
theorem multivariableLaurentCoeff_eq_zero_of_not_nonneg {U : Set (Fin n → ℂ)}
    (ho : IsOpen U) (hc : IsPreconnected U) (hR : IsReinhardt U)
    (hmeet : ∀ i, ∃ z ∈ U, z i = 0) {f : (Fin n → ℂ) → F}
    (hf : AnalyticOnNhd ℂ f U) {r : Fin n → ℝ} (hr : ∀ i, 0 < r i)
    (hrU : (fun i => (r i : ℂ)) ∈ U) {m : Fin n → ℤ} (hm : ¬ ∀ i, 0 ≤ m i) :
    multivariableLaurentCoeff f r m = 0 := by
  push Not at hm
  obtain ⟨i, hi⟩ := hm
  exact multivariableLaurentCoeff_neg_eq_zero ho hc hR hf hr hrU m i (hmeet i) hi

end SeveralComplexVariables

/- Adapted for Lean Pool: module imports and compatibility with its pinned toolchain. -/
