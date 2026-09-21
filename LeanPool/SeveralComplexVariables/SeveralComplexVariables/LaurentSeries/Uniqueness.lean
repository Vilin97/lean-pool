/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import LeanPool.SeveralComplexVariables.SeveralComplexVariables.LaurentSeries.Basic
public import LeanPool.SeveralComplexVariables.SeveralComplexVariables.LocallyUniform

/-!
# Uniqueness of analytic Laurent expansions

Uniform convergence on one positive coordinate torus permits coefficient extraction. The
coefficients of a locally uniformly convergent Laurent series are therefore unique,
independently of the existence theorem and without a connectedness hypothesis.

## Main results

`tendsto_multivariableLaurentCoeff` extracts coefficients from uniform convergence on a torus.
`eq_multivariableLaurentCoeff_of_hasSumLocallyUniformlyOn` is uniqueness of the coefficient
family of a locally uniformly convergent expansion.
-/

public noncomputable section

open Complex Set MeasureTheory Metric Filter
open scoped Real Topology

namespace SeveralComplexVariables

variable {n : ℕ} {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F] [CompleteSpace F]

omit [CompleteSpace F] in
/-- Uniform convergence on a torus implies convergence of each Laurent coefficient. -/
theorem tendsto_multivariableLaurentCoeff {α : Type*} {l : Filter α}
    {f : α → (Fin n → ℂ) → F} {g : (Fin n → ℂ) → F} {K : Set (Fin n → ℂ)}
    {r : Fin n → ℝ} (hr : ∀ i, 0 < r i) (hK : ∀ θ, torusMap 0 r θ ∈ K)
    (hf : ∀ᶠ a in l, Continuous (fun θ => f a (torusMap 0 r θ)))
    (hg : Continuous (fun θ => g (torusMap 0 r θ)))
    (hu : TendstoUniformlyOn f g l K) (m : Fin n → ℤ) :
    Tendsto (fun a => multivariableLaurentCoeff (f a) r m) l
      (𝓝 (multivariableLaurentCoeff g r m)) := by
  let C := ∏ i, r i ^ (-m i)
  have hC : 0 ≤ C := Finset.prod_nonneg fun i _ => zpow_nonneg (hr i).le _
  rw [Metric.tendsto_nhds]
  intro ε hε
  have hδ : 0 < ε / (C + 1) := div_pos hε (by positivity)
  filter_upwards [Metric.tendstoUniformlyOn_iff.mp hu _ hδ, hf] with a ha hfa
  rw [dist_eq_norm, ← multivariableLaurentCoeff_sub hr hfa hg]
  calc
    ‖multivariableLaurentCoeff (fun z => f a z - g z) r m‖ ≤ ε / (C + 1) * C :=
      norm_multivariableLaurentCoeff_le hr (fun θ => by
        rw [norm_sub_rev]
        simpa only [dist_eq_norm] using (ha _ (hK θ)).le) m
    _ < ε := by
      have he := div_mul_cancel₀ ε (show C + 1 ≠ 0 by positivity)
      nlinarith

/-- The coefficient of a finite Laurent sum is its corresponding summand coefficient. -/
theorem multivariableLaurentCoeff_sum_terms (c : (Fin n → ℤ) → F)
    (s : Finset (Fin n → ℤ)) {r : Fin n → ℝ} (hr : ∀ i, 0 < r i) (m : Fin n → ℤ) :
    multivariableLaurentCoeff (fun z => ∑ k ∈ s, multivariableLaurentTerm c k z) r m =
      if m ∈ s then c m else 0 := by
  classical
  rw [multivariableLaurentCoeff_sum s hr (fun k _ =>
    show Continuous (fun θ => multivariableLaurentTerm c k (torusMap 0 r θ)) from
      continuous_laurentMonomial_smul_torus (f := fun _ => c k) hr continuous_const k)]
  change (∑ k ∈ s, multivariableLaurentCoeff (fun z => (∏ i, z i ^ k i) • c k) r m) = _
  simp [multivariableLaurentCoeff_monomial r hr]

/-- A locally uniformly convergent Laurent expansion has the torus integral coefficients. Only
continuity of the limit and containment of a positive torus are needed. -/
theorem eq_multivariableLaurentCoeff_of_hasSumLocallyUniformlyOn
    {U : Set (Fin n → ℂ)} {f : (Fin n → ℂ) → F} (hf : ContinuousOn f U)
    {r : Fin n → ℝ} (hr : ∀ i, 0 < r i)
    (hTU : ∀ z, (∀ i, ‖z i‖ = r i) → z ∈ U)
    {c : (Fin n → ℤ) → F}
    (hs : HasSumLocallyUniformlyOn (multivariableLaurentTerm c) f U) :
    c = multivariableLaurentCoeff f r := by
  classical
  let T : Set (Fin n → ℂ) := {z | ∀ i, z i ∈ sphere 0 (r i)}
  have hT : IsCompact T := isCompact_pi_infinite (fun i => isCompact_sphere 0 (r i))
  have hTU' : T ⊆ U := fun z hz => hTU z (fun i => mem_sphere_zero_iff_norm.mp (hz i))
  have htor (θ : Fin n → ℝ) : torusMap 0 r θ ∈ T := by
    intro i
    simp [torusMap, abs_of_pos (hr i)]
  have hfc : Continuous (fun θ => f (torusMap 0 r θ)) :=
    hf.comp_continuous (continuous_torusMap 0 r) (fun θ => hTU' (htor θ))
  have hcont (s : Finset (Fin n → ℤ)) :
      Continuous (fun θ => ∑ k ∈ s, multivariableLaurentTerm c k (torusMap 0 r θ)) :=
    continuous_finsetSum s (fun k _ =>
      continuous_laurentMonomial_smul_torus (f := fun _ => c k) hr continuous_const k)
  have hu := (tendstoLocallyUniformlyOn_iff_tendstoUniformlyOn_of_compact hT).mp (hs.mono hTU')
  funext m
  have hlim := tendsto_multivariableLaurentCoeff hr htor (.of_forall hcont) hfc hu m
  have hvalue : Tendsto
      (fun s : Finset (Fin n → ℤ) =>
        multivariableLaurentCoeff (fun z => ∑ k ∈ s, multivariableLaurentTerm c k z) r m)
      atTop (𝓝 (c m)) := by
    apply tendsto_const_nhds.congr'
    filter_upwards [eventually_finset_mem_atTop m] with s hsm
    rw [multivariableLaurentCoeff_sum_terms c s hr m, ite_eq_left hsm]
  exact tendsto_nhds_unique hvalue hlim

end SeveralComplexVariables

/- Adapted for Lean Pool: module imports and compatibility with its pinned toolchain. -/
