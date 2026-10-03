/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Core.Iteration.Arithmetic

/-!
# Positive small-data thresholds

The scalar expression in the start estimate tends to zero with the data
size. Its admissible threshold depends only on the numerical constants,
before any solution or domain is chosen.
-/

public section

open Filter
open scoped Topology


noncomputable section

namespace CKN

/-- The numerical upper bound for the initial theta quantity in
`lem:thmA-start`. -/
@[expose]
def theoremAStartBound (q κ C₂₅ C₂₆ C₃₂ ε₀ : ℝ) : ℝ :=
      C₂₅ * (κ * (16 * ε₀) ^ (1 / 3 : ℝ) +
          κ ^ (-1 : ℝ) * (16 * ε₀) ^ (1 / 2 : ℝ) +
          κ ^ (-1 : ℝ) * (16 * ε₀) ^ (1 / 3 : ℝ) *
            (16 * ε₀) ^ (1 / 6 : ℝ)) +
        C₂₆ * κ ^ (-1 / 2 : ℝ) * (16 * ε₀) ^ (1 / 6 : ℝ) *
          (ε₀ ^ (1 / q : ℝ)) ^ (1 / 2 : ℝ) +
        κ ^ (-4 : ℝ) *
          (C₃₂ * (κ⁻¹ ^ (2 : ℕ) * (8 * (16 * ε₀)) +
            κ * (16 * ε₀) +
            κ ^ (3 / 2 : ℝ) * (ε₀ ^ (1 / q : ℝ)) ^ (3 / 2 : ℝ))) ^
              (2 / 3 : ℝ)

/-- The numerical start bound vanishes continuously with the data size. -/
theorem theoremAStartBound_continuous {q : ℝ} (hq : 0 < q)
    (κ C₂₅ C₂₆ C₃₂ : ℝ) :
    Continuous (theoremAStartBound q κ C₂₅ C₂₆ C₃₂) := by
  have hi : 0 < (1 / q : ℝ) := one_div_pos.mpr hq
  unfold theoremAStartBound
  fun_prop (disch := positivity)

/-- At zero data the numerical start bound is zero. -/
theorem theoremAStartBound_zero {q : ℝ} (hq : 0 < q)
    (κ C₂₅ C₂₆ C₃₂ : ℝ) :
    theoremAStartBound q κ C₂₅ C₂₆ C₃₂ 0 = 0 := by
  have hi : (1 / q : ℝ) ≠ 0 := ne_of_gt (one_div_pos.mpr hq)
  have hqi : q⁻¹ ≠ 0 := inv_ne_zero hq.ne'
  norm_num [theoremAStartBound, Real.zero_rpow hi, Real.zero_rpow hqi]

/-- A positive data threshold simultaneously satisfies the force and theta
smallness requirements, with all constants fixed before the solution. -/
theorem exists_theoremA_start_smallness
    (q C₂₅ C₂₆ C₂₇ C₂₈ C₃₂ : ℝ)
    (hq : 0 < q) (hC₂₇ : 0 < C₂₇) (hC₂₈ : 0 < C₂₈) :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧
      ε₀ ^ (1 / q : ℝ) ≤ iterationLambda₀ C₂₇ C₂₈ ∧
      theoremAStartBound q (iterationKappa C₂₇) C₂₅ C₂₆ C₃₂ ε₀ ≤
        iterationEta C₂₇ := by
  have hi : 0 < (1 / q : ℝ) := one_div_pos.mpr hq
  have hpow : Continuous (fun ε : ℝ => ε ^ (1 / q : ℝ)) :=
    continuous_id.rpow_const (fun _ => Or.inr hi.le)
  have hlimpow : Tendsto (fun ε : ℝ => ε ^ (1 / q : ℝ)) (𝓝 (0 : ℝ)) (𝓝 0) := by
    simpa only [Real.zero_rpow hi.ne'] using hpow.continuousAt.tendsto (x := 0)
  have hlim := (theoremAStartBound_continuous hq (iterationKappa C₂₇)
    C₂₅ C₂₆ C₃₂).continuousAt.tendsto (x := 0)
  rw [theoremAStartBound_zero hq] at hlim
  have hf := hlimpow.eventually_lt_const (iterationLambda₀_pos hC₂₇ hC₂₈)
  have ht := hlim.eventually_lt_const (iterationEta_pos hC₂₇)
  have hboth : ∀ᶠ ε : ℝ in 𝓝[>] (0 : ℝ),
      0 < ε ∧ ε ^ (1 / q : ℝ) < iterationLambda₀ C₂₇ C₂₈ ∧
      theoremAStartBound q (iterationKappa C₂₇) C₂₅ C₂₆ C₃₂ ε < iterationEta C₂₇ := by
    have hpos : ∀ᶠ ε : ℝ in 𝓝[>] (0 : ℝ), 0 < ε := self_mem_nhdsWithin
    filter_upwards [hpos, hf.filter_mono nhdsWithin_le_nhds,
      ht.filter_mono nhdsWithin_le_nhds] with ε hε hforce htheta
    exact ⟨hε, hforce, htheta⟩
  obtain ⟨ε₀, hε₀, hforce, htheta⟩ := hboth.exists
  exact ⟨ε₀, hε₀, hforce.le, htheta.le⟩

end CKN
