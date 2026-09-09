/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.Analysis.Complex.Exponential
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

/-!
# A scalar bound for the forced energy inequality

The integrating factor controls an energy whose time derivative is bounded by
the energy plus a constant. Only derivatives in the interior of the time
interval are required.
-/

@[expose] public section



noncomputable section

open Set

namespace NavierStokesR3.ScalarEnergyBound

/-- The shifted energy has a nonincreasing integrating factor. -/
theorem forced_gronwall_weighted {T C : ℝ} {E E' : ℝ → ℝ}
    (hT : 0 ≤ T) (hcont : ContinuousOn E (Icc 0 T)) (hinitial : E 0 = 0)
    (hderiv : ∀ t ∈ Ioo 0 T, HasDerivAt E (E' t) t)
    (hbound : ∀ t ∈ Ioo 0 T, E' t ≤ E t + C) :
    ∀ t ∈ Icc 0 T, (E t + C) * Real.exp (-t) ≤ C := by
  let G : ℝ → ℝ := fun t => Real.exp (-t) * (E t + C)
  let G' : ℝ → ℝ := fun t => Real.exp (-t) * (E' t - (E t + C))
  have hgcont : ContinuousOn G (Icc 0 T) :=
    (Real.continuous_exp.comp continuous_id.neg).continuousOn.mul
      (hcont.add continuousOn_const)
  have hgderiv (t : ℝ) (ht : t ∈ Ioo 0 T) : HasDerivAt G (G' t) t := by
    have hexp := (hasDerivAt_id t).neg.exp
    convert! hexp.mul ((hderiv t ht).add_const C) using 1
    try dsimp [G, G']
    ring
  have hG : AntitoneOn G (Icc 0 T) := by
    apply antitoneOn_of_hasDerivWithinAt_nonpos (convex_Icc 0 T) hgcont
    · intro t ht
      exact (hgderiv t (by simpa only [interior_Icc] using ht)).hasDerivWithinAt
    · intro t ht
      exact mul_nonpos_of_nonneg_of_nonpos (Real.exp_pos _).le
        (sub_nonpos.mpr (hbound t (by simpa only [interior_Icc] using ht)))
  intro t ht
  have hle := hG ⟨le_rfl, hT⟩ ht ht.1
  simpa [G, hinitial, mul_comm] using hle

/-- The scalar forced Gronwall estimate with zero initial energy. -/
theorem forced_gronwall {T C : ℝ} {E E' : ℝ → ℝ}
    (hT : 0 ≤ T) (hcont : ContinuousOn E (Icc 0 T)) (hinitial : E 0 = 0)
    (hderiv : ∀ t ∈ Ioo 0 T, HasDerivAt E (E' t) t)
    (hbound : ∀ t ∈ Ioo 0 T, E' t ≤ E t + C) :
    ∀ t ∈ Icc 0 T, E t ≤ C * (Real.exp t - 1) := by
  intro t ht
  have hweighted := forced_gronwall_weighted hT hcont hinitial hderiv hbound t ht
  have hmul := mul_le_mul_of_nonneg_right hweighted (Real.exp_pos t).le
  have hexp : Real.exp (-t) * Real.exp t = 1 := by
    rw [← Real.exp_add]
    simp
  rw [mul_assoc, hexp, mul_one] at hmul
  calc
    E t ≤ C * Real.exp t - C := by linarith
    _ = C * (Real.exp t - 1) := by ring

/-- A bound independent of the endpoint of an interval contained in `[0, 1]`. -/
theorem forced_gronwall_uniform {T C : ℝ} {E E' : ℝ → ℝ}
    (hT : 0 ≤ T) (hT1 : T ≤ 1) (hC : 0 ≤ C)
    (hcont : ContinuousOn E (Icc 0 T)) (hinitial : E 0 = 0)
    (hderiv : ∀ t ∈ Ioo 0 T, HasDerivAt E (E' t) t)
    (hbound : ∀ t ∈ Ioo 0 T, E' t ≤ E t + C) :
    ∀ t ∈ Icc 0 T, E t ≤ C * Real.exp 1 := by
  intro t ht
  calc
    E t ≤ C * (Real.exp t - 1) :=
      forced_gronwall hT hcont hinitial hderiv hbound t ht
    _ ≤ C * Real.exp t := mul_le_mul_of_nonneg_left (by linarith) hC
    _ ≤ C * Real.exp 1 :=
      mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (ht.2.trans hT1)) hC

end NavierStokesR3.ScalarEnergyBound
