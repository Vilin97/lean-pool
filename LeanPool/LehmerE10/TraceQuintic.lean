/-
Copyright (c) 2026 Dillon Ryan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dillon Ryan
-/

import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Topology.Algebra.Polynomial

/-!
# locating the roots of Lehmer's polynomial via its trace quintic.
`L` is reciprocal, so with `y = x + 1/x` it factors through a degree-5 polynomial:
  `L(x) = x⁵ · q(x + 1/x)`,  `q(y) = y⁵ + y⁴ − 5y³ − 5y² + 4y + 3`,
and a root of `L` lies on `|z| = 1` iff its trace `y = x + 1/x` lies in `[−2, 2]`
(`x = e^{iθ}`, `y = 2 cos θ`).  Salem's picture — 8 roots on the unit circle, one
reciprocal pair `{λ, 1/λ}` off it — therefore reduces to "`q` has 4 real roots in
`(−2, 2)` and one root in `(2, 21/10)`": five intermediate-value sign checks,
carried out here.
Axiom footprint: `propext`, `Classical.choice`, `Quot.sound` only.
-/

namespace LehmerE10


/-- Lehmer's polynomial as a function on ℂ. -/
noncomputable def lehmerC (z : ℂ) : ℂ :=
  z ^ 10 + z ^ 9 - z ^ 7 - z ^ 6 - z ^ 5 - z ^ 4 - z ^ 3 + z + 1

/-- The degree-5 TRACE polynomial over ℝ (for root location). -/
def traceQ (y : ℝ) : ℝ := y ^ 5 + y ^ 4 - 5 * y ^ 3 - 5 * y ^ 2 + 4 * y + 3

/-- Trace polynomial over ℂ. -/
noncomputable def traceQC (y : ℂ) : ℂ := y ^ 5 + y ^ 4 - 5 * y ^ 3 - 5 * y ^ 2 + 4 * y + 3

@[simp] theorem traceQC_ofReal (y : ℝ) : traceQC (y : ℂ) = (traceQ y : ℂ) := by
  unfold traceQC traceQ; push_cast; ring

/-- **THE RECIPROCAL → TRACE REDUCTION: `L(x) = x⁵ · q(x + 1/x)`, PROVEN.** -/
theorem lehmer_trace_reduction (z : ℂ) (hz : z ≠ 0) :
    lehmerC z = z ^ 5 * traceQC (z + 1 / z) := by
  unfold lehmerC traceQC
  field_simp
  ring

/-! ### The five real roots of the trace polynomial (IVT). -/

private theorem traceQ_cont : Continuous traceQ := by unfold traceQ; fun_prop

/-- A trace root in `(−2, −3/2)` (endpoints: q(−2)=−1 < 0 < 3/32 = q(−3/2)). -/
theorem traceQ_root_1 : ∃ y ∈ Set.Ioo (-2 : ℝ) (-3/2), traceQ y = 0 := by
  have h : (0:ℝ) ∈ Set.Ioo (traceQ (-2)) (traceQ (-3/2)) := by
    rw [Set.mem_Ioo]; unfold traceQ; norm_num
  obtain ⟨y, hy, hy0⟩ := intermediate_value_Ioo (by norm_num : (-2:ℝ) ≤ -3/2)
    traceQ_cont.continuousOn h
  exact ⟨y, hy, hy0⟩

/-- A trace root in `(−3/2, −1)`. -/
theorem traceQ_root_2 : ∃ y ∈ Set.Ioo (-3/2 : ℝ) (-1), traceQ y = 0 := by
  have h : (0:ℝ) ∈ Set.Ioo (traceQ (-1)) (traceQ (-3/2)) := by
    rw [Set.mem_Ioo]; unfold traceQ; norm_num
  obtain ⟨y, hy, hy0⟩ := intermediate_value_Ioo' (by norm_num : (-3/2:ℝ) ≤ -1)
    traceQ_cont.continuousOn h
  exact ⟨y, hy, hy0⟩

/-- A trace root in `(−1, 0)`. -/
theorem traceQ_root_3 : ∃ y ∈ Set.Ioo (-1 : ℝ) 0, traceQ y = 0 := by
  have h : (0:ℝ) ∈ Set.Ioo (traceQ (-1)) (traceQ 0) := by
    rw [Set.mem_Ioo]; unfold traceQ; norm_num
  obtain ⟨y, hy, hy0⟩ := intermediate_value_Ioo (by norm_num : (-1:ℝ) ≤ 0)
    traceQ_cont.continuousOn h
  exact ⟨y, hy, hy0⟩

/-- A trace root in `(0, 1)`. -/
theorem traceQ_root_4 : ∃ y ∈ Set.Ioo (0 : ℝ) 1, traceQ y = 0 := by
  have h : (0:ℝ) ∈ Set.Ioo (traceQ 1) (traceQ 0) := by
    rw [Set.mem_Ioo]; unfold traceQ; norm_num
  obtain ⟨y, hy, hy0⟩ := intermediate_value_Ioo' (by norm_num : (0:ℝ) ≤ 1)
    traceQ_cont.continuousOn h
  exact ⟨y, hy, hy0⟩

/-- The Salem trace root in `(2, 21/10)` — `y_L = λ_L + 1/λ_L > 2`, the off-circle
reciprocal pair. -/
theorem traceQ_root_salem : ∃ y ∈ Set.Ioo (2 : ℝ) (21/10), traceQ y = 0 := by
  have h : (0:ℝ) ∈ Set.Ioo (traceQ 2) (traceQ (21/10)) := by
    rw [Set.mem_Ioo]; unfold traceQ; norm_num
  obtain ⟨y, hy, hy0⟩ := intermediate_value_Ioo (by norm_num : (2:ℝ) ≤ 21/10)
    traceQ_cont.continuousOn h
  exact ⟨y, hy, hy0⟩

/-! ### On-circle Lehmer roots from trace roots in `(−2,2)`. -/

/-- Each trace root in `(−2,2)` gives a root of `L` on `|z| = 1`: for `y₀ ∈ (−2,2)`
    with `q(y₀) = 0`, the explicit `z = (y₀ + i√(4−y₀²))/2` has `‖z‖ = 1` and
    `z + 1/z = y₀`, so by the trace reduction `L(z) = z⁵ · q(y₀) = 0`. -/
theorem lehmer_root_on_circle (y₀ : ℝ) (h0 : traceQ y₀ = 0) (hmem : y₀ ∈ Set.Ioo (-2 : ℝ) 2) :
    ∃ z : ℂ, ‖z‖ = 1 ∧ lehmerC z = 0 := by
  obtain ⟨hlo, hhi⟩ := hmem
  have h4 : (0:ℝ) ≤ 4 - y₀ ^ 2 := by nlinarith
  set r : ℝ := Real.sqrt (4 - y₀ ^ 2) with hrdef
  have hrr : r * r = 4 - y₀ ^ 2 := Real.mul_self_sqrt h4
  set z : ℂ := ⟨y₀ / 2, r / 2⟩ with hzdef
  have hns : Complex.normSq z = 1 := by rw [hzdef, Complex.normSq_mk]; nlinarith [hrr]
  have hznorm : ‖z‖ = 1 := by rw [Complex.norm_def, hns, Real.sqrt_one]
  have hz0 : z ≠ 0 := Complex.normSq_pos.mp (by rw [hns]; norm_num)
  have hzre : z.re = y₀ / 2 := by rw [hzdef]
  have h1z : 1 / z = (starRingEnd ℂ) z := by
    rw [one_div, Complex.inv_def, hns]; simp
  have hsum : z + 1 / z = (y₀ : ℂ) := by
    rw [h1z, Complex.add_conj, hzre]; push_cast; ring
  refine ⟨z, hznorm, ?_⟩
  rw [lehmer_trace_reduction z hz0, hsum, traceQC_ofReal, h0, Complex.ofReal_zero, mul_zero]

/-- `L` has a root on the unit circle (combining the trace root in `(−1,0)` with
    `lehmer_root_on_circle`). -/
theorem elliptic_root_on_circle : ∃ z : ℂ, ‖z‖ = 1 ∧ lehmerC z = 0 := by
  obtain ⟨y, hy, hy0⟩ := traceQ_root_3
  exact lehmer_root_on_circle y hy0 ⟨by linarith [hy.1], by linarith [hy.2]⟩

end LehmerE10

