/-
Copyright (c) 2026 Quadratic Carleson formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quadratic Carleson formalization contributors
-/

import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecificLimits.Normed
import LeanPool.QuadraticCarleson.QuadraticCarleson.LacunaryMiddleRange
import LeanPool.QuadraticCarleson.QuadraticCarleson.DyadicAtomScales
import Mathlib.Topology.Algebra.InfiniteSum.ENNReal

/-!
# Geometric summation in the lacunary very-small range

For `j ∈ L B c m`, the paper's very-small contribution has weight
`2^(B + m/2 + j)`. Here the exponent is interpreted in `ℝ`, exactly as in
the displayed analytic estimate. For fixed `j`, the allowed modulation
indices form a left half-line. Reindexing that half-line by `ℕ` gives a
geometric series of ratio `2^(-1/2)`.

The final theorem is stated in `ℝ≥0∞`, so the exchange of the two countable
sums is genuine Tonelli and requires no summability assumption on the
nonnegative coefficients.
-/

open Set

namespace QuadraticCarleson.LacunaryVerySmallRange


open QuadraticCarleson.LacunaryMiddleRange

/-- The real-exponent weight in the paper's very-small double sum. -/
noncomputable def verySmallWeight (B : ℕ) (m j : ℤ) : ℝ :=
  (2 : ℝ) ^ ((B : ℝ) + (m : ℝ) / 2 + (j : ℝ))

theorem verySmallWeight_pos (B : ℕ) (m j : ℤ) :
    0 < verySmallWeight B m j := by
  unfold verySmallWeight
  positivity

/-- The author's exact half-open atom convention introduces at most a factor
`2` when the actual atom length is replaced by its lower dyadic scale. -/
theorem modulationWeight_mul_atomLength_le_two_mul_verySmallWeight
    {ι : Type*} {length : ι → ℝ} {I : ι} {j : ℤ}
    (hI : I ∈ QuadraticCarleson.dyadicAtomScaleClass length j)
    (B : ℕ) (m : ℤ) :
    (2 : ℝ) ^ ((B : ℝ) + (m : ℝ) / 2) * length I ≤
      2 * verySmallWeight B m j := by
  have hlength :=
    (QuadraticCarleson.dyadicAtomScaleClass_length_lt_two_mul hI).le
  have hweight : verySmallWeight B m j =
      (2 : ℝ) ^ ((B : ℝ) + (m : ℝ) / 2) * (2 : ℝ) ^ j := by
    unfold verySmallWeight
    rw [show (B : ℝ) + (m : ℝ) / 2 + (j : ℝ) =
      ((B : ℝ) + (m : ℝ) / 2) + (j : ℝ) by ring]
    rw [Real.rpow_add (by norm_num : (0 : ℝ) < 2), Real.rpow_intCast]
  calc
    (2 : ℝ) ^ ((B : ℝ) + (m : ℝ) / 2) * length I ≤
        (2 : ℝ) ^ ((B : ℝ) + (m : ℝ) / 2) *
          (2 * (2 : ℝ) ^ j) :=
      mul_le_mul_of_nonneg_left hlength (by positivity)
    _ = 2 * verySmallWeight B m j := by rw [hweight]; ring

/-- For fixed atom scale `j`, the admissible modulation indices. -/
def verySmallModulations (B c : ℕ) (j : ℤ) : Set ℤ :=
  {m | j ∈ L B c m}

/-- The largest admissible modulation index for a fixed atom scale. -/
def verySmallCutoff (B c : ℕ) (j : ℤ) : ℤ :=
  -(c : ℤ) - 2 * (B : ℤ) - 2 * j

theorem mem_verySmallModulations_iff {B c : ℕ} {j m : ℤ} :
    m ∈ verySmallModulations B c j ↔ m ≤ verySmallCutoff B c j := by
  simp only [verySmallModulations, mem_ofPred_eq, mem_L, verySmallCutoff]
  omega

/-- Reindex the integral half-line of admissible modulations by its distance
below the endpoint. -/
noncomputable def verySmallModulationsEquivNat (B c : ℕ) (j : ℤ) :
    verySmallModulations B c j ≃ ℕ where
  toFun m := Int.toNat (verySmallCutoff B c j - (m : ℤ))
  invFun n := ⟨verySmallCutoff B c j - (n : ℤ), by
    rw [mem_verySmallModulations_iff]
    omega⟩
  left_inv m := by
    apply Subtype.ext
    have hm : (m : ℤ) ≤ verySmallCutoff B c j :=
      mem_verySmallModulations_iff.mp m.property
    simp only
    rw [Int.toNat_of_nonneg (by omega)]
    omega
  right_inv n := by
    simp only
    rw [show verySmallCutoff B c j -
        (verySmallCutoff B c j - (n : ℤ)) = (n : ℤ) by ring]
    simp

/-- The geometric ratio appearing when `m` is decreased by one. -/
noncomputable def verySmallGeometricRatio : ℝ :=
  (2 : ℝ) ^ (-(1 : ℝ) / 2)

theorem verySmallGeometricRatio_nonneg :
    0 ≤ verySmallGeometricRatio := by
  unfold verySmallGeometricRatio
  positivity

theorem verySmallGeometricRatio_lt_one :
    verySmallGeometricRatio < 1 := by
  unfold verySmallGeometricRatio
  exact Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by norm_num)

/-- Explicit absolute sum of the geometric ratio. -/
noncomputable def verySmallGeometricConstant : ℝ :=
  (1 - verySmallGeometricRatio)⁻¹

theorem verySmallGeometricConstant_nonneg :
    0 ≤ verySmallGeometricConstant := by
  unfold verySmallGeometricConstant
  exact inv_nonneg.mpr (sub_nonneg.mpr verySmallGeometricRatio_lt_one.le)

/-- Exact support-slack factor left at the endpoint of the half-line. -/
noncomputable def verySmallSupportSlack (c : ℕ) : ℝ :=
  (2 : ℝ) ^ (-(c : ℝ) / 2)

theorem verySmallSupportSlack_pos (c : ℕ) :
    0 < verySmallSupportSlack c := by
  unfold verySmallSupportSlack
  positivity

theorem verySmallSupportSlack_le_one (c : ℕ) :
    verySmallSupportSlack c ≤ 1 := by
  unfold verySmallSupportSlack
  apply Real.rpow_le_one_of_one_le_of_nonpos (by norm_num)
  have hc : 0 ≤ (c : ℝ) := Nat.cast_nonneg c
  linarith

/-- At distance `n` below the endpoint, the very-small weight is the endpoint
slack times the `n`th power of the geometric ratio. -/
theorem verySmallWeight_cutoff_sub (B c : ℕ) (j : ℤ) (n : ℕ) :
    verySmallWeight B (verySmallCutoff B c j - (n : ℤ)) j =
      verySmallSupportSlack c * verySmallGeometricRatio ^ n := by
  unfold verySmallWeight verySmallCutoff verySmallSupportSlack
    verySmallGeometricRatio
  have hexp :
      (B : ℝ) +
          ((-(c : ℤ) - 2 * (B : ℤ) - 2 * j - (n : ℤ) : ℤ) : ℝ) / 2 +
          (j : ℝ) =
        -(c : ℝ) / 2 + (-(1 : ℝ) / 2) * (n : ℝ) := by
    push_cast
    ring
  rw [hexp, Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
  congr 1
  rw [← Real.rpow_natCast]
  rw [← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)]

/-- The very-small weight, extended by zero away from the admissible
modulation half-line. -/
noncomputable def restrictedVerySmallWeight (B c : ℕ) (j m : ℤ) : ℝ :=
  (verySmallModulations B c j).indicator (fun m ↦ verySmallWeight B m j) m

theorem restrictedVerySmallWeight_nonneg (B c : ℕ) (j m : ℤ) :
    0 ≤ restrictedVerySmallWeight B c j m := by
  by_cases hm : m ∈ verySmallModulations B c j
  · simp [restrictedVerySmallWeight, hm, (verySmallWeight_pos B m j).le]
  · simp [restrictedVerySmallWeight, hm]

theorem summable_restrictedVerySmallWeight (B c : ℕ) (j : ℤ) :
    Summable (restrictedVerySmallWeight B c j) := by
  have hgeom : Summable (fun n : ℕ ↦ verySmallGeometricRatio ^ n) :=
    summable_geometric_of_lt_one verySmallGeometricRatio_nonneg
      verySmallGeometricRatio_lt_one
  have hnat : Summable (fun n : ℕ ↦
      verySmallSupportSlack c * verySmallGeometricRatio ^ n) :=
    hgeom.mul_left _
  let e := verySmallModulationsEquivNat B c j
  have hsub : Summable (fun m : verySmallModulations B c j ↦
      verySmallWeight B (m : ℤ) j) := by
    apply ((e.symm).summable_iff).mp
    have heq :
        ((fun m : verySmallModulations B c j ↦ verySmallWeight B (m : ℤ) j) ∘
            e.symm) =
          (fun n : ℕ ↦ verySmallSupportSlack c * verySmallGeometricRatio ^ n) := by
      funext n
      change verySmallWeight B (verySmallCutoff B c j - (n : ℤ)) j = _
      exact verySmallWeight_cutoff_sub B c j n
    rw [heq]
    exact hnat
  rw [← summable_subtype_and_compl (s := verySmallModulations B c j)]
  constructor
  · simpa [restrictedVerySmallWeight] using hsub
  · have hz :
        (fun x : ↥((verySmallModulations B c j)ᶜ) ↦
          restrictedVerySmallWeight B c j (x : ℤ)) = 0 := by
      funext x
      have hx : (x : ℤ) ∉ verySmallModulations B c j := by
        simpa only [mem_compl_iff] using x.property
      simp [restrictedVerySmallWeight, hx]
    rw [hz]
    exact summable_zero

/-- Exact fixed-`j` geometric sum, including the support-slack factor. -/
theorem tsum_restrictedVerySmallWeight (B c : ℕ) (j : ℤ) :
    ∑' m : ℤ, restrictedVerySmallWeight B c j m =
      verySmallSupportSlack c * verySmallGeometricConstant := by
  unfold restrictedVerySmallWeight
  rw [← tsum_subtype (verySmallModulations B c j)
    (fun m : ℤ ↦ verySmallWeight B m j)]
  let e := verySmallModulationsEquivNat B c j
  calc
    (∑' m : verySmallModulations B c j, verySmallWeight B (m : ℤ) j) =
        ∑' n : ℕ, verySmallWeight B ((e.symm n :
          verySmallModulations B c j) : ℤ) j :=
      ((e.symm).tsum_eq (fun m : verySmallModulations B c j ↦
        verySmallWeight B (m : ℤ) j)).symm
    _ = ∑' n : ℕ,
        verySmallSupportSlack c * verySmallGeometricRatio ^ n := by
      apply tsum_congr
      intro n
      change verySmallWeight B (verySmallCutoff B c j - (n : ℤ)) j = _
      exact verySmallWeight_cutoff_sub B c j n
    _ = verySmallSupportSlack c *
        (∑' n : ℕ, verySmallGeometricRatio ^ n) := by
      rw [tsum_mul_left]
    _ = verySmallSupportSlack c * verySmallGeometricConstant := by
      rw [tsum_geometric_of_lt_one verySmallGeometricRatio_nonneg
        verySmallGeometricRatio_lt_one]
      rfl

/-- Uniform fixed-`j` bound by an absolute geometric constant. -/
theorem tsum_restrictedVerySmallWeight_le (B c : ℕ) (j : ℤ) :
    ∑' m : ℤ, restrictedVerySmallWeight B c j m ≤
      verySmallGeometricConstant := by
  rw [tsum_restrictedVerySmallWeight]
  exact mul_le_of_le_one_left verySmallGeometricConstant_nonneg
    (verySmallSupportSlack_le_one c)

/-- ENNReal form of the fixed-`j` estimate, used in the unconditional Tonelli
argument below. -/
theorem tsum_ofReal_restrictedVerySmallWeight_le (B c : ℕ) (j : ℤ) :
    ∑' m : ℤ, ENNReal.ofReal (restrictedVerySmallWeight B c j m) ≤
      ENNReal.ofReal verySmallGeometricConstant := by
  rw [← ENNReal.ofReal_tsum_of_nonneg
    (restrictedVerySmallWeight_nonneg B c j)
    (summable_restrictedVerySmallWeight B c j)]
  exact ENNReal.ofReal_le_ofReal (tsum_restrictedVerySmallWeight_le B c j)

/-- Tonelli consequence for arbitrary nonnegative atom-scale coefficients.
No summability assumption is needed because the statement takes values in
`ℝ≥0∞`. -/
theorem tsum_tsum_verySmall_le (B c : ℕ) (a : ℤ → ENNReal) :
    ∑' m : ℤ, ∑' j : ℤ,
        ENNReal.ofReal (restrictedVerySmallWeight B c j m) * a j ≤
      ENNReal.ofReal verySmallGeometricConstant * (∑' j : ℤ, a j) := by
  rw [ENNReal.tsum_comm]
  calc
    (∑' j : ℤ, ∑' m : ℤ,
        ENNReal.ofReal (restrictedVerySmallWeight B c j m) * a j) =
        ∑' j : ℤ,
          (∑' m : ℤ, ENNReal.ofReal (restrictedVerySmallWeight B c j m)) *
            a j := by
      apply tsum_congr
      intro j
      rw [ENNReal.tsum_mul_right]
    _ ≤ ∑' j : ℤ, ENNReal.ofReal verySmallGeometricConstant * a j := by
      apply ENNReal.tsum_le_tsum
      intro j
      gcongr
      exact tsum_ofReal_restrictedVerySmallWeight_le B c j
    _ = ENNReal.ofReal verySmallGeometricConstant * ∑' j : ℤ, a j := by
      rw [ENNReal.tsum_mul_left]

end QuadraticCarleson.LacunaryVerySmallRange
