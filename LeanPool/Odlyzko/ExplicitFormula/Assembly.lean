/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import LeanPool.Odlyzko.Numerics.Certificate
public import LeanPool.Odlyzko.Numerics.Degree
public import LeanPool.Odlyzko.Numerics.IntegralTail
public import LeanPool.Odlyzko.Reduction

/-! TODO: Add doc-string. -/

@[expose] public section

noncomputable section

open NumberField Module

namespace NumberField.Odlyzko

variable (K : Type*) [Field K] [NumberField K]

theorem le_rootDiscr_of_log_le_logDiscr_div_finrank {c : ℝ} (hc : 0 < c)
    (h :
      Real.log c ≤ Real.log |(discr K : ℝ)| / finrank ℚ K) :
    c ≤ rootDiscr K := by
  have hD : 0 < |(discr K : ℝ)| :=
    abs_pos.mpr (Int.cast_ne_zero.mpr (discr_ne_zero K))
  rw [rootDiscr_def, Int.cast_abs]
  calc
    c = Real.exp (Real.log c) := (Real.exp_log hc).symm
    _ ≤ Real.exp (Real.log |(discr K : ℝ)| / finrank ℚ K) :=
      Real.exp_le_exp.mpr h
    _ = |(discr K : ℝ)| ^ ((finrank ℚ K : ℝ)⁻¹) := by
      rw [Real.rpow_def_of_pos hD]
      grind

/-- A totally complex poitou estimate used in the Odlyzko-bound argument. -/
def TotallyComplexPoitouEstimate : Prop :=
  Real.log |(discr K : ℝ)| / finrank ℚ K ≥
    Real.eulerMascheroniConstant + Real.log (4 * Real.pi) -
      archimedeanIntegral odlyzkoScale -
      12 * Real.pi / (5 * finrank ℚ K * odlyzkoScale)

theorem target_le_rootDiscr_of_poitouEstimate
    (hdim : 18 ≤ finrank ℚ K) (hP : TotallyComplexPoitouEstimate K) :
    (8.25 : ℝ) ≤ rootDiscr K := by
  have hJ := NumericalCertificate.archimedeanIntegral_le
  have hnum := numericalCertificate_of_integral_le hJ
  have hdegree := degreeCorrection_le_degreeEighteen hdim
  have hlog :
      Real.log (33 / 4) ≤ Real.log |(discr K : ℝ)| / finrank ℚ K := by
    unfold TotallyComplexPoitouEstimate at hP
    linarith
  norm_num [show (8.25 : ℝ) = 33 / 4 by norm_num]
  exact le_rootDiscr_of_log_le_logDiscr_div_finrank K (by norm_num) hlog

theorem odlyzkoBound_of_poitouEstimate (hdim : 18 ≤ finrank ℚ K)
    (hP : TotallyComplexPoitouEstimate K) :
    |(discr K : ℝ)| ≥ (8.25 : ℝ) ^ finrank ℚ K :=
  target_pow_finrank_le_abs_discr K
    (target_le_rootDiscr_of_poitouEstimate K hdim hP)

end NumberField.Odlyzko
