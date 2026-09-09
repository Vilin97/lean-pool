/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.NavierStokes.CommonCoverSolve

/-!
# Normal, clock and amplitude rescaling in the tangent equation

The normal scales by `s`, its clock derivative by `s * rate`, and the
velocity amplitude by `amp`. The projected equation then scales by
`rate * amp`, whereas the scalar pressure coefficient scales by
`rate * amp / s`. These are identities of the actual operators, including
the totalized zero-normal case.
-/

@[expose] public section


namespace NavierStokes.NormalScaling

noncomputable section

open scoped InnerProductSpace
open TangentProjection

variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

theorem tangentProj_smul_normal (n f : H) {s : ℝ} (hs : s ≠ 0) :
    tangentProj (s • n) f = tangentProj n f := by
  by_cases hn : n = 0
  · simp [hn, tangentProj]
  have hn2 : ⟪n, n⟫_ℝ ≠ 0 := inner_self_ne_zero.mpr hn
  simp only [tangentProj, real_inner_smul_left, real_inner_smul_right, smul_smul]
  congr 2
  field_simp

theorem tangentProj_smul_right (n f : H) (amp : ℝ) :
    tangentProj n (amp • f) = amp • tangentProj n f := by
  simp only [tangentProj, real_inner_smul_right, smul_sub, smul_smul]
  congr 1
  congr 1
  ring

theorem negativeTangentProjection_smul (n : H) {s : ℝ} (hs : s ≠ 0) :
    CommonCoverSolve.negativeTangentProjection (s • n) =
      CommonCoverSolve.negativeTangentProjection n := by
  ext x
  simp only [CommonCoverSolve.negativeTangentProjection_apply,
    tangentProj_smul_normal n x hs]

theorem pressureCoefficient_rescale (n nDot u Ku f : H)
    (rate amp : ℝ) {s : ℝ} (hs : s ≠ 0) :
    pressureCoefficient (s • n) ((s * rate) • nDot) (amp • u)
      ((rate * amp) • Ku) ((rate * amp) • f) =
        (rate * amp / s) * pressureCoefficient n nDot u Ku f := by
  by_cases hn : n = 0
  · simp [hn, pressureCoefficient]
  have hn2 : ⟪n, n⟫_ℝ ≠ 0 := inner_self_ne_zero.mpr hn
  simp only [pressureCoefficient, real_inner_smul_left, real_inner_smul_right]
  field_simp

theorem projectedRhs_eq_pressure (n nDot u Ku f : H) (δ : ℝ) :
    projectedRhs n nDot u Ku f δ =
      pressureCoefficient n nDot u Ku f • n - (Ku + δ • u + f) := by
  apply eq_sub_iff_add_eq.mpr
  simpa only [add_assoc] using projected_balance n nDot u Ku f δ

theorem projectedRhs_rescale (n nDot u Ku f : H)
    (rate amp δ : ℝ) {s : ℝ} (hs : s ≠ 0) :
    projectedRhs (s • n) ((s * rate) • nDot) (amp • u)
      ((rate * amp) • Ku) ((rate * amp) • f) (rate * δ) =
        (rate * amp) • projectedRhs n nDot u Ku f δ := by
  rw [projectedRhs_eq_pressure, projectedRhs_eq_pressure,
    pressureCoefficient_rescale n nDot u Ku f rate amp hs]
  simp only [smul_smul]
  have hc : (rate * amp / s * pressureCoefficient n nDot u Ku f) * s =
      (rate * amp) * pressureCoefficient n nDot u Ku f := by
    field_simp
  rw [hc]
  module

theorem projectedOperator_rescale (n nDot : H) (K : H →L[ℝ] H)
    (rate δ : ℝ) {s : ℝ} (hs : s ≠ 0) :
    TangentODE.projectedOperator (s • n) ((s * rate) • nDot)
      (rate • K) (rate * δ) = rate • TangentODE.projectedOperator n nDot K δ := by
  ext x
  have hn : TangentODE.projectedOperator (s • n) ((s * rate) • nDot)
      (rate • K) (rate * δ) x =
      projectedRhs (s • n) ((s * rate) • nDot) x (rate • K x) 0 (rate * δ) := by
    simpa [tangentProj] using
      TangentODE.projectedOperator_apply (s • n) ((s * rate) • nDot) x 0
        (rate • K) (rate * δ)
  have ho : TangentODE.projectedOperator n nDot K δ x =
      projectedRhs n nDot x (K x) 0 δ := by
    simpa [tangentProj] using TangentODE.projectedOperator_apply n nDot x 0 K δ
  rw [hn]
  simp only [_root_.smul_apply, ho]
  simpa only [one_smul, mul_one, smul_zero] using
    projectedRhs_rescale n nDot x (K x) 0 rate 1 δ hs

end

end NavierStokes.NormalScaling
