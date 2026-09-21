/-
Copyright (c) 2026 Yuma Mizuno. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuma Mizuno
-/

import LeanPool.MarkoffModP.BGS.HasseWeil.FormalZetaDegreeIndexOne
import LeanPool.MarkoffModP.BGS.HasseWeil.FormalZetaUniqueness

/-!
# Formal zeta identity under a constant extension

Let `N r` be the point count over the degree-`r` extension of the original
constant field.  If all nonzero counts occur in degrees divisible by `d`,
and the point counts after the degree-`d` constant extension satisfy

`N_extended r = N (d * r)`,

then the exponential point-count zeta series satisfy

`Z_extended(T^d) = Z(T)^d`.

The proof does not assume this identity.  It reindexes the logarithmic
derivative series and then applies the already proved uniqueness theorem for
normalized formal differential equations.
-/

namespace BGS.HasseWeil

noncomputable section

open scoped PowerSeries

/-- Reindexing the point-count derivative series under a degree-`d`
constant extension.  Only positive indices occur in this series, so the
count and support hypotheses are correspondingly restricted to positive
integers. -/
theorem subst_pointCountDerivativeSeries_mul_derivative_X_pow
    (pointCount extendedPointCount : ℕ → ℕ) (d : ℕ) (hd : 0 < d)
    (hcount : ∀ r, 0 < r →
      extendedPointCount r = pointCount (d * r))
    (hsupport : ∀ n, 0 < n → ¬ d ∣ n → pointCount n = 0) :
    PowerSeries.subst (PowerSeries.X ^ d)
          (pointCountDerivativeSeries extendedPointCount) *
        PowerSeries.derivative ℂ (PowerSeries.X ^ d) =
      pointCountDerivativeSeries (fun n => d * pointCount n) := by
  ext n
  rw [PowerSeries.derivative_pow]
  simp only [PowerSeries.derivative_X, mul_one]
  rw [show PowerSeries.subst (PowerSeries.X ^ d)
          (pointCountDerivativeSeries extendedPointCount) *
        ((d : PowerSeries ℂ) * PowerSeries.X ^ (d - 1)) =
      (d : PowerSeries ℂ) *
        (PowerSeries.subst (PowerSeries.X ^ d)
          (pointCountDerivativeSeries extendedPointCount) *
            PowerSeries.X ^ (d - 1)) by ring]
  rw [show (d : PowerSeries ℂ) = PowerSeries.C (d : ℂ) by simp]
  simp only [PowerSeries.coeff_C_mul, PowerSeries.coeff_mul_X_pow',
    pointCountDerivativeSeries, PowerSeries.coeff_mk]
  split_ifs with hn
  · rw [PowerSeries.coeff_subst_X_pow hd.ne']
    split_ifs with hdiv
    · simp only [PowerSeries.coeff_mk, map_natCast]
      rw [hcount _ (Nat.succ_pos _)]
      have harg : d * ((n - (d - 1)) / d + 1) = n + 1 := by
        rw [mul_add, Nat.mul_div_cancel' hdiv]
        omega
      rw [harg]
      norm_cast
    · have hnot : ¬ d ∣ n + 1 := by
        intro hplus
        apply hdiv
        have heq : (n + 1) - d = n - (d - 1) := by omega
        simpa only [heq] using Nat.dvd_sub hplus (dvd_refl d)
      rw [hsupport (n + 1) (by omega) hnot]
      simp
  · have hnot : ¬ d ∣ n + 1 := by
      intro hplus
      have hle : d ≤ n + 1 := Nat.le_of_dvd (by omega) hplus
      omega
    rw [hsupport (n + 1) (by omega) hnot]
    simp

/-- Multiplying every point count by `d` multiplies its derivative series by
the constant series `d`. -/
theorem pointCountDerivativeSeries_nat_mul
    (pointCount : ℕ → ℕ) (d : ℕ) :
    pointCountDerivativeSeries (fun n => d * pointCount n) =
      (d : PowerSeries ℂ) * pointCountDerivativeSeries pointCount := by
  ext n
  rw [show (d : PowerSeries ℂ) = PowerSeries.C (d : ℂ) by simp]
  rw [PowerSeries.coeff_C_mul]
  simp [pointCountDerivativeSeries]

/-- The exponential point-count zeta series is normalized at `T = 0`. -/
@[simp] theorem constantCoeff_formalPointCountZeta (pointCount : ℕ → ℕ) :
    PowerSeries.constantCoeff (formalPointCountZeta pointCount) = 1 := by
  rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply]
  rw [formalPointCountZeta,
    PowerSeries.coeff_subst' (pointCountLogSeries_hasSubst pointCount)]
  rw [finsum_eq_single _ 0]
  · simp [pointCountLogSeries]
  · intro e he
    simp [pointCountLogSeries, zero_pow he]

/-- The formal constant-extension zeta identity, with hypotheses restricted
to the positive indices that actually occur in the zeta series. -/
theorem formalPointCountZeta_hasDegreeExtensionIdentity_of_positive
    (pointCount extendedPointCount : ℕ → ℕ) (d : ℕ) (hd : 0 < d)
    (hcount : ∀ r, 0 < r →
      extendedPointCount r = pointCount (d * r))
    (hsupport : ∀ n, 0 < n → ¬ d ∣ n → pointCount n = 0) :
    HasFormalDegreeExtensionZetaIdentity
      (formalPointCountZeta pointCount)
      (formalPointCountZeta extendedPointCount) d := by
  rw [HasFormalDegreeExtensionZetaIdentity]
  let F : PowerSeries ℂ := PowerSeries.subst
    (PowerSeries.X ^ d : PowerSeries ℂ)
    (formalPointCountZeta extendedPointCount)
  let G := formalPointCountZeta pointCount ^ d
  let A := pointCountDerivativeSeries (fun n => d * pointCount n)
  let hs : PowerSeries.HasSubst (PowerSeries.X ^ d : PowerSeries ℂ) :=
    PowerSeries.HasSubst.X_pow hd.ne'
  have hconstant : PowerSeries.constantCoeff F =
      PowerSeries.constantCoeff G := by
    rw [show F = PowerSeries.subst (PowerSeries.X ^ d)
      (formalPointCountZeta extendedPointCount) by rfl]
    rw [PowerSeries.constantCoeff_subst_X_pow hd.ne']
    simp [G]
  have hF : PowerSeries.derivative ℂ F = F * A := by
    have htrace :=
      formalPointCountZeta_hasPointCountDerivative extendedPointCount
    rw [HasFormalZetaPointCountDerivative] at htrace
    calc
      PowerSeries.derivative ℂ F =
          PowerSeries.subst (PowerSeries.X ^ d)
              (PowerSeries.derivative ℂ
                (formalPointCountZeta extendedPointCount)) *
            PowerSeries.derivative ℂ (PowerSeries.X ^ d) := by
              exact PowerSeries.derivative_subst ℂ hs
      _ = PowerSeries.subst (PowerSeries.X ^ d)
              (formalPointCountZeta extendedPointCount *
                pointCountDerivativeSeries extendedPointCount) *
            PowerSeries.derivative ℂ (PowerSeries.X ^ d) := by rw [htrace]
      _ = F * (PowerSeries.subst (PowerSeries.X ^ d)
              (pointCountDerivativeSeries extendedPointCount) *
            PowerSeries.derivative ℂ (PowerSeries.X ^ d)) := by
              rw [PowerSeries.subst_mul hs]
              simp only [F]
              rw [mul_assoc]
      _ = F * A := by
        rw [subst_pointCountDerivativeSeries_mul_derivative_X_pow
          pointCount extendedPointCount d hd hcount hsupport]
  have hG : PowerSeries.derivative ℂ G = G * A := by
    have htrace := formalPointCountZeta_hasPointCountDerivative pointCount
    rw [HasFormalZetaPointCountDerivative] at htrace
    have hpred : d - 1 + 1 = d :=
      Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr hd.ne')
    have hzpow : formalPointCountZeta pointCount ^ (d - 1) *
        formalPointCountZeta pointCount =
          formalPointCountZeta pointCount ^ d := by
      rw [← pow_succ, hpred]
    calc
      PowerSeries.derivative ℂ G =
          (d : PowerSeries ℂ) *
              formalPointCountZeta pointCount ^ (d - 1) *
            PowerSeries.derivative ℂ
              (formalPointCountZeta pointCount) := by
                exact PowerSeries.derivative_pow ℂ
                  (formalPointCountZeta pointCount) d
      _ = (d : PowerSeries ℂ) *
              formalPointCountZeta pointCount ^ (d - 1) *
            (formalPointCountZeta pointCount *
              pointCountDerivativeSeries pointCount) := by rw [htrace]
      _ = (formalPointCountZeta pointCount ^ (d - 1) *
              formalPointCountZeta pointCount) *
            ((d : PowerSeries ℂ) *
              pointCountDerivativeSeries pointCount) := by ring
      _ = G * A := by
        rw [hzpow, ← pointCountDerivativeSeries_nat_mul]
  exact powerSeries_eq_of_constantCoeff_eq_of_derivative_eq_mul
    F G A hconstant hF hG

/-- The formal constant-extension zeta identity from all-index count and
degree-support relations.  This is the convenient downstream form. -/
theorem formalPointCountZeta_hasDegreeExtensionIdentity
    (pointCount extendedPointCount : ℕ → ℕ) (d : ℕ) (hd : 0 < d)
    (hcount : ∀ r,
      extendedPointCount r = pointCount (d * r))
    (hsupport : ∀ n, ¬ d ∣ n → pointCount n = 0) :
    HasFormalDegreeExtensionZetaIdentity
      (formalPointCountZeta pointCount)
      (formalPointCountZeta extendedPointCount) d := by
  apply formalPointCountZeta_hasDegreeExtensionIdentity_of_positive
    pointCount extendedPointCount d hd
  · intro r _
    exact hcount r
  · intro n _ hn
    exact hsupport n hn

end

end BGS.HasseWeil
