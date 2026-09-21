/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

import LeanPool.CoarseGraining.Homogenization.Book.Ch05.Theorems.Section56.SmallContrastAssembly

/-! # Scalar Recursion -/

namespace Homogenization
namespace Book
namespace Ch05
namespace Section56

open MeasureTheory
open scoped BigOperators Matrix.Norms.Elementwise Matrix.Norms.L2Operator

noncomputable section

namespace SmallContrastAlgebraicDecay

open SmallContrastAssembly

/-!
# Scalar reductions for Proposition `p.small.contrast.algebraic.decay`

This file extracts the manuscript scalar recursion ingredients from the
Section 5.6 assembly estimate.  In particular, the additivity defect for the
special vectors at scale `m` is controlled by the drop of `Theta` from `k` to
`m`.
-/

/-- If `\widetilde\Theta_0 - 1` is at most a parameter not exceeding one, then
`\widetilde\Theta_0 ≤ 2`. -/
theorem widetildeThetaAtScale_zero_le_two_of_sub_one_le_delta
    {d : ℕ} [NeZero d] {P : Ch04.RestrictionCoeffLaw d}
    {hP4 : QuantitativeCoarseGrainedEllipticity P} {delta : ℝ}
    (hdelta_le_one : delta ≤ 1)
    (hsmall : widetildeThetaAtScale P (0 : ℤ) hP4 - 1 ≤ delta) :
    widetildeThetaAtScale P (0 : ℤ) hP4 ≤ 2 := by
  linarith

/-- Smallness at scale zero propagates to all scalar contrasts. -/
theorem thetaAtScale_sub_one_le_delta_of_widetildeThetaAtScale_zero_sub_one_le_delta
    {d : ℕ} [NeZero d] {P : Ch04.RestrictionCoeffLaw d}
    (hP : Ch04.RestrictionLawCarrier P) (hStruct : Ch04.RestrictionStructuralLaw P)
    (hP4 : QuantitativeCoarseGrainedEllipticity P)
    {delta : ℝ}
    (hsmall : widetildeThetaAtScale P (0 : ℤ) hP4 - 1 ≤ delta)
    (m : ℕ) :
    thetaAtScale hP hStruct (m : ℤ) - 1 ≤ delta := by
  have hmono :
      thetaAtScale hP hStruct (m : ℤ) ≤
        thetaAtScale hP hStruct (0 : ℤ) := by
    simpa using
      Section54.GoodScale.thetaAtScale_mono_of_P4
        hP hStruct hP4 (n := 0) (m := m) (Nat.zero_le m)
  have htheta0 :
      thetaAtScale hP hStruct (0 : ℤ) ≤
        widetildeThetaAtScale P (0 : ℤ) hP4 :=
    thetaAtScale_zero_le_widetildeThetaAtScale_zero_of_P4 hP hStruct hP4
  linarith

/-- A real-variable form of the special-vector `tau` drop. -/
theorem half_sum_sub_le_product_drop
    {r x y : ℝ} (hr : 1 ≤ r) (hx : r ≤ x) (hy : r ≤ y) :
    (1 / 2 : ℝ) * (x - r) + (1 / 2 : ℝ) * (y - r) ≤
      x * y - r ^ (2 : ℕ) := by
  have hx_nonneg : 0 ≤ x - r := by linarith
  have hy_nonneg : 0 ≤ y - r := by linarith
  have hprod_nonneg : 0 ≤ (x - r) * (y - r) :=
    mul_nonneg hx_nonneg hy_nonneg
  nlinarith

/-- The special-vector additivity defect is controlled by the scalar contrast
drop between scales `k` and `m`. -/
theorem tauAtScale_special_le_thetaAtScale_sub
    {d : ℕ} [NeZero d] {P : Ch04.RestrictionCoeffLaw d}
    (hP : Ch04.RestrictionLawCarrier P) (hStruct : Ch04.RestrictionStructuralLaw P)
    (hP4 : QuantitativeCoarseGrainedEllipticity P)
    {k m : ℕ} (hkm : k ≤ m) (e : Vec d) (he : vecNormSq e = 1) :
    let p_e := specialPAtScale hP hStruct (m : ℤ) e
    let q_e := specialQAtScale hP hStruct (m : ℤ) e
    tauAtScale P (m : ℤ) (k : ℤ) p_e q_e ≤
      thetaAtScale hP hStruct (k : ℤ) -
        thetaAtScale hP hStruct (m : ℤ) := by
  dsimp only
  let p_e := specialPAtScale hP hStruct (m : ℤ) e
  let q_e := specialQAtScale hP hStruct (m : ℤ) e
  let σ := sigmaHatAtScale hP hStruct (m : ℤ)
  let b_m := hP.barSigmaAtScale hStruct (m : ℤ)
  let c_m := hP.barSigmaStarAtScale hStruct (m : ℤ)
  let b_k := hP.barSigmaAtScale hStruct (k : ℤ)
  let c_k := hP.barSigmaStarAtScale hStruct (k : ℤ)
  let θm := thetaAtScale hP hStruct (m : ℤ)
  let θk := thetaAtScale hP hStruct (k : ℤ)
  let r := Real.sqrt θm
  let x := σ⁻¹ * b_k
  let y := σ * c_k⁻¹
  have hb_m : 0 < b_m := by
    simpa [b_m] using
      Section54.Pigeonhole.barSigmaAtScale_pos_of_P4 hP hStruct hP4 m
  have hc_m : 0 < c_m := by
    simpa [c_m] using
      Section54.Pigeonhole.barSigmaStarAtScale_pos_of_P4 hP hStruct hP4 m
  have hb_k : 0 < b_k := by
    simpa [b_k] using
      Section54.Pigeonhole.barSigmaAtScale_pos_of_P4 hP hStruct hP4 k
  have hc_k : 0 < c_k := by
    simpa [c_k] using
      Section54.Pigeonhole.barSigmaStarAtScale_pos_of_P4 hP hStruct hP4 k
  have hσ_pos : 0 < σ := by
    simpa [σ] using
      Section54.GoodScale.sigmaHatAtScale_pos_of_P4 hP hStruct hP4 m
  have hchain :=
    Section54.Pigeonhole.scalarChain_of_P4 hP hStruct hP4 hkm
  have hb_m_le_k : b_m ≤ b_k := by
    simpa [b_m, b_k] using hchain.2.2
  have hc_inv_m_le_k : c_m⁻¹ ≤ c_k⁻¹ := by
    simpa [c_m, c_k] using hchain.2.1
  have hσ_eq : σ = Real.sqrt (b_m * c_m) := by rfl
  have hθm_eq : θm = b_m * c_m⁻¹ := by rfl
  have hθk_eq : θk = b_k * c_k⁻¹ := by rfl
  have hbm_scaled : σ⁻¹ * b_m = r := by
    rw [mul_comm]
    simpa [r, θm, b_m, c_m, σ] using
      Section54.GoodScale.barSigma_mul_inv_sigma_eq_sqrt_theta
        hb_m hc_m hσ_eq hθm_eq
  have hcm_scaled : σ * c_m⁻¹ = r := by
    simpa [r, θm, b_m, c_m, σ] using
      Section54.GoodScale.sigma_mul_inv_star_eq_sqrt_theta
        hb_m hc_m hσ_eq hθm_eq
  have hr_one : 1 ≤ r := by
    have hθm_one : 1 ≤ θm := by
      simpa [θm] using
        Section54.GoodScale.one_le_thetaAtScale_of_P4 hP hStruct hP4 m
    simpa [r] using Real.one_le_sqrt.mpr hθm_one
  have hx_ge : r ≤ x := by
    calc
      r = σ⁻¹ * b_m := hbm_scaled.symm
      _ ≤ σ⁻¹ * b_k :=
        mul_le_mul_of_nonneg_left hb_m_le_k (inv_pos.mpr hσ_pos).le
      _ = x := rfl
  have hy_ge : r ≤ y := by
    calc
      r = σ * c_m⁻¹ := hcm_scaled.symm
      _ ≤ σ * c_k⁻¹ :=
        mul_le_mul_of_nonneg_left hc_inv_m_le_k hσ_pos.le
      _ = y := rfl
  have htau_formula :
      tauAtScale P (m : ℤ) (k : ℤ) p_e q_e =
        (1 / 2 : ℝ) * σ⁻¹ * (b_k - b_m) +
          (1 / 2 : ℝ) * σ * (c_k⁻¹ - c_m⁻¹) := by
    have hBlock_m :
        Integrable (Ch04.coarseFullBlockMatrixAtCube (originCube d (m : ℤ))) P :=
      Section52.originBlockIntegrableAtScale_from_P4 hP hStruct hP4 m
    have hBlock_k :
        Integrable (Ch04.coarseFullBlockMatrixAtCube (originCube d (k : ℤ))) P :=
      Section52.originBlockIntegrableAtScale_from_P4 hP hStruct hP4 k
    calc
      tauAtScale P (m : ℤ) (k : ℤ) p_e q_e =
          tauScalarFormula hP hStruct (m : ℤ) (k : ℤ) p_e q_e := by
        rw [Section52.tauAtScale_eq_tauScalarFormula
          hP hStruct (m : ℤ) (k : ℤ) p_e q_e hBlock_m hBlock_k]
      _ = (1 / 2 : ℝ) * σ⁻¹ * (b_k - b_m) +
          (1 / 2 : ℝ) * σ * (c_k⁻¹ - c_m⁻¹) := by
        simpa [p_e, q_e, σ, b_k, b_m, c_k, c_m] using
          Section54.GoodScale.tauScalarFormula_special_eq_of_P4
            hP hStruct hP4 m k e he
  have hleft_eq :
      (1 / 2 : ℝ) * σ⁻¹ * (b_k - b_m) +
          (1 / 2 : ℝ) * σ * (c_k⁻¹ - c_m⁻¹) =
        (1 / 2 : ℝ) * (x - r) + (1 / 2 : ℝ) * (y - r) := by
    have hx_sub : x - r = σ⁻¹ * (b_k - b_m) := by
      rw [← hbm_scaled]
      ring
    have hy_sub : y - r = σ * (c_k⁻¹ - c_m⁻¹) := by
      rw [← hcm_scaled]
      ring
    rw [hx_sub, hy_sub]
    ring
  have hprod_eq : x * y - r ^ (2 : ℕ) = θk - θm := by
    have hr_sq : r ^ (2 : ℕ) = θm := by
      have hθm_nonneg : 0 ≤ θm := by
        have hθm_one : 1 ≤ θm := by
          simpa [θm] using
            Section54.GoodScale.one_le_thetaAtScale_of_P4 hP hStruct hP4 m
        linarith
      simp [r, Real.sq_sqrt hθm_nonneg]
    have hx_y : x * y = θk := by
      have hσ_ne : σ ≠ 0 := ne_of_gt hσ_pos
      calc
        x * y = (σ⁻¹ * b_k) * (σ * c_k⁻¹) := rfl
        _ = b_k * c_k⁻¹ := by field_simp [hσ_ne]
        _ = θk := hθk_eq.symm
    rw [hx_y, hr_sq]
  calc
    tauAtScale P (m : ℤ) (k : ℤ) p_e q_e
        = (1 / 2 : ℝ) * (x - r) + (1 / 2 : ℝ) * (y - r) := by
          rw [htau_formula, hleft_eq]
    _ ≤ x * y - r ^ (2 : ℕ) :=
          half_sum_sub_le_product_drop hr_one hx_ge hy_ge
    _ = θk - θm := hprod_eq

end SmallContrastAlgebraicDecay

end

end Section56
end Ch05
end Book
end Homogenization
