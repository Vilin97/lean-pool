/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Tactic.Abel
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import LeanPool.CoarseGraining.Homogenization.Book.Ch02.Theorems.MatrixOperatorNorm
import LeanPool.CoarseGraining.Homogenization.Book.Ch04.Theorems.PartitionAveragesDefinitions
import LeanPool.CoarseGraining.Homogenization.Book.Ch04.Theorems.StationaryExpectations
import LeanPool.CoarseGraining.Homogenization.Book.Ch05.Theorems.Section52.ScalarPreliminaries
import LeanPool.CoarseGraining.Homogenization.Book.Ch05.Theorems.Section54.GoodScale.ScalarBounds

/-! # P1 -/

open scoped BigOperators Matrix.Norms.Elementwise
open scoped Matrix.Norms.L2Operator


/-!
# Deterministic contrast algebra

Pure-real deterministic algebra from the high-moment paper
(Armstrong–Kuusi–Loher, to appear), Section "Deterministic contrast
algebra".  The scalar drop estimates are paired with the library's operator-norm API
for the normalization comparison in `e.norm.compare`.
-/


namespace Homogenization.HighContrast.EntryScale

/-- The scalar contrast drop `r_m^2 (a b - 1)`.

Source label: `e.F.drop`.
-/
def contrastDrop (r_m a b : ℝ) : ℝ :=
  r_m ^ 2 * (a * b - 1)

/-- The terminal additivity defect `tau`.

Source label: `e.tau.terminal`.
-/
noncomputable def terminalTau (r_m a b : ℝ) : ℝ :=
  r_m * ((a - 1) + (b - 1)) / 2

/-- A no-drop window, written only in terms of the endpoint contrasts.

Source label: `e.nodrop`.
-/
def noDropWindow (rho F_k F_m : ℝ) : Prop :=
  F_k - F_m ≤ rho * F_m

/-- The scalar contrast excess `F_m = Theta_m - 1`.

Source label: `e.F.drop`.
-/
noncomputable def contrastExcessAtScale
    {d : ℕ} [NeZero d] {P : Homogenization.Book.Ch04.RestrictionCoeffLaw d}
    (hP : Homogenization.Book.Ch04.RestrictionLawCarrier P)
    (hStruct : Homogenization.Book.Ch04.RestrictionStructuralLaw P)
    (m : ℕ) : ℝ :=
  Homogenization.Book.Ch05.thetaAtScale hP hStruct (m : ℤ) - 1

/--
Source label `e.J.moment.bound`: conversion from the library's
`sqrt(theta_m)` scalar to the manuscript's `r_m` normalization, under the
source hypothesis `r_m^2 = 1 + F_m`.
-/
theorem sqrt_thetaAtScale_eq_r_m_of_sq_contrastExcess
    {d : ℕ} [NeZero d] {P : Homogenization.Book.Ch04.RestrictionCoeffLaw d}
    (hP : Homogenization.Book.Ch04.RestrictionLawCarrier P)
    (hStruct : Homogenization.Book.Ch04.RestrictionStructuralLaw P)
    (m : ℕ) {r_m : ℝ}
    (hr_nonneg : 0 ≤ r_m)
    (hr_sq : r_m ^ 2 = 1 + contrastExcessAtScale hP hStruct m) :
    Real.sqrt (Homogenization.Book.Ch05.thetaAtScale hP hStruct (m : ℤ)) = r_m := by
  let θ := Homogenization.Book.Ch05.thetaAtScale hP hStruct (m : ℤ)
  have hθ_eq : θ = 1 + contrastExcessAtScale hP hStruct m := by
    dsimp [θ, contrastExcessAtScale]
    ring
  have hθ_nonneg : 0 ≤ θ := by
    rw [hθ_eq, ← hr_sq]
    exact sq_nonneg r_m
  exact (Real.sqrt_eq_iff_eq_sq hθ_nonneg hr_nonneg).2
    (by rw [hθ_eq, ← hr_sq])

/--
Source labels `p.HC.CR` and `e.HC.CR`: the library's centered coarse-fluctuation
term `(sqrt(theta_m) - 1)^2` is controlled by the manuscript contrast excess
`F_m = theta_m - 1`.
-/
theorem sqrt_thetaAtScale_sub_one_sq_le_contrastExcessAtScale
    {d : ℕ} [NeZero d] {P : Homogenization.Book.Ch04.RestrictionCoeffLaw d}
    (hP : Homogenization.Book.Ch04.RestrictionLawCarrier P)
    (hStruct : Homogenization.Book.Ch04.RestrictionStructuralLaw P)
    (hP4 : Homogenization.Book.Ch05.QuantitativeCoarseGrainedEllipticity P)
    (m : ℕ) :
    (Real.sqrt (Homogenization.Book.Ch05.thetaAtScale hP hStruct (m : ℤ)) - 1) ^
        (2 : ℕ) ≤
      contrastExcessAtScale hP hStruct m := by
  let θ := Homogenization.Book.Ch05.thetaAtScale hP hStruct (m : ℤ)
  have hθ_one : 1 ≤ θ := by
    simpa [θ] using
      Homogenization.Book.Ch05.Section54.GoodScale.one_le_thetaAtScale_of_P4
        hP hStruct hP4 m
  have hθ_nonneg : 0 ≤ θ := le_trans zero_le_one hθ_one
  let a := Real.sqrt θ
  have ha_sq : a ^ (2 : ℕ) = θ := Real.sq_sqrt hθ_nonneg
  have ha_sub_nonneg : 0 ≤ a - 1 := by
    have ha_one : 1 ≤ a := by
      simpa [a] using Real.one_le_sqrt.mpr hθ_one
    linarith
  have hdiff_nonneg : 0 ≤ a ^ (2 : ℕ) - 1 - (a - 1) ^ (2 : ℕ) := by
    have hdiff_eq : a ^ (2 : ℕ) - 1 - (a - 1) ^ (2 : ℕ) = 2 * (a - 1) := by
      ring
    rw [hdiff_eq]
    nlinarith
  calc
    (Real.sqrt (Homogenization.Book.Ch05.thetaAtScale hP hStruct (m : ℤ)) - 1) ^
        (2 : ℕ) = (a - 1) ^ (2 : ℕ) := by
          rfl
    _ ≤ a ^ (2 : ℕ) - 1 := by linarith
    _ = contrastExcessAtScale hP hStruct m := by
      rw [ha_sq]
      rfl

/-- The terminal scalar prefactor `P_{k,m}`.

Source label: `e.P.bound`.
-/
def terminalP (r_m a b : ℝ) : ℝ :=
  r_m * (a + b)

/--
The concrete terminal scalar prefactor at scales `k <= m`:
`P_{k,m} = r_m (a_{k,m} + b_{k,m})`.

Source label: `e.P.bound`.
-/
noncomputable def terminalPAtScales
    {d : ℕ} [NeZero d] {P : Homogenization.Book.Ch04.RestrictionCoeffLaw d}
    (hP : Homogenization.Book.Ch04.RestrictionLawCarrier P)
    (hStruct : Homogenization.Book.Ch04.RestrictionStructuralLaw P)
    (k m : ℕ) : ℝ :=
  terminalP
    (Real.sqrt (1 + contrastExcessAtScale hP hStruct m))
    (hP.barSigmaAtScale hStruct (k : ℤ) /
      hP.barSigmaAtScale hStruct (m : ℤ))
    ((hP.barSigmaStarAtScale hStruct (k : ℤ))⁻¹ /
      (hP.barSigmaStarAtScale hStruct (m : ℤ))⁻¹)

/--
Local weak-norm scalar weight at the left edge of the window.  This is the
coefficient produced by the raw high-contrast computation before the library's final
scale-zero baseline conversion.

Source labels: `p.HC.CR` and `e.P.bound`.
-/
noncomputable def localWeakNormScalarWeightAtScales
    {d : ℕ} [NeZero d] {P : Homogenization.Book.Ch04.RestrictionCoeffLaw d}
    (hP : Homogenization.Book.Ch04.RestrictionLawCarrier P)
    (hStruct : Homogenization.Book.Ch04.RestrictionStructuralLaw P)
    (k m : ℕ) : ℝ :=
  let σ := Homogenization.Book.Ch05.sigmaHatAtScale hP hStruct (m : ℤ)
  σ * (hP.barSigmaStarAtScale hStruct (k : ℤ))⁻¹ +
    σ⁻¹ * hP.barSigmaAtScale hStruct (k : ℤ)

/-- Source label `e.F.drop`: the contrast drop is `r_m^2 (a b - 1)`. -/
@[simp]
theorem contrast_drop_eq (r_m a b : ℝ) :
    contrastDrop r_m a b = r_m ^ 2 * (a * b - 1) :=
  rfl

/--
Source label `e.tau.terminal`: real algebra rewriting the library's special-vector
tau scalar formula into the paper's `r_m`, `a_{j,m}`, `b_{j,m}` notation.
-/
theorem terminalTau_eq_of_barSigma_ratios {sigma theta bm cm bk ck : ℝ}
    (hbm : 0 < bm) (hcm : 0 < cm) (hck : 0 < ck)
    (hsigma : sigma = Real.sqrt (bm * cm))
    (htheta : theta = bm * cm⁻¹) :
    (1 / 2 : ℝ) * sigma⁻¹ * (bk - bm) +
        (1 / 2 : ℝ) * sigma * (ck⁻¹ - cm⁻¹) =
      terminalTau (Real.sqrt theta) (bk / bm) (ck⁻¹ / cm⁻¹) := by
  have hsigma_inv : bm * sigma⁻¹ = Real.sqrt theta :=
    Homogenization.Book.Ch05.Section54.GoodScale.barSigma_mul_inv_sigma_eq_sqrt_theta
      hbm hcm hsigma htheta
  have hsigma_star : sigma * cm⁻¹ = Real.sqrt theta :=
    Homogenization.Book.Ch05.Section54.GoodScale.sigma_mul_inv_star_eq_sqrt_theta
      hbm hcm hsigma htheta
  have hbm_ne : bm ≠ 0 := ne_of_gt hbm
  have hcm_ne : cm ≠ 0 := ne_of_gt hcm
  have hck_ne : ck ≠ 0 := ne_of_gt hck
  have hfirst :
      sigma⁻¹ * (bk - bm) = Real.sqrt theta * (bk / bm - 1) := by
    calc
      sigma⁻¹ * (bk - bm) = (bm * sigma⁻¹) * (bk / bm - 1) := by
        field_simp [hbm_ne]
      _ = Real.sqrt theta * (bk / bm - 1) := by rw [hsigma_inv]
  have hsecond :
      sigma * (ck⁻¹ - cm⁻¹) = Real.sqrt theta * (ck⁻¹ / cm⁻¹ - 1) := by
    calc
      sigma * (ck⁻¹ - cm⁻¹) =
          (sigma * cm⁻¹) * (ck⁻¹ / cm⁻¹ - 1) := by
        field_simp [hcm_ne, hck_ne]
      _ = Real.sqrt theta * (ck⁻¹ / cm⁻¹ - 1) := by rw [hsigma_star]
  rw [terminalTau]
  calc
    (1 / 2 : ℝ) * sigma⁻¹ * (bk - bm) +
        (1 / 2 : ℝ) * sigma * (ck⁻¹ - cm⁻¹)
        = (1 / 2 : ℝ) * (sigma⁻¹ * (bk - bm)) +
          (1 / 2 : ℝ) * (sigma * (ck⁻¹ - cm⁻¹)) := by ring
    _ = (1 / 2 : ℝ) * (Real.sqrt theta * (bk / bm - 1)) +
          (1 / 2 : ℝ) * (Real.sqrt theta * (ck⁻¹ / cm⁻¹ - 1)) := by
          rw [hfirst, hsecond]
    _ = Real.sqrt theta * (bk / bm - 1 + (ck⁻¹ / cm⁻¹ - 1)) / 2 := by
          ring

/--
Source label `e.sqrt.tau.absorb`: real algebra rewriting the library's special-vector
expected-response scalar formula into the paper's terminal prefactor notation.
-/
theorem half_terminalP_sub_one_eq_of_barSigma_ratios {sigma theta bm cm bk ck : ℝ}
    (hbm : 0 < bm) (hcm : 0 < cm) (hck : 0 < ck)
    (hsigma : sigma = Real.sqrt (bm * cm))
    (htheta : theta = bm * cm⁻¹) :
    (1 / 2 : ℝ) * sigma⁻¹ * bk +
        (1 / 2 : ℝ) * sigma * ck⁻¹ - 1 =
      (1 / 2 : ℝ) *
          terminalP (Real.sqrt theta) (bk / bm) (ck⁻¹ / cm⁻¹) - 1 := by
  have hsigma_inv : bm * sigma⁻¹ = Real.sqrt theta :=
    Homogenization.Book.Ch05.Section54.GoodScale.barSigma_mul_inv_sigma_eq_sqrt_theta
      hbm hcm hsigma htheta
  have hsigma_star : sigma * cm⁻¹ = Real.sqrt theta :=
    Homogenization.Book.Ch05.Section54.GoodScale.sigma_mul_inv_star_eq_sqrt_theta
      hbm hcm hsigma htheta
  have hbm_ne : bm ≠ 0 := ne_of_gt hbm
  have hcm_ne : cm ≠ 0 := ne_of_gt hcm
  have hck_ne : ck ≠ 0 := ne_of_gt hck
  have hfirst :
      sigma⁻¹ * bk = Real.sqrt theta * (bk / bm) := by
    calc
      sigma⁻¹ * bk = (bm * sigma⁻¹) * (bk / bm) := by
        field_simp [hbm_ne]
      _ = Real.sqrt theta * (bk / bm) := by rw [hsigma_inv]
  have hsecond :
      sigma * ck⁻¹ = Real.sqrt theta * (ck⁻¹ / cm⁻¹) := by
    calc
      sigma * ck⁻¹ = (sigma * cm⁻¹) * (ck⁻¹ / cm⁻¹) := by
        field_simp [hcm_ne, hck_ne]
      _ = Real.sqrt theta * (ck⁻¹ / cm⁻¹) := by rw [hsigma_star]
  rw [terminalP]
  calc
    (1 / 2 : ℝ) * sigma⁻¹ * bk +
        (1 / 2 : ℝ) * sigma * ck⁻¹ - 1
        = (1 / 2 : ℝ) * (sigma⁻¹ * bk) +
          (1 / 2 : ℝ) * (sigma * ck⁻¹) - 1 := by ring
    _ = (1 / 2 : ℝ) * (Real.sqrt theta * (bk / bm)) +
          (1 / 2 : ℝ) * (Real.sqrt theta * (ck⁻¹ / cm⁻¹)) - 1 := by
          rw [hfirst, hsecond]
    _ = (1 / 2 : ℝ) *
          (Real.sqrt theta * (bk / bm + ck⁻¹ / cm⁻¹)) - 1 := by
          ring

/--
Source label `e.tau.terminal`: library-facing terminal-pair formula.  For the
special vectors `p_e,q_e`, `tauAtScale` is exactly the local scalar
`terminalTau` with `r_m = sqrt Theta_m` and the paper ratios
`a_{k,m}`, `b_{k,m}`.
-/
theorem tauAtScale_special_eq_terminalTau_of_P4
    {d : ℕ} [NeZero d] {P : Homogenization.Book.Ch04.RestrictionCoeffLaw d}
    (hP : Homogenization.Book.Ch04.RestrictionLawCarrier P)
    (hStruct : Homogenization.Book.Ch04.RestrictionStructuralLaw P)
    (hP4 : Homogenization.Book.Ch05.QuantitativeCoarseGrainedEllipticity P)
    (m k : ℕ) (_hk_le_m : k ≤ m) (e : Homogenization.Vec d)
    (he : Homogenization.Book.Ch02.vecNorm e = 1) :
    Homogenization.Book.Ch05.tauAtScale P (m : ℤ) (k : ℤ)
      (Homogenization.Book.Ch05.specialPAtScale hP hStruct (m : ℤ) e)
      (Homogenization.Book.Ch05.specialQAtScale hP hStruct (m : ℤ) e) =
    terminalTau
      (Real.sqrt (Homogenization.Book.Ch05.thetaAtScale hP hStruct (m : ℤ)))
      (hP.barSigmaAtScale hStruct (k : ℤ) /
        hP.barSigmaAtScale hStruct (m : ℤ))
      ((hP.barSigmaStarAtScale hStruct (k : ℤ))⁻¹ /
        (hP.barSigmaStarAtScale hStruct (m : ℤ))⁻¹) := by
  have he_sq : Homogenization.vecNormSq e = 1 :=
    Homogenization.Book.Ch05.Section54.GoodScale.vecNormSq_eq_one_of_vecNorm_eq_one
      he
  let p_e := Homogenization.Book.Ch05.specialPAtScale hP hStruct (m : ℤ) e
  let q_e := Homogenization.Book.Ch05.specialQAtScale hP hStruct (m : ℤ) e
  have hBlock_m :
      MeasureTheory.Integrable
        (Homogenization.Book.Ch04.coarseFullBlockMatrixAtCube
          (Homogenization.originCube d (m : ℤ))) P :=
    Homogenization.Book.Ch05.Section52.originBlockIntegrableAtScale_from_P4
      hP hStruct hP4 m
  have hBlock_k :
      MeasureTheory.Integrable
        (Homogenization.Book.Ch04.coarseFullBlockMatrixAtCube
          (Homogenization.originCube d (k : ℤ))) P :=
    Homogenization.Book.Ch05.Section52.originBlockIntegrableAtScale_from_P4
      hP hStruct hP4 k
  have htau :
      Homogenization.Book.Ch05.tauAtScale P (m : ℤ) (k : ℤ) p_e q_e =
        Homogenization.Book.Ch05.tauScalarFormula hP hStruct (m : ℤ) (k : ℤ)
          p_e q_e :=
    Homogenization.Book.Ch05.Section52.tauAtScale_eq_tauScalarFormula
      hP hStruct (m : ℤ) (k : ℤ) p_e q_e hBlock_m hBlock_k
  have hspecial :
      Homogenization.Book.Ch05.tauScalarFormula hP hStruct (m : ℤ) (k : ℤ)
          p_e q_e =
        (1 / 2 : ℝ) *
            (Homogenization.Book.Ch05.sigmaHatAtScale hP hStruct (m : ℤ))⁻¹ *
            (hP.barSigmaAtScale hStruct (k : ℤ) -
              hP.barSigmaAtScale hStruct (m : ℤ)) +
          (1 / 2 : ℝ) *
            Homogenization.Book.Ch05.sigmaHatAtScale hP hStruct (m : ℤ) *
            ((hP.barSigmaStarAtScale hStruct (k : ℤ))⁻¹ -
              (hP.barSigmaStarAtScale hStruct (m : ℤ))⁻¹) := by
    simpa [p_e, q_e] using
      Homogenization.Book.Ch05.Section54.GoodScale.tauScalarFormula_special_eq_of_P4
        hP hStruct hP4 m k e he_sq
  let sigma := Homogenization.Book.Ch05.sigmaHatAtScale hP hStruct (m : ℤ)
  let theta := Homogenization.Book.Ch05.thetaAtScale hP hStruct (m : ℤ)
  let bm := hP.barSigmaAtScale hStruct (m : ℤ)
  let cm := hP.barSigmaStarAtScale hStruct (m : ℤ)
  let bk := hP.barSigmaAtScale hStruct (k : ℤ)
  let ck := hP.barSigmaStarAtScale hStruct (k : ℤ)
  have hbm : 0 < bm := by
    simpa [bm] using
      Homogenization.Book.Ch05.Section54.Pigeonhole.barSigmaAtScale_pos_of_P4
        hP hStruct hP4 m
  have hcm : 0 < cm := by
    simpa [cm] using
      Homogenization.Book.Ch05.Section54.Pigeonhole.barSigmaStarAtScale_pos_of_P4
        hP hStruct hP4 m
  have hck : 0 < ck := by
    simpa [ck] using
      Homogenization.Book.Ch05.Section54.Pigeonhole.barSigmaStarAtScale_pos_of_P4
        hP hStruct hP4 k
  have halg :
      (1 / 2 : ℝ) * sigma⁻¹ * (bk - bm) +
          (1 / 2 : ℝ) * sigma * (ck⁻¹ - cm⁻¹) =
        terminalTau (Real.sqrt theta) (bk / bm) (ck⁻¹ / cm⁻¹) :=
    terminalTau_eq_of_barSigma_ratios hbm hcm hck rfl rfl
  calc
    Homogenization.Book.Ch05.tauAtScale P (m : ℤ) (k : ℤ)
      (Homogenization.Book.Ch05.specialPAtScale hP hStruct (m : ℤ) e)
      (Homogenization.Book.Ch05.specialQAtScale hP hStruct (m : ℤ) e)
        = Homogenization.Book.Ch05.tauAtScale P (m : ℤ) (k : ℤ) p_e q_e := rfl
    _ = Homogenization.Book.Ch05.tauScalarFormula hP hStruct (m : ℤ) (k : ℤ)
          p_e q_e := htau
    _ = (1 / 2 : ℝ) * sigma⁻¹ * (bk - bm) +
          (1 / 2 : ℝ) * sigma * (ck⁻¹ - cm⁻¹) := by
          simpa [sigma, bm, cm, bk, ck] using hspecial
    _ = terminalTau (Real.sqrt theta) (bk / bm) (ck⁻¹ / cm⁻¹) := halg
    _ = terminalTau
      (Real.sqrt (Homogenization.Book.Ch05.thetaAtScale hP hStruct (m : ℤ)))
      (hP.barSigmaAtScale hStruct (k : ℤ) /
        hP.barSigmaAtScale hStruct (m : ℤ))
      ((hP.barSigmaStarAtScale hStruct (k : ℤ))⁻¹ /
        (hP.barSigmaStarAtScale hStruct (m : ℤ))⁻¹) := by
        rfl

/--
Source label `l.union.bound`: the library's Section 52 scalar preliminaries compare the
scale-`m` scalar contrast to the corrected note's initial budget
`T = widetildeTheta_0`.
-/
theorem thetaAtScale_le_initialWidetildeTheta_of_P4
    {d : ℕ} [NeZero d] {P : Homogenization.Book.Ch04.RestrictionCoeffLaw d}
    (hP : Homogenization.Book.Ch04.RestrictionLawCarrier P)
    (hStruct : Homogenization.Book.Ch04.RestrictionStructuralLaw P)
    (hP4 : Homogenization.Book.Ch05.QuantitativeCoarseGrainedEllipticity P)
    (m : ℕ) :
    Homogenization.Book.Ch05.thetaAtScale hP hStruct (m : ℤ) ≤
      Homogenization.Book.Ch05.widetildeThetaAtScale P (0 : ℤ) hP4 := by
  have hprelim :=
    Homogenization.Book.Ch05.Section52.scalarPreliminaries_homogenizationScale
      hP hStruct hP4 (n := 0) (m := m) (k := 0) (p := 0) (q := 0)
      (Nat.zero_le m) (Nat.zero_le 0)
  exact hprelim.2.1.trans hprelim.2.2.1

/--
Source label `l.union.bound`: the corrected initial contrast budget
`T = widetildeTheta_0` is at least one under `(P4)`.
-/
theorem one_le_initialWidetildeTheta_of_P4
    {d : ℕ} [NeZero d] {P : Homogenization.Book.Ch04.RestrictionCoeffLaw d}
    (hP : Homogenization.Book.Ch04.RestrictionLawCarrier P)
    (hStruct : Homogenization.Book.Ch04.RestrictionStructuralLaw P)
    (hP4 : Homogenization.Book.Ch05.QuantitativeCoarseGrainedEllipticity P) :
    1 ≤ Homogenization.Book.Ch05.widetildeThetaAtScale P (0 : ℤ) hP4 := by
  have htheta :
      1 ≤ Homogenization.Book.Ch05.thetaAtScale hP hStruct (0 : ℤ) :=
    Homogenization.Book.Ch05.Section54.GoodScale.one_le_thetaAtScale_of_P4
      hP hStruct hP4 0
  exact htheta.trans (thetaAtScale_le_initialWidetildeTheta_of_P4 hP hStruct hP4 0)

/-- Source label `e.F.drop`: `F_m = Theta_m - 1` is nonnegative under `(P4)`. -/
theorem contrastExcessAtScale_nonneg_of_P4
    {d : ℕ} [NeZero d] {P : Homogenization.Book.Ch04.RestrictionCoeffLaw d}
    (hP : Homogenization.Book.Ch04.RestrictionLawCarrier P)
    (hStruct : Homogenization.Book.Ch04.RestrictionStructuralLaw P)
    (hP4 : Homogenization.Book.Ch05.QuantitativeCoarseGrainedEllipticity P)
    (m : ℕ) :
    0 ≤ contrastExcessAtScale hP hStruct m := by
  have htheta :
      1 ≤ Homogenization.Book.Ch05.thetaAtScale hP hStruct (m : ℤ) :=
    Homogenization.Book.Ch05.Section54.GoodScale.one_le_thetaAtScale_of_P4
      hP hStruct hP4 m
  change 0 ≤ Homogenization.Book.Ch05.thetaAtScale hP hStruct (m : ℤ) - 1
  linarith

/--
Source label `l.det.memory`: the manuscript contrast sequence
`F_m = Theta_m - 1` is nonincreasing in the scale.
-/
theorem contrastExcessAtScale_antitone_of_P4
    {d : ℕ} [NeZero d] {P : Homogenization.Book.Ch04.RestrictionCoeffLaw d}
    (hP : Homogenization.Book.Ch04.RestrictionLawCarrier P)
    (hStruct : Homogenization.Book.Ch04.RestrictionStructuralLaw P)
    (hP4 : Homogenization.Book.Ch05.QuantitativeCoarseGrainedEllipticity P) :
    Antitone fun m : ℕ => contrastExcessAtScale hP hStruct m := by
  intro j m hjm
  have htheta :
      Homogenization.Book.Ch05.thetaAtScale hP hStruct (m : ℤ) ≤
        Homogenization.Book.Ch05.thetaAtScale hP hStruct (j : ℤ) :=
    Homogenization.Book.Ch05.Section54.GoodScale.thetaAtScale_mono_of_P4
      hP hStruct hP4 (n := j) (m := m) hjm
  change
    Homogenization.Book.Ch05.thetaAtScale hP hStruct (m : ℤ) - 1 ≤
      Homogenization.Book.Ch05.thetaAtScale hP hStruct (j : ℤ) - 1
  linarith

/--
Source label `l.union.bound`: real algebra for the product of the two scalar
normalization ratios.  In source notation this is
`a_{j,m} b_{j,m} = Theta_j / Theta_m`.
-/
theorem terminalScalarRatioProduct_eq_theta_ratio
    {barSigma_j barSigma_m barSigmaStar_j barSigmaStar_m : ℝ}
    (hbarSigma_m : barSigma_m ≠ 0)
    (hbarSigmaStar_j : barSigmaStar_j ≠ 0)
    (hbarSigmaStar_m : barSigmaStar_m ≠ 0) :
    (barSigma_j / barSigma_m) *
        (barSigmaStar_j⁻¹ / barSigmaStar_m⁻¹) =
      (barSigma_j * barSigmaStar_j⁻¹) /
        (barSigma_m * barSigmaStar_m⁻¹) := by
  field_simp [hbarSigma_m, hbarSigmaStar_j, hbarSigmaStar_m]

/--
Source label `l.union.bound`: for `j <= m`, the product of the upper and
inverse-star scalar normalization ratios is controlled by the corrected initial
budget `T = widetildeTheta_0`.
-/
theorem terminalScalarRatioProduct_le_initialWidetildeTheta_of_P4
    {d : ℕ} [NeZero d] {P : Homogenization.Book.Ch04.RestrictionCoeffLaw d}
    (hP : Homogenization.Book.Ch04.RestrictionLawCarrier P)
    (hStruct : Homogenization.Book.Ch04.RestrictionStructuralLaw P)
    (hP4 : Homogenization.Book.Ch05.QuantitativeCoarseGrainedEllipticity P)
    {j m : ℕ} (_hjm : j ≤ m) :
    (hP.barSigmaAtScale hStruct (j : ℤ) /
        hP.barSigmaAtScale hStruct (m : ℤ)) *
      ((hP.barSigmaStarAtScale hStruct (j : ℤ))⁻¹ /
        (hP.barSigmaStarAtScale hStruct (m : ℤ))⁻¹) ≤
      Homogenization.Book.Ch05.widetildeThetaAtScale P (0 : ℤ) hP4 := by
  let theta_j := Homogenization.Book.Ch05.thetaAtScale hP hStruct (j : ℤ)
  let theta_m := Homogenization.Book.Ch05.thetaAtScale hP hStruct (m : ℤ)
  have hbm_pos :
      0 < hP.barSigmaAtScale hStruct (m : ℤ) :=
    Homogenization.Book.Ch05.Section54.Pigeonhole.barSigmaAtScale_pos_of_P4
      hP hStruct hP4 m
  have hcj_pos :
      0 < hP.barSigmaStarAtScale hStruct (j : ℤ) :=
    Homogenization.Book.Ch05.Section54.Pigeonhole.barSigmaStarAtScale_pos_of_P4
      hP hStruct hP4 j
  have hcm_pos :
      0 < hP.barSigmaStarAtScale hStruct (m : ℤ) :=
    Homogenization.Book.Ch05.Section54.Pigeonhole.barSigmaStarAtScale_pos_of_P4
      hP hStruct hP4 m
  have htheta_m_one : 1 ≤ theta_m := by
    simpa [theta_m] using
      Homogenization.Book.Ch05.Section54.GoodScale.one_le_thetaAtScale_of_P4
        hP hStruct hP4 m
  have htheta_j_nonneg : 0 ≤ theta_j := by
    have htheta_j_one :
        1 ≤ theta_j := by
      simpa [theta_j] using
        Homogenization.Book.Ch05.Section54.GoodScale.one_le_thetaAtScale_of_P4
          hP hStruct hP4 j
    linarith
  have htheta_m_pos : 0 < theta_m := by linarith
  have htheta_j_le_T :
      theta_j ≤ Homogenization.Book.Ch05.widetildeThetaAtScale P (0 : ℤ) hP4 := by
    simpa [theta_j] using
      thetaAtScale_le_initialWidetildeTheta_of_P4 hP hStruct hP4 j
  have hratio_le_theta_j : theta_j / theta_m ≤ theta_j := by
    rw [div_le_iff₀ htheta_m_pos]
    nlinarith
  have hprod_eq :
      (hP.barSigmaAtScale hStruct (j : ℤ) /
          hP.barSigmaAtScale hStruct (m : ℤ)) *
        ((hP.barSigmaStarAtScale hStruct (j : ℤ))⁻¹ /
          (hP.barSigmaStarAtScale hStruct (m : ℤ))⁻¹) =
        theta_j / theta_m := by
    rw [terminalScalarRatioProduct_eq_theta_ratio
      (ne_of_gt hbm_pos) (ne_of_gt hcj_pos) (ne_of_gt hcm_pos)]
    rfl
  rw [hprod_eq]
  exact hratio_le_theta_j.trans htheta_j_le_T

/--
Source label `l.union.bound`: the upper scalar block of the terminal/intermediate
normalization change is controlled by the initial budget
`T = widetildeTheta_0`.
-/
theorem terminalUpperScalarRatio_le_initialWidetildeTheta_of_P4
    {d : ℕ} [NeZero d] {P : Homogenization.Book.Ch04.RestrictionCoeffLaw d}
    (hP : Homogenization.Book.Ch04.RestrictionLawCarrier P)
    (hStruct : Homogenization.Book.Ch04.RestrictionStructuralLaw P)
    (hP4 : Homogenization.Book.Ch05.QuantitativeCoarseGrainedEllipticity P)
    {j m : ℕ} (hjm : j ≤ m) :
    hP.barSigmaAtScale hStruct (j : ℤ) /
        hP.barSigmaAtScale hStruct (m : ℤ) ≤
      Homogenization.Book.Ch05.widetildeThetaAtScale P (0 : ℤ) hP4 := by
  let upper :=
    hP.barSigmaAtScale hStruct (j : ℤ) /
      hP.barSigmaAtScale hStruct (m : ℤ)
  let lower :=
    (hP.barSigmaStarAtScale hStruct (j : ℤ))⁻¹ /
      (hP.barSigmaStarAtScale hStruct (m : ℤ))⁻¹
  have hchain :=
    Homogenization.Book.Ch05.Section54.Pigeonhole.scalarChain_of_P4
      hP hStruct hP4 hjm
  have hbm_pos :
      0 < hP.barSigmaAtScale hStruct (m : ℤ) :=
    Homogenization.Book.Ch05.Section54.Pigeonhole.barSigmaAtScale_pos_of_P4
      hP hStruct hP4 m
  have hcm_inv_pos :
      0 < (hP.barSigmaStarAtScale hStruct (m : ℤ))⁻¹ :=
    Homogenization.Book.Ch05.Section54.Pigeonhole.barSigmaStarAtScale_inv_pos_of_P4
      hP hStruct hP4 m
  have hupper_ge_one : 1 ≤ upper := by
    rw [show upper =
        hP.barSigmaAtScale hStruct (j : ℤ) /
          hP.barSigmaAtScale hStruct (m : ℤ) by rfl]
    rw [le_div_iff₀ hbm_pos]
    simpa using hchain.2.2
  have hlower_ge_one : 1 ≤ lower := by
    rw [show lower =
        (hP.barSigmaStarAtScale hStruct (j : ℤ))⁻¹ /
          (hP.barSigmaStarAtScale hStruct (m : ℤ))⁻¹ by rfl]
    rw [le_div_iff₀ hcm_inv_pos]
    simpa using hchain.2.1
  have hupper_le_product : upper ≤ upper * lower := by
    have hupper_nonneg : 0 ≤ upper := le_trans zero_le_one hupper_ge_one
    simpa [one_mul] using
      mul_le_mul_of_nonneg_left hlower_ge_one hupper_nonneg
  have hproduct :
      upper * lower ≤
        Homogenization.Book.Ch05.widetildeThetaAtScale P (0 : ℤ) hP4 := by
    simpa [upper, lower] using
      terminalScalarRatioProduct_le_initialWidetildeTheta_of_P4
        hP hStruct hP4 hjm
  exact hupper_le_product.trans hproduct

/--
Source label `l.union.bound`: the inverse-star scalar block of the
terminal/intermediate normalization change is controlled by the initial budget
`T = widetildeTheta_0`.
-/
theorem terminalInvStarScalarRatio_le_initialWidetildeTheta_of_P4
    {d : ℕ} [NeZero d] {P : Homogenization.Book.Ch04.RestrictionCoeffLaw d}
    (hP : Homogenization.Book.Ch04.RestrictionLawCarrier P)
    (hStruct : Homogenization.Book.Ch04.RestrictionStructuralLaw P)
    (hP4 : Homogenization.Book.Ch05.QuantitativeCoarseGrainedEllipticity P)
    {j m : ℕ} (hjm : j ≤ m) :
    (hP.barSigmaStarAtScale hStruct (j : ℤ))⁻¹ /
        (hP.barSigmaStarAtScale hStruct (m : ℤ))⁻¹ ≤
      Homogenization.Book.Ch05.widetildeThetaAtScale P (0 : ℤ) hP4 := by
  let upper :=
    hP.barSigmaAtScale hStruct (j : ℤ) /
      hP.barSigmaAtScale hStruct (m : ℤ)
  let lower :=
    (hP.barSigmaStarAtScale hStruct (j : ℤ))⁻¹ /
      (hP.barSigmaStarAtScale hStruct (m : ℤ))⁻¹
  have hchain :=
    Homogenization.Book.Ch05.Section54.Pigeonhole.scalarChain_of_P4
      hP hStruct hP4 hjm
  have hbm_pos :
      0 < hP.barSigmaAtScale hStruct (m : ℤ) :=
    Homogenization.Book.Ch05.Section54.Pigeonhole.barSigmaAtScale_pos_of_P4
      hP hStruct hP4 m
  have hcm_inv_pos :
      0 < (hP.barSigmaStarAtScale hStruct (m : ℤ))⁻¹ :=
    Homogenization.Book.Ch05.Section54.Pigeonhole.barSigmaStarAtScale_inv_pos_of_P4
      hP hStruct hP4 m
  have hupper_ge_one : 1 ≤ upper := by
    rw [show upper =
        hP.barSigmaAtScale hStruct (j : ℤ) /
          hP.barSigmaAtScale hStruct (m : ℤ) by rfl]
    rw [le_div_iff₀ hbm_pos]
    simpa using hchain.2.2
  have hlower_ge_one : 1 ≤ lower := by
    rw [show lower =
        (hP.barSigmaStarAtScale hStruct (j : ℤ))⁻¹ /
          (hP.barSigmaStarAtScale hStruct (m : ℤ))⁻¹ by rfl]
    rw [le_div_iff₀ hcm_inv_pos]
    simpa using hchain.2.1
  have hlower_le_product : lower ≤ upper * lower := by
    have hlower_nonneg : 0 ≤ lower := le_trans zero_le_one hlower_ge_one
    simpa [mul_comm, one_mul] using
      mul_le_mul_of_nonneg_right hupper_ge_one hlower_nonneg
  have hproduct :
      upper * lower ≤
        Homogenization.Book.Ch05.widetildeThetaAtScale P (0 : ℤ) hP4 := by
    simpa [upper, lower] using
      terminalScalarRatioProduct_le_initialWidetildeTheta_of_P4
        hP hStruct hP4 hjm
  exact hlower_le_product.trans hproduct

/-- Source label `e.nodrop`: unfolding the no-drop condition. -/
@[simp]
theorem no_drop_window_iff (rho F_k F_m : ℝ) :
    noDropWindow rho F_k F_m ↔ F_k - F_m ≤ rho * F_m :=
  Iff.rfl

/--
Source label `e.rtau.drop`: if `a,b ≥ 1`, the terminal additivity defect is
absorbed by half of the deterministic contrast drop.
-/
theorem rtau_drop (r_m a b : ℝ) (ha : 1 ≤ a) (hb : 1 ≤ b) :
    r_m * terminalTau r_m a b ≤ (1 / 2 : ℝ) * contrastDrop r_m a b := by
  have hprod_nonneg : 0 ≤ (a - 1) * (b - 1) :=
    mul_nonneg (sub_nonneg.mpr ha) (sub_nonneg.mpr hb)
  have hsquare_nonneg : 0 ≤ r_m ^ 2 := sq_nonneg r_m
  have hmain : 0 ≤ r_m ^ 2 * ((a - 1) * (b - 1)) :=
    mul_nonneg hsquare_nonneg hprod_nonneg
  rw [contrastDrop, terminalTau]
  nlinarith

/--
Source label `e.rtau.drop`: formula-facing version using explicit contrast and
terminal-tau hypotheses.
-/
theorem rtau_drop_of_eq {r_m a b F_j F_m tau : ℝ}
    (hF : F_j - F_m = contrastDrop r_m a b)
    (htau : tau = terminalTau r_m a b)
    (ha : 1 ≤ a) (hb : 1 ≤ b) :
    r_m * tau ≤ (1 / 2 : ℝ) * (F_j - F_m) := by
  rw [htau, hF]
  exact rtau_drop r_m a b ha hb

/--
Source label `e.rtau.drop`: library-facing terminal-pair version.  The special
vectors `p_e,q_e` identify `tauAtScale` with the terminal scalar `tau`, and the
contrast excesses give the deterministic drop `F_j - F_m`.
-/
theorem sqrt_contrastExcess_mul_tauAtScale_special_le_half_contrastExcess_drop_of_P4
    {d : ℕ} [NeZero d] {P : Homogenization.Book.Ch04.RestrictionCoeffLaw d}
    (hP : Homogenization.Book.Ch04.RestrictionLawCarrier P)
    (hStruct : Homogenization.Book.Ch04.RestrictionStructuralLaw P)
    (hP4 : Homogenization.Book.Ch05.QuantitativeCoarseGrainedEllipticity P)
    {j m : ℕ} (hjm : j ≤ m) (e : Homogenization.Vec d)
    (he : Homogenization.Book.Ch02.vecNorm e = 1) :
    Real.sqrt (1 + contrastExcessAtScale hP hStruct m) *
        Homogenization.Book.Ch05.tauAtScale P (m : ℤ) (j : ℤ)
          (Homogenization.Book.Ch05.specialPAtScale hP hStruct (m : ℤ) e)
          (Homogenization.Book.Ch05.specialQAtScale hP hStruct (m : ℤ) e) ≤
      (1 / 2 : ℝ) *
        (contrastExcessAtScale hP hStruct j -
          contrastExcessAtScale hP hStruct m) := by
  let r_m : ℝ := Real.sqrt (1 + contrastExcessAtScale hP hStruct m)
  let a : ℝ :=
    hP.barSigmaAtScale hStruct (j : ℤ) /
      hP.barSigmaAtScale hStruct (m : ℤ)
  let b : ℝ :=
    (hP.barSigmaStarAtScale hStruct (j : ℤ))⁻¹ /
      (hP.barSigmaStarAtScale hStruct (m : ℤ))⁻¹
  let theta_j := Homogenization.Book.Ch05.thetaAtScale hP hStruct (j : ℤ)
  let theta_m := Homogenization.Book.Ch05.thetaAtScale hP hStruct (m : ℤ)
  let tau : ℝ :=
    Homogenization.Book.Ch05.tauAtScale P (m : ℤ) (j : ℤ)
      (Homogenization.Book.Ch05.specialPAtScale hP hStruct (m : ℤ) e)
      (Homogenization.Book.Ch05.specialQAtScale hP hStruct (m : ℤ) e)
  have hchain :=
    Homogenization.Book.Ch05.Section54.Pigeonhole.scalarChain_of_P4
      hP hStruct hP4 hjm
  have hbm_pos :
      0 < hP.barSigmaAtScale hStruct (m : ℤ) :=
    Homogenization.Book.Ch05.Section54.Pigeonhole.barSigmaAtScale_pos_of_P4
      hP hStruct hP4 m
  have hcj_pos :
      0 < hP.barSigmaStarAtScale hStruct (j : ℤ) :=
    Homogenization.Book.Ch05.Section54.Pigeonhole.barSigmaStarAtScale_pos_of_P4
      hP hStruct hP4 j
  have hcm_pos :
      0 < hP.barSigmaStarAtScale hStruct (m : ℤ) :=
    Homogenization.Book.Ch05.Section54.Pigeonhole.barSigmaStarAtScale_pos_of_P4
      hP hStruct hP4 m
  have hcm_inv_pos :
      0 < (hP.barSigmaStarAtScale hStruct (m : ℤ))⁻¹ :=
    inv_pos.mpr hcm_pos
  have htheta_m_one : 1 ≤ theta_m := by
    simpa [theta_m] using
      Homogenization.Book.Ch05.Section54.GoodScale.one_le_thetaAtScale_of_P4
        hP hStruct hP4 m
  have htheta_m_pos : 0 < theta_m := by linarith
  have ha : 1 ≤ a := by
    dsimp [a]
    rw [le_div_iff₀ hbm_pos]
    simpa using hchain.2.2
  have hb : 1 ≤ b := by
    dsimp [b]
    rw [le_div_iff₀ hcm_inv_pos]
    simpa using hchain.2.1
  have hr_sq : r_m ^ 2 = theta_m := by
    have harg_nonneg : 0 ≤ 1 + contrastExcessAtScale hP hStruct m := by
      have harg_eq :
          1 + contrastExcessAtScale hP hStruct m = theta_m := by
        dsimp [contrastExcessAtScale, theta_m]
        ring
      rw [harg_eq]
      exact le_of_lt htheta_m_pos
    dsimp [r_m]
    rw [Real.sq_sqrt harg_nonneg]
    dsimp [contrastExcessAtScale, theta_m]
    ring
  have hprod_eq : a * b = theta_j / theta_m := by
    dsimp [a, b, theta_j, theta_m]
    rw [terminalScalarRatioProduct_eq_theta_ratio
      (ne_of_gt hbm_pos) (ne_of_gt hcj_pos) (ne_of_gt hcm_pos)]
    rfl
  have hF :
      contrastExcessAtScale hP hStruct j -
          contrastExcessAtScale hP hStruct m =
        contrastDrop r_m a b := by
    calc
      contrastExcessAtScale hP hStruct j -
          contrastExcessAtScale hP hStruct m
          = theta_j - theta_m := by
            dsimp [contrastExcessAtScale, theta_j, theta_m]
            ring
      _ = theta_m * (theta_j / theta_m - 1) := by
            field_simp [ne_of_gt htheta_m_pos]
      _ = r_m ^ 2 * (a * b - 1) := by
            rw [hr_sq, hprod_eq]
      _ = contrastDrop r_m a b := rfl
  have hr_eq :
      Real.sqrt (Homogenization.Book.Ch05.thetaAtScale hP hStruct (m : ℤ)) =
        r_m := by
    dsimp [r_m, contrastExcessAtScale]
    congr 1
    ring
  have htau0 :=
    tauAtScale_special_eq_terminalTau_of_P4 hP hStruct hP4 m j hjm e he
  have htau : tau = terminalTau r_m a b := by
    calc
      tau =
          Homogenization.Book.Ch05.tauAtScale P (m : ℤ) (j : ℤ)
            (Homogenization.Book.Ch05.specialPAtScale hP hStruct (m : ℤ) e)
            (Homogenization.Book.Ch05.specialQAtScale hP hStruct (m : ℤ) e) := rfl
      _ = terminalTau
            (Real.sqrt
              (Homogenization.Book.Ch05.thetaAtScale hP hStruct (m : ℤ)))
            a b := by
            simpa [a, b] using htau0
      _ = terminalTau r_m a b := by rw [hr_eq]
  have hbase :
      r_m * tau ≤
        (1 / 2 : ℝ) *
          (contrastExcessAtScale hP hStruct j -
            contrastExcessAtScale hP hStruct m) :=
    rtau_drop_of_eq hF htau ha hb
  simpa [r_m, tau] using hbase

/--
Source label `e.sqrt.tau.absorb`: library-facing formula for the lower-scale
expected response of the special terminal pair.
-/
theorem expectedResponseJCubeSet_special_eq_half_terminalP_sub_one_of_P4
    {d : ℕ} [NeZero d] {P : Homogenization.Book.Ch04.RestrictionCoeffLaw d}
    (hP : Homogenization.Book.Ch04.RestrictionLawCarrier P)
    (hStruct : Homogenization.Book.Ch04.RestrictionStructuralLaw P)
    (hP4 : Homogenization.Book.Ch05.QuantitativeCoarseGrainedEllipticity P)
    (m k : ℕ) (e : Homogenization.Vec d)
    (he : Homogenization.Book.Ch02.vecNorm e = 1) :
    Homogenization.Book.Ch04.expectedResponseJCubeSet P
        (Homogenization.originCube d (k : ℤ))
        (Homogenization.Book.Ch05.specialPAtScale hP hStruct (m : ℤ) e)
        (Homogenization.Book.Ch05.specialQAtScale hP hStruct (m : ℤ) e) =
      (1 / 2 : ℝ) *
        terminalP
          (Real.sqrt (Homogenization.Book.Ch05.thetaAtScale hP hStruct (m : ℤ)))
          (hP.barSigmaAtScale hStruct (k : ℤ) /
            hP.barSigmaAtScale hStruct (m : ℤ))
          ((hP.barSigmaStarAtScale hStruct (k : ℤ))⁻¹ /
            (hP.barSigmaStarAtScale hStruct (m : ℤ))⁻¹) - 1 := by
  have he_sq : Homogenization.vecNormSq e = 1 :=
    Homogenization.Book.Ch05.Section54.GoodScale.vecNormSq_eq_one_of_vecNorm_eq_one
      he
  let p_e := Homogenization.Book.Ch05.specialPAtScale hP hStruct (m : ℤ) e
  let q_e := Homogenization.Book.Ch05.specialQAtScale hP hStruct (m : ℤ) e
  have hBlock_k :
      MeasureTheory.Integrable
        (Homogenization.Book.Ch04.coarseFullBlockMatrixAtCube
          (Homogenization.originCube d (k : ℤ))) P :=
    Homogenization.Book.Ch05.Section52.originBlockIntegrableAtScale_from_P4
      hP hStruct hP4 k
  have hresp :
      Homogenization.Book.Ch04.expectedResponseJCubeSet P
          (Homogenization.originCube d (k : ℤ)) p_e q_e =
        Homogenization.Book.Ch05.expectedJScalarFormula hP hStruct (k : ℤ)
          p_e q_e := by
    have h :=
      Homogenization.Book.Ch05.Section52.annealedResponseJAtScale_eq_expectedJScalarFormula
        hP hStruct (k : ℤ) p_e q_e hBlock_k
    simpa [Homogenization.Book.Ch04.expectedResponseJCubeSet,
      Homogenization.Book.Ch04.annealedResponseJAtScale,
      Homogenization.Book.Ch04.responseJAtScale,
      Homogenization.Book.Ch04.restrictionResponseJObservableCubeSet] using h
  have hspecial :
      Homogenization.Book.Ch05.expectedJScalarFormula hP hStruct (k : ℤ)
          p_e q_e =
        (1 / 2 : ℝ) *
            (Homogenization.Book.Ch05.sigmaHatAtScale hP hStruct (m : ℤ))⁻¹ *
            hP.barSigmaAtScale hStruct (k : ℤ) +
          (1 / 2 : ℝ) *
            Homogenization.Book.Ch05.sigmaHatAtScale hP hStruct (m : ℤ) *
            (hP.barSigmaStarAtScale hStruct (k : ℤ))⁻¹ - 1 := by
    simpa [p_e, q_e] using
      Homogenization.Book.Ch05.Section54.GoodScale.expectedJScalarFormula_special_eq_of_P4
        hP hStruct hP4 m k e he_sq
  let sigma := Homogenization.Book.Ch05.sigmaHatAtScale hP hStruct (m : ℤ)
  let theta := Homogenization.Book.Ch05.thetaAtScale hP hStruct (m : ℤ)
  let bm := hP.barSigmaAtScale hStruct (m : ℤ)
  let cm := hP.barSigmaStarAtScale hStruct (m : ℤ)
  let bk := hP.barSigmaAtScale hStruct (k : ℤ)
  let ck := hP.barSigmaStarAtScale hStruct (k : ℤ)
  have hbm : 0 < bm := by
    simpa [bm] using
      Homogenization.Book.Ch05.Section54.Pigeonhole.barSigmaAtScale_pos_of_P4
        hP hStruct hP4 m
  have hcm : 0 < cm := by
    simpa [cm] using
      Homogenization.Book.Ch05.Section54.Pigeonhole.barSigmaStarAtScale_pos_of_P4
        hP hStruct hP4 m
  have hck : 0 < ck := by
    simpa [ck] using
      Homogenization.Book.Ch05.Section54.Pigeonhole.barSigmaStarAtScale_pos_of_P4
        hP hStruct hP4 k
  have halg :
      (1 / 2 : ℝ) * sigma⁻¹ * bk + (1 / 2 : ℝ) * sigma * ck⁻¹ - 1 =
        (1 / 2 : ℝ) *
            terminalP (Real.sqrt theta) (bk / bm) (ck⁻¹ / cm⁻¹) - 1 :=
    half_terminalP_sub_one_eq_of_barSigma_ratios hbm hcm hck rfl rfl
  calc
    Homogenization.Book.Ch04.expectedResponseJCubeSet P
        (Homogenization.originCube d (k : ℤ))
        (Homogenization.Book.Ch05.specialPAtScale hP hStruct (m : ℤ) e)
        (Homogenization.Book.Ch05.specialQAtScale hP hStruct (m : ℤ) e)
        = Homogenization.Book.Ch04.expectedResponseJCubeSet P
            (Homogenization.originCube d (k : ℤ)) p_e q_e := rfl
    _ = Homogenization.Book.Ch05.expectedJScalarFormula hP hStruct (k : ℤ)
          p_e q_e := hresp
    _ = (1 / 2 : ℝ) * sigma⁻¹ * bk + (1 / 2 : ℝ) * sigma * ck⁻¹ - 1 := by
          simpa [sigma, bk, ck] using hspecial
    _ = (1 / 2 : ℝ) *
            terminalP (Real.sqrt theta) (bk / bm) (ck⁻¹ / cm⁻¹) - 1 := halg
    _ = (1 / 2 : ℝ) *
        terminalP
          (Real.sqrt (Homogenization.Book.Ch05.thetaAtScale hP hStruct (m : ℤ)))
          (hP.barSigmaAtScale hStruct (k : ℤ) /
            hP.barSigmaAtScale hStruct (m : ℤ))
          ((hP.barSigmaStarAtScale hStruct (k : ℤ))⁻¹ /
            (hP.barSigmaStarAtScale hStruct (m : ℤ))⁻¹) - 1 := by
          rfl

/--
Source label `e.no.drop.ab`: on a no-drop window, the product excess satisfies
`a * b ≤ 1 + rho`.
-/
theorem mul_le_one_add_rho_of_no_drop {r_m a b F_j F_k F_m rho : ℝ}
    (hno : noDropWindow rho F_k F_m)
    (hj_le_k : F_j - F_m ≤ F_k - F_m)
    (hF : F_j - F_m = contrastDrop r_m a b)
    (hFm_le_sq : F_m ≤ r_m ^ 2)
    (hr_sq_pos : 0 < r_m ^ 2)
    (hrho_pos : 0 < rho) :
    a * b ≤ 1 + rho := by
  have hdrop_le : contrastDrop r_m a b ≤ rho * F_m := by
    rw [← hF]
    exact le_trans hj_le_k hno
  have hrho_nonneg : 0 ≤ rho := le_of_lt hrho_pos
  have hscale_le : rho * F_m ≤ rho * r_m ^ 2 :=
    mul_le_mul_of_nonneg_left hFm_le_sq hrho_nonneg
  have hcontrast_le : contrastDrop r_m a b ≤ rho * r_m ^ 2 :=
    le_trans hdrop_le hscale_le
  have hmul :
      (a * b - 1) * r_m ^ 2 ≤ rho * r_m ^ 2 := by
    simpa [contrastDrop, mul_comm, mul_left_comm, mul_assoc] using hcontrast_le
  have hab_minus_le : a * b - 1 ≤ rho :=
    le_of_mul_le_mul_right hmul hr_sq_pos
  linarith

/--
Source label `e.no.drop.ab`: on a no-drop window, scalar terminal ratios stay
between `1` and `1 + rho`.
-/
theorem no_drop_ab_bounds {r_m a b F_j F_k F_m rho : ℝ}
    (hno : noDropWindow rho F_k F_m)
    (hj_le_k : F_j - F_m ≤ F_k - F_m)
    (hF : F_j - F_m = contrastDrop r_m a b)
    (hFm_le_sq : F_m ≤ r_m ^ 2)
    (hr_sq_pos : 0 < r_m ^ 2)
    (hrho_pos : 0 < rho)
    (ha : 1 ≤ a) (hb : 1 ≤ b) :
    1 ≤ a ∧ a ≤ 1 + rho ∧ 1 ≤ b ∧ b ≤ 1 + rho := by
  have hab : a * b ≤ 1 + rho :=
    mul_le_one_add_rho_of_no_drop hno hj_le_k hF hFm_le_sq hr_sq_pos hrho_pos
  have ha_nonneg : 0 ≤ a := le_trans zero_le_one ha
  have hb_nonneg : 0 ≤ b := le_trans zero_le_one hb
  have ha_le_mul : a ≤ a * b := by
    have h := mul_le_mul_of_nonneg_left hb ha_nonneg
    simpa using h
  have hb_le_mul : b ≤ a * b := by
    have h := mul_le_mul_of_nonneg_right ha hb_nonneg
    simpa [one_mul] using h
  exact ⟨ha, le_trans ha_le_mul hab, hb, le_trans hb_le_mul hab⟩

end Homogenization.HighContrast.EntryScale
