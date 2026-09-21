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
import LeanPool.CoarseGraining.Homogenization.HighContrast.EntryScale.Inputs
import LeanPool.CoarseGraining.Homogenization.HighContrast.EntryScale.DeterministicAlgebra.P1
import LeanPool.CoarseGraining.Homogenization.HighContrast.EntryScale.DeterministicAlgebra.P2

/-! # P3 -/

open scoped BigOperators Matrix.Norms.Elementwise
open scoped Matrix.Norms.L2Operator

namespace Homogenization.HighContrast.EntryScale

/--
Source label `l.union.bound`: `ENNReal` form of the terminal/intermediate
normalization comparison, ready to combine with the high-moment envelope.
-/
theorem ofReal_fullBlockOperatorNorm_terminalNormalizedCenteredFullBlock_le_initialWidetildeTheta_mul_intermediate_of_P4
    {d : ℕ} [NeZero d] {P : Homogenization.Book.Ch04.RestrictionCoeffLaw d}
    (hP : Homogenization.Book.Ch04.RestrictionLawCarrier P)
    (hStruct : Homogenization.Book.Ch04.RestrictionStructuralLaw P)
    (hP4 : Homogenization.Book.Ch05.QuantitativeCoarseGrainedEllipticity P)
    {j m : ℕ} (hjm : j ≤ m) (Y : Homogenization.FullBlockMat d) :
    ENNReal.ofReal
        (fullBlockOperatorNorm
          (scalarFullBlockNormalizerMatrixAtScale hP hStruct m *
            scalarCenteredFullBlockMatrixAtScale hP hStruct j Y *
            scalarFullBlockNormalizerMatrixAtScale hP hStruct m)) ≤
      ENNReal.ofReal
          (Homogenization.Book.Ch05.widetildeThetaAtScale P (0 : ℤ) hP4) *
        ENNReal.ofReal
          (fullBlockOperatorNorm
            (scalarFullBlockNormalizerMatrixAtScale hP hStruct j *
              scalarCenteredFullBlockMatrixAtScale hP hStruct j Y *
              scalarFullBlockNormalizerMatrixAtScale hP hStruct j)) := by
  let T := Homogenization.Book.Ch05.widetildeThetaAtScale P (0 : ℤ) hP4
  let terminalNorm : ℝ :=
    fullBlockOperatorNorm
      (scalarFullBlockNormalizerMatrixAtScale hP hStruct m *
        scalarCenteredFullBlockMatrixAtScale hP hStruct j Y *
        scalarFullBlockNormalizerMatrixAtScale hP hStruct m)
  let intermediateNorm : ℝ :=
    fullBlockOperatorNorm
      (scalarFullBlockNormalizerMatrixAtScale hP hStruct j *
        scalarCenteredFullBlockMatrixAtScale hP hStruct j Y *
        scalarFullBlockNormalizerMatrixAtScale hP hStruct j)
  have hT_nonneg : 0 ≤ T := by
    have hT_one : 1 ≤ T := by
      simpa [T] using one_le_initialWidetildeTheta_of_P4 hP hStruct hP4
    linarith
  have hreal : terminalNorm ≤ T * intermediateNorm := by
    simpa [terminalNorm, intermediateNorm, T] using
      fullBlockOperatorNorm_terminalNormalizedCenteredFullBlock_le_initialWidetildeTheta_mul_intermediate_of_P4
        hP hStruct hP4 hjm Y
  calc
    ENNReal.ofReal terminalNorm ≤ ENNReal.ofReal (T * intermediateNorm) :=
      ENNReal.ofReal_le_ofReal hreal
    _ = ENNReal.ofReal T * ENNReal.ofReal intermediateNorm := by
      rw [ENNReal.ofReal_mul hT_nonneg]

/--
Source label `a.HM`: concrete intermediate-scale centered full-block deviation.
The matrix argument `Y j Q ω` is the full-block coarse coefficient matrix
attached to the cube `Q`; the normalization and centering are both at scale `j`.
-/
noncomputable def intermediateCenteredFullBlockDeviation
    {Ω : Type*} {d : ℕ} [NeZero d]
    {P : Homogenization.Book.Ch04.RestrictionCoeffLaw d}
    (hP : Homogenization.Book.Ch04.RestrictionLawCarrier P)
    (hStruct : Homogenization.Book.Ch04.RestrictionStructuralLaw P)
    (Y : ℕ → Homogenization.TriadicCube d → Ω → Homogenization.FullBlockMat d) :
    ℕ → Homogenization.TriadicCube d → Ω → ENNReal :=
  fun j Q ω =>
    ENNReal.ofReal
      (fullBlockOperatorNorm
        (scalarFullBlockNormalizerMatrixAtScale hP hStruct j *
          scalarCenteredFullBlockMatrixAtScale hP hStruct j (Y j Q ω) *
          scalarFullBlockNormalizerMatrixAtScale hP hStruct j))

/--
Source label `l.union.bound`: terminal-scale normalization of the same
full-block matrix centered at scale `j`.
-/
noncomputable def terminalCenteredFullBlockDeviation
    {Ω : Type*} {d : ℕ} [NeZero d]
    {P : Homogenization.Book.Ch04.RestrictionCoeffLaw d}
    (hP : Homogenization.Book.Ch04.RestrictionLawCarrier P)
    (hStruct : Homogenization.Book.Ch04.RestrictionStructuralLaw P)
    (m : ℕ)
    (Y : ℕ → Homogenization.TriadicCube d → Ω → Homogenization.FullBlockMat d) :
    ℕ → Homogenization.TriadicCube d → Ω → ENNReal :=
  fun j Q ω =>
    ENNReal.ofReal
      (fullBlockOperatorNorm
        (scalarFullBlockNormalizerMatrixAtScale hP hStruct m *
          scalarCenteredFullBlockMatrixAtScale hP hStruct j (Y j Q ω) *
          scalarFullBlockNormalizerMatrixAtScale hP hStruct m))

/--
Source labels `a.HM` and `l.union.bound`: the terminal-normalized concrete
centered full-block deviation is bounded by `T = widetildeTheta_0` times the
intermediate-normalized deviation from the high-moment hypothesis.
-/
theorem terminalCenteredFullBlockDeviation_le_initialWidetildeTheta_mul_intermediate_of_P4
    {Ω : Type*} {d : ℕ} [NeZero d]
    {P : Homogenization.Book.Ch04.RestrictionCoeffLaw d}
    (hP : Homogenization.Book.Ch04.RestrictionLawCarrier P)
    (hStruct : Homogenization.Book.Ch04.RestrictionStructuralLaw P)
    (hP4 : Homogenization.Book.Ch05.QuantitativeCoarseGrainedEllipticity P)
    (m : ℕ)
    (Y : ℕ → Homogenization.TriadicCube d → Ω → Homogenization.FullBlockMat d)
    {j : ℕ} (hjm : j ≤ m) (Q : Homogenization.TriadicCube d) (ω : Ω) :
    terminalCenteredFullBlockDeviation hP hStruct m Y j Q ω ≤
      ENNReal.ofReal
          (Homogenization.Book.Ch05.widetildeThetaAtScale P (0 : ℤ) hP4) *
        intermediateCenteredFullBlockDeviation hP hStruct Y j Q ω := by
  unfold terminalCenteredFullBlockDeviation
  unfold intermediateCenteredFullBlockDeviation
  exact
    ofReal_fullBlockOperatorNorm_terminalNormalizedCenteredFullBlock_le_initialWidetildeTheta_mul_intermediate_of_P4
      hP hStruct hP4 hjm (Y j Q ω)

/--
Source label `a.HM`: the library's full-block coarse matrix process on a triadic cube.
The scale parameter is present only to match the high-moment observable shape.
-/
noncomputable def coarseFullBlockMatrixAtCubeProcess
    {Ω : Type*} {d : ℕ} (a : Ω → Homogenization.RegCoeffField d) :
    ℕ → Homogenization.TriadicCube d → Ω → Homogenization.FullBlockMat d :=
  fun _j Q ω => Homogenization.Book.Ch04.coarseFullBlockMatrixAtCube Q (a ω)

/--
Source label `a.HM`: the manuscript's intermediate-normalized centered
coarse-block deviation
`|Ahom_j^{-1/2} (bfA(Q)-Ahom_j) Ahom_j^{-1/2}|`.
-/
noncomputable def intermediateCoarseBlockDeviation
    {Ω : Type*} {d : ℕ} [NeZero d]
    {P : Homogenization.Book.Ch04.RestrictionCoeffLaw d}
    (hP : Homogenization.Book.Ch04.RestrictionLawCarrier P)
    (hStruct : Homogenization.Book.Ch04.RestrictionStructuralLaw P)
    (a : Ω → Homogenization.RegCoeffField d) :
    ℕ → Homogenization.TriadicCube d → Ω → ENNReal :=
  intermediateCenteredFullBlockDeviation hP hStruct
    (coarseFullBlockMatrixAtCubeProcess a)

/--
Source label `l.union.bound`: terminal-normalized centered coarse-block
deviation used in the maximal union bound.
-/
noncomputable def terminalCoarseBlockDeviation
    {Ω : Type*} {d : ℕ} [NeZero d]
    {P : Homogenization.Book.Ch04.RestrictionCoeffLaw d}
    (hP : Homogenization.Book.Ch04.RestrictionLawCarrier P)
    (hStruct : Homogenization.Book.Ch04.RestrictionStructuralLaw P)
    (m : ℕ) (a : Ω → Homogenization.RegCoeffField d) :
    ℕ → Homogenization.TriadicCube d → Ω → ENNReal :=
  terminalCenteredFullBlockDeviation hP hStruct m
    (coarseFullBlockMatrixAtCubeProcess a)

/--
Source label `l.S.and.J`: the library's squared terminal full-block fluctuation
observable is the square of the local full-block operator norm with the same
terminal normalization.
-/
theorem fullBlockNormalizedFluctuationOperatorNormSqAtScale_eq_terminal_norm_sq
    {d : ℕ} [NeZero d] {P : Homogenization.Book.Ch04.RestrictionCoeffLaw d}
    (hP : Homogenization.Book.Ch04.RestrictionLawCarrier P)
    (hStruct : Homogenization.Book.Ch04.RestrictionStructuralLaw P)
    (m : ℕ) (Q : Homogenization.TriadicCube d)
    (a : Homogenization.RegCoeffField d) :
    Homogenization.Book.Ch04.fullBlockNormalizedFluctuationOperatorNormSqAtScale
        hP hStruct (m : ℤ) Q a =
      fullBlockOperatorNorm
        (scalarFullBlockNormalizerMatrixAtScale hP hStruct m *
          scalarCenteredFullBlockMatrixAtScale hP hStruct m
            (Homogenization.Book.Ch04.coarseFullBlockMatrixAtCube Q a) *
          scalarFullBlockNormalizerMatrixAtScale hP hStruct m) ^ 2 := by
  simp [Homogenization.Book.Ch04.fullBlockNormalizedFluctuationOperatorNormSqAtScale,
    Homogenization.Book.Ch04.fullBlockNormalizedFluctuationOperatorNormSq,
    Homogenization.Book.Ch04.coarseFullBlockMatrixAtCube,
    Homogenization.coarseFullBlockMatrixObservable,
    scalarFullBlockNormalizerMatrixAtScale, scalarCenteredFullBlockMatrixAtScale,
    fullBlockOperatorNorm]

/--
Source label `l.S.and.J`: deterministic split of the library's terminal full-block
fluctuation into the stochastic centered-at-`j` block and the deterministic
annealed drift `Ahom_j - Ahom_m`.
-/
theorem fullBlockNormalizedFluctuationOperatorNormSqAtScale_le_two_stochastic_add_two_drift
    {d : ℕ} [NeZero d] {P : Homogenization.Book.Ch04.RestrictionCoeffLaw d}
    (hP : Homogenization.Book.Ch04.RestrictionLawCarrier P)
    (hStruct : Homogenization.Book.Ch04.RestrictionStructuralLaw P)
    (j m : ℕ) (Q : Homogenization.TriadicCube d)
    (a : Homogenization.RegCoeffField d) :
    Homogenization.Book.Ch04.fullBlockNormalizedFluctuationOperatorNormSqAtScale
        hP hStruct (m : ℤ) Q a ≤
      2 *
        fullBlockOperatorNorm
          (scalarFullBlockNormalizerMatrixAtScale hP hStruct m *
            scalarCenteredFullBlockMatrixAtScale hP hStruct j
              (Homogenization.Book.Ch04.coarseFullBlockMatrixAtCube Q a) *
            scalarFullBlockNormalizerMatrixAtScale hP hStruct m) ^ 2 +
      2 *
        fullBlockOperatorNorm
          (scalarFullBlockNormalizerMatrixAtScale hP hStruct m *
            (Homogenization.toFullBlockMat
                (Homogenization.Book.Ch04.scalarAnnealedBlockMatrixAtScale
                  hP hStruct (j : ℤ)) -
              Homogenization.toFullBlockMat
                (Homogenization.Book.Ch04.scalarAnnealedBlockMatrixAtScale
                  hP hStruct (m : ℤ))) *
            scalarFullBlockNormalizerMatrixAtScale hP hStruct m) ^ 2 := by
  let Dm := scalarFullBlockNormalizerMatrixAtScale hP hStruct m
  let A := Homogenization.Book.Ch04.coarseFullBlockMatrixAtCube Q a
  let Aj :=
    Homogenization.toFullBlockMat
      (Homogenization.Book.Ch04.scalarAnnealedBlockMatrixAtScale
        hP hStruct (j : ℤ))
  let Am :=
    Homogenization.toFullBlockMat
      (Homogenization.Book.Ch04.scalarAnnealedBlockMatrixAtScale
        hP hStruct (m : ℤ))
  have hcenter :
      scalarCenteredFullBlockMatrixAtScale hP hStruct m A =
        scalarCenteredFullBlockMatrixAtScale hP hStruct j A + (Aj - Am) := by
    dsimp [scalarCenteredFullBlockMatrixAtScale, A, Aj, Am]
    abel
  have hsplit :
      Dm * scalarCenteredFullBlockMatrixAtScale hP hStruct m A * Dm =
        Dm * scalarCenteredFullBlockMatrixAtScale hP hStruct j A * Dm +
          Dm * (Aj - Am) * Dm := by
    rw [hcenter, mul_add, add_mul]
  rw [fullBlockNormalizedFluctuationOperatorNormSqAtScale_eq_terminal_norm_sq
    hP hStruct m Q a]
  rw [show scalarFullBlockNormalizerMatrixAtScale hP hStruct m = Dm from rfl]
  rw [show Homogenization.Book.Ch04.coarseFullBlockMatrixAtCube Q a = A from rfl]
  rw [hsplit]
  exact fullBlockOperatorNorm_add_sq_le_two_mul_add
    (Dm * scalarCenteredFullBlockMatrixAtScale hP hStruct j A * Dm)
    (Dm * (Aj - Am) * Dm)

/--
Source label `e.P.bound`: if `a,b ≤ 1 + rho` and `rho ≤ 1`, then
`P_{k,m} = r_m(a+b)` is at most `4 r_m`.
-/
theorem terminal_p_le_four_mul_of_ab_bounds {r_m a b rho : ℝ}
    (hr_nonneg : 0 ≤ r_m)
    (hrho_le_one : rho ≤ 1)
    (ha : a ≤ 1 + rho) (hb : b ≤ 1 + rho) :
    terminalP r_m a b ≤ 4 * r_m := by
  have hab_sum : a + b ≤ 4 := by
    linarith
  have hmul := mul_le_mul_of_nonneg_left hab_sum hr_nonneg
  simpa [terminalP, mul_comm, mul_left_comm, mul_assoc] using hmul

/--
Source label `e.P.bound`: no-drop version of the terminal prefactor bound.
-/
theorem p_bound_of_no_drop {r_m a b F_k F_m rho P_km : ℝ}
    (hno : noDropWindow rho F_k F_m)
    (hF : F_k - F_m = contrastDrop r_m a b)
    (hP : P_km = terminalP r_m a b)
    (hFm_le_sq : F_m ≤ r_m ^ 2)
    (hr_sq_pos : 0 < r_m ^ 2)
    (hr_nonneg : 0 ≤ r_m)
    (hrho_pos : 0 < rho)
    (hrho_le_one : rho ≤ 1)
    (ha : 1 ≤ a) (hb : 1 ≤ b) :
    P_km ≤ 4 * r_m := by
  have hbounds :
      1 ≤ a ∧ a ≤ 1 + rho ∧ 1 ≤ b ∧ b ≤ 1 + rho :=
    no_drop_ab_bounds hno (le_refl (F_k - F_m)) hF hFm_le_sq hr_sq_pos
      hrho_pos ha hb
  rw [hP]
  exact terminal_p_le_four_mul_of_ab_bounds hr_nonneg hrho_le_one hbounds.2.1
    hbounds.2.2.2

/-- Source label `e.P.bound`: the concrete terminal prefactor is nonnegative. -/
theorem terminalPAtScales_nonneg_of_P4
    {d : ℕ} [NeZero d] {P : Homogenization.Book.Ch04.RestrictionCoeffLaw d}
    (hP : Homogenization.Book.Ch04.RestrictionLawCarrier P)
    (hStruct : Homogenization.Book.Ch04.RestrictionStructuralLaw P)
    (hP4 : Homogenization.Book.Ch05.QuantitativeCoarseGrainedEllipticity P)
    {k m : ℕ} (hkm : k ≤ m) :
    0 ≤ terminalPAtScales hP hStruct k m := by
  let r_m : ℝ := Real.sqrt (1 + contrastExcessAtScale hP hStruct m)
  let a : ℝ :=
    hP.barSigmaAtScale hStruct (k : ℤ) /
      hP.barSigmaAtScale hStruct (m : ℤ)
  let b : ℝ :=
    (hP.barSigmaStarAtScale hStruct (k : ℤ))⁻¹ /
      (hP.barSigmaStarAtScale hStruct (m : ℤ))⁻¹
  have hchain :=
    Homogenization.Book.Ch05.Section54.Pigeonhole.scalarChain_of_P4
      hP hStruct hP4 hkm
  have hbm_pos :
      0 < hP.barSigmaAtScale hStruct (m : ℤ) :=
    Homogenization.Book.Ch05.Section54.Pigeonhole.barSigmaAtScale_pos_of_P4
      hP hStruct hP4 m
  have hcm_pos :
      0 < hP.barSigmaStarAtScale hStruct (m : ℤ) :=
    Homogenization.Book.Ch05.Section54.Pigeonhole.barSigmaStarAtScale_pos_of_P4
      hP hStruct hP4 m
  have hcm_inv_pos :
      0 < (hP.barSigmaStarAtScale hStruct (m : ℤ))⁻¹ :=
    inv_pos.mpr hcm_pos
  have ha : 1 ≤ a := by
    dsimp [a]
    rw [le_div_iff₀ hbm_pos]
    simpa using hchain.2.2
  have hb : 1 ≤ b := by
    dsimp [b]
    rw [le_div_iff₀ hcm_inv_pos]
    simpa using hchain.2.1
  have hr_nonneg : 0 ≤ r_m := by
    dsimp [r_m]
    exact Real.sqrt_nonneg _
  have hsum_nonneg : 0 ≤ a + b := by linarith
  have hmain : 0 ≤ terminalP r_m a b := by
    exact mul_nonneg hr_nonneg hsum_nonneg
  simpa [terminalPAtScales, terminalP, r_m, a, b] using hmain

/--
Source labels `p.HC.CR` and `e.P.bound`: the concrete terminal prefactor
dominates the terminal square-root scale.  Under `(P4)`, the scalar ratios
`a_{k,m}` and `b_{k,m}` are each at least one, so
`P_{k,m} = r_m (a_{k,m}+b_{k,m})` is in particular at least `r_m`.
-/
theorem sqrt_one_add_contrastExcessAtScale_le_terminalPAtScales_of_P4
    {d : ℕ} [NeZero d] {P : Homogenization.Book.Ch04.RestrictionCoeffLaw d}
    (hP : Homogenization.Book.Ch04.RestrictionLawCarrier P)
    (hStruct : Homogenization.Book.Ch04.RestrictionStructuralLaw P)
    (hP4 : Homogenization.Book.Ch05.QuantitativeCoarseGrainedEllipticity P)
    {k m : ℕ} (hkm : k ≤ m) :
    Real.sqrt (1 + contrastExcessAtScale hP hStruct m) ≤
      terminalPAtScales hP hStruct k m := by
  let r_m : ℝ := Real.sqrt (1 + contrastExcessAtScale hP hStruct m)
  let a : ℝ :=
    hP.barSigmaAtScale hStruct (k : ℤ) /
      hP.barSigmaAtScale hStruct (m : ℤ)
  let b : ℝ :=
    (hP.barSigmaStarAtScale hStruct (k : ℤ))⁻¹ /
      (hP.barSigmaStarAtScale hStruct (m : ℤ))⁻¹
  have hchain :=
    Homogenization.Book.Ch05.Section54.Pigeonhole.scalarChain_of_P4
      hP hStruct hP4 hkm
  have hbm_pos :
      0 < hP.barSigmaAtScale hStruct (m : ℤ) :=
    Homogenization.Book.Ch05.Section54.Pigeonhole.barSigmaAtScale_pos_of_P4
      hP hStruct hP4 m
  have hcm_pos :
      0 < hP.barSigmaStarAtScale hStruct (m : ℤ) :=
    Homogenization.Book.Ch05.Section54.Pigeonhole.barSigmaStarAtScale_pos_of_P4
      hP hStruct hP4 m
  have hcm_inv_pos :
      0 < (hP.barSigmaStarAtScale hStruct (m : ℤ))⁻¹ :=
    inv_pos.mpr hcm_pos
  have ha : 1 ≤ a := by
    dsimp [a]
    rw [le_div_iff₀ hbm_pos]
    simpa using hchain.2.2
  have hb : 1 ≤ b := by
    dsimp [b]
    rw [le_div_iff₀ hcm_inv_pos]
    simpa using hchain.2.1
  have hr_nonneg : 0 ≤ r_m := by
    dsimp [r_m]
    exact Real.sqrt_nonneg _
  have hsum : 1 ≤ a + b := by
    linarith
  have hmain : r_m ≤ terminalP r_m a b := by
    calc
      r_m = r_m * 1 := by ring
      _ ≤ r_m * (a + b) := mul_le_mul_of_nonneg_left hsum hr_nonneg
      _ = terminalP r_m a b := by rfl
  simpa [terminalPAtScales, terminalP, r_m, a, b] using hmain

/--
Source labels `p.HC.CR` and `e.P.bound`: the terminal prefactor dominates
twice the library's scalar `sqrt(theta_m)`.  Under `(P4)` both scalar ratios
`a_{k,m}` and `b_{k,m}` are at least one, so
`P_{k,m} = r_m (a_{k,m} + b_{k,m}) >= 2 r_m = 2 sqrt(theta_m)`.  This is the
sharp pricing needed to pay the summed-weight first-power source split with
`2 * r_m` instead of the crude `2 * (1 + F_m)`.
-/
theorem two_mul_sqrtTheta_le_terminalPAtScales_of_P4
    {d : ℕ} [NeZero d] {P : Homogenization.Book.Ch04.RestrictionCoeffLaw d}
    (hP : Homogenization.Book.Ch04.RestrictionLawCarrier P)
    (hStruct : Homogenization.Book.Ch04.RestrictionStructuralLaw P)
    (hP4 : Homogenization.Book.Ch05.QuantitativeCoarseGrainedEllipticity P)
    {k m : ℕ} (hkm : k ≤ m) :
    2 * Real.sqrt (Homogenization.Book.Ch05.thetaAtScale hP hStruct (m : ℤ)) ≤
      terminalPAtScales hP hStruct k m := by
  have htheta :
      Homogenization.Book.Ch05.thetaAtScale hP hStruct (m : ℤ) =
        1 + contrastExcessAtScale hP hStruct m := by
    dsimp [contrastExcessAtScale]
    ring
  rw [htheta]
  let r_m : ℝ := Real.sqrt (1 + contrastExcessAtScale hP hStruct m)
  let a : ℝ :=
    hP.barSigmaAtScale hStruct (k : ℤ) /
      hP.barSigmaAtScale hStruct (m : ℤ)
  let b : ℝ :=
    (hP.barSigmaStarAtScale hStruct (k : ℤ))⁻¹ /
      (hP.barSigmaStarAtScale hStruct (m : ℤ))⁻¹
  have hchain :=
    Homogenization.Book.Ch05.Section54.Pigeonhole.scalarChain_of_P4
      hP hStruct hP4 hkm
  have hbm_pos :
      0 < hP.barSigmaAtScale hStruct (m : ℤ) :=
    Homogenization.Book.Ch05.Section54.Pigeonhole.barSigmaAtScale_pos_of_P4
      hP hStruct hP4 m
  have hcm_pos :
      0 < hP.barSigmaStarAtScale hStruct (m : ℤ) :=
    Homogenization.Book.Ch05.Section54.Pigeonhole.barSigmaStarAtScale_pos_of_P4
      hP hStruct hP4 m
  have hcm_inv_pos :
      0 < (hP.barSigmaStarAtScale hStruct (m : ℤ))⁻¹ :=
    inv_pos.mpr hcm_pos
  have ha : 1 ≤ a := by
    dsimp [a]
    rw [le_div_iff₀ hbm_pos]
    simpa using hchain.2.2
  have hb : 1 ≤ b := by
    dsimp [b]
    rw [le_div_iff₀ hcm_inv_pos]
    simpa using hchain.2.1
  have hr_nonneg : 0 ≤ r_m := by
    dsimp [r_m]
    exact Real.sqrt_nonneg _
  have hsum : 2 ≤ a + b := by
    linarith
  have hmain : 2 * r_m ≤ terminalP r_m a b := by
    calc
      2 * r_m = r_m * 2 := by ring
      _ ≤ r_m * (a + b) := mul_le_mul_of_nonneg_left hsum hr_nonneg
      _ = terminalP r_m a b := by rfl
  simpa [terminalPAtScales, terminalP, r_m, a, b] using hmain

/--
Source labels `p.HC.CR` and `e.P.bound`: the local weak-norm scalar
coefficient is exactly the manuscript terminal prefactor `P_{k,m}`.
-/
theorem localWeakNormScalarWeightAtScales_eq_terminalPAtScales_of_P4
    {d : ℕ} [NeZero d] {P : Homogenization.Book.Ch04.RestrictionCoeffLaw d}
    (hP : Homogenization.Book.Ch04.RestrictionLawCarrier P)
    (hStruct : Homogenization.Book.Ch04.RestrictionStructuralLaw P)
    (hP4 : Homogenization.Book.Ch05.QuantitativeCoarseGrainedEllipticity P)
    (k m : ℕ) :
    localWeakNormScalarWeightAtScales hP hStruct k m =
      terminalPAtScales hP hStruct k m := by
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
  have hsigma : sigma = Real.sqrt (bm * cm) := by
    rfl
  have htheta : theta = bm * cm⁻¹ := by
    rfl
  have hsqrt_bar : bm * sigma⁻¹ = Real.sqrt theta :=
    Homogenization.Book.Ch05.Section54.GoodScale.barSigma_mul_inv_sigma_eq_sqrt_theta
      hbm hcm hsigma htheta
  have hsqrt_star : sigma * cm⁻¹ = Real.sqrt theta :=
    Homogenization.Book.Ch05.Section54.GoodScale.sigma_mul_inv_star_eq_sqrt_theta
      hbm hcm hsigma htheta
  have harg : 1 + contrastExcessAtScale hP hStruct m = theta := by
    dsimp [contrastExcessAtScale, theta]
    ring
  have hbar_term : Real.sqrt theta * (bk / bm) = sigma⁻¹ * bk := by
    rw [← hsqrt_bar]
    field_simp [ne_of_gt hbm]
  have hstar_term : Real.sqrt theta * (ck⁻¹ / cm⁻¹) = sigma * ck⁻¹ := by
    rw [← hsqrt_star]
    rw [div_eq_mul_inv, inv_inv]
    field_simp [ne_of_gt hcm]
  change
    sigma * ck⁻¹ + sigma⁻¹ * bk =
      Real.sqrt (1 + contrastExcessAtScale hP hStruct m) *
        (bk / bm + ck⁻¹ / cm⁻¹)
  rw [harg, mul_add, hbar_term, hstar_term]
  ring

/--
Source label `e.P.bound`: on a no-drop window, the concrete terminal
prefactor satisfies `P_{k,m} <= 4 r_m`.
-/
theorem terminalPAtScales_le_four_mul_sqrt_contrastExcess_of_noDrop_of_P4
    {d : ℕ} [NeZero d] {P : Homogenization.Book.Ch04.RestrictionCoeffLaw d}
    (hP : Homogenization.Book.Ch04.RestrictionLawCarrier P)
    (hStruct : Homogenization.Book.Ch04.RestrictionStructuralLaw P)
    (hP4 : Homogenization.Book.Ch05.QuantitativeCoarseGrainedEllipticity P)
    {k m : ℕ} (hkm : k ≤ m) {rho : ℝ}
    (hno :
      noDropWindow rho
        (contrastExcessAtScale hP hStruct k)
        (contrastExcessAtScale hP hStruct m))
    (hrho_pos : 0 < rho) (hrho_le_one : rho ≤ 1) :
    terminalPAtScales hP hStruct k m ≤
      4 * Real.sqrt (1 + contrastExcessAtScale hP hStruct m) := by
  let r_m : ℝ := Real.sqrt (1 + contrastExcessAtScale hP hStruct m)
  let a : ℝ :=
    hP.barSigmaAtScale hStruct (k : ℤ) /
      hP.barSigmaAtScale hStruct (m : ℤ)
  let b : ℝ :=
    (hP.barSigmaStarAtScale hStruct (k : ℤ))⁻¹ /
      (hP.barSigmaStarAtScale hStruct (m : ℤ))⁻¹
  let theta_k := Homogenization.Book.Ch05.thetaAtScale hP hStruct (k : ℤ)
  let theta_m := Homogenization.Book.Ch05.thetaAtScale hP hStruct (m : ℤ)
  have hchain :=
    Homogenization.Book.Ch05.Section54.Pigeonhole.scalarChain_of_P4
      hP hStruct hP4 hkm
  have hbm_pos :
      0 < hP.barSigmaAtScale hStruct (m : ℤ) :=
    Homogenization.Book.Ch05.Section54.Pigeonhole.barSigmaAtScale_pos_of_P4
      hP hStruct hP4 m
  have hck_pos :
      0 < hP.barSigmaStarAtScale hStruct (k : ℤ) :=
    Homogenization.Book.Ch05.Section54.Pigeonhole.barSigmaStarAtScale_pos_of_P4
      hP hStruct hP4 k
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
  have hprod_eq : a * b = theta_k / theta_m := by
    dsimp [a, b, theta_k, theta_m]
    rw [terminalScalarRatioProduct_eq_theta_ratio
      (ne_of_gt hbm_pos) (ne_of_gt hck_pos) (ne_of_gt hcm_pos)]
    rfl
  have hF :
      contrastExcessAtScale hP hStruct k -
          contrastExcessAtScale hP hStruct m =
        contrastDrop r_m a b := by
    calc
      contrastExcessAtScale hP hStruct k -
          contrastExcessAtScale hP hStruct m
          = theta_k - theta_m := by
            dsimp [contrastExcessAtScale, theta_k, theta_m]
            ring
      _ = theta_m * (theta_k / theta_m - 1) := by
            field_simp [ne_of_gt htheta_m_pos]
      _ = r_m ^ 2 * (a * b - 1) := by
            rw [hr_sq, hprod_eq]
      _ = contrastDrop r_m a b := rfl
  have hFm_le_sq :
      contrastExcessAtScale hP hStruct m ≤ r_m ^ 2 := by
    rw [hr_sq]
    dsimp [contrastExcessAtScale, theta_m]
    linarith
  have hr_sq_pos : 0 < r_m ^ 2 := by
    rw [hr_sq]
    exact htheta_m_pos
  have hr_nonneg : 0 ≤ r_m := by
    dsimp [r_m]
    exact Real.sqrt_nonneg _
  have hP_le :
      terminalP r_m a b ≤ 4 * r_m :=
    p_bound_of_no_drop hno hF rfl hFm_le_sq hr_sq_pos hr_nonneg
      hrho_pos hrho_le_one ha hb
  simpa [terminalPAtScales, r_m, a, b] using hP_le

/--
Scalar KEY CHECK for the linear edge-memory channel (Layer B).

The linear residual factor `terminalP / (1 + F_k)` collapses to a bounded
constant `4` whenever `F_m ≤ F_k` (contrast antitonicity on a window with
`k ≤ m`), `0 ≤ F_m`, and `terminalP ≤ 4 √(1 + F_m)`: the `1 / (1 + F_k)`
denominator eats the `√(1 + F_m)` numerator down to at most `1`, because
`√(1 + F_m) ≤ 1 + F_m ≤ 1 + F_k`.  Hence the H-linear residual
`(H / (1 + F_k)) · terminalP` is at most `4 · H`, with no leftover `√(1 + F)`. -/
theorem linearEdgeMemory_factor_le_four_of_le {H terminalP F_k F_m : ℝ}
    (hH_nonneg : 0 ≤ H)
    (hFm_nonneg : 0 ≤ F_m)
    (hFm_le_Fk : F_m ≤ F_k)
    (hP_le : terminalP ≤ 4 * Real.sqrt (1 + F_m)) :
    (H / (1 + F_k)) * terminalP ≤ 4 * H := by
  have hFk_nonneg : 0 ≤ F_k := le_trans hFm_nonneg hFm_le_Fk
  have hden_pos : 0 < 1 + F_k := by linarith
  have hden_m_pos : 0 < 1 + F_m := by linarith
  -- `√(1 + F_m) ≤ 1 + F_k`, since `1 + F_m ≤ (1 + F_k)^2`.
  have hsqrt_le : Real.sqrt (1 + F_m) ≤ 1 + F_k := by
    rw [Real.sqrt_le_left (le_of_lt hden_pos)]
    nlinarith
  have hsqrt_nonneg : 0 ≤ Real.sqrt (1 + F_m) := Real.sqrt_nonneg _
  -- `(H / (1+F_k)) · terminalP ≤ (H / (1+F_k)) · 4 √(1+F_m) ≤ 4 H`.
  have hdiv_nonneg : 0 ≤ H / (1 + F_k) :=
    div_nonneg hH_nonneg (le_of_lt hden_pos)
  calc
    (H / (1 + F_k)) * terminalP
        ≤ (H / (1 + F_k)) * (4 * Real.sqrt (1 + F_m)) :=
          mul_le_mul_of_nonneg_left hP_le hdiv_nonneg
    _ = (4 * H) * (Real.sqrt (1 + F_m) / (1 + F_k)) := by
          rw [div_mul_eq_mul_div, mul_div_assoc]
          ring
    _ ≤ (4 * H) * 1 := by
          have hratio_le : Real.sqrt (1 + F_m) / (1 + F_k) ≤ 1 :=
            (div_le_one hden_pos).mpr hsqrt_le
          exact mul_le_mul_of_nonneg_left hratio_le (by positivity)
    _ = 4 * H := by ring

/--
Concrete KEY CHECK for the linear edge-memory channel (Layer B): on a
no-drop window `k = i-1`, `m = i` with `k ≤ m`, the H-linear edge-memory
residual factor `terminalPAtScales / (1 + F_k)` collapses so that
`(H / (1 + F_k)) · terminalPAtScales ≤ 4 · H`.  The `terminalPAtScales`
factor is thus **fully absorbable into an `A·H` (linear-memory) channel**: it
reduces to `4·H` up to fixed no-drop constants, leaving no residual `√(1+F)`. -/
theorem linearEdgeMemory_terminalPAtScales_factor_le_four_of_noDrop_of_P4
    {d : ℕ} [NeZero d] {P : Homogenization.Book.Ch04.RestrictionCoeffLaw d}
    (hP : Homogenization.Book.Ch04.RestrictionLawCarrier P)
    (hStruct : Homogenization.Book.Ch04.RestrictionStructuralLaw P)
    (hP4 : Homogenization.Book.Ch05.QuantitativeCoarseGrainedEllipticity P)
    {k m : ℕ} (hkm : k ≤ m) {rho H : ℝ}
    (hno :
      noDropWindow rho
        (contrastExcessAtScale hP hStruct k)
        (contrastExcessAtScale hP hStruct m))
    (hrho_pos : 0 < rho) (hrho_le_one : rho ≤ 1)
    (hH_nonneg : 0 ≤ H) :
    (H / (1 + contrastExcessAtScale hP hStruct k)) *
        terminalPAtScales hP hStruct k m ≤
      4 * H := by
  have hP_le :
      terminalPAtScales hP hStruct k m ≤
        4 * Real.sqrt (1 + contrastExcessAtScale hP hStruct m) :=
    terminalPAtScales_le_four_mul_sqrt_contrastExcess_of_noDrop_of_P4
      hP hStruct hP4 hkm hno hrho_pos hrho_le_one
  have hFm_nonneg : 0 ≤ contrastExcessAtScale hP hStruct m :=
    contrastExcessAtScale_nonneg_of_P4 hP hStruct hP4 m
  have hFm_le_Fk :
      contrastExcessAtScale hP hStruct m ≤
        contrastExcessAtScale hP hStruct k :=
    contrastExcessAtScale_antitone_of_P4 hP hStruct hP4 hkm
  exact linearEdgeMemory_factor_le_four_of_le hH_nonneg hFm_nonneg
    hFm_le_Fk hP_le

/--
Source label `e.sqrt.tau.absorb`: on a no-drop window, the expected
lower-scale response of the special terminal pair is at most `2 r_m`.
-/
theorem expectedResponseJCubeSet_special_le_two_mul_sqrt_contrastExcess_of_noDrop_of_P4
    {d : ℕ} [NeZero d] {P : Homogenization.Book.Ch04.RestrictionCoeffLaw d}
    (hP : Homogenization.Book.Ch04.RestrictionLawCarrier P)
    (hStruct : Homogenization.Book.Ch04.RestrictionStructuralLaw P)
    (hP4 : Homogenization.Book.Ch05.QuantitativeCoarseGrainedEllipticity P)
    {k m : ℕ} (hkm : k ≤ m) {rho : ℝ}
    (hno :
      noDropWindow rho
        (contrastExcessAtScale hP hStruct k)
        (contrastExcessAtScale hP hStruct m))
    (hrho_pos : 0 < rho) (hrho_le_one : rho ≤ 1)
    (e : Homogenization.Vec d)
    (he : Homogenization.Book.Ch02.vecNorm e = 1) :
    Homogenization.Book.Ch04.expectedResponseJCubeSet P
        (Homogenization.originCube d (k : ℤ))
        (Homogenization.Book.Ch05.specialPAtScale hP hStruct (m : ℤ) e)
        (Homogenization.Book.Ch05.specialQAtScale hP hStruct (m : ℤ) e) ≤
      2 * Real.sqrt (1 + contrastExcessAtScale hP hStruct m) := by
  let r_m : ℝ := Real.sqrt (1 + contrastExcessAtScale hP hStruct m)
  let a : ℝ :=
    hP.barSigmaAtScale hStruct (k : ℤ) /
      hP.barSigmaAtScale hStruct (m : ℤ)
  let b : ℝ :=
    (hP.barSigmaStarAtScale hStruct (k : ℤ))⁻¹ /
      (hP.barSigmaStarAtScale hStruct (m : ℤ))⁻¹
  let theta_k := Homogenization.Book.Ch05.thetaAtScale hP hStruct (k : ℤ)
  let theta_m := Homogenization.Book.Ch05.thetaAtScale hP hStruct (m : ℤ)
  have hchain :=
    Homogenization.Book.Ch05.Section54.Pigeonhole.scalarChain_of_P4
      hP hStruct hP4 hkm
  have hbm_pos :
      0 < hP.barSigmaAtScale hStruct (m : ℤ) :=
    Homogenization.Book.Ch05.Section54.Pigeonhole.barSigmaAtScale_pos_of_P4
      hP hStruct hP4 m
  have hck_pos :
      0 < hP.barSigmaStarAtScale hStruct (k : ℤ) :=
    Homogenization.Book.Ch05.Section54.Pigeonhole.barSigmaStarAtScale_pos_of_P4
      hP hStruct hP4 k
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
  have hprod_eq : a * b = theta_k / theta_m := by
    dsimp [a, b, theta_k, theta_m]
    rw [terminalScalarRatioProduct_eq_theta_ratio
      (ne_of_gt hbm_pos) (ne_of_gt hck_pos) (ne_of_gt hcm_pos)]
    rfl
  have hF :
      contrastExcessAtScale hP hStruct k -
          contrastExcessAtScale hP hStruct m =
        contrastDrop r_m a b := by
    calc
      contrastExcessAtScale hP hStruct k -
          contrastExcessAtScale hP hStruct m
          = theta_k - theta_m := by
            dsimp [contrastExcessAtScale, theta_k, theta_m]
            ring
      _ = theta_m * (theta_k / theta_m - 1) := by
            field_simp [ne_of_gt htheta_m_pos]
      _ = r_m ^ 2 * (a * b - 1) := by
            rw [hr_sq, hprod_eq]
      _ = contrastDrop r_m a b := rfl
  have hFm_le_sq :
      contrastExcessAtScale hP hStruct m ≤ r_m ^ 2 := by
    rw [hr_sq]
    dsimp [contrastExcessAtScale, theta_m]
    linarith
  have hr_sq_pos : 0 < r_m ^ 2 := by
    rw [hr_sq]
    exact htheta_m_pos
  have hr_nonneg : 0 ≤ r_m := by
    dsimp [r_m]
    exact Real.sqrt_nonneg _
  have hP_le :
      terminalP r_m a b ≤ 4 * r_m :=
    p_bound_of_no_drop hno hF rfl hFm_le_sq hr_sq_pos hr_nonneg
      hrho_pos hrho_le_one ha hb
  have hr_eq :
      Real.sqrt (Homogenization.Book.Ch05.thetaAtScale hP hStruct (m : ℤ)) =
        r_m := by
    dsimp [r_m, contrastExcessAtScale]
    congr 1
    ring
  have hformula :=
    expectedResponseJCubeSet_special_eq_half_terminalP_sub_one_of_P4
      hP hStruct hP4 m k e he
  have hformula' :
      Homogenization.Book.Ch04.expectedResponseJCubeSet P
          (Homogenization.originCube d (k : ℤ))
          (Homogenization.Book.Ch05.specialPAtScale hP hStruct (m : ℤ) e)
          (Homogenization.Book.Ch05.specialQAtScale hP hStruct (m : ℤ) e) =
        (1 / 2 : ℝ) * terminalP r_m a b - 1 := by
    calc
      Homogenization.Book.Ch04.expectedResponseJCubeSet P
          (Homogenization.originCube d (k : ℤ))
          (Homogenization.Book.Ch05.specialPAtScale hP hStruct (m : ℤ) e)
          (Homogenization.Book.Ch05.specialQAtScale hP hStruct (m : ℤ) e)
          =
        (1 / 2 : ℝ) *
          terminalP
            (Real.sqrt (Homogenization.Book.Ch05.thetaAtScale hP hStruct (m : ℤ)))
            (hP.barSigmaAtScale hStruct (k : ℤ) /
              hP.barSigmaAtScale hStruct (m : ℤ))
            ((hP.barSigmaStarAtScale hStruct (k : ℤ))⁻¹ /
              (hP.barSigmaStarAtScale hStruct (m : ℤ))⁻¹) - 1 := hformula
      _ = (1 / 2 : ℝ) * terminalP r_m a b - 1 := by
        rw [hr_eq]
  calc
    Homogenization.Book.Ch04.expectedResponseJCubeSet P
        (Homogenization.originCube d (k : ℤ))
        (Homogenization.Book.Ch05.specialPAtScale hP hStruct (m : ℤ) e)
        (Homogenization.Book.Ch05.specialQAtScale hP hStruct (m : ℤ) e)
        = (1 / 2 : ℝ) * terminalP r_m a b - 1 := hformula'
    _ ≤ (1 / 2 : ℝ) * terminalP r_m a b := by linarith
    _ ≤ 2 * r_m := by nlinarith

/--
Source label `e.tau.sum.absorb`: scalar absorption step behind the weighted
additivity-defect estimate.
-/
theorem terminal_p_mul_tau_le_two_mul_drop {r_m P tau drop : ℝ}
    (hP_le : P ≤ 4 * r_m)
    (htau_nonneg : 0 ≤ tau)
    (hrt : r_m * tau ≤ (1 / 2 : ℝ) * drop) :
    P * tau ≤ 2 * drop := by
  have hP_tau_le : P * tau ≤ (4 * r_m) * tau :=
    mul_le_mul_of_nonneg_right hP_le htau_nonneg
  have hfour : (4 * r_m) * tau = 4 * (r_m * tau) := by ring
  have hrt_four : 4 * (r_m * tau) ≤ 4 * ((1 / 2 : ℝ) * drop) := by
    nlinarith
  have htarget : 4 * ((1 / 2 : ℝ) * drop) = 2 * drop := by ring
  calc
    P * tau ≤ (4 * r_m) * tau := hP_tau_le
    _ = 4 * (r_m * tau) := hfour
    _ ≤ 4 * ((1 / 2 : ℝ) * drop) := hrt_four
    _ = 2 * drop := htarget

/--
Source label `e.tau.sum.absorb`: finite weighted version of the no-drop
additivity-defect absorption.  The geometric estimate for the concrete weights
is supplied later by the scale iteration.
-/
theorem weighted_terminal_tau_absorb {ι : Type*} (s : Finset ι)
    {w tau drop : ι → ℝ} {r_m P rho F_m Cw : ℝ}
    (hP_le : P ≤ 4 * r_m)
    (hw_nonneg : ∀ i ∈ s, 0 ≤ w i)
    (htau_nonneg : ∀ i ∈ s, 0 ≤ tau i)
    (hrt : ∀ i ∈ s, r_m * tau i ≤ (1 / 2 : ℝ) * drop i)
    (hdrop : ∀ i ∈ s, drop i ≤ rho * F_m)
    (hCw : ∑ i ∈ s, w i ≤ Cw)
    (hrhoF_nonneg : 0 ≤ rho * F_m) :
    P * (∑ i ∈ s, w i * tau i) ≤ 2 * Cw * (rho * F_m) := by
  have hterm :
      ∀ i ∈ s, P * (w i * tau i) ≤ w i * (2 * (rho * F_m)) := by
    intro i hi
    have hPtau_drop :
        P * tau i ≤ 2 * drop i :=
      terminal_p_mul_tau_le_two_mul_drop hP_le (htau_nonneg i hi) (hrt i hi)
    have hdrop_bound : 2 * drop i ≤ 2 * (rho * F_m) := by
      nlinarith [hdrop i hi]
    have hPtau_bound : P * tau i ≤ 2 * (rho * F_m) :=
      le_trans hPtau_drop hdrop_bound
    have hwi_nonneg : 0 ≤ w i := hw_nonneg i hi
    have h := mul_le_mul_of_nonneg_left hPtau_bound hwi_nonneg
    simpa [mul_comm, mul_left_comm, mul_assoc] using h
  calc
    P * (∑ i ∈ s, w i * tau i)
        = ∑ i ∈ s, P * (w i * tau i) := by
          rw [Finset.mul_sum]
    _ ≤ ∑ i ∈ s, w i * (2 * (rho * F_m)) :=
          Finset.sum_le_sum fun i hi => hterm i hi
    _ = (∑ i ∈ s, w i) * (2 * (rho * F_m)) := by
          rw [Finset.sum_mul]
    _ ≤ Cw * (2 * (rho * F_m)) :=
          mul_le_mul_of_nonneg_right hCw (by nlinarith [hrhoF_nonneg])
    _ = 2 * Cw * (rho * F_m) := by ring

/--
Source label `e.sqrt.tau.absorb`: square-root absorption once the product of
the additivity defect and the lower-scale response has the required bound.
-/
theorem sqrt_tau_response_absorb {tau response B : ℝ}
    (htau_nonneg : 0 ≤ tau)
    (hresponse_nonneg : 0 ≤ response)
    (hB_nonneg : 0 ≤ B)
    (hprod : tau * response ≤ B ^ 2) :
    Real.sqrt tau * Real.sqrt response ≤ B := by
  have hsquare :
      (Real.sqrt tau * Real.sqrt response) ^ 2 ≤ B ^ 2 := by
    rw [mul_pow, Real.sq_sqrt htau_nonneg, Real.sq_sqrt hresponse_nonneg]
    exact hprod
  have hleft_nonneg : 0 ≤ Real.sqrt tau * Real.sqrt response :=
    mul_nonneg (Real.sqrt_nonneg tau) (Real.sqrt_nonneg response)
  nlinarith [sq_nonneg (B - Real.sqrt tau * Real.sqrt response)]

/--
Source label `e.sqrt.tau.absorb`: formula-facing version with the
`ρ^{1/2} δ^{-1/2} F_m` scale.
-/
theorem sqrt_tau_response_absorb_delta {tau response C rho delta F_m : ℝ}
    (htau_nonneg : 0 ≤ tau)
    (hresponse_nonneg : 0 ≤ response)
    (hC_nonneg : 0 ≤ C)
    (hdelta_pos : 0 < delta)
    (hF_nonneg : 0 ≤ F_m)
    (hprod :
      tau * response ≤
        (C * Real.sqrt rho * Real.sqrt delta⁻¹ * F_m) ^ 2) :
    Real.sqrt tau * Real.sqrt response ≤
      C * Real.sqrt rho * Real.sqrt delta⁻¹ * F_m := by
  have hdelta_inv_nonneg : 0 ≤ delta⁻¹ :=
    inv_nonneg.mpr (le_of_lt hdelta_pos)
  have hB_nonneg : 0 ≤ C * Real.sqrt rho * Real.sqrt delta⁻¹ * F_m := by
    positivity
  exact sqrt_tau_response_absorb htau_nonneg hresponse_nonneg hB_nonneg hprod

end Homogenization.HighContrast.EntryScale
