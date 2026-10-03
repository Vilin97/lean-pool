/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/
module


public import LeanPool.CoarseGraining.Homogenization.Deterministic.MultiscaleQuantitiesBasic
public import LeanPool.CoarseGraining.Homogenization.Deterministic.WeakNormInterfaces
public import LeanPool.CoarseGraining.Homogenization.Multiscale.NormalizedNorms
public import LeanPool.CoarseGraining.Homogenization.CoarseGraining.MagicIdentities.MuOrdering
public import LeanPool.CoarseGraining.Homogenization.CoarseGraining.OriginCubeEllipticRecovery
public import LeanPool.CoarseGraining.Homogenization.CoarseGraining.ResponseIdentities.Existence
public import LeanPool.CoarseGraining.Homogenization.CoarseGraining.ResponseIdentities.AverageFormulas
public import LeanPool.CoarseGraining.Homogenization.PDE.HarmonicCube
public import LeanPool.CoarseGraining.Homogenization.Sobolev.Foundations.HodgeCubeBridge
public import LeanPool.CoarseGraining.Homogenization.Geometry.CubeMetric

/-! # Conversions -/

@[expose] public section

namespace Homogenization

noncomputable section

open scoped BigOperators

/-!
# Deterministic coarse-grained Poincare inequalities

This file packages the first deterministic Chapter-3 `q = 1` Poincare step.

At the current checkpoint we keep the one-cube energy estimate as an explicit
hypothesis on descendant cube averages. This isolates the honest downstream
multiscale summation argument while the fully note-faithful Chapter-2
energy-averaging interface is still being stabilized upstream.
-/

/-- Descendant cube-average control for gradients by the local coarse
`σ_*^{-1}` block and a scalar energy density. -/
def CubeAverageGradientEnergyControl {d : ℕ} (Q : TriadicCube d)
    (a : CoeffField d) (g : Vec d → Vec d) (energy : Vec d → ℝ) : Prop :=
  ∀ j : ℕ, ∀ R ∈ descendantsAtDepth Q j,
    vecNormSq (cubeAverageVec R g) ≤
      coarseSigmaStarInvBlockNorm R a * cubeAverage R energy

/-- Descendant cube-average control for fluxes by the local coarse `b` block
and a scalar energy density. -/
def CubeAverageFluxEnergyControl {d : ℕ} (Q : TriadicCube d)
    (a : CoeffField d) (flux : Vec d → Vec d) (energy : Vec d → ℝ) : Prop :=
  ∀ j : ℕ, ∀ R ∈ descendantsAtDepth Q j,
    vecNormSq (cubeAverageVec R flux) ≤
      coarseBBlockNorm R a * cubeAverage R energy


private theorem vecNormSq_single_one {d : ℕ} (i : Fin d) :
    vecNormSq (Pi.single i 1 : Vec d) = 1 := by
  rw [vecNormSq, vecDot, Finset.sum_eq_single i]
  · simp
  · intro j _ hij
    simp [Pi.single_eq_of_ne hij]
  · simp

private theorem basis_sub_pairing {d : ℕ} (M : Mat d) (i j : Fin d) :
    vecDot (Pi.single i 1 - Pi.single j 1)
      (matVecMul M (Pi.single i 1 - Pi.single j 1)) =
      M i i - M i j - M j i + M j j := by
  calc
    vecDot (Pi.single i 1 - Pi.single j 1)
        (matVecMul M (Pi.single i 1 - Pi.single j 1)) =
      vecDot (Pi.single i 1 - Pi.single j 1)
        (matVecMul M (Pi.single i 1) - matVecMul M (Pi.single j 1)) := by
          simp [sub_eq_add_neg, matVecMul_add, matVecMul_neg]
    _ =
        vecDot (Pi.single i 1 - Pi.single j 1) (matVecMul M (Pi.single i 1)) -
          vecDot (Pi.single i 1 - Pi.single j 1) (matVecMul M (Pi.single j 1)) := by
            simp [sub_eq_add_neg, vecDot_add_right, vecDot_neg_right]
    _ =
        (vecDot (Pi.single i 1) (matVecMul M (Pi.single i 1)) -
            vecDot (Pi.single j 1) (matVecMul M (Pi.single i 1))) -
          (vecDot (Pi.single i 1) (matVecMul M (Pi.single j 1)) -
            vecDot (Pi.single j 1) (matVecMul M (Pi.single j 1))) := by
              simp [sub_eq_add_neg, vecDot_add_left, vecDot_neg_left]
    _ = M i i - M i j - M j i + M j j := by
          simp [vecDot_single_left, matVecMul_single]
          ring

theorem responseJ_le_plainUpperBound_of_isEllipticFieldOn {d : ℕ}
    {U : Set (Vec d)} {a : CoeffField d} {lam Lam : ℝ}
    [MeasureTheory.IsFiniteMeasure (volumeMeasureOn U)]
    (hEll : IsEllipticFieldOn lam Lam U a)
    (hvol : (MeasureTheory.volume U).toReal ≠ 0)
    (p q : Vec d) :
    ResponseJ U p q a ≤ lam⁻¹ * (Lam ^ 2 * vecNormSq p + vecNormSq q) := by
  unfold ResponseJ
  refine csSup_le (responseJValueSet_nonempty U p q a) ?_
  rintro m ⟨u, rfl⟩
  refine volumeAverage_le_of_le_on (measurableSet_of_isEllipticFieldOn hEll)
    (scalarResponseIntegrand_integrableOn_of_isEllipticFieldOn hEll p q u) hvol ?_
  exact scalarResponseIntegrand_le_plainUpperBound_of_isEllipticFieldOn hEll p q u

theorem matNorm_le_two_mul_card_mul_of_posSemidef_of_quadratic_le
    {d : ℕ} {A : Mat d} {C : ℝ}
    (hPos : A.PosSemidef) (hC : 0 ≤ C)
    (hquad : ∀ x : Vec d, vecDot x (matVecMul A x) ≤ C * vecNormSq x) :
    matNorm A ≤ 2 * (Fintype.card (Fin d) : ℝ) * C := by
  have hsymm : A.IsSymm := by
    simpa [Matrix.IsHermitian, Matrix.IsSymm] using hPos.isHermitian
  have hentry :
      ∀ i j : Fin d, |A i j| ≤ 2 * C := by
    intro i j
    by_cases hij : i = j
    · subst j
      have hdiag_nonneg : 0 ≤ A i i := by
        simpa using hPos.diag_nonneg (i := i)
      have hdiag_le : A i i ≤ C := by
        have hsingle := hquad (Pi.single i 1 : Vec d)
        simpa [vecNormSq_single_one, vecDot_single_left, matVecMul_single] using hsingle
      have hdiag_abs : |A i i| ≤ 2 * C := by
        refine abs_le.mpr ?_
        constructor <;> nlinarith
      simpa using hdiag_abs
    · have hii_nonneg : 0 ≤ A i i := by
        simpa using hPos.diag_nonneg (i := i)
      have hjj_nonneg : 0 ≤ A j j := by
        simpa using hPos.diag_nonneg (i := j)
      have hi : vecNormSq (Pi.single i 1 : Vec d) = 1 := vecNormSq_single_one i
      have hj : vecNormSq (Pi.single j 1 : Vec d) = 1 := vecNormSq_single_one j
      have hsum_pairing :
          A i i + A i j + A j i + A j j ≤ 4 * C := by
        have hsum :=
          hquad ((Pi.single i 1 : Vec d) + Pi.single j 1)
        have hsum_norm :
            vecNormSq ((Pi.single i 1 : Vec d) + Pi.single j 1) ≤ 4 := by
          calc
            vecNormSq ((Pi.single i 1 : Vec d) + Pi.single j 1) ≤
                2 *
                  (vecNormSq (Pi.single i 1 : Vec d) +
                    vecNormSq (Pi.single j 1 : Vec d)) := by
                      exact vecNormSq_add_le _ _
            _ = 4 := by rw [hi, hj]; norm_num
        rw [basis_sum_pairing] at hsum
        nlinarith
      have hsub_pairing :
          A i i - A i j - A j i + A j j ≤ 4 * C := by
        have hsub :=
          hquad ((Pi.single i 1 : Vec d) - Pi.single j 1)
        have hsub_norm :
            vecNormSq ((Pi.single i 1 : Vec d) - Pi.single j 1) ≤ 4 := by
          calc
            vecNormSq ((Pi.single i 1 : Vec d) - Pi.single j 1) =
                vecNormSq ((Pi.single i 1 : Vec d) + (-1 : ℝ) • (Pi.single j 1 : Vec d)) := by
                  simp [sub_eq_add_neg]
            _ ≤
                2 *
                  (vecNormSq (Pi.single i 1 : Vec d) +
                    vecNormSq ((-1 : ℝ) • (Pi.single j 1 : Vec d))) := by
                      exact vecNormSq_add_le _ _
            _ = 4 := by
                  rw [hi, vecNormSq_smul, hj]
                  norm_num
        rw [basis_sub_pairing] at hsub
        nlinarith
      have hupper : A i j ≤ 2 * C := by
        rw [hsymm.apply i j] at hsum_pairing
        nlinarith
      have hlower : -2 * C ≤ A i j := by
        rw [hsymm.apply i j] at hsub_pairing
        nlinarith
      exact abs_le.mpr ⟨by simpa using hlower, hupper⟩
  have hsq :
      matNormSq A ≤ (2 * (Fintype.card (Fin d) : ℝ) * C) ^ 2 := by
    unfold matNormSq
    calc
      ∑ i, ∑ j, A i j ^ 2 ≤ ∑ i, ∑ j, (2 * C) ^ 2 := by
        refine Finset.sum_le_sum ?_
        intro i hi
        refine Finset.sum_le_sum ?_
        intro j hj
        have hij : |A i j| ≤ 2 * C := hentry i j
        rcases abs_le.mp hij with ⟨hij_lo, hij_hi⟩
        nlinarith [sq_nonneg (A i j)]
      _ = (Fintype.card (Fin d) : ℝ) * ((Fintype.card (Fin d) : ℝ) * (2 * C) ^ 2) := by
        simp [Finset.sum_const, nsmul_eq_mul]
      _ = (2 * (Fintype.card (Fin d) : ℝ) * C) ^ 2 := by
        ring
  have hrhs_nonneg : 0 ≤ 2 * (Fintype.card (Fin d) : ℝ) * C := by
    positivity
  unfold matNorm
  exact (Real.sqrt_le_iff).2 ⟨hrhs_nonneg, hsq⟩

end

end Homogenization
