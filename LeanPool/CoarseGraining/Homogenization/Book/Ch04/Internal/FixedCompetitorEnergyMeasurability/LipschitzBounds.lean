/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

import LeanPool.CoarseGraining.Homogenization.CoarseGraining.MuQuadratic
import LeanPool.CoarseGraining.Homogenization.CoarseGraining.MuOperator.CoeffOperator
import LeanPool.CoarseGraining.Homogenization.CoarseGraining.MuRecovery.CorrectionSpaceEnergy
import LeanPool.CoarseGraining.Homogenization.Book.Ch04.Internal.CoarseObservableMeasurability.Mu
import LeanPool.CoarseGraining.Homogenization.Book.Ch04.Internal.FixedCompetitorEnergyMeasurability.Measurability
import LeanPool.CoarseGraining.Homogenization.Probability.LocalEllipticitySlices
import LeanPool.CoarseGraining.Homogenization.Probability.LocalObservable
import LeanPool.CoarseGraining.Homogenization.Probability.RandomFieldMeasurability
import Mathlib.Analysis.Normed.Lp.SmoothApprox
import Mathlib.Geometry.Manifold.ContMDiff.NormedSpace
import Mathlib.Geometry.Manifold.PartitionOfUnity
import Mathlib.MeasureTheory.Function.UniformIntegrable

/-! # Lipschitz Bounds -/

namespace Homogenization

open scoped Manifold
open scoped ENNReal
open scoped Topology
open Filter

/-!
# Audit tag (Ch4 rebuild contract `CH04_REBUILD_SURFACE_2026-05-16.md`)

**Internal claim:** Borel/Lipschitz measurability of fixed-coefficient maps
`HilbertMat d → block-coefficient entry` — the finite-dimensional nonlinear
atoms behind the bounded-elliptic Nemytskii step used to lift local scalar
atoms into measurable energy approximants.

**Consumed by (within `Internal/FixedCompetitorEnergyMeasurability/`):**
`Integrals.lean`. Upstream chain continues to `Theorems/Mu.lean ::
aemeasurable_Mu_cubeSet`.

If the single-claim summary above grows into three or more distinct
claims, split or refactor per the rebuild contract.
-/

/-- A single full-block coefficient entry is a Borel function of the finite
Hilbert-matrix coefficient value.  This is the finite-dimensional nonlinear
atom behind the later bounded elliptic Nemytskii step. -/
theorem measurable_fullBlockCoeffEntry_hilbertMat {d : ℕ} (α β : BlockCoord d) :
    Measurable fun A : HilbertMat d =>
      toFullBlockMat (blockMatrixOfCoeff A.toMat) α β := by
  have hA : Measurable fun A : HilbertMat d => A.toMat :=
    (HilbertMat.continuousLinearEquivMat d).continuous.measurable
  have hblock :
      Measurable (fun A : HilbertMat d => fun α β =>
        toFullBlockMat (blockMatrixOfCoeff A.toMat) α β) :=
    measurable_toFullBlockMat_blockCoeffField hA
  exact measurable_pi_iff.1 (measurable_pi_iff.1 hblock α) β

/-- The quantitative ellipticity value set for Hilbert-matrix representatives
on the `k`-th slice.  A coefficient field in `QuantitativeEllipticSlice U k`
takes values in this set for `volumeMeasureOn U`-almost every point. -/
def quantitativeEllipticHilbertMatSet (d : ℕ) (k : ℕ) : Set (HilbertMat d) :=
  {A | IsEllipticMatrix ((k + 1 : ℝ)⁻¹) (k + 1 : ℝ) A.toMat}

private theorem abs_symmPart_toMat_sub_le_norm {d : ℕ} (A B : HilbertMat d)
    (i j : Fin d) :
    |symmPart A.toMat i j - symmPart B.toMat i j| ≤ ‖A - B‖ := by
  have hij := HilbertMat.abs_apply_sub_apply_le_norm A B i j
  have hji := HilbertMat.abs_apply_sub_apply_le_norm A B j i
  have htri :
      |(A i j - B i j) + (A j i - B j i)| ≤ 2 * ‖A - B‖ := by
    calc
      |(A i j - B i j) + (A j i - B j i)|
          ≤ |A i j - B i j| + |A j i - B j i| := abs_add_le _ _
      _ ≤ ‖A - B‖ + ‖A - B‖ := add_le_add hij hji
      _ = 2 * ‖A - B‖ := by ring
  have hentry :
      symmPart A.toMat i j - symmPart B.toMat i j =
        ((A i j - B i j) + (A j i - B j i)) / 2 := by
    simp [symmPart, HilbertMat.toMat]
    ring
  calc
    |symmPart A.toMat i j - symmPart B.toMat i j|
        = |((A i j - B i j) + (A j i - B j i)) / 2| := by rw [hentry]
    _ = |(A i j - B i j) + (A j i - B j i)| / 2 := by
      rw [abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
    _ ≤ (2 * ‖A - B‖) / 2 :=
      div_le_div_of_nonneg_right htri (by norm_num)
    _ = ‖A - B‖ := by ring

private theorem abs_skewPart_toMat_sub_le_norm {d : ℕ} (A B : HilbertMat d)
    (i j : Fin d) :
    |skewPart A.toMat i j - skewPart B.toMat i j| ≤ ‖A - B‖ := by
  have hij := HilbertMat.abs_apply_sub_apply_le_norm A B i j
  have hji := HilbertMat.abs_apply_sub_apply_le_norm A B j i
  have htri :
      |(A i j - B i j) - (A j i - B j i)| ≤ 2 * ‖A - B‖ := by
    calc
      |(A i j - B i j) - (A j i - B j i)|
          ≤ |A i j - B i j| + |-(A j i - B j i)| := by
            simpa [sub_eq_add_neg] using
              abs_add_le (A i j - B i j) (-(A j i - B j i))
      _ = |A i j - B i j| + |A j i - B j i| := by rw [abs_neg]
      _ ≤ ‖A - B‖ + ‖A - B‖ := add_le_add hij hji
      _ = 2 * ‖A - B‖ := by ring
  have hentry :
      skewPart A.toMat i j - skewPart B.toMat i j =
        ((A i j - B i j) - (A j i - B j i)) / 2 := by
    simp [skewPart, HilbertMat.toMat]
    ring
  calc
    |skewPart A.toMat i j - skewPart B.toMat i j|
        = |((A i j - B i j) - (A j i - B j i)) / 2| := by rw [hentry]
    _ = |(A i j - B i j) - (A j i - B j i)| / 2 := by
      rw [abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
    _ ≤ (2 * ‖A - B‖) / 2 :=
      div_le_div_of_nonneg_right htri (by norm_num)
    _ = ‖A - B‖ := by ring

private theorem abs_skewPart_toMat_le_of_mem_quantitative
    {d : ℕ} {k : ℕ} {A : HilbertMat d}
    (hA : A ∈ quantitativeEllipticHilbertMatSet d k) (i j : Fin d) :
    |skewPart A.toMat i j| ≤ (k + 1 : ℝ) := by
  have hij := abs_apply_le_of_isEllipticMatrix hA i j
  have hji := abs_apply_le_of_isEllipticMatrix hA j i
  have htri : |A i j - A j i| ≤ 2 * (k + 1 : ℝ) := by
    calc
      |A i j - A j i| ≤ |A i j| + |A j i| := by
        simpa [sub_eq_add_neg] using abs_add_le (A i j) (-(A j i))
      _ ≤ (k + 1 : ℝ) + (k + 1 : ℝ) := add_le_add hij hji
      _ = 2 * (k + 1 : ℝ) := by ring
  have hentry : skewPart A.toMat i j = (A i j - A j i) / 2 := by
    simp [skewPart, HilbertMat.toMat]
  calc
    |skewPart A.toMat i j| = |(A i j - A j i) / 2| := by rw [hentry]
    _ = |A i j - A j i| / 2 := by
      rw [abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
    _ ≤ (2 * (k + 1 : ℝ)) / 2 :=
      div_le_div_of_nonneg_right htri (by norm_num)
    _ = (k + 1 : ℝ) := by ring

private theorem abs_symmPartInv_toMat_sub_le_norm_of_mem_quantitative
    {d : ℕ} {k : ℕ} {A B : HilbertMat d}
    (hA : A ∈ quantitativeEllipticHilbertMatSet d k)
    (hB : B ∈ quantitativeEllipticHilbertMatSet d k) (i j : Fin d) :
    |((symmPart A.toMat)⁻¹ : Mat d) i j - ((symmPart B.toMat)⁻¹ : Mat d) i j| ≤
      ((d : ℝ) ^ 2 * (((k + 1 : ℝ)⁻¹)⁻¹) ^ 2) * ‖A - B‖ := by
  let lam : ℝ := ((k + 1 : ℝ)⁻¹)
  let S : Mat d := symmPart A.toMat
  let T : Mat d := symmPart B.toMat
  have hSunit : IsUnit S := isUnit_symmPart_of_isEllipticMatrix hA
  have hTunit : IsUnit T := isUnit_symmPart_of_isEllipticMatrix hB
  have hunit_iff : IsUnit S ↔ IsUnit T := ⟨fun _ => hTunit, fun _ => hSunit⟩
  have hSinv_bound :
      ∀ p : Fin d, |(S⁻¹ : Mat d) i p| ≤ lam⁻¹ := by
    intro p
    simpa [S, lam] using abs_apply_symmPartInv_le_of_isEllipticMatrix hA i p
  have hTinv_bound :
      ∀ q : Fin d, |(T⁻¹ : Mat d) q j| ≤ lam⁻¹ := by
    intro q
    simpa [T, lam] using abs_apply_symmPartInv_le_of_isEllipticMatrix hB q j
  have hmid_bound :
      ∀ p q : Fin d, |(T - S) p q| ≤ ‖A - B‖ := by
    intro p q
    simpa [S, T, abs_sub_comm] using abs_symmPart_toMat_sub_le_norm A B p q
  calc
    |((symmPart A.toMat)⁻¹ : Mat d) i j - ((symmPart B.toMat)⁻¹ : Mat d) i j|
        = |(S⁻¹ - T⁻¹ : Mat d) i j| := by simp [S, T]
    _ = |(S⁻¹ * (T - S) * T⁻¹ : Mat d) i j| := by
      rw [Matrix.inv_sub_inv hunit_iff]
    _ ≤ ∑ p : Fin d, ∑ q : Fin d,
        |(S⁻¹ : Mat d) i q * (T - S) q p * (T⁻¹ : Mat d) p j| := by
      rw [Matrix.mul_apply]
      refine le_trans
        (Finset.abs_sum_le_sum_abs
          (fun p : Fin d => (S⁻¹ * (T - S) : Mat d) i p * (T⁻¹ : Mat d) p j)
          Finset.univ) ?_
      refine Finset.sum_le_sum ?_
      intro p _
      rw [Matrix.mul_apply]
      calc
        |(∑ q : Fin d, (S⁻¹ : Mat d) i q * (T - S) q p) * (T⁻¹ : Mat d) p j|
            = |∑ q : Fin d, (S⁻¹ : Mat d) i q * (T - S) q p| *
                |(T⁻¹ : Mat d) p j| := by
              rw [abs_mul]
        _ ≤ (∑ q : Fin d, |(S⁻¹ : Mat d) i q * (T - S) q p|) *
              |(T⁻¹ : Mat d) p j| := by
              exact mul_le_mul_of_nonneg_right
                (Finset.abs_sum_le_sum_abs
                  (fun q : Fin d => (S⁻¹ : Mat d) i q * (T - S) q p) Finset.univ)
                (abs_nonneg _)
        _ = ∑ q : Fin d,
              |(S⁻¹ : Mat d) i q * (T - S) q p| * |(T⁻¹ : Mat d) p j| := by
              rw [← Finset.sum_mul]
        _ = ∑ q : Fin d,
              |(S⁻¹ : Mat d) i q * (T - S) q p * (T⁻¹ : Mat d) p j| := by
              apply Finset.sum_congr rfl
              intro q _
              rw [abs_mul]
              rw [abs_mul]
              rw [abs_mul ((S⁻¹ : Mat d) i q) ((T - S) q p)]
    _ ≤ ∑ _p : Fin d, ∑ _q : Fin d, lam⁻¹ * ‖A - B‖ * lam⁻¹ := by
      refine Finset.sum_le_sum ?_
      intro p _
      refine Finset.sum_le_sum ?_
      intro q _
      calc
        |(S⁻¹ : Mat d) i q * (T - S) q p * (T⁻¹ : Mat d) p j|
            = |(S⁻¹ : Mat d) i q| * |(T - S) q p| * |(T⁻¹ : Mat d) p j| := by
              rw [abs_mul, abs_mul]
        _ ≤ lam⁻¹ * ‖A - B‖ * lam⁻¹ := by
          gcongr
          · exact hSinv_bound q
          · exact hmid_bound q p
          · exact hTinv_bound p
    _ = ((d : ℝ) ^ 2 * lam⁻¹ ^ 2) * ‖A - B‖ := by
      simp [Finset.card_univ, nsmul_eq_mul]
      ring
    _ = ((d : ℝ) ^ 2 * (((k + 1 : ℝ)⁻¹)⁻¹) ^ 2) * ‖A - B‖ := by
      simp [lam]

noncomputable def quantitativeSymmPartInvEntryLipschitzConstant (d k : ℕ) : NNReal :=
  Real.toNNReal ((d : ℝ) ^ 2 * (((k + 1 : ℝ)⁻¹)⁻¹) ^ 2)

noncomputable def quantitativeInvSkewProductEntryLipschitzConstant (d k : ℕ) : NNReal :=
  Real.toNNReal
    ((d : ℝ) *
      (((d : ℝ) ^ 2 * (((k + 1 : ℝ)⁻¹)⁻¹) ^ 2) * (k + 1 : ℝ) +
        (((k + 1 : ℝ)⁻¹)⁻¹)))

noncomputable def quantitativeUpperLeftEntryLipschitzConstant (d k : ℕ) : NNReal :=
  Real.toNNReal
    (1 +
      (d : ℝ) *
        (((d : ℝ) *
            (((d : ℝ) ^ 2 * (((k + 1 : ℝ)⁻¹)⁻¹) ^ 2) * (k + 1 : ℝ) +
              (((k + 1 : ℝ)⁻¹)⁻¹))) *
          (k + 1 : ℝ) +
          (d : ℝ) * (k + 1 : ℝ) * (((k + 1 : ℝ)⁻¹)⁻¹)))

theorem lipschitzOnWith_fullBlockCoeffEntry_hilbertMat_lowerRight_quantitative
    {d : ℕ} {k : ℕ} (i j : Fin d) :
    LipschitzOnWith (quantitativeSymmPartInvEntryLipschitzConstant d k)
      (fun A : HilbertMat d =>
        toFullBlockMat (blockMatrixOfCoeff A.toMat) (Sum.inr i) (Sum.inr j))
      (quantitativeEllipticHilbertMatSet d k) := by
  refine LipschitzOnWith.of_dist_le_mul ?_
  intro A hA B hB
  have hC_nonneg :
      0 ≤ (d : ℝ) ^ 2 * (((k + 1 : ℝ)⁻¹)⁻¹) ^ 2 := by positivity
  have h :=
    abs_symmPartInv_toMat_sub_le_norm_of_mem_quantitative hA hB i j
  have hC_coe :
      ((quantitativeSymmPartInvEntryLipschitzConstant d k : NNReal) : ℝ) =
        (d : ℝ) ^ 2 * (((k + 1 : ℝ)⁻¹)⁻¹) ^ 2 := by
    rw [quantitativeSymmPartInvEntryLipschitzConstant, Real.coe_toNNReal _ hC_nonneg]
  rw [Real.dist_eq, dist_eq_norm, hC_coe]
  simpa [toFullBlockMat, blockMatrixOfCoeff] using h

private theorem abs_symmPartInv_mul_skewPart_toMat_sub_le_norm_of_mem_quantitative
    {d : ℕ} {k : ℕ} {A B : HilbertMat d}
    (hA : A ∈ quantitativeEllipticHilbertMatSet d k)
    (hB : B ∈ quantitativeEllipticHilbertMatSet d k) (i j : Fin d) :
    |(((symmPart A.toMat)⁻¹ : Mat d) * skewPart A.toMat) i j -
        (((symmPart B.toMat)⁻¹ : Mat d) * skewPart B.toMat) i j| ≤
      ((d : ℝ) *
        (((d : ℝ) ^ 2 * (((k + 1 : ℝ)⁻¹)⁻¹) ^ 2) * (k + 1 : ℝ) +
          (((k + 1 : ℝ)⁻¹)⁻¹))) * ‖A - B‖ := by
  let lam : ℝ := ((k + 1 : ℝ)⁻¹)
  let Cinv : ℝ := (d : ℝ) ^ 2 * lam⁻¹ ^ 2
  let SA : Mat d := symmPart A.toMat
  let SB : Mat d := symmPart B.toMat
  let KA : Mat d := skewPart A.toMat
  let KB : Mat d := skewPart B.toMat
  have hentry :
      (SA⁻¹ * KA) i j - (SB⁻¹ * KB) i j =
        ∑ p : Fin d,
          (((SA⁻¹ : Mat d) i p - (SB⁻¹ : Mat d) i p) * KA p j +
            (SB⁻¹ : Mat d) i p * (KA p j - KB p j)) := by
    simp [Matrix.mul_apply]
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro p _
    ring
  have hterm :
      ∀ p : Fin d,
        |((SA⁻¹ : Mat d) i p - (SB⁻¹ : Mat d) i p) * KA p j +
            (SB⁻¹ : Mat d) i p * (KA p j - KB p j)| ≤
          Cinv * ‖A - B‖ * (k + 1 : ℝ) + lam⁻¹ * ‖A - B‖ := by
    intro p
    have hInvDiff :
        |(SA⁻¹ : Mat d) i p - (SB⁻¹ : Mat d) i p| ≤ Cinv * ‖A - B‖ := by
      simpa [SA, SB, Cinv, lam] using
        abs_symmPartInv_toMat_sub_le_norm_of_mem_quantitative hA hB i p
    have hSkewA : |KA p j| ≤ (k + 1 : ℝ) := by
      simpa [KA] using abs_skewPart_toMat_le_of_mem_quantitative hA p j
    have hInvB : |(SB⁻¹ : Mat d) i p| ≤ lam⁻¹ := by
      simpa [SB, lam] using abs_apply_symmPartInv_le_of_isEllipticMatrix hB i p
    have hSkewDiff : |KA p j - KB p j| ≤ ‖A - B‖ := by
      simpa [KA, KB] using abs_skewPart_toMat_sub_le_norm A B p j
    calc
      |((SA⁻¹ : Mat d) i p - (SB⁻¹ : Mat d) i p) * KA p j +
          (SB⁻¹ : Mat d) i p * (KA p j - KB p j)|
          ≤ |((SA⁻¹ : Mat d) i p - (SB⁻¹ : Mat d) i p) * KA p j| +
              |(SB⁻¹ : Mat d) i p * (KA p j - KB p j)| := abs_add_le _ _
      _ = |(SA⁻¹ : Mat d) i p - (SB⁻¹ : Mat d) i p| * |KA p j| +
              |(SB⁻¹ : Mat d) i p| * |KA p j - KB p j| := by
            rw [abs_mul, abs_mul]
      _ ≤ Cinv * ‖A - B‖ * (k + 1 : ℝ) + lam⁻¹ * ‖A - B‖ := by
            gcongr
  calc
    |(((symmPart A.toMat)⁻¹ : Mat d) * skewPart A.toMat) i j -
        (((symmPart B.toMat)⁻¹ : Mat d) * skewPart B.toMat) i j|
        = |∑ p : Fin d,
          (((SA⁻¹ : Mat d) i p - (SB⁻¹ : Mat d) i p) * KA p j +
            (SB⁻¹ : Mat d) i p * (KA p j - KB p j))| := by
          rw [hentry]
    _ ≤ ∑ p : Fin d,
        |((SA⁻¹ : Mat d) i p - (SB⁻¹ : Mat d) i p) * KA p j +
          (SB⁻¹ : Mat d) i p * (KA p j - KB p j)| :=
      Finset.abs_sum_le_sum_abs _ Finset.univ
    _ ≤ ∑ _p : Fin d, (Cinv * ‖A - B‖ * (k + 1 : ℝ) + lam⁻¹ * ‖A - B‖) := by
      exact Finset.sum_le_sum fun p _ => hterm p
    _ = ((d : ℝ) * (Cinv * (k + 1 : ℝ) + lam⁻¹)) * ‖A - B‖ := by
      simp [Finset.card_univ, nsmul_eq_mul]
      ring
    _ =
      ((d : ℝ) *
        (((d : ℝ) ^ 2 * (((k + 1 : ℝ)⁻¹)⁻¹) ^ 2) * (k + 1 : ℝ) +
          (((k + 1 : ℝ)⁻¹)⁻¹))) * ‖A - B‖ := by
      simp [Cinv, lam]

theorem lipschitzOnWith_fullBlockCoeffEntry_hilbertMat_lowerLeft_quantitative
    {d : ℕ} {k : ℕ} (i j : Fin d) :
    LipschitzOnWith (quantitativeInvSkewProductEntryLipschitzConstant d k)
      (fun A : HilbertMat d =>
        toFullBlockMat (blockMatrixOfCoeff A.toMat) (Sum.inr i) (Sum.inl j))
      (quantitativeEllipticHilbertMatSet d k) := by
  refine LipschitzOnWith.of_dist_le_mul ?_
  intro A hA B hB
  have hC_nonneg :
      0 ≤
        (d : ℝ) *
          (((d : ℝ) ^ 2 * (((k + 1 : ℝ)⁻¹)⁻¹) ^ 2) * (k + 1 : ℝ) +
            (((k + 1 : ℝ)⁻¹)⁻¹)) := by positivity
  have h :=
    abs_symmPartInv_mul_skewPart_toMat_sub_le_norm_of_mem_quantitative hA hB i j
  have hC_coe :
      ((quantitativeInvSkewProductEntryLipschitzConstant d k : NNReal) : ℝ) =
        (d : ℝ) *
          (((d : ℝ) ^ 2 * (((k + 1 : ℝ)⁻¹)⁻¹) ^ 2) * (k + 1 : ℝ) +
            (((k + 1 : ℝ)⁻¹)⁻¹)) := by
    rw [quantitativeInvSkewProductEntryLipschitzConstant,
      Real.coe_toNNReal _ hC_nonneg]
  rw [Real.dist_eq, dist_eq_norm, hC_coe]
  simp only [toFullBlockMat, blockMatrixOfCoeff]
  change |-(((symmPart A.toMat)⁻¹ : Mat d) * skewPart A.toMat) i j +
      -(-(((symmPart B.toMat)⁻¹ : Mat d) * skewPart B.toMat) i j)| ≤
    (d : ℝ) *
      (((d : ℝ) ^ 2 * (((k + 1 : ℝ)⁻¹)⁻¹) ^ 2) * (k + 1 : ℝ) +
        (((k + 1 : ℝ)⁻¹)⁻¹)) * ‖A - B‖
  convert h using 1
  rw [← abs_neg]
  congr 1
  ring

private theorem toFullBlockMat_blockMatrixOfCoeff_upperRight_eq_lowerLeft_transpose
    {d : ℕ} (A : Mat d) (i j : Fin d) :
    toFullBlockMat (blockMatrixOfCoeff A) (Sum.inl i) (Sum.inr j) =
      toFullBlockMat (blockMatrixOfCoeff A) (Sum.inr j) (Sum.inl i) := by
  have h := congrArg (fun M : Mat d => M j i) (blockMatrixOfCoeff_upperRight_transpose A)
  simpa [matTranspose, toFullBlockMat] using h

theorem lipschitzOnWith_fullBlockCoeffEntry_hilbertMat_upperRight_quantitative
    {d : ℕ} {k : ℕ} (i j : Fin d) :
    LipschitzOnWith (quantitativeInvSkewProductEntryLipschitzConstant d k)
      (fun A : HilbertMat d =>
        toFullBlockMat (blockMatrixOfCoeff A.toMat) (Sum.inl i) (Sum.inr j))
      (quantitativeEllipticHilbertMatSet d k) := by
  refine LipschitzOnWith.of_dist_le_mul ?_
  intro A hA B hB
  have hLL :=
    (lipschitzOnWith_fullBlockCoeffEntry_hilbertMat_lowerLeft_quantitative
      (k := k) j i).dist_le_mul A hA B hB
  simpa [toFullBlockMat_blockMatrixOfCoeff_upperRight_eq_lowerLeft_transpose] using hLL

private theorem abs_skewTranspose_mul_symmPartInv_toMat_le_of_mem_quantitative
    {d : ℕ} {k : ℕ} {A : HilbertMat d}
    (hA : A ∈ quantitativeEllipticHilbertMatSet d k) (i j : Fin d) :
    |(matTranspose (skewPart A.toMat) * ((symmPart A.toMat)⁻¹ : Mat d)) i j| ≤
      (d : ℝ) * (k + 1 : ℝ) * (((k + 1 : ℝ)⁻¹)⁻¹) := by
  let lam : ℝ := ((k + 1 : ℝ)⁻¹)
  let K : Mat d := skewPart A.toMat
  let SInv : Mat d := (symmPart A.toMat)⁻¹
  have hterm :
      ∀ p : Fin d, |(matTranspose K) i p * SInv p j| ≤ (k + 1 : ℝ) * lam⁻¹ := by
    intro p
    have hK : |K p i| ≤ (k + 1 : ℝ) := by
      simpa [K] using abs_skewPart_toMat_le_of_mem_quantitative hA p i
    have hS : |SInv p j| ≤ lam⁻¹ := by
      simpa [SInv, lam] using abs_apply_symmPartInv_le_of_isEllipticMatrix hA p j
    calc
      |(matTranspose K) i p * SInv p j| = |K p i| * |SInv p j| := by
        simp [matTranspose, abs_mul]
      _ ≤ (k + 1 : ℝ) * lam⁻¹ := by gcongr
  calc
    |(matTranspose (skewPart A.toMat) * ((symmPart A.toMat)⁻¹ : Mat d)) i j|
        = |∑ p : Fin d, (matTranspose K) i p * SInv p j| := by
          rw [Matrix.mul_apply]
    _ ≤ ∑ p : Fin d, |(matTranspose K) i p * SInv p j| :=
      Finset.abs_sum_le_sum_abs _ Finset.univ
    _ ≤ ∑ _p : Fin d, (k + 1 : ℝ) * lam⁻¹ := by
      exact Finset.sum_le_sum fun p _ => hterm p
    _ = (d : ℝ) * (k + 1 : ℝ) * lam⁻¹ := by
      simp [Finset.card_univ, nsmul_eq_mul]
      ring
    _ = (d : ℝ) * (k + 1 : ℝ) * (((k + 1 : ℝ)⁻¹)⁻¹) := by
      simp [lam]

private theorem abs_skewTranspose_mul_symmPartInv_toMat_sub_le_norm_of_mem_quantitative
    {d : ℕ} {k : ℕ} {A B : HilbertMat d}
    (hA : A ∈ quantitativeEllipticHilbertMatSet d k)
    (hB : B ∈ quantitativeEllipticHilbertMatSet d k) (i j : Fin d) :
    |(matTranspose (skewPart A.toMat) * ((symmPart A.toMat)⁻¹ : Mat d)) i j -
        (matTranspose (skewPart B.toMat) * ((symmPart B.toMat)⁻¹ : Mat d)) i j| ≤
      ((d : ℝ) *
        (((d : ℝ) ^ 2 * (((k + 1 : ℝ)⁻¹)⁻¹) ^ 2) * (k + 1 : ℝ) +
          (((k + 1 : ℝ)⁻¹)⁻¹))) * ‖A - B‖ := by
  have hC_nonneg :
      0 ≤
        (d : ℝ) *
          (((d : ℝ) ^ 2 * (((k + 1 : ℝ)⁻¹)⁻¹) ^ 2) * (k + 1 : ℝ) +
            (((k + 1 : ℝ)⁻¹)⁻¹)) := by positivity
  have hC_coe :
      ((quantitativeInvSkewProductEntryLipschitzConstant d k : NNReal) : ℝ) =
        (d : ℝ) *
          (((d : ℝ) ^ 2 * (((k + 1 : ℝ)⁻¹)⁻¹) ^ 2) * (k + 1 : ℝ) +
            (((k + 1 : ℝ)⁻¹)⁻¹)) := by
    rw [quantitativeInvSkewProductEntryLipschitzConstant,
      Real.coe_toNNReal _ hC_nonneg]
  have hUR :=
    (lipschitzOnWith_fullBlockCoeffEntry_hilbertMat_upperRight_quantitative
      (k := k) i j).dist_le_mul A hA B hB
  rw [Real.dist_eq, dist_eq_norm, hC_coe] at hUR
  simp only [toFullBlockMat, blockMatrixOfCoeff] at hUR
  rw [show
      (-(matTranspose (skewPart A.toMat) * ((symmPart A.toMat)⁻¹ : Mat d))) i j =
        -((matTranspose (skewPart A.toMat) * ((symmPart A.toMat)⁻¹ : Mat d)) i j) by rfl,
    show
      (-(matTranspose (skewPart B.toMat) * ((symmPart B.toMat)⁻¹ : Mat d))) i j =
        -((matTranspose (skewPart B.toMat) * ((symmPart B.toMat)⁻¹ : Mat d)) i j) by rfl] at hUR
  convert hUR using 1
  rw [← abs_neg]
  congr 1
  ring

private theorem abs_upperLeft_toMat_sub_le_norm_of_mem_quantitative
    {d : ℕ} {k : ℕ} {A B : HilbertMat d}
    (hA : A ∈ quantitativeEllipticHilbertMatSet d k)
    (hB : B ∈ quantitativeEllipticHilbertMatSet d k) (i j : Fin d) :
    |(blockMatrixOfCoeff A.toMat).upperLeft i j -
        (blockMatrixOfCoeff B.toMat).upperLeft i j| ≤
      (1 +
        (d : ℝ) *
          (((d : ℝ) *
              (((d : ℝ) ^ 2 * (((k + 1 : ℝ)⁻¹)⁻¹) ^ 2) * (k + 1 : ℝ) +
                (((k + 1 : ℝ)⁻¹)⁻¹))) *
            (k + 1 : ℝ) +
            (d : ℝ) * (k + 1 : ℝ) * (((k + 1 : ℝ)⁻¹)⁻¹))) * ‖A - B‖ := by
  let lam : ℝ := ((k + 1 : ℝ)⁻¹)
  let Cinv : ℝ := (d : ℝ) ^ 2 * lam⁻¹ ^ 2
  let Cprod : ℝ := (d : ℝ) * (Cinv * (k + 1 : ℝ) + lam⁻¹)
  let Hbound : ℝ := (d : ℝ) * (k + 1 : ℝ) * lam⁻¹
  let Ctriple : ℝ := (d : ℝ) * (Cprod * (k + 1 : ℝ) + Hbound)
  let SA : Mat d := symmPart A.toMat
  let SB : Mat d := symmPart B.toMat
  let HA : Mat d := matTranspose (skewPart A.toMat) * ((symmPart A.toMat)⁻¹ : Mat d)
  let HB : Mat d := matTranspose (skewPart B.toMat) * ((symmPart B.toMat)⁻¹ : Mat d)
  let KA : Mat d := skewPart A.toMat
  let KB : Mat d := skewPart B.toMat
  have hProdEntry :
      (HA * KA) i j - (HB * KB) i j =
        ∑ p : Fin d,
          ((HA i p - HB i p) * KA p j + HB i p * (KA p j - KB p j)) := by
    simp [Matrix.mul_apply]
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro p _
    ring
  have hterm :
      ∀ p : Fin d,
        |(HA i p - HB i p) * KA p j + HB i p * (KA p j - KB p j)| ≤
          Cprod * ‖A - B‖ * (k + 1 : ℝ) + Hbound * ‖A - B‖ := by
    intro p
    have hHDiff : |HA i p - HB i p| ≤ Cprod * ‖A - B‖ := by
      simpa [HA, HB, Cprod, Cinv, lam] using
        abs_skewTranspose_mul_symmPartInv_toMat_sub_le_norm_of_mem_quantitative hA hB i p
    have hSkewA : |KA p j| ≤ (k + 1 : ℝ) := by
      simpa [KA] using abs_skewPart_toMat_le_of_mem_quantitative hA p j
    have hHB : |HB i p| ≤ Hbound := by
      simpa [HB, Hbound, lam] using
        abs_skewTranspose_mul_symmPartInv_toMat_le_of_mem_quantitative hB i p
    have hSkewDiff : |KA p j - KB p j| ≤ ‖A - B‖ := by
      simpa [KA, KB] using abs_skewPart_toMat_sub_le_norm A B p j
    calc
      |(HA i p - HB i p) * KA p j + HB i p * (KA p j - KB p j)|
          ≤ |(HA i p - HB i p) * KA p j| +
              |HB i p * (KA p j - KB p j)| := abs_add_le _ _
      _ = |HA i p - HB i p| * |KA p j| +
            |HB i p| * |KA p j - KB p j| := by
          rw [abs_mul, abs_mul]
      _ ≤ Cprod * ‖A - B‖ * (k + 1 : ℝ) + Hbound * ‖A - B‖ := by
          gcongr
  have hTriple :
      |(HA * KA) i j - (HB * KB) i j| ≤ Ctriple * ‖A - B‖ := by
    calc
      |(HA * KA) i j - (HB * KB) i j|
          = |∑ p : Fin d,
              ((HA i p - HB i p) * KA p j + HB i p * (KA p j - KB p j))| := by
            rw [hProdEntry]
      _ ≤ ∑ p : Fin d,
            |(HA i p - HB i p) * KA p j + HB i p * (KA p j - KB p j)| :=
        Finset.abs_sum_le_sum_abs _ Finset.univ
      _ ≤ ∑ _p : Fin d, (Cprod * ‖A - B‖ * (k + 1 : ℝ) + Hbound * ‖A - B‖) := by
        exact Finset.sum_le_sum fun p _ => hterm p
      _ = Ctriple * ‖A - B‖ := by
        simp [Ctriple, Finset.card_univ, nsmul_eq_mul]
        ring
  have hSymm : |SA i j - SB i j| ≤ ‖A - B‖ := by
    simpa [SA, SB] using abs_symmPart_toMat_sub_le_norm A B i j
  have hEntry :
      (blockMatrixOfCoeff A.toMat).upperLeft i j -
          (blockMatrixOfCoeff B.toMat).upperLeft i j =
        (SA i j - SB i j) + ((HA * KA) i j - (HB * KB) i j) := by
    simp [blockMatrixOfCoeff, SA, SB, HA, HB, KA, KB]
    ring
  calc
    |(blockMatrixOfCoeff A.toMat).upperLeft i j -
        (blockMatrixOfCoeff B.toMat).upperLeft i j|
        = |(SA i j - SB i j) + ((HA * KA) i j - (HB * KB) i j)| := by
          rw [hEntry]
    _ ≤ |SA i j - SB i j| + |(HA * KA) i j - (HB * KB) i j| :=
      abs_add_le _ _
    _ ≤ ‖A - B‖ + Ctriple * ‖A - B‖ := add_le_add hSymm hTriple
    _ = (1 + Ctriple) * ‖A - B‖ := by ring
    _ =
      (1 +
        (d : ℝ) *
          (((d : ℝ) *
              (((d : ℝ) ^ 2 * (((k + 1 : ℝ)⁻¹)⁻¹) ^ 2) * (k + 1 : ℝ) +
                (((k + 1 : ℝ)⁻¹)⁻¹))) *
            (k + 1 : ℝ) +
            (d : ℝ) * (k + 1 : ℝ) * (((k + 1 : ℝ)⁻¹)⁻¹))) * ‖A - B‖ := by
      simp [Ctriple, Cprod, Cinv, Hbound, lam]

theorem lipschitzOnWith_fullBlockCoeffEntry_hilbertMat_upperLeft_quantitative
    {d : ℕ} {k : ℕ} (i j : Fin d) :
    LipschitzOnWith (quantitativeUpperLeftEntryLipschitzConstant d k)
      (fun A : HilbertMat d =>
        toFullBlockMat (blockMatrixOfCoeff A.toMat) (Sum.inl i) (Sum.inl j))
      (quantitativeEllipticHilbertMatSet d k) := by
  refine LipschitzOnWith.of_dist_le_mul ?_
  intro A hA B hB
  have hC_nonneg :
      0 ≤
        1 +
          (d : ℝ) *
            (((d : ℝ) *
                (((d : ℝ) ^ 2 * (((k + 1 : ℝ)⁻¹)⁻¹) ^ 2) * (k + 1 : ℝ) +
                  (((k + 1 : ℝ)⁻¹)⁻¹))) *
              (k + 1 : ℝ) +
              (d : ℝ) * (k + 1 : ℝ) * (((k + 1 : ℝ)⁻¹)⁻¹)) := by positivity
  have h :=
    abs_upperLeft_toMat_sub_le_norm_of_mem_quantitative hA hB i j
  have hC_coe :
      ((quantitativeUpperLeftEntryLipschitzConstant d k : NNReal) : ℝ) =
        1 +
          (d : ℝ) *
            (((d : ℝ) *
                (((d : ℝ) ^ 2 * (((k + 1 : ℝ)⁻¹)⁻¹) ^ 2) * (k + 1 : ℝ) +
                  (((k + 1 : ℝ)⁻¹)⁻¹))) *
              (k + 1 : ℝ) +
              (d : ℝ) * (k + 1 : ℝ) * (((k + 1 : ℝ)⁻¹)⁻¹)) := by
    rw [quantitativeUpperLeftEntryLipschitzConstant, Real.coe_toNNReal _ hC_nonneg]
  rw [Real.dist_eq, dist_eq_norm, hC_coe]
  simpa [toFullBlockMat] using h

noncomputable def quantitativeFullBlockCoeffEntryLipschitzConstant
    (d k : ℕ) (α β : BlockCoord d) : NNReal :=
  match α, β with
  | Sum.inl _, Sum.inl _ => quantitativeUpperLeftEntryLipschitzConstant d k
  | Sum.inl _, Sum.inr _ => quantitativeInvSkewProductEntryLipschitzConstant d k
  | Sum.inr _, Sum.inl _ => quantitativeInvSkewProductEntryLipschitzConstant d k
  | Sum.inr _, Sum.inr _ => quantitativeSymmPartInvEntryLipschitzConstant d k

theorem lipschitzOnWith_fullBlockCoeffEntry_hilbertMat_quantitative
    {d : ℕ} {k : ℕ} (α β : BlockCoord d) :
    LipschitzOnWith (quantitativeFullBlockCoeffEntryLipschitzConstant d k α β)
      (fun A : HilbertMat d => toFullBlockMat (blockMatrixOfCoeff A.toMat) α β)
      (quantitativeEllipticHilbertMatSet d k) := by
  cases α with
  | inl i =>
      cases β with
      | inl j =>
          simpa [quantitativeFullBlockCoeffEntryLipschitzConstant] using
            lipschitzOnWith_fullBlockCoeffEntry_hilbertMat_upperLeft_quantitative
              (k := k) i j
      | inr j =>
          simpa [quantitativeFullBlockCoeffEntryLipschitzConstant] using
            lipschitzOnWith_fullBlockCoeffEntry_hilbertMat_upperRight_quantitative
              (k := k) i j
  | inr i =>
      cases β with
      | inl j =>
          simpa [quantitativeFullBlockCoeffEntryLipschitzConstant] using
            lipschitzOnWith_fullBlockCoeffEntry_hilbertMat_lowerLeft_quantitative
              (k := k) i j
      | inr j =>
          simpa [quantitativeFullBlockCoeffEntryLipschitzConstant] using
            lipschitzOnWith_fullBlockCoeffEntry_hilbertMat_lowerRight_quantitative
              (k := k) i j

end Homogenization
