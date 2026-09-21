/-
Copyright (c) 2026 Anastasios Fragkos. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anastasios Fragkos
-/

import LeanPool.QuadraticCarleson.QuadraticCarleson.KrauseLaceyFullDyadicSparseTransfer
import LeanPool.QuadraticCarleson.QuadraticCarleson.KrauseLaceyThreeShiftMaximalAction

/-!
# The positive finite suffix maximum through three shifted forests

The moving-lower-cutoff positive dyadic suffix used by the smooth sparse
transfer is exactly a physical tail of a finite three-shift global family.
The top scale is `j + N - 1`, depths are `range N`, and suffix `m` has the
physical lower cutoff `j + m + 2`. In particular the complete maximum starts
at `j + 2`. The empty case is included: when `N = 0`, both sides are zero.
-/

open Function MeasureTheory Set
open scoped ENNReal NNReal

namespace QuadraticCarleson
namespace KrauseLaceyPositiveSuffixThreeShift

open KrauseLaceyFullDyadicReflection KrauseLaceyFullDyadicSparseTransfer
open KrauseLaceyStoppingRecursion KrauseLaceyThreeShiftGrid


/-- The physical tail at `j + m + 2` of the reversed depth family is exactly
the consecutive positive suffix beginning at scale `j + m`. This includes
`m = N`, where both sums are empty. -/
theorem finitePositiveGlobalTail_eq_positiveDyadicSuffix
    (f : L0Infinity) (j : ℤ) (N m : ℕ) (hm : m ≤ N) (x : ℝ) :
    finitePositiveGlobalTail (j + (N : ℤ) - 1) (Finset.range N) f
      (j + (m : ℤ) + 2) x =
      finitePositiveDyadicSuffix 1 j N m f x := by
  let F : ℕ → ℂ := fun depth ↦ ∫ t,
    annularQuadraticKernel
      (positiveDyadicAmplitude (j + (N : ℤ) - 1 - (depth : ℤ))) 1 (x - t) * f t
  have hcut (depth : ℕ) :
      ((2 : ℝ) ^ (j + (m : ℤ) + 2) ≤
        (2 : ℝ) ^ (j + (N : ℤ) - 1 - (depth : ℤ) + 2)) ↔ depth < N - m := by
    rw [zpow_le_zpow_iff_right₀ (by norm_num : (1 : ℝ) < 2)]
    omega
  have hglobal : finitePositiveGlobalTail (j + (N : ℤ) - 1) (Finset.range N) f
      (j + (m : ℤ) + 2) x = ∑ depth ∈ Finset.range (N - m), F depth := by
    unfold finitePositiveGlobalTail
    rw [← Finset.sum_filter]
    congr 1
    ext depth
    simp only [Finset.mem_filter, Finset.mem_range, hcut]
    omega
  rw [hglobal]
  unfold finitePositiveDyadicSuffix finitePositiveDyadicTail positiveDyadicConvolution
  rw [← Finset.sum_range_reflect]
  apply Finset.sum_congr rfl
  intro depth hdepth
  have hd : depth < N - m := Finset.mem_range.mp hdepth
  have hpositive : 0 < N - m := (Nat.zero_le depth).trans_lt hd
  have hcast : ((N - m - 1 : ℕ) : ℤ) = (N - m : ℤ) - 1 := by omega
  have hrevcast : ((N - m - 1 - depth : ℕ) : ℤ) =
      ((N - m - 1 : ℕ) : ℤ) - (depth : ℤ) := by omega
  have hscale : j + (N : ℤ) - 1 -
      ((N - m - 1 : ℕ) : ℤ) + (depth : ℤ) = j + (m : ℤ) + (depth : ℤ) := by
    rw [hcast]
    omega
  dsimp [F]
  rw [hrevcast]
  have hscale' : j + (N : ℤ) - 1 -
      (((N - m - 1 : ℕ) : ℤ) - (depth : ℤ)) =
        j + (m : ℤ) + (depth : ℤ) := by
    linarith [hscale]
  congr 1
  funext t
  rw [hscale']

/-- The actual finite positive suffix maximal test operator is pointwise
controlled by the finite global positive-tail maximum with exactly the
source lower cutoff `j + 2`. -/
theorem enorm_finitePositiveDyadicSuffixMaxOperator_le_globalTailMaximal
    (j : ℤ) (N : ℕ) (f : L0Infinity) (x : ℝ) :
    ‖finitePositiveDyadicSuffixMaxOperator 1 j N f x‖ₑ ≤
      finitePositiveGlobalTailMaximal (j + 2) (j + (N : ℤ) - 1)
        (Finset.range N) f x := by
  have hnorm : ‖finitePositiveDyadicSuffixMaxOperator 1 j N f x‖ₑ =
      (finitePositiveDyadicSuffixMaxNNNorm 1 j N f x : ℝ≥0∞) := by
    unfold finitePositiveDyadicSuffixMaxOperator
    rw [← ofReal_norm]
    simp
  rw [hnorm]
  unfold finitePositiveDyadicSuffixMaxNNNorm
  rw [ENNReal.coe_finset_sup]
  apply Finset.sup_le
  intro m hm
  change ‖finitePositiveDyadicSuffix 1 j N m f x‖ₑ ≤ _
  have hmN : m ≤ N := Nat.le_of_lt_succ (Finset.mem_range.mp hm)
  rw [← finitePositiveGlobalTail_eq_positiveDyadicSuffix f j N m hmN x]
  exact le_iSup
    (fun ell : {ell : ℤ // j + 2 ≤ ell} ↦
      ‖finitePositiveGlobalTail (j + (N : ℤ) - 1) (Finset.range N) f ell.1 x‖ₑ)
    ⟨j + (m : ℤ) + 2, by omega⟩

/-- A concrete three-shift and parent-closed-forest reduction for the unit
positive finite suffix operator. No sparse estimate is assumed: the result
is only the exact geometric/operator reduction needed before the local KL
stopping argument. -/
theorem exists_threeShiftForests_finitePositiveDyadicSuffixMax
    (j : ℤ) (N : ℕ) (f : L0Infinity) :
    ∃ E : ℕ → Finset ℤ,
      (∀ shift,
        finiteOneShiftMultiscaleFamily (j + (N : ℤ) - 1) (Finset.range N) E shift ⊆
          completeFiniteShiftGridForest (j + (N : ℤ) - 1) shift N
            (finiteOneShiftMultiscaleAddresses (Finset.range N) E shift)) ∧
      ∀ x,
        ‖finitePositiveDyadicSuffixMaxOperator 1 j N f x‖ₑ ≤
          ∑ shift : Fin 3,
            localizedTailMaximal (j + 2)
              (finiteShiftGridScale (j + (N : ℤ) - 1) shift)
              (finiteOneShiftMultiscaleFamily (j + (N : ℤ) - 1)
                (Finset.range N) E shift) f x := by
  obtain ⟨E, hforest, hmax⟩ :=
    exists_threeShiftForests_globalTailMaximal f (j + 2) (j + (N : ℤ) - 1)
      (Finset.range N) N (fun depth hdepth ↦ Nat.le_of_lt (Finset.mem_range.mp hdepth))
  refine ⟨E, hforest, fun x ↦ ?_⟩
  exact (enorm_finitePositiveDyadicSuffixMaxOperator_le_globalTailMaximal j N f x).trans
    (hmax x)


end KrauseLaceyPositiveSuffixThreeShift
end QuadraticCarleson
