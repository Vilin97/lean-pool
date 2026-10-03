/-
Copyright (c) 2026 Anastasios Fragkos. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anastasios Fragkos
-/
module


public import LeanPool.QuadraticCarleson.QuadraticCarleson.KrauseLaceyScaleOffsetPointwise

/-!
# Smooth cutoffs in the normalized oscillatory range

The paper's finite height blocks have normalized smooth radii at least
`1/8`. Upward rounding places those radii in the dyadic maximum starting
at scale `1`. Rounding in physical coordinates keeps its maximal-function
error common across all modulations.
-/

@[expose] public section

open Function MeasureTheory Set
open scoped ENNReal NNReal

namespace QuadraticCarleson.KrauseLaceyUnitSmoothHighReduction

open KrauseLaceySharpSmoothAdapter KrauseLaceyFullDyadicReflection
open KrauseLaceyFullDyadicSparseTransfer KrauseLaceyCompactPairingStabilization
open KrauseLaceyScaleOffsetPointwise KrauseLaceySparseDilation


noncomputable
section

/-- Raising the first allowed scale reduces the smooth suffix maximum. -/
theorem dyadicSmoothHighPassMaxEnorm_antitone_start
    (lam : ℝ) {i j : ℤ} (hij : i ≤ j) (f : L0Infinity) (x : ℝ) :
    dyadicSmoothHighPassMaxEnorm lam j f x ≤
      dyadicSmoothHighPassMaxEnorm lam i f x := by
  apply iSup_le
  intro m
  let n : ℕ := (j - i).toNat + m
  have hn : i + (n : ℤ) = j + (m : ℤ) := by
    dsimp [n]
    rw [Int.toNat_of_nonneg (sub_nonneg.mpr hij)]
    omega
  change ‖smoothQuadraticHighPass lam ((2 : ℝ) ^ (j + (m : ℤ) - 3)) f x‖ₑ ≤ _
  rw [← hn]
  exact le_iSup (fun r : ℕ ↦
    ‖smoothQuadraticHighPass lam ((2 : ℝ) ^ (i + (r : ℤ) - 3)) f x‖ₑ) n

/-- Upward rounding of a normalized radius at least `1/8` starts in the
high range of the checked Krause--Lacey estimate. -/
theorem one_le_roundedScale {ρ : ℝ} (hρ : 0 < ρ) (hmin : 1 / 8 ≤ ρ) :
    1 ≤ dyadicFloorScale ρ hρ + 4 := by
  have hpow : (2 : ℝ) ^ (-3 : ℤ) <
      (2 : ℝ) ^ (dyadicFloorScale ρ hρ + 1) := by
    have h := hmin.trans_lt (dyadicFloorScale_bounds ρ hρ).2
    norm_num at h ⊢
    exact h
  have hidx := (zpow_lt_zpow_iff_right₀ (by norm_num : (1 : ℝ) < 2)).mp hpow
  omega

/-- Every such rounded cutoff is already one of the allowed high cutoffs. -/
theorem enorm_roundedSmooth_le_highMax {ρ : ℝ} (hρ : 0 < ρ)
    (hmin : 1 / 8 ≤ ρ) (f : L0Infinity) (x : ℝ) :
    ‖smoothQuadraticHighPass 1 (dyadicCeilRadius ρ hρ) f x‖ₑ ≤
      dyadicSmoothHighPassMaxEnorm 1 1 f x := by
  have hi := one_le_roundedScale hρ hmin
  let m : ℕ := (dyadicFloorScale ρ hρ + 4 - 1).toNat
  have hm : 1 + (m : ℤ) = dyadicFloorScale ρ hρ + 4 := by
    dsimp [m]
    rw [Int.toNat_of_nonneg (by omega)]
    omega
  rw [dyadicCeilRadius_eq_two_pow_scale_sub_three, ← hm]
  exact le_iSup (fun r : ℕ ↦
    ‖smoothQuadraticHighPass 1 ((2 : ℝ) ^ (1 + (r : ℤ) - 3)) f x‖ₑ) m


end
end QuadraticCarleson.KrauseLaceyUnitSmoothHighReduction
