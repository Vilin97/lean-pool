/-
Copyright (c) 2026 Yuma Mizuno. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuma Mizuno
-/
module


public import LeanPool.MarkoffModP.BGS.HasseWeil.ConstantExtensionClosedPlaceSplittingFormula
public import LeanPool.MarkoffModP.BGS.HasseWeil.FiniteExtensionHasseBoundFromEvenConstantExtensions

/-!
# Divisible-even errors from one enlarged constant field

Let `F / K(X)` have exact constant field `K`, and let `C / K` be finite
Galois of degree `r`.  Exact constant-extension splitting identifies the
closed-place count of `C F` at level `m` with the count of `F` at level
`r m`.  Since `#C = (#K)^r`, a square-root-scale estimate for `C F` along
the levels `2 H n` is therefore exactly such an estimate for `F` along the
fixed divisible-even subsequence `2 (r H) n`.
-/

@[expose] public section

namespace BGS.HasseWeil

noncomputable section

open Filter Asymptotics


variable (K C F : Type*)
  [Field K] [Fintype K] [DecidableEq K] [DecidableEq (RatFunc K)]
  [Field C] [Fintype C] [Algebra K C]
  [FiniteDimensional K C] [IsGalois K C]
  [Field F] [Algebra (RatFunc K) F]
  [FiniteDimensional (RatFunc K) F]
  [Algebra.IsSeparable (RatFunc K) F]

local instance divisibleErrorBaseConstantAlgebra : Algebra K F :=
  bridgeBaseConstantAlgebra K F

local instance divisibleErrorBaseConstantTower :
    IsScalarTower K (RatFunc K) F :=
  IsScalarTower.of_algebraMap_eq' rfl

/-- Pointwise error transport from the scalar extension `C F` to `F`.
The multiplier `r H`, where `r = [C : K]`, is independent of `n`. -/
theorem finiteExtensionClosedPlace_divisibleEvenError_bound_of_constantBase
    (hExact : algebraicClosure K F =
      (⊥ : IntermediateField K F))
    (H : ℕ) (A B : ℝ)
    (hbound : ∀ n, 0 < n →
      |(exactConstantExtensionClosedPlaceExtensionCount
          K C F hExact (2 * H * n) : ℝ) -
          (Nat.card C : ℝ) ^ (2 * H * n) - 1| ≤
        A + B * (Nat.card C : ℝ) ^ (H * n)) :
    ∀ n, 0 < n →
      |(finiteExtensionClosedPlaceExtensionCount K F
          (2 * (Module.finrank K C * H) * n) : ℝ) -
          (Nat.card K : ℝ) ^
            (2 * (Module.finrank K C * H) * n) - 1| ≤
        A + B * (((Nat.card K : ℝ) ^
          (Module.finrank K C * H)) ^ n) := by
  intro n hn
  have hcount :
      exactConstantExtensionClosedPlaceExtensionCount
          K C F hExact (2 * H * n) =
        finiteExtensionClosedPlaceExtensionCount K F
          (2 * (Module.finrank K C * H) * n) := by
    rw [exactConstantExtensionClosedPlaceExtensionCount_eq_classical_decidableEq]
    have h := exactConstantExtensionClosedPlaceExtensionCount_eq
      K C F hExact (2 * H * n)
    convert h using 1
    all_goals congr 1 <;> ring
  have hcard : Nat.card C = Nat.card K ^ Module.finrank K C :=
    Module.natCard_eq_pow_finrank
  have hcenter :
      (Nat.card C : ℝ) ^ (2 * H * n) =
        (Nat.card K : ℝ) ^
          (2 * (Module.finrank K C * H) * n) := by
    rw [hcard, Nat.cast_pow]
    calc
      ((Nat.card K : ℝ) ^ Module.finrank K C) ^ (2 * H * n) =
          (Nat.card K : ℝ) ^
            (Module.finrank K C * (2 * H * n)) := by
              exact (pow_mul (Nat.card K : ℝ)
                (Module.finrank K C) (2 * H * n)).symm
      _ = (Nat.card K : ℝ) ^
          (2 * (Module.finrank K C * H) * n) := by
            congr 1
            ring
  have hscale :
      (Nat.card C : ℝ) ^ (H * n) =
        ((Nat.card K : ℝ) ^ (Module.finrank K C * H)) ^ n := by
    rw [hcard, Nat.cast_pow]
    calc
      ((Nat.card K : ℝ) ^ Module.finrank K C) ^ (H * n) =
          (Nat.card K : ℝ) ^
            (Module.finrank K C * (H * n)) := by
              exact (pow_mul (Nat.card K : ℝ)
                (Module.finrank K C) (H * n)).symm
      _ = (Nat.card K : ℝ) ^
          ((Module.finrank K C * H) * n) := by
            congr 1
            ring
      _ = ((Nat.card K : ℝ) ^
          (Module.finrank K C * H)) ^ n := by
            exact pow_mul (Nat.card K : ℝ)
              (Module.finrank K C * H) n
  have h := hbound n hn
  rw [hcount, hcenter, hscale] at h
  exact h

/-- The preceding pointwise transport immediately supplies the
divisible-even `IsBigO` premise used by the spectral Hasse argument. -/
theorem finiteExtensionClosedPlace_divisibleEvenError_isBigO_of_constantBase
    (hExact : algebraicClosure K F =
      (⊥ : IntermediateField K F))
    (H : ℕ) (A B : ℝ) (hA : 0 ≤ A)
    (hbound : ∀ n, 0 < n →
      |(exactConstantExtensionClosedPlaceExtensionCount
          K C F hExact (2 * H * n) : ℝ) -
          (Nat.card C : ℝ) ^ (2 * H * n) - 1| ≤
        A + B * (Nat.card C : ℝ) ^ (H * n)) :
    (fun n : ℕ ↦
      (finiteExtensionClosedPlaceExtensionCount K F
          (2 * (Module.finrank K C * H) * n) : ℂ) -
        (Nat.card K : ℂ) ^
          (2 * (Module.finrank K C * H) * n) - 1) =O[atTop]
      fun n : ℕ ↦
        ((Nat.card K : ℝ) ^ (Module.finrank K C * H)) ^ n := by
  apply divisibleEvenExtensionError_isBigO_of_pointwise_bound
    (Nat.card K) (Module.finrank K C * H)
      (finiteExtensionClosedPlaceExtensionCount K F) A B
      Nat.card_pos hA
  exact finiteExtensionClosedPlace_divisibleEvenError_bound_of_constantBase
    K C F hExact H A B hbound

/-- Closed Hasse--Weil over `K` from one fixed enlarged constant field.
The geometric work is isolated in `hbound`; exact splitting and the spectral
argument discharge every remaining count and zeta-function step. -/
theorem finiteExtensionClosedPlaceHasseBound_of_constantBase_bound
    (budget : ℕ)
    (hExact : algebraicClosure K F =
      (⊥ : IntermediateField K F))
    (hgenus : FunctionField.genus K F ≤ budget)
    (H : ℕ) (hH : 0 < H) (A B : ℝ) (hA : 0 ≤ A)
    (hbound : ∀ n, 0 < n →
      |(exactConstantExtensionClosedPlaceExtensionCount
          K C F hExact (2 * H * n) : ℝ) -
          (Nat.card C : ℝ) ^ (2 * H * n) - 1| ≤
        A + B * (Nat.card C : ℝ) ^ (H * n)) :
    |(finiteExtensionClosedPlaceExtensionCount K F 1 : ℝ) -
        Nat.card K - 1| ≤
      (2 * budget + 1 : ℝ) * Real.sqrt (Nat.card K) := by
  apply
    finiteExtensionClosedPlaceHasseBound_of_exactConstants_and_divisibleEvenError
      K F budget (Module.finrank K C * H) hExact hgenus
      (Nat.mul_pos Module.finrank_pos hH)
  exact
    finiteExtensionClosedPlace_divisibleEvenError_isBigO_of_constantBase
      K C F hExact H A B hA hbound

end

end BGS.HasseWeil
