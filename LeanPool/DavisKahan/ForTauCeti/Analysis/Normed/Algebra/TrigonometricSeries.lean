/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI GPT-5.6 Sol
-/
module

public import Mathlib.Analysis.Normed.Algebra.Exponential
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Series

/-!
# Trigonometric power series in Banach algebras

This module defines cosine and sine by their norm-convergent power series in an arbitrary
Banach algebra over an `RCLike` field. It also proves the supported Euler identity needed
for quarter-turn constructions:

`exp (J * T) = cosSeries T + J * sinSeries T`

under the two algebraic hypotheses `J * T = T * J` and `J * J * T = -T`.
The second hypothesis is deliberately weaker than `J * J = -1`: it allows `J` to vanish on
the kernel of `T`, as happens for polar quarter turns.
-/

public section

namespace TauCeti

open NormedSpace
open scoped Nat

noncomputable section

/-- The `n`th cosine-series term at `x` in a normed algebra. -/
@[expose]
def cosSeriesTerm {𝕜 : Type*} [RCLike 𝕜] {A : Type*} [NormedRing A]
    [NormedAlgebra 𝕜 A] (x : A) (n : ℕ) : A :=
  ((((2 * n)! : 𝕜)⁻¹) * (-1 : 𝕜) ^ n) • x ^ (2 * n)

/-- The `n`th sine-series term at `x` in a normed algebra. -/
@[expose]
def sinSeriesTerm {𝕜 : Type*} [RCLike 𝕜] {A : Type*} [NormedRing A]
    [NormedAlgebra 𝕜 A] (x : A) (n : ℕ) : A :=
  ((((2 * n + 1)! : 𝕜)⁻¹) * (-1 : 𝕜) ^ n) • x ^ (2 * n + 1)

/-- The cosine power series in a normed algebra. -/
@[expose]
noncomputable def cosSeries {𝕜 : Type*} [RCLike 𝕜] {A : Type*} [NormedRing A]
    [NormedAlgebra 𝕜 A] (x : A) : A :=
  ∑' n : ℕ, cosSeriesTerm (𝕜 := 𝕜) x n

/-- The sine power series in a normed algebra. -/
@[expose]
noncomputable def sinSeries {𝕜 : Type*} [RCLike 𝕜] {A : Type*} [NormedRing A]
    [NormedAlgebra 𝕜 A] (x : A) : A :=
  ∑' n : ℕ, sinSeriesTerm (𝕜 := 𝕜) x n

section Definitions

variable {𝕜 : Type*} [RCLike 𝕜]
variable {A : Type*} [NormedRing A] [NormedAlgebra 𝕜 A]

/-- The cosine series unfolded as its defining sum. -/
theorem cosSeries_eq_tsum (x : A) :
    cosSeries (𝕜 := 𝕜) x = ∑' n : ℕ, cosSeriesTerm (𝕜 := 𝕜) x n := by
  rw [cosSeries]

/-- The sine series unfolded as its defining sum. -/
theorem sinSeries_eq_tsum (x : A) :
    sinSeries (𝕜 := 𝕜) x = ∑' n : ℕ, sinSeriesTerm (𝕜 := 𝕜) x n := by
  rw [sinSeries]

end Definitions

section BanachAlgebra

variable {𝕜 : Type*} [RCLike 𝕜]
variable {A : Type*} [NormedRing A] [NormedAlgebra 𝕜 A] [CompleteSpace A]

/-- The cosine power series is summable in every Banach algebra over an `RCLike` field. -/
theorem summable_cosSeriesTerm (x : A) :
    Summable (fun n : ℕ => cosSeriesTerm (𝕜 := 𝕜) x n) := by
  have hmul : Function.Injective (fun n : ℕ => 2 * n) :=
    mul_right_injective₀ (by norm_num : (2 : ℕ) ≠ 0)
  have hmajor :=
    (NormedSpace.norm_expSeries_summable' (𝕂 := 𝕜) x).comp_injective hmul
  refine Summable.of_norm_bounded hmajor fun n => ?_
  simp [cosSeriesTerm, norm_smul]

/-- The sine power series is summable in every Banach algebra over an `RCLike` field. -/
theorem summable_sinSeriesTerm (x : A) :
    Summable (fun n : ℕ => sinSeriesTerm (𝕜 := 𝕜) x n) := by
  have hmul : Function.Injective (fun n : ℕ => 2 * n) :=
    mul_right_injective₀ (by norm_num : (2 : ℕ) ≠ 0)
  have hodd : Function.Injective (fun n : ℕ => 2 * n + 1) := by
    intro m n hmn
    exact hmul (Nat.add_right_cancel hmn)
  have hmajor :=
    (NormedSpace.norm_expSeries_summable' (𝕂 := 𝕜) x).comp_injective hodd
  refine Summable.of_norm_bounded hmajor fun n => ?_
  simp [sinSeriesTerm, norm_smul]

/-- The cosine series has sum `cosSeries x`. -/
theorem hasSum_cosSeries (x : A) :
    HasSum (fun n : ℕ => cosSeriesTerm (𝕜 := 𝕜) x n) (cosSeries (𝕜 := 𝕜) x) := by
  exact (summable_cosSeriesTerm (𝕜 := 𝕜) x).hasSum

/-- The sine series has sum `sinSeries x`. -/
theorem hasSum_sinSeries (x : A) :
    HasSum (fun n : ℕ => sinSeriesTerm (𝕜 := 𝕜) x n) (sinSeries (𝕜 := 𝕜) x) := by
  exact (summable_sinSeriesTerm (𝕜 := 𝕜) x).hasSum

section Map

variable {B : Type*} [NormedRing B] [NormedAlgebra 𝕜 B] [CompleteSpace B]

/-- A continuous algebra homomorphism commutes with the cosine power series. -/
theorem map_cosSeries (f : A →ₐ[𝕜] B) (hf : Continuous f) (x : A) :
    f (cosSeries (𝕜 := 𝕜) x) = cosSeries (𝕜 := 𝕜) (f x) := by
  have hmap := (hasSum_cosSeries (𝕜 := 𝕜) x).map f hf
  have hmap' :
      HasSum (fun n : ℕ => cosSeriesTerm (𝕜 := 𝕜) (f x) n)
        (f (cosSeries (𝕜 := 𝕜) x)) := by
    convert! hmap using 1
    ext n : 1
    simp [cosSeriesTerm]
  exact hmap'.unique (hasSum_cosSeries (𝕜 := 𝕜) (f x))

/-- A continuous algebra homomorphism commutes with the sine power series. -/
theorem map_sinSeries (f : A →ₐ[𝕜] B) (hf : Continuous f) (x : A) :
    f (sinSeries (𝕜 := 𝕜) x) = sinSeries (𝕜 := 𝕜) (f x) := by
  have hmap := (hasSum_sinSeries (𝕜 := 𝕜) x).map f hf
  have hmap' :
      HasSum (fun n : ℕ => sinSeriesTerm (𝕜 := 𝕜) (f x) n)
        (f (sinSeries (𝕜 := 𝕜) x)) := by
    convert! hmap using 1
    ext n : 1
    simp [sinSeriesTerm]
  exact hmap'.unique (hasSum_sinSeries (𝕜 := 𝕜) (f x))

end Map

end BanachAlgebra

section Algebraic

variable {𝕜 : Type*} [RCLike 𝕜]
variable {A : Type*} [NormedRing A] [NormedAlgebra 𝕜 A]

/-- Even powers of `J * T` under the supported quarter-turn relations. -/
theorem mul_pow_even_of_commute_of_sq_mul_eq_neg
    {J T : A} (hcomm : Commute J T) (hsq : J * J * T = -T) (n : ℕ) :
    (J * T) ^ (2 * n) = ((-1 : 𝕜) ^ n) • T ^ (2 * n) := by
  have hJT_sq : (J * T) ^ 2 = -(T ^ 2) := by
    rw [pow_two, pow_two]
    calc
      (J * T) * (J * T) = J * ((T * J) * T) := by simp only [mul_assoc]
      _ = J * ((J * T) * T) := by rw [← hcomm.eq]
      _ = (J * J * T) * T := by simp only [mul_assoc]
      _ = (-T) * T := by rw [hsq]
      _ = -(T * T) := by rw [neg_mul]
  calc
    (J * T) ^ (2 * n) = ((J * T) ^ 2) ^ n := by rw [pow_mul]
    _ = (-(T ^ 2)) ^ n := by rw [hJT_sq]
    _ = ((-1 : 𝕜) ^ n) • (T ^ 2) ^ n := by
      rw [neg_pow]
      simp [Algebra.smul_def]
    _ = ((-1 : 𝕜) ^ n) • T ^ (2 * n) := by rw [pow_mul]

/-- Odd powers of `J * T` under the supported quarter-turn relations. -/
theorem mul_pow_odd_of_commute_of_sq_mul_eq_neg
    {J T : A} (hcomm : Commute J T) (hsq : J * J * T = -T) (n : ℕ) :
    (J * T) ^ (2 * n + 1) = ((-1 : 𝕜) ^ n) • (J * T ^ (2 * n + 1)) := by
  rw [pow_succ, mul_pow_even_of_commute_of_sq_mul_eq_neg (𝕜 := 𝕜) hcomm hsq n]
  calc
    (((-1 : 𝕜) ^ n) • T ^ (2 * n)) * (J * T) =
        ((-1 : 𝕜) ^ n) • (T ^ (2 * n) * (J * T)) := by
      rw [smul_mul_assoc]
    _ = ((-1 : 𝕜) ^ n) • (J * (T ^ (2 * n) * T)) := by
      congr 1
      calc
        T ^ (2 * n) * (J * T) = (T ^ (2 * n) * J) * T := by
          rw [mul_assoc]
        _ = (J * T ^ (2 * n)) * T := by
          rw [← (hcomm.pow_right (2 * n)).eq]
        _ = J * (T ^ (2 * n) * T) := by rw [mul_assoc]
    _ = ((-1 : 𝕜) ^ n) • (J * T ^ (2 * n + 1)) := by rw [pow_succ]

end Algebraic

section Euler

variable {𝕜 : Type*} [RCLike 𝕜]
variable {A : Type*} [NormedRing A] [NormedAlgebra 𝕜 A] [CompleteSpace A]

/-- **Supported Euler identity.**

If `J` commutes with `T` and acts as a square root of `-1` on the range relevant to `T`,
expressed globally as `J * J * T = -T`, then the exponential of `J * T` splits into the
cosine and sine power series. -/
theorem exp_mul_eq_cosSeries_add_mul_sinSeries
    {J T : A} (hcomm : Commute J T) (hsq : J * J * T = -T) :
    NormedSpace.exp (J * T) =
      cosSeries (𝕜 := 𝕜) T + J * sinSeries (𝕜 := 𝕜) T := by
  have heven : HasSum
      (fun n : ℕ => NormedSpace.expSeries 𝕜 A (2 * n) (fun _ => J * T))
      (cosSeries (𝕜 := 𝕜) T) := by
    convert! hasSum_cosSeries (𝕜 := 𝕜) T using 1
    ext n : 1
    rw [NormedSpace.expSeries_apply_eq]
    rw [mul_pow_even_of_commute_of_sq_mul_eq_neg (𝕜 := 𝕜) hcomm hsq n]
    simp [cosSeriesTerm, smul_smul, mul_comm]
  have hodd : HasSum
      (fun n : ℕ => NormedSpace.expSeries 𝕜 A (2 * n + 1) (fun _ => J * T))
      (J * sinSeries (𝕜 := 𝕜) T) := by
    convert! (hasSum_sinSeries (𝕜 := 𝕜) T).mul_left J using 1
    ext n : 1
    rw [NormedSpace.expSeries_apply_eq]
    rw [mul_pow_odd_of_commute_of_sq_mul_eq_neg (𝕜 := 𝕜) hcomm hsq n]
    simp [sinSeriesTerm, smul_smul, mul_comm]
  have hsplit : HasSum
      (fun n : ℕ => NormedSpace.expSeries 𝕜 A n (fun _ => J * T))
      (cosSeries (𝕜 := 𝕜) T + J * sinSeries (𝕜 := 𝕜) T) := by
    exact HasSum.even_add_odd heven hodd
  exact (NormedSpace.expSeries_hasSum_exp (𝕂 := 𝕜) (J * T)).unique hsplit

end Euler

section Scalars

/-- The Banach-algebra cosine series on `ℝ` is the usual real cosine. -/
@[simp]
theorem cosSeries_real (x : ℝ) : cosSeries (𝕜 := ℝ) x = Real.cos x := by
  rw [cosSeries, Real.cos_eq_tsum]
  apply tsum_congr
  intro n
  simp only [cosSeriesTerm, smul_eq_mul]
  rw [div_eq_mul_inv]
  ring

/-- The Banach-algebra sine series on `ℝ` is the usual real sine. -/
@[simp]
theorem sinSeries_real (x : ℝ) : sinSeries (𝕜 := ℝ) x = Real.sin x := by
  rw [sinSeries, Real.sin_eq_tsum]
  apply tsum_congr
  intro n
  simp only [sinSeriesTerm, smul_eq_mul]
  rw [div_eq_mul_inv]
  ring

end Scalars

end

end TauCeti

end
