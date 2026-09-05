/-
Copyright (c) 2026 D.S. McNeil, Gábor P. Nagy, Attila Vajda. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: D.S. McNeil, Gábor P. Nagy, Attila Vajda
-/

import LeanPool.KasamiCyclicAdditive.Phase.Definitions

/-!
# Basic facts: the power map `x ↦ x^D` and the group `μ₃(K)`
-/

open Finset

namespace KasamiCyclicAdditive.Phase

variable {K : Type*} [Field K] [Fintype K] [DecidableEq K]

/-! ### The exponent `D` -/

section PowD

variable {m D : ℕ}

/-- If `m * D ≡ 1 (mod N)` with `N = #Kˣ`, then `x ^ (m * D) = x` on all of `K`,
so `x ↦ x^D` and `x ↦ x^m` are mutually inverse. -/
lemma pow_mul_eq_self (hm : m ≠ 0) (hD : D ≠ 0)
    (hmD : m * D ≡ 1 [MOD Fintype.card Kˣ]) (x : K) : x ^ (m * D) = x := by
  have h1 : 1 ≤ m * D := Nat.one_le_iff_ne_zero.mpr (mul_ne_zero hm hD)
  obtain ⟨k, hk⟩ := (Nat.modEq_iff_dvd' h1).mp hmD.symm
  have hmD' : m * D = 1 + Fintype.card Kˣ * k := by omega
  rcases eq_or_ne x 0 with rfl | hx
  · simp [zero_pow (by omega : m * D ≠ 0)]
  · lift x to Kˣ using hx.isUnit
    rw [hmD', pow_add, pow_mul, pow_one]
    norm_cast
    simp [pow_card_eq_one]

/-- `x ↦ x^m` undoes `x ↦ x^D`. -/
lemma powD_powm (hm : m ≠ 0) (hD : D ≠ 0) (hmD : m * D ≡ 1 [MOD Fintype.card Kˣ]) (x : K) :
    (x ^ D) ^ m = x := by
  rw [← pow_mul, mul_comm D m]; exact pow_mul_eq_self hm hD hmD x

/-- `x ↦ x^D` undoes `x ↦ x^m`. -/
lemma powm_powD (hm : m ≠ 0) (hD : D ≠ 0) (hmD : m * D ≡ 1 [MOD Fintype.card Kˣ]) (x : K) :
    (x ^ m) ^ D = x := by
  rw [← pow_mul]; exact pow_mul_eq_self hm hD hmD x

/-- Hence `x ↦ x^D` is a bijection of `K`. -/
lemma powD_bijective (hm : m ≠ 0) (hD : D ≠ 0) (hmD : m * D ≡ 1 [MOD Fintype.card Kˣ]) :
    Function.Bijective (fun x : K => x ^ D) :=
  Function.bijective_iff_has_inverse.mpr
    ⟨fun x => x ^ m, powD_powm hm hD hmD, powm_powD hm hD hmD⟩


/-- `∑_{y ∈ K} ψ(C y^D) = Q` if `C = 0` and `0` otherwise. -/
lemma sum_psi_mul_powD {ψ : AddChar K ℂ} (hψ : ψ.IsPrimitive)
    (hm : m ≠ 0) (hD : D ≠ 0) (hmD : m * D ≡ 1 [MOD Fintype.card Kˣ]) (C : K) :
    ∑ y : K, ψ (C * y ^ D) = if C = 0 then (Fintype.card K : ℂ) else 0 := by
  have hbij := (powD_bijective (m := m) hm hD hmD (K := K))
  have h2 : ∑ y : K, ψ (C * y ^ D) = ∑ x : K, ψ (C * x) :=
    Fintype.sum_bijective _ hbij _ _ (fun y => rfl)
  rw [h2]
  simpa [mul_comm] using AddChar.sum_mulShift (R := K) (R' := ℂ) C hψ

end PowD

/-! ### The group `μ₃(K)` -/

/-- Membership in `μ₃(K)` is the equation `u ^ 3 = 1`. -/
@[simp] lemma mem_cubeRootsOne {u : K} : u ∈ cubeRootsOne K ↔ u ^ 3 = 1 := by
  simp [cubeRootsOne]

/-- Cube roots of unity are nonzero. -/
lemma cubeRootsOne_ne_zero {u : K} (h : u ∈ cubeRootsOne K) : u ≠ 0 := by
  intro h0; rw [mem_cubeRootsOne, h0] at h; simp at h

/-- `1` is a cube root of unity. -/
private lemma one_mem_cubeRootsOne : (1 : K) ∈ cubeRootsOne K := by simp

/-- `μ₃(K)` is closed under multiplication. -/
lemma mul_mem_cubeRootsOne {u v : K} (hu : u ∈ cubeRootsOne K) (hv : v ∈ cubeRootsOne K) :
    u * v ∈ cubeRootsOne K := by
  rw [mem_cubeRootsOne] at *; rw [mul_pow, hu, hv, one_mul]

/-- `μ₃(K)` is closed under inverses. -/
lemma inv_mem_cubeRootsOne {u : K} (hu : u ∈ cubeRootsOne K) : u⁻¹ ∈ cubeRootsOne K := by
  rw [mem_cubeRootsOne] at *
  rw [inv_pow, hu, inv_one]

/-- `μ₃(K)` is nonempty, so `mu3Card K` is positive. -/
private lemma mu3Card_pos : 0 < mu3Card K :=
  Finset.card_pos.mpr ⟨1, one_mem_cubeRootsOne⟩

/-- Hence `mu3Card K` is nonzero in `ℂ`, and may be divided by. -/
lemma mu3Card_ne_zero : (mu3Card K : ℂ) ≠ 0 :=
  Nat.cast_ne_zero.mpr mu3Card_pos.ne'

end KasamiCyclicAdditive.Phase
