/-
Copyright (c) 2026 Antoine de Saint Germain, Ambrose Tang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Antoine de Saint Germain, Ambrose Tang
-/

import Mathlib.LinearAlgebra.RootSystem.OfBilinear
import Mathlib.Tactic.Ext
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Push
import Mathlib.Tactic.Tauto

/-!
# Type-BCₙ root systems

Explicit construction of the type-`BCₙ` root pairing from the standard dot product
on `ℤⁿ`, exhibited as a Mathlib `RootPairing`, together with a characterization of
its roots as the classical type-`BCₙ` root set `{±eᵢ, ±2eᵢ, ±eᵢ ± eⱼ (i ≠ j)}`
(`BCn.isReflective_iff_isClassicalRoot`, `BCn.range_rootPairing_root`).
-/

namespace BCn

/-- The ambient space `Fin n → ℤ` for the type-BCₙ construction. -/
abbrev Space (n : ℕ) := Fin n → ℤ
/-- The `ℤ`-linear dual of `Space n`. -/
abbrev CoSpace (n : ℕ) := Module.Dual ℤ (Space n)

/-- The standard dot product on `ℤⁿ`. -/
noncomputable def dotProduct (n : ℕ) : Space n →ₗ[ℤ] Space n →ₗ[ℤ] ℤ where
  toFun x :=
    { toFun := fun y => ∑ i, x i * y i
      map_add' := by
        intro y z
        simp [mul_add, Finset.sum_add_distrib]
      map_smul' := by
        intro a y
        simp [Finset.mul_sum, mul_left_comm] }
  map_add' := by
    intro x y
    ext z
    simp [add_mul, Finset.sum_add_distrib]
  map_smul' := by
    intro a x
    ext y
    simp [Finset.mul_sum, mul_comm, mul_left_comm]

theorem dotProduct_apply (n : ℕ) (x y : Space n) :
    dotProduct n x y = ∑ i, x i * y i :=
  rfl

@[simp]
theorem dotProduct_single_right {n : ℕ} (x : Space n) (i : Fin n) :
    dotProduct n x (Pi.single i 1) = x i := by
  rw [dotProduct_apply]
  simp [Pi.single_apply]

@[simp]
theorem dotProduct_single_left {n : ℕ} (x : Space n) (i : Fin n) :
    dotProduct n (Pi.single i 1) x = x i := by
  rw [dotProduct_apply]
  simp [Pi.single_apply]

theorem dotProduct_isSymm (n : ℕ) : LinearMap.IsSymm (dotProduct n) where
  eq x y := by
    simp [dotProduct_apply, mul_comm]

theorem dotProduct_nondegenerate (n : ℕ) : LinearMap.Nondegenerate (dotProduct n) := by
  constructor
  · intro x hx
    ext i
    simpa using hx (Pi.single i 1)
  · intro y hy
    ext i
    simpa using hy (Pi.single i 1)

/-- The reflective vectors for the standard dot product. -/
abbrev ReflectiveIndex (n : ℕ) :=
  { x : Space n // LinearMap.IsReflective (dotProduct n) x }

/-- The `BCₙ` root pairing, built from all reflective vectors for the standard dot product. -/
noncomputable def rootPairing (n : ℕ) :
    RootPairing (ReflectiveIndex n) ℤ (Space n) (CoSpace n) :=
  RootPairing.ofBilinear (dotProduct n) (dotProduct_nondegenerate n) (dotProduct_isSymm n)
    (IsRegular.of_ne_zero (by norm_num : (2 : ℤ) ≠ 0))

/-!
## Characterization of the type-`BCₙ` roots

The reflective vectors of the standard dot product on `ℤⁿ` are exactly the classical
type-`BCₙ` roots `±eᵢ`, `±2eᵢ`, and `±eᵢ ± eⱼ` for `i ≠ j`.
-/

theorem dotProduct_single_left_eq {n : ℕ} (i : Fin n) (a : ℤ) (y : Space n) :
    dotProduct n (Pi.single i a) y = a * y i := by
  rw [dotProduct_apply]
  simp [Pi.single_apply, ite_mul]

/-- The classical type-`BCₙ` root set: `x` is a classical root when it is `±eᵢ` or `±2eᵢ`
for some `i`, or `±eᵢ ± eⱼ` for some `i ≠ j`, where `eᵢ` is the `i`-th standard basis
vector of `ℤⁿ`. -/
def IsClassicalRoot {n : ℕ} (x : Space n) : Prop :=
  (∃ (c : ℤ) (i : Fin n), (c = 1 ∨ c = -1 ∨ c = 2 ∨ c = -2) ∧ x = Pi.single i c) ∨
    ∃ (a b : ℤ) (i j : Fin n), i ≠ j ∧ (a = 1 ∨ a = -1) ∧ (b = 1 ∨ b = -1) ∧
      x = Pi.single i a + Pi.single j b

theorem eq_single_of_eq_zero {n : ℕ} {x : Space n} {i : Fin n} (h : ∀ k, k ≠ i → x k = 0) :
    x = Pi.single i (x i) := by
  funext k
  rcases eq_or_ne k i with rfl | hk
  · rw [Pi.single_eq_same]
  · rw [Pi.single_eq_of_ne hk]
    exact h k hk

theorem eq_single_add_single_of_eq_zero {n : ℕ} {x : Space n} {i j : Fin n} (hij : i ≠ j)
    (h : ∀ k, k ≠ i → k ≠ j → x k = 0) :
    x = Pi.single i (x i) + Pi.single j (x j) := by
  funext k
  rcases eq_or_ne k i with rfl | hki
  · rw [Pi.add_apply, Pi.single_eq_same, Pi.single_eq_of_ne hij, add_zero]
  · rcases eq_or_ne k j with rfl | hkj
    · rw [Pi.add_apply, Pi.single_eq_same, Pi.single_eq_of_ne hki, zero_add]
    · rw [Pi.add_apply, Pi.single_eq_of_ne hki, Pi.single_eq_of_ne hkj, add_zero, h k hki hkj]

theorem isClassicalRoot_of_isReflective {n : ℕ} {x : Space n}
    (hx : LinearMap.IsReflective (dotProduct n) x) : IsClassicalRoot x := by
  obtain ⟨hreg, hdvd⟩ := hx
  -- The squared norm `Σ xₖ²` divides `2 xᵢ` for every coordinate `i`.
  have hqdvd : ∀ i, (∑ k, x k * x k) ∣ 2 * x i := by
    intro i
    have h := hdvd (Pi.single i 1)
    rw [dotProduct_single_right] at h
    rwa [dotProduct_apply] at h
  have hterm : ∀ k : Fin n, 0 ≤ x k * x k := fun k => mul_self_nonneg (x k)
  have hsq_le : ∀ k, x k * x k ≤ ∑ m, x m * x m := fun k =>
    Finset.single_le_sum (fun m _ => hterm m) (Finset.mem_univ k)
  have hq0 : (∑ k, x k * x k) ≠ 0 := by
    intro h
    rw [dotProduct_apply, h] at hreg
    exact not_isRegular_zero hreg
  -- Every coordinate lies in `{-2, -1, 0, 1, 2}`.
  have hcoord : ∀ k, x k = 0 ∨ x k = 1 ∨ x k = -1 ∨ x k = 2 ∨ x k = -2 := by
    intro k
    by_cases h0 : x k = 0
    · exact Or.inl h0
    have h1 : 1 ≤ |x k| := Int.one_le_abs h0
    have h2 : (∑ m, x m * x m) ≤ |2 * x k| :=
      Int.le_of_dvd (abs_pos.mpr (mul_ne_zero two_ne_zero h0)) ((dvd_abs _ _).mpr (hqdvd k))
    have h3 : |x k| * |x k| ≤ 2 * |x k| := by
      rw [abs_mul_abs_self]
      calc x k * x k ≤ ∑ m, x m * x m := hsq_le k
        _ ≤ |2 * x k| := h2
        _ = 2 * |x k| := by rw [abs_mul]; norm_num
    have h4 : |x k| ≤ 2 := by
      rw [mul_comm (2 : ℤ)] at h3
      exact le_of_mul_le_mul_left h3 (zero_lt_one.trans_le h1)
    have h5 := abs_le.mp h4
    omega
  have hex : ∃ i, x i ≠ 0 := by
    by_contra h
    push Not at h
    exact hq0 (Finset.sum_eq_zero fun k _ => by rw [h k, mul_zero])
  have hzero : ∀ s : Finset (Fin n), ∑ k ∈ s, x k * x k = 0 → ∀ k ∈ s, x k = 0 := by
    intro s hs k hk
    exact mul_self_eq_zero.mp
      ((Finset.sum_eq_zero_iff_of_nonneg fun m _ => hterm m).mp hs k hk)
  by_cases hbig : ∃ i, x i = 2 ∨ x i = -2
  · -- `±2eᵢ`: the squared norm is `4` and all other coordinates vanish.
    obtain ⟨i, hi⟩ := hbig
    have hxi : x i * x i = 4 := by rcases hi with h | h <;> rw [h] <;> norm_num
    have habs : |2 * x i| = 4 := by rcases hi with h | h <;> rw [h] <;> norm_num
    have hle : (∑ k, x k * x k) ≤ 4 := by
      have h := Int.le_of_dvd (by rw [habs]; norm_num) ((dvd_abs _ _).mpr (hqdvd i))
      omega
    have hsplit : x i * x i + ∑ k ∈ Finset.univ.erase i, x k * x k = ∑ k, x k * x k :=
      Finset.add_sum_erase Finset.univ (fun k => x k * x k) (Finset.mem_univ i)
    have htail : ∑ k ∈ Finset.univ.erase i, x k * x k = 0 := by
      have hnn : 0 ≤ ∑ k ∈ Finset.univ.erase i, x k * x k :=
        Finset.sum_nonneg fun k _ => hterm k
      omega
    have hxeq : x = Pi.single i (x i) :=
      eq_single_of_eq_zero fun k hk =>
        hzero _ htail k (Finset.mem_erase.mpr ⟨hk, Finset.mem_univ k⟩)
    exact Or.inl ⟨x i, i, by tauto, hxeq⟩
  · -- All coordinates lie in `{-1, 0, 1}`; the squared norm is `1` or `2`.
    push Not at hbig
    obtain ⟨i, hi⟩ := hex
    have hsmall : ∀ k, x k ≠ 0 → x k = 1 ∨ x k = -1 := by
      intro k hk
      have h1 := hcoord k
      have h2 := hbig k
      tauto
    have hxi : x i * x i = 1 := by rcases hsmall i hi with h | h <;> rw [h] <;> norm_num
    have habs : |2 * x i| = 2 := by rcases hsmall i hi with h | h <;> rw [h] <;> norm_num
    have hle : (∑ k, x k * x k) ≤ 2 := by
      have h := Int.le_of_dvd (by rw [habs]; norm_num) ((dvd_abs _ _).mpr (hqdvd i))
      omega
    have hsplit : x i * x i + ∑ k ∈ Finset.univ.erase i, x k * x k = ∑ k, x k * x k :=
      Finset.add_sum_erase Finset.univ (fun k => x k * x k) (Finset.mem_univ i)
    have hnn : 0 ≤ ∑ k ∈ Finset.univ.erase i, x k * x k :=
      Finset.sum_nonneg fun k _ => hterm k
    have htail01 : ∑ k ∈ Finset.univ.erase i, x k * x k = 0 ∨
        ∑ k ∈ Finset.univ.erase i, x k * x k = 1 := by omega
    rcases htail01 with htail | htail
    · -- `±eᵢ`
      have hxeq : x = Pi.single i (x i) :=
        eq_single_of_eq_zero fun k hk =>
          hzero _ htail k (Finset.mem_erase.mpr ⟨hk, Finset.mem_univ k⟩)
      exact Or.inl ⟨x i, i, by rcases hsmall i hi with h | h <;> tauto, hxeq⟩
    · -- `±eᵢ ± eⱼ`: a second nonzero coordinate exists, and all others vanish.
      have hexj : ∃ j ∈ Finset.univ.erase i, x j ≠ 0 := by
        by_contra h
        push Not at h
        rw [Finset.sum_eq_zero fun k hk => by rw [h k hk, mul_zero]] at htail
        exact absurd htail (by norm_num)
      obtain ⟨j, hjmem, hj⟩ := hexj
      have hij : i ≠ j := fun h => (Finset.mem_erase.mp hjmem).1 h.symm
      have hxj : x j * x j = 1 := by rcases hsmall j hj with h | h <;> rw [h] <;> norm_num
      have hsplit2 :
          x j * x j + ∑ k ∈ (Finset.univ.erase i).erase j, x k * x k
            = ∑ k ∈ Finset.univ.erase i, x k * x k :=
        Finset.add_sum_erase (Finset.univ.erase i) (fun k => x k * x k) hjmem
      have htail2 : ∑ k ∈ (Finset.univ.erase i).erase j, x k * x k = 0 := by omega
      have hxeq : x = Pi.single i (x i) + Pi.single j (x j) :=
        eq_single_add_single_of_eq_zero hij fun k hki hkj =>
          hzero _ htail2 k
            (Finset.mem_erase.mpr ⟨hkj, Finset.mem_erase.mpr ⟨hki, Finset.mem_univ k⟩⟩)
      exact Or.inr ⟨x i, x j, i, j, hij, hsmall i hi, hsmall j hj, hxeq⟩

theorem isReflective_of_isClassicalRoot {n : ℕ} {x : Space n} (hx : IsClassicalRoot x) :
    LinearMap.IsReflective (dotProduct n) x := by
  rcases hx with ⟨c, i, hc, rfl⟩ | ⟨a, b, i, j, hij, ha, hb, rfl⟩
  · have hBxx : dotProduct n (Pi.single i c) (Pi.single i c) = c * c := by
      rw [dotProduct_single_left_eq, Pi.single_eq_same]
    refine ⟨?_, fun y => ?_⟩
    · rw [hBxx]
      rcases hc with rfl | rfl | rfl | rfl <;> exact IsRegular.of_ne_zero (by norm_num)
    · rw [hBxx, dotProduct_single_left_eq]
      rcases hc with rfl | rfl | rfl | rfl
      · exact ⟨2 * y i, by ring⟩
      · exact ⟨-(2 * y i), by ring⟩
      · exact ⟨y i, by ring⟩
      · exact ⟨-y i, by ring⟩
  · have hBy : ∀ y, dotProduct n (Pi.single i a + Pi.single j b) y = a * y i + b * y j := by
      intro y
      rw [map_add, LinearMap.add_apply, dotProduct_single_left_eq, dotProduct_single_left_eq]
    have hBxx : dotProduct n (Pi.single i a + Pi.single j b) (Pi.single i a + Pi.single j b)
        = a * a + b * b := by
      rw [hBy, Pi.add_apply, Pi.add_apply, Pi.single_eq_same, Pi.single_eq_same,
        Pi.single_eq_of_ne hij, Pi.single_eq_of_ne (Ne.symm hij), add_zero, zero_add]
    refine ⟨?_, fun y => ?_⟩
    · rw [hBxx]
      rcases ha with rfl | rfl <;> rcases hb with rfl | rfl <;>
        exact IsRegular.of_ne_zero (by norm_num)
    · rw [hBxx, hBy]
      rcases ha with rfl | rfl <;> rcases hb with rfl | rfl
      · exact ⟨y i + y j, by ring⟩
      · exact ⟨y i - y j, by ring⟩
      · exact ⟨-y i + y j, by ring⟩
      · exact ⟨-(y i + y j), by ring⟩

/-- A vector of `ℤⁿ` is reflective for the standard dot product precisely when it is one
of the classical type-`BCₙ` roots `±eᵢ`, `±2eᵢ`, or `±eᵢ ± eⱼ` with `i ≠ j`. -/
theorem isReflective_iff_isClassicalRoot {n : ℕ} (x : Space n) :
    LinearMap.IsReflective (dotProduct n) x ↔ IsClassicalRoot x :=
  ⟨isClassicalRoot_of_isReflective, isReflective_of_isClassicalRoot⟩

/-- The roots of the type-`BCₙ` root pairing are exactly the classical type-`BCₙ` roots
`±eᵢ`, `±2eᵢ`, and `±eᵢ ± eⱼ` for `i ≠ j`. -/
theorem range_rootPairing_root (n : ℕ) :
    Set.range (rootPairing n).root = {x : Space n | IsClassicalRoot x} := by
  ext y
  constructor
  · rintro ⟨⟨z, hz⟩, rfl⟩
    exact isClassicalRoot_of_isReflective hz
  · intro hy
    exact ⟨⟨y, isReflective_of_isClassicalRoot hy⟩, rfl⟩

end BCn
