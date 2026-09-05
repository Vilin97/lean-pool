/-
Copyright (c) 2026 D.S. McNeil, Gábor P. Nagy, Attila Vajda. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: D.S. McNeil, Gábor P. Nagy, Attila Vajda
-/

import LeanPool.KasamiCyclicAdditive.Prelude
import LeanPool.KasamiCyclicAdditive.Preliminaries.Arithmetic

/-!
# The rational kernel of `1 + π^k` on the Fermat cubic over `𝔽₂`

Let `E : X³ + Y³ = Z³` be the Fermat cubic over `𝔽₂`, with origin `O = [1 : 1 : 0]`, and let
`π` be the `2`-power Frobenius endomorphism.

Everything in this file is phrased directly in terms of homogeneous coordinates.  This is
possible because both maps involved admit a purely coordinatewise description:

* Frobenius is `π [X : Y : Z] = [X² : Y² : Z²]`, hence `π^k [X : Y : Z] = [X^(2^k) : ⋯]`;
* negation on the Fermat cubic with origin `[1 : 1 : 0]` swaps the first two coordinates,
  `-[X : Y : Z] = [Y : X : Z]`.

Consequently `(1 + π^k) R = O` if and only if `π^k R = -R`, which is the coordinate condition
`IsKernelPoint` below: the two triples `(X^(2^k), Y^(2^k), Z^(2^k))` and `(Y, X, Z)` are
proportional.  No use of the group law itself is needed.

## Main results

Let `K` be a field with `2^n` elements and `gcd (k, n) = 1`.

* `rational_kernel_odd`: if `n` is odd, the `K`-rational points of `ker (1 + π^k)` reduce to the
  origin `O = [1 : 1 : 0]`.
* `rational_kernel_even`: if `n` is even, they are exactly the points at infinity `Z = 0`.
* `geometric_kernel_one_add_frobenius`: over *any* field of characteristic `2`, `ker (1 + π)`
  consists exactly of the points at infinity `[1 : ω : 0]` with `ω³ = 1`.

## Notes on the key steps

1. The fixed-field/Bézout step `π^(2k) R = R`, `π^n R = R` ⟹ `π^(gcd (2k, n)) R = R` is
   `pow_two_pow_gcd`, applied coordinatewise to the affine coordinate `X / Z` in
   `Z_eq_zero_of_isKernelPoint`.  Here `gcd (2k, n) = gcd (2, n) ∈ {1, 2}`, and in both cases
   the affine coordinate satisfies `x⁴ = x`; the two cases of the informal proof are thereby
   merged into one.
2. `π^k = π` on cube roots of unity for odd `k` is `pow_two_pow_of_cube_root`.
3. That the points at infinity are precisely `ker (1 + π)` is
   `geometric_kernel_one_add_frobenius`.
4. Instead of deducing `#ker (1 + π) = 3` from `deg (1 + π) = 3` and separability, step 3
   proves directly, over an arbitrary field of characteristic `2`, that there are no further
   kernel points; this is a self-contained substitute for the degree/separability argument.

The corollary of the informal text — for odd `n` the endomorphism `1 + π^k` is injective, hence
bijective, on the finite group `E(K)` — is exactly the triviality of the rational kernel proved
in `rational_kernel_odd`, combined with the standard fact that a group homomorphism with trivial
kernel is injective; the group law on `E` itself is not developed here.
-/

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Pointwise

open Classical in
section
namespace KasamiCyclicAdditive.FermatCubicFrobenius

variable {K : Type*} [Field K]

/-- `IsPoint X Y Z` says that `[X : Y : Z]` is a point of the projective Fermat cubic
`X³ + Y³ = Z³`: the coordinates are not all zero and they satisfy the equation. -/
def IsPoint (X Y Z : K) : Prop :=
  ¬ (X = 0 ∧ Y = 0 ∧ Z = 0) ∧ X ^ 3 + Y ^ 3 = Z ^ 3

/-- `IsKernelPoint k X Y Z` says that `(1 + π^k) [X : Y : Z] = O`, equivalently
`π^k [X : Y : Z] = -[X : Y : Z]`, i.e. that the triples `(X^(2^k), Y^(2^k), Z^(2^k))` and
`(Y, X, Z)` define the same projective point. -/
def IsKernelPoint (k : ℕ) (X Y Z : K) : Prop :=
  ∃ c : K, c ≠ 0 ∧ X ^ 2 ^ k = c * Y ∧ Y ^ 2 ^ k = c * X ∧ Z ^ 2 ^ k = c * Z

/-! ### Basic facts about the origin and the points at infinity -/

/-- On a point at infinity (`Z = 0`) both remaining coordinates are nonzero. -/
lemma ne_zero_of_isPoint_infinity {X Y : K} (hP : IsPoint X Y 0) : X ≠ 0 ∧ Y ≠ 0 := by
  obtain ⟨hne, heq⟩ := hP
  rw [zero_pow (by norm_num)] at heq
  constructor
  · rintro rfl
    have hY : Y ^ 3 = 0 := by simpa using heq
    exact hne ⟨rfl, pow_eq_zero_iff (by norm_num) |>.mp hY, rfl⟩
  · rintro rfl
    have hX : X ^ 3 = 0 := by simpa using heq
    exact hne ⟨pow_eq_zero_iff (by norm_num) |>.mp hX, rfl, rfl⟩

/-- On a point at infinity in characteristic `2` we have `Y³ = X³`. -/
lemma cube_eq_of_isPoint_infinity (h2 : (2 : K) = 0) {X Y : K} (hP : IsPoint X Y 0) :
    Y ^ 3 = X ^ 3 := by
  obtain ⟨-, heq⟩ := hP
  rw [zero_pow (by norm_num)] at heq
  linear_combination heq - X ^ 3 * h2

/-- In characteristic `2`, the ratio `ω = Y / X` of a point at infinity
`[X : Y : 0]` is a cube root of unity, so the point is `[1 : ω : 0]`. -/
lemma cube_ratio_of_isPoint_infinity (h2 : (2 : K) = 0) {X Y : K} (hP : IsPoint X Y 0) :
    (Y / X) ^ 3 = 1 := by
  obtain ⟨hX, -⟩ := ne_zero_of_isPoint_infinity hP
  have hXY : Y ^ 3 = X ^ 3 := cube_eq_of_isPoint_infinity h2 hP
  rw [div_pow, hXY, div_self (pow_ne_zero 3 hX)]

/-! ### Characteristic and Frobenius facts for a field with `2^n` elements -/

/-- A field with `2^n` elements has characteristic `2`. -/
lemma two_eq_zero_of_card [Fintype K] {n : ℕ} (hcard : Fintype.card K = 2 ^ n) : (2 : K) = 0 := by
  have hn : n ≠ 0 := by
    rintro rfl
    have h1 := Fintype.one_lt_card (α := K)
    rw [hcard] at h1
    norm_num at h1
  have h := FiniteField.cast_card_eq_zero K
  rw [hcard] at h
  push_cast at h
  exact (pow_eq_zero_iff hn).mp h

/-- Every element of a field with `2^n` elements is fixed by the `n`-th power of Frobenius. -/
lemma pow_two_pow_card [Fintype K] {n : ℕ} (hcard : Fintype.card K = 2 ^ n) (x : K) :
    x ^ 2 ^ n = x := by
  rw [← hcard]; exact FiniteField.pow_card x

/-- For odd `n`, `3` is coprime to `2^n - 1`. -/
private lemma coprime_three_two_pow_sub_one_of_odd {n : ℕ} (hn : Odd n) :
    Nat.Coprime 3 (2 ^ n - 1) := by
  rw [Nat.coprime_iff_gcd_eq_one]
  have h3 : (3 : ℕ) = 2 ^ 2 - 1 := by norm_num
  rw [h3, Nat.pow_sub_one_gcd_pow_sub_one]
  have hg2 : Nat.gcd 2 n = 1 := Nat.coprime_two_left.mpr hn
  rw [hg2]
  norm_num

/-- For odd `n` the only cube root of unity in a field with `2^n` elements is `1`. -/
lemma cube_root_eq_one_of_odd [Fintype K] {n : ℕ} (hn : Odd n)
    (hcard : Fintype.card K = 2 ^ n) {a : K} (ha : a ^ 3 = 1) : a = 1 := by
  have ha0 : a ≠ 0 := by
    rintro rfl
    simp at ha
  have h1 : a ^ (2 ^ n - 1) = 1 := by
    have := FiniteField.pow_card_sub_one_eq_one a ha0
    rwa [hcard] at this
  have hdvd : orderOf a ∣ Nat.gcd 3 (2 ^ n - 1) :=
    Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one ha) (orderOf_dvd_of_pow_eq_one h1)
  rw [(coprime_three_two_pow_sub_one_of_odd hn).gcd_eq_one] at hdvd
  exact orderOf_eq_one_iff.mp (Nat.dvd_one.mp hdvd)

/-! ### There is no affine kernel point -/

/-- Frobenius swaps the affine coordinates `X / Z` and `Y / Z` of a kernel point. -/
private lemma affine_swap_of_isKernelPoint {k : ℕ} {X Y Z : K}
    (hK : IsKernelPoint k X Y Z) :
    (X / Z) ^ 2 ^ k = Y / Z ∧ (Y / Z) ^ 2 ^ k = X / Z := by
  obtain ⟨c, hc, hX, hY, hZc⟩ := hK
  constructor
  · rw [div_pow, hX, hZc, mul_comm c Y, mul_comm c Z, mul_div_mul_right _ _ hc]
  · rw [div_pow, hY, hZc, mul_comm c X, mul_comm c Z, mul_div_mul_right _ _ hc]

/-- The affine `x`-coordinate of a kernel point is fixed by the `2k`-th Frobenius power. -/
private lemma affine_fixed_by_two_k_of_isKernelPoint {k : ℕ} {X Y Z : K}
    (hK : IsKernelPoint k X Y Z) :
    (X / Z) ^ 2 ^ (k * 2) = X / Z := by
  obtain ⟨hxy, hyx⟩ := affine_swap_of_isKernelPoint hK
  have he : (2 : ℕ) ^ (k * 2) = 2 ^ k * 2 ^ k := by rw [pow_mul]; ring
  rw [he, pow_mul, hxy, hyx]

/-- The core computation: an affine (`Z ≠ 0`) kernel point whose affine `x`-coordinate lies in
`𝔽₄` cannot exist. -/
lemma not_kernel_of_Z_ne_zero (h2 : (2 : K) = 0) {k : ℕ} {X Y Z : K} (hP : IsPoint X Y Z)
    (hK : IsKernelPoint k X Y Z) (hZ : Z ≠ 0) (h4 : (X / Z) ^ 4 = X / Z) : False := by
  obtain ⟨-, hcurve⟩ := hP
  set x : K := X / Z with hxdef
  set y : K := Y / Z with hydef
  have haff : x ^ 3 + y ^ 3 = 1 := by
    rw [hxdef, hydef, div_pow, div_pow, ← add_div, hcurve]
    exact div_self (pow_ne_zero 3 hZ)
  have hxy : x ^ 2 ^ k = y := by
    simpa [hxdef, hydef] using (affine_swap_of_isKernelPoint hK).1
  have hx3 : x = 0 ∨ x ^ 3 = 1 := by
    rcases eq_or_ne x 0 with h | h
    · exact Or.inl h
    · right
      have : x ^ 3 * x = 1 * x := by rw [one_mul, ← pow_succ]; simpa using h4
      exact mul_right_cancel₀ h this
  rcases hx3 with h | h
  · have hy : y = 0 := by rw [← hxy, h, zero_pow (Nat.two_pow_pos k).ne']
    rw [h, hy] at haff
    simp at haff
  · have hy3 : y ^ 3 = 1 := by
      rw [← hxy, ← pow_mul, mul_comm, pow_mul, h, one_pow]
    rw [h, hy3] at haff
    have : (2 : K) = 1 := by linear_combination haff
    rw [h2] at this
    exact zero_ne_one this

/-- **No affine kernel points.**  If `gcd (k, n) = 1` then every `K`-rational point of
`ker (1 + π^k)` is a point at infinity. -/
theorem Z_eq_zero_of_isKernelPoint [Fintype K] {n k : ℕ} (hcard : Fintype.card K = 2 ^ n)
    (hkn : Nat.Coprime k n) {X Y Z : K} (hP : IsPoint X Y Z) (hK : IsKernelPoint k X Y Z) :
    Z = 0 := by
  by_contra hZ
  set x : K := X / Z with hxdef
  have h2k : x ^ 2 ^ (k * 2) = x := by
    simpa [hxdef] using affine_fixed_by_two_k_of_isKernelPoint hK
  have hn : x ^ 2 ^ n = x := pow_two_pow_card hcard x
  have hgcd : x ^ 2 ^ Nat.gcd (k * 2) n = x := pow_two_pow_gcd h2k hn
  rw [hkn.gcd_mul_left_cancel 2] at hgcd
  have h4 : x ^ 4 = x := by
    rcases (Nat.dvd_prime Nat.prime_two).mp (Nat.gcd_dvd_left 2 n) with h | h
    · rw [h] at hgcd
      norm_num at hgcd
      calc x ^ 4 = (x ^ 2) ^ 2 := by ring
        _ = x := by rw [hgcd, hgcd]
    · rw [h] at hgcd
      norm_num at hgcd
      exact hgcd
  exact not_kernel_of_Z_ne_zero (two_eq_zero_of_card hcard) hP hK hZ h4

/-! ### The points at infinity and the kernel condition -/

/-- For a point at infinity `[X : Y : 0]` with `ω = Y / X`, the kernel condition
`π^k R = -R` is equivalent to `ω^(2^k) = ω²`. -/
lemma isKernelPoint_infinity_iff (h2 : (2 : K) = 0) {k : ℕ} {X Y : K} (hP : IsPoint X Y 0) :
    IsKernelPoint k X Y 0 ↔ (Y / X) ^ 2 ^ k = (Y / X) ^ 2 := by
  obtain ⟨hX, hY⟩ := ne_zero_of_isPoint_infinity hP
  have hXY : Y ^ 3 = X ^ 3 := cube_eq_of_isPoint_infinity h2 hP
  constructor
  · rintro ⟨c, hc, h1, h2', -⟩
    have : (Y / X) ^ 2 ^ k = X / Y := by
      rw [div_pow, h1, h2', mul_comm c X, mul_comm c Y, mul_div_mul_right _ _ hc]
    rw [this]
    field_simp
    linear_combination -hXY
  · intro hw
    refine ⟨X ^ 2 ^ k / Y, div_ne_zero (pow_ne_zero _ hX) hY, ?_, ?_, by simp⟩
    · field_simp
    · rw [div_pow, div_pow] at hw
      field_simp at hw ⊢
      have hX2 : X ^ 2 ≠ 0 := pow_ne_zero _ hX
      apply mul_left_cancel₀ hX2
      calc X ^ 2 * (Y ^ 2 ^ k * Y) = (Y ^ 2 ^ k * X ^ 2) * Y := by ring
        _ = (X ^ 2 ^ k * Y ^ 2) * Y := by rw [hw]
        _ = X ^ 2 ^ k * Y ^ 3 := by ring
        _ = X ^ 2 ^ k * X ^ 3 := by rw [hXY]
        _ = X ^ 2 * (X ^ 2 ^ k * X) := by ring

/-- For odd `k` we have `2^k ≡ 2 [MOD 3]`, hence `ω^(2^k) = ω²` for every cube root of unity.
(`π^k = π` on `E(𝔽₄)`.) -/
lemma pow_two_pow_of_cube_root {k : ℕ} (hk : Odd k) {w : K} (hw : w ^ 3 = 1) :
    w ^ 2 ^ k = w ^ 2 := by
  have hmod := two_pow_mod_three_of_odd hk
  have hdiv := Nat.mod_add_div (2 ^ k) 3
  rw [hmod] at hdiv
  obtain ⟨q, hq⟩ : ∃ q : ℕ, 2 ^ k = 3 * q + 2 := by
    refine ⟨2 ^ k / 3, ?_⟩
    omega
  rw [hq, pow_add, pow_mul, hw, one_pow, one_mul]

/-! ### The main theorems -/

/-- **Odd `n`: the rational kernel is trivial.**

For `K` a field with `2^n` elements, `n` odd and `gcd (k, n) = 1`, a point of `E(K)` lies in
`ker (1 + π^k)` if and only if it is the origin `O = [1 : 1 : 0]` (i.e. `Z = 0` and `X = Y`).

The hypothesis "`k` is odd" of the informal statement is not needed here. -/
theorem rational_kernel_odd [Fintype K] {n k : ℕ} (hn : Odd n) (hkn : Nat.Coprime k n)
    (hcard : Fintype.card K = 2 ^ n) {X Y Z : K} (hP : IsPoint X Y Z) :
    IsKernelPoint k X Y Z ↔ (Z = 0 ∧ X = Y) := by
  have h2 : (2 : K) = 0 := two_eq_zero_of_card hcard
  constructor
  · intro hK
    have hZ : Z = 0 := Z_eq_zero_of_isKernelPoint hcard hkn hP hK
    subst hZ
    obtain ⟨hX, -⟩ := ne_zero_of_isPoint_infinity hP
    refine ⟨rfl, ?_⟩
    have hw : Y / X = 1 := cube_root_eq_one_of_odd hn hcard
      (cube_ratio_of_isPoint_infinity h2 hP)
    rw [div_eq_one_iff_eq hX] at hw
    exact hw.symm
  · rintro ⟨rfl, rfl⟩
    obtain ⟨hX, -⟩ := ne_zero_of_isPoint_infinity hP
    exact ⟨X ^ 2 ^ k / X, div_ne_zero (pow_ne_zero _ hX) hX, by field_simp, by field_simp, by simp⟩

/-- **Even `n`: the rational kernel is the set of points at infinity.**

For `K` a field with `2^n` elements, `n` even and `gcd (k, n) = 1`, a point of `E(K)` lies in
`ker (1 + π^k)` if and only if it is a point at infinity, `Z = 0`.

Note that `k` is automatically odd here, since `gcd (k, n) = 1` and `n` is even. -/
theorem rational_kernel_even [Fintype K] {n k : ℕ} (hn : Even n) (hkn : Nat.Coprime k n)
    (hcard : Fintype.card K = 2 ^ n) {X Y Z : K} (hP : IsPoint X Y Z) :
    IsKernelPoint k X Y Z ↔ Z = 0 := by
  have h2 : (2 : K) = 0 := two_eq_zero_of_card hcard
  have hk : Odd k := by
    rcases Nat.even_or_odd k with hke | hko
    · exfalso
      have h2k : 2 ∣ Nat.gcd k n := Nat.dvd_gcd hke.two_dvd hn.two_dvd
      rw [hkn.gcd_eq_one] at h2k
      omega
    · exact hko
  refine ⟨fun hK => Z_eq_zero_of_isKernelPoint hcard hkn hP hK, ?_⟩
  rintro rfl
  rw [isKernelPoint_infinity_iff h2 hP]
  exact pow_two_pow_of_cube_root hk (cube_ratio_of_isPoint_infinity h2 hP)

/-- **The geometric kernel of `1 + π`.**

Over *any* field of characteristic `2` (in particular over an algebraic closure of `𝔽₂`), the
kernel of `1 + π` consists exactly of the points at infinity `[1 : ω : 0]`, `ω³ = 1`, so it has
exactly three points, without appealing to the degree of the isogeny or to separability. -/
theorem geometric_kernel_one_add_frobenius (h2 : (2 : K) = 0) {X Y Z : K} (hP : IsPoint X Y Z) :
    IsKernelPoint 1 X Y Z ↔ Z = 0 := by
  constructor
  · intro hK
    by_contra hZ
    have h4 : (X / Z) ^ 4 = X / Z := by
      have hfix := affine_fixed_by_two_k_of_isKernelPoint (k := 1) hK
      norm_num at hfix ⊢
      exact hfix
    exact not_kernel_of_Z_ne_zero h2 hP hK hZ h4
  · rintro rfl
    rw [isKernelPoint_infinity_iff h2 hP]
    exact pow_two_pow_of_cube_root odd_one (cube_ratio_of_isPoint_infinity h2 hP)

/-! ### Non-vacuity checks

The hypotheses of the two main theorems are satisfiable: they apply to `𝔽₂` (`n = 1`) and to
`𝔽₄` (`n = 2`). -/

/-- The odd case applies over `K = 𝔽₂` with `n = 1`, `k = 1`. -/
example {X Y Z : ZMod 2} (hP : IsPoint X Y Z) :
    IsKernelPoint 1 X Y Z ↔ (Z = 0 ∧ X = Y) :=
  rational_kernel_odd (n := 1) odd_one (by norm_num) (by simp) hP

/-- The even case applies over `K = 𝔽₄` with `n = 2`, `k = 3`. -/
example : ∀ X Y Z : GaloisField 2 2, IsPoint X Y Z → (IsKernelPoint 3 X Y Z ↔ Z = 0) := by
  have : Fintype (GaloisField 2 2) := Fintype.ofFinite _
  intro X Y Z hP
  refine rational_kernel_even (n := 2) (by decide) (by norm_num) ?_ hP
  rw [← Nat.card_eq_fintype_card]
  exact GaloisField.card 2 2 (by norm_num)

end KasamiCyclicAdditive.FermatCubicFrobenius
end
