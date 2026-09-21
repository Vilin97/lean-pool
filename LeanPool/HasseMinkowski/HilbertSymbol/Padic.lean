/-
Copyright (c) 2026 jayyswan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: jayyswan
-/
import LeanPool.HasseMinkowski.HilbertSymbol.Defs
import LeanPool.HasseMinkowski.Padics.Squares
import Mathlib.NumberTheory.LegendreSymbol.QuadraticChar.Basic

/-!
# The `p`-adic Hilbert symbol at an odd prime

This file begins the computation of the Hilbert symbol `(a,b)_p` on `ℚ_[p]` for odd `p`,
following Serre's explicit formula

`(a,b)_p = (-1)^{αβ(p-1)/2} · (u/p)^β · (v/p)^α`,  where `a = p^α u`, `b = p^β v`,
`u,v ∈ ℤ_[p]ˣ`, and `(·/p)` is the quadratic character modulo `p`.

The first ingredient is the "case `00`" of the formula: **two `p`-adic units have
Hilbert symbol `1`**. Although upstream states this through the Legendre symbol (with both
valuations zero the formula collapses), the underlying geometric content is just that the
ternary form `z² - u x² - v y²` has a nontrivial zero: modulo `p` this form is isotropic
(sum of two squares cover a finite field), and a nonsingular mod-`p` point Hensel-lifts.

We prove this here as `hilbertSym_padicInt_units`.  The remaining cases `10` / `11`
(one resp. two factors divisible by `p`) and the general multiplicativity `mul_left_eq`
are recorded in `HANDOFF-hilbertpadic.md` as the outstanding work; only `p = 2` is out of
scope entirely.
-/

namespace HasseMinkowski

attribute [local instance] Classical.propDecidable

/-! ### General consequences of a nontrivial zero -/

/-- A quadratic form `z² - a x² - b y²` with a nontrivial zero has Hilbert symbol `1`
(provided `a` and `b` are nonzero). -/
theorem hilbertSym_eq_one_of_sol {k : Type*} [Field k] {a b : k} (ha : a ≠ 0) (hb : b ≠ 0)
    (h : ∃ z x y : k, (z, x, y) ≠ (0, 0, 0) ∧ z ^ 2 - a * x ^ 2 - b * y ^ 2 = 0) :
    hilbertSym a b = 1 := by
  unfold hilbertSym
  rw [ite_eq_right (by rw [not_or]; exact ⟨ha, hb⟩), ite_eq_left h]

-- Theorem: if the first argument of the Hilbert symbol is a nonzero square then the symbol
-- is `1`.
theorem hilbertSym_sq_left {k : Type*} [Field k] {a b : k} (ha : a ≠ 0) (hb : b ≠ 0) :
    hilbertSym (a ^ 2) b = 1 :=
  hilbertSym_eq_one_of_sol (pow_ne_zero 2 ha) hb ⟨a, 1, 0, by simp, by ring⟩

-- Theorem: if the second argument of the Hilbert symbol is a nonzero square then the symbol
-- is `1`.
theorem hilbertSym_sq_right {k : Type*} [Field k] {a b : k} (ha : a ≠ 0) (hb : b ≠ 0) :
    hilbertSym a (b ^ 2) = 1 :=
  hilbertSym_eq_one_of_sol ha (pow_ne_zero 2 hb) ⟨b, 0, 1, by simp, by ring⟩

-- Theorem: the Hilbert symbol depends only on the square classes of its arguments: multiplying
-- either argument by a nonzero square leaves it unchanged.
theorem hilbertSym_mul_square_eq {k : Type*} [Field k] {a a' b b' : k}
    (ha' : a' ≠ 0) (hb' : b' ≠ 0) :
    hilbertSym (a * a' ^ 2) (b * b' ^ 2) = hilbertSym a b := by
  by_cases hab : a = 0 ∨ b = 0
  · rcases hab with ha | hb
    · rw [ha, zero_mul, hilbertSym_zero_left, hilbertSym_zero_left]
    · rw [hb, zero_mul, hilbertSym_zero_right, hilbertSym_zero_right]
  · have ha : a ≠ 0 := fun h => hab (Or.inl h)
    have hb : b ≠ 0 := fun h => hab (Or.inr h)
    have h1 : a * a' ^ 2 ≠ 0 := mul_ne_zero ha (pow_ne_zero 2 ha')
    have h2 : b * b' ^ 2 ≠ 0 := mul_ne_zero hb (pow_ne_zero 2 hb')
    have key : (∃ z x y : k, (z, x, y) ≠ (0, 0, 0) ∧
          z ^ 2 - (a * a' ^ 2) * x ^ 2 - (b * b' ^ 2) * y ^ 2 = 0) ↔
        (∃ z x y : k, (z, x, y) ≠ (0, 0, 0) ∧ z ^ 2 - a * x ^ 2 - b * y ^ 2 = 0) := by
      constructor
      · rintro ⟨z, x, y, hne, heq⟩
        refine ⟨z, a' * x, b' * y, ?_, ?_⟩
        · intro hc
          apply hne
          have hz : z = 0 := by simpa using congrArg Prod.fst hc
          have hx : a' * x = 0 := by simpa using congrArg (fun w => w.2.1) hc
          have hy : b' * y = 0 := by simpa using congrArg (fun w => w.2.2) hc
          have hx0 : x = 0 := (mul_eq_zero.mp hx).resolve_left ha'
          have hy0 : y = 0 := (mul_eq_zero.mp hy).resolve_left hb'
          simp [hz, hx0, hy0]
        · have e1 : a * (a' * x) ^ 2 = (a * a' ^ 2) * x ^ 2 := by ring
          have e2 : b * (b' * y) ^ 2 = (b * b' ^ 2) * y ^ 2 := by ring
          rw [e1, e2]
          exact heq
      · rintro ⟨z, x, y, hne, heq⟩
        refine ⟨z, x / a', y / b', ?_, ?_⟩
        · intro hc
          apply hne
          have hz : z = 0 := by simpa using congrArg Prod.fst hc
          have hx : x / a' = 0 := by simpa using congrArg (fun w => w.2.1) hc
          have hy : y / b' = 0 := by simpa using congrArg (fun w => w.2.2) hc
          have hx0 : x = 0 := by
            have h := congrArg (fun t => t * a') hx
            simpa [div_eq_mul_inv, ha'] using h
          have hy0 : y = 0 := by
            have h := congrArg (fun t => t * b') hy
            simpa [div_eq_mul_inv, hb'] using h
          simp [hz, hx0, hy0]
        · have hx : (a * a' ^ 2) * (x / a') ^ 2 = a * x ^ 2 := by field_simp
          have hy : (b * b' ^ 2) * (y / b') ^ 2 = b * y ^ 2 := by field_simp
          rw [hx, hy]
          exact heq
    unfold hilbertSym
    rw [ite_eq_right (show ¬(a * a' ^ 2 = 0 ∨ b * b' ^ 2 = 0) by rw [not_or]; exact ⟨h1, h2⟩),
        ite_eq_right (show ¬(a = 0 ∨ b = 0) by rw [not_or]; exact ⟨ha, hb⟩)]
    by_cases h : ∃ z x y : k, (z, x, y) ≠ (0, 0, 0) ∧ z ^ 2 - a * x ^ 2 - b * y ^ 2 = 0
    · rw [ite_eq_left h, ite_eq_left (key.mpr h)]
    · rw [ite_eq_right h, ite_eq_right (fun h' => h (key.mp h'))]

/-! ### Isotropy of `u x² + v y² = 1` over `𝔽_p` -/

-- Theorem: for odd `p` and units `u`, `v` in `ZMod p`, the equation `u x² + v y² = 1` has a
-- solution.  If either coefficient is a square this is immediate; otherwise the quotient
-- `v / u` is a square and one reduces to `ZMod.sq_add_sq`.
theorem zmod_sq_add_sq_eq_one {p : ℕ} [Fact (Nat.Prime p)] (_hp : p ≠ 2)
    {u v : ZMod p} (hu : u ≠ 0) (hv : v ≠ 0) :
    ∃ x y : ZMod p, u * x ^ 2 + v * y ^ 2 = 1 := by
  by_cases hu2 : IsSquare u
  · obtain ⟨s, hs⟩ := hu2
    have hs0 : s ≠ 0 := by
      rintro rfl
      rw [mul_zero] at hs
      exact hu hs
    exact ⟨s⁻¹, 0, by rw [hs]; field_simp; ring⟩
  · by_cases hv2 : IsSquare v
    · obtain ⟨s, hs⟩ := hv2
      have hs0 : s ≠ 0 := by
        rintro rfl
        rw [mul_zero] at hs
        exact hv hs
      exact ⟨0, s⁻¹, by rw [hs]; field_simp; ring⟩
    · have huch : (quadraticChar (ZMod p)) u = -1 := by
        rcases quadraticChar_dichotomy hu with h | h
        · exact absurd h (fun hh => hu2 ((quadraticChar_one_iff_isSquare hu).mp hh))
        · exact h
      have hvch : (quadraticChar (ZMod p)) v = -1 := by
        rcases quadraticChar_dichotomy hv with h | h
        · exact absurd h (fun hh => hv2 ((quadraticChar_one_iff_isSquare hv).mp hh))
        · exact h
      have huinv : (quadraticChar (ZMod p)) u⁻¹ = -1 := by
        have hmul : (quadraticChar (ZMod p)) u * (quadraticChar (ZMod p)) u⁻¹ = 1 := by
          rw [← map_mul, mul_inv_cancel₀ hu, map_one]
        rw [huch] at hmul
        linarith
      have hsq : IsSquare (v * u⁻¹) := by
        rw [← quadraticChar_one_iff_isSquare (mul_ne_zero hv (inv_ne_zero hu)), map_mul, hvch,
          huinv]
        norm_num
      obtain ⟨c, hc⟩ := hsq
      have hc0 : c ≠ 0 := by
        rintro rfl
        rw [mul_zero] at hc
        exact mul_ne_zero hv (inv_ne_zero hu) hc
      obtain ⟨a, b, hab⟩ := ZMod.sq_add_sq p u⁻¹
      refine ⟨a, b * c⁻¹, ?_⟩
      have hv_eq : v = c * c * u := by rw [← hc, mul_assoc, inv_mul_cancel₀ hu, mul_one]
      rw [hv_eq]
      have hbc : c * c * u * (b * c⁻¹) ^ 2 = u * b ^ 2 := by field_simp [hc0]
      rw [hbc]
      have hfac : u * a ^ 2 + u * b ^ 2 = u * (a ^ 2 + b ^ 2) := by ring
      rw [hfac, hab, mul_inv_cancel₀ hu]

/-! ### The case of two units -/

-- Theorem: the Hilbert symbol of two `p`-adic units is `1` for odd `p`.  This is case `00`
-- of Serre's formula.
theorem hilbertSym_padicInt_units {p : ℕ} [Fact (Nat.Prime p)] (hp : p ≠ 2)
    (u v : ℤ_[p]ˣ) :
    hilbertSym (u : ℚ_[p]) (v : ℚ_[p]) = 1 := by
  have huZ : PadicInt.toZMod (p := p) (u : ℤ_[p]) ≠ 0 :=
    (IsUnit.map (PadicInt.toZMod (p := p)) u.isUnit).ne_zero
  have hvZ : PadicInt.toZMod (p := p) (v : ℤ_[p]) ≠ 0 :=
    (IsUnit.map (PadicInt.toZMod (p := p)) v.isUnit).ne_zero
  obtain ⟨x, y, hxy⟩ := zmod_sq_add_sq_eq_one hp huZ hvZ
  set X : ℤ_[p] := ((x.val : ℕ) : ℤ_[p]) with hXdef
  set Y : ℤ_[p] := ((y.val : ℕ) : ℤ_[p]) with hYdef
  have hX : PadicInt.toZMod (p := p) X = x := by
    rw [hXdef, map_natCast, ZMod.natCast_zmod_val]
  have hY : PadicInt.toZMod (p := p) Y = y := by
    rw [hYdef, map_natCast, ZMod.natCast_zmod_val]
  set c : ℤ_[p] := (u : ℤ_[p]) * X ^ 2 + (v : ℤ_[p]) * Y ^ 2 with hcdef
  have hc : PadicInt.toZMod (p := p) c = 1 := by
    rw [hcdef, map_add, map_mul, map_mul, map_pow, map_pow, hX, hY]
    exact hxy
  have hndvd : ¬ (p : ℤ_[p]) ∣ c := by
    rw [PadicInt.p_dvd_iff_toZMod_eq_zero, hc]
    exact one_ne_zero
  obtain ⟨z, hz⟩ := PadicInt.isSquare_of_zmod hp hndvd (by rw [hc]; exact IsSquare.one)
  have hz0 : z ≠ 0 := by
    rintro rfl
    have hc0 : c = 0 := by rw [hz, mul_zero]
    exact hndvd (by rw [hc0]; exact dvd_zero _)
  refine hilbertSym_eq_one_of_sol ?_ ?_ ⟨z, X, Y, ?_, ?_⟩
  · rw [PadicInt.coe_ne_zero]; exact u.ne_zero
  · rw [PadicInt.coe_ne_zero]; exact v.ne_zero
  · intro h
    have hzq : (z : ℚ_[p]) = 0 := by simpa using congrArg Prod.fst h
    exact (PadicInt.coe_ne_zero.mpr hz0) hzq
  · have hcc : ((z * z : ℤ_[p]) : ℚ_[p]) = (z : ℚ_[p]) ^ 2 := by push_cast; ring
    have hcQ : (c : ℚ_[p]) = ((u : ℤ_[p]) : ℚ_[p]) * (X : ℚ_[p]) ^ 2
        + ((v : ℤ_[p]) : ℚ_[p]) * (Y : ℚ_[p]) ^ 2 := by
      rw [hcdef]
      push_cast
      ring
    rw [hz, hcc] at hcQ
    rw [hcQ]
    ring

-- Theorem: case `00` of Serre's formula in `ℚ_[p]`-intrinsic form: two `p`-adic numbers of
-- norm `1` (i.e. two units) have Hilbert symbol `1`.
theorem hilbertSym_padic_odd_case00 {p : ℕ} [Fact (Nat.Prime p)] (hp : p ≠ 2)
    {a b : ℚ_[p]} (ha : ‖a‖ = 1) (hb : ‖b‖ = 1) : hilbertSym a b = 1 := by
  let A : ℤ_[p] := ⟨a, le_of_eq ha⟩
  let B : ℤ_[p] := ⟨b, le_of_eq hb⟩
  have hA : (A : ℚ_[p]) = a := rfl
  have hB : (B : ℚ_[p]) = b := rfl
  have hAu : IsUnit A := by
    rw [PadicInt.isUnit_iff]
    change ‖(A : ℚ_[p])‖ = 1
    rw [hA, ha]
  have hBu : IsUnit B := by
    rw [PadicInt.isUnit_iff]
    change ‖(B : ℚ_[p])‖ = 1
    rw [hB, hb]
  have h := hilbertSym_padicInt_units hp hAu.unit hBu.unit
  simpa [IsUnit.unit_spec, hA, hB] using h

/-! ### Case `10`: a unit against an element of valuation `1`

Serre's formula for `(a,b)_p` with `a` a unit and `b` of valuation `1` collapses to the
Legendre symbol `(a/p)` of the unit `a`.  Geometrically the form `z² - a x² - b y²` has
its `b`-term divisible by `p`, so after rescaling to an integral solution with a unit
coordinate a mod-`p` argument identifies `a` with a square exactly when a solution exists.

The scaling lemma below is the same normalization as `Padic.exists_padicInt_solution`
(`Padics/CommonRoot.lean`), but with both coefficients arbitrary — the coefficients never
enter the rescaling. -/

section Case10

variable {p : ℕ} [Fact (Nat.Prime p)]

-- Theorem: rescaling all three coordinates of a solution by a common factor preserves the
-- equation `z² - c₁ x² - c₂ y² = 0` for arbitrary coefficients.
private lemma scaled_solution_gen {c₁ c₂ x y z t : ℚ_[p]}
    (hsol : z ^ 2 - c₁ * x ^ 2 - c₂ * y ^ 2 = 0) :
    (z * t) ^ 2 - c₁ * (x * t) ^ 2 - c₂ * (y * t) ^ 2 = 0 := by
  rw [show (z * t) ^ 2 - c₁ * (x * t) ^ 2 - c₂ * (y * t) ^ 2
      = t ^ 2 * (z ^ 2 - c₁ * x ^ 2 - c₂ * y ^ 2) by ring, hsol, mul_zero]

-- Theorem: multiplying a coordinate of norm at most `‖w‖` by `p ^ (-(w.valuation))` keeps it
-- in the unit ball.
private lemma norm_mul_pow_neg_valuation_le_one_gen {u w : ℚ_[p]} (hw : w ≠ 0)
    (hu : ‖u‖ ≤ ‖w‖) : ‖u * p ^ (-(w.valuation))‖ ≤ 1 := by
  have hp0 : (p : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.Prime.ne_zero Fact.out)
  have hw_norm : ‖w‖ = (p : ℝ) ^ (-(w.valuation)) := Padic.norm_eq_zpow_neg_valuation hw
  rw [norm_mul, Padic.norm_p_zpow, neg_neg]
  calc
    ‖u‖ * (p : ℝ) ^ w.valuation
        ≤ (p : ℝ) ^ (-(w.valuation)) * (p : ℝ) ^ w.valuation :=
          mul_le_mul_of_nonneg_right (by rw [← hw_norm]; exact hu)
            (zpow_nonneg (Nat.cast_nonneg p) _)
    _ = 1 := by rw [← zpow_add₀ hp0, neg_add_cancel, zpow_zero]

-- Theorem: multiplying `w` itself by `p ^ (-(w.valuation))` gives an element of norm `1`.
private lemma norm_mul_pow_neg_valuation_eq_one_gen {w : ℚ_[p]} (hw : w ≠ 0) :
    ‖w * p ^ (-(w.valuation))‖ = 1 := by
  have hp0 : (p : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.Prime.ne_zero Fact.out)
  rw [norm_mul, Padic.norm_p_zpow, neg_neg, Padic.norm_eq_zpow_neg_valuation hw,
    ← zpow_add₀ hp0, neg_add_cancel, zpow_zero]

-- Theorem: a nontrivial solution of `z² - c₁ x² - c₂ y² = 0` (arbitrary coefficients)
-- rescales to an integral solution at least one of whose coordinates is a unit.
private lemma exists_padicInt_solution_gen {c₁ c₂ x y z : ℚ_[p]}
    (hnontriv : (x, y, z) ≠ (0, 0, 0)) (hsol : z ^ 2 - c₁ * x ^ 2 - c₂ * y ^ 2 = 0) :
    ∃ Z X Y : ℤ_[p], (Z : ℚ_[p]) ^ 2 - c₁ * (X : ℚ_[p]) ^ 2 - c₂ * (Y : ℚ_[p]) ^ 2 = 0
      ∧ (IsUnit Z ∨ IsUnit X ∨ IsUnit Y) := by
  set m : ℝ := max ‖x‖ (max ‖y‖ ‖z‖) with hm
  have hm_ne_zero : m ≠ 0 := by
    intro h
    have hx0 : x = 0 := by
      refine norm_eq_zero.mp ?_
      exact le_antisymm (le_trans (le_max_left _ _) (le_of_eq h)) (norm_nonneg _)
    have hy0 : y = 0 := by
      refine norm_eq_zero.mp ?_
      exact le_antisymm
        (le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) (le_of_eq h)) (norm_nonneg _)
    have hz0 : z = 0 := by
      refine norm_eq_zero.mp ?_
      exact le_antisymm
        (le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) (le_of_eq h)) (norm_nonneg _)
    exact hnontriv (by simp [hx0, hy0, hz0])
  have hm_pos : 0 < m := lt_of_le_of_ne (le_trans (norm_nonneg x) (le_max_left _ _))
    (Ne.symm hm_ne_zero)
  have hcoord : ‖x‖ = m ∨ ‖y‖ = m ∨ ‖z‖ = m := by
    simp only [hm]
    rcases le_total (max ‖y‖ ‖z‖) ‖x‖ with h | h
    · exact Or.inl (Eq.symm (max_eq_left h))
    · rcases le_total ‖y‖ ‖z‖ with hyz | hzy
      · exact Or.inr (Or.inr (Eq.symm (by rw [max_eq_right h, max_eq_right hyz])))
      · exact Or.inr (Or.inl (Eq.symm (by rw [max_eq_right h, max_eq_left hzy])))
  have hxle : ‖x‖ ≤ m := le_max_left _ _
  have hyle : ‖y‖ ≤ m := le_trans (le_max_left _ _) (le_max_right _ _)
  have hzle : ‖z‖ ≤ m := le_trans (le_max_right _ _) (le_max_right _ _)
  rcases hcoord with hxmax | hymax | hzmax
  · have hx0 : x ≠ 0 := norm_pos_iff.mp (hxmax ▸ hm_pos)
    have heq : ‖x * p ^ (-(x.valuation))‖ = 1 := norm_mul_pow_neg_valuation_eq_one_gen hx0
    have hy' : ‖y * p ^ (-(x.valuation))‖ ≤ 1 :=
      norm_mul_pow_neg_valuation_le_one_gen hx0 (hxmax ▸ hyle)
    have hz' : ‖z * p ^ (-(x.valuation))‖ ≤ 1 :=
      norm_mul_pow_neg_valuation_le_one_gen hx0 (hxmax ▸ hzle)
    exact ⟨⟨z * p ^ (-(x.valuation)), hz'⟩, ⟨x * p ^ (-(x.valuation)), heq.le⟩,
      ⟨y * p ^ (-(x.valuation)), hy'⟩, scaled_solution_gen hsol,
      Or.inr (Or.inl (PadicInt.isUnit_iff.mpr heq))⟩
  · have hy0 : y ≠ 0 := norm_pos_iff.mp (hymax ▸ hm_pos)
    have heq : ‖y * p ^ (-(y.valuation))‖ = 1 := norm_mul_pow_neg_valuation_eq_one_gen hy0
    have hx' : ‖x * p ^ (-(y.valuation))‖ ≤ 1 :=
      norm_mul_pow_neg_valuation_le_one_gen hy0 (hymax ▸ hxle)
    have hz' : ‖z * p ^ (-(y.valuation))‖ ≤ 1 :=
      norm_mul_pow_neg_valuation_le_one_gen hy0 (hymax ▸ hzle)
    exact ⟨⟨z * p ^ (-(y.valuation)), hz'⟩, ⟨x * p ^ (-(y.valuation)), hx'⟩,
      ⟨y * p ^ (-(y.valuation)), heq.le⟩, scaled_solution_gen hsol,
      Or.inr (Or.inr (PadicInt.isUnit_iff.mpr heq))⟩
  · have hz0 : z ≠ 0 := norm_pos_iff.mp (hzmax ▸ hm_pos)
    have heq : ‖z * p ^ (-(z.valuation))‖ = 1 := norm_mul_pow_neg_valuation_eq_one_gen hz0
    have hx' : ‖x * p ^ (-(z.valuation))‖ ≤ 1 :=
      norm_mul_pow_neg_valuation_le_one_gen hz0 (hzmax ▸ hxle)
    have hy' : ‖y * p ^ (-(z.valuation))‖ ≤ 1 :=
      norm_mul_pow_neg_valuation_le_one_gen hz0 (hzmax ▸ hyle)
    exact ⟨⟨z * p ^ (-(z.valuation)), heq.le⟩, ⟨x * p ^ (-(z.valuation)), hx'⟩,
      ⟨y * p ^ (-(z.valuation)), hy'⟩, scaled_solution_gen hsol,
      Or.inl (PadicInt.isUnit_iff.mpr heq)⟩

-- Theorem: if `z² - u x² - c y² = 0` has a nontrivial solution with `u` a unit and
-- `‖c‖ = p⁻¹`, then `u` is a square modulo `p`.  The `c`-term vanishes mod `p`, so an
-- integral solution with a unit coordinate reduces to `u ≡ (Z/X)²`.
private theorem isSquare_toZMod_of_sol (u : ℤ_[p]ˣ) {c : ℚ_[p]}
    (hc : ‖c‖ = (p : ℝ)⁻¹)
    (h : ∃ z x y : ℚ_[p], (z, x, y) ≠ (0, 0, 0) ∧
      z ^ 2 - (u : ℚ_[p]) * x ^ 2 - c * y ^ 2 = 0) :
    IsSquare (PadicInt.toZMod (u : ℤ_[p])) := by
  obtain ⟨z, x, y, hne, hsol⟩ := h
  have hne' : (x, y, z) ≠ (0, 0, 0) := by intro hc; exact hne (by simp_all)
  obtain ⟨Z, X, Y, hZY, hunit⟩ :=
    exists_padicInt_solution_gen (c₁ := (u : ℚ_[p])) (c₂ := c) hne' hsol
  set M : ℤ_[p] := Z ^ 2 - (u : ℤ_[p]) * X ^ 2 with hMdef
  have hM : (M : ℚ_[p]) = c * (Y : ℚ_[p]) ^ 2 := by
    rw [hMdef]
    push_cast
    linear_combination hZY
  have hMnorm : ‖M‖ ≤ (p : ℝ)⁻¹ := by
    have hYle : ‖Y‖ ≤ 1 := PadicInt.norm_le_one Y
    have hY2 : ‖Y‖ ^ 2 ≤ 1 := by nlinarith [norm_nonneg Y, hYle]
    calc ‖M‖ = ‖(M : ℚ_[p])‖ := PadicInt.norm_def
      _ = (p : ℝ)⁻¹ * ‖(Y : ℚ_[p])‖ ^ 2 := by rw [hM, norm_mul, hc, norm_pow]
      _ = (p : ℝ)⁻¹ * ‖Y‖ ^ 2 := by rw [PadicInt.norm_def]
      _ ≤ (p : ℝ)⁻¹ * 1 := by
            exact mul_le_mul_of_nonneg_left hY2 (by positivity)
      _ = (p : ℝ)⁻¹ := mul_one _
  have hpM : (p : ℤ_[p]) ∣ M := by
    rw [← PadicInt.norm_lt_one_iff_dvd]
    have hp1 : (1 : ℝ) < p := by exact_mod_cast (Nat.Prime.one_lt Fact.out)
    calc ‖M‖ ≤ (p : ℝ)⁻¹ := hMnorm
      _ < 1 := inv_lt_one_of_one_lt₀ hp1
  have htoM : PadicInt.toZMod M = 0 := (PadicInt.p_dvd_iff_toZMod_eq_zero).mp hpM
  have hrel : PadicInt.toZMod Z ^ 2
      = PadicInt.toZMod (u : ℤ_[p]) * PadicInt.toZMod X ^ 2 := by
    have h := htoM
    rw [hMdef, map_sub, map_mul, map_pow, map_pow] at h
    linear_combination h
  have hXu : PadicInt.toZMod X ≠ 0 := by
    intro hX0
    have hZ0 : PadicInt.toZMod Z = 0 := by
      have h : (PadicInt.toZMod Z) ^ 2 = 0 := by
        rw [hrel, hX0]; ring
      exact sq_eq_zero_iff.mp h
    have hZnu : ¬ IsUnit Z :=
      fun hZ => (IsUnit.map (PadicInt.toZMod (p := p)) hZ).ne_zero hZ0
    have hXnu : ¬ IsUnit X :=
      fun hX => (IsUnit.map (PadicInt.toZMod (p := p)) hX).ne_zero hX0
    have hYu : IsUnit Y := by
      rcases hunit with h | h | h
      · exact absurd h hZnu
      · exact absurd h hXnu
      · exact h
    have hYnorm : ‖(Y : ℚ_[p])‖ = 1 := by
      rw [← PadicInt.norm_def]; exact PadicInt.isUnit_iff.mp hYu
    have hMbig : ‖M‖ = (p : ℝ)⁻¹ := by
      rw [PadicInt.norm_def, hM, norm_mul, hc, norm_pow, hYnorm, one_pow, mul_one]
    have hp2M : ((p : ℤ_[p])) ^ 2 ∣ M := by
      have hZdvd : (p : ℤ_[p]) ∣ Z :=
        (PadicInt.norm_lt_one_iff_dvd Z).mp (PadicInt.not_isUnit_iff.mp hZnu)
      have hXdvd : (p : ℤ_[p]) ∣ X :=
        (PadicInt.norm_lt_one_iff_dvd X).mp (PadicInt.not_isUnit_iff.mp hXnu)
      obtain ⟨a, ha⟩ := hZdvd
      obtain ⟨b, hb⟩ := hXdvd
      refine ⟨a ^ 2 - (u : ℤ_[p]) * b ^ 2, ?_⟩
      rw [hMdef, ha, hb]; ring
    have hMsmall : ‖M‖ ≤ (p : ℝ) ^ (-(2 : ℤ)) := by
      have hmem : M ∈ Ideal.span {((p : ℤ_[p])) ^ 2} := Ideal.mem_span_singleton.mpr hp2M
      simpa using (PadicInt.norm_le_pow_iff_mem_span_pow M 2).mpr hmem
    have hp1 : (1 : ℝ) < p := by exact_mod_cast (Nat.Prime.one_lt Fact.out)
    have hlt : (p : ℝ) ^ (-(2 : ℤ)) < (p : ℝ)⁻¹ := by
      rw [show (p : ℝ)⁻¹ = (p : ℝ) ^ (-(1 : ℤ)) by rw [zpow_neg_one]]
      exact (zpow_lt_zpow_iff_right₀ hp1).mpr (by norm_num)
    rw [hMbig] at hMsmall
    linarith
  refine ⟨PadicInt.toZMod Z * (PadicInt.toZMod X)⁻¹, ?_⟩
  have key : PadicInt.toZMod (u : ℤ_[p])
      = PadicInt.toZMod Z ^ 2 * (PadicInt.toZMod X)⁻¹ ^ 2 := by
    rw [hrel, mul_assoc, ← mul_pow, mul_inv_cancel₀ hXu, one_pow, mul_one]
  rw [key, ← pow_two, mul_pow]

-- Theorem: case `10` of Serre's formula for odd `p`: the Hilbert symbol of a `p`-adic unit
-- `u` and an element `c` of norm `p⁻¹` (i.e. valuation `1`) is the Legendre symbol `(u/p)`,
-- independently of the unit part of `c`.
theorem hilbertSym_padic_odd_case10 (hp : p ≠ 2) (u : ℤ_[p]ˣ) {c : ℚ_[p]}
    (hc : ‖c‖ = (p : ℝ)⁻¹) :
    hilbertSym (u : ℚ_[p]) c = (quadraticChar (ZMod p)) (PadicInt.toZMod (u : ℤ_[p])) := by
  have hu_ne : (u : ℚ_[p]) ≠ 0 := by
    intro h
    have h1 : ‖(u : ℚ_[p])‖ = 1 := by
      rw [← PadicInt.norm_def]; exact PadicInt.isUnit_iff.mp u.isUnit
    rw [h, norm_zero] at h1
    norm_num at h1
  have hc_ne : c ≠ 0 := by
    rintro rfl
    rw [norm_zero] at hc
    have : (0 : ℝ) < (p : ℝ)⁻¹ := inv_pos.mpr (Nat.cast_pos.mpr (Nat.Prime.pos Fact.out))
    linarith
  have huZ : PadicInt.toZMod (u : ℤ_[p]) ≠ 0 :=
    (IsUnit.map (PadicInt.toZMod (p := p)) u.isUnit).ne_zero
  by_cases hsq : IsSquare (PadicInt.toZMod (u : ℤ_[p]))
  · rw [(quadraticChar_one_iff_isSquare huZ).mpr hsq]
    have hndvd : ¬ (p : ℤ_[p]) ∣ (u : ℤ_[p]) := by
      rw [PadicInt.p_dvd_iff_toZMod_eq_zero]; exact huZ
    obtain ⟨s, hs⟩ := PadicInt.isSquare_of_zmod hp hndvd hsq
    have hs0 : s ≠ 0 := by
      rintro rfl
      exact u.ne_zero (by rw [hs]; ring)
    have hsQ : (s : ℚ_[p]) ≠ 0 := PadicInt.coe_ne_zero.mpr hs0
    have hueq : (u : ℚ_[p]) = (s : ℚ_[p]) ^ 2 := by
      have := congrArg (fun t : ℤ_[p] => (t : ℚ_[p])) hs
      push_cast at this
      simpa [pow_two] using this
    rw [hueq]
    exact hilbertSym_sq_left hsQ hc_ne
  · have hchi : (quadraticChar (ZMod p)) (PadicInt.toZMod (u : ℤ_[p])) = -1 := by
      rcases quadraticChar_dichotomy huZ with h1 | h1
      · exact absurd ((quadraticChar_one_iff_isSquare huZ).mp h1) hsq
      · exact h1
    rw [hchi]
    unfold hilbertSym
    rw [ite_eq_right (by rw [not_or]; exact ⟨hu_ne, hc_ne⟩)]
    rw [ite_eq_right (fun hsol => hsq (isSquare_toZMod_of_sol u hc hsol))]

end Case10

/-! ### Case `11`: two elements of valuation `1`

With both arguments of valuation `1` the form `z² - p x² - p y²` has a nontrivial zero
exactly when `-1` is a square modulo `p`, i.e. `(p,p)_p = (-1)^{(p-1)/2}`.  The square
direction is the explicit solution `(0, s, 1)` with `s² = -1`; the non-square direction
reduces an integral solution mod `p` twice, forcing `X² + Y² ≡ 0`. -/

section Case11

variable {p : ℕ} [Fact (Nat.Prime p)]

-- Theorem: a nontrivial solution of `z² - p x² - p y² = 0` forces `-1` to be a square
-- modulo `p`.
private theorem isSquare_neg_one_of_sol {z x y : ℚ_[p]}
    (hne : (z, x, y) ≠ (0, 0, 0))
    (hsol : z ^ 2 - (p : ℚ_[p]) * x ^ 2 - (p : ℚ_[p]) * y ^ 2 = 0) :
    IsSquare (-1 : ZMod p) := by
  have hne' : (x, y, z) ≠ (0, 0, 0) := by intro hc; exact hne (by simp_all)
  obtain ⟨Z, X, Y, hZY, hunit⟩ :=
    exists_padicInt_solution_gen (c₁ := (p : ℚ_[p])) (c₂ := (p : ℚ_[p])) hne' hsol
  set S : ℤ_[p] := X ^ 2 + Y ^ 2 with hSdef
  have hZsQ : (Z : ℚ_[p]) ^ 2 = (p : ℚ_[p]) * (S : ℚ_[p]) := by
    rw [hSdef]
    push_cast
    linear_combination hZY
  have hZs : Z ^ 2 = (p : ℤ_[p]) * S := by
    apply PadicInt.ext
    push_cast
    exact hZsQ
  have hZ0 : PadicInt.toZMod Z = 0 := by
    have h : (PadicInt.toZMod Z) ^ 2 = 0 := by
      have := congrArg (PadicInt.toZMod (p := p)) hZs
      simpa using this
    exact sq_eq_zero_iff.mp h
  obtain ⟨Z₁, hZ₁⟩ := (PadicInt.p_dvd_iff_toZMod_eq_zero).mpr hZ0
  have hp0 : (p : ℤ_[p]) ≠ 0 := by
    intro h
    have hnorm : ‖(p : ℤ_[p])‖ = 0 := by rw [h, norm_zero]
    rw [PadicInt.norm_p] at hnorm
    exact (inv_ne_zero (Nat.cast_ne_zero.mpr (Nat.Prime.ne_zero Fact.out))) hnorm
  have hS : S = (p : ℤ_[p]) * Z₁ ^ 2 := by
    have h : (p : ℤ_[p]) * ((p : ℤ_[p]) * Z₁ ^ 2) = (p : ℤ_[p]) * S := by
      rw [← hZs, hZ₁]; ring
    exact (mul_left_cancel₀ hp0 h).symm
  have htoS : PadicInt.toZMod S = 0 :=
    (PadicInt.p_dvd_iff_toZMod_eq_zero).mp ⟨Z₁ ^ 2, hS⟩
  have hSrel : (PadicInt.toZMod X) ^ 2 + (PadicInt.toZMod Y) ^ 2 = 0 := by
    have h := htoS
    rw [hSdef, map_add, map_pow, map_pow] at h
    linear_combination h
  have hZu : ¬ IsUnit Z :=
    fun hZ => (IsUnit.map (PadicInt.toZMod (p := p)) hZ).ne_zero hZ0
  rcases hunit with h | h | h
  · exact absurd h hZu
  · have hX0 : PadicInt.toZMod X ≠ 0 :=
      (IsUnit.map (PadicInt.toZMod (p := p)) h).ne_zero
    refine ⟨PadicInt.toZMod Y * (PadicInt.toZMod X)⁻¹, ?_⟩
    have hb2 : (PadicInt.toZMod Y) ^ 2 = -(PadicInt.toZMod X) ^ 2 := by
      linear_combination hSrel
    rw [← pow_two, mul_pow, hb2, inv_pow, neg_mul, neg_inj,
      mul_inv_cancel₀ (pow_ne_zero 2 hX0)]
  · have hY0 : PadicInt.toZMod Y ≠ 0 :=
      (IsUnit.map (PadicInt.toZMod (p := p)) h).ne_zero
    refine ⟨PadicInt.toZMod X * (PadicInt.toZMod Y)⁻¹, ?_⟩
    have ha2 : (PadicInt.toZMod X) ^ 2 = -(PadicInt.toZMod Y) ^ 2 := by
      linear_combination hSrel
    rw [← pow_two, mul_pow, ha2, inv_pow, neg_mul, neg_inj,
      mul_inv_cancel₀ (pow_ne_zero 2 hY0)]

-- Theorem: case `11` of Serre's formula for odd `p`: `(p,p)_p = (-1)^{(p-1)/2}`, written
-- here as the quadratic character of `-1` modulo `p`.
theorem hilbertSym_padic_odd_case11 (hp : p ≠ 2) :
    hilbertSym (p : ℚ_[p]) (p : ℚ_[p]) = (quadraticChar (ZMod p)) (-1 : ZMod p) := by
  have hpQ_ne : (p : ℚ_[p]) ≠ 0 := by
    intro h
    have hnorm : ‖(p : ℚ_[p])‖ = 0 := by rw [h, norm_zero]
    rw [Padic.norm_p] at hnorm
    exact (inv_ne_zero (Nat.cast_ne_zero.mpr (Nat.Prime.ne_zero Fact.out))) hnorm
  have hneg_ne : (-1 : ZMod p) ≠ 0 := neg_ne_zero.mpr one_ne_zero
  by_cases hsq : IsSquare (-1 : ZMod p)
  · rw [(quadraticChar_one_iff_isSquare hneg_ne).mpr hsq]
    have hndvd : ¬ (p : ℤ_[p]) ∣ (-1 : ℤ_[p]) := by
      rw [PadicInt.p_dvd_iff_toZMod_eq_zero]
      simp [hneg_ne]
    obtain ⟨s, hs⟩ := PadicInt.isSquare_of_zmod hp hndvd (by simpa using hsq)
    have hs2 : (s : ℚ_[p]) ^ 2 = -1 := by
      have := congrArg (fun t : ℤ_[p] => (t : ℚ_[p])) hs
      push_cast at this
      simpa [pow_two] using this.symm
    refine hilbertSym_eq_one_of_sol hpQ_ne hpQ_ne
      ⟨(0 : ℚ_[p]), (s : ℚ_[p]), (1 : ℚ_[p]), by simp, ?_⟩
    rw [hs2]; ring
  · have hchi : (quadraticChar (ZMod p)) (-1 : ZMod p) = -1 := by
      rcases quadraticChar_dichotomy hneg_ne with h1 | h1
      · exact absurd ((quadraticChar_one_iff_isSquare hneg_ne).mp h1) hsq
      · exact h1
    rw [hchi]
    unfold hilbertSym
    rw [ite_eq_right (by rw [not_or]; exact ⟨hpQ_ne, hpQ_ne⟩)]
    rw [ite_eq_right (by
      rintro ⟨z, x, y, hne, hsol⟩
      exact hsq (isSquare_neg_one_of_sol hne hsol))]

-- Theorem: a nontrivial solution of `z² - p u x² - p v y² = 0` forces `-uv` to be a square
-- modulo `p`.
private theorem isSquare_neg_mul_of_sol (u v : ℤ_[p]ˣ) {z x y : ℚ_[p]}
    (hne : (z, x, y) ≠ (0, 0, 0))
    (hsol : z ^ 2 - (p : ℚ_[p]) * (u : ℚ_[p]) * x ^ 2
      - (p : ℚ_[p]) * (v : ℚ_[p]) * y ^ 2 = 0) :
    IsSquare (-(PadicInt.toZMod (u : ℤ_[p]) * PadicInt.toZMod (v : ℤ_[p]))) := by
  have hne' : (x, y, z) ≠ (0, 0, 0) := by intro hc; exact hne (by simp_all)
  obtain ⟨Z, X, Y, hZY, hunit⟩ :=
    exists_padicInt_solution_gen (c₁ := (p : ℚ_[p]) * (u : ℚ_[p]))
      (c₂ := (p : ℚ_[p]) * (v : ℚ_[p])) hne' hsol
  set S : ℤ_[p] := (u : ℤ_[p]) * X ^ 2 + (v : ℤ_[p]) * Y ^ 2 with hSdef
  have hZsQ : (Z : ℚ_[p]) ^ 2 = (p : ℚ_[p]) * (S : ℚ_[p]) := by
    rw [hSdef]
    push_cast
    linear_combination hZY
  have hZs : Z ^ 2 = (p : ℤ_[p]) * S := by
    apply PadicInt.ext
    push_cast
    exact hZsQ
  have hZ0 : PadicInt.toZMod Z = 0 := by
    have h : (PadicInt.toZMod Z) ^ 2 = 0 := by
      have := congrArg (PadicInt.toZMod (p := p)) hZs
      simpa using this
    exact sq_eq_zero_iff.mp h
  obtain ⟨Z₁, hZ₁⟩ := (PadicInt.p_dvd_iff_toZMod_eq_zero).mpr hZ0
  have hp0 : (p : ℤ_[p]) ≠ 0 := by
    intro h
    have hnorm : ‖(p : ℤ_[p])‖ = 0 := by rw [h, norm_zero]
    rw [PadicInt.norm_p] at hnorm
    exact (inv_ne_zero (Nat.cast_ne_zero.mpr (Nat.Prime.ne_zero Fact.out))) hnorm
  have hS : S = (p : ℤ_[p]) * Z₁ ^ 2 := by
    have h : (p : ℤ_[p]) * ((p : ℤ_[p]) * Z₁ ^ 2) = (p : ℤ_[p]) * S := by
      rw [← hZs, hZ₁]; ring
    exact (mul_left_cancel₀ hp0 h).symm
  have htoS : PadicInt.toZMod S = 0 :=
    (PadicInt.p_dvd_iff_toZMod_eq_zero).mp ⟨Z₁ ^ 2, hS⟩
  have hSrel : PadicInt.toZMod (u : ℤ_[p]) * (PadicInt.toZMod X) ^ 2
      + PadicInt.toZMod (v : ℤ_[p]) * (PadicInt.toZMod Y) ^ 2 = 0 := by
    have h := htoS
    rw [hSdef, map_add, map_mul, map_mul, map_pow, map_pow] at h
    linear_combination h
  have hZu : ¬ IsUnit Z :=
    fun hZ => (IsUnit.map (PadicInt.toZMod (p := p)) hZ).ne_zero hZ0
  rcases hunit with h | h | h
  · exact absurd h hZu
  · have hX0 : PadicInt.toZMod X ≠ 0 :=
      (IsUnit.map (PadicInt.toZMod (p := p)) h).ne_zero
    refine ⟨PadicInt.toZMod (v : ℤ_[p]) * PadicInt.toZMod Y * (PadicInt.toZMod X)⁻¹, ?_⟩
    field_simp [hX0]
    linear_combination (-(PadicInt.toZMod (v : ℤ_[p]))) * hSrel
  · have hY0 : PadicInt.toZMod Y ≠ 0 :=
      (IsUnit.map (PadicInt.toZMod (p := p)) h).ne_zero
    refine ⟨PadicInt.toZMod (u : ℤ_[p]) * PadicInt.toZMod X * (PadicInt.toZMod Y)⁻¹, ?_⟩
    field_simp [hY0]
    linear_combination (-(PadicInt.toZMod (u : ℤ_[p]))) * hSrel

-- Theorem: case `11` with unit parts: for units `u`, `v` and odd `p`,
-- `(p u, p v)_p = (-1)^{(p-1)/2} (u/p) (v/p) = χ(-uv)`.
theorem hilbertSym_padic_odd_case11_units (hp : p ≠ 2) (u v : ℤ_[p]ˣ) :
    hilbertSym ((p : ℚ_[p]) * (u : ℚ_[p])) ((p : ℚ_[p]) * (v : ℚ_[p]))
      = (quadraticChar (ZMod p))
          (-(PadicInt.toZMod (u : ℤ_[p]) * PadicInt.toZMod (v : ℤ_[p]))) := by
  have hpQ_ne : (p : ℚ_[p]) ≠ 0 := by
    intro h
    have hnorm : ‖(p : ℚ_[p])‖ = 0 := by rw [h, norm_zero]
    rw [Padic.norm_p] at hnorm
    exact (inv_ne_zero (Nat.cast_ne_zero.mpr (Nat.Prime.ne_zero Fact.out))) hnorm
  have hu_ne : (u : ℚ_[p]) ≠ 0 := by
    intro h
    have h1 : ‖(u : ℚ_[p])‖ = 1 := by
      rw [← PadicInt.norm_def]; exact PadicInt.isUnit_iff.mp u.isUnit
    rw [h, norm_zero] at h1
    norm_num at h1
  have hv_ne : (v : ℚ_[p]) ≠ 0 := by
    intro h
    have h1 : ‖(v : ℚ_[p])‖ = 1 := by
      rw [← PadicInt.norm_def]; exact PadicInt.isUnit_iff.mp v.isUnit
    rw [h, norm_zero] at h1
    norm_num at h1
  have hne : -(PadicInt.toZMod (u : ℤ_[p]) * PadicInt.toZMod (v : ℤ_[p])) ≠ 0 := by
    simp only [neg_ne_zero, mul_ne_zero_iff]
    exact ⟨(IsUnit.map (PadicInt.toZMod (p := p)) u.isUnit).ne_zero,
      (IsUnit.map (PadicInt.toZMod (p := p)) v.isUnit).ne_zero⟩
  by_cases hsq : IsSquare
      (-(PadicInt.toZMod (u : ℤ_[p]) * PadicInt.toZMod (v : ℤ_[p])))
  · rw [(quadraticChar_one_iff_isSquare hne).mpr hsq]
    have hndvd : ¬ (p : ℤ_[p]) ∣ (-((u : ℤ_[p]) * (v : ℤ_[p]))) := by
      rw [PadicInt.p_dvd_iff_toZMod_eq_zero, map_neg, map_mul]
      exact hne
    obtain ⟨s, hs⟩ := PadicInt.isSquare_of_zmod hp hndvd (by simpa using hsq)
    have hs0 : s ≠ 0 := by
      intro h
      rw [h, mul_zero] at hs
      exact (mul_ne_zero u.ne_zero v.ne_zero) (neg_eq_zero.mp hs)
    have hsQ : (s : ℚ_[p]) ≠ 0 := PadicInt.coe_ne_zero.mpr hs0
    have hs2 : (s : ℚ_[p]) ^ 2 = -((u : ℚ_[p]) * (v : ℚ_[p])) := by
      have := congrArg (fun t : ℤ_[p] => (t : ℚ_[p])) hs
      push_cast at this
      simpa [pow_two] using this.symm
    refine hilbertSym_eq_one_of_sol (mul_ne_zero hpQ_ne hu_ne) (mul_ne_zero hpQ_ne hv_ne)
      ⟨(p : ℚ_[p]), (((u : ℚ_[p]) + (p : ℚ_[p])) / (2 * (u : ℚ_[p]))),
        (((p : ℚ_[p]) - (u : ℚ_[p])) / (2 * (s : ℚ_[p]))), by simp [hpQ_ne], ?_⟩
    have haux : (u : ℚ_[p]) * ((((u : ℚ_[p]) + (p : ℚ_[p])) / (2 * (u : ℚ_[p])))) ^ 2
        + (v : ℚ_[p]) * ((((p : ℚ_[p]) - (u : ℚ_[p])) / (2 * (s : ℚ_[p])))) ^ 2
        = (p : ℚ_[p]) := by
      field_simp [hu_ne, hsQ]
      rw [hs2]; ring
    rw [show (p : ℚ_[p]) ^ 2 - (p : ℚ_[p]) * (u : ℚ_[p])
          * (((u : ℚ_[p]) + (p : ℚ_[p])) / (2 * (u : ℚ_[p]))) ^ 2
          - (p : ℚ_[p]) * (v : ℚ_[p])
          * (((p : ℚ_[p]) - (u : ℚ_[p])) / (2 * (s : ℚ_[p]))) ^ 2
        = (p : ℚ_[p]) ^ 2 - (p : ℚ_[p]) * ((u : ℚ_[p])
          * (((u : ℚ_[p]) + (p : ℚ_[p])) / (2 * (u : ℚ_[p]))) ^ 2
          + (v : ℚ_[p])
          * (((p : ℚ_[p]) - (u : ℚ_[p])) / (2 * (s : ℚ_[p]))) ^ 2) by ring, haux]
    ring
  · have hchi : (quadraticChar (ZMod p))
        (-(PadicInt.toZMod (u : ℤ_[p]) * PadicInt.toZMod (v : ℤ_[p]))) = -1 := by
      rcases quadraticChar_dichotomy hne with h1 | h1
      · exact absurd ((quadraticChar_one_iff_isSquare hne).mp h1) hsq
      · exact h1
    rw [hchi]
    unfold hilbertSym
    rw [ite_eq_right (by
      rw [not_or]
      exact ⟨mul_ne_zero hpQ_ne hu_ne, mul_ne_zero hpQ_ne hv_ne⟩)]
    rw [ite_eq_right (by
      rintro ⟨z, x, y, hne2, hsol⟩
      exact hsq (isSquare_neg_mul_of_sol u v hne2 hsol))]

end Case11

/-! ### The general formula for odd `p`

Assembling the four square-class cases gives Serre's formula.  For nonzero `a, b : ℚ_[p]` write
`a = p ^ α · u`, `b = p ^ β · v` with `α = a.valuation`, `β = b.valuation` and units
`u = padicUnit a ha`, `v = padicUnit b hb` (the "unit part" `a · p ^ (-α)`).  Then

`(a,b)_p = (-1)^{αβ(p-1)/2} · χ(u)^β · χ(v)^α`,   `χ = quadraticChar (ZMod p)`.

Since `χ(-1) = (-1)^{(p-1)/2}` the sign is `χ(-1)^{αβ}`.  Negative exponents are handled by
`parityPow`, which is `b ^ n` when `b = ±1` and depends only on the parity of `n`.

The proof reduces `α`, `β` modulo `2` by absorbing `(p^{α/2})²` into the arguments through
`hilbertSym_mul_square_eq`, then checks the four parities against the case lemmas `00`, `10`
and `11`.  Bilinearity in the first argument follows formally. -/

section General

variable {p : ℕ} [Fact (Nat.Prime p)]

-- Theorem: `p` is nonzero as an element of `ℚ_[p]`.
private lemma padic_p_ne_zero : (p : ℚ_[p]) ≠ 0 := by
  intro h
  have hnorm : ‖(p : ℚ_[p])‖ = 0 := by rw [h, norm_zero]
  rw [Padic.norm_p] at hnorm
  exact (inv_ne_zero (Nat.cast_ne_zero.mpr (Nat.Prime.ne_zero Fact.out))) hnorm

/-- The unit part of a nonzero `p`-adic number: `a = p ^ a.valuation * padicUnit a ha`. -/
noncomputable def padicUnit (a : ℚ_[p]) (ha : a ≠ 0) : ℤ_[p]ˣ :=
  let w : ℚ_[p] := a * (p : ℚ_[p]) ^ (-(a.valuation))
  have hw : ‖w‖ = 1 := by
    have hp0 : (p : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.Prime.ne_zero Fact.out)
    rw [norm_mul, Padic.norm_p_zpow, Padic.norm_eq_zpow_neg_valuation ha, neg_neg,
      ← zpow_add₀ hp0, neg_add_cancel, zpow_zero]
  let A : ℤ_[p] := ⟨w, le_of_eq hw⟩
  have hAu : IsUnit A := by
    rw [PadicInt.isUnit_iff]
    change ‖(A : ℚ_[p])‖ = 1
    exact hw
  hAu.unit

-- Theorem: the underlying `p`-adic number of `padicUnit a ha` is `a * p ^ (-(a.valuation))`.
private lemma coe_padicUnit (a : ℚ_[p]) (ha : a ≠ 0) :
    ((padicUnit a ha : ℤ_[p]) : ℚ_[p]) = a * (p : ℚ_[p]) ^ (-(a.valuation)) := by
  rw [padicUnit]
  exact congrArg (fun t : ℤ_[p] => (t : ℚ_[p])) (IsUnit.unit_spec _)

-- Theorem: the unit part of a nonzero `p`-adic number has norm `1`.
private lemma norm_padicUnit (a : ℚ_[p]) (ha : a ≠ 0) :
    ‖((padicUnit a ha : ℤ_[p]) : ℚ_[p])‖ = 1 := by
  rw [coe_padicUnit]
  exact norm_mul_pow_neg_valuation_eq_one_gen ha

-- Theorem: every nonzero `p`-adic number is `p ^ a.valuation` times its unit part.
private lemma padicUnit_spec (a : ℚ_[p]) (ha : a ≠ 0) :
    a = (p : ℚ_[p]) ^ a.valuation * ((padicUnit a ha : ℤ_[p]) : ℚ_[p]) := by
  have hp0 := padic_p_ne_zero (p := p)
  rw [coe_padicUnit]
  calc a = a * 1 := (mul_one a).symm
    _ = a * ((p : ℚ_[p]) ^ a.valuation * (p : ℚ_[p]) ^ (-(a.valuation))) := by
          rw [← zpow_add₀ hp0, add_neg_cancel, zpow_zero]
    _ = (p : ℚ_[p]) ^ a.valuation * (a * (p : ℚ_[p]) ^ (-(a.valuation))) := by ring

/-- `parityPow b n` is `b ^ n` when `b = ±1`, well defined for negative `n`. -/
def parityPow (b n : ℤ) : ℤ := if Even n then 1 else b

-- Theorem: `parityPow b n = 1` when `n` is even.
private lemma parityPow_of_even {b n : ℤ} (h : Even n) : parityPow b n = 1 :=
  ite_eq_left h

-- Theorem: `parityPow b n = b` when `n` is odd.
private lemma parityPow_of_odd {b n : ℤ} (h : ¬ Even n) : parityPow b n = b :=
  ite_eq_right h

-- Theorem: `parityPow b` is additive in the exponent when `b ^ 2 = 1`.
private lemma parityPow_add (b : ℤ) (hb : b ^ 2 = 1) (m n : ℤ) :
    parityPow b (m + n) = parityPow b m * parityPow b n := by
  rcases Int.even_or_odd m with hm | hm <;> rcases Int.even_or_odd n with hn | hn
  · rw [parityPow_of_even (hm.add hn), parityPow_of_even hm, parityPow_of_even hn, one_mul]
  · rw [parityPow_of_odd (Int.not_even_iff_odd.mpr (hm.add_odd hn)), parityPow_of_even hm,
      parityPow_of_odd (Int.not_even_iff_odd.mpr hn), one_mul]
  · rw [parityPow_of_odd (Int.not_even_iff_odd.mpr (hm.add_even hn)),
      parityPow_of_odd (Int.not_even_iff_odd.mpr hm), parityPow_of_even hn, mul_one]
  · rw [parityPow_of_even (hm.add_odd hn), parityPow_of_odd (Int.not_even_iff_odd.mpr hm),
      parityPow_of_odd (Int.not_even_iff_odd.mpr hn), ← pow_two, hb]

-- Theorem: `parityPow` is multiplicative in the base.
private lemma parityPow_mul (b₁ b₂ n : ℤ) :
    parityPow (b₁ * b₂) n = parityPow b₁ n * parityPow b₂ n := by
  by_cases h : Even n
  · rw [parityPow_of_even h, parityPow_of_even h, parityPow_of_even h, one_mul]
  · rw [parityPow_of_odd h, parityPow_of_odd h, parityPow_of_odd h]

-- Theorem: the square of `χ(-1)` is `1`.
private lemma chi_neg_one_sq : ((quadraticChar (ZMod p)) (-1 : ZMod p)) ^ 2 = 1 := by
  rcases quadraticChar_dichotomy (show (-1 : ZMod p) ≠ 0 from neg_ne_zero.mpr one_ne_zero)
    with h | h <;> rw [h] <;> norm_num

-- Theorem: for a `p`-adic unit `u`, the square of `χ(u)` is `1`.
private lemma chi_unit_sq (u : ℤ_[p]ˣ) :
    ((quadraticChar (ZMod p)) (PadicInt.toZMod (u : ℤ_[p]))) ^ 2 = 1 := by
  rcases quadraticChar_dichotomy
    (IsUnit.map (PadicInt.toZMod (p := p)) u.isUnit).ne_zero with h | h <;>
    rw [h] <;> norm_num

-- Theorem: the norm of `p` times a `p`-adic unit is `p⁻¹`.
private lemma norm_p_mul_unit (u : ℤ_[p]ˣ) :
    ‖(p : ℚ_[p]) * (u : ℚ_[p])‖ = (p : ℝ)⁻¹ := by
  have hu1 : ‖(u : ℚ_[p])‖ = 1 := by
    rw [← PadicInt.norm_def]; exact PadicInt.isUnit_iff.mp u.isUnit
  rw [norm_mul, Padic.norm_p, hu1, mul_one]

-- Theorem: multiplication of units is compatible with `padicUnit`.
private lemma padicUnit_mul (a a' : ℚ_[p]) (ha : a ≠ 0) (ha' : a' ≠ 0) :
    (padicUnit (a * a') (mul_ne_zero ha ha') : ℤ_[p])
      = (padicUnit a ha : ℤ_[p]) * (padicUnit a' ha' : ℤ_[p]) := by
  apply PadicInt.ext
  rw [PadicInt.coe_mul, coe_padicUnit, coe_padicUnit, coe_padicUnit,
    Padic.valuation_mul ha ha']
  have hp0 := padic_p_ne_zero (p := p)
  have hneg : -(a.valuation + a'.valuation) = -a.valuation + -a'.valuation := by ring
  rw [hneg, zpow_add₀ hp0]
  ring

-- Theorem: reduction of the valuation modulo `2` (absorbing `(p^{α/2})²`).
private lemma hilbertSym_reduce (a b : ℚ_[p]) (ha : a ≠ 0) (hb : b ≠ 0) :
    hilbertSym a b
      = hilbertSym ((p : ℚ_[p]) ^ (a.valuation % 2)
            * ((padicUnit a ha : ℤ_[p]) : ℚ_[p]))
          ((p : ℚ_[p]) ^ (b.valuation % 2)
            * ((padicUnit b hb : ℤ_[p]) : ℚ_[p])) := by
  have hp0 := padic_p_ne_zero (p := p)
  have hpα : (p : ℚ_[p]) ^ a.valuation
      = (p : ℚ_[p]) ^ (a.valuation % 2) * ((p : ℚ_[p]) ^ (a.valuation / 2)) ^ 2 := by
    have hdec : a.valuation = a.valuation % 2 + 2 * (a.valuation / 2) := by omega
    nth_rewrite 1 [hdec]
    rw [zpow_add₀ hp0,
      show (2 : ℤ) * (a.valuation / 2) = a.valuation / 2 + a.valuation / 2 by ring,
      zpow_add₀ hp0, pow_two]
  have hpβ : (p : ℚ_[p]) ^ b.valuation
      = (p : ℚ_[p]) ^ (b.valuation % 2) * ((p : ℚ_[p]) ^ (b.valuation / 2)) ^ 2 := by
    have hdec : b.valuation = b.valuation % 2 + 2 * (b.valuation / 2) := by omega
    nth_rewrite 1 [hdec]
    rw [zpow_add₀ hp0,
      show (2 : ℤ) * (b.valuation / 2) = b.valuation / 2 + b.valuation / 2 by ring,
      zpow_add₀ hp0, pow_two]
  have hA : a = ((p : ℚ_[p]) ^ (a.valuation % 2)
          * ((padicUnit a ha : ℤ_[p]) : ℚ_[p]))
        * ((p : ℚ_[p]) ^ (a.valuation / 2)) ^ 2 := by
    calc a = (p : ℚ_[p]) ^ a.valuation * ((padicUnit a ha : ℤ_[p]) : ℚ_[p]) :=
          padicUnit_spec a ha
      _ = ((p : ℚ_[p]) ^ (a.valuation % 2) * ((padicUnit a ha : ℤ_[p]) : ℚ_[p]))
            * ((p : ℚ_[p]) ^ (a.valuation / 2)) ^ 2 := by rw [hpα]; ring
  have hB : b = ((p : ℚ_[p]) ^ (b.valuation % 2)
          * ((padicUnit b hb : ℤ_[p]) : ℚ_[p]))
        * ((p : ℚ_[p]) ^ (b.valuation / 2)) ^ 2 := by
    calc b = (p : ℚ_[p]) ^ b.valuation * ((padicUnit b hb : ℤ_[p]) : ℚ_[p]) :=
          padicUnit_spec b hb
      _ = ((p : ℚ_[p]) ^ (b.valuation % 2) * ((padicUnit b hb : ℤ_[p]) : ℚ_[p]))
            * ((p : ℚ_[p]) ^ (b.valuation / 2)) ^ 2 := by rw [hpβ]; ring
  conv_lhs => rw [hA, hB]
  exact hilbertSym_mul_square_eq (zpow_ne_zero _ hp0) (zpow_ne_zero _ hp0)

-- Theorem: Serre's formula for the Hilbert symbol at an odd prime `p`.
theorem hilbertSym_padic_odd_eq (hp : p ≠ 2) {a b : ℚ_[p]} (ha : a ≠ 0) (hb : b ≠ 0) :
    hilbertSym a b
      = parityPow ((quadraticChar (ZMod p)) (-1 : ZMod p)) (a.valuation * b.valuation)
        * parityPow ((quadraticChar (ZMod p))
            (PadicInt.toZMod (padicUnit a ha : ℤ_[p]))) b.valuation
        * parityPow ((quadraticChar (ZMod p))
            (PadicInt.toZMod (padicUnit b hb : ℤ_[p]))) a.valuation := by
  rw [hilbertSym_reduce a b ha hb]
  obtain hα0 | hα1 := Int.emod_two_eq_zero_or_one a.valuation
  · obtain hβ0 | hβ1 := Int.emod_two_eq_zero_or_one b.valuation
    · -- both valuations even: the two units case `00`
      have hαe : Even a.valuation := Int.even_iff.mpr hα0
      have hβe : Even b.valuation := Int.even_iff.mpr hβ0
      rw [hα0, hβ0]
      simp only [zpow_zero, one_mul]
      rw [parityPow_of_even (hαe.mul_right b.valuation), parityPow_of_even hβe,
        parityPow_of_even hαe]
      simp only [mul_one]
      exact hilbertSym_padic_odd_case00 hp (norm_padicUnit a ha) (norm_padicUnit b hb)
    · -- `α` even, `β` odd: case `10`
      have hαe : Even a.valuation := Int.even_iff.mpr hα0
      rw [hα0, hβ1]
      simp only [zpow_zero, zpow_one, one_mul]
      rw [hilbertSym_padic_odd_case10 hp (padicUnit a ha) (norm_p_mul_unit (padicUnit b hb)),
        parityPow_of_even (hαe.mul_right b.valuation),
        parityPow_of_odd (Int.not_even_iff.mpr hβ1), parityPow_of_even hαe]
      simp only [one_mul, mul_one]
  · obtain hβ0 | hβ1 := Int.emod_two_eq_zero_or_one b.valuation
    · -- `α` odd, `β` even: case `10` after symmetry
      have hβe : Even b.valuation := Int.even_iff.mpr hβ0
      rw [hα1, hβ0]
      simp only [zpow_one, zpow_zero, one_mul]
      rw [hilbertSym_comm,
        hilbertSym_padic_odd_case10 hp (padicUnit b hb) (norm_p_mul_unit (padicUnit a ha)),
        parityPow_of_even (hβe.mul_left a.valuation), parityPow_of_even hβe,
        parityPow_of_odd (Int.not_even_iff.mpr hα1)]
      simp only [one_mul, mul_one]
    · -- both valuations odd: case `11` with unit parts
      have hαo : ¬ Even a.valuation := Int.not_even_iff.mpr hα1
      have hβo : ¬ Even b.valuation := Int.not_even_iff.mpr hβ1
      rw [hα1, hβ1]
      simp only [zpow_one]
      rw [hilbertSym_padic_odd_case11_units hp (padicUnit a ha) (padicUnit b hb),
        parityPow_of_odd (fun h => (Int.even_mul.mp h).elim hαo hβo),
        parityPow_of_odd hβo, parityPow_of_odd hαo]
      rw [show -(PadicInt.toZMod (padicUnit a ha : ℤ_[p])
            * PadicInt.toZMod (padicUnit b hb : ℤ_[p]))
          = (-1 : ZMod p) * (PadicInt.toZMod (padicUnit a ha : ℤ_[p])
              * PadicInt.toZMod (padicUnit b hb : ℤ_[p])) by ring,
        map_mul, map_mul]
      ring

-- Theorem: the Hilbert symbol on `ℚ_[p]` is additive in the first argument for odd `p`.
theorem hilbertSym_padic_odd_mul_left (hp : p ≠ 2) (a a' b : ℚ_[p]) :
    hilbertSym (a * a') b = hilbertSym a b * hilbertSym a' b := by
  rcases eq_or_ne a 0 with rfl | ha
  · simp [hilbertSym_zero_left]
  rcases eq_or_ne a' 0 with rfl | ha'
  · simp [hilbertSym_zero_left]
  rcases eq_or_ne b 0 with rfl | hb
  · simp [hilbertSym_zero_right]
  rw [hilbertSym_padic_odd_eq hp (mul_ne_zero ha ha') hb,
    hilbertSym_padic_odd_eq hp ha hb, hilbertSym_padic_odd_eq hp ha' hb]
  rw [Padic.valuation_mul ha ha', padicUnit_mul a a' ha ha']
  simp only [map_mul]
  rw [parityPow_mul,
    show (a.valuation + a'.valuation) * b.valuation
        = a.valuation * b.valuation + a'.valuation * b.valuation by ring,
    parityPow_add _ (chi_neg_one_sq (p := p)) _ _,
    parityPow_add _ (chi_unit_sq (padicUnit b hb)) _ _]
  ring

end General

end HasseMinkowski
