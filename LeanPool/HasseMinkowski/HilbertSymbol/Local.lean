/-
Copyright (c) 2026 jayyswan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: jayyswan
-/
import LeanPool.HasseMinkowski.Basic
import LeanPool.HasseMinkowski.Prod
import LeanPool.HasseMinkowski.RankCriteria
import LeanPool.HasseMinkowski.HilbertSymbol.Padic
import LeanPool.HasseMinkowski.HilbertSymbol.Real
import LeanPool.HasseMinkowski.HilbertSymbol.Two

/-!
# Local Hilbert symbols at the completions of `ℚ`

This file collects the place-by-place facts about the Hilbert symbol `(·,·)_k` for
`k = ℚ_[p]` (and, later, `ℝ`).  The first item is the bilinearity of the symbol in its
first argument, `HasBilinHilbertSym ℚ_[p]`, which makes the generic rank criteria of
`RankCriteria.lean` available at every `p`-adic place.

The two-adic case is imported from `HilbertSymbol/Two.lean`; for odd `p` the result is
`hilbertSym_padic_odd_mul_left`.
-/

open Module QuadraticMap

namespace HasseMinkowski

/-! ### Bilinearity of the `p`-adic Hilbert symbol -/

/-- The Hilbert symbol on the `p`-adic numbers is bilinear in its first argument.

For `p = 2` this is `instHasBilinHilbertSym` from `HilbertSymbol/Two.lean`; for odd `p` it
is `hilbertSym_padic_odd_mul_left`. -/
instance instHasBilinHilbertSymPadic (p : ℕ) [Fact p.Prime] : HasBilinHilbertSym ℚ_[p] := by
  by_cases hp : p = 2
  · subst hp
    infer_instance
  · exact ⟨fun {a a' b} => hilbertSym_padic_odd_mul_left hp a a' b⟩

/-! ### The rank-two representation criterion -/

section TwoRepresents

variable {k : Type*} [Field k]

/-- A nonzero vector of the plane `⟨a, b⟩` represents `x` exactly when the ternary form
`⟨a, b, -x⟩` is isotropic.

This is the bridge between representability by a rank-two form and the ternary isotropy
criterion of `RankCriteria.lean`.  The hard case is when the isotropic vector of `⟨a, b, -x⟩`
has last coordinate `0`: then `⟨a, b⟩` is itself isotropic, and since it is nondegenerate it
represents every value. -/
private lemma weightedSumSquares_two_represents_iff_ternary {a b x : k} [Invertible (2 : k)]
    (ha : a ≠ 0) (hb : b ≠ 0) (hx : x ≠ 0) :
    (weightedSumSquares k ![a, b]).represents x ↔
      (weightedSumSquares k ![a, b, -x]).Isotropic := by
  have key2 : ∀ y : Fin 2 → k,
      (weightedSumSquares k ![a, b]) y = a * y 0 ^ 2 + b * y 1 ^ 2 := by
    intro y
    simp [weightedSumSquares_apply, Fin.sum_univ_two, smul_eq_mul, pow_two]
  have key3 : ∀ y : Fin 3 → k,
      (weightedSumSquares k ![a, b, -x]) y =
        a * y 0 ^ 2 + b * y 1 ^ 2 + (-x) * y 2 ^ 2 := by
    intro y
    simp [weightedSumSquares_apply, Fin.sum_univ_three, smul_eq_mul, pow_two]
  constructor
  · rintro ⟨y, _hy, hyQ⟩
    refine ⟨![y 0, y 1, 1], ?_, ?_⟩
    · intro h0
      have h1 : (1 : k) = 0 := by simpa using congr_fun h0 2
      exact one_ne_zero h1
    · rw [key3]
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
        Matrix.cons_val_two, Matrix.tail_cons]
      rw [key2] at hyQ
      linear_combination hyQ
  · rintro ⟨y, hy, hyQ⟩
    rw [key3] at hyQ
    by_cases hy2 : y 2 = 0
    · have hyQ' : a * y 0 ^ 2 + b * y 1 ^ 2 = 0 := by
        have h := hyQ
        rw [hy2] at h
        simpa using h
      have hneq : (![y 0, y 1] : Fin 2 → k) ≠ 0 := by
        intro h0
        apply hy
        funext j
        fin_cases j
        · simpa using congr_fun h0 0
        · simpa using congr_fun h0 1
        · exact hy2
      have hiso : (weightedSumSquares k ![a, b]).Isotropic := by
        refine ⟨![y 0, y 1], hneq, ?_⟩
        rw [key2]
        simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
        exact hyQ'
      have hnd : (weightedSumSquares k ![a, b]).Nondegenerate := by
        let w : Fin 2 → kˣ := ![Units.mk0 a ha, Units.mk0 b hb]
        have hw : (fun i => (w i : k)) = ![a, b] := by
          funext i
          fin_cases i <;> simp [w]
        rw [← hw]
        exact nondegenerate_weightedSumSquares w
      exact represents_of_isotropic_nondegenerate hnd hiso x
    · set z : Fin 2 → k := ![y 0 / y 2, y 1 / y 2] with hz_def
      have hzval : (weightedSumSquares k ![a, b]) z = x := by
        rw [key2]
        simp only [hz_def, Matrix.cons_val_zero, Matrix.cons_val_one]
        have hdiv : a * (y 0 / y 2) ^ 2 + b * (y 1 / y 2) ^ 2 =
            (a * y 0 ^ 2 + b * y 1 ^ 2) / y 2 ^ 2 := by
          field_simp [hy2]
        rw [hdiv]
        have hthis : a * y 0 ^ 2 + b * y 1 ^ 2 = x * y 2 ^ 2 := by
          linear_combination hyQ
        rw [hthis, mul_div_assoc, div_self (pow_ne_zero 2 hy2), mul_one]
      exact ⟨z, fun h0 => by
        rw [h0, map_zero] at hzval
        exact hx hzval.symm, hzval⟩

-- Theorem: the rank-two criterion for a diagonal form with two named weights.
-- `⟨a, b⟩` represents `x ≠ 0` exactly when `(x, -ab) = (a, b)`.
theorem represents_weightedSumSquares_two_iff {a b x : k} [HasBilinHilbertSym k]
    [Invertible (2 : k)] (ha : a ≠ 0) (hb : b ≠ 0) (hx : x ≠ 0) :
    (weightedSumSquares k ![a, b]).represents x ↔
      hilbertSym x (-(a * b)) = hilbertSym a b := by
  rw [weightedSumSquares_two_represents_iff_ternary ha hb hx,
    weightedSumSquares_isotropic_iff_hilbertSym_eq_one a b (-x) ha hb (neg_ne_zero.mpr hx)]
  rw [show -(-x) * a = x * a by ring, show -(-x) * b = x * b by ring]
  rw [hilbertSym_mul_mul (a := a) (b := b) (c := x)]
  exact mul_eq_one_iff_eq_of_signs
    (hilbertSym_eq_one_or_neg_one_of_ne_zero hx (neg_ne_zero.mpr (mul_ne_zero ha hb)))
    (hilbertSym_eq_one_or_neg_one_of_ne_zero ha hb)

end TwoRepresents

/-! ### Nontriviality of `x ↦ (x, c)` for a nonsquare `c`

For a nonsquare `c ≠ 0` the character `x ↦ (x, c)_k` is nontrivial.  Over `ℝ` this is
immediate from `hilbertSym_real_eq`; over `ℚ_[p]` it is read off Serre's closed formulas,
using the decomposition `c = p ^ α · u`. -/

section Nontriviality

-- Theorem: over `ℝ`, a negative `c` has `(-1, c)_ℝ = -1`.
theorem exists_hilbertSym_eq_neg_one_real {c : ℝ} (hc : c < 0) :
    ∃ x : ℝ, x ≠ 0 ∧ hilbertSym x c = -1 := by
  refine ⟨-1, by norm_num, ?_⟩
  rw [hilbertSym_real_eq (by norm_num) (ne_of_lt hc)]
  have h : ¬ (0 < (-1 : ℝ) ∨ 0 < c) := by
    rintro (h | h) <;> linarith
  rw [ite_eq_right h]

end Nontriviality

section OddPrime

variable {p : ℕ} [Fact p.Prime]

-- Theorem: `p` is nonzero as an element of `ℚ_[p]`.
private lemma padic_p_ne_zero_local : (p : ℚ_[p]) ≠ 0 := by
  intro h
  have hnorm : ‖(p : ℚ_[p])‖ = 0 := by rw [h, norm_zero]
  rw [Padic.norm_p] at hnorm
  exact (inv_ne_zero (Nat.cast_ne_zero.mpr (Nat.Prime.ne_zero Fact.out))) hnorm

-- Theorem: the underlying `p`-adic number of `padicUnit a ha` is `a * p ^ (-(a.valuation))`.
private lemma coe_padicUnit_local (a : ℚ_[p]) (ha : a ≠ 0) :
    ((padicUnit a ha : ℤ_[p]) : ℚ_[p]) = a * (p : ℚ_[p]) ^ (-(a.valuation)) := by
  rw [padicUnit]
  exact congrArg (fun t : ℤ_[p] => (t : ℚ_[p])) (IsUnit.unit_spec _)

-- Theorem: every nonzero `p`-adic number is `p ^ a.valuation` times its unit part.
private lemma padicUnit_spec_local (a : ℚ_[p]) (ha : a ≠ 0) :
    a = (p : ℚ_[p]) ^ a.valuation * ((padicUnit a ha : ℤ_[p]) : ℚ_[p]) := by
  have hp0 := padic_p_ne_zero_local (p := p)
  rw [coe_padicUnit_local]
  calc a = a * 1 := (mul_one a).symm
    _ = a * ((p : ℚ_[p]) ^ a.valuation * (p : ℚ_[p]) ^ (-(a.valuation))) := by
          rw [← zpow_add₀ hp0, add_neg_cancel, zpow_zero]
    _ = (p : ℚ_[p]) ^ a.valuation * (a * (p : ℚ_[p]) ^ (-(a.valuation))) := by ring

-- Theorem: a nonzero element of valuation `0` is its own unit part.
private lemma coe_padicUnit_of_valuation_zero (a : ℚ_[p]) (ha : a ≠ 0) (h0 : a.valuation = 0) :
    ((padicUnit a ha : ℤ_[p]) : ℚ_[p]) = a := by
  rw [coe_padicUnit_local, h0, neg_zero, zpow_zero, mul_one]

-- Theorem: the unit part of a natural number of valuation `0` is that natural number.
private lemma padicUnit_eq_natCast_of_valuation_zero {a : ℚ_[p]} (ha : a ≠ 0)
    (h0 : a.valuation = 0) {n : ℕ} (hn : a = (n : ℚ_[p])) :
    (padicUnit a ha : ℤ_[p]) = (n : ℤ_[p]) := by
  apply PadicInt.ext
  rw [coe_padicUnit_of_valuation_zero a ha h0]
  simpa using hn

-- Theorem: a unit (valuation `0`) with quadratic character `-1` pairs to `-1` against an
-- element of odd valuation.
private lemma hilbertSym_padic_odd_unit_of_neg_valuation (hp : p ≠ 2) {x c : ℚ_[p]}
    (hx : x ≠ 0) (hc : c ≠ 0) (hx0 : x.valuation = 0) (hβ : ¬ Even c.valuation)
    (hchi : (quadraticChar (ZMod p))
      (PadicInt.toZMod (padicUnit x hx : ℤ_[p])) = -1) :
    hilbertSym x c = -1 := by
  rw [hilbertSym_padic_odd_eq hp hx hc, hx0]
  simp only [zero_mul]
  rw [show parityPow ((quadraticChar (ZMod p)) (-1 : ZMod p)) 0 = 1 by
        rw [parityPow, ite_eq_left ⟨0, by ring⟩],
      show parityPow ((quadraticChar (ZMod p))
          (PadicInt.toZMod (padicUnit x hx : ℤ_[p]))) c.valuation
          = (quadraticChar (ZMod p)) (PadicInt.toZMod (padicUnit x hx : ℤ_[p])) by
        rw [parityPow, ite_eq_right hβ],
      show parityPow ((quadraticChar (ZMod p))
          (PadicInt.toZMod (padicUnit c hc : ℤ_[p]))) 0 = 1 by
        rw [parityPow, ite_eq_left ⟨0, by ring⟩],
      hchi]
  norm_num

-- Theorem: for even valuation, `(p, c)_p = -1` when the unit part of `c` is a quadratic
-- non-residue.
private lemma hilbertSym_padic_odd_p_of_nonresidue (hp : p ≠ 2) {c : ℚ_[p]} (hc : c ≠ 0)
    (hβ : Even c.valuation)
    (hchi : (quadraticChar (ZMod p))
      (PadicInt.toZMod (padicUnit c hc : ℤ_[p])) = -1) :
    hilbertSym (p : ℚ_[p]) c = -1 := by
  have hx := padic_p_ne_zero_local (p := p)
  have hup : PadicInt.toZMod (padicUnit (p : ℚ_[p]) hx : ℤ_[p]) = 1 := by
    have hcoe : ((padicUnit (p : ℚ_[p]) hx : ℤ_[p]) : ℚ_[p]) = 1 := by
      rw [coe_padicUnit_local, Padic.valuation_p]
      rw [show (-(1 : ℤ)) = -1 by norm_num, zpow_neg_one]
      exact mul_inv_cancel₀ hx
    have hone : (padicUnit (p : ℚ_[p]) hx : ℤ_[p]) = 1 := by
      apply PadicInt.ext
      rw [hcoe]
      simp
    rw [hone, map_one]
  rw [hilbertSym_padic_odd_eq hp hx hc, Padic.valuation_p]
  simp only [one_mul]
  rw [hup,
    show parityPow ((quadraticChar (ZMod p)) (-1 : ZMod p)) c.valuation = 1 by
      rw [parityPow, ite_eq_left hβ],
    show parityPow ((quadraticChar (ZMod p)) (1 : ZMod p)) c.valuation = 1 by
      rw [map_one, parityPow, ite_eq_left hβ],
    show parityPow ((quadraticChar (ZMod p))
        (PadicInt.toZMod (padicUnit c hc : ℤ_[p]))) 1
        = (quadraticChar (ZMod p)) (PadicInt.toZMod (padicUnit c hc : ℤ_[p])) by
      rw [parityPow, ite_eq_right (show ¬ Even (1 : ℤ) by norm_num)],
    hchi]
  norm_num

-- Theorem: for odd `p` and nonsquare `c ≠ 0`, some `x` has `(x, c)_p = -1`.
private theorem exists_hilbertSym_eq_neg_one_odd (hp : p ≠ 2) {c : ℚ_[p]}
    (hc : c ≠ 0) (hcsq : ¬ IsSquare c) :
    ∃ x : ℚ_[p], x ≠ 0 ∧ hilbertSym x c = -1 := by
  by_cases hβ : Even c.valuation
  · -- even valuation: use `x = p`, the unit part of `c` is a non-residue
    refine ⟨(p : ℚ_[p]), padic_p_ne_zero_local (p := p), ?_⟩
    refine hilbertSym_padic_odd_p_of_nonresidue hp hc hβ ?_
    rw [quadraticChar_neg_one_iff_not_isSquare]
    intro hmod
    have hnd : ¬ (p : ℤ_[p]) ∣ (padicUnit c hc : ℤ_[p]) := by
      rw [PadicInt.p_dvd_iff_toZMod_eq_zero]
      exact (IsUnit.map (PadicInt.toZMod (p := p)) (padicUnit c hc).isUnit).ne_zero
    obtain ⟨z, hz⟩ := PadicInt.isSquare_of_zmod hp hnd hmod
    obtain ⟨k, hk⟩ := hβ
    have hv : ((padicUnit c hc : ℤ_[p]) : ℚ_[p]) = (z : ℚ_[p]) ^ 2 := by
      rw [hz]; push_cast; ring
    have hpβ : (p : ℚ_[p]) ^ c.valuation = ((p : ℚ_[p]) ^ k) ^ 2 := by
      rw [hk, pow_two, ← zpow_add₀ (padic_p_ne_zero_local (p := p))]
    refine (hcsq ⟨(z : ℚ_[p]) * (p : ℚ_[p]) ^ k, ?_⟩)
    rw [padicUnit_spec_local c hc, hpβ, hv]
    ring
  · -- odd valuation: use a quadratic non-residue `x` of valuation `0`
    have hring : ringChar (ZMod p) ≠ 2 := by
      rw [ZMod.ringChar_zmod_n]
      exact hp
    obtain ⟨a, ha⟩ := quadraticChar_exists_neg_one' (F := ZMod p) hring
    let n : ℕ := (a : ZMod p).val
    have hnZ : (n : ZMod p) = (a : ZMod p) := ZMod.natCast_zmod_val _
    have hnd : ¬ p ∣ n := by
      intro hd
      have h0 : (n : ZMod p) = 0 := (ZMod.natCast_eq_zero_iff n p).mpr hd
      rw [hnZ] at h0
      exact a.ne_zero h0
    let x : ℚ_[p] := (n : ℚ_[p])
    have hx : x ≠ 0 := by
      intro h
      have hn0 : n = 0 := by simpa [x] using h
      exact hnd (by rw [hn0]; exact dvd_zero p)
    have hxval : x.valuation = 0 := by
      change (n : ℚ_[p]).valuation = 0
      rw [Padic.valuation_natCast, padicValNat.eq_zero_of_not_dvd hnd]
      norm_num
    refine ⟨x, hx, ?_⟩
    refine hilbertSym_padic_odd_unit_of_neg_valuation hp hx hc hxval hβ ?_
    have hunit : (padicUnit x hx : ℤ_[p]) = (n : ℤ_[p]) :=
      padicUnit_eq_natCast_of_valuation_zero (a := x) (n := n) hx hxval rfl
    rw [hunit, map_natCast, hnZ]
    exact ha

end OddPrime

section TwoAdic

-- Theorem: every nonzero `2`-adic number is `2 ^ a.valuation` times its unit part.
private lemma twoAdicUnit_spec_local (a : ℚ_[2]) (ha : a ≠ 0) :
    a = (2 : ℚ_[2]) ^ a.valuation * ((twoAdicUnit a ha : ℤ_[2]) : ℚ_[2]) := by
  simpa [twoAdicUnit] using padicUnit_spec_local (p := 2) a ha

-- Theorem: `(5, c)_2` is the parity of `c.valuation` (`5 ≡ 1 (mod 4)`, `5 ≢ ±1 (mod 8)`).
private lemma hilbertSym_two_five_eq {c : ℚ_[2]} (hc : c ≠ 0) :
    hilbertSym (5 : ℚ_[2]) c = parityPow (-1) c.valuation := by
  have hx : (5 : ℚ_[2]) ≠ 0 := by norm_num
  have hval : ((5 : ℚ_[2])).valuation = 0 := by
    rw [show (5 : ℚ_[2]) = ((5 : ℕ) : ℚ_[2]) by norm_num, Padic.valuation_natCast,
      padicValNat.eq_zero_of_not_dvd (by decide : ¬ 2 ∣ 5)]
    norm_num
  have hunit : (twoAdicUnit (5 : ℚ_[2]) hx : ℤ_[2]) = ((5 : ℕ) : ℤ_[2]) :=
    padicUnit_eq_natCast_of_valuation_zero hx hval rfl
  have heps : eps (twoAdicUnit (5 : ℚ_[2]) hx) = 0 := by
    have h : (twoAdicUnit (5 : ℚ_[2]) hx : ℤ_[2]).toZModPow 2 = 1 := by
      rw [hunit, map_natCast]
      decide
    rw [eps, ite_eq_left h]
  have homg : omg (twoAdicUnit (5 : ℚ_[2]) hx) = 1 := by
    have h : ¬ ((twoAdicUnit (5 : ℚ_[2]) hx : ℤ_[2]).toZModPow 3 = 1 ∨
        (twoAdicUnit (5 : ℚ_[2]) hx : ℤ_[2]).toZModPow 3 = 7) := by
      rw [hunit, map_natCast]
      decide
    rw [omg, ite_eq_right h]
  rw [hilbertSym_padic_two_eq hx hc, hval, heps, homg]
  simp only [zero_mul, mul_one, zero_add]

-- Theorem: `(7, c)_2` is the `ε` character of the unit part of `c` (`7 ≡ 3 (mod 4)`,
-- `7 ≡ -1 (mod 8)`).
private lemma hilbertSym_two_seven_eq {c : ℚ_[2]} (hc : c ≠ 0) :
    hilbertSym (7 : ℚ_[2]) c = parityPow (-1) (eps (twoAdicUnit c hc)) := by
  have hx : (7 : ℚ_[2]) ≠ 0 := by norm_num
  have hval : ((7 : ℚ_[2])).valuation = 0 := by
    rw [show (7 : ℚ_[2]) = ((7 : ℕ) : ℚ_[2]) by norm_num, Padic.valuation_natCast,
      padicValNat.eq_zero_of_not_dvd (by decide : ¬ 2 ∣ 7)]
    norm_num
  have hunit : (twoAdicUnit (7 : ℚ_[2]) hx : ℤ_[2]) = ((7 : ℕ) : ℤ_[2]) :=
    padicUnit_eq_natCast_of_valuation_zero hx hval rfl
  have heps : eps (twoAdicUnit (7 : ℚ_[2]) hx) = 1 := by
    have h : ¬ ((twoAdicUnit (7 : ℚ_[2]) hx : ℤ_[2]).toZModPow 2 = 1) := by
      rw [hunit, map_natCast]
      decide
    rw [eps, ite_eq_right h]
  have homg : omg (twoAdicUnit (7 : ℚ_[2]) hx) = 0 := by
    have h : (twoAdicUnit (7 : ℚ_[2]) hx : ℤ_[2]).toZModPow 3 = 7 := by
      rw [hunit, map_natCast]
      decide
    rw [omg, ite_eq_left (Or.inr h)]
  rw [hilbertSym_padic_two_eq hx hc, hval, heps, homg]
  simp only [one_mul, zero_mul, mul_zero, add_zero]

-- Theorem: `(2, c)_2` is the `ω` character of the unit part of `c`.
private lemma hilbertSym_two_two_eq {c : ℚ_[2]} (hc : c ≠ 0) :
    hilbertSym (2 : ℚ_[2]) c = parityPow (-1) (omg (twoAdicUnit c hc)) := by
  have hx : (2 : ℚ_[2]) ≠ 0 := by norm_num
  have hval : ((2 : ℚ_[2])).valuation = 1 := Padic.valuation_p (p := 2)
  have hunit : (twoAdicUnit (2 : ℚ_[2]) hx : ℤ_[2]) = 1 := by
    apply PadicInt.ext
    rw [twoAdicUnit, coe_padicUnit_local (p := 2), hval]
    rw [show (-(1 : ℤ)) = -1 by norm_num, zpow_neg_one]
    simp
  have heps : eps (twoAdicUnit (2 : ℚ_[2]) hx) = 0 := by
    have h : (twoAdicUnit (2 : ℚ_[2]) hx : ℤ_[2]).toZModPow 2 = 1 := by
      rw [hunit, map_one]
    rw [eps, ite_eq_left h]
  have homg : omg (twoAdicUnit (2 : ℚ_[2]) hx) = 0 := by
    have h : (twoAdicUnit (2 : ℚ_[2]) hx : ℤ_[2]).toZModPow 3 = 1 := by
      rw [hunit, map_one]
    rw [omg, ite_eq_left (Or.inl h)]
  rw [hilbertSym_padic_two_eq hx hc, hval, heps, homg]
  simp only [zero_mul, one_mul, mul_zero, zero_add, add_zero]

-- Theorem: for even valuation and nonsquare `c`, if the `ε` character of the unit part of
-- `c` vanishes then the `ω` character does not.
private lemma omg_eq_one_of_eps_eq_zero {c : ℚ_[2]} (hc : c ≠ 0)
    (hcsq : ¬ IsSquare c) (hβ : Even c.valuation)
    (hε0 : eps (twoAdicUnit c hc) = 0) : omg (twoAdicUnit c hc) = 1 := by
  have hpow2 : (twoAdicUnit c hc : ℤ_[2]).toZModPow 2 = 1 := by
    by_contra h
    rw [show eps (twoAdicUnit c hc) = 1 by rw [eps, ite_eq_right h]] at hε0
    exact one_ne_zero hε0
  have hnd : ¬ ((2 : ℕ) : ℤ_[2]) ∣ (twoAdicUnit c hc : ℤ_[2]) := by
    rw [PadicInt.p_dvd_iff_toZMod_eq_zero]
    exact (IsUnit.map (PadicInt.toZMod (p := 2)) (twoAdicUnit c hc).isUnit).ne_zero
  have hnot : ¬ ((twoAdicUnit c hc : ℤ_[2]).toZModPow 3 = 1 ∨
      (twoAdicUnit c hc : ℤ_[2]).toZModPow 3 = 7) := by
    rintro (h3 | h3)
    · obtain ⟨z, hz⟩ := PadicInt.isSquare_of_zmodPow hnd ⟨1, by rw [h3]; ring⟩
      apply hcsq
      obtain ⟨k, hk⟩ := hβ
      have h2 : (2 : ℚ_[2]) ≠ 0 := by norm_num
      have hpβ : (2 : ℚ_[2]) ^ c.valuation = ((2 : ℚ_[2]) ^ k) ^ 2 := by
        rw [hk, pow_two, ← zpow_add₀ h2]
      have huval : ((twoAdicUnit c hc : ℤ_[2]) : ℚ_[2]) = (z : ℚ_[2]) ^ 2 := by
        rw [hz]; push_cast; ring
      refine ⟨(2 : ℚ_[2]) ^ k * (z : ℚ_[2]), ?_⟩
      rw [twoAdicUnit_spec_local c hc, hpβ, huval]
      ring
    · have hcast : (twoAdicUnit c hc : ℤ_[2]).toZModPow 2
          = ZMod.cast ((twoAdicUnit c hc : ℤ_[2]).toZModPow 3) :=
        (PadicInt.cast_toZModPow 2 3 (by norm_num) (twoAdicUnit c hc : ℤ_[2])).symm
      rw [h3, hpow2] at hcast
      exact absurd hcast (by decide)
  rw [omg, ite_eq_right hnot]

-- Theorem: for `p = 2` and nonsquare `c ≠ 0`, some `x` has `(x, c)_2 = -1`.
private theorem exists_hilbertSym_eq_neg_one_two {c : ℚ_[2]} (hc : c ≠ 0)
    (hcsq : ¬ IsSquare c) : ∃ x : ℚ_[2], x ≠ 0 ∧ hilbertSym x c = -1 := by
  by_cases hβ : Even c.valuation
  · by_cases hε : eps (twoAdicUnit c hc) = 1
    · refine ⟨7, by norm_num, ?_⟩
      rw [hilbertSym_two_seven_eq hc, hε]
      rw [show parityPow (-1) 1 = -1 by rw [parityPow, ite_eq_right (by norm_num)]]
    · have hε0 : eps (twoAdicUnit c hc) = 0 := by
        by_cases h : (twoAdicUnit c hc : ℤ_[2]).toZModPow 2 = 1
        · rw [eps, ite_eq_left h]
        · exact absurd (by rw [eps, ite_eq_right h]) hε
      have hω : omg (twoAdicUnit c hc) = 1 := omg_eq_one_of_eps_eq_zero hc hcsq hβ hε0
      refine ⟨2, by norm_num, ?_⟩
      rw [hilbertSym_two_two_eq hc, hω]
      rw [show parityPow (-1) 1 = -1 by rw [parityPow, ite_eq_right (by norm_num)]]
  · refine ⟨5, by norm_num, ?_⟩
    rw [hilbertSym_two_five_eq hc]
    rw [show parityPow (-1) c.valuation = -1 by rw [parityPow, ite_eq_right hβ]]

end TwoAdic

/-! ### Nontriviality of the local Hilbert symbol character -/

-- Theorem: for a nonsquare nonzero `c` over `ℚ_[p]`, the character `x ↦ (x, c)_p` is
-- nontrivial: some `x` has `(x, c)_p = -1`.
theorem exists_hilbertSym_eq_neg_one_padic (p : ℕ) [Fact p.Prime] {c : ℚ_[p]}
    (hc : c ≠ 0) (hcsq : ¬ IsSquare c) :
    ∃ x : ℚ_[p], x ≠ 0 ∧ hilbertSym x c = -1 := by
  by_cases hp : p = 2
  · subst hp
    exact exists_hilbertSym_eq_neg_one_two hc hcsq
  · exact exists_hilbertSym_eq_neg_one_odd hp hc hcsq

/-! ### Two prescribed Hilbert symbols (WP2.4) and the pair of non-squares (WP2.5) -/

section Prescribed

-- Theorem: a square in `ℚ_[p]` has even valuation.
private lemma even_valuation_of_isSquare {p : ℕ} [Fact p.Prime] {x : ℚ_[p]}
    (h : IsSquare x) : Even x.valuation := by
  obtain ⟨y, hy⟩ := h
  rw [hy, ← pow_two, Padic.valuation_pow]
  exact ⟨y.valuation, by ring⟩

-- Theorem: an element of odd valuation is not a square.
private lemma not_isSquare_of_odd_valuation {p : ℕ} [Fact p.Prime] {x : ℚ_[p]}
    (h : ¬ Even x.valuation) : ¬ IsSquare x :=
  fun hs => h (even_valuation_of_isSquare hs)

-- Theorem: over `ℚ_[p]` there is a unit (element of valuation `0`) that is not a square.
private lemma exists_nonsquare_unit (p : ℕ) [Fact p.Prime] :
    ∃ u : ℚ_[p], u ≠ 0 ∧ u.valuation = 0 ∧ ¬ IsSquare u := by
  by_cases hp : p = 2
  · subst hp
    refine ⟨(7 : ℚ_[2]), by norm_num, ?_, ?_⟩
    · rw [show (7 : ℚ_[2]) = ((7 : ℕ) : ℚ_[2]) by norm_num, Padic.valuation_natCast,
        padicValNat.eq_zero_of_not_dvd (by decide : ¬ 2 ∣ 7)]
      norm_num
    · intro hs
      have h7 : (7 : ℚ_[2]) ≠ 0 := by norm_num
      have h1 : hilbertSym (7 : ℚ_[2]) (7 : ℚ_[2]) = 1 := by
        obtain ⟨y, hy⟩ := hs
        have hy_ne : y ≠ 0 := by
          rintro rfl
          rw [mul_zero] at hy
          exact h7 hy
        nth_rewrite 1 [hy]
        rw [← pow_two]
        exact hilbertSym_sq_left hy_ne h7
      have h2 : hilbertSym (7 : ℚ_[2]) (7 : ℚ_[2]) = -1 := by
        have hval7 : ((7 : ℚ_[2])).valuation = 0 := by
          rw [show (7 : ℚ_[2]) = ((7 : ℕ) : ℚ_[2]) by norm_num, Padic.valuation_natCast,
            padicValNat.eq_zero_of_not_dvd (by decide : ¬ 2 ∣ 7)]
          norm_num
        have hunit : (twoAdicUnit (7 : ℚ_[2]) h7 : ℤ_[2]) = ((7 : ℕ) : ℤ_[2]) :=
          padicUnit_eq_natCast_of_valuation_zero h7 hval7 rfl
        have heps : eps (twoAdicUnit (7 : ℚ_[2]) h7) = 1 := by
          have h : ¬ ((twoAdicUnit (7 : ℚ_[2]) h7 : ℤ_[2]).toZModPow 2 = 1) := by
            rw [hunit, map_natCast]
            decide
          rw [eps, ite_eq_right h]
        rw [hilbertSym_two_seven_eq h7, heps]
        rw [show parityPow (-1) 1 = -1 by rw [parityPow, ite_eq_right (by norm_num)]]
      linarith
  · -- odd `p`: lift a quadratic non-residue modulo `p`
    have hring : ringChar (ZMod p) ≠ 2 := by rw [ZMod.ringChar_zmod_n]; exact hp
    obtain ⟨a, ha⟩ := quadraticChar_exists_neg_one' (F := ZMod p) hring
    let n : ℕ := (a : ZMod p).val
    have hnZ : (n : ZMod p) = (a : ZMod p) := ZMod.natCast_zmod_val _
    have hnd : ¬ p ∣ n := by
      intro hd
      have h0 : (n : ZMod p) = 0 := (ZMod.natCast_eq_zero_iff n p).mpr hd
      rw [hnZ] at h0
      exact a.ne_zero h0
    have hn0 : n ≠ 0 := fun h => hnd (by rw [h]; exact dvd_zero p)
    have huval : ((n : ℚ_[p])).valuation = 0 := by
      rw [Padic.valuation_natCast, padicValNat.eq_zero_of_not_dvd hnd]
      norm_num
    refine ⟨(n : ℚ_[p]), Nat.cast_ne_zero.mpr hn0, huval, ?_⟩
    intro hs
    obtain ⟨y, hy⟩ := hs
    have hy_ne : y ≠ 0 := by
      rintro rfl
      rw [mul_zero] at hy
      exact (Nat.cast_ne_zero.mpr hn0) hy
    have hyval : y.valuation = 0 := by
      have h : (y * y).valuation = 0 := by rw [← hy]; exact huval
      rw [← pow_two, Padic.valuation_pow] at h
      omega
    have hynorm : ‖y‖ = 1 := by
      rw [Padic.norm_eq_zpow_neg_valuation hy_ne, hyval, neg_zero, zpow_zero]
    let Y : ℤ_[p] := ⟨y, le_of_eq hynorm⟩
    have hYcoe : ((Y : ℤ_[p]) : ℚ_[p]) = y := rfl
    have hYsq : Y * Y = (n : ℤ_[p]) := by
      apply PadicInt.ext
      rw [PadicInt.coe_mul, hYcoe, ← hy]
      simp
    have hnsqZ : IsSquare ((n : ZMod p)) := by
      refine ⟨PadicInt.toZMod (p := p) Y, ?_⟩
      have h := congrArg (PadicInt.toZMod (p := p)) hYsq
      simp only [map_mul, map_natCast] at h
      rw [h]
    have hchi1 : (quadraticChar (ZMod p)) ((n : ZMod p)) = 1 :=
      (quadraticChar_one_iff_isSquare (by rw [hnZ]; exact a.ne_zero)).mpr hnsqZ
    rw [hnZ] at hchi1
    linarith [ha, hchi1]

-- Theorem: for a nonsquare `c` over `ℚ_[p]` there is a nonsquare `c₂` with `c * c₂` also
-- nonsquare.
theorem exists_not_isSquare_and_not_isSquare_mul (p : ℕ) [Fact p.Prime] {c : ℚ_[p]}
    (hc : c ≠ 0) (hcsq : ¬ IsSquare c) :
    ∃ c₂ : ℚ_[p], ¬ IsSquare c₂ ∧ ¬ IsSquare (c * c₂) := by
  have _ := hcsq
  by_cases hβ : Even c.valuation
  · refine ⟨(p : ℚ_[p]), ?_, ?_⟩
    · exact not_isSquare_of_odd_valuation (by rw [Padic.valuation_p]; norm_num)
    · apply not_isSquare_of_odd_valuation
      rw [Padic.valuation_mul hc (padic_p_ne_zero_local (p := p)), Padic.valuation_p]
      intro h
      obtain ⟨k, hk⟩ := hβ
      obtain ⟨m, hm⟩ := h
      omega
  · obtain ⟨u, hu_ne, huval, hu⟩ := exists_nonsquare_unit p
    refine ⟨u, hu, ?_⟩
    apply not_isSquare_of_odd_valuation
    rw [Padic.valuation_mul hc hu_ne, huval, add_zero]
    exact hβ

-- Theorem: two prescribed values `e₁, e₂ ∈ {±1}` of the Hilbert symbol against `c₁`,
-- `c₂` can be realised by a single nonzero `x`, when `c₁`, `c₂`, `c₁ c₂` are all nonsquares.
theorem exists_hilbertSym_two_prescribed {k : Type*} [Field k] [HasBilinHilbertSym k]
    {c₁ c₂ : k} (h1 : c₁ ≠ 0) (h2 : c₂ ≠ 0)
    (hc1 : ¬ IsSquare c₁) (hc2 : ¬ IsSquare c₂) (hc12 : ¬ IsSquare (c₁ * c₂))
    (hnd : ∀ c : k, c ≠ 0 → ¬ IsSquare c → ∃ x : k, x ≠ 0 ∧ hilbertSym x c = -1)
    {e₁ e₂ : ℤ} (he1 : e₁ = 1 ∨ e₁ = -1) (he2 : e₂ = 1 ∨ e₂ = -1) :
    ∃ x : k, x ≠ 0 ∧ hilbertSym x c₁ = e₁ ∧ hilbertSym x c₂ = e₂ := by
  obtain ⟨y, hy_ne, hy⟩ := hnd c₁ h1 hc1
  obtain ⟨w, hw_ne, hw⟩ := hnd c₂ h2 hc2
  obtain ⟨z, hz_ne, hz⟩ := hnd (c₁ * c₂) (mul_ne_zero h1 h2) hc12
  have hzprod : hilbertSym z c₁ * hilbertSym z c₂ = -1 := by
    rw [← HasBilinHilbertSym.mul_right_eq, hz]
  have hs_or : hilbertSym y c₂ = 1 ∨ hilbertSym y c₂ = -1 :=
    hilbertSym_eq_one_or_neg_one_of_ne_zero hy_ne h2
  have ht_or : hilbertSym w c₁ = 1 ∨ hilbertSym w c₁ = -1 :=
    hilbertSym_eq_one_or_neg_one_of_ne_zero hw_ne h1
  have ha_or : hilbertSym z c₁ = 1 ∨ hilbertSym z c₁ = -1 :=
    hilbertSym_eq_one_or_neg_one_of_ne_zero hz_ne h1
  rcases he1 with rfl | rfl <;> rcases he2 with rfl | rfl
  · refine ⟨w * w, mul_ne_zero hw_ne hw_ne, ?_, ?_⟩
    · rw [HasBilinHilbertSym.mul_left_eq]
      rcases ht_or with ht | ht <;> rw [ht] <;> norm_num
    · rw [HasBilinHilbertSym.mul_left_eq, hw]; norm_num
  · by_cases ht1 : hilbertSym w c₁ = 1
    · exact ⟨w, hw_ne, ht1, hw⟩
    · have ht' : hilbertSym w c₁ = -1 := by
        rcases ht_or with h | h
        · exact absurd h ht1
        · exact h
      by_cases hs1 : hilbertSym y c₂ = 1
      · refine ⟨y * w, mul_ne_zero hy_ne hw_ne, ?_, ?_⟩
        · rw [HasBilinHilbertSym.mul_left_eq, hy, ht']; norm_num
        · rw [HasBilinHilbertSym.mul_left_eq, hs1, hw]; norm_num
      · have hs' : hilbertSym y c₂ = -1 := by
          rcases hs_or with h | h
          · exact absurd h hs1
          · exact h
        rcases ha_or with ha | ha
        · have hzb : hilbertSym z c₂ = -1 := by
            have h := hzprod; rw [ha] at h; linarith
          exact ⟨z, hz_ne, ha, hzb⟩
        · have hzb : hilbertSym z c₂ = 1 := by
            have h := hzprod; rw [ha] at h; linarith
          refine ⟨y * z, mul_ne_zero hy_ne hz_ne, ?_, ?_⟩
          · rw [HasBilinHilbertSym.mul_left_eq, hy, ha]; norm_num
          · rw [HasBilinHilbertSym.mul_left_eq, hs', hzb]; norm_num
  · by_cases hs1 : hilbertSym y c₂ = 1
    · exact ⟨y, hy_ne, hy, hs1⟩
    · have hs' : hilbertSym y c₂ = -1 := by
        rcases hs_or with h | h
        · exact absurd h hs1
        · exact h
      by_cases ht1 : hilbertSym w c₁ = 1
      · refine ⟨y * w, mul_ne_zero hy_ne hw_ne, ?_, ?_⟩
        · rw [HasBilinHilbertSym.mul_left_eq, hy, ht1]; norm_num
        · rw [HasBilinHilbertSym.mul_left_eq, hs', hw]; norm_num
      · have ht' : hilbertSym w c₁ = -1 := by
          rcases ht_or with h | h
          · exact absurd h ht1
          · exact h
        rcases ha_or with ha | ha
        · have hzb : hilbertSym z c₂ = -1 := by
            have h := hzprod; rw [ha] at h; linarith
          refine ⟨y * z, mul_ne_zero hy_ne hz_ne, ?_, ?_⟩
          · rw [HasBilinHilbertSym.mul_left_eq, hy, ha]; norm_num
          · rw [HasBilinHilbertSym.mul_left_eq, hs', hzb]; norm_num
        · have hzb : hilbertSym z c₂ = 1 := by
            have h := hzprod; rw [ha] at h; linarith
          exact ⟨z, hz_ne, ha, hzb⟩
  · by_cases hs1 : hilbertSym y c₂ = -1
    · exact ⟨y, hy_ne, hy, hs1⟩
    · have hs' : hilbertSym y c₂ = 1 := by
        rcases hs_or with h | h
        · exact h
        · exact absurd h hs1
      by_cases ht1 : hilbertSym w c₁ = -1
      · exact ⟨w, hw_ne, ht1, hw⟩
      · have ht' : hilbertSym w c₁ = 1 := by
          rcases ht_or with h | h
          · exact h
          · exact absurd h ht1
        refine ⟨y * w, mul_ne_zero hy_ne hw_ne, ?_, ?_⟩
        · rw [HasBilinHilbertSym.mul_left_eq, hy, ht']; norm_num
        · rw [HasBilinHilbertSym.mul_left_eq, hs', hw]; norm_num

end Prescribed

/-! ### Rank-3 representation and the five-variable isotropy theorem (WP2.6) -/

section FiveIsotropic

-- Theorem: the value of the binary weighted sum of squares.
private lemma wss2_val {k : Type*} [Field k] (b₁ b₂ : k) (v : Fin 2 → k) :
    (weightedSumSquares k ![b₁, b₂]) v = b₁ * v 0 ^ 2 + b₂ * v 1 ^ 2 := by
  simp [weightedSumSquares_apply, Fin.sum_univ_two, smul_eq_mul, pow_two]

-- Theorem: the value of the ternary weighted sum of squares.
private lemma wss3_val {k : Type*} [Field k] (b₁ b₂ b₃ : k) (v : Fin 3 → k) :
    (weightedSumSquares k ![b₁, b₂, b₃]) v =
      b₁ * v 0 ^ 2 + b₂ * v 1 ^ 2 + b₃ * v 2 ^ 2 := by
  simp [weightedSumSquares_apply, Fin.sum_univ_three, smul_eq_mul, pow_two]

-- Theorem: a ternary weighted sum of squares with nonzero weights is nondegenerate.
private lemma nondegenerate_wss3 {k : Type*} [Field k] [Invertible (2 : k)]
    {b₁ b₂ b₃ : k} (h₁ : b₁ ≠ 0) (h₂ : b₂ ≠ 0) (h₃ : b₃ ≠ 0) :
    (weightedSumSquares k ![b₁, b₂, b₃]).Nondegenerate := by
  let u : Fin 3 → kˣ := ![Units.mk0 b₁ h₁, Units.mk0 b₂ h₂, Units.mk0 b₃ h₃]
  have hu : (fun i => (u i : k)) = ![b₁, b₂, b₃] := by
    funext i; fin_cases i <;> simp [u]
  rw [← hu]
  exact nondegenerate_weightedSumSquares u

-- Theorem (rank-3 representation, implication form of Serre III.2.3): if `-(b₁b₂b₃)x`
-- is not a square then `⟨b₁,b₂,b₃⟩` represents `x`.  (The converse is false: an isotropic
-- ternary form represents its nonsquares too; see HANDOFF-local.md.)
private lemma represents_three_of_not_isSquare {k : Type*} [Field k] [HasBilinHilbertSym k]
    [Invertible (2 : k)]
    (hnd : ∀ c : k, c ≠ 0 → ¬ IsSquare c → ∃ x : k, x ≠ 0 ∧ hilbertSym x c = -1)
    {b₁ b₂ b₃ x : k} (h₁ : b₁ ≠ 0) (h₂ : b₂ ≠ 0) (h₃ : b₃ ≠ 0) (hx : x ≠ 0)
    (hnsq : ¬ IsSquare (-(b₁ * b₂ * b₃) * x)) :
    (weightedSumSquares k ![b₁, b₂, b₃]).represents x := by
  have h12 : b₁ * b₂ ≠ 0 := mul_ne_zero h₁ h₂
  have h3x : b₃ * x ≠ 0 := mul_ne_zero h₃ hx
  have hc1ne : -(b₁ * b₂) ≠ 0 := neg_ne_zero.mpr h12
  have hc12 : ¬ IsSquare (-(b₁ * b₂) * (b₃ * x)) := by
    rwa [show -(b₁ * b₂) * (b₃ * x) = -(b₁ * b₂ * b₃) * x by ring]
  by_cases hc1 : IsSquare (-(b₁ * b₂))
  · obtain ⟨s, hs⟩ := hc1
    have hiso : (weightedSumSquares k ![b₁, b₂, b₃]).Isotropic := by
      refine ⟨![s / b₁, 1, 0], ?_, ?_⟩
      · intro h0
        have h := congr_fun h0 1
        simp at h
      · rw [wss3_val]
        simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
          Matrix.cons_val_two, Matrix.tail_cons]
        have h0val : b₁ * (s / b₁) ^ 2 + b₂ = 0 := by
          rw [show b₁ * (s / b₁) ^ 2 + b₂ = (s * s + b₁ * b₂) / b₁ by field_simp]
          rw [hs.symm]
          simp
        simpa using h0val
    exact represents_of_isotropic_nondegenerate (nondegenerate_wss3 h₁ h₂ h₃) hiso x
  by_cases hc2 : IsSquare (b₃ * x)
  · obtain ⟨s, hs⟩ := hc2
    have hs0 : s ≠ 0 := by
      rintro rfl
      rw [mul_zero] at hs
      exact h3x hs
    refine ⟨![0, 0, s / b₃], ?_, ?_⟩
    · intro h0
      have h := congr_fun h0 2
      simp only [Matrix.cons_val_two, Matrix.tail_cons, Pi.zero_apply] at h
      exact (div_ne_zero hs0 h₃) h
    · rw [wss3_val]
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
        Matrix.cons_val_two, Matrix.tail_cons]
      have hval : b₃ * (s / b₃) ^ 2 = x := by
        rw [show b₃ * (s / b₃) ^ 2 = (s * s) / b₃ by field_simp]
        rw [← hs]
        field_simp
      rw [hval]
      ring
  · obtain ⟨y, hy_ne, hy1, hy2⟩ :=
      exists_hilbertSym_two_prescribed hc1ne h3x hc1 hc2 hc12 hnd
        (e₁ := hilbertSym b₁ b₂) (e₂ := hilbertSym (-b₃) x)
        (hilbertSym_eq_one_or_neg_one_of_ne_zero h₁ h₂)
        (hilbertSym_eq_one_or_neg_one_of_ne_zero (neg_ne_zero.mpr h₃) hx)
    have hEy : (weightedSumSquares k ![b₁, b₂]).represents y :=
      (represents_weightedSumSquares_two_iff h₁ h₂ hy_ne).mpr hy1
    have hFy : (weightedSumSquares k ![-b₃, x]).represents y :=
      (represents_weightedSumSquares_two_iff (neg_ne_zero.mpr h₃) hx hy_ne).mpr (by
        rw [show -((-b₃) * x) = b₃ * x by ring]; exact hy2)
    obtain ⟨u, hu_ne, huval⟩ := hEy
    obtain ⟨v, hv_ne, hvval⟩ := hFy
    rw [wss2_val] at huval hvval
    by_cases hv1 : v 1 = 0
    · have hzero : (weightedSumSquares k ![b₁, b₂, b₃]) ![u 0, u 1, v 0] = 0 := by
        rw [wss3_val]
        simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
          Matrix.cons_val_two, Matrix.tail_cons]
        rw [hv1] at hvval
        simp at hvval
        linear_combination huval - hvval
      have hne : (![u 0, u 1, v 0] : Fin 3 → k) ≠ 0 := by
        intro h0
        apply hu_ne
        funext i; fin_cases i
        · simpa using congr_fun h0 0
        · simpa using congr_fun h0 1
      exact represents_of_isotropic_nondegenerate (nondegenerate_wss3 h₁ h₂ h₃)
        ⟨_, hne, hzero⟩ x
    · refine ⟨![u 0 / v 1, u 1 / v 1, v 0 / v 1], ?_, ?_⟩
      · intro h0
        have h1 : u 0 / v 1 = 0 := by simpa using congr_fun h0 0
        have h2 : u 1 / v 1 = 0 := by simpa using congr_fun h0 1
        apply hu_ne
        funext i; fin_cases i
        · exact (div_eq_zero_iff.mp h1).resolve_right hv1
        · exact (div_eq_zero_iff.mp h2).resolve_right hv1
      · rw [wss3_val]
        simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
          Matrix.cons_val_two, Matrix.tail_cons]
        have hkey : b₁ * (u 0 / v 1) ^ 2 + b₂ * (u 1 / v 1) ^ 2 + b₃ * (v 0 / v 1) ^ 2
            = (b₁ * u 0 ^ 2 + b₂ * u 1 ^ 2 + b₃ * v 0 ^ 2) / v 1 ^ 2 := by
          field_simp
        rw [hkey]
        have hxval : b₁ * u 0 ^ 2 + b₂ * u 1 ^ 2 + b₃ * v 0 ^ 2 = x * v 1 ^ 2 := by
          linear_combination huval - hvval
        rw [hxval, mul_div_assoc, div_self (pow_ne_zero 2 hv1), mul_one]

-- Theorem: the value of a five-term weighted sum of squares.
private lemma wss5_val {p : ℕ} [Fact p.Prime] (w : Fin 5 → ℚ_[p]) (v : Fin 5 → ℚ_[p]) :
    (weightedSumSquares ℚ_[p] w) v =
      w 0 * v 0 ^ 2 + w 1 * v 1 ^ 2 + w 2 * v 2 ^ 2 + w 3 * v 3 ^ 2 + w 4 * v 4 ^ 2 := by
  simp [weightedSumSquares_apply, Fin.sum_univ_five, smul_eq_mul, pow_two]

-- Theorem (Serre IV.2 Thm 6): over `ℚ_[p]` every five-variable diagonal form is isotropic.
theorem isotropic_weightedSumSquares_five (p : ℕ) [Fact p.Prime] (w : Fin 5 → ℚ_[p])
    (hw : ∀ i, w i ≠ 0) : (weightedSumSquares ℚ_[p] w).Isotropic := by
  have h0 : w 0 ≠ 0 := hw 0
  have h1 : w 1 ≠ 0 := hw 1
  have h2 : w 2 ≠ 0 := hw 2
  have h3 : w 3 ≠ 0 := hw 3
  have h4 : w 4 ≠ 0 := hw 4
  by_cases hc1 : IsSquare (-(w 0 * w 1))
  · obtain ⟨s, hs⟩ := hc1
    refine ⟨![s / w 0, 1, 0, 0, 0], ?_, ?_⟩
    · intro hv
      have h := congr_fun hv 1
      simp at h
    · have hz : (weightedSumSquares ℚ_[p] w) ![s / w 0, 1, 0, 0, 0]
          = w 0 * (s / w 0) ^ 2 + w 1 := by
        rw [wss5_val]
        simp
      rw [hz]
      have h0val : w 0 * (s / w 0) ^ 2 + w 1 = 0 := by
        rw [show w 0 * (s / w 0) ^ 2 + w 1 = (s * s + w 0 * w 1) / w 0 by field_simp]
        rw [hs.symm]
        simp
      exact h0val
  · have hc1ne : -(w 0 * w 1) ≠ 0 := neg_ne_zero.mpr (mul_ne_zero h0 h1)
    obtain ⟨c2, hc2, hc1c2⟩ := exists_not_isSquare_and_not_isSquare_mul p hc1ne hc1
    have hc2ne : c2 ≠ 0 := fun h => hc2 (h ▸ IsSquare.zero)
    have h234 : w 2 * w 3 * w 4 ≠ 0 := mul_ne_zero (mul_ne_zero h2 h3) h4
    have hsig : hilbertSym (w 2 * w 3 * w 4) c2 = 1 ∨
        hilbertSym (w 2 * w 3 * w 4) c2 = -1 :=
      hilbertSym_eq_one_or_neg_one_of_ne_zero h234 hc2ne
    have hsign : hilbertSym (w 2 * w 3 * w 4) c2 * hilbertSym (w 2 * w 3 * w 4) c2 = 1 := by
      rcases hsig with h | h <;> rw [h] <;> norm_num
    have he1 : hilbertSym (w 0) (w 1) = 1 ∨ hilbertSym (w 0) (w 1) = -1 :=
      hilbertSym_eq_one_or_neg_one_of_ne_zero h0 h1
    have he2 : (-hilbertSym (w 2 * w 3 * w 4) c2) = 1 ∨
        (-hilbertSym (w 2 * w 3 * w 4) c2) = -1 := by
      rcases hsig with h | h <;> rw [h] <;> norm_num
    obtain ⟨x, hx_ne, hx1, hx2⟩ :=
      exists_hilbertSym_two_prescribed hc1ne hc2ne hc1 hc2 hc1c2
        (fun c hc hcsq => exists_hilbertSym_eq_neg_one_padic p hc hcsq)
        (e₁ := hilbertSym (w 0) (w 1)) (e₂ := -hilbertSym (w 2 * w 3 * w 4) c2)
        he1 he2
    have hEx : (weightedSumSquares ℚ_[p] ![w 0, w 1]).represents x :=
      (represents_weightedSumSquares_two_iff h0 h1 hx_ne).mpr hx1
    have hnsq234 : ¬ IsSquare ((w 2 * w 3 * w 4) * x) := by
      intro hs
      obtain ⟨t, ht⟩ := hs
      have ht_ne : t ≠ 0 := by
        rintro rfl
        rw [mul_zero] at ht
        exact (mul_ne_zero h234 hx_ne) ht
      have hs1 : hilbertSym ((w 2 * w 3 * w 4) * x) c2 = 1 := by
        rw [ht, ← pow_two]
        exact hilbertSym_sq_left ht_ne hc2ne
      have hs2 : hilbertSym ((w 2 * w 3 * w 4) * x) c2 = -1 := by
        rw [HasBilinHilbertSym.mul_left_eq, hx2]
        linear_combination -1 * hsign
      linarith
    have hGx : (weightedSumSquares ℚ_[p] ![-(w 2), -(w 3), -(w 4)]).represents x :=
      represents_three_of_not_isSquare
        (fun c hc hcsq => exists_hilbertSym_eq_neg_one_padic p hc hcsq)
        (neg_ne_zero.mpr h2) (neg_ne_zero.mpr h3) (neg_ne_zero.mpr h4) hx_ne
        (by rwa [show -(-(w 2) * -(w 3) * -(w 4)) * x = (w 2 * w 3 * w 4) * x by ring])
    obtain ⟨u, hu_ne, huval⟩ := hEx
    obtain ⟨v, hv_ne, hvval⟩ := hGx
    rw [wss2_val] at huval
    rw [wss3_val] at hvval
    refine ⟨![u 0, u 1, v 0, v 1, v 2], ?_, ?_⟩
    · intro hv
      apply hu_ne
      funext i; fin_cases i
      · simpa using congr_fun hv 0
      · simpa using congr_fun hv 1
    · have hz : (weightedSumSquares ℚ_[p] w) ![u 0, u 1, v 0, v 1, v 2]
          = w 0 * u 0 ^ 2 + w 1 * u 1 ^ 2 + w 2 * v 0 ^ 2 + w 3 * v 1 ^ 2
            + w 4 * v 2 ^ 2 := by
        rw [wss5_val]
        simp
      rw [hz]
      linear_combination huval - hvval

-- Theorem (Serre IV.2 Thm 6, `n ≥ 5`): over `ℚ_[p]` every diagonal form in at least five
-- variables is isotropic.
theorem isotropic_weightedSumSquares_of_five_le {ι : Type*} [Fintype ι]
    (p : ℕ) [Fact p.Prime] {w : ι → ℚ_[p]} (hw : ∀ i, w i ≠ 0)
    (h : 5 ≤ Fintype.card ι) :
    (weightedSumSquares ℚ_[p] w).Isotropic := by
  classical
  let f : Fin 5 → ι := fun j => (Fintype.equivFin ι).symm (Fin.castLE h j)
  have hf : Function.Injective f := by
    intro a b hab
    have h2 : Fin.castLE h a = Fin.castLE h b := (Fintype.equivFin ι).symm.injective hab
    exact Fin.ext (by simpa using congrArg Fin.val h2)
  let w' : Fin 5 → ℚ_[p] := fun j => w (f j)
  have hw' : ∀ j, w' j ≠ 0 := fun j => hw (f j)
  obtain ⟨v, hv_ne, hv0⟩ := isotropic_weightedSumSquares_five p w' hw'
  let V : ι → ℚ_[p] := fun i => if hi : i ∈ Set.range f then v (Classical.choose hi) else 0
  have hVf : ∀ j, V (f j) = v j := by
    intro j
    dsimp only [V]
    rw [dite_eq_left ⟨j, rfl⟩]
    congr 1
    exact hf (Classical.choose_spec (⟨j, rfl⟩ : f j ∈ Set.range f))
  have hV0 : ∀ x, x ∉ Set.range f → V x = 0 := by
    intro x hx
    dsimp only [V]
    rw [dite_eq_right hx]
  have hL : (weightedSumSquares ℚ_[p] w) V = ∑ i : ι, w i * (V i * V i) := by
    simp only [weightedSumSquares_apply, smul_eq_mul]
  have hR : (weightedSumSquares ℚ_[p] w') v = ∑ j : Fin 5, w' j * (v j * v j) := by
    simp only [weightedSumSquares_apply, smul_eq_mul]
  have hsum : (∑ i : ι, w i * (V i * V i)) = ∑ j : Fin 5, w' j * (v j * v j) := by
    have hzero : ∀ x ∈ (Finset.univ : Finset ι), x ∉ Finset.univ.image f →
        w x * (V x * V x) = 0 := by
      intro x _ hx
      have hxr : x ∉ Set.range f := by
        intro hmem
        obtain ⟨a, ha⟩ := hmem
        exact hx (Finset.mem_image.mpr ⟨a, Finset.mem_univ a, ha⟩)
      rw [hV0 x hxr]; ring
    rw [← Finset.sum_subset (Finset.subset_univ (Finset.univ.image f)) hzero]
    rw [Finset.sum_image (fun a _ b _ hab => hf hab)]
    exact Finset.sum_congr rfl (fun j _ => by simp only [w', hVf j])
  refine ⟨V, ?_, ?_⟩
  · intro hVz
    have hvne' : ∃ j, v j ≠ 0 := by
      by_contra hcon
      simp only [not_exists, not_not] at hcon
      exact hv_ne (funext hcon)
    obtain ⟨j, hj⟩ := hvne'
    have : V (f j) = 0 := by rw [hVz]; rfl
    exact hj (by rw [← hVf j]; exact this)
  · rw [hL, hsum, ← hR]
    exact hv0

end FiveIsotropic

end HasseMinkowski
