/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import LeanPool.LeanQuantumAlg.Init
public import Mathlib.Analysis.SpecialFunctions.Complex.Log

/-!
# Complex exponential and unit-circle helper lemmas (quantum-free)

Generic identities used by the QSP development, factored out so they carry no
dependency on the quantum framework (gates, states): phase-factor scalars
`e^{±iφ}`, the special values `e^{±iπ/2}`, `e^{±iπ/4}`, the real-square-root
identity `√(1-x²)² = 1-x²`, injectivity of `t ↦ e^{it}` on `(0, π)`, and the
SU(2)/unit-circle parameterizations (`mul_conj_eq_norm_sq`, `exists_unit_mul`,
`exists_real_unit`, `exists_cos_sin`, `exists_exp_sq_eq`).

These are upstream candidates for Mathlib; nothing here mentions `Gate`/`PureState`.
-/

@[expose] public section

namespace QuantumAlg

open Complex

/-- `exp(iθ) = cos θ + i sin θ` for real `θ`, with real-valued `cos/sin`. -/
theorem exp_ofReal_mul_I (θ : ℝ) :
    Complex.exp (θ * Complex.I) =
      (Real.cos θ : ℂ) + (Real.sin θ : ℂ) * Complex.I := by
  rw [Complex.exp_mul_I, Complex.ofReal_cos, Complex.ofReal_sin]

theorem conj_exp_I (φ : ℝ) :
    starRingEnd ℂ (Complex.exp (φ * Complex.I)) =
      Complex.exp (-(φ * Complex.I)) := by
  rw [← Complex.exp_conj]
  congr 1
  simp

theorem conj_exp_neg_I (φ : ℝ) :
    starRingEnd ℂ (Complex.exp (-(φ * Complex.I))) =
      Complex.exp (φ * Complex.I) := by
  rw [← Complex.exp_conj]
  congr 1
  simp

theorem exp_I_mul_exp_neg_I (φ : ℝ) :
    Complex.exp (φ * Complex.I) * Complex.exp (-(φ * Complex.I)) = 1 := by
  rw [← Complex.exp_add, add_neg_cancel, Complex.exp_zero]

theorem exp_neg_I_mul_exp_I (φ : ℝ) :
    Complex.exp (-(φ * Complex.I)) * Complex.exp (φ * Complex.I) = 1 := by
  rw [← Complex.exp_add, neg_add_cancel, Complex.exp_zero]

theorem exp_pi_div_two_mul_I :
    Complex.exp ((Real.pi : ℂ) / 2 * Complex.I) = Complex.I := by
  rw [show ((Real.pi : ℂ) / 2) = ((Real.pi / 2 : ℝ) : ℂ) by push_cast; ring,
    exp_ofReal_mul_I, Real.cos_pi_div_two, Real.sin_pi_div_two]
  simp

theorem exp_neg_pi_div_two_mul_I :
    Complex.exp (-((Real.pi : ℂ) / 2 * Complex.I)) = -Complex.I := by
  rw [show -((Real.pi : ℂ) / 2 * Complex.I)
      = ((-(Real.pi / 2) : ℝ) : ℂ) * Complex.I by push_cast; ring,
    exp_ofReal_mul_I, Real.cos_neg, Real.sin_neg, Real.cos_pi_div_two,
    Real.sin_pi_div_two]
  simp

/-- `√(1-x²)` squares back to `1 - x²` over `ℂ` for `x ∈ [-1,1]`. -/
theorem sq_sqrt_one_sub_sq {x : ℝ} (hx : x ∈ Set.Icc (-1 : ℝ) 1) :
    ((Real.sqrt (1 - x ^ 2) : ℂ)) ^ 2 = 1 - (x : ℂ) ^ 2 := by
  rw [← Complex.ofReal_pow,
    Real.sq_sqrt (by nlinarith [hx.1, hx.2] : (0 : ℝ) ≤ 1 - x ^ 2)]
  push_cast
  ring

/-- A phase factor solving the degree-reduction equation `e^{2iφ} q = p`,
available whenever `|p| = |q| ≠ 0` [Lin22, hermfunc.tex:1226]. -/
theorem exists_exp_sq_eq {p q : ℂ} (hq : q ≠ 0)
    (hpq : p * starRingEnd ℂ p = q * starRingEnd ℂ q) :
    ∃ φ : ℝ, Complex.exp (φ * Complex.I) ^ 2 * q = p := by
  refine ⟨(p / q).arg / 2, ?_⟩
  have hnorm : ‖p / q‖ = 1 := by
    have h1 : ‖p‖ * ‖p‖ = ‖q‖ * ‖q‖ := by
      have := congrArg norm hpq
      simpa [norm_mul, Complex.norm_conj] using this
    have h2 : ‖p‖ = ‖q‖ := by
      nlinarith [norm_nonneg p, norm_nonneg q]
    rw [norm_div, h2, div_self (norm_ne_zero_iff.mpr hq)]
  have harg : Complex.exp ((p / q).arg * Complex.I) = p / q := by
    have h := Complex.norm_mul_exp_arg_mul_I (p / q)
    rw [hnorm] at h
    simpa using h
  have hsq : Complex.exp (((p / q).arg / 2 : ℝ) * Complex.I) ^ 2
      = Complex.exp ((p / q).arg * Complex.I) := by
    rw [← Complex.exp_nat_mul]
    congr 1
    push_cast
    ring
  rw [hsq, harg, div_mul_cancel₀ p hq]

theorem exp_pi_div_four_sq :
    Complex.exp ((Real.pi : ℂ) / 4 * Complex.I) *
      Complex.exp ((Real.pi : ℂ) / 4 * Complex.I) = Complex.I := by
  rw [← Complex.exp_add, show (Real.pi : ℂ) / 4 * Complex.I
      + (Real.pi : ℂ) / 4 * Complex.I = (Real.pi : ℂ) / 2 * Complex.I by ring,
    exp_pi_div_two_mul_I]

theorem exp_pi_div_four_mul_neg :
    Complex.exp ((Real.pi : ℂ) / 4 * Complex.I) *
      Complex.exp (-((Real.pi : ℂ) / 4 * Complex.I)) = 1 := by
  rw [← Complex.exp_add, add_neg_cancel, Complex.exp_zero]

/-- `e^{iπ/4} · i = -e^{-iπ/4}` (both equal `e^{3iπ/4}`). -/
theorem exp_pi_div_four_mul_I :
    Complex.exp ((Real.pi : ℂ) / 4 * Complex.I) * Complex.I
      = -Complex.exp (-((Real.pi : ℂ) / 4 * Complex.I)) := by
  apply mul_left_cancel₀ (Complex.exp_ne_zero ((Real.pi : ℂ) / 4 * Complex.I))
  rw [← mul_assoc, exp_pi_div_four_sq, Complex.I_mul_I, mul_neg,
    exp_pi_div_four_mul_neg]

/-- `e^{-iπ/4} · i = e^{iπ/4}`. -/
theorem exp_neg_pi_div_four_mul_I :
    Complex.exp (-((Real.pi : ℂ) / 4 * Complex.I)) * Complex.I
      = Complex.exp ((Real.pi : ℂ) / 4 * Complex.I) := by
  apply mul_left_cancel₀ (Complex.exp_ne_zero ((Real.pi : ℂ) / 4 * Complex.I))
  rw [← mul_assoc, exp_pi_div_four_mul_neg, one_mul, exp_pi_div_four_sq]

theorem ofReal_sin_sq_add_cos_sq (t : ℝ) :
    (Real.sin t : ℂ) * (Real.sin t : ℂ) + (Real.cos t : ℂ) * (Real.cos t : ℂ)
      = 1 := by
  norm_cast
  linear_combination Real.sin_sq_add_cos_sq t

/-- `t ↦ e^{it}` is injective on `(0, π)`. -/
theorem exp_I_injOn_Ioo :
    Set.InjOn (fun t : ℝ => Complex.exp ((t : ℂ) * Complex.I))
      (Set.Ioo 0 Real.pi) := by
  intro s hs t ht hst
  simp only [] at hst
  rw [Complex.exp_eq_exp_iff_exists_int] at hst
  obtain ⟨n, hn⟩ := hst
  have h2 : ((s : ℂ)) * Complex.I
      = ((t : ℂ) + (n : ℂ) * (2 * (Real.pi : ℂ))) * Complex.I := by
    rw [hn]; ring
  have hreal : s = t + (n : ℝ) * (2 * Real.pi) := by
    exact_mod_cast mul_right_cancel₀ Complex.I_ne_zero h2
  have hπ := Real.pi_pos
  have hn0 : n = 0 := by
    rcases lt_trichotomy n 0 with hneg | hz | hpos
    · exfalso
      have hle : (n : ℝ) ≤ -1 := by exact_mod_cast (by omega : n ≤ -1)
      have hmul : (n : ℝ) * (2 * Real.pi) ≤ (-1) * (2 * Real.pi) :=
        mul_le_mul_of_nonneg_right hle (by linarith)
      linarith [hs.1, ht.2]
    · exact hz
    · exfalso
      have hle : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast (by omega : 1 ≤ n)
      have hmul : (1 : ℝ) * (2 * Real.pi) ≤ (n : ℝ) * (2 * Real.pi) :=
        mul_le_mul_of_nonneg_right hle (by linarith)
      linarith [hs.2, ht.1]
  rw [hn0] at hreal
  push_cast at hreal
  linarith

/-- `z·z* = ‖z‖²` in `ℂ`. -/
theorem mul_conj_eq_norm_sq (z : ℂ) :
    z * starRingEnd ℂ z = ((‖z‖ : ℝ) : ℂ) ^ 2 := by
  conv_lhs => rw [← Complex.norm_mul_exp_arg_mul_I z]
  rw [map_mul, Complex.conj_ofReal, conj_exp_I]
  linear_combination ((‖z‖ : ℂ) * (‖z‖ : ℂ)) * exp_I_mul_exp_neg_I z.arg

/-- A unit-normalized multiple of a nonzero pair, with real product: the
phase `e^{-i·arg(pq)/2}` makes `|cp|² + |cq|² = 1` and `c²pq` real. -/
theorem exists_unit_mul {p q : ℂ} (hpq : ¬(p = 0 ∧ q = 0)) :
    ∃ c : ℂ,
      c * p * starRingEnd ℂ (c * p) + c * q * starRingEnd ℂ (c * q) = 1 ∧
      (c * p * (c * q)).im = 0 := by
  have hpos : 0 < ‖p‖ ^ 2 + ‖q‖ ^ 2 := by
    rcases not_and_or.mp hpq with hp | hq
    · have h1 : 0 < ‖p‖ := norm_pos_iff.mpr hp
      nlinarith [sq_nonneg ‖q‖]
    · have h1 : 0 < ‖q‖ := norm_pos_iff.mpr hq
      nlinarith [sq_nonneg ‖p‖]
  set r : ℝ := Real.sqrt (‖p‖ ^ 2 + ‖q‖ ^ 2) with hrdef
  have hrpos : 0 < r := Real.sqrt_pos.mpr hpos
  have hr2 : r ^ 2 = ‖p‖ ^ 2 + ‖q‖ ^ 2 := Real.sq_sqrt hpos.le
  set μ : ℝ := -(p * q).arg / 2 with hμdef
  set c : ℂ := ((r⁻¹ : ℝ) : ℂ) * Complex.exp ((μ : ℂ) * Complex.I)
    with hcdef
  clear_value c
  have hcc : c * starRingEnd ℂ c = ((r⁻¹ ^ 2 : ℝ) : ℂ) := by
    rw [hcdef, map_mul, Complex.conj_ofReal, conj_exp_I]
    push_cast
    linear_combination ((r : ℂ))⁻¹ * ((r : ℂ))⁻¹ * exp_I_mul_exp_neg_I μ
  refine ⟨c, ?_, ?_⟩
  · have hsum : p * starRingEnd ℂ p + q * starRingEnd ℂ q
        = ((r ^ 2 : ℝ) : ℂ) := by
      rw [mul_conj_eq_norm_sq, mul_conj_eq_norm_sq, hr2]
      push_cast
      ring
    calc c * p * starRingEnd ℂ (c * p) + c * q * starRingEnd ℂ (c * q)
        = (c * starRingEnd ℂ c)
            * (p * starRingEnd ℂ p + q * starRingEnd ℂ q) := by
          rw [map_mul, map_mul]; ring
      _ = ((r⁻¹ ^ 2 : ℝ) : ℂ) * ((r ^ 2 : ℝ) : ℂ) := by rw [hcc, hsum]
      _ = 1 := by
          norm_cast
          rw [inv_pow]
          exact inv_mul_cancel₀ (pow_ne_zero 2 hrpos.ne')
  · have hexp : Complex.exp ((μ : ℂ) * Complex.I)
        * Complex.exp ((μ : ℂ) * Complex.I)
        * Complex.exp (((p * q).arg : ℂ) * Complex.I) = 1 := by
      rw [← Complex.exp_add, ← Complex.exp_add]
      rw [show (μ : ℂ) * Complex.I + (μ : ℂ) * Complex.I
          + ((p * q).arg : ℂ) * Complex.I
          = ((μ + μ + (p * q).arg : ℝ) : ℂ) * Complex.I by push_cast; ring]
      rw [show (μ + μ + (p * q).arg : ℝ) = 0 by rw [hμdef]; ring]
      simp
    have hprod : c * p * (c * q) = ((r⁻¹ ^ 2 * ‖p * q‖ : ℝ) : ℂ) := by
      calc c * p * (c * q) = c * c * (p * q) := by ring
        _ = ((r⁻¹ : ℝ) : ℂ) * ((r⁻¹ : ℝ) : ℂ) * ((‖p * q‖ : ℝ) : ℂ)
            * (Complex.exp ((μ : ℂ) * Complex.I)
              * Complex.exp ((μ : ℂ) * Complex.I)
              * Complex.exp (((p * q).arg : ℂ) * Complex.I)) := by
            rw [hcdef]
            conv_lhs => rw [← Complex.norm_mul_exp_arg_mul_I (p * q)]
            ring
        _ = ((r⁻¹ ^ 2 * ‖p * q‖ : ℝ) : ℂ) := by
            rw [hexp, mul_one]
            push_cast
            ring
    rw [hprod]
    exact Complex.ofReal_im _

/-- A unit-normalized positive multiple of a nonzero real pair. -/
theorem exists_real_unit {p q : ℝ} (hpq : ¬(p = 0 ∧ q = 0)) :
    ∃ v w : ℝ, v ^ 2 + w ^ 2 = 1 ∧ ∃ c : ℝ, v = c * p ∧ w = c * q := by
  have hpos : 0 < p ^ 2 + q ^ 2 := by
    rcases not_and_or.mp hpq with hp | hq
    · rcases lt_or_gt_of_ne hp with h | h <;> nlinarith [sq_nonneg q]
    · rcases lt_or_gt_of_ne hq with h | h <;> nlinarith [sq_nonneg p]
  set r : ℝ := Real.sqrt (p ^ 2 + q ^ 2) with hrdef
  have hrpos : 0 < r := Real.sqrt_pos.mpr hpos
  have hr2 : r ^ 2 = p ^ 2 + q ^ 2 := Real.sq_sqrt hpos.le
  refine ⟨r⁻¹ * p, r⁻¹ * q, ?_, r⁻¹, rfl, rfl⟩
  have h1 : (r⁻¹ * p) ^ 2 + (r⁻¹ * q) ^ 2 = r⁻¹ ^ 2 * (p ^ 2 + q ^ 2) := by
    ring
  rw [h1, ← hr2, inv_pow]
  exact inv_mul_cancel₀ (pow_ne_zero 2 hrpos.ne')

/-- Any point of the real unit circle is `(cos(θ/2), sin(θ/2))` for some
angle `θ`. -/
theorem exists_cos_sin {v w : ℝ} (hvw : v ^ 2 + w ^ 2 = 1) :
    ∃ θ : ℝ, Real.cos (θ / 2) = v ∧ Real.sin (θ / 2) = w := by
  set ζ : ℂ := (v : ℂ) + (w : ℂ) * Complex.I with hζdef
  have hC : (v : ℂ) ^ 2 + (w : ℂ) ^ 2 = 1 := by exact_mod_cast hvw
  have hζconj : ζ * starRingEnd ℂ ζ = 1 := by
    rw [hζdef]
    simp only [map_add, map_mul, Complex.conj_ofReal, Complex.conj_I]
    linear_combination (-(w : ℂ) ^ 2) * Complex.I_sq + hC
  have hn1 : ‖ζ‖ = 1 := by
    have h1 := mul_conj_eq_norm_sq ζ
    rw [hζconj] at h1
    have h2 : ‖ζ‖ ^ 2 = 1 := by exact_mod_cast h1.symm
    have h4 : (‖ζ‖ - 1) * (‖ζ‖ + 1) = 0 := by linear_combination h2
    rcases mul_eq_zero.mp h4 with h5 | h5
    · linarith
    · exfalso; linarith [norm_nonneg ζ]
  have hζ0 : ζ ≠ 0 := by
    intro h0
    rw [h0, norm_zero] at hn1
    norm_num at hn1
  refine ⟨2 * ζ.arg, ?_, ?_⟩
  · rw [show (2 * ζ.arg) / 2 = ζ.arg by ring, Complex.cos_arg hζ0, hn1,
      div_one, hζdef]
    simp
  · rw [show (2 * ζ.arg) / 2 = ζ.arg by ring, Complex.sin_arg, hn1,
      div_one, hζdef]
    simp

end QuantumAlg
