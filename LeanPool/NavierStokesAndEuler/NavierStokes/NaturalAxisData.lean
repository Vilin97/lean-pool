/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.NavierStokes.PressureDatum
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.ContDiff.Operations

/-!
# The fixed real natural-axis data

The small parameters are quantitative. The unique zero of `H` is proved,
not postulated. The pressure is an input with explicit real smoothness,
negativity, and derivative-sign hypotheses; its construction and complex
analytic estimates are separate results.
-/

@[expose] public section


noncomputable section

namespace NavierStokes.NaturalAxisData

open Set
open scoped ContDiff Topology

/-- D, given by `1 / 2 - h`. -/
def D (h : ℝ) : ℝ := 1 / 2 - h
/-- A, given by `1 / 2 + h`. -/
def A (h : ℝ) : ℝ := 1 / 2 + h
/-- D, given by `1 - η ^ 2`. -/
def d (η : ℝ) : ℝ := 1 - η ^ 2
/-- L, given by `1 - 2 * h * η ^ 2`. -/
def L (h η : ℝ) : ℝ := 1 - 2 * h * η ^ 2
/-- U, given by `4 * η + j`. -/
def U (j η : ℝ) : ℝ := 4 * η + j
/-- H, given by `D h * η + d η * U j η`. -/
def H (h j η : ℝ) : ℝ := D h * η + d η * U j η
/-- W, given by `1 - 4 * d η - 2 * D h * η * U j η`. -/
def W (h j η : ℝ) : ℝ := 1 - 4 * d η - 2 * D h * η * U j η
/-- Z, given by `-A h * (1 - 2 * η * U j η) * U j η - H h j η * 4 - d η * deriv P η + 4 * A h *
η * P η`. -/
def Z (h j : ℝ) (P : ℝ → ℝ) (η : ℝ) : ℝ :=
  -A h * (1 - 2 * η * U j η) * U j η - H h j η * 4 -
    d η * deriv P η + 4 * A h * η * P η

/-- Chi, given by `(H h j η) ^ 2 / ((H h j η) ^ 2 + σ ^ 2)`. -/
def chi (h j σ η : ℝ) : ℝ := (H h j η) ^ 2 / ((H h j η) ^ 2 + σ ^ 2)

/-- A concrete range of choices permitted by the manuscript's smallness order. -/
structure SmallParameters (h j : ℝ) : Prop where
  h_pos : 0 < h
  h_le : h ≤ 1 / 1000
  j_pos : 0 < j
  j_le : j ≤ 1 / 1000

theorem D_bounds {h j : ℝ} (p : SmallParameters h j) :
    499 / 1000 ≤ D h ∧ D h < 1 / 2 := by
  unfold D
  constructor <;> linarith [p.h_pos, p.h_le]

theorem D_pos {h j : ℝ} (p : SmallParameters h j) : 0 < D h := by
  linarith [(D_bounds p).1]

theorem A_bounds {h j : ℝ} (p : SmallParameters h j) :
    1 / 2 < A h ∧ A h ≤ 501 / 1000 := by
  unfold A
  constructor <;> linarith [p.h_pos, p.h_le]

theorem A_pos {h j : ℝ} (p : SmallParameters h j) : 0 < A h := by
  linarith [(A_bounds p).1]

theorem d_nonneg {η : ℝ} (hη : η ∈ Icc (-1 : ℝ) 1) : 0 ≤ d η := by
  have hp := mul_nonneg (sub_nonneg.mpr hη.2)
    (show 0 ≤ η + 1 by linarith [hη.1])
  unfold d
  nlinarith

theorem L_lower_bound {h j η : ℝ} (p : SmallParameters h j)
    (hη : η ∈ Icc (-1 : ℝ) 1) : 499 / 500 ≤ L h η := by
  have hp := mul_nonneg p.h_pos.le (d_nonneg hη)
  dsimp [d, L] at *
  nlinarith [p.h_le]

theorem L_pos {h j η : ℝ} (p : SmallParameters h j)
    (hη : η ∈ Icc (-1 : ℝ) 1) : 0 < L h η := by
  linarith [L_lower_bound p hη]

theorem neg_W_formula (h j η : ℝ) :
    -W h j η = 3 - 8 * h * η ^ 2 + 2 * D h * j * η := by
  unfold W U d D
  ring

/-- The proof gives 2.991, stronger than the manuscript's 2.8. -/
theorem neg_W_lower_bound {h j η : ℝ} (p : SmallParameters h j)
    (hη : η ∈ Icc (-1 : ℝ) 1) : 2991 / 1000 ≤ -W h j η := by
  have hDj : 0 ≤ 2 * D h * j :=
    mul_nonneg (mul_nonneg (by norm_num) (D_pos p).le) p.j_pos.le
  have hDjle : 2 * D h * j ≤ j := by
    nlinarith [mul_nonneg (show 0 ≤ 1 - 2 * D h by linarith [(D_bounds p).2]) p.j_pos.le]
  have hηDj : -(2 * D h * j) ≤ 2 * D h * j * η := by
    nlinarith [mul_nonneg hDj (show 0 ≤ η + 1 by linarith [hη.1])]
  have hhη : h * η ^ 2 ≤ h := by
    have hp := mul_nonneg p.h_pos.le (d_nonneg hη)
    dsimp [d] at hp
    nlinarith
  rw [neg_W_formula]
  nlinarith [p.h_le, p.j_le]

theorem neg_W_gt {h j η : ℝ} (p : SmallParameters h j)
    (hη : η ∈ Icc (-1 : ℝ) 1) : 14 / 5 < -W h j η := by
  linarith [neg_W_lower_bound p hη]

theorem H_contDiff (h j : ℝ) : ContDiff ℝ ∞ (H h j) := by
  unfold H U d
  exact (contDiff_const.mul contDiff_id).add
    ((contDiff_const.sub (contDiff_id.pow 2)).mul
      ((contDiff_const.mul contDiff_id).add contDiff_const))

theorem H_at_left (h j : ℝ) : H h j (-j / 4) = -(D h * j) / 4 := by
  unfold H U d
  ring

theorem H_at_right (h j : ℝ) :
    H h j (-j / 5) = (j / 5) * (1 - D h - j ^ 2 / 25) := by
  unfold H U d
  ring

theorem H_left_neg {h j : ℝ} (p : SmallParameters h j) : H h j (-j / 4) < 0 := by
  rw [H_at_left]
  have hp := mul_pos (D_pos p) p.j_pos
  linarith

theorem H_right_pos {h j : ℝ} (p : SmallParameters h j) : 0 < H h j (-j / 5) := by
  rw [H_at_right]
  apply mul_pos (div_pos p.j_pos (by norm_num))
  have hj1 : j ≤ 1 := by linarith [p.j_le]
  have hj2 : j ^ 2 ≤ 1 := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hj1) (show 0 ≤ j + 1 by linarith [p.j_pos])]
  nlinarith [(D_bounds p).2]

theorem H_pos_of_nonneg {h j η : ℝ} (p : SmallParameters h j)
    (hη : η ∈ Icc (-1 : ℝ) 1) (hη0 : 0 ≤ η) : 0 < H h j η := by
  rcases eq_or_lt_of_le hη0 with heq | hpos
  · subst η
    simpa [H, U, d] using p.j_pos
  · have hU : 0 ≤ U j η := by dsimp [U]; linarith [p.j_pos]
    exact add_pos_of_pos_of_nonneg (mul_pos (D_pos p) hpos)
      (mul_nonneg (d_nonneg hη) hU)

theorem H_neg_of_le_left {h j η : ℝ} (p : SmallParameters h j)
    (hη : η ∈ Icc (-1 : ℝ) 1) (hleft : η ≤ -j / 4) : H h j η < 0 := by
  have hη0 : η < 0 := by linarith [p.j_pos]
  have hU : U j η ≤ 0 := by dsimp [U]; linarith
  exact add_neg_of_neg_of_nonpos (mul_neg_of_pos_of_neg (D_pos p) hη0)
    (mul_nonpos_of_nonneg_of_nonpos (d_nonneg hη) hU)

theorem root_negative {h j η : ℝ} (p : SmallParameters h j)
    (hη : η ∈ Icc (-1 : ℝ) 1) (hzero : H h j η = 0) : η < 0 := by
  by_contra hn
  have hp := H_pos_of_nonneg p hη (le_of_not_gt hn)
  linarith

theorem cross_identity (h j x y : ℝ) :
    H h j x * d y - H h j y * d x =
      (x - y) * (D h * (1 + x * y) + 4 * d x * d y) := by
  unfold H U d
  ring

/-- Uniqueness is proved algebraically from the actual polynomial. -/
theorem root_unique {h j x y : ℝ} (p : SmallParameters h j)
    (hx : x ∈ Icc (-1 : ℝ) 1) (hy : y ∈ Icc (-1 : ℝ) 1)
    (hx0 : H h j x = 0) (hy0 : H h j y = 0) : x = y := by
  have hxn := root_negative p hx hx0
  have hyn := root_negative p hy hy0
  have hxy : 0 < x * y := mul_pos_of_neg_of_neg hxn hyn
  have hp : 0 < D h * (1 + x * y) + 4 * d x * d y :=
    add_pos_of_pos_of_nonneg (mul_pos (D_pos p) (by linarith))
      (mul_nonneg (mul_nonneg (by norm_num) (d_nonneg hx)) (d_nonneg hy))
  have hid := cross_identity h j x y
  rw [hx0, hy0] at hid
  have hprod : (x - y) * (D h * (1 + x * y) + 4 * d x * d y) = 0 := by
    linarith
  have heq := (mul_eq_zero.mp hprod).resolve_right (ne_of_gt hp)
  linarith

/-- The unique zero lies strictly between `-j/4` and `-j/5`. -/
theorem exists_unique_root {h j : ℝ} (p : SmallParameters h j) :
    ∃ η₀ : ℝ, η₀ ∈ Ioo (-j / 4) (-j / 5) ∧ H h j η₀ = 0 ∧
      ∀ η ∈ Icc (-1 : ℝ) 1, H h j η = 0 → η = η₀ := by
  have hab : -j / 4 ≤ -j / 5 := by linarith [p.j_pos]
  obtain ⟨η₀, hη₀, hz⟩ :=
    intermediate_value_Ioo (f := H h j) hab (H_contDiff h j).continuous.continuousOn
      (show (0 : ℝ) ∈ Ioo (H h j (-j / 4)) (H h j (-j / 5)) from
        ⟨H_left_neg p, H_right_pos p⟩)
  have hI : η₀ ∈ Icc (-1 : ℝ) 1 := by
    constructor <;> linarith [hη₀.1, hη₀.2, p.j_le, p.j_pos]
  exact ⟨η₀, hη₀, hz, fun η hη hzero => root_unique p hη hI hzero hz⟩

/-- Real pressure hypotheses provided by the separately constructed datum.
The derivative-sign condition is weak, so zero derivative is permitted. -/
structure PressureData (P : ℝ → ℝ) : Prop where
  smooth : ContDiff ℝ ∞ P
  negative : ∀ η ∈ Icc (-1 : ℝ) 1, P η ≤ -1
  derivative_sign : ∀ η ∈ Icc (-1 : ℝ) 1, 0 ≤ η * deriv P η

theorem PressureData.deriv_nonpos {P : ℝ → ℝ} (pP : PressureData P)
    {η : ℝ} (hη : η ∈ Icc (-1 : ℝ) 1) (hn : η < 0) : deriv P η ≤ 0 := by
  by_contra hp
  have hm := mul_neg_of_neg_of_pos hn (lt_of_not_ge hp)
  exact (not_lt_of_ge (pP.derivative_sign η hη)) hm

/-- A quantitative version of the crucial nonzero-root assertion:
pressure at most minus one is already sufficient. -/
theorem Z_at_root_lower {h j η : ℝ} {P : ℝ → ℝ} (p : SmallParameters h j)
    (hη : η ∈ Ioo (-j / 4) (-j / 5)) (hz : H h j η = 0)
    (hP : P η ≤ -1) (hP' : deriv P η ≤ 0) : j / 5 < Z h j P η := by
  have hηn : η < 0 := by linarith [hη.2, p.j_pos]
  have hI : η ∈ Icc (-1 : ℝ) 1 := by
    constructor <;> linarith [hη.1, hη.2, p.j_pos, p.j_le]
  have hU : 0 < U j η := by dsimp [U]; linarith [hη.1]
  have hUj : U j η < j / 5 := by dsimp [U]; linarith [hη.2]
  have hrU : -η * U j η ≤ U j η := by
    simpa using mul_le_mul_of_nonneg_right (show -η ≤ 1 by linarith [hI.1]) hU.le
  have hfactor : 1 - 2 * η * U j η ≤ 2 := by nlinarith [p.j_le]
  have hadverse : (1 - 2 * η * U j η) * U j η < 2 * j / 5 :=
    lt_of_le_of_lt (mul_le_mul_of_nonneg_right hfactor hU.le) (by linarith)
  have hpressure := mul_le_mul_of_nonpos_left hP hηn.le
  have hcore : 2 * j / 5 < -(1 - 2 * η * U j η) * U j η + 4 * η * P η := by
    nlinarith [hη.2]
  have hderiv : d η * deriv P η ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos (d_nonneg hI) hP'
  calc
    j / 5 ≤ A h * (2 * j / 5) := by
      nlinarith [mul_nonneg (show 0 ≤ A h - 1 / 2 by linarith [(A_bounds p).1]) p.j_pos.le]
    _ < A h * (-(1 - 2 * η * U j η) * U j η + 4 * η * P η) :=
      mul_lt_mul_of_pos_left hcore (A_pos p)
    _ ≤ Z h j P η := by
      unfold Z
      rw [hz]
      nlinarith

theorem Z_continuous (h j : ℝ) {P : ℝ → ℝ} (hP : ContDiff ℝ ∞ P) :
    Continuous (Z h j P) := by
  have hc : Continuous P := hP.continuous
  have hd : Continuous (deriv P) := hP.continuous_deriv
    (WithTop.coe_le_coe.mpr (le_top : (1 : ℕ∞) ≤ ⊤))
  unfold Z H U d
  fun_prop

/-- The true fixed data have a unique negative root at which `Z` is bounded
strictly away from zero. No root property is an input hypothesis. -/
theorem exists_root_with_positive_Z {h j : ℝ} {P : ℝ → ℝ}
    (p : SmallParameters h j) (pP : PressureData P) :
    ∃ η₀ : ℝ, η₀ ∈ Ioo (-j / 4) (-j / 5) ∧ H h j η₀ = 0 ∧
      j / 5 < Z h j P η₀ ∧
      ∀ η ∈ Icc (-1 : ℝ) 1, H h j η = 0 → η = η₀ := by
  obtain ⟨η₀, hη₀, hz, huniq⟩ := exists_unique_root p
  have hI : η₀ ∈ Icc (-1 : ℝ) 1 := by
    constructor <;> linarith [hη₀.1, hη₀.2, p.j_pos, p.j_le]
  have hn : η₀ < 0 := by linarith [hη₀.2, p.j_pos]
  exact ⟨η₀, hη₀, hz, Z_at_root_lower p hη₀ hz (pP.negative η₀ hI)
    (pP.deriv_nonpos hI hn), huniq⟩

/-- On the actual compact low-`Z` set, `H²` has a strictly positive uniform
minimum. The threshold is the explicit choice `δ_* = j/10`. -/
theorem low_Z_has_H_margin {h j : ℝ} {P : ℝ → ℝ}
    (p : SmallParameters h j) (pP : PressureData P) :
    ∃ m : ℝ, 0 < m ∧ ∀ η ∈ Icc (-1 : ℝ) 1,
      |Z h j P η| ≤ j / 10 → m ≤ (H h j η) ^ 2 := by
  obtain ⟨η₀, hη₀, hz, hZpos, huniq⟩ := exists_root_with_positive_Z p pP
  let K : Set ℝ := Icc (-1) 1 ∩ {η | |Z h j P η| ≤ j / 10}
  have hK : IsCompact K := isCompact_Icc.inter_right
    (isClosed_le (Z_continuous h j pP.smooth).abs continuous_const)
  have hnonzero : ∀ η ∈ K, H h j η ≠ 0 := by
    intro η hη hzero
    have heq := huniq η hη.1 hzero
    have hbound : Z h j P η ≤ j / 10 := (le_abs_self _).trans hη.2
    rw [heq] at hbound
    linarith [p.j_pos]
  have hpositive : ∀ η ∈ K, 0 < (H h j η) ^ 2 :=
    fun η hη => sq_pos_of_ne_zero (hnonzero η hη)
  obtain ⟨m, hm, hbound⟩ := hK.exists_forall_le'
    ((H_contDiff h j).continuous.pow 2).continuousOn hpositive
  exact ⟨m, hm, fun η hη hZ => hbound η ⟨hη, hZ⟩⟩

theorem chi_contDiff (h j : ℝ) {σ : ℝ} (hσ : 0 < σ) :
    ContDiff ℝ ∞ (chi h j σ) := by
  unfold chi
  apply ((H_contDiff h j).pow 2).div (((H_contDiff h j).pow 2).add contDiff_const)
  intro η
  exact ne_of_gt (add_pos_of_nonneg_of_pos (sq_nonneg _) (sq_pos_of_pos hσ))

theorem chi_bounds (h j : ℝ) {σ : ℝ} (hσ : 0 < σ) (η : ℝ) :
    0 ≤ chi h j σ η ∧ chi h j σ η < 1 := by
  have hsq : 0 < σ ^ 2 := sq_pos_of_pos hσ
  have hden : 0 < (H h j η) ^ 2 + σ ^ 2 :=
    add_pos_of_nonneg_of_pos (sq_nonneg _) hsq
  constructor
  · exact div_nonneg (sq_nonneg _) hden.le
  · exact (div_lt_one hden).mpr (lt_add_of_pos_right _ hsq)

/-- Construct the cutoff scale after the root-separation proof. The proof
chooses `σ_* = sqrt(m)/20` from the actual compact minimum bound. -/
theorem exists_sigma {h j : ℝ} {P : ℝ → ℝ}
    (p : SmallParameters h j) (pP : PressureData P) :
    ∃ σ : ℝ, 0 < σ ∧ ∀ η ∈ Icc (-1 : ℝ) 1,
      |Z h j P η| ≤ j / 10 → 99 / 100 < chi h j σ η := by
  obtain ⟨m, hm, hbound⟩ := low_Z_has_H_margin p pP
  let σ : ℝ := Real.sqrt m / 20
  have hσ : 0 < σ := div_pos (Real.sqrt_pos.mpr hm) (by norm_num)
  have hsq : σ ^ 2 = m / 400 := by
    dsimp [σ]
    rw [div_pow, Real.sq_sqrt hm.le]
    norm_num
  refine ⟨σ, hσ, ?_⟩
  intro η hη hZ
  have hH := hbound η hη hZ
  have hden : 0 < (H h j η) ^ 2 + σ ^ 2 := by nlinarith [sq_nonneg σ]
  unfold chi
  apply (lt_div_iff₀ hden).mpr
  nlinarith

/-- The requested fixed positive choices, with no input separation premise. -/
theorem exists_cutoff_parameters {h j : ℝ} {P : ℝ → ℝ}
    (p : SmallParameters h j) (pP : PressureData P) :
    ∃ δ σ : ℝ, 0 < δ ∧ 0 < σ ∧
      (∀ η ∈ Icc (-1 : ℝ) 1, |Z h j P η| ≤ δ → 99 / 100 < chi h j σ η) ∧
      ContDiff ℝ ∞ (chi h j σ) := by
  obtain ⟨σ, hσ, hcut⟩ := exists_sigma p pP
  exact ⟨j / 10, σ, div_pos p.j_pos (by norm_num), hσ, hcut, chi_contDiff h j hσ⟩

/-- The actual integral pressure datum satisfies the real axis hypotheses.
The ideal-prefix amplitude `B ≥ 2` suffices uniformly on `[-1,1]`. -/
theorem pressureData_of_ideal_prefix {g a : ℝ → ℝ} {cap B : ℝ}
    (hp : PressureDatum.Admissible g a cap) (hB : 2 ≤ B)
    (hg : ∀ y ≤ 0, g y = B ^ 2 * Real.exp ((1 / 5 : ℝ) * y))
    (ha : ∀ y ≤ 0, a y = 1) :
    PressureData (PressureDatum.pressure g a) := by
  have hBpos : 0 < B := by linarith
  have hmass := PressureDatum.exponent_mass_pos_of_ideal_prefix hp hBpos hg ha
  refine ⟨PressureDatum.pressure_contDiff hp, ?_, ?_⟩
  · intro η hη
    have hηsq : η ^ 2 ≤ 1 := by
      have hd := d_nonneg hη
      dsimp [d] at hd
      linarith
    have hden : 0 < 1 + η ^ 2 := by positivity
    have hi : 1 / 2 ≤ (1 + η ^ 2)⁻¹ := by
      rw [← one_div]
      apply (le_div_iff₀ hden).mpr
      linarith
    have hisq : (1 / 4 : ℝ) ≤ ((1 + η ^ 2)⁻¹) ^ 2 := by
      nlinarith [sq_nonneg ((1 + η ^ 2)⁻¹ - 1 / 2)]
    have hBsq : (4 : ℝ) ≤ B ^ 2 := by nlinarith
    have hprod : (1 : ℝ) ≤ B ^ 2 * ((1 + η ^ 2)⁻¹) ^ 2 := by
      have hm := mul_le_mul hBsq hisq (by norm_num : (0 : ℝ) ≤ 1 / 4) (sq_nonneg B)
      nlinarith
    have hpressure := PressureDatum.pressure_le_of_ideal_prefix hp hg ha η
    nlinarith
  · intro η hη
    rcases lt_trichotomy η 0 with hn | rfl | hpη
    · exact (mul_pos_of_neg_of_neg hn (PressureDatum.deriv_pressure_neg hp hmass hn)).le
    · simp
    · exact (mul_pos hpη (PressureDatum.deriv_pressure_pos hp hmass hpη)).le

/-- End-to-end real cutoff construction from the actual weighted pressure
integral and its ideal prefix, rather than assumed pressure conclusions. -/
theorem ideal_prefix_cutoff_parameters {h j : ℝ} (p : SmallParameters h j)
    {g a : ℝ → ℝ} {cap B : ℝ}
    (hp : PressureDatum.Admissible g a cap) (hB : 2 ≤ B)
    (hg : ∀ y ≤ 0, g y = B ^ 2 * Real.exp ((1 / 5 : ℝ) * y))
    (ha : ∀ y ≤ 0, a y = 1) :
    ∃ δ σ : ℝ, 0 < δ ∧ 0 < σ ∧
      (∀ η ∈ Icc (-1 : ℝ) 1,
        |Z h j (PressureDatum.pressure g a) η| ≤ δ → 99 / 100 < chi h j σ η) ∧
      ContDiff ℝ ∞ (chi h j σ) :=
  exists_cutoff_parameters p (pressureData_of_ideal_prefix hp hB hg ha)

theorem ideal_prefix_root_positive {h j : ℝ} (p : SmallParameters h j)
    {g a : ℝ → ℝ} {cap B : ℝ}
    (hp : PressureDatum.Admissible g a cap) (hB : 2 ≤ B)
    (hg : ∀ y ≤ 0, g y = B ^ 2 * Real.exp ((1 / 5 : ℝ) * y))
    (ha : ∀ y ≤ 0, a y = 1) :
    ∃ η₀ : ℝ, η₀ ∈ Ioo (-j / 4) (-j / 5) ∧ H h j η₀ = 0 ∧
      j / 5 < Z h j (PressureDatum.pressure g a) η₀ ∧
      ∀ η ∈ Icc (-1 : ℝ) 1, H h j η = 0 → η = η₀ :=
  exists_root_with_positive_Z p (pressureData_of_ideal_prefix hp hB hg ha)

end NavierStokes.NaturalAxisData
