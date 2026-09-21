/-
Copyright (c) 2026 Avik Das. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Avik Das
-/
/-
Copyright (c) 2026 adas1236. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: adas1236
-/
import LeanPool.KaltonPeck.KaltonPeck.Support.Definitions
import Mathlib.Analysis.InnerProductSpace.l2Space
import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# Coordinates for the real Kalton--Peck space

This file develops coordinate presentations of the real Kalton--Peck space, constructs the
canonical model and quotient map, and compares arbitrary complete presented models.
-/


namespace KaltonPeck.Support

noncomputable
section

/-- A real sequence is square-summable. -/
def IsSquareSummable (x : ℕ → ℝ) : Prop :=
  Summable fun n ↦ x n ^ 2

/-- The usual `ℓ₂` norm, defined on all real sequences and used on square-summable ones. -/
def l2Norm (x : ℕ → ℝ) : ℝ :=
  Real.sqrt (∑' n, x n ^ 2)

/-- The Kalton--Peck centralizer, with Lean's `Real.log 0 = 0` supplying the zero convention. -/
def centralizer (x : ℕ → ℝ) (n : ℕ) : ℝ :=
  2 * x n * Real.log (|x n| / l2Norm x)

/-- The admissible coordinate pairs in the usual real Kalton--Peck presentation. -/
def IsAdmissiblePair (p : (ℕ → ℝ) × (ℕ → ℝ)) : Prop :=
  IsSquareSummable p.2 ∧ IsSquareSummable (p.1 - centralizer p.2)

/-- The standard quasi-norm used to present the real Kalton--Peck space. -/
def kaltonPeckQuasiNorm (p : (ℕ → ℝ) × (ℕ → ℝ)) : ℝ :=
  l2Norm (p.1 - centralizer p.2) + l2Norm p.2

/-- A real Banach space carrying the standard Kalton--Peck coordinate presentation. -/
structure RealKaltonPeckPresentation (X : Type*) [NormedAddCommGroup X]
    [NormedSpace ℝ X] where
  /-- Linear coordinates identifying the space with the admissible Kalton--Peck pairs. -/
  coordinates : X →ₗ[ℝ] (ℕ → ℝ) × (ℕ → ℝ)
  coordinates_injective : Function.Injective coordinates
  coordinates_mem : ∀ z, IsAdmissiblePair (coordinates z)
  coordinates_surjective : ∀ p, IsAdmissiblePair p → ∃ z, coordinates z = p
  norm_equivalent : ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∀ z,
    c * kaltonPeckQuasiNorm (coordinates z) ≤ ‖z‖ ∧
      ‖z‖ ≤ C * kaltonPeckQuasiNorm (coordinates z)

namespace Coordinates

/-- The unscaled `K₀` centralizer used by the pinned canonical source.
Blueprint label: `lem:kp-normalization`; audit IDs `EXT-KP-CANONICAL-BANACH` and
`INF-KP-CANONICAL-MODEL`. -/
def k0Centralizer (x : ℕ → ℝ) : ℕ → ℝ := by
  exact fun n ↦ x n * Real.log (|x n| / l2Norm x)

/-- A real sequence is uniformly bounded.
Support definition for blueprint label `lem:kp-normalization`. -/
def IsBoundedSequence (x : ℕ → ℝ) : Prop := by
  exact ∃ C, ∀ n, |x n| ≤ C

/-- Admissibility for the source's `K₀` normalization.
Blueprint label: `lem:kp-normalization`. -/
def IsK0AdmissiblePair (p : (ℕ → ℝ) × (ℕ → ℝ)) : Prop := by
  exact IsBoundedSequence p.1 ∧ IsSquareSummable p.2 ∧
    IsSquareSummable (p.1 - k0Centralizer p.2)

/-- The `K₀` quasi-norm on pairs of real sequences.
Blueprint label: `lem:kp-normalization`. -/
def k0QuasiNorm (p : (ℕ → ℝ) × (ℕ → ℝ)) : ℝ := by
  exact l2Norm (p.1 - k0Centralizer p.2) + l2Norm p.2

/-- The ambient coordinate equivalence `(u, x) ↦ (u / 2, x)`.
Blueprint label: `lem:kp-normalization`. -/
def normalizationEquiv :
    ((ℕ → ℝ) × (ℕ → ℝ)) ≃ₗ[ℝ] ((ℕ → ℝ) × (ℕ → ℝ)) := by
  refine
    { toFun := fun p ↦ ((fun n ↦ p.1 n / 2), p.2)
      invFun := fun p ↦ ((fun n ↦ 2 * p.1 n), p.2)
      left_inv := ?_
      right_inv := ?_
      map_add' := ?_
      map_smul' := ?_ }
  · intro p q
    ext n <;> simp [add_div]
  · intro a p
    ext n <;> simp [mul_div_assoc]
  · intro p
    apply Prod.ext
    · funext n
      ring
    · rfl
  · intro p
    apply Prod.ext
    · funext n
      ring
    · rfl

/-- The exact factor-two adapter between the project and `K₀` conventions.
Blueprint label: `lem:kp-normalization`; audit IDs `EXT-KP-CANONICAL-BANACH`,
`INF-KP-CANONICAL-MODEL`, and `BLK-KP-CANONICAL-BANACH`. -/
lemma kpNormalization :
    (∀ x, IsSquareSummable x →
      IsBoundedSequence (k0Centralizer x) ∧
        ∀ n, |k0Centralizer x n| ≤ l2Norm x / Real.exp 1) ∧
      (∀ x, IsSquareSummable x → centralizer x = 2 • k0Centralizer x) ∧
      (∀ p, normalizationEquiv p = ((fun n ↦ p.1 n / 2), p.2)) ∧
      (∀ p, normalizationEquiv.symm p = ((fun n ↦ 2 * p.1 n), p.2)) ∧
      (∀ p, IsAdmissiblePair p ↔ IsK0AdmissiblePair (normalizationEquiv p)) ∧
      ∀ p, IsAdmissiblePair p →
        k0QuasiNorm (normalizationEquiv p) =
            (1 / 2 : ℝ) * l2Norm (p.1 - centralizer p.2) + l2Norm p.2 ∧
          (1 / 2 : ℝ) * kaltonPeckQuasiNorm p ≤ k0QuasiNorm (normalizationEquiv p) ∧
            k0QuasiNorm (normalizationEquiv p) ≤ kaltonPeckQuasiNorm p := by
  have coordinate_le (x : ℕ → ℝ) (hx : IsSquareSummable x) (n : ℕ) :
      |x n| ≤ l2Norm x := by
    have hterm : x n ^ 2 ≤ ∑' k, x k ^ 2 := by
      simpa using hx.sum_le_tsum {n} (fun k _ ↦ sq_nonneg (x k))
    have hsum : 0 ≤ ∑' k, x k ^ 2 :=
      (sq_nonneg (x n)).trans hterm
    rw [l2Norm]
    exact (Real.le_sqrt (abs_nonneg _) hsum).2 (by simpa [sq_abs] using hterm)
  have squareSummable_bounded (x : ℕ → ℝ) (hx : IsSquareSummable x) :
      IsBoundedSequence x :=
    ⟨l2Norm x, coordinate_le x hx⟩
  have bounded_add {x y : ℕ → ℝ}
      (hx : IsBoundedSequence x) (hy : IsBoundedSequence y) :
      IsBoundedSequence (x + y) := by
    obtain ⟨Cx, hx⟩ := hx
    obtain ⟨Cy, hy⟩ := hy
    refine ⟨Cx + Cy, fun n ↦ ?_⟩
    exact (abs_add_le (x n) (y n)).trans (add_le_add (hx n) (hy n))
  have bounded_smul (a : ℝ) {x : ℕ → ℝ} (hx : IsBoundedSequence x) :
      IsBoundedSequence (a • x) := by
    obtain ⟨C, hx⟩ := hx
    refine ⟨|a| * C, fun n ↦ ?_⟩
    simp only [Pi.smul_apply, smul_eq_mul, abs_mul]
    exact mul_le_mul_of_nonneg_left (hx n) (abs_nonneg a)
  have squareSummable_smul (a : ℝ) {x : ℕ → ℝ} (hx : IsSquareSummable x) :
      IsSquareSummable (a • x) := by
    rw [IsSquareSummable]
    have h := hx.mul_left (a ^ 2)
    exact h.congr (fun n ↦ by
      simp only [Pi.smul_apply]
      ring)
  have l2Norm_smul_nonneg (a : ℝ) (ha : 0 ≤ a) (x : ℕ → ℝ)
      (hx : IsSquareSummable x) :
      l2Norm (a • x) = a * l2Norm x := by
    have htsum :
        (∑' n, (a * x n) ^ 2) = a ^ 2 * ∑' n, x n ^ 2 := by
      have h := hx.tsum_mul_left (a ^ 2)
      rw [← h]
      congr 1
      funext n
      ring
    rw [l2Norm, l2Norm]
    simp only [Pi.smul_apply, smul_eq_mul, htsum]
    rw [Real.sqrt_mul (sq_nonneg a), Real.sqrt_sq_eq_abs, abs_of_nonneg ha]
  have entropy_bound {r : ℝ} (hr : 0 < r) (hr1 : r ≤ 1) :
      |r * Real.log r| ≤ 1 / Real.exp 1 := by
    have he : 0 < Real.exp 1 := Real.exp_pos 1
    have hbase := Real.log_le_sub_one_of_pos
      (show 0 < 1 / (Real.exp 1 * r) by positivity)
    have hlog : Real.log (1 / (Real.exp 1 * r)) = -1 - Real.log r := by
      rw [Real.log_div one_ne_zero (mul_ne_zero he.ne' hr.ne'),
        Real.log_one, Real.log_mul he.ne' hr.ne', Real.log_exp]
      ring
    rw [hlog] at hbase
    have hneg : -Real.log r ≤ 1 / (Real.exp 1 * r) := by linarith
    have hmul := mul_le_mul_of_nonneg_left hneg hr.le
    have hcalc : r * (1 / (Real.exp 1 * r)) = 1 / Real.exp 1 := by
      field_simp
    have hlog_nonpos : Real.log r ≤ 0 := Real.log_nonpos hr.le hr1
    rw [abs_of_nonpos (mul_nonpos_of_nonneg_of_nonpos hr.le hlog_nonpos)]
    rw [hcalc] at hmul
    nlinarith
  have hk0 (x : ℕ → ℝ) (hx : IsSquareSummable x) :
      IsBoundedSequence (k0Centralizer x) ∧
        ∀ n, |k0Centralizer x n| ≤ l2Norm x / Real.exp 1 := by
    have hnorm_nonneg : 0 ≤ l2Norm x := Real.sqrt_nonneg _
    by_cases hx0 : x = 0
    · subst x
      constructor
      · refine ⟨0, fun n ↦ ?_⟩
        simp [k0Centralizer]
      · intro n
        simp [k0Centralizer, l2Norm]
    have hnorm_ne : l2Norm x ≠ 0 := by
      intro hzero
      apply hx0
      funext n
      have hn := coordinate_le x hx n
      rw [hzero] at hn
      exact abs_eq_zero.mp (le_antisymm hn (abs_nonneg _))
    have hnorm_pos : 0 < l2Norm x :=
      lt_of_le_of_ne hnorm_nonneg (Ne.symm hnorm_ne)
    have hbound (n : ℕ) :
        |k0Centralizer x n| ≤ l2Norm x / Real.exp 1 := by
      by_cases hn0 : x n = 0
      · rw [k0Centralizer, hn0]
        simp only [zero_mul, abs_zero]
        exact div_nonneg hnorm_nonneg (Real.exp_pos 1).le
      let r : ℝ := |x n| / l2Norm x
      have hr : 0 < r := div_pos (abs_pos.mpr hn0) hnorm_pos
      have hr1 : r ≤ 1 :=
        (div_le_one hnorm_pos).2 (coordinate_le x hx n)
      have hentropy := entropy_bound hr hr1
      have hrewrite :
          |k0Centralizer x n| = l2Norm x * |r * Real.log r| := by
        rw [k0Centralizer, abs_mul, abs_mul]
        change |x n| * |Real.log r| = _
        rw [abs_of_pos hr]
        have hrdef : l2Norm x * r = |x n| := by
          dsimp only [r]
          field_simp
        rw [← hrdef]
        ring
      rw [hrewrite]
      have := mul_le_mul_of_nonneg_left hentropy hnorm_nonneg
      simpa [div_eq_mul_inv] using this
    exact ⟨⟨l2Norm x / Real.exp 1, hbound⟩, hbound⟩
  have hcentral (x : ℕ → ℝ) (hx : IsSquareSummable x) :
      centralizer x = 2 • k0Centralizer x := by
    funext n
    simp [centralizer, k0Centralizer]
    ring
  refine ⟨hk0, hcentral, ?_, ?_, ?_, ?_⟩
  · intro p
    rfl
  · intro p
    rfl
  · intro p
    constructor
    · intro hp
      rcases hp with ⟨hx, hdefect⟩
      have hcent := hcentral p.2 hx
      have hfirst :
          (fun n ↦ p.1 n / 2) =
            (1 / 2 : ℝ) • (p.1 - centralizer p.2) + k0Centralizer p.2 := by
        funext n
        change p.1 n / 2 =
          (1 / 2 : ℝ) * (p.1 n - centralizer p.2 n) + k0Centralizer p.2 n
        rw [congrFun hcent n]
        simp only [Pi.smul_apply]
        ring
      have hfirst_bounded : IsBoundedSequence (fun n ↦ p.1 n / 2) := by
        rw [hfirst]
        exact bounded_add (bounded_smul (1 / 2) (squareSummable_bounded _ hdefect))
          (hk0 p.2 hx).1
      refine ⟨hfirst_bounded, hx, ?_⟩
      have hscaled := squareSummable_smul (1 / 2 : ℝ) hdefect
      convert hscaled using 1
      funext n
      change p.1 n / 2 - k0Centralizer p.2 n =
        (1 / 2 : ℝ) * (p.1 n - centralizer p.2 n)
      rw [congrFun hcent n]
      simp only [Pi.smul_apply]
      ring
    · intro hp
      rcases hp with ⟨_, hx, hdefect⟩
      refine ⟨hx, ?_⟩
      have hcent := hcentral p.2 hx
      have hscaled := squareSummable_smul (2 : ℝ) hdefect
      convert hscaled using 1
      funext n
      change p.1 n - centralizer p.2 n =
        2 * (p.1 n / 2 - k0Centralizer p.2 n)
      rw [congrFun hcent n]
      simp only [Pi.smul_apply]
      ring
  · intro p hp
    have hcent := hcentral p.2 hp.1
    have hseq :
        (normalizationEquiv p).1 - k0Centralizer (normalizationEquiv p).2 =
          (1 / 2 : ℝ) • (p.1 - centralizer p.2) := by
      funext n
      change p.1 n / 2 - k0Centralizer p.2 n =
        (1 / 2 : ℝ) * (p.1 n - centralizer p.2 n)
      rw [congrFun hcent n]
      simp only [Pi.smul_apply]
      ring
    have hnorm := l2Norm_smul_nonneg (1 / 2 : ℝ) (by norm_num)
      (p.1 - centralizer p.2) hp.2
    have hexact :
        k0QuasiNorm (normalizationEquiv p) =
          (1 / 2 : ℝ) * l2Norm (p.1 - centralizer p.2) + l2Norm p.2 := by
      rw [k0QuasiNorm, hseq, hnorm]
      rfl
    have hA : 0 ≤ l2Norm (p.1 - centralizer p.2) := Real.sqrt_nonneg _
    have hB : 0 ≤ l2Norm p.2 := Real.sqrt_nonneg _
    refine ⟨hexact, ?_, ?_⟩
    · rw [hexact, kaltonPeckQuasiNorm]
      nlinarith
    · rw [hexact, kaltonPeckQuasiNorm]
      nlinarith

/-- Both coordinates of a pair have finite support.
Support definition for blueprint label `thm:kp-canonical-banach`. -/
def IsFiniteCoordinatePair (p : (ℕ → ℝ) × (ℕ → ℝ)) : Prop := by
  exact Set.Finite {n | p.1 n ≠ 0} ∧ Set.Finite {n | p.2 n ≠ 0}

/-- The fixed project-normalized canonical real Kalton--Peck carrier.
Blueprint label: `thm:kp-canonical-banach`; audit ID `INF-KP-CANONICAL-MODEL`. -/
def CanonicalRealKaltonPeck : Type := by
  exact {p : (ℕ → ℝ) × (ℕ → ℝ) // IsAdmissiblePair p}

open scoped ENNReal NNReal Topology lp
open Filter Topology

private abbrev L2 := lp (fun _ : ℕ => ℝ) 2

private def toL2 (x : ℕ → ℝ) (hx : IsSquareSummable x) : L2 :=
  ⟨x, by
    apply memℓp_gen
    simpa [IsSquareSummable, Real.norm_eq_abs, sq_abs] using hx⟩

private lemma l2Norm_eq_norm_toL2 (x : ℕ → ℝ) (hx : IsSquareSummable x) :
    l2Norm x = ‖toL2 x hx‖ := by
  apply (sq_eq_sq₀ (Real.sqrt_nonneg _) (norm_nonneg _)).mp
  rw [Real.sq_sqrt (tsum_nonneg fun n => sq_nonneg (x n))]
  symm
  rw [norm_sq_eq_re_inner (𝕜 := ℝ), lp.inner_eq_tsum]
  simp [toL2, pow_two]

private def entropy (t : ℝ) : ℝ := t * Real.log |t|

private lemma abs_entropy_le_one {t : ℝ} (ht : |t| ≤ 1) : |entropy t| ≤ 1 := by
  by_cases hzero : t = 0
  · simp [hzero, entropy]
  have hpos : 0 < |t| := abs_pos.mpr hzero
  have h := (Real.abs_log_mul_self_lt |t| hpos ht).le
  calc
    abs (entropy t) = abs (Real.log |t| * |t|) := by
      simp only [entropy, abs_mul, abs_abs]
      ring
    _ ≤ 1 := h

private lemma entropy_scale (t S : ℝ) (hS : 0 < S) :
    entropy t = S * entropy (t / S) + t * Real.log S := by
  by_cases ht : t = 0
  · simp [ht, entropy]
  have hS0 : S ≠ 0 := hS.ne'
  have habst : |t| ≠ 0 := abs_ne_zero.mpr ht
  rw [entropy, entropy, abs_div, abs_of_pos hS, Real.log_div habst hS0]
  field_simp
  ring

private lemma entropy_add_defect_bound (a b : ℝ) :
    |entropy a + entropy b - entropy (a + b)| ≤ 3 * (|a| + |b|) := by
  let c := |a| + |b|
  by_cases hc0 : c = 0
  · have ha : a = 0 := by
      have : |a| = 0 := by linarith [abs_nonneg a, abs_nonneg b]
      exact abs_eq_zero.mp this
    have hb : b = 0 := by
      have : |b| = 0 := by linarith [abs_nonneg a, abs_nonneg b]
      exact abs_eq_zero.mp this
    simp [ha, hb, entropy]
  have hc : 0 < c := lt_of_le_of_ne (by positivity) (Ne.symm hc0)
  have ha_unit : |a / c| ≤ 1 := by
    rw [abs_div, abs_of_pos hc, div_le_one hc]
    dsimp [c]
    linarith [abs_nonneg b]
  have hb_unit : |b / c| ≤ 1 := by
    rw [abs_div, abs_of_pos hc, div_le_one hc]
    dsimp [c]
    linarith [abs_nonneg a]
  have hab_unit : |(a + b) / c| ≤ 1 := by
    rw [abs_div, abs_of_pos hc, div_le_one hc]
    exact abs_add_le a b
  rw [entropy_scale (a + b) c hc, entropy_scale a c hc,
    entropy_scale b c hc]
  have htri :
      |entropy ((a + b) / c) - entropy (a / c) - entropy (b / c)| ≤ 3 := by
    calc
      |entropy ((a + b) / c) - entropy (a / c) - entropy (b / c)| ≤
          |entropy ((a + b) / c)| + |entropy (a / c)| + |entropy (b / c)| :=
        (abs_sub _ _).trans (add_le_add (abs_sub _ _) le_rfl)
      _ ≤ 1 + 1 + 1 := by
        gcongr
        · exact abs_entropy_le_one hab_unit
        · exact abs_entropy_le_one ha_unit
        · exact abs_entropy_le_one hb_unit
      _ = 3 := by norm_num
  have hid :
      c * entropy (a / c) + a * Real.log c +
          (c * entropy (b / c) + b * Real.log c) -
        (c * entropy ((a + b) / c) + (a + b) * Real.log c) =
      -c * (entropy ((a + b) / c) - entropy (a / c) - entropy (b / c)) := by
    ring
  rw [hid, abs_mul, abs_neg, abs_of_pos hc]
  nlinarith

private lemma squareSummable_iff_memL2 (x : ℕ → ℝ) :
    IsSquareSummable x ↔ Memℓp x 2 := by
  constructor
  · intro hx
    exact (toL2 x hx).2
  · intro hx
    have hs := hx.summable (by norm_num)
    simpa [IsSquareSummable, Real.norm_eq_abs, sq_abs] using hs

private lemma squareSummable_zero : IsSquareSummable (0 : ℕ → ℝ) := by
  rw [squareSummable_iff_memL2]
  exact zero_memℓp

private lemma squareSummable_add {x y : ℕ → ℝ}
    (hx : IsSquareSummable x) (hy : IsSquareSummable y) : IsSquareSummable (x + y) := by
  rw [squareSummable_iff_memL2] at hx hy ⊢
  exact hx.add hy

private lemma squareSummable_smul (a : ℝ) {x : ℕ → ℝ} (hx : IsSquareSummable x) :
    IsSquareSummable (a • x) := by
  rw [squareSummable_iff_memL2] at hx ⊢
  exact hx.const_smul a

private lemma toL2_add (x y : ℕ → ℝ) (hx : IsSquareSummable x)
    (hy : IsSquareSummable y) :
    toL2 (x + y) (squareSummable_add hx hy) = toL2 x hx + toL2 y hy := by
  ext n
  rfl

private lemma toL2_smul (a : ℝ) (x : ℕ → ℝ) (hx : IsSquareSummable x) :
    toL2 (a • x) (squareSummable_smul a hx) = a • toL2 x hx := by
  ext n
  rfl

private lemma l2Norm_zero : l2Norm (0 : ℕ → ℝ) = 0 := by simp [l2Norm]

private lemma l2Norm_nonneg (x : ℕ → ℝ) : 0 ≤ l2Norm x := Real.sqrt_nonneg _

private lemma l2Norm_smul (a : ℝ) (x : ℕ → ℝ) (hx : IsSquareSummable x) :
    l2Norm (a • x) = |a| * l2Norm x := by
  rw [l2Norm_eq_norm_toL2 (a • x) (squareSummable_smul a hx),
    l2Norm_eq_norm_toL2 x hx, toL2_smul, norm_smul, Real.norm_eq_abs]

private lemma l2Norm_eq_zero_iff (x : ℕ → ℝ) (hx : IsSquareSummable x) :
    l2Norm x = 0 ↔ x = 0 := by
  rw [l2Norm_eq_norm_toL2 x hx, norm_eq_zero, lp.ext_iff]
  rfl

private lemma l2Norm_pos (x : ℕ → ℝ) (hx : IsSquareSummable x) (hxn : x ≠ 0) :
    0 < l2Norm x :=
  lt_of_le_of_ne (l2Norm_nonneg x) fun h ↦
    hxn ((l2Norm_eq_zero_iff x hx).mp h.symm)

private lemma centralizer_smul (a : ℝ) (x : ℕ → ℝ) (hx : IsSquareSummable x) :
    centralizer (a • x) = a • centralizer x := by
  by_cases ha : a = 0
  · subst a
    funext n
    simp [centralizer, l2Norm]
  funext n
  change 2 * (a * x n) * Real.log (|a * x n| / l2Norm (a • x)) =
    a * (2 * x n * Real.log (|x n| / l2Norm x))
  rw [l2Norm_smul a x hx]
  simp only [abs_mul]
  have habs : |a| ≠ 0 := abs_ne_zero.mpr ha
  have hratio : |a| * |x n| / (|a| * l2Norm x) = |x n| / l2Norm x := by
    field_simp
  rw [hratio]
  ring

private lemma centralizer_zero : centralizer (0 : ℕ → ℝ) = 0 := by
  simpa using centralizer_smul 0 (0 : ℕ → ℝ) squareSummable_zero

private lemma centralizer_entropy (x : ℕ → ℝ) (hx : IsSquareSummable x) (n : ℕ) :
    centralizer x n = 2 * (entropy (x n) - x n * Real.log (l2Norm x)) := by
  by_cases hxn : x = 0
  · subst x
    simp [centralizer_zero, entropy, l2Norm_zero]
  have hnorm := l2Norm_pos x hx hxn
  by_cases hcoord : x n = 0
  · simp [hcoord, centralizer, entropy]
  rw [centralizer, entropy, Real.log_div (abs_ne_zero.mpr hcoord) hnorm.ne']
  ring

private lemma entropyDefect_squareSummable (x y : ℕ → ℝ)
    (hx : IsSquareSummable x) (hy : IsSquareSummable y) :
    IsSquareSummable (fun n ↦ entropy (x n) + entropy (y n) - entropy (x n + y n)) := by
  rw [squareSummable_iff_memL2]
  have hbound : Memℓp (fun n ↦ 3 * (|x n| + |y n|)) 2 := by
    have hx' : Memℓp x 2 := (squareSummable_iff_memL2 x).mp hx
    have hy' : Memℓp y 2 := (squareSummable_iff_memL2 y).mp hy
    convert (hx'.norm.add hy'.norm).const_smul (3 : ℝ) using 1
  exact hbound.mono fun n ↦ by
    simpa only [Real.norm_eq_abs] using entropy_add_defect_bound (x n) (y n)

private lemma centralizer_add_defect_squareSummable (x y : ℕ → ℝ)
    (hx : IsSquareSummable x) (hy : IsSquareSummable y) :
    IsSquareSummable (centralizer x + centralizer y - centralizer (x + y)) := by
  have hxy := squareSummable_add hx hy
  have hlocal := entropyDefect_squareSummable x y hx hy
  have hxlog := squareSummable_smul (-2 * Real.log (l2Norm x)) hx
  have hylog := squareSummable_smul (-2 * Real.log (l2Norm y)) hy
  have hxylog := squareSummable_smul (2 * Real.log (l2Norm (x + y))) hxy
  have hsum := squareSummable_add
    (squareSummable_smul 2 hlocal)
    (squareSummable_add (squareSummable_add hxlog hylog) hxylog)
  apply (squareSummable_iff_memL2 _).mpr
  have hmem := (squareSummable_iff_memL2 _).mp hsum
  convert hmem using 1
  funext n
  simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  rw [centralizer_entropy x hx n, centralizer_entropy y hy n,
    centralizer_entropy (x + y) hxy n]
  simp only [Pi.add_apply]
  ring

private lemma admissible_zero : IsAdmissiblePair (0 : (ℕ → ℝ) × (ℕ → ℝ)) := by
  refine ⟨squareSummable_zero, ?_⟩
  simpa [centralizer_zero] using squareSummable_zero

private lemma admissible_add {p q : (ℕ → ℝ) × (ℕ → ℝ)}
    (hp : IsAdmissiblePair p) (hq : IsAdmissiblePair q) : IsAdmissiblePair (p + q) := by
  refine ⟨squareSummable_add hp.1 hq.1, ?_⟩
  let rp := p.1 - centralizer p.2
  let rq := q.1 - centralizer q.2
  let d := centralizer p.2 + centralizer q.2 - centralizer (p.2 + q.2)
  have hrp : IsSquareSummable rp := hp.2
  have hrq : IsSquareSummable rq := hq.2
  have hd : IsSquareSummable d :=
    centralizer_add_defect_squareSummable p.2 q.2 hp.1 hq.1
  have hsum := squareSummable_add (squareSummable_add hrp hrq) hd
  convert hsum using 1
  funext n
  simp [rp, rq, d]
  ring

private lemma admissible_smul (a : ℝ) {p : (ℕ → ℝ) × (ℕ → ℝ)}
    (hp : IsAdmissiblePair p) : IsAdmissiblePair (a • p) := by
  have hcentral := centralizer_smul a p.2 hp.1
  refine ⟨?_, ?_⟩
  · change IsSquareSummable (a • p.2)
    exact squareSummable_smul a hp.1
  · have := squareSummable_smul a hp.2
    convert this using 1
    funext n
    change (a * p.1 n - centralizer (a • p.2) n) =
      a * (p.1 n - centralizer p.2 n)
    rw [congrFun hcentral n]
    simp only [Pi.smul_apply, smul_eq_mul]
    ring

private lemma abs_mul_log_sub_log_le_sq_add_sq (a b : ℝ) :
    abs (a * b * (Real.log |a| - Real.log |b|)) ≤ a ^ 2 + b ^ 2 := by
  by_cases ha : a = 0
  · subst a
    simpa using sq_nonneg b
  by_cases hb : b = 0
  · subst b
    simpa using sq_nonneg a
  have hA : 0 < |a| := abs_pos.mpr ha
  have hB : 0 < |b| := abs_pos.mpr hb
  rw [abs_mul, abs_mul]
  by_cases hab : |a| ≤ |b|
  · have hratio : 1 ≤ |b| / |a| := (le_div_iff₀ hA).mpr (by simpa using hab)
    have hlog : Real.log (|b| / |a|) ≤ |b| / |a| :=
      Real.log_le_self (by positivity)
    have hdiff : abs (Real.log |a| - Real.log |b|) = Real.log (|b| / |a|) := by
      rw [abs_sub_comm, ← Real.log_div (abs_ne_zero.mpr hb) (abs_ne_zero.mpr ha),
        abs_of_nonneg (Real.log_nonneg hratio)]
    rw [hdiff]
    calc
      |a| * |b| * Real.log (|b| / |a|) ≤ |a| * |b| * (|b| / |a|) := by gcongr
      _ = b ^ 2 := by field_simp; exact sq_abs b
      _ ≤ a ^ 2 + b ^ 2 := by nlinarith [sq_nonneg a]
  · have hba : |b| ≤ |a| := le_of_lt (lt_of_not_ge hab)
    have hratio : 1 ≤ |a| / |b| := (le_div_iff₀ hB).mpr (by simpa using hba)
    have hlog : Real.log (|a| / |b|) ≤ |a| / |b| :=
      Real.log_le_self (by positivity)
    have hdiff : abs (Real.log |a| - Real.log |b|) = Real.log (|a| / |b|) := by
      rw [← Real.log_div (abs_ne_zero.mpr ha) (abs_ne_zero.mpr hb),
        abs_of_nonneg (Real.log_nonneg hratio)]
    rw [hdiff]
    calc
      |a| * |b| * Real.log (|a| / |b|) ≤ |a| * |b| * (|a| / |b|) := by gcongr
      _ = a ^ 2 := by field_simp; exact sq_abs a
      _ ≤ a ^ 2 + b ^ 2 := by nlinarith [sq_nonneg b]

private def rawSubmodule : Submodule ℝ ((ℕ → ℝ) × (ℕ → ℝ)) where
  carrier := {p | IsAdmissiblePair p}
  zero_mem' := admissible_zero
  add_mem' := admissible_add
  smul_mem' := admissible_smul

private abbrev Raw : Type := rawSubmodule

private def secondL2 : Raw →ₗ[ℝ] L2 where
  toFun p := toL2 p.1.2 p.2.1
  map_add' p q := by
    apply Subtype.ext
    rfl
  map_smul' a p := by
    apply Subtype.ext
    rfl

private lemma secondL2_norm (p : Raw) : ‖secondL2 p‖ = l2Norm p.1.2 := by
  symm
  exact l2Norm_eq_norm_toL2 p.1.2 p.2.1

private lemma tsum_sq_eq_l2Norm_sq (x : ℕ → ℝ) :
    ∑' n, x n ^ 2 = l2Norm x ^ 2 := by
  rw [l2Norm, Real.sq_sqrt (tsum_nonneg fun n ↦ sq_nonneg (x n))]

private lemma centralizer_of_l2Norm_one (x : ℕ → ℝ) (hx : IsSquareSummable x)
    (hnorm : l2Norm x = 1) (n : ℕ) : centralizer x n = 2 * entropy (x n) := by
  rw [centralizer_entropy x hx n, hnorm]
  simp [entropy]

private def commutatorTerm (x y : ℕ → ℝ) (n : ℕ) : ℝ :=
  centralizer x n * y n - x n * centralizer y n

private lemma centralizer_commutator_summable (x y : ℕ → ℝ)
    (hx : IsSquareSummable x) (hy : IsSquareSummable y) :
    Summable (commutatorTerm x y) := by
  by_cases hx0 : x = 0
  · subst x
    have hz : commutatorTerm 0 y = 0 := by
      funext n
      simp [commutatorTerm, centralizer_zero]
    rw [hz]
    exact summable_zero
  by_cases hy0 : y = 0
  · subst y
    have hz : commutatorTerm x 0 = 0 := by
      funext n
      simp [commutatorTerm, centralizer_zero]
    rw [hz]
    exact summable_zero
  have hnx : 0 < l2Norm x := l2Norm_pos x hx hx0
  have hny : 0 < l2Norm y := l2Norm_pos y hy hy0
  let xn : ℕ → ℝ := (l2Norm x)⁻¹ • x
  let yn : ℕ → ℝ := (l2Norm y)⁻¹ • y
  have hxn : IsSquareSummable xn := squareSummable_smul _ hx
  have hyn : IsSquareSummable yn := squareSummable_smul _ hy
  have hxn_norm : l2Norm xn = 1 := by
    rw [l2Norm_smul _ x hx, abs_inv, abs_of_pos hnx, inv_mul_cancel₀ hnx.ne']
  have hyn_norm : l2Norm yn = 1 := by
    rw [l2Norm_smul _ y hy, abs_inv, abs_of_pos hny, inv_mul_cancel₀ hny.ne']
  have hx_repr : x = l2Norm x • xn := by simp [xn, hnx.ne']
  have hy_repr : y = l2Norm y • yn := by simp [yn, hny.ne']
  have hKx : centralizer x = l2Norm x • centralizer xn := by
    conv_lhs => rw [hx_repr]
    exact centralizer_smul (l2Norm x) xn hxn
  have hKy : centralizer y = l2Norm y • centralizer yn := by
    conv_lhs => rw [hy_repr]
    exact centralizer_smul (l2Norm y) yn hyn
  have hpoint (n : ℕ) :
      |commutatorTerm xn yn n| ≤ 2 * (xn n ^ 2 + yn n ^ 2) := by
    have hterm : commutatorTerm xn yn n =
        2 * (xn n * yn n * (Real.log |xn n| - Real.log |yn n|)) := by
      rw [commutatorTerm, centralizer_of_l2Norm_one xn hxn hxn_norm,
        centralizer_of_l2Norm_one yn hyn hyn_norm]
      simp only [entropy]
      ring
    rw [hterm, abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
    have h := abs_mul_log_sub_log_le_sq_add_sq (xn n) (yn n)
    exact mul_le_mul_of_nonneg_left h (by norm_num)
  have hnormalized : Summable (commutatorTerm xn yn) := by
    have hbound : Summable (fun n ↦ 2 * (xn n ^ 2 + yn n ^ 2)) :=
      ((hxn.add hyn).mul_left 2)
    exact hbound.of_norm_bounded fun n ↦ by
      simpa only [Real.norm_eq_abs] using hpoint n
  have hscale : commutatorTerm x y =
      fun n ↦ l2Norm x * l2Norm y * commutatorTerm xn yn n := by
    funext n
    have hx_apply : x n = l2Norm x * xn n := congrFun hx_repr n
    have hy_apply : y n = l2Norm y * yn n := congrFun hy_repr n
    rw [commutatorTerm, commutatorTerm, congrFun hKx n, congrFun hKy n,
      hx_apply, hy_apply]
    simp only [Pi.smul_apply, smul_eq_mul]
    ring
  rw [hscale]
  exact hnormalized.mul_left _

private lemma centralizer_commutator_tsum_bound (x y : ℕ → ℝ)
    (hx : IsSquareSummable x) (hy : IsSquareSummable y) :
    |∑' n, commutatorTerm x y n| ≤ 4 * l2Norm x * l2Norm y := by
  by_cases hx0 : x = 0
  · subst x
    simp [commutatorTerm, centralizer_zero, l2Norm_zero]
  by_cases hy0 : y = 0
  · subst y
    simp [commutatorTerm, centralizer_zero, l2Norm_zero]
  have hnx : 0 < l2Norm x := l2Norm_pos x hx hx0
  have hny : 0 < l2Norm y := l2Norm_pos y hy hy0
  let xn : ℕ → ℝ := (l2Norm x)⁻¹ • x
  let yn : ℕ → ℝ := (l2Norm y)⁻¹ • y
  have hxn : IsSquareSummable xn := squareSummable_smul _ hx
  have hyn : IsSquareSummable yn := squareSummable_smul _ hy
  have hxn_norm : l2Norm xn = 1 := by
    rw [l2Norm_smul _ x hx, abs_inv, abs_of_pos hnx, inv_mul_cancel₀ hnx.ne']
  have hyn_norm : l2Norm yn = 1 := by
    rw [l2Norm_smul _ y hy, abs_inv, abs_of_pos hny, inv_mul_cancel₀ hny.ne']
  have hx_repr : x = l2Norm x • xn := by simp [xn, hnx.ne']
  have hy_repr : y = l2Norm y • yn := by simp [yn, hny.ne']
  have hKx : centralizer x = l2Norm x • centralizer xn := by
    conv_lhs => rw [hx_repr]
    exact centralizer_smul (l2Norm x) xn hxn
  have hKy : centralizer y = l2Norm y • centralizer yn := by
    conv_lhs => rw [hy_repr]
    exact centralizer_smul (l2Norm y) yn hyn
  have hpoint (n : ℕ) :
      |commutatorTerm xn yn n| ≤ 2 * (xn n ^ 2 + yn n ^ 2) := by
    have hterm : commutatorTerm xn yn n =
        2 * (xn n * yn n * (Real.log |xn n| - Real.log |yn n|)) := by
      rw [commutatorTerm, centralizer_of_l2Norm_one xn hxn hxn_norm,
        centralizer_of_l2Norm_one yn hyn hyn_norm]
      simp only [entropy]
      ring
    rw [hterm, abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
    have h := abs_mul_log_sub_log_le_sq_add_sq (xn n) (yn n)
    exact mul_le_mul_of_nonneg_left h (by norm_num)
  have hnormalized := centralizer_commutator_summable xn yn hxn hyn
  have hbound : Summable (fun n ↦ 2 * (xn n ^ 2 + yn n ^ 2)) :=
    ((hxn.add hyn).mul_left 2)
  have hnorm_tsum : |∑' n, commutatorTerm xn yn n| ≤ 4 := by
    calc
      |∑' n, commutatorTerm xn yn n| ≤ ∑' n, |commutatorTerm xn yn n| := by
        simpa only [Real.norm_eq_abs] using norm_tsum_le_tsum_norm hnormalized.norm
      _ ≤ ∑' n, 2 * (xn n ^ 2 + yn n ^ 2) :=
        Summable.tsum_le_tsum hpoint hnormalized.norm hbound
      _ = 2 * ((∑' n, xn n ^ 2) + ∑' n, yn n ^ 2) := by
        rw [tsum_mul_left]
        congr 1
        exact Summable.tsum_add hxn hyn
      _ = 4 := by
        rw [tsum_sq_eq_l2Norm_sq, tsum_sq_eq_l2Norm_sq, hxn_norm, hyn_norm]
        norm_num
  have hscale : commutatorTerm x y =
      fun n ↦ l2Norm x * l2Norm y * commutatorTerm xn yn n := by
    funext n
    have hx_apply : x n = l2Norm x * xn n := congrFun hx_repr n
    have hy_apply : y n = l2Norm y * yn n := congrFun hy_repr n
    rw [commutatorTerm, commutatorTerm, congrFun hKx n, congrFun hKy n,
      hx_apply, hy_apply]
    simp only [Pi.smul_apply, smul_eq_mul]
    ring
  rw [hscale, tsum_mul_left, abs_mul, abs_mul, abs_of_pos hnx, abs_of_pos hny]
  calc
    l2Norm x * l2Norm y * |∑' n, commutatorTerm xn yn n| ≤
        l2Norm x * l2Norm y * 4 :=
      mul_le_mul_of_nonneg_left hnorm_tsum (mul_nonneg hnx.le hny.le)
    _ = 4 * l2Norm x * l2Norm y := by ring

private def sectionPairingTerm (p : Raw) (y : L2) (n : ℕ) : ℝ :=
  p.1.1 n * y n - p.1.2 n * centralizer (fun k ↦ y k) n

private lemma sectionPairingTerm_summable (p : Raw) (y : L2) :
    Summable (sectionPairingTerm p y) := by
  let r : ℕ → ℝ := p.1.1 - centralizer p.1.2
  have hr : IsSquareSummable r := p.2.2
  have hy : IsSquareSummable (fun n ↦ y n) := by
    rw [squareSummable_iff_memL2]
    exact y.2
  have hinner : Summable (fun n ↦ r n * y n) := by
    have hpq : (2 : ℝ≥0∞).toReal.HolderConjugate (2 : ℝ≥0∞).toReal := by
      rw [Real.holderConjugate_iff]
      norm_num
    refine (lp.summable_mul hpq (toL2 r hr) y).of_norm_bounded ?_
    intro n
    simp only [norm_mul, toL2]
    exact le_rfl
  have hcomm := centralizer_commutator_summable p.1.2 (fun n ↦ y n) p.2.1 hy
  convert hinner.add hcomm using 1
  funext n
  simp [sectionPairingTerm, commutatorTerm, r]
  ring

private def sectionPairing (p : Raw) (y : L2) : ℝ :=
  ∑' n, sectionPairingTerm p y n

private lemma sectionPairing_decomp (p : Raw) (y : L2) :
    sectionPairing p y =
      (∑' n, (p.1.1 - centralizer p.1.2) n * y n) +
        ∑' n, commutatorTerm p.1.2 (fun n ↦ y n) n := by
  let r : ℕ → ℝ := p.1.1 - centralizer p.1.2
  have hr : IsSquareSummable r := p.2.2
  have hy : IsSquareSummable (fun n ↦ y n) := by
    rw [squareSummable_iff_memL2]
    exact y.2
  have hpq : (2 : ℝ≥0∞).toReal.HolderConjugate (2 : ℝ≥0∞).toReal := by
    rw [Real.holderConjugate_iff]
    norm_num
  have hinner : Summable (fun n ↦ r n * y n) := by
    refine (lp.summable_mul hpq (toL2 r hr) y).of_norm_bounded ?_
    intro n
    simp only [norm_mul, toL2]
    exact le_rfl
  rw [sectionPairing, ← hinner.tsum_add
    (centralizer_commutator_summable p.1.2 (fun n ↦ y n) p.2.1 hy)]
  congr 1
  funext n
  simp only [sectionPairingTerm, commutatorTerm, r, Pi.sub_apply]
  ring

private lemma sectionPairing_bound (p : Raw) (y : L2) :
    |sectionPairing p y| ≤
      (l2Norm (p.1.1 - centralizer p.1.2) + 4 * l2Norm p.1.2) * ‖y‖ := by
  let r : ℕ → ℝ := p.1.1 - centralizer p.1.2
  have hr : IsSquareSummable r := p.2.2
  have hy : IsSquareSummable (fun n ↦ y n) := by
    rw [squareSummable_iff_memL2]
    exact y.2
  have hdecomp : sectionPairing p y =
      (∑' n, r n * y n) + ∑' n, commutatorTerm p.1.2 (fun n ↦ y n) n := by
    rw [sectionPairing, ← Summable.tsum_add]
    · congr 1
      funext n
      simp [sectionPairingTerm, commutatorTerm, r]
      ring
    · have hpq : (2 : ℝ≥0∞).toReal.HolderConjugate (2 : ℝ≥0∞).toReal := by
        rw [Real.holderConjugate_iff]
        norm_num
      refine (lp.summable_mul hpq (toL2 r hr) y).of_norm_bounded ?_
      intro n
      simp only [norm_mul, toL2]
      exact le_rfl
    · exact centralizer_commutator_summable p.1.2 (fun n ↦ y n) p.2.1 hy
  have hinner : |∑' n, r n * y n| ≤ l2Norm r * ‖y‖ := by
    have hpq : (2 : ℝ≥0∞).toReal.HolderConjugate (2 : ℝ≥0∞).toReal := by
      rw [Real.holderConjugate_iff]
      norm_num
    have hprod : Summable (fun n ↦ r n * y n) := by
      refine (lp.summable_mul hpq (toL2 r hr) y).of_norm_bounded ?_
      intro n
      simp only [norm_mul, toL2]
      exact le_rfl
    calc
      |∑' n, r n * y n| ≤ ∑' n, ‖r n * y n‖ := by
        simpa only [Real.norm_eq_abs] using norm_tsum_le_tsum_norm hprod.norm
      _ = ∑' n, ‖(toL2 r hr) n‖ * ‖y n‖ := by
        congr 1
        funext n
        simp only [norm_mul, toL2]
      _ ≤ ‖toL2 r hr‖ * ‖y‖ := lp.tsum_mul_le_mul_norm' hpq _ _
      _ = l2Norm r * ‖y‖ := by rw [l2Norm_eq_norm_toL2 r hr]
  have hcomm := centralizer_commutator_tsum_bound p.1.2 (fun n ↦ y n) p.2.1 hy
  rw [l2Norm_eq_norm_toL2 (fun n ↦ y n) hy] at hcomm
  rw [hdecomp]
  calc
    |_ + _| ≤ |∑' n, r n * y n| +
        |∑' n, commutatorTerm p.1.2 (fun n ↦ y n) n| := abs_add_le _ _
    _ ≤ l2Norm r * ‖y‖ + 4 * l2Norm p.1.2 * ‖y‖ := add_le_add hinner hcomm
    _ = (l2Norm r + 4 * l2Norm p.1.2) * ‖y‖ := by ring

private abbrev UnitL2 := {y : L2 // ‖y‖ ≤ 1}

private abbrev Features := lp (fun _ : UnitL2 ↦ ℝ) ⊤

private lemma sectionPairing_add (p q : Raw) (y : L2) :
    sectionPairing (p + q) y = sectionPairing p y + sectionPairing q y := by
  rw [sectionPairing, sectionPairing, sectionPairing,
    ← (sectionPairingTerm_summable p y).tsum_add (sectionPairingTerm_summable q y)]
  congr 1
  funext n
  simp only [sectionPairingTerm, Submodule.coe_add, Prod.fst_add, Prod.snd_add,
    Pi.add_apply]
  ring

private lemma sectionPairing_smul (a : ℝ) (p : Raw) (y : L2) :
    sectionPairing (a • p) y = a * sectionPairing p y := by
  rw [sectionPairing, sectionPairing, ← tsum_mul_left]
  congr 1
  funext n
  simp only [sectionPairingTerm, Submodule.coe_smul_of_tower, Prod.smul_fst,
    Prod.smul_snd, Pi.smul_apply, smul_eq_mul]
  ring

private lemma feature_mem (p : Raw) :
    Memℓp (fun y : UnitL2 ↦ sectionPairing p y.1) ⊤ := by
  rw [memℓp_infty_iff]
  let C := l2Norm (p.1.1 - centralizer p.1.2) + 4 * l2Norm p.1.2
  have hC : 0 ≤ C :=
    add_nonneg (l2Norm_nonneg _) (mul_nonneg (by norm_num) (l2Norm_nonneg _))
  refine ⟨C, ?_⟩
  rintro z ⟨y, rfl⟩
  change ‖sectionPairing p y.1‖ ≤ C
  rw [Real.norm_eq_abs]
  calc
    |sectionPairing p y.1| ≤ C * ‖y.1‖ := sectionPairing_bound p y.1
    _ ≤ C * 1 := mul_le_mul_of_nonneg_left y.2 hC
    _ = C := mul_one C

private def featureLinear : Raw →ₗ[ℝ] Features where
  toFun p := ⟨fun y ↦ sectionPairing p y.1, feature_mem p⟩
  map_add' p q := by
    apply Subtype.ext
    funext y
    exact sectionPairing_add p q y.1
  map_smul' a p := by
    apply Subtype.ext
    funext y
    exact sectionPairing_smul a p y.1

private lemma featureLinear_norm_le (p : Raw) :
    ‖featureLinear p‖ ≤
      l2Norm (p.1.1 - centralizer p.1.2) + 4 * l2Norm p.1.2 := by
  let C := l2Norm (p.1.1 - centralizer p.1.2) + 4 * l2Norm p.1.2
  have hC : 0 ≤ C :=
    add_nonneg (l2Norm_nonneg _) (mul_nonneg (by norm_num) (l2Norm_nonneg _))
  apply lp.norm_le_of_forall_le hC
  intro y
  change ‖sectionPairing p y.1‖ ≤ C
  rw [Real.norm_eq_abs]
  calc
    |sectionPairing p y.1| ≤ C * ‖y.1‖ := sectionPairing_bound p y.1
    _ ≤ C * 1 := mul_le_mul_of_nonneg_left y.2 hC
    _ = C := mul_one C

private def modelLinear : Raw →ₗ[ℝ] L2 × Features :=
  secondL2.prod featureLinear

private lemma modelLinear_eq_zero (p : Raw) (hp : modelLinear p = 0) : p = 0 := by
  have hsL2 : secondL2 p = 0 := by
    have h := congrArg Prod.fst hp
    change secondL2 p = 0 at h
    exact h
  have hs : p.1.2 = 0 := by
    funext n
    have hn := congrArg (fun z : L2 ↦ z n) hsL2
    change p.1.2 n = (0 : ℝ) at hn
    exact hn
  have hf : featureLinear p = 0 := by
    have h := congrArg Prod.snd hp
    change featureLinear p = 0 at h
    exact h
  apply Subtype.ext
  apply Prod.ext
  · funext n
    let e : L2 := lp.single 2 n (1 : ℝ)
    have he : ‖e‖ ≤ 1 := by
      rw [lp.norm_single (by norm_num : (0 : ℝ≥0∞) < 2)]
      norm_num
    let u : UnitL2 := ⟨e, he⟩
    have hvalue : sectionPairing p e = 0 := by
      have hu := congrArg (fun z : Features ↦ z u) hf
      change sectionPairing p e = (0 : ℝ) at hu
      exact hu
    have hterm : sectionPairingTerm p e = fun k ↦ p.1.1 k * e k := by
      funext k
      simp only [sectionPairingTerm, hs, Pi.zero_apply, zero_mul, sub_zero]
    have hsum : (∑' k, p.1.1 k * e k) = p.1.1 n := by
      rw [tsum_eq_single n]
      · simp only [e, lp.coeFn_single, Pi.single_eq_same, mul_one]
      · intro k hk
        simp only [e, lp.coeFn_single, Pi.single_eq_of_ne hk, mul_zero]
    rw [sectionPairing, hterm, hsum] at hvalue
    exact hvalue
  · change p.1.2 = 0
    exact hs

private lemma modelLinear_injective : Function.Injective modelLinear := by
  intro p q hpq
  apply sub_eq_zero.mp
  apply modelLinear_eq_zero
  rw [map_sub, hpq, sub_self]

@[reducible] private noncomputable def rawNormedAddCommGroup : NormedAddCommGroup Raw :=
  NormedAddCommGroup.induced Raw (L2 × Features) modelLinear modelLinear_injective

/-- The induced normed additive structure during construction of the canonical carrier. -/
local instance rawNormedAddCommGroupInst : NormedAddCommGroup Raw :=
  rawNormedAddCommGroup

/-- The metric selected from the constructed norm, avoiding the ambient subtype metric. -/
local instance rawMetricSpaceInst : MetricSpace Raw :=
  rawNormedAddCommGroup.toMetricSpace

/-- The uniformity selected from the constructed norm. -/
local instance rawUniformSpaceInst : UniformSpace Raw :=
  rawNormedAddCommGroup.toMetricSpace.toPseudoMetricSpace.toUniformSpace

/-- The topology selected from the constructed norm. -/
local instance rawTopologicalSpaceInst : TopologicalSpace Raw :=
  rawNormedAddCommGroup.toMetricSpace.toPseudoMetricSpace.toUniformSpace.toTopologicalSpace

@[reducible] private noncomputable def rawNormedSpace : NormedSpace ℝ Raw :=
  NormedSpace.induced ℝ Raw (L2 × Features) modelLinear

/-- The induced real normed-space structure during construction of the canonical carrier. -/
local instance rawNormedSpaceInst : NormedSpace ℝ Raw := rawNormedSpace

private lemma raw_norm_eq_model (p : Raw) : ‖p‖ = ‖modelLinear p‖ := rfl

private lemma model_norm_le_quasiNorm (p : Raw) :
    ‖p‖ ≤ 4 * kaltonPeckQuasiNorm p.1 := by
  rw [raw_norm_eq_model, Prod.norm_def]
  apply max_le
  · change ‖secondL2 p‖ ≤ 4 * kaltonPeckQuasiNorm p.1
    rw [secondL2_norm]
    change l2Norm p.1.2 ≤
      4 * (l2Norm (p.1.1 - centralizer p.1.2) + l2Norm p.1.2)
    nlinarith [l2Norm_nonneg p.1.2, l2Norm_nonneg (p.1.1 - centralizer p.1.2)]
  · apply (featureLinear_norm_le p).trans
    change l2Norm (p.1.1 - centralizer p.1.2) + 4 * l2Norm p.1.2 ≤
      4 * (l2Norm (p.1.1 - centralizer p.1.2) + l2Norm p.1.2)
    nlinarith [l2Norm_nonneg p.1.2, l2Norm_nonneg (p.1.1 - centralizer p.1.2)]

private lemma second_norm_le_model_norm (p : Raw) : l2Norm p.1.2 ≤ ‖p‖ := by
  rw [raw_norm_eq_model, ← secondL2_norm p]
  exact norm_fst_le (modelLinear p)

private lemma feature_norm_le_model_norm (p : Raw) : ‖featureLinear p‖ ≤ ‖p‖ := by
  rw [raw_norm_eq_model]
  exact norm_snd_le (modelLinear p)

private lemma quasiNorm_le_model_norm (p : Raw) :
    kaltonPeckQuasiNorm p.1 ≤ 6 * ‖p‖ := by
  let r : ℕ → ℝ := p.1.1 - centralizer p.1.2
  have hr : IsSquareSummable r := p.2.2
  by_cases hr0 : r = 0
  · change l2Norm r + l2Norm p.1.2 ≤ 6 * ‖p‖
    rw [hr0, l2Norm_zero, zero_add]
    nlinarith [second_norm_le_model_norm p, norm_nonneg p]
  have hrpos : 0 < l2Norm r := l2Norm_pos r hr hr0
  let y : L2 := (l2Norm r)⁻¹ • toL2 r hr
  have hy_norm : ‖y‖ = 1 := by
    dsimp only [y]
    rw [norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos hrpos,
      ← l2Norm_eq_norm_toL2 r hr, inv_mul_cancel₀ hrpos.ne']
  let u : UnitL2 := ⟨y, hy_norm.le⟩
  have hfeature : |sectionPairing p y| ≤ ‖featureLinear p‖ := by
    have h := lp.norm_apply_le_norm ENNReal.top_ne_zero (featureLinear p) u
    change ‖sectionPairing p y‖ ≤ ‖featureLinear p‖ at h
    simpa only [Real.norm_eq_abs] using h
  have hinner : (∑' n, r n * y n) = l2Norm r := by
    have hfun : (fun n ↦ r n * y n) = fun n ↦ (l2Norm r)⁻¹ * r n ^ 2 := by
      funext n
      change r n * ((l2Norm r)⁻¹ * r n) = (l2Norm r)⁻¹ * r n ^ 2
      ring
    rw [hfun, tsum_mul_left, tsum_sq_eq_l2Norm_sq]
    field_simp
  have hy : IsSquareSummable (fun n ↦ y n) := by
    rw [squareSummable_iff_memL2]
    exact y.2
  have hcomm := centralizer_commutator_tsum_bound p.1.2
    (fun n ↦ y n) p.2.1 hy
  have hto : toL2 (fun n ↦ y n) hy = y := by
    apply Subtype.ext
    rfl
  rw [l2Norm_eq_norm_toL2 (fun n ↦ y n) hy, hto, hy_norm, mul_one] at hcomm
  have hdecomp := sectionPairing_decomp p y
  change sectionPairing p y =
    (∑' n, r n * y n) + ∑' n, commutatorTerm p.1.2 (fun n ↦ y n) n at hdecomp
  rw [hinner] at hdecomp
  have hres : l2Norm r ≤ |sectionPairing p y| +
      |∑' n, commutatorTerm p.1.2 (fun n ↦ y n) n| := by
    calc
      l2Norm r = |l2Norm r| := (abs_of_pos hrpos).symm
      _ = |sectionPairing p y -
          ∑' n, commutatorTerm p.1.2 (fun n ↦ y n) n| := by
        rw [hdecomp]
        ring_nf
      _ ≤ |sectionPairing p y| +
          |∑' n, commutatorTerm p.1.2 (fun n ↦ y n) n| := abs_sub _ _
  change l2Norm r + l2Norm p.1.2 ≤ 6 * ‖p‖
  nlinarith [hres, hfeature, hcomm, second_norm_le_model_norm p,
    feature_norm_le_model_norm p]

private def secondLinear : Raw →ₗ[ℝ] L2 where
  toFun p := toL2 p.1.2 p.2.1
  map_add' p q := by
    apply Subtype.ext
    rfl
  map_smul' a p := by
    apply Subtype.ext
    rfl

private def secondCLM : Raw →L[ℝ] L2 :=
  secondLinear.mkContinuous 1 fun p ↦ by
    rw [one_mul]
    change ‖toL2 p.1.2 p.2.1‖ ≤ ‖p‖
    rw [← l2Norm_eq_norm_toL2 p.1.2 p.2.1]
    exact second_norm_le_model_norm p

private lemma l2Norm_coe (x : L2) : l2Norm (fun n ↦ x n) = ‖x‖ := by
  have hx : IsSquareSummable (fun n ↦ x n) := by
    rw [squareSummable_iff_memL2]
    exact x.2
  rw [l2Norm_eq_norm_toL2 (fun n ↦ x n) hx]
  congr 1

private def canonicalSection (x : L2) : Raw := by
  let seq : ℕ → ℝ := fun n ↦ x n
  have hx : IsSquareSummable seq := by
    rw [squareSummable_iff_memL2]
    exact x.2
  refine ⟨(centralizer seq, seq), hx, ?_⟩
  simpa only [sub_self] using squareSummable_zero

private lemma secondCLM_section (x : L2) : secondCLM (canonicalSection x) = x := by
  apply Subtype.ext
  rfl

private lemma canonicalSection_norm_le (x : L2) :
    ‖canonicalSection x‖ ≤ 4 * ‖x‖ := by
  apply (model_norm_le_quasiNorm (canonicalSection x)).trans_eq
  congr 1
  change kaltonPeckQuasiNorm
      (centralizer (fun n ↦ x n), fun n ↦ x n) = ‖x‖
  rw [kaltonPeckQuasiNorm]
  simp only [sub_self, l2Norm_zero, zero_add, l2Norm_coe]

private lemma ker_second_zero (z : secondCLM.ker) : z.1.1.2 = 0 := by
  funext n
  have h := congrArg (fun y : L2 ↦ y n) z.2
  change z.1.1.2 n = (0 : ℝ) at h
  exact h

private lemma ker_first_squareSummable (z : secondCLM.ker) :
    IsSquareSummable z.1.1.1 := by
  have hz := z.1.2.2
  have hs := ker_second_zero z
  convert hz using 1
  funext n
  rw [hs, centralizer_zero]
  simp only [sub_zero]

private def kernelFirst : secondCLM.ker →ₗ[ℝ] L2 where
  toFun z := toL2 z.1.1.1 (ker_first_squareSummable z)
  map_add' z w := by
    apply Subtype.ext
    rfl
  map_smul' a z := by
    apply Subtype.ext
    rfl

private lemma kernelFirst_injective : Function.Injective kernelFirst := by
  intro z w hzw
  apply Subtype.ext
  apply Subtype.ext
  apply Prod.ext
  · funext n
    have h := congrArg (fun y : L2 ↦ y n) hzw
    exact h
  · rw [ker_second_zero z, ker_second_zero w]

private def kernelPair (x : L2) : secondCLM.ker := by
  let seq : ℕ → ℝ := fun n ↦ x n
  have hx : IsSquareSummable seq := by
    rw [squareSummable_iff_memL2]
    exact x.2
  let p : Raw := ⟨(seq, 0), squareSummable_zero, by
    simpa only [centralizer_zero, sub_zero] using hx⟩
  refine ⟨p, ?_⟩
  apply Subtype.ext
  rfl

private lemma kernelFirst_surjective : Function.Surjective kernelFirst := by
  intro x
  refine ⟨kernelPair x, ?_⟩
  apply Subtype.ext
  rfl

private def kernelEquiv : secondCLM.ker ≃ₗ[ℝ] L2 :=
  LinearEquiv.ofBijective kernelFirst ⟨kernelFirst_injective, kernelFirst_surjective⟩

private lemma kernelEquiv_symm_apply (x : L2) : kernelEquiv.symm x = kernelPair x := by
  apply kernelEquiv.injective
  rw [kernelEquiv.apply_symm_apply]
  symm
  apply Subtype.ext
  rfl

private lemma kernel_quasiNorm_eq (z : secondCLM.ker) :
    kaltonPeckQuasiNorm z.1.1 = ‖kernelEquiv z‖ := by
  rw [kaltonPeckQuasiNorm]
  have hs := ker_second_zero z
  rw [hs, centralizer_zero]
  simp only [sub_zero, l2Norm_zero, add_zero, kernelEquiv,
    LinearEquiv.ofBijective_apply, kernelFirst]
  rw [l2Norm_eq_norm_toL2 z.1.1.1 (ker_first_squareSummable z)]
  change ‖toL2 z.1.1.1 (ker_first_squareSummable z)‖ =
    ‖toL2 z.1.1.1 (ker_first_squareSummable z)‖
  rfl

private lemma kernelEquiv_norm_le (z : secondCLM.ker) :
    ‖kernelEquiv z‖ ≤ 6 * ‖z‖ := by
  rw [← kernel_quasiNorm_eq]
  exact quasiNorm_le_model_norm z.1

private lemma kernelEquiv_symm_norm_le (x : L2) :
    ‖kernelEquiv.symm x‖ ≤ 4 * ‖x‖ := by
  rw [kernelEquiv_symm_apply]
  change ‖(kernelPair x).1‖ ≤ 4 * ‖x‖
  have hq := model_norm_le_quasiNorm (kernelPair x).1
  apply hq.trans_eq
  change 4 * kaltonPeckQuasiNorm ((fun n ↦ x n), 0) = 4 * ‖x‖
  congr 1
  rw [kaltonPeckQuasiNorm, centralizer_zero]
  simp only [sub_zero, l2Norm_zero, add_zero, l2Norm_coe]

private lemma complete_of_linear_equiv_bounds
    {A B : Type*} [NormedAddCommGroup A] [NormedSpace ℝ A]
    [NormedAddCommGroup B] [NormedSpace ℝ B] [CompleteSpace B]
    (e : A ≃ₗ[ℝ] B) (C D : ℝ)
    (he : ∀ x, ‖e x‖ ≤ C * ‖x‖) (he' : ∀ y, ‖e.symm y‖ ≤ D * ‖y‖) :
    CompleteSpace A := by
  let E : A ≃L[ℝ] B := e.toContinuousLinearEquivOfBounds C D he he'
  apply Metric.complete_of_cauchySeq_tendsto
  intro u hu
  have hEu : CauchySeq (fun n ↦ E (u n)) :=
    E.toContinuousLinearMap.lipschitzWith.cauchySeq_comp hu
  obtain ⟨y, hy⟩ := cauchySeq_tendsto_of_complete hEu
  refine ⟨E.symm y, ?_⟩
  convert (E.symm.continuous.tendsto y).comp hy using 1
  simp [Function.comp_def]

private theorem kernelCompleteSpace :
    CompleteSpace secondCLM.ker :=
  complete_of_linear_equiv_bounds kernelEquiv 6 4 kernelEquiv_norm_le
    kernelEquiv_symm_norm_le

/-- Completeness of the kernel used by the split-extension completeness argument. -/
local instance kernelCompleteSpaceInst : CompleteSpace secondCLM.ker :=
  kernelCompleteSpace

private lemma complete_of_section_and_complete_ker
    {A B : Type*} [NormedAddCommGroup A] [NormedSpace ℝ A]
    [NormedAddCommGroup B] [NormedSpace ℝ B] [CompleteSpace B]
    (f : A →L[ℝ] B) (s : B → A) (C : ℝ)
    (hs_right : ∀ x, f (s x) = x)
    (hs_norm : ∀ x, ‖s x‖ ≤ C * ‖x‖)
    [CompleteSpace f.ker] : CompleteSpace A := by
  apply Metric.complete_of_cauchySeq_tendsto
  intro u hu
  have hfu : CauchySeq (fun n ↦ f (u n)) :=
    f.lipschitzWith.cauchySeq_comp hu
  obtain ⟨x, hx⟩ := cauchySeq_tendsto_of_complete hfu
  let d : ℕ → B := fun n ↦ x - f (u n)
  have hd : Tendsto d atTop (nhds 0) := by
    have hconst : Tendsto (fun _ : ℕ ↦ x) atTop (nhds x) := tendsto_const_nhds
    simpa [d] using hconst.sub hx
  let c : ℕ → A := fun n ↦ s (d n)
  have hc : Tendsto c atTop (nhds 0) := by
    apply squeeze_zero_norm (fun n ↦ hs_norm (d n))
    have hnorm : Tendsto (fun n ↦ ‖d n‖) atTop (nhds 0) :=
      tendsto_norm_zero.comp hd
    simpa using tendsto_const_nhds.mul hnorm
  let v : ℕ → A := fun n ↦ u n + c n
  have hv : CauchySeq v := by
    have : v = u + c := rfl
    rw [this]
    exact hu.add hc.cauchySeq
  have hfv (n : ℕ) : f (v n) = x := by
    simp only [v, c, map_add, hs_right, d]
    abel
  let k : ℕ → f.ker := fun n ↦ ⟨v n - v 0, by simp [hfv]⟩
  have hk : CauchySeq k := by
    rw [Metric.cauchySeq_iff]
    intro ε hε
    obtain ⟨N, hN⟩ := (Metric.cauchySeq_iff.mp hv) ε hε
    refine ⟨N, fun m hm n hn ↦ ?_⟩
    simpa [k, dist_eq_norm] using hN m hm n hn
  obtain ⟨z, hz⟩ := cauchySeq_tendsto_of_complete hk
  refine ⟨v 0 + z.1, ?_⟩
  have hvlim : Tendsto v atTop (nhds (v 0 + z.1)) := by
    have hsub : Tendsto (fun n ↦ v n - v 0) atTop (nhds z.1) :=
      (continuous_subtype_val.tendsto z).comp hz
    convert tendsto_const_nhds.add hsub using 1
    all_goals simp [sub_eq_add_neg]
  have huv : Tendsto (fun n ↦ v n - c n) atTop (nhds (v 0 + z.1 - 0)) :=
    hvlim.sub hc
  simpa [v] using huv

private theorem rawCompleteSpace : CompleteSpace Raw := by
  exact complete_of_section_and_complete_ker secondCLM canonicalSection 4
    secondCLM_section canonicalSection_norm_le

/-- Summability and the quantitative bound for the canonical coordinate pairing.
Implementation data shared by the canonical Banach model and its symplectic form. -/
theorem canonicalPairingData :
    (∀ (p : (ℕ → ℝ) × (ℕ → ℝ)) (y : ℕ → ℝ), IsAdmissiblePair p →
      IsSquareSummable y →
        Summable (fun n ↦ p.1 n * y n - p.2 n * centralizer y n)) ∧
    ∀ (p : (ℕ → ℝ) × (ℕ → ℝ)) (y : ℕ → ℝ), IsAdmissiblePair p →
      IsSquareSummable y →
        |∑' n, (p.1 n * y n - p.2 n * centralizer y n)| ≤
          (l2Norm (p.1 - centralizer p.2) + 4 * l2Norm p.2) * l2Norm y := by
  constructor
  · intro p y hp hy
    let rp : Raw := ⟨p, hp⟩
    let yl2 : L2 := toL2 y hy
    have h := sectionPairingTerm_summable rp yl2
    change Summable (fun n ↦ p.1 n * y n - p.2 n * centralizer y n) at h
    exact h
  · intro p y hp hy
    let rp : Raw := ⟨p, hp⟩
    let yl2 : L2 := toL2 y hy
    have h := sectionPairing_bound rp yl2
    change |∑' n, (p.1 n * y n - p.2 n * centralizer y n)| ≤
      (l2Norm (p.1 - centralizer p.2) + 4 * l2Norm p.2) * ‖toL2 y hy‖ at h
    rw [← l2Norm_eq_norm_toL2 y hy] at h
    exact h

private def rawPresentation : RealKaltonPeckPresentation Raw := by
  let coords : Raw →ₗ[ℝ] (ℕ → ℝ) × (ℕ → ℝ) :=
    { toFun := fun p ↦ p.1
      map_add' := by intro p q; rfl
      map_smul' := by intro a p; rfl }
  refine
    { coordinates := coords
      coordinates_injective := ?_
      coordinates_mem := ?_
      coordinates_surjective := ?_
      norm_equivalent := ?_ }
  · intro p q hpq
    exact Subtype.ext hpq
  · intro p
    exact p.2
  · intro p hp
    exact ⟨⟨p, hp⟩, rfl⟩
  · refine ⟨1 / 6, 4, by norm_num, by norm_num, ?_⟩
    intro p
    have hlower := quasiNorm_le_model_norm p
    have hupper := model_norm_le_quasiNorm p
    have hqnonneg : 0 ≤ kaltonPeckQuasiNorm p.1 := by
      exact add_nonneg (l2Norm_nonneg _) (l2Norm_nonneg _)
    change (1 / 6 : ℝ) * kaltonPeckQuasiNorm p.1 ≤ ‖p‖ ∧
      ‖p‖ ≤ 4 * kaltonPeckQuasiNorm p.1
    constructor
    · nlinarith
    · exact hupper

/-- The additive normed-space structure on the canonical model.
Blueprint label: `thm:kp-canonical-banach`. -/
instance instNormedAddCommGroupCanonicalRealKaltonPeck :
    NormedAddCommGroup CanonicalRealKaltonPeck := by
  exact rawNormedAddCommGroup

/-- The real normed-space structure on the canonical model.
Blueprint label: `thm:kp-canonical-banach`. -/
instance instNormedSpaceCanonicalRealKaltonPeck :
    NormedSpace ℝ CanonicalRealKaltonPeck := by
  exact rawNormedSpace

/-- Completeness of the canonical model obtained from the pinned renormability theorem.
Blueprint label: `thm:kp-canonical-banach`. -/
instance instCompleteSpaceCanonicalRealKaltonPeck :
    CompleteSpace CanonicalRealKaltonPeck := by
  exact rawCompleteSpace

/-- The coordinate presentation of the fixed canonical model.
Blueprint label: `thm:kp-canonical-banach`. -/
def canonicalRealKaltonPeckPresentation :
    RealKaltonPeckPresentation CanonicalRealKaltonPeck := by
  exact rawPresentation

/-- The real Hilbert sequence space in the canonical Kalton--Peck exact sequence.
Blueprint support for `thm:kp-canonical-banach`; audit ID `EXT-CGP-UPPER-SEMI-PRIMARY`. -/
abbrev CanonicalL2 := lp (fun _ : ℕ ↦ ℝ) 2

/-- The canonical quotient `Z₂ → ℓ₂`, given by the second coordinate.
Blueprint support for `thm:kp-canonical-banach`; audit ID `EXT-CGP-UPPER-SEMI-PRIMARY`. -/
def canonicalL2Quotient : CanonicalRealKaltonPeck →L[ℝ] CanonicalL2 := by
  exact secondCLM

/-- The canonical quotient is evaluation of the second Kalton--Peck coordinate.
Blueprint support for `thm:kp-canonical-banach`; audit ID `EXT-CGP-UPPER-SEMI-PRIMARY`. -/
theorem canonicalL2Quotient_apply (z : CanonicalRealKaltonPeck) (n : ℕ) :
    canonicalL2Quotient z n =
      (canonicalRealKaltonPeckPresentation.coordinates z).2 n := by
  rfl

/-- The canonical second-coordinate quotient is onto.
Blueprint support for `thm:kp-canonical-banach`; audit ID `EXT-CGP-UPPER-SEMI-PRIMARY`. -/
theorem canonicalL2Quotient_surjective :
    Function.Surjective canonicalL2Quotient := by
  intro x
  exact ⟨canonicalSection x, secondCLM_section x⟩

/-- The Hilbert space in the canonical exact sequence is infinite-dimensional.
Blueprint support for `thm:kp-canonical-banach`; audit ID `EXT-CGP-UPPER-SEMI-PRIMARY`. -/
theorem canonicalL2_not_finiteDimensional :
    ¬ FiniteDimensional ℝ CanonicalL2 := by
  intro h
  let : FiniteDimensional ℝ CanonicalL2 := h
  have hlinear :
      LinearIndependent ℝ
        (fun i : ℕ ↦ (lp.single 2 i (1 : ℝ) : CanonicalL2)) := by
    rw [linearIndependent_iff']
    intro s g hg i hi
    have hgi := congrArg (fun x : CanonicalL2 ↦ x i) hg
    simp only [lp.coeFn_sum, Finset.sum_apply, lp.coeFn_smul, Pi.smul_apply,
      lp.single_apply, lp.coeFn_zero, Pi.zero_apply] at hgi
    rw [Finset.sum_eq_single i] at hgi
    · simpa using hgi
    · intro j hj hji
      simp [hji]
    · exact fun hni ↦ (hni hi).elim
  have hcard := hlinear.lt_aleph0_of_finiteDimensional
  rw [Cardinal.mk_nat] at hcard
  exact (lt_irrefl Cardinal.aleph0) hcard

/-- The canonical Banach model has the exact admissible range and dense finite-coordinate vectors.
Blueprint label: `thm:kp-canonical-banach`; audit IDs `EXT-KP-CANONICAL-BANACH` and
`INF-KP-CANONICAL-MODEL`. -/
theorem canonicalKaltonPeckBanach :
    IsAdmissiblePair 0 ∧
      (∀ p q, IsAdmissiblePair p → IsAdmissiblePair q → IsAdmissiblePair (p + q)) ∧
      (∀ (a : ℝ) p, IsAdmissiblePair p → IsAdmissiblePair (a • p)) ∧
      Dense {z : CanonicalRealKaltonPeck |
        IsFiniteCoordinatePair (canonicalRealKaltonPeckPresentation.coordinates z)} := by
  refine ⟨admissible_zero, ?_, ?_, ?_⟩
  · intro p q hp hq
    exact admissible_add hp hq
  · intro a p hp
    exact admissible_smul a hp
  · let D : Submodule ℝ Raw :=
      { carrier := {p | IsFiniteCoordinatePair p.1}
        zero_mem' := by
          change Set.Finite {n | (0 : ℝ) ≠ 0} ∧ Set.Finite {n | (0 : ℝ) ≠ 0}
          exact ⟨by simp, by simp⟩
        add_mem' := by
          intro p q hp hq
          change Set.Finite {n | p.1.1 n + q.1.1 n ≠ 0} ∧
            Set.Finite {n | p.1.2 n + q.1.2 n ≠ 0}
          change Set.Finite {n | p.1.1 n ≠ 0} ∧ Set.Finite {n | p.1.2 n ≠ 0} at hp
          change Set.Finite {n | q.1.1 n ≠ 0} ∧ Set.Finite {n | q.1.2 n ≠ 0} at hq
          constructor
          · exact (hp.1.union hq.1).subset fun n hn ↦ by
              simp only [Set.mem_union, Set.mem_ofPred_eq]
              by_cases hp0 : p.1.1 n = 0
              · right
                exact fun hq0 ↦ hn (by rw [hp0, hq0, add_zero])
              · exact Or.inl hp0
          · exact (hp.2.union hq.2).subset fun n hn ↦ by
              simp only [Set.mem_union, Set.mem_ofPred_eq]
              by_cases hp0 : p.1.2 n = 0
              · right
                exact fun hq0 ↦ hn (by rw [hp0, hq0, add_zero])
              · exact Or.inl hp0
        smul_mem' := by
          intro a p hp
          change Set.Finite {n | a * p.1.1 n ≠ 0} ∧ Set.Finite {n | a * p.1.2 n ≠ 0}
          change Set.Finite {n | p.1.1 n ≠ 0} ∧ Set.Finite {n | p.1.2 n ≠ 0} at hp
          constructor
          · exact hp.1.subset fun n hn ↦ by
              simp only [Set.mem_ofPred_eq]
              exact fun h ↦ hn (by rw [h, mul_zero])
          · exact hp.2.subset fun n hn ↦ by
              simp only [Set.mem_ofPred_eq]
              exact fun h ↦ hn (by rw [h, mul_zero]) }
    have hL2 : Dense {x : L2 | Set.Finite {n | x n ≠ 0}} := by
      rw [dense_iff_closure_eq]
      apply Set.eq_univ_of_forall
      intro x
      refine mem_closure_of_tendsto (lp.hasSum_single ENNReal.ofNat_ne_top x) ?_
      apply Eventually.of_forall
      intro s
      change Set.Finite {n | (∑ i ∈ s, lp.single 2 i (x i)) n ≠ 0}
      exact s.finite_toSet.subset fun n hn ↦ by
        simp only [Finset.mem_coe]
        by_contra hns
        have hz : (∑ i ∈ s, lp.single 2 i (x i)) n = 0 := by
          simp only [lp.coeFn_sum, Finset.sum_apply, lp.coeFn_single]
          apply Finset.sum_eq_zero
          intro i hi
          rw [Pi.single_eq_of_ne]
          exact fun hni => hns (hni ▸ hi)
        exact hn hz
    have hker : secondCLM.ker ≤ D.topologicalClosure := by
      intro z hz
      let zz : secondCLM.ker := ⟨z, hz⟩
      change z ∈ (D.topologicalClosure : Set Raw)
      rw [Submodule.topologicalClosure_coe]
      rw [Metric.mem_closure_iff]
      intro ε hε
      obtain ⟨x, hxfin, hx⟩ :=
        hL2.exists_dist_lt (kernelEquiv zz) (div_pos hε (by norm_num : (0 : ℝ) < 4))
      let w : secondCLM.ker := kernelEquiv.symm x
      refine ⟨w.1, ?_, ?_⟩
      · change IsFiniteCoordinatePair w.1.1
        rw [show w = kernelPair x from kernelEquiv_symm_apply x]
        change Set.Finite {n | x n ≠ 0} ∧ Set.Finite {n | (0 : ℝ) ≠ 0}
        exact ⟨hxfin, by simp⟩
      · rw [dist_eq_norm]
        change ‖zz - w‖ < ε
        have hbound := kernelEquiv_symm_norm_le (kernelEquiv zz - x)
        change ‖kernelEquiv.symm (kernelEquiv zz - x)‖ ≤
          4 * ‖kernelEquiv zz - x‖ at hbound
        have heq : kernelEquiv.symm (kernelEquiv zz - x) = zz - w := by
          rw [map_sub, LinearEquiv.symm_apply_apply]
        rw [heq] at hbound
        calc
          ‖zz - w‖ ≤ 4 * ‖kernelEquiv zz - x‖ := hbound
          _ = 4 * dist (kernelEquiv zz) x := by rw [dist_eq_norm]
          _ < 4 * (ε / 4) := mul_lt_mul_of_pos_left hx (by norm_num)
          _ = ε := by ring
    have hsection (x : L2) (hx : Set.Finite {n | x n ≠ 0}) :
        canonicalSection x ∈ D := by
      change IsFiniteCoordinatePair (canonicalSection x).1
      change Set.Finite {n | centralizer (fun n ↦ x n) n ≠ 0} ∧
        Set.Finite {n | x n ≠ 0}
      refine ⟨hx.subset ?_, hx⟩
      intro n hn
      simp only [Set.mem_ofPred_eq] at hn ⊢
      exact fun hzero ↦ hn (by simp [centralizer, hzero])
    change Dense (D : Set Raw)
    rw [dense_iff_closure_eq]
    apply Set.eq_univ_of_forall
    intro p
    rw [Metric.mem_closure_iff]
    intro ε hε
    obtain ⟨x, hxfin, hx⟩ :=
      hL2.exists_dist_lt (secondCLM p) (div_pos hε (by norm_num : (0 : ℝ) < 8))
    let d : Raw := canonicalSection x
    let c : Raw := canonicalSection (secondCLM (p - d))
    let k : Raw := p - d - c
    have hdD : d ∈ D := hsection x hxfin
    have hkker : k ∈ secondCLM.ker := by
      change secondCLM k = 0
      simp only [k, c, d, map_sub, secondCLM_section, sub_self]
    have hkcl := hker hkker
    change k ∈ (D.topologicalClosure : Set Raw) at hkcl
    rw [Submodule.topologicalClosure_coe] at hkcl
    obtain ⟨e, heD, he⟩ :=
      (Metric.mem_closure_iff.mp hkcl) (ε / 2) (half_pos hε)
    refine ⟨d + e, D.add_mem hdD heD, ?_⟩
    rw [dist_eq_norm]
    have heq : p - (d + e) = c + (k - e) := by
      dsimp only [k]
      abel
    rw [heq]
    have hc : ‖c‖ < ε / 2 := by
      calc
        ‖c‖ ≤ 4 * ‖secondCLM (p - d)‖ := canonicalSection_norm_le _
        _ = 4 * dist (secondCLM p) x := by
          rw [map_sub, show secondCLM d = x from secondCLM_section x, dist_eq_norm]
        _ < 4 * (ε / 8) := mul_lt_mul_of_pos_left hx (by norm_num)
        _ = ε / 2 := by ring
    have hke : ‖k - e‖ < ε / 2 := by
      simpa only [dist_eq_norm] using he
    calc
      ‖c + (k - e)‖ ≤ ‖c‖ + ‖k - e‖ := norm_add_le _ _
      _ < ε / 2 + ε / 2 := add_lt_add hc hke
      _ = ε := by ring

/-- A chosen pair of comparison constants for a Kalton--Peck presentation.
Support definition for blueprint label `thm:presentation-equivalence`. -/
def AreComparisonConstants {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    (hX : RealKaltonPeckPresentation X) (c C : ℝ) : Prop := by
  exact 0 < c ∧ 0 < C ∧ ∀ z,
    c * kaltonPeckQuasiNorm (hX.coordinates z) ≤ ‖z‖ ∧
      ‖z‖ ≤ C * kaltonPeckQuasiNorm (hX.coordinates z)

private theorem norm_le_mul_of_coordinate_match
    {X Y : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    (hX : RealKaltonPeckPresentation X) (hY : RealKaltonPeckPresentation Y)
    {c C : ℝ} (hc : 0 < c) (hC : 0 ≤ C)
    (hlower : ∀ x, c * kaltonPeckQuasiNorm (hX.coordinates x) ≤ ‖x‖)
    (hupper : ∀ y, ‖y‖ ≤ C * kaltonPeckQuasiNorm (hY.coordinates y))
    (x : X) (y : Y) (hcoord : hY.coordinates y = hX.coordinates x) :
    ‖y‖ ≤ (C / c) * ‖x‖ := by
  have hq : kaltonPeckQuasiNorm (hX.coordinates x) ≤ ‖x‖ / c :=
    (le_div_iff₀ hc).2 (by simpa [mul_comm] using hlower x)
  calc
    ‖y‖ ≤ C * kaltonPeckQuasiNorm (hY.coordinates y) := hupper y
    _ = C * kaltonPeckQuasiNorm (hX.coordinates x) := by rw [hcoord]
    _ ≤ C * (‖x‖ / c) := mul_le_mul_of_nonneg_left hq hC
    _ = (C / c) * ‖x‖ := by ring

/-- The coordinate-matching bounded linear equivalence between two presented models.
Blueprint label: `thm:presentation-equivalence`; audit ID
`INF-KP-COORDINATE-EQUIVALENCE`. -/
def presentationEquiv {X Y : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    [CompleteSpace X] [NormedAddCommGroup Y] [NormedSpace ℝ Y] [CompleteSpace Y]
    (hX : RealKaltonPeckPresentation X) (hY : RealKaltonPeckPresentation Y) :
    X ≃L[ℝ] Y := by
  let hCompleteX : CompleteSpace X := inferInstance
  let hCompleteY : CompleteSpace Y := inferInstance
  let f : X → Y := fun x ↦ Classical.choose
    (hY.coordinates_surjective (hX.coordinates x) (hX.coordinates_mem x))
  have hf_coordinates (x : X) : hY.coordinates (f x) = hX.coordinates x :=
    Classical.choose_spec
      (hY.coordinates_surjective (hX.coordinates x) (hX.coordinates_mem x))
  let fLinear : X →ₗ[ℝ] Y :=
    { toFun := f
      map_add' := by
        intro x y
        apply hY.coordinates_injective
        rw [map_add, hf_coordinates, hf_coordinates, hf_coordinates, map_add]
      map_smul' := by
        intro a x
        apply hY.coordinates_injective
        rw [map_smul, hf_coordinates, hf_coordinates, map_smul]
        rfl }
  have hfLinear_coordinates (x : X) :
      hY.coordinates (fLinear x) = hX.coordinates x := by
    exact hf_coordinates x
  have hfLinear_injective : Function.Injective fLinear := by
    intro x y hxy
    apply hX.coordinates_injective
    rw [← hfLinear_coordinates x, ← hfLinear_coordinates y, hxy]
  have hfLinear_surjective : Function.Surjective fLinear := by
    intro y
    obtain ⟨x, hx⟩ :=
      hX.coordinates_surjective (hY.coordinates y) (hY.coordinates_mem y)
    refine ⟨x, ?_⟩
    apply hY.coordinates_injective
    rw [hfLinear_coordinates, hx]
  let e : X ≃ₗ[ℝ] Y :=
    LinearEquiv.ofBijective fLinear ⟨hfLinear_injective, hfLinear_surjective⟩
  have he_coordinates (x : X) : hY.coordinates (e x) = hX.coordinates x := by
    exact hfLinear_coordinates x
  let cX : ℝ := Classical.choose hX.norm_equivalent
  let CX : ℝ := Classical.choose (Classical.choose_spec hX.norm_equivalent)
  have hX_data : 0 < cX ∧ 0 < CX ∧ ∀ x,
      cX * kaltonPeckQuasiNorm (hX.coordinates x) ≤ ‖x‖ ∧
        ‖x‖ ≤ CX * kaltonPeckQuasiNorm (hX.coordinates x) :=
    Classical.choose_spec (Classical.choose_spec hX.norm_equivalent)
  let cY : ℝ := Classical.choose hY.norm_equivalent
  let CY : ℝ := Classical.choose (Classical.choose_spec hY.norm_equivalent)
  have hY_data : 0 < cY ∧ 0 < CY ∧ ∀ y,
      cY * kaltonPeckQuasiNorm (hY.coordinates y) ≤ ‖y‖ ∧
        ‖y‖ ≤ CY * kaltonPeckQuasiNorm (hY.coordinates y) :=
    Classical.choose_spec (Classical.choose_spec hY.norm_equivalent)
  refine e.toContinuousLinearEquivOfBounds (CY / cX) (CX / cY) ?_ ?_
  · intro x
    exact norm_le_mul_of_coordinate_match hX hY hX_data.1 hY_data.2.1.le
      (fun z => (hX_data.2.2 z).1) (fun z => (hY_data.2.2 z).2) x (e x)
      (he_coordinates x)
  · intro y
    have he_symm_coordinates : hX.coordinates (e.symm y) = hY.coordinates y := by
      symm
      simpa using he_coordinates (e.symm y)
    exact norm_le_mul_of_coordinate_match hY hX hY_data.1 hX_data.2.1.le
      (fun z => (hY_data.2.2 z).1) (fun z => (hX_data.2.2 z).2) y (e.symm y)
      he_symm_coordinates

/-- Coordinate identity, algebraic uniqueness, and the two explicit presentation bounds.
Blueprint label: `thm:presentation-equivalence`; audit IDs
`INF-KP-COORDINATE-EQUIVALENCE` and `COV-LINEAR-EQUIV-OF-BOUNDS`. -/
theorem presentationEquiv_spec {X Y : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    [CompleteSpace X] [NormedAddCommGroup Y] [NormedSpace ℝ Y] [CompleteSpace Y]
    (hX : RealKaltonPeckPresentation X) (hY : RealKaltonPeckPresentation Y) :
    (∀ x, hY.coordinates (presentationEquiv hX hY x) = hX.coordinates x) ∧
      (∀ e : X ≃ₗ[ℝ] Y, (∀ x, hY.coordinates (e x) = hX.coordinates x) →
        e = (presentationEquiv hX hY).toLinearEquiv) ∧
      ∀ cX CX cY CY,
        AreComparisonConstants hX cX CX → AreComparisonConstants hY cY CY →
          (∀ x, ‖presentationEquiv hX hY x‖ ≤ (CY / cX) * ‖x‖) ∧
            ∀ y, ‖(presentationEquiv hX hY).symm y‖ ≤ (CX / cY) * ‖y‖ := by
  have hcoordinates (x : X) :
      hY.coordinates (presentationEquiv hX hY x) = hX.coordinates x := by
    simp only [presentationEquiv, LinearEquiv.toContinuousLinearEquivOfBounds,
      LinearEquiv.ofBijective, ContinuousLinearEquiv.coe_mk, LinearEquiv.trans_apply,
      LinearEquiv.ofTop_apply, LinearEquiv.ofInjective_apply, LinearMap.coe_mk, AddHom.coe_mk]
    exact Classical.choose_spec
      (hY.coordinates_surjective (hX.coordinates x) (hX.coordinates_mem x))
  refine ⟨hcoordinates, ?_, ?_⟩
  · intro e he
    apply LinearEquiv.ext
    intro x
    apply hY.coordinates_injective
    rw [he x]
    exact (hcoordinates x).symm
  · intro cX CX cY CY hXconstants hYconstants
    change 0 < cX ∧ 0 < CX ∧ ∀ x,
      cX * kaltonPeckQuasiNorm (hX.coordinates x) ≤ ‖x‖ ∧
        ‖x‖ ≤ CX * kaltonPeckQuasiNorm (hX.coordinates x) at hXconstants
    change 0 < cY ∧ 0 < CY ∧ ∀ y,
      cY * kaltonPeckQuasiNorm (hY.coordinates y) ≤ ‖y‖ ∧
        ‖y‖ ≤ CY * kaltonPeckQuasiNorm (hY.coordinates y) at hYconstants
    constructor
    · intro x
      have hq : kaltonPeckQuasiNorm (hX.coordinates x) ≤ ‖x‖ / cX :=
        (le_div_iff₀ hXconstants.1).2
          (by simpa [mul_comm] using (hXconstants.2.2 x).1)
      calc
        ‖presentationEquiv hX hY x‖ ≤
            CY * kaltonPeckQuasiNorm (hY.coordinates (presentationEquiv hX hY x)) :=
          (hYconstants.2.2 (presentationEquiv hX hY x)).2
        _ = CY * kaltonPeckQuasiNorm (hX.coordinates x) := by rw [hcoordinates]
        _ ≤ CY * (‖x‖ / cX) :=
          mul_le_mul_of_nonneg_left hq hYconstants.2.1.le
        _ = (CY / cX) * ‖x‖ := by ring
    · intro y
      have hsymm :
          hX.coordinates ((presentationEquiv hX hY).symm y) = hY.coordinates y := by
        symm
        simpa using hcoordinates ((presentationEquiv hX hY).symm y)
      have hq : kaltonPeckQuasiNorm (hY.coordinates y) ≤ ‖y‖ / cY :=
        (le_div_iff₀ hYconstants.1).2
          (by simpa [mul_comm] using (hYconstants.2.2 y).1)
      calc
        ‖(presentationEquiv hX hY).symm y‖ ≤
            CX * kaltonPeckQuasiNorm
              (hX.coordinates ((presentationEquiv hX hY).symm y)) :=
          (hXconstants.2.2 ((presentationEquiv hX hY).symm y)).2
        _ = CX * kaltonPeckQuasiNorm (hY.coordinates y) := by rw [hsymm]
        _ ≤ CX * (‖y‖ / cY) :=
          mul_le_mul_of_nonneg_left hq hXconstants.2.1.le
        _ = (CX / cY) * ‖y‖ := by ring

end Coordinates

end


end KaltonPeck.Support

/-
Upstream license notice:
MIT License

Copyright (c) 2026 Avik Das

Permission is hereby granted, free of charge, to any person obtaining a copy
of this software and associated documentation files (the "Software"), to deal
in the Software without restriction, including without limitation the rights
to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
copies of the Software, and to permit persons to whom the Software is
furnished to do so, subject to the following conditions:

The above copyright notice and this permission notice shall be included in all
copies or substantial portions of the Software.

THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE
SOFTWARE.
-/

/- Adapted for Lean Pool: module imports and compatibility with its pinned toolchain. -/
