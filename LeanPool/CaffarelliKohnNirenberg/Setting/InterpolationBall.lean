/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Foundation.Sobolev.Inequalities.H1
public import LeanPool.CaffarelliKohnNirenberg.Setting.SobolevPoincareBridge
public import Mathlib.Analysis.MeanInequalitiesPow
public import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp

/-!
# Interpolation Ball

Part of the Caffarelli–Kohn–Nirenberg partial regularity proof.
-/

@[expose] public section

open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology


noncomputable section

namespace CKN

/-- Interpolation weight relating the velocity exponent to the L² and L⁶ endpoints. -/
def interpolationTheta (q : ℝ) : ℝ :=
  3 * (q - 2) / (2 * q)

/-- Exponent of the gradient contribution in the velocity interpolation estimate. -/
def interpolationExponent (q : ℝ) : ℝ :=
  3 * (q - 2) / 4

private theorem interpolationTheta_bounds {q : ℝ} (hq2 : 2 < q) (hq6 : q < 6) :
    0 < interpolationTheta q ∧ interpolationTheta q < 1 := by
  have hq : 0 < q := by linarith only [hq2]
  constructor
  · dsimp [interpolationTheta]
    positivity
  · dsimp [interpolationTheta]
    apply (div_lt_iff₀ (mul_pos (by norm_num) hq)).2
    nlinarith only [hq6]

private theorem eLpNorm_interpolate_two_six
    {μ : Measure (Vec 3)} {f : Vec 3 → ℝ} {q : ℝ}
    (hq2 : 2 < q) (hq6 : q < 6)
    (hf : AEStronglyMeasurable f μ) :
    eLpNorm f (ENNReal.ofReal q) μ ≤
      eLpNorm f 2 μ ^ (1 - interpolationTheta q) *
        eLpNorm f 6 μ ^ interpolationTheta q := by
  let θ := interpolationTheta q
  let p : ℝ := 2 / (1 - θ)
  let s : ℝ := 6 / θ
  have hθ := interpolationTheta_bounds hq2 hq6
  have hθ' : 0 < θ ∧ θ < 1 := by simpa [θ] using hθ
  have hq : 0 < q := by linarith only [hq2]
  have hp : 0 < p := by
    dsimp [p]
    exact div_pos (by norm_num) (sub_pos.mpr hθ'.2)
  have hs : 0 < s := by
    dsimp [s]
    exact div_pos (by norm_num) hθ'.1
  have hrecip : p⁻¹ + s⁻¹ = q⁻¹ := by
    dsimp [p, s, θ, interpolationTheta]
    field_simp
    ring_nf
  let pE : ℝ≥0∞ := ENNReal.ofReal p
  let sE : ℝ≥0∞ := ENNReal.ofReal s
  let qE : ℝ≥0∞ := ENNReal.ofReal q
  have hpE : pE⁻¹ = ENNReal.ofReal p⁻¹ := by
    dsimp [pE]
    exact (ENNReal.ofReal_inv_of_pos hp).symm
  have hsE : sE⁻¹ = ENNReal.ofReal s⁻¹ := by
    dsimp [sE]
    exact (ENNReal.ofReal_inv_of_pos hs).symm
  have hqE : qE⁻¹ = ENNReal.ofReal q⁻¹ := by
    dsimp [qE]
    exact (ENNReal.ofReal_inv_of_pos hq).symm
  have : ENNReal.HolderTriple pE sE qE := by
    refine ⟨?_⟩
    rw [hpE, hsE, hqE, ← ENNReal.ofReal_add (by positivity) (by positivity), hrecip]
  let w : Vec 3 → ℝ := fun x => ‖f x‖ ^ (1 - θ)
  let z : Vec 3 → ℝ := fun x => ‖f x‖ ^ θ
  have hw : AEStronglyMeasurable w μ := by
    simpa [w, Function.comp_def] using
      ((Real.continuous_rpow_const (q := 1 - θ) (by linarith only
        [hθ'.2])).aemeasurable.comp_aemeasurable
        hf.aemeasurable.norm).aestronglyMeasurable
  have hz : AEStronglyMeasurable z μ := by
    simpa [z, Function.comp_def] using
      ((Real.continuous_rpow_const (q := θ) (by linarith only
        [hθ'.1])).aemeasurable.comp_aemeasurable
        hf.aemeasurable.norm).aestronglyMeasurable
  have hholder : eLpNorm (fun x => w x * z x) qE μ ≤
      eLpNorm w pE μ * eLpNorm z sE μ := by
    simpa [w, z, ENNReal.smul_def, one_mul] using
      (eLpNorm_le_eLpNorm_mul_eLpNorm_of_norm
        (μ := μ) (p := pE) (q := sE) (r := qE)
        (fun a b : ℝ => a * b) 1 continuous_mul hw hz
        (Filter.Eventually.of_forall (fun x => by
          simp [Real.norm_eq_abs, one_mul])))
  have hprod : (fun x => w x * z x) = fun x => ‖f x‖ := by
    funext x
    change ‖f x‖ ^ (1 - θ) * ‖f x‖ ^ θ = ‖f x‖
    by_cases hzero : ‖f x‖ = 0
    · rw [hzero, Real.zero_rpow (by linarith only [hθ'.2]),
        Real.zero_rpow (by linarith only [hθ'.1]), zero_mul]
    · rw [← Real.rpow_add (lt_of_le_of_ne (norm_nonneg _) (Ne.symm hzero))]
      norm_num
  have hwp : eLpNorm w pE μ = eLpNorm f 2 μ ^ (1 - θ) := by
    have hraw := eLpNorm_norm_rpow f hf (q := 1 - θ)
      (by linarith only [hθ'.2]) (p := pE)
    have hpexp : pE * ENNReal.ofReal (1 - θ) = 2 := by
      dsimp [pE, p]
      rw [← ENNReal.ofReal_mul (by positivity)]
      field_simp [ne_of_gt (sub_pos.mpr hθ'.2)]
      norm_num
    rw [hpexp] at hraw
    simpa [w] using hraw
  have hzs : eLpNorm z sE μ = eLpNorm f 6 μ ^ θ := by
    have hraw := eLpNorm_norm_rpow f hf (q := θ) hθ'.1 (p := sE)
    have hsexp : sE * ENNReal.ofReal θ = 6 := by
      dsimp [sE, s]
      rw [← ENNReal.ofReal_mul (by positivity)]
      field_simp [ne_of_gt hθ'.1]
      norm_num
    rw [hsexp] at hraw
    simpa [z] using hraw
  rw [hprod, hwp, hzs, eLpNorm_norm f hf] at hholder
  exact hholder

private theorem ennreal_rpow_add_bound {x y : ℝ≥0∞} {p : ℝ}
    (hp0 : 0 ≤ p) (hp6 : p ≤ 6) :
    (x + y) ^ p ≤ 32 * (x ^ p + y ^ p) := by
  by_cases hp1 : p ≤ 1
  · calc
      (x + y) ^ p ≤ x ^ p + y ^ p :=
        ENNReal.rpow_add_le_add_rpow x y hp0 hp1
      _ ≤ 32 * (x ^ p + y ^ p) := by
        calc
          x ^ p + y ^ p = (1 : ℝ≥0∞) * (x ^ p + y ^ p) := by rw [one_mul]
          _ ≤ 32 * (x ^ p + y ^ p) :=
            mul_le_mul_of_nonneg_right (by norm_num) (by positivity)
  · have hp1' : 1 ≤ p := le_of_not_ge hp1
    have hmean := ENNReal.rpow_add_le_mul_rpow_add_rpow x y hp1'
    have hexp : p - 1 ≤ (5 : ℝ) := by
      linarith only [hp6]
    have htwo : (2 : ℝ≥0∞) ^ (p - 1) ≤ 32 := by
      calc
        (2 : ℝ≥0∞) ^ (p - 1) ≤ (2 : ℝ≥0∞) ^ (5 : ℝ) :=
          ENNReal.rpow_le_rpow_of_exponent_le (x := (2 : ℝ≥0∞)) (by norm_num) hexp
        _ = 32 := by norm_num
    calc
      (x + y) ^ p ≤ (2 : ℝ≥0∞) ^ (p - 1) * (x ^ p + y ^ p) := hmean
      _ ≤ 32 * (x ^ p + y ^ p) := by
        exact mul_le_mul_of_nonneg_right htwo (by positivity)

private theorem ennreal_rpow_le_six_add_one {x : ℝ≥0∞} {p : ℝ}
    (hp0 : 0 ≤ p) (hp6 : p ≤ 6) :
    x ^ p ≤ x ^ (6 : ℝ) + 1 := by
  by_cases hx : x ≤ 1
  · calc
      x ^ p ≤ 1 := ENNReal.rpow_le_one hx hp0
      _ ≤ x ^ (6 : ℝ) + 1 := by
        exact le_add_of_nonneg_left (by positivity)
  · have hx1 : 1 ≤ x := le_of_not_ge hx
    exact (ENNReal.rpow_le_rpow_of_exponent_le hx1 hp6).trans
      (le_add_of_nonneg_right (by positivity))

private theorem ennreal_scaled_rpow_bound
    {S G L R : ℝ≥0∞} {p : ℝ} (hp0 : 0 ≤ p) (hp6 : p ≤ 6) :
    (S * (G + R * L)) ^ p ≤
      32 * (S ^ (6 : ℝ) + 1) * (G ^ p + (R * L) ^ p) := by
  have hadd := ennreal_rpow_add_bound (x := G) (y := R * L) hp0 hp6
  have hS := ennreal_rpow_le_six_add_one (x := S) hp0 hp6
  calc
    (S * (G + R * L)) ^ p = S ^ p * (G + R * L) ^ p :=
      ENNReal.mul_rpow_of_nonneg _ _ hp0
    _ ≤ S ^ p * (32 * (G ^ p + (R * L) ^ p)) :=
      mul_le_mul_of_nonneg_left hadd (by positivity)
    _ = 32 * S ^ p * (G ^ p + (R * L) ^ p) := by ring
    _ ≤ 32 * (S ^ (6 : ℝ) + 1) * (G ^ p + (R * L) ^ p) := by
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hS (by positivity)) (by positivity)

private theorem interpolation_finish
    {C S G L R Lq : ℝ≥0∞} {q P Q p : ℝ}
    (hcore : Lq ^ q ≤ L ^ Q * (S * (G + R * L)) ^ P)
    (hP0 : 0 ≤ p) (hP6 : p ≤ 6)
    (hQ0 : 0 ≤ Q) (hP : P = p) (hQ : Q + P = q)
    (hC : C = 32 * (S ^ (6 : ℝ) + 1)) :
    Lq ^ q ≤ C * G ^ P * L ^ Q + C * R ^ P * L ^ q := by
  have hscaled := ennreal_scaled_rpow_bound (S := S) (G := G) (L := L)
    (R := R) (p := p) hP0 hP6
  have hscaled' : (S * (G + R * L)) ^ P ≤
      32 * (S ^ (6 : ℝ) + 1) * (G ^ P + (R * L) ^ P) := by
    simpa [hP] using hscaled
  have hP0' : 0 ≤ P := by simpa [hP] using hP0
  have hmul := mul_le_mul_of_nonneg_left hscaled' (by positivity : 0 ≤ L ^ Q)
  rw [hC]
  calc
    Lq ^ q ≤ L ^ Q * (S * (G + R * L)) ^ P := hcore
    _ ≤ L ^ Q * (32 * (S ^ (6 : ℝ) + 1) *
        (G ^ P + (R * L) ^ P)) := hmul
    _ = 32 * (S ^ (6 : ℝ) + 1) * G ^ P * L ^ Q +
        32 * (S ^ (6 : ℝ) + 1) * R ^ P * L ^ q := by
      rw [mul_add, ENNReal.mul_rpow_of_nonneg R L hP0']
      have hLp : L ^ Q * L ^ P = L ^ q := by
        rw [← ENNReal.rpow_add_of_nonneg (x := L) (y := Q) (z := P)
          hQ0 hP0', hQ]
      calc
        L ^ Q * (32 * (S ^ (6 : ℝ) + 1) * G ^ P +
            32 * (S ^ (6 : ℝ) + 1) * (R ^ P * L ^ P)) =
            32 * (S ^ (6 : ℝ) + 1) * G ^ P * L ^ Q +
              32 * (S ^ (6 : ℝ) + 1) * R ^ P *
                (L ^ Q * L ^ P) := by ring
        _ = 32 * (S ^ (6 : ℝ) + 1) * G ^ P * L ^ Q +
            32 * (S ^ (6 : ℝ) + 1) * R ^ P * L ^ q := by rw [hLp]

private theorem interpolationBall_of_sobolev_constant
    {S : ℝ≥0∞}
    (hS : ∀ {x₀ : Vec 3} {r : ℝ}, 0 < r →
      ∀ v : H1Function (euclideanBall x₀ r),
        lpNormOn 6 (euclideanBall x₀ r) v.toFun ≤
          S * (weakGradientLpNormOn 2 (euclideanBall x₀ r) v.grad +
            (ENNReal.ofReal r)⁻¹ * lpNormOn 2 (euclideanBall x₀ r) v.toFun)) :
    ∀ q : ℝ, 2 ≤ q → q ≤ 6 →
      ∀ {x₀ : Vec 3} {r : ℝ}, 0 < r →
      ∀ v : H1Function (euclideanBall x₀ r),
        lpNormOn (ENNReal.ofReal q) (euclideanBall x₀ r) v.toFun ^ q ≤
          (32 * (S ^ (6 : ℝ) + 1)) * weakGradientLpNormOn 2 (euclideanBall x₀ r) v.grad ^
              (2 * interpolationExponent q) *
              lpNormOn 2 (euclideanBall x₀ r) v.toFun ^
                (q - 2 * interpolationExponent q) +
          (32 * (S ^ (6 : ℝ) + 1)) * (ENNReal.ofReal r) ^
              (-(2 * interpolationExponent q)) *
              lpNormOn 2 (euclideanBall x₀ r) v.toFun ^ q := by
  intro q hq2 hq6 x₀ r hr v
  let Lq := lpNormOn (ENNReal.ofReal q) (euclideanBall x₀ r) v.toFun
  let L := lpNormOn 2 (euclideanBall x₀ r) v.toFun
  let G := weakGradientLpNormOn 2 (euclideanBall x₀ r) v.grad
  let R := (ENNReal.ofReal r)⁻¹
  let P : ℝ := 2 * interpolationExponent q
  let Q : ℝ := q - 2 * interpolationExponent q
  have hq0 : 0 ≤ q := by linarith only [hq2]
  have hP0 : 0 ≤ P := by
    dsimp [P, interpolationExponent]
    positivity
  have hP6 : P ≤ 6 := by
    dsimp [P, interpolationExponent]
    nlinarith only [hq6]
  have hQ0 : 0 ≤ Q := by
    dsimp [Q, interpolationExponent]
    nlinarith only [hq2, hq6]
  have hqPQ : Q + P = q := by
    dsimp [Q, P]
    ring
  have hsob' := hS (x₀ := x₀) (r := r) hr v
  have hsob'' : lpNormOn 6 (euclideanBall x₀ r) v.toFun ≤
      S * (G + R * L) := by
    simpa [G, R, L] using hsob'
  have hcore : Lq ^ q ≤ L ^ (Q : ℝ) * (S * (G + R * L)) ^ (P : ℝ) := by
    by_cases hqeq2 : q = 2
    · have hLqeq : Lq = L := by simp [Lq, L, hqeq2]
      have hQeq : Q = 2 := by
        dsimp [Q, interpolationExponent]
        rw [hqeq2]
        norm_num
      have hPeq : P = 0 := by
        dsimp [P, interpolationExponent]
        rw [hqeq2]
        norm_num
      rw [hqeq2, hLqeq, hQeq, hPeq]
      simp
    · by_cases hqeq6 : q = 6
      · have hpow := ENNReal.rpow_le_rpow hsob'' (by positivity : 0 ≤ (6 : ℝ))
        have hLqeq : Lq = lpNormOn 6 (euclideanBall x₀ r) v.toFun := by
          simp [Lq, hqeq6]
        have hQeq : Q = 0 := by
          dsimp [Q, interpolationExponent]
          rw [hqeq6]
          norm_num
        have hPeq : P = 6 := by
          dsimp [P, interpolationExponent]
          rw [hqeq6]
          norm_num
        rw [hqeq6, hLqeq, hQeq, hPeq]
        simpa using hpow
      · have hq2' : 2 < q := lt_of_le_of_ne hq2 (Ne.symm hqeq2)
        have hq6' : q < 6 := lt_of_le_of_ne hq6 hqeq6
        have hmeas : AEStronglyMeasurable v.toFun
            (volume.restrict (euclideanBall x₀ r)) := by
          exact v.memL2.aestronglyMeasurable
        have hinterp := eLpNorm_interpolate_two_six
          (μ := volume.restrict (euclideanBall x₀ r))
          (f := v.toFun) hq2' hq6' hmeas
        have hpow := ENNReal.rpow_le_rpow hinterp (by positivity : 0 ≤ q)
        have hsix := ENNReal.rpow_le_rpow hsob'' hP0
        have hthetaP :
            (1 - interpolationTheta q) * q = Q ∧
              interpolationTheta q * q = P := by
          dsimp [Q, P, interpolationExponent, interpolationTheta]
          have hqpos : q ≠ 0 := ne_of_gt (by linarith only [hq2])
          constructor <;> field_simp [hqpos] <;> ring
        have hpow' : Lq ^ q ≤
            (L ^ (1 - interpolationTheta q) *
              (lpNormOn 6 (euclideanBall x₀ r) v.toFun) ^
                interpolationTheta q) ^ q := by
          simpa [Lq, L, lpNormOn] using hpow
        calc
          Lq ^ q ≤ (L ^ (1 - interpolationTheta q) *
              (lpNormOn 6 (euclideanBall x₀ r) v.toFun) ^
                interpolationTheta q) ^ q := hpow'
          _ = L ^ Q *
              (lpNormOn 6 (euclideanBall x₀ r) v.toFun) ^ P := by
            rw [ENNReal.mul_rpow_of_nonneg _ _ hq0]
            rw [← ENNReal.rpow_mul, ← ENNReal.rpow_mul]
            rw [hthetaP.1, hthetaP.2]
          _ ≤ L ^ Q * (S * (G + R * L)) ^ P := by
            gcongr
  have hfinish := interpolation_finish (C := 32 * (S ^ (6 : ℝ) + 1))
    (S := S) (G := G) (L := L) (R := R) (Lq := Lq)
    (q := q) (P := P) (Q := Q)
    (p := P) hcore
    hP0 hP6 hQ0 rfl hqPQ rfl
  simpa [Lq, L, G, R, P, Q, interpolationExponent,
    ENNReal.inv_rpow, ENNReal.rpow_neg] using hfinish

theorem interpolationBall_of_sobolev
    (hsob : ∃ S : ℝ≥0∞, ∀ {x₀ : Vec 3} {r : ℝ}, 0 < r →
      ∀ v : H1Function (euclideanBall x₀ r),
        lpNormOn 6 (euclideanBall x₀ r) v.toFun ≤
          S * (weakGradientLpNormOn 2 (euclideanBall x₀ r) v.grad +
            (ENNReal.ofReal r)⁻¹ * lpNormOn 2 (euclideanBall x₀ r) v.toFun)) :
    ∃ C₆ : ℝ≥0∞, ∀ q : ℝ, 2 ≤ q → q ≤ 6 →
      ∀ {x₀ : Vec 3} {r : ℝ}, 0 < r →
      ∀ v : H1Function (euclideanBall x₀ r),
        lpNormOn (ENNReal.ofReal q) (euclideanBall x₀ r) v.toFun ^ q ≤
          C₆ * weakGradientLpNormOn 2 (euclideanBall x₀ r) v.grad ^
              (2 * interpolationExponent q) *
              lpNormOn 2 (euclideanBall x₀ r) v.toFun ^
                (q - 2 * interpolationExponent q) +
          C₆ * (ENNReal.ofReal r) ^ (-(2 * interpolationExponent q)) *
              lpNormOn 2 (euclideanBall x₀ r) v.toFun ^ q := by
  obtain ⟨S, hS⟩ := hsob
  exact ⟨32 * (S ^ (6 : ℝ) + 1), interpolationBall_of_sobolev_constant hS⟩

/-- The interpolation estimate on every positive-radius Euclidean ball.
This statement does not record finiteness of its `ℝ≥0∞` coefficient; use
`interpolationBall_finite` for the finite-constant estimate, or
`interpolationBall_three_finite` for its cubic specialization. -/
theorem interpolationBall :
    ∃ C₆ : ℝ≥0∞, ∀ q : ℝ, 2 ≤ q → q ≤ 6 →
      ∀ {x₀ : Vec 3} {r : ℝ}, 0 < r →
      ∀ v : H1Function (euclideanBall x₀ r),
        lpNormOn (ENNReal.ofReal q) (euclideanBall x₀ r) v.toFun ^ q ≤
          C₆ * weakGradientLpNormOn 2 (euclideanBall x₀ r) v.grad ^
              (2 * interpolationExponent q) *
              lpNormOn 2 (euclideanBall x₀ r) v.toFun ^
                (q - 2 * interpolationExponent q) +
          C₆ * (ENNReal.ofReal r) ^ (-(2 * interpolationExponent q)) *
              lpNormOn 2 (euclideanBall x₀ r) v.toFun ^ q := by
  apply interpolationBall_of_sobolev
  refine ⟨2 * sobolevPoincareL6Constant +
    2 * sobolevPoincareBallFullConstant, ?_⟩
  intro x₀ r hr v
  exact h1SobolevBall_of_sobolevPoincare hr v

/-! The witness supplied by the Sobolev bridge is finite.  Keeping this fact
separate lets cylinder arguments pass from `ℝ≥0∞` estimates to the real
scale quantities without introducing an artificial finiteness hypothesis. -/

/-- A finite constant witnesses the interpolation estimate on every ball. -/
theorem interpolationBall_finite :
    ∃ C₆ : ℝ≥0∞, C₆ ≠ ∞ ∧ ∀ q : ℝ, 2 ≤ q → q ≤ 6 →
      ∀ {x₀ : Vec 3} {r : ℝ}, 0 < r →
      ∀ v : H1Function (euclideanBall x₀ r),
        lpNormOn (ENNReal.ofReal q) (euclideanBall x₀ r) v.toFun ^ q ≤
          C₆ * weakGradientLpNormOn 2 (euclideanBall x₀ r) v.grad ^
              (2 * interpolationExponent q) *
          lpNormOn 2 (euclideanBall x₀ r) v.toFun ^
              (q - 2 * interpolationExponent q) +
          C₆ * (ENNReal.ofReal r) ^ (-(2 * interpolationExponent q)) *
          lpNormOn 2 (euclideanBall x₀ r) v.toFun ^ q := by
  let C₆ : ℝ≥0∞ := 32 *
    ((2 * sobolevPoincareL6Constant +
      2 * sobolevPoincareBallFullConstant) ^ (6 : ℝ) + 1)
  have hC₆ : C₆ ≠ ∞ := by
    dsimp [C₆]
    have hS : sobolevPoincareL6Constant ≠ ∞ := by
      unfold sobolevPoincareL6Constant
      apply ENNReal.mul_ne_top
      · unfold localSobolevConstant
        finiteness
      · apply ENNReal.add_ne_top.mpr
        constructor
        · apply ENNReal.rpow_ne_top_of_nonneg (by positivity)
          apply ENNReal.add_ne_top.mpr
          constructor
          · norm_num
          · apply ENNReal.mul_ne_top
            · norm_num
            · simp [euclideanBallPoincareConstant]
        · apply ENNReal.mul_ne_top
          · norm_num
          · apply ENNReal.mul_ne_top
            · apply ENNReal.rpow_ne_top_of_nonneg (by positivity)
              norm_num
            · apply ENNReal.rpow_ne_top_of_nonneg (by positivity)
              simp [euclideanBallPoincareConstant]
    have hF : sobolevPoincareBallFullConstant < ∞ := by
      unfold sobolevPoincareBallFullConstant
      rw [lt_top_iff_ne_top]
      apply ENNReal.rpow_ne_top_of_ne_zero
      · exact ENNReal.ofReal_ne_zero_iff.mpr (by positivity)
      · exact ENNReal.ofReal_ne_top
    have hsum : 2 * sobolevPoincareL6Constant +
        2 * sobolevPoincareBallFullConstant ≠ ∞ := by
      apply ENNReal.add_ne_top.mpr
      exact ⟨ENNReal.mul_ne_top ENNReal.ofNat_ne_top hS,
        ENNReal.mul_ne_top ENNReal.ofNat_ne_top hF.ne⟩
    have hpow := ENNReal.rpow_lt_top_of_nonneg
      (by norm_num : (0 : ℝ) ≤ 6) hsum
    exact (ENNReal.mul_lt_top ENNReal.ofNat_lt_top
      (ENNReal.add_lt_top.mpr ⟨hpow, ENNReal.one_lt_top⟩)).ne
  refine ⟨C₆, hC₆, ?_⟩
  have hS' : ∀ {x₀ : Vec 3} {r : ℝ}, 0 < r →
      ∀ v : H1Function (euclideanBall x₀ r),
        lpNormOn 6 (euclideanBall x₀ r) v.toFun ≤
          (2 * sobolevPoincareL6Constant +
            2 * sobolevPoincareBallFullConstant) *
            (weakGradientLpNormOn 2 (euclideanBall x₀ r) v.grad +
            (ENNReal.ofReal r)⁻¹ * lpNormOn 2 (euclideanBall x₀ r) v.toFun) := by
    intro x₀ r hr v
    exact h1SobolevBall_of_sobolevPoincare hr v
  have h := interpolationBall_of_sobolev_constant
    (S := 2 * sobolevPoincareL6Constant +
      2 * sobolevPoincareBallFullConstant) hS'
  simpa [C₆] using h

/-- The finite-witness interpolation estimate specialized to the cubic slice
exponent used on parabolic cylinders. -/
theorem interpolationBall_three_finite :
    ∃ C₆ : ℝ≥0∞, C₆ ≠ ∞ ∧ ∀ {x₀ : Vec 3} {r : ℝ}, 0 < r →
      ∀ v : H1Function (euclideanBall x₀ r),
        lpNormOn 3 (euclideanBall x₀ r) v.toFun ^ (3 : ℕ) ≤
          C₆ * weakGradientLpNormOn 2 (euclideanBall x₀ r) v.grad ^
              (3 / 2 : ℝ) * lpNormOn 2 (euclideanBall x₀ r) v.toFun ^
                (3 / 2 : ℝ) +
          C₆ * (ENNReal.ofReal r) ^ (-(3 / 2 : ℝ)) *
            lpNormOn 2 (euclideanBall x₀ r) v.toFun ^ (3 : ℕ) := by
  obtain ⟨C₆, hC₆, hC⟩ := interpolationBall_finite
  refine ⟨C₆, hC₆, ?_⟩
  intro x₀ r hr v
  have h := hC 3 (by norm_num) (by norm_num) hr v
  norm_num [interpolationExponent] at h
  exact h

end CKN
