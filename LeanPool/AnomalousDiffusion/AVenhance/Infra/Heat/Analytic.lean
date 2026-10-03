/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Heat.Energy
public import Mathlib.Analysis.Complex.Exponential

/-! Explicit Gaussian bounds for the Fourier heat multiplier. -/

@[expose] public section

noncomputable section

open AVenhance.Infra.Torus

namespace AVenhance.Infra.Heat

/-- Total order of a coordinate multi-index in two dimensions. -/
def multiIndexDegree (α : Fin 2 → ℕ) : ℕ :=
  ∑ i : Fin 2, α i

/-- The Fourier multiplier for the coordinate derivative with multi-index `α`. -/
def multiIndexFourierFactor (α : Fin 2 → ℕ) (k : Frequency) : ℂ :=
  ∏ i : Fin 2, (2 * Real.pi * Complex.I * (k i : ℂ)) ^ (α i)

/-- Fourier multiplier of the corresponding derivative after heat evolution. -/
def heatDerivativeMultiplier (s : ℝ) (α : Fin 2 → ℕ) (k : Frequency) : ℂ :=
  (heatMultiplier s k : ℂ) * multiIndexFourierFactor α k

/-- The coordinate frequencies are controlled by the Euclidean frequency length. -/
theorem Analytic.abs_frequencyCoord_le_sqrt (k : Frequency) (i : Fin 2) :
    |(k i : ℝ)| ≤ Real.sqrt (frequencySq k) := by
  have hq : 0 ≤ frequencySq k := by
    unfold frequencySq
    exact Finset.sum_nonneg fun j hj => sq_nonneg (k j : ℝ)
  have hcoord : (k i : ℝ) ^ 2 ≤ frequencySq k := by
    unfold frequencySq
    exact Finset.single_le_sum (fun j hj => sq_nonneg (k j : ℝ)) (Finset.mem_univ i)
  apply (sq_le_sq₀ (abs_nonneg _) (Real.sqrt_nonneg _)).mp
  rw [sq_abs, Real.sq_sqrt hq]
  exact hcoord

/-- The multi-index Fourier factor is bounded by the radial frequency power. -/
theorem Analytic.multiIndexFourierFactor_norm_le (α : Fin 2 → ℕ) (k : Frequency) :
    ‖multiIndexFourierFactor α k‖ ≤
      (2 * Real.pi * Real.sqrt (frequencySq k)) ^ multiIndexDegree α := by
  have hfactor : ∀ i : Fin 2,
      2 * Real.pi * |(k i : ℝ)| ≤ 2 * Real.pi * Real.sqrt (frequencySq k) := by
    intro i
    exact mul_le_mul_of_nonneg_left (Analytic.abs_frequencyCoord_le_sqrt k i) (by positivity)
  have hprod :
      (∏ i : Fin 2, (2 * Real.pi * |(k i : ℝ)|) ^ (α i)) ≤
        ∏ i : Fin 2, (2 * Real.pi * Real.sqrt (frequencySq k)) ^ (α i) := by
    apply Finset.prod_le_prod₀
    · intro i hi
      positivity
    · intro i hi
      exact pow_le_pow_left₀ (by positivity) (hfactor i) (α i)
  have hprodEq :
      (∏ i : Fin 2, (2 * Real.pi * Real.sqrt (frequencySq k)) ^ (α i)) =
        (2 * Real.pi * Real.sqrt (frequencySq k)) ^ multiIndexDegree α := by
    simp [multiIndexDegree, Finset.prod_pow_eq_pow_sum]
  calc
    ‖multiIndexFourierFactor α k‖ =
        ∏ i : Fin 2, (2 * Real.pi * |(k i : ℝ)|) ^ (α i) := by
      simp [multiIndexFourierFactor, Complex.norm_I, Complex.norm_intCast,
        Complex.norm_real, Real.norm_eq_abs]
    _ ≤ ∏ i : Fin 2, (2 * Real.pi * Real.sqrt (frequencySq k)) ^ (α i) := hprod
    _ = (2 * Real.pi * Real.sqrt (frequencySq k)) ^ multiIndexDegree α := hprodEq

/-- The Gaussian multiplier absorbs a radial frequency power with factorial
loss one. This gives the universal analyticity constant `C = 1`. -/
theorem radialHeatMultiplier_bound {s : ℝ} (hs : 0 < s)
    (n : ℕ) (k : Frequency) :
    (2 * Real.pi * Real.sqrt (frequencySq k)) ^ n * heatMultiplier s k ≤
      (Nat.factorial n : ℝ) * (1 / Real.sqrt s) ^ n := by
  let y : ℝ := 2 * Real.pi * Real.sqrt s * Real.sqrt (frequencySq k)
  have hsqrt : 0 < Real.sqrt s := Real.sqrt_pos.2 hs
  have hfreq : 0 ≤ Real.sqrt (frequencySq k) := Real.sqrt_nonneg _
  have hy : 0 ≤ y := by dsimp [y]; positivity
  have hysq : y ^ 2 = 4 * Real.pi ^ 2 * s * frequencySq k := by
    dsimp [y]
    have hq : 0 ≤ frequencySq k := by
      unfold frequencySq
      exact Finset.sum_nonneg fun i hi => sq_nonneg (k i : ℝ)
    rw [mul_pow, mul_pow, Real.sq_sqrt hs.le, Real.sq_sqrt hq]
    ring
  have hTaylor := Real.pow_div_factorial_le_exp (y ^ 2) (sq_nonneg y) n
  have hfactorialPos : 0 < (Nat.factorial n : ℝ) := by exact_mod_cast Nat.factorial_pos n
  have hTaylor' : y ^ (2 * n) ≤ (Nat.factorial n : ℝ) * Real.exp (y ^ 2) := by
    have hpow : (y ^ 2) ^ n = y ^ (2 * n) := by rw [← pow_mul]
    calc
      y ^ (2 * n) = (y ^ 2) ^ n := hpow.symm
      _ ≤ Real.exp (y ^ 2) * (Nat.factorial n : ℝ) :=
        (div_le_iff₀ hfactorialPos).mp (by simpa using hTaylor)
      _ = (Nat.factorial n : ℝ) * Real.exp (y ^ 2) := by ring
  have hExpSq :
      (y ^ n * Real.exp (-(y ^ 2))) ^ 2 ≤ (Nat.factorial n : ℝ) ^ 2 := by
    have hExp : Real.exp (-(y ^ 2)) ^ 2 = Real.exp (-(2 * y ^ 2)) := by
      rw [pow_two, ← Real.exp_add]
      congr 1
      ring
    calc
      (y ^ n * Real.exp (-(y ^ 2))) ^ 2 =
          y ^ (n * 2) * Real.exp (-(2 * y ^ 2)) := by
        rw [mul_pow, ← pow_mul, hExp]
      _ ≤
          ((Nat.factorial n : ℝ) * Real.exp (y ^ 2)) * Real.exp (-(2 * y ^ 2)) := by
        exact mul_le_mul_of_nonneg_right (by simpa [Nat.mul_comm] using hTaylor')
          (Real.exp_pos _).le
      _ = (Nat.factorial n : ℝ) * Real.exp (-(y ^ 2)) := by
        rw [mul_assoc, ← Real.exp_add]
        congr 1
        ring_nf
      _ ≤ (Nat.factorial n : ℝ) ^ 2 := by
        have hle : Real.exp (-(y ^ 2)) ≤ 1 :=
          Real.exp_le_one_iff.mpr (by nlinarith [sq_nonneg y])
        have hfactOne : 1 ≤ (Nat.factorial n : ℝ) := by
          exact_mod_cast Nat.one_le_of_lt (Nat.factorial_pos n)
        calc
          _ ≤ (Nat.factorial n : ℝ) := by
            calc
              _ ≤ (Nat.factorial n : ℝ) * 1 :=
                mul_le_mul_of_nonneg_left hle hfactorialPos.le
              _ = _ := by ring
          _ ≤ (Nat.factorial n : ℝ) ^ 2 := by nlinarith
  have hgauss : y ^ n * Real.exp (-(y ^ 2)) ≤ (Nat.factorial n : ℝ) := by
    have hleft : 0 ≤ y ^ n * Real.exp (-(y ^ 2)) := by positivity
    have hright : 0 ≤ (Nat.factorial n : ℝ) := hfactorialPos.le
    nlinarith [hExpSq]
  have hscale : 2 * Real.pi * Real.sqrt (frequencySq k) = (1 / Real.sqrt s) * y := by
    dsimp [y]
    field_simp
  rw [heatMultiplier]
  calc
    (2 * Real.pi * Real.sqrt (frequencySq k)) ^ n *
        Real.exp (-(4 * Real.pi ^ 2 * s * frequencySq k)) =
        (1 / Real.sqrt s) ^ n * (y ^ n * Real.exp (-(y ^ 2))) := by
      rw [hscale, mul_pow, hysq]
      ring
    _ ≤ (1 / Real.sqrt s) ^ n * (Nat.factorial n : ℝ) :=
      mul_le_mul_of_nonneg_left hgauss (by positivity)
    _ = (Nat.factorial n : ℝ) * (1 / Real.sqrt s) ^ n := by ring

/-- For every coordinate multi-index, the heat multiplier and derivative
factor obey the factorial analyticity bound with explicit universal constant `1`. -/
theorem heatDerivativeMultiplier_norm_le {s : ℝ} (hs : 0 < s)
    (α : Fin 2 → ℕ) (k : Frequency) :
    ‖heatDerivativeMultiplier s α k‖ ≤
      (Nat.factorial (multiIndexDegree α) : ℝ) *
        (1 / Real.sqrt s) ^ multiIndexDegree α := by
  have hmult : 0 ≤ heatMultiplier s k := (Real.exp_pos _).le
  rw [heatDerivativeMultiplier, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg hmult]
  have hrad := radialHeatMultiplier_bound hs (multiIndexDegree α) k
  have hfactor := Analytic.multiIndexFourierFactor_norm_le α k
  calc
    heatMultiplier s k * ‖multiIndexFourierFactor α k‖ ≤
        heatMultiplier s k *
          (2 * Real.pi * Real.sqrt (frequencySq k)) ^ multiIndexDegree α :=
      mul_le_mul_of_nonneg_left hfactor hmult
    _ ≤ (Nat.factorial (multiIndexDegree α) : ℝ) *
          (1 / Real.sqrt s) ^ multiIndexDegree α := by
      simpa [mul_comm] using hrad

/-- Fourier sequence of the order-`α` spectral derivative of the heat flow. -/
noncomputable def heatDerivativeSequence {s : ℝ} (hs : 0 < s)
    (f : TorusL2 2) (α : Fin 2 → ℕ) : lp (fun _ : Frequency => ℂ) 2 := by
  let a : lp (fun _ : Frequency => ℂ) 2 := UnitAddTorus.mFourierBasis.repr f
  let M : ℝ := (Nat.factorial (multiIndexDegree α) : ℝ) *
    (1 / Real.sqrt s) ^ multiIndexDegree α
  have hM : 0 ≤ M := by positivity
  have hnorm : Memℓp (fun k : Frequency => ‖a k‖) 2 := a.2.norm
  have hscaled : Memℓp (fun k : Frequency => M * ‖a k‖) 2 := by
    exact hnorm.const_mul M
  have hmem : Memℓp
      (fun k : Frequency => heatDerivativeMultiplier s α k * a k) 2 := by
    apply Memℓp.mono hscaled
    intro k
    rw [norm_mul]
    calc
      ‖heatDerivativeMultiplier s α k‖ * ‖a k‖ ≤ M * ‖a k‖ :=
        mul_le_mul_of_nonneg_right (by
          simpa [M] using heatDerivativeMultiplier_norm_le hs α k)
          (norm_nonneg _)
      _ = M * ‖a k‖ := rfl
  exact ⟨fun k => heatDerivativeMultiplier s α k * a k, hmem⟩

/-- The `L²` spectral derivative of heat flow, defined by the coordinate
Fourier multiplier. -/
noncomputable def heatDerivativeTorusL2 {s : ℝ} (hs : 0 < s)
    (f : TorusL2 2) (α : Fin 2 → ℕ) : TorusL2 2 :=
  UnitAddTorus.mFourierBasis.repr.symm (heatDerivativeSequence hs f α)

/-- Fourier coefficients of the spectral derivative are the expected
multi-index multiplier. -/
theorem mFourierCoeff_heatDerivativeTorusL2 {s : ℝ} (hs : 0 < s)
    (f : TorusL2 2) (α : Fin 2 → ℕ) (k : Frequency) :
    UnitAddTorus.mFourierCoeff (heatDerivativeTorusL2 hs f α) k =
      heatDerivativeMultiplier s α k * UnitAddTorus.mFourierCoeff f k := by
  rw [← UnitAddTorus.mFourierBasis_repr (heatDerivativeTorusL2 hs f α) k]
  simp only [heatDerivativeTorusL2, LinearIsometryEquiv.apply_symm_apply,
    heatDerivativeSequence]
  rw [← UnitAddTorus.mFourierBasis_repr f k]

/-- The `L²` norm of every spectral derivative obeys the factorial
analyticity estimate with explicit constant `C = 1`. -/
theorem norm_heatDerivativeTorusL2_le {s : ℝ} (hs : 0 < s)
    (f : TorusL2 2) (α : Fin 2 → ℕ) :
    ‖heatDerivativeTorusL2 hs f α‖ ≤
      (Nat.factorial (multiIndexDegree α) : ℝ) *
        (1 / Real.sqrt s) ^ multiIndexDegree α * ‖f‖ := by
  let a : lp (fun _ : Frequency => ℂ) 2 := UnitAddTorus.mFourierBasis.repr f
  let M : ℝ := (Nat.factorial (multiIndexDegree α) : ℝ) *
    (1 / Real.sqrt s) ^ multiIndexDegree α
  have hM : 0 ≤ M := by positivity
  have hcoord : ∀ k : Frequency,
      ‖(heatDerivativeSequence hs f α) k‖ ≤ ‖(M : ℂ) * a k‖ := by
    intro k
    change ‖heatDerivativeMultiplier s α k * a k‖ ≤ ‖(M : ℂ) * a k‖
    rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hM]
    exact mul_le_mul_of_nonneg_right (by
      simpa [M, a] using heatDerivativeMultiplier_norm_le hs α k) (norm_nonneg _)
  have hseq :
      ‖heatDerivativeSequence hs f α‖ ≤ ‖(M : ℂ) • a‖ :=
    lp.norm_mono (by norm_num : (2 : ENNReal) ≠ 0) hcoord
  rw [heatDerivativeTorusL2, UnitAddTorus.mFourierBasis.repr.symm.norm_map]
  calc
    ‖heatDerivativeSequence hs f α‖ ≤ ‖(M : ℂ) • a‖ := hseq
    _ = M * ‖a‖ := by
      rw [norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hM]
    _ = M * ‖f‖ := by simp [a, UnitAddTorus.mFourierBasis.repr.norm_map]
    _ = (Nat.factorial (multiIndexDegree α) : ℝ) *
        (1 / Real.sqrt s) ^ multiIndexDegree α * ‖f‖ := by
      simp [M]

end AVenhance.Infra.Heat
