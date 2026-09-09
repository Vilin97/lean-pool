/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import Mathlib.Analysis.Analytic.Basic
public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-!
# Actual analytic Volterra words for the slow axis recursion

The functions and radial integrals here are genuine functions and Bochner
integrals. The parameter derivative is the actual complex derivative.
-/

@[expose] public section


noncomputable section

namespace NavierStokes.VolterraAnalyticBounds

open Set Metric MeasureTheory intervalIntegral Complex
open scoped BigOperators NNReal Interval

/-- Vector: an abbreviation for `Fin 6 → ℂ`. -/
abbrev Vec := Fin 6 → ℂ
/-- Field: an abbreviation for `ℝ → ℂ → Vec`. -/
abbrev Field := ℝ → ℂ → Vec
/-- Coefficient: an abbreviation for `ℝ → ℂ → Matrix (Fin 6) (Fin 6) ℂ`. -/
abbrev Coeff := ℝ → ℂ → Matrix (Fin 6) (Fin 6) ℂ

/-- The singular diagonal in the transformed axis equations is
(0, 0, 2, 0, 3, 1), with zero-based component indices. -/
noncomputable def exponent (i : Fin 6) : ℕ :=
  if i.val = 2 then 2 else if i.val = 4 then 3 else if i.val = 5 then 1 else 0

/-- Parameter derivative, defined pointwise by `deriv (fun w : ℂ => F r w i) z`. -/
noncomputable def parameterDeriv (F : Field) : Field :=
  fun r z i => deriv (fun w : ℂ => F r w i) z

/-- Normalized form of the regular inverse. It includes r = 0 without
division by the radial coordinate. -/
noncomputable def radialInverse (F : Field) : Field :=
  fun r z i => r • ∫ t : ℝ in (0)..(1), (t ^ exponent i) • F (t * r) z i

/-- Matrix action, defined pointwise by `(A r z).mulVec (F r z)`. -/
noncomputable def matrixAction (A : Coeff) (F : Field) : Field :=
  fun r z => (A r z).mulVec (F r z)

/-- False is the multiplication letter; true is the parameter-derivative letter. -/
noncomputable def letter (A₀ A₁ : Coeff) (b : Bool) (F : Field) : Field :=
  radialInverse (if b then matrixAction A₁ (parameterDeriv F) else matrixAction A₀ F)

/-- Word as an element of `w, F => letter A₀ A₁ b (word A₀ A₁ w F)`. -/
noncomputable def word (A₀ A₁ : Coeff) : List Bool → Field → Field
  | [], F => F
  | b :: w, F => letter A₀ A₁ b (word A₀ A₁ w F)

/-- Only the last two rows and first four columns may be nonzero. -/
def DerivativeShape (A : Coeff) : Prop :=
  ∀ r z (i j : Fin 6), (i.val < 4 ∨ 4 ≤ j.val) → A r z i j = 0

/-- Vanishing of the first four components as actual functions. -/
def LowZero (F : Field) : Prop :=
  ∀ r z (i : Fin 6), i.val < 4 → F r z i = 0

theorem lowZero_matrixAction {A : Coeff} (hA : DerivativeShape A) (F : Field) :
    LowZero (matrixAction A F) := by
  intro r z i hi
  unfold matrixAction Matrix.mulVec dotProduct
  apply Finset.sum_eq_zero
  intro j hj
  change A r z i j * F r z j = 0
  rw [hA r z i j (Or.inl hi), zero_mul]

theorem lowZero_parameterDeriv {F : Field} (hF : LowZero F) :
    LowZero (parameterDeriv F) := by
  intro r z i hi
  have heq : (fun w : ℂ => F r w i) = (fun _ : ℂ => 0) := by
    funext w
    exact hF r w i hi
  simp only [parameterDeriv, heq, deriv_const]

theorem lowZero_radialInverse {F : Field} (hF : LowZero F) :
    LowZero (radialInverse F) := by
  intro r z i hi
  have heq : (fun t : ℝ => (t ^ exponent i) • F (t * r) z i) =
      (fun _ : ℝ => (0 : ℂ)) := by
    funext t
    rw [hF (t * r) z i hi, smul_zero]
  change r • (∫ t : ℝ in (0)..(1), (t ^ exponent i) • F (t * r) z i) = 0
  rw [heq]
  simp

theorem matrixAction_lowZero_eq_zero {A : Coeff} (hA : DerivativeShape A)
    {F : Field} (hF : LowZero F) : matrixAction A F = 0 := by
  funext r z i
  unfold matrixAction Matrix.mulVec dotProduct
  apply Finset.sum_eq_zero
  intro j hj
  change A r z i j * F r z j = 0
  by_cases hj4 : j.val < 4
  · rw [hF r z j hj4, mul_zero]
  · rw [hA r z i j (Or.inr (Nat.le_of_not_gt hj4)), zero_mul]

@[simp] theorem radialInverse_zero : radialInverse 0 = 0 := by
  funext r z i
  simp [radialInverse]

@[simp] theorem parameterDeriv_zero : parameterDeriv 0 = 0 := by
  funext r z i
  simp [parameterDeriv]

@[simp] theorem matrixAction_zero (A : Coeff) : matrixAction A 0 = 0 := by
  funext r z i
  simp [matrixAction, Matrix.mulVec, dotProduct]

@[simp] theorem letter_zero (A₀ A₁ : Coeff) (b : Bool) : letter A₀ A₁ b 0 = 0 := by
  cases b <;> simp [letter]

theorem derivativeLetter_lowZero (A₀ : Coeff) {A₁ : Coeff}
    (hA : DerivativeShape A₁) (F : Field) : LowZero (letter A₀ A₁ true F) := by
  exact lowZero_radialInverse (lowZero_matrixAction hA (parameterDeriv F))

theorem derivativeLetter_of_lowZero (A₀ : Coeff) {A₁ : Coeff}
    (hA : DerivativeShape A₁) {F : Field} (hF : LowZero F) :
    letter A₀ A₁ true F = 0 := by
  change radialInverse (matrixAction A₁ (parameterDeriv F)) = 0
  rw [matrixAction_lowZero_eq_zero hA (lowZero_parameterDeriv hF), radialInverse_zero]

/-- This is an identity of actual differentiated integral operators.
The proof differentiates identically zero components, so it includes the
terms where the parameter derivative would hit the adjacent coefficient. -/
theorem adjacent_derivative_letters_zero (A₀ : Coeff) {A₁ : Coeff}
    (hA : DerivativeShape A₁) (F : Field) :
    letter A₀ A₁ true (letter A₀ A₁ true F) = 0 :=
  derivativeLetter_of_lowZero A₀ hA (derivativeLetter_lowZero A₀ hA F)

/-- The number of parameter-derivative letters. -/
noncomputable def losses : List Bool → ℕ
  | [] => 0
  | false :: w => losses w
  | true :: w => losses w + 1

/-- Words without consecutive parameter-derivative letters. -/
def GoodWord : List Bool → Prop
  | [] => True
  | false :: w => GoodWord w
  | true :: [] => True
  | true :: false :: w => GoodWord w
  | true :: true :: _ => False

theorem goodWord_losses (w : List Bool) (hw : GoodWord w) :
    2 * losses w ≤ w.length + 1 := by
  match w with
  | [] => simp [losses]
  | false :: w =>
      have ih := goodWord_losses w hw
      simp only [losses, List.length_cons]
      omega
  | [true] => simp [losses]
  | true :: false :: w =>
      have ih := goodWord_losses w hw
      simp only [losses, List.length_cons]
      omega
  | true :: true :: w => exact False.elim hw
termination_by w.length

theorem losses_le_half (w : List Bool) (hw : GoodWord w) :
    losses w ≤ (w.length + 1) / 2 := by
  have := goodWord_losses w hw
  omega

/-- Forbidden words are identically zero, for arbitrary actual input functions. -/
theorem word_eq_zero_of_not_good (A₀ : Coeff) {A₁ : Coeff}
    (hA : DerivativeShape A₁) (w : List Bool) (hw : ¬ GoodWord w) (F : Field) :
    word A₀ A₁ w F = 0 := by
  match w with
  | [] => exact False.elim (hw trivial)
  | false :: w =>
      rw [word, word_eq_zero_of_not_good A₀ hA w hw F, letter_zero]
  | [true] => exact False.elim (hw trivial)
  | true :: false :: w =>
      rw [word, word, word_eq_zero_of_not_good A₀ hA w hw F, letter_zero, letter_zero]
  | true :: true :: w =>
      exact adjacent_derivative_letters_zero A₀ hA (word A₀ A₁ w F)
termination_by w.length

/-- A factorially normalized radial bound on an actual field. -/
def RadialBound (F : Field) (T : ℝ) (c : ℂ) (ρ B : ℝ) (k : ℕ) : Prop :=
  ∀ r ∈ Icc 0 T, ∀ z ∈ closedBall c ρ, ∀ i,
    ‖F r z i‖ ≤ B * r ^ k / (k.factorial : ℝ)

/-- Coordinatewise holomorphy on a neighborhood of the closed parameter disk. -/
def AnalyticField (F : Field) (T : ℝ) (c : ℂ) (ρ : ℝ) : Prop :=
  ∀ r ∈ Icc 0 T, ∀ i, AnalyticOnNhd ℂ (fun z => F r z i) (closedBall c ρ)

/-- A row-sum bound on the actual matrix coefficients. -/
def MatrixBound (A : Coeff) (T : ℝ) (c : ℂ) (ρ M : ℝ) : Prop :=
  ∀ r ∈ Icc 0 T, ∀ z ∈ closedBall c ρ, ∀ i,
    ∑ j, ‖A r z i j‖ ≤ M

theorem RadialBound.mono_radius {F : Field} {T ρ σ B : ℝ} {c : ℂ} {k : ℕ}
    (h : RadialBound F T c σ B k) (hρ : ρ ≤ σ) : RadialBound F T c ρ B k :=
  fun r hr z hz i => h r hr z (closedBall_subset_closedBall hρ hz) i

theorem MatrixBound.mono_radius {A : Coeff} {T ρ σ M : ℝ} {c : ℂ}
    (h : MatrixBound A T c σ M) (hρ : ρ ≤ σ) : MatrixBound A T c ρ M :=
  fun r hr z hz i => h r hr z (closedBall_subset_closedBall hρ hz) i

theorem RadialBound.matrixAction {A : Coeff} {F : Field} {T ρ B M : ℝ}
    {c : ℂ} {k : ℕ} (hB : 0 ≤ B) (hA : MatrixBound A T c ρ M)
    (hF : RadialBound F T c ρ B k) :
    RadialBound (matrixAction A F) T c ρ (M * B) k := by
  intro r hr z hz i
  change ‖∑ j, A r z i j * F r z j‖ ≤ _
  calc
    _ ≤ ∑ j, ‖A r z i j * F r z j‖ := norm_sum_le _ _
    _ ≤ ∑ j, ‖A r z i j‖ * (B * r ^ k / (k.factorial : ℝ)) := by
      apply Finset.sum_le_sum
      intro j hj
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_left (hF r hr z hz j) (norm_nonneg _)
    _ = (∑ j, ‖A r z i j‖) * (B * r ^ k / (k.factorial : ℝ)) := by
      rw [Finset.sum_mul]
    _ ≤ M * (B * r ^ k / (k.factorial : ℝ)) :=
      mul_le_mul_of_nonneg_right (hA r hr z hz i)
        (div_nonneg (mul_nonneg hB (pow_nonneg hr.1 _)) (by positivity))
    _ = _ := by ring

/-- The elementary radial integral supplies one full factorial denominator.
No radial analyticity, and no estimate on radial derivatives, is used. -/
theorem RadialBound.radialInverse {F : Field} {T ρ B : ℝ} {c : ℂ} {k : ℕ}
    (hB : 0 ≤ B) (hF : RadialBound F T c ρ B k) :
    RadialBound (radialInverse F) T c ρ B (k + 1) := by
  intro r hr z hz i
  let C : ℝ := B * r ^ k / (k.factorial : ℝ)
  have hC : 0 ≤ C := div_nonneg (mul_nonneg hB (pow_nonneg hr.1 _)) (by positivity)
  have hb : ∀ t ∈ Icc (0 : ℝ) 1,
      ‖(t ^ exponent i) • F (t * r) z i‖ ≤ C * t ^ k := by
    intro t ht
    have htr : t * r ∈ Icc 0 T := ⟨mul_nonneg ht.1 hr.1,
      (mul_le_mul_of_nonneg_right ht.2 hr.1).trans (by simpa using hr.2)⟩
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (pow_nonneg ht.1 _)]
    calc
      t ^ exponent i * ‖F (t * r) z i‖ ≤ 1 * ‖F (t * r) z i‖ :=
        mul_le_mul_of_nonneg_right (pow_le_one₀ ht.1 ht.2) (norm_nonneg _)
      _ ≤ B * (t * r) ^ k / (k.factorial : ℝ) := by
        simpa using hF (t * r) htr z hz i
      _ = C * t ^ k := by dsimp [C]; rw [mul_pow]; ring
  have hbe : ∀ᵐ t ∂volume.restrict (Ι (0 : ℝ) 1),
      ‖(t ^ exponent i) • F (t * r) z i‖ ≤ C * t ^ k := by
    filter_upwards [ae_restrict_mem measurableSet_uIoc] with t ht
    rw [uIoc_of_le (by norm_num : (0 : ℝ) ≤ 1)] at ht
    exact hb t ⟨ht.1.le, ht.2⟩
  have hi := intervalIntegral.norm_integral_le_abs_of_norm_le hbe
    ((continuous_const.fun_mul (continuous_id.fun_pow k)).intervalIntegrable (0 : ℝ) 1)
  have heq : (∫ t : ℝ in (0)..(1), C * t ^ k) = C / ((k : ℝ) + 1) := by
    rw [intervalIntegral.integral_const_mul, integral_pow]
    simp [div_eq_mul_inv]
  rw [heq, abs_of_nonneg (div_nonneg hC (by positivity))] at hi
  change ‖r • (∫ t : ℝ in (0)..(1), (t ^ exponent i) • F (t * r) z i)‖ ≤ _
  rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hr.1]
  calc
    _ ≤ r * (C / ((k : ℝ) + 1)) := mul_le_mul_of_nonneg_left hi hr.1
    _ = B * r ^ (k + 1) / ((k + 1).factorial : ℝ) := by
      dsimp [C]
      rw [Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one, pow_succ]
      simp only [div_eq_mul_inv, mul_inv_rev]
      ring

/-- Cauchy's first derivative estimate from the actual circle integral. -/
theorem norm_deriv_le {f : ℂ → ℂ} {c : ℂ} {δ C : ℝ}
    (hδ : 0 < δ) (hf : DifferentiableOn ℂ f (closedBall c δ))
    (hb : ∀ z ∈ sphere c δ, ‖f z‖ ≤ C) :
    ‖deriv f c‖ ≤ C / δ := by
  have hc : ‖cauchyPowerSeries f c δ 1 (fun _ => 1)‖ ≤ δ⁻¹ * C := by
    rw [cauchyPowerSeries_apply]
    have hbound : ∀ z ∈ sphere c δ,
        ‖(1 / (z - c)) ^ 1 • (z - c)⁻¹ • f z‖ ≤ δ⁻¹ * (δ⁻¹ * C) := by
      intro z hz
      have hz' : ‖z - c‖ = δ := by simpa only [mem_sphere, dist_eq_norm] using hz
      rw [norm_smul, norm_smul, norm_pow, norm_div, norm_one, norm_inv, hz',
        one_div, pow_one]
      exact mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left (hb z hz) (inv_nonneg.mpr hδ.le))
        (inv_nonneg.mpr hδ.le)
    calc
      _ ≤ δ * (δ⁻¹ * (δ⁻¹ * C)) :=
        circleIntegral.norm_two_pi_i_inv_smul_integral_le_of_norm_le_const hδ.le hbound
      _ = δ⁻¹ * C := by rw [← mul_assoc, mul_inv_cancel₀ hδ.ne', one_mul]
  let s : ℝ≥0 := ⟨δ, hδ.le⟩
  have hp := (show DifferentiableOn ℂ f (closedBall c (s : ℝ)) from hf).hasFPowerSeriesOnBall
    (show 0 < s from hδ)
  have heq : deriv f c = cauchyPowerSeries f c δ 1 (fun _ => 1) := by
    have h := (hp.factorial_smul (1 : ℂ) 1).symm
    simp only [← iteratedDeriv_eq_iteratedFDeriv, iteratedDeriv_one, Nat.factorial_one, one_smul]
        at h
    exact h
  rw [heq]
  simpa [div_eq_mul_inv, mul_comm] using hc

theorem nested_closedBall {c z : ℂ} {ρ δ : ℝ} (hz : z ∈ closedBall c ρ) :
    closedBall z δ ⊆ closedBall c (ρ + δ) := by
  intro w hw
  exact (dist_triangle w z c).trans (by linarith [mem_closedBall.mp hw, mem_closedBall.mp hz])

/-- One real Cauchy loss, on a fixed smaller disk, without any radial loss. -/
theorem RadialBound.parameterDeriv {F : Field} {T ρ δ B : ℝ} {c : ℂ} {k : ℕ}
    (hδ : 0 < δ) (ha : AnalyticField F T c (ρ + δ))
    (hF : RadialBound F T c (ρ + δ) B k) :
    RadialBound (parameterDeriv F) T c ρ (B / δ) k := by
  intro r hr z hz i
  have hd : DifferentiableOn ℂ (fun w => F r w i) (closedBall z δ) :=
    (ha r hr i).differentiableOn.mono (nested_closedBall hz)
  have h := norm_deriv_le hδ hd (fun w hw =>
    hF r hr w (nested_closedBall hz (sphere_subset_closedBall hw)) i)
  change ‖deriv (fun w => F r w i) z‖ ≤ _
  convert! h using 1
  ring

theorem AnalyticField.mono_radius {F : Field} {T ρ σ : ℝ} {c : ℂ}
    (h : AnalyticField F T c σ) (hρ : ρ ≤ σ) : AnalyticField F T c ρ :=
  fun r hr i => (h r hr i).mono (closedBall_subset_closedBall hρ)

theorem RadialBound.mono_const {F : Field} {T ρ B C : ℝ} {c : ℂ} {k : ℕ}
    (h : RadialBound F T c ρ B k) (hBC : B ≤ C) : RadialBound F T c ρ C k := by
  intro r hr z hz i
  have hr0 := hr.1
  exact (h r hr z hz i).trans (by gcongr)

/-- The exact word estimate. Holomorphy of the finite words is a regularity
input, independently obtained by closure of holomorphic curve-valued maps.
Neither a convergent series nor a solution is assumed. -/
theorem word_radialBound {A₀ A₁ : Coeff} {F : Field} {T σ B M δ : ℝ} {c : ℂ}
    (hB : 0 ≤ B) (hM : 0 ≤ M) (hδ : 0 < δ)
    (hA₀ : MatrixBound A₀ T c σ M) (hA₁ : MatrixBound A₁ T c σ M)
    (hF : RadialBound F T c σ B 0)
    (ha : ∀ v, AnalyticField (word A₀ A₁ v F) T c σ)
    (w : List Bool) {ρ : ℝ} (hgap : ρ + (losses w : ℝ) * δ ≤ σ) :
    RadialBound (word A₀ A₁ w F) T c ρ
      (B * M ^ w.length * (δ⁻¹) ^ losses w) w.length := by
  induction w generalizing ρ with
  | nil =>
      simpa [word, losses] using hF.mono_radius (by simpa [losses] using hgap)
  | cons b w ih =>
      have hcost : 0 ≤ B * M ^ w.length * (δ⁻¹) ^ losses w := by positivity
      cases b with
      | false =>
          have hg : ρ + (losses w : ℝ) * δ ≤ σ := by simpa [losses] using hgap
          have hr : ρ ≤ σ := le_trans (le_add_of_nonneg_right
            (mul_nonneg (Nat.cast_nonneg _) hδ.le)) hg
          have h := (((ih hg).matrixAction hcost (hA₀.mono_radius hr)).radialInverse
            (mul_nonneg hM hcost))
          change RadialBound (radialInverse (matrixAction A₀ (word A₀ A₁ w F)))
            T c ρ _ _
          convert! h using 1
          simp only [List.length_cons, losses, pow_succ]
          ring
      | true =>
          have hg : ρ + δ + (losses w : ℝ) * δ ≤ σ := by
            simp only [losses, Nat.cast_add, Nat.cast_one] at hgap
            nlinarith
          have hr : ρ + δ ≤ σ := le_trans (le_add_of_nonneg_right
            (mul_nonneg (Nat.cast_nonneg _) hδ.le)) hg
          have hd := (ih hg).parameterDeriv hδ ((ha w).mono_radius hr)
          have h := (hd.matrixAction (div_nonneg hcost hδ.le)
            (hA₁.mono_radius ((le_add_of_nonneg_right hδ.le).trans hr))).radialInverse
            (mul_nonneg hM (div_nonneg hcost hδ.le))
          change RadialBound (radialInverse (matrixAction A₁ (parameterDeriv (word A₀ A₁ w F))))
            T c ρ _ _
          convert! h using 1
          simp only [List.length_cons, losses, pow_succ, div_eq_mul_inv]
          ring

/-- Half the word length, rounded upward. -/
noncomputable def halfLength (k : ℕ) : ℕ := (k + 1) / 2

/-- A common majorant for every word of length k, including forbidden words. -/
noncomputable def wordMajorant (a b : ℝ) (k : ℕ) : ℝ :=
  a ^ k * (b * (max 1 (halfLength k) : ℕ)) ^ halfLength k / (k.factorial : ℝ)

theorem wordMajorant_nonneg {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (k : ℕ) :
    0 ≤ wordMajorant a b k := by
  unfold wordMajorant
  positivity

/-- Uniform bound on an entire finite radial interval. The strip gap is split
only among the possible derivative letters, and not among all letters. -/
theorem norm_word_le {A₀ A₁ : Coeff} {F : Field} {T ρ σ B M : ℝ} {c : ℂ}
    (hB : 0 ≤ B) (hM : 0 ≤ M) (hT : 0 ≤ T) (hgap : ρ < σ)
    (hshape : DerivativeShape A₁)
    (hA₀ : MatrixBound A₀ T c σ M) (hA₁ : MatrixBound A₁ T c σ M)
    (hF : RadialBound F T c σ B 0)
    (ha : ∀ v, AnalyticField (word A₀ A₁ v F) T c σ)
    (w : List Bool) {r : ℝ} (hr : r ∈ Icc 0 T)
    {z : ℂ} (hz : z ∈ closedBall c ρ) (i : Fin 6) :
    ‖word A₀ A₁ w F r z i‖ ≤
      B * wordMajorant (M * T) (max 1 (σ - ρ)⁻¹) w.length := by
  have hr0 := hr.1
  have hrT := hr.2
  by_cases hw : GoodWord w
  · let p := halfLength w.length
    let q : ℝ := (max 1 p : ℕ)
    let δ : ℝ := (σ - ρ) / q
    have hq : 1 ≤ q := by
      dsimp [q]
      exact_mod_cast (le_max_left 1 p)
    have hq0 : 0 < q := lt_of_lt_of_le zero_lt_one hq
    have hd : 0 < δ := div_pos (sub_pos.mpr hgap) hq0
    have hp : (losses w : ℝ) ≤ q := by
      dsimp [q]
      exact_mod_cast (losses_le_half w hw).trans (le_max_right 1 p)
    have hbudget : ρ + (losses w : ℝ) * δ ≤ σ := by
      have hmul := mul_le_mul_of_nonneg_right hp hd.le
      have hcancel : q * δ = σ - ρ := by dsimp [δ]; field_simp
      rw [hcancel] at hmul
      linarith
    have hwbound := word_radialBound hB hM hd hA₀ hA₁ hF ha w hbudget r hr z hz i
    have hδinv : δ⁻¹ ≤ max 1 (σ - ρ)⁻¹ * q := by
      dsimp [δ]
      rw [inv_div]
      calc
        q / (σ - ρ) = (σ - ρ)⁻¹ * q := by ring
        _ ≤ _ := mul_le_mul_of_nonneg_right (le_max_right _ _) hq0.le
    have hbase : 1 ≤ max 1 (σ - ρ)⁻¹ * q :=
      one_le_mul_of_one_le_of_one_le (le_max_left _ _) hq
    have hp' : losses w ≤ p := losses_le_half w hw
    have hpow : (δ⁻¹) ^ losses w ≤ (max 1 (σ - ρ)⁻¹ * q) ^ p :=
      (pow_le_pow_left₀ (inv_nonneg.mpr hd.le) hδinv _).trans
        (pow_le_pow_right₀ hbase hp')
    calc
      _ ≤ B * M ^ w.length * (δ⁻¹) ^ losses w * r ^ w.length /
          (w.length.factorial : ℝ) := hwbound
      _ ≤ B * M ^ w.length * (max 1 (σ - ρ)⁻¹ * q) ^ p * T ^ w.length /
          (w.length.factorial : ℝ) := by gcongr
      _ = _ := by dsimp [wordMajorant, p, q]; rw [mul_pow]; ring
  · rw [word_eq_zero_of_not_good A₀ hshape w hw F]
    simpa using mul_nonneg hB
      (wordMajorant_nonneg (mul_nonneg hM hT) (le_trans zero_le_one (le_max_left _ _)) w.length)

/-- The factorial cancels all powers introduced by at most half as many
Cauchy losses, leaving an exponential-series denominator. -/
theorem factorial_half_bound (k : ℕ) :
    (max 1 (halfLength k)) ^ halfLength k * (k / 2).factorial ≤ k.factorial := by
  have hsum : k / 2 + halfLength k = k := by unfold halfLength; omega
  have hbase : max 1 (halfLength k) ≤ k / 2 + 1 := by
    unfold halfLength
    omega
  calc
    _ = (k / 2).factorial * (max 1 (halfLength k)) ^ halfLength k := by ac_rfl
    _ ≤ (k / 2).factorial * (k / 2 + 1).ascFactorial (halfLength k) :=
      Nat.mul_le_mul_left _ ((Nat.pow_le_pow_left hbase _).trans
        (Nat.pow_succ_le_ascFactorial _ _))
    _ = _ := by rw [Nat.factorial_mul_ascFactorial, hsum]

theorem half_power_div_factorial_le (k : ℕ) :
    ((max 1 (halfLength k) : ℕ) : ℝ) ^ halfLength k / (k.factorial : ℝ) ≤
      1 / ((k / 2).factorial : ℝ) := by
  apply (div_le_div_iff₀ (by positivity) (by positivity)).mpr
  simpa only [one_mul] using
    (show ((max 1 (halfLength k) : ℕ) : ℝ) ^ halfLength k *
        ((k / 2).factorial : ℝ) ≤ (k.factorial : ℝ) by
      exact_mod_cast factorial_half_bound k)

theorem wordMajorant_le_exponential {a b : ℝ} (ha : 1 ≤ a) (hb : 1 ≤ b) (k : ℕ) :
    wordMajorant a b k ≤
      (a * b) * ((a ^ 2 * b) ^ (k / 2) / ((k / 2).factorial : ℝ)) := by
  have ha0 : 0 ≤ a := zero_le_one.trans ha
  have hb0 : 0 ≤ b := zero_le_one.trans hb
  have hk : k ≤ 2 * (k / 2) + 1 := by omega
  have hp : halfLength k ≤ k / 2 + 1 := by unfold halfLength; omega
  have hpow : a ^ k * b ^ halfLength k ≤ (a * b) * (a ^ 2 * b) ^ (k / 2) := by
    calc
      _ ≤ a ^ (2 * (k / 2) + 1) * b ^ (k / 2 + 1) :=
        mul_le_mul (pow_le_pow_right₀ ha hk) (pow_le_pow_right₀ hb hp)
          (pow_nonneg hb0 _) (pow_nonneg ha0 _)
      _ = _ := by rw [pow_succ, pow_succ, pow_mul, mul_pow]; ring
  unfold wordMajorant
  rw [mul_pow]
  calc
    a ^ k * (b ^ halfLength k * ((max 1 (halfLength k) : ℕ) : ℝ) ^ halfLength k) /
        (k.factorial : ℝ) =
        (a ^ k * b ^ halfLength k) *
          (((max 1 (halfLength k) : ℕ) : ℝ) ^ halfLength k / (k.factorial : ℝ)) := by ring
    _ ≤ ((a * b) * (a ^ 2 * b) ^ (k / 2)) *
        (1 / ((k / 2).factorial : ℝ)) :=
      mul_le_mul hpow (half_power_div_factorial_le k) (by positivity) (by positivity)
    _ = _ := by ring

theorem wordMajorant_mono {a a' b b' : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (haa : a ≤ a') (hbb : b ≤ b') (k : ℕ) :
    wordMajorant a b k ≤ wordMajorant a' b' k := by
  have ha' : 0 ≤ a' := ha.trans haa
  unfold wordMajorant
  gcongr

/-- Repeating each exponential-series term twice preserves summability. -/
theorem summable_half_exponential (x C : ℝ) :
    Summable (fun k : ℕ => C * (x ^ (k / 2) / ((k / 2).factorial : ℝ))) := by
  have hs := (Real.summable_pow_div_factorial x).mul_left C
  have hprod : Summable (fun q : Fin 2 × ℕ => C * (x ^ q.2 / (q.2.factorial : ℝ))) := by
    have hn : Summable (fun q : Fin 2 × ℕ => ‖C * (x ^ q.2 / (q.2.factorial : ℝ))‖) := by
      apply (summable_prod_of_nonneg (f := fun q : Fin 2 × ℕ =>
        ‖C * (x ^ q.2 / (q.2.factorial : ℝ))‖) (fun _ => norm_nonneg _)).mpr
      exact ⟨fun _ => hs.norm, (hasSum_fintype _).summable⟩
    exact hn.of_norm
  let index : ℕ → Fin 2 × ℕ := fun k => (⟨k % 2, Nat.mod_lt _ (by decide)⟩, k / 2)
  have hinj : Function.Injective index := by
    intro m n h
    have h₁ : m % 2 = n % 2 := congrArg (fun q : Fin 2 × ℕ => q.1.val) h
    have h₂ : m / 2 = n / 2 := congrArg Prod.snd h
    omega
  exact hprod.comp_injective (i := index) hinj

/-- The Cauchy/Volterra majorant is summable for every finite coefficient,
radial, and strip-gap constant. There is no smallness assumption. -/
theorem summable_wordMajorant {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    Summable (wordMajorant a b) := by
  have hs := summable_half_exponential ((max 1 a) ^ 2 * max 1 b) (max 1 a * max 1 b)
  apply Summable.of_nonneg_of_le (wordMajorant_nonneg ha hb) _ hs
  intro k
  exact (wordMajorant_mono ha hb (le_max_right _ _) (le_max_right _ _) k).trans
    (wordMajorant_le_exponential (le_max_left _ _) (le_max_left _ _) k)

/-- The factor 2^k counting all Boolean words is absorbed into the first
majorant constant, so the entire Picard layer is still summable. -/
theorem summable_wordLayers {a b B : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    Summable (fun k : ℕ => B * (2 : ℝ) ^ k * wordMajorant a b k) := by
  have hs := (summable_wordMajorant (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) ha) hb).mul_left B
  convert! hs using 1
  ext k
  unfold wordMajorant
  rw [mul_pow]
  ring

/-- The actual finite sum of all words of a fixed length. -/
noncomputable def wordLayer (A₀ A₁ : Coeff) (F : Field) (k : ℕ) : Field :=
  fun r z i => ∑ v : Fin k → Bool, word A₀ A₁ (List.ofFn v) F r z i

theorem norm_wordLayer_le {A₀ A₁ : Coeff} {F : Field} {T ρ σ B M : ℝ} {c : ℂ}
    (hB : 0 ≤ B) (hM : 0 ≤ M) (hT : 0 ≤ T) (hgap : ρ < σ)
    (hshape : DerivativeShape A₁)
    (hA₀ : MatrixBound A₀ T c σ M) (hA₁ : MatrixBound A₁ T c σ M)
    (hF : RadialBound F T c σ B 0)
    (ha : ∀ v, AnalyticField (word A₀ A₁ v F) T c σ)
    (k : ℕ) {r : ℝ} (hr : r ∈ Icc 0 T)
    {z : ℂ} (hz : z ∈ closedBall c ρ) (i : Fin 6) :
    ‖wordLayer A₀ A₁ F k r z i‖ ≤
      B * (2 : ℝ) ^ k * wordMajorant (M * T) (max 1 (σ - ρ)⁻¹) k := by
  unfold wordLayer
  calc
    _ ≤ ∑ v : Fin k → Bool, ‖word A₀ A₁ (List.ofFn v) F r z i‖ := norm_sum_le _ _
    _ ≤ ∑ _v : Fin k → Bool, B * wordMajorant (M * T) (max 1 (σ - ρ)⁻¹) k := by
      apply Finset.sum_le_sum
      intro v hv
      simpa using norm_word_le hB hM hT hgap hshape hA₀ hA₁ hF ha (List.ofFn v) hr hz i
    _ = _ := by simp [mul_assoc, mul_comm, mul_left_comm]

/-- Absolute convergence of the actual Volterra-word expansion at every
point of a smaller closed parameter disk, uniformly bounded by one summable
sequence independent of that point. -/
theorem summable_norm_wordLayer {A₀ A₁ : Coeff} {F : Field}
    {T ρ σ B M : ℝ} {c : ℂ}
    (hB : 0 ≤ B) (hM : 0 ≤ M) (hT : 0 ≤ T) (hgap : ρ < σ)
    (hshape : DerivativeShape A₁)
    (hA₀ : MatrixBound A₀ T c σ M) (hA₁ : MatrixBound A₁ T c σ M)
    (hF : RadialBound F T c σ B 0)
    (ha : ∀ v, AnalyticField (word A₀ A₁ v F) T c σ)
    {r : ℝ} (hr : r ∈ Icc 0 T)
    {z : ℂ} (hz : z ∈ closedBall c ρ) (i : Fin 6) :
    Summable (fun k => ‖wordLayer A₀ A₁ F k r z i‖) :=
  Summable.of_nonneg_of_le (fun _ => norm_nonneg _)
    (fun k => norm_wordLayer_le hB hM hT hgap hshape hA₀ hA₁ hF ha k hr hz i)
    (summable_wordLayers (mul_nonneg hM hT) (zero_le_one.trans (le_max_left _ _)))

theorem summable_wordLayer {A₀ A₁ : Coeff} {F : Field}
    {T ρ σ B M : ℝ} {c : ℂ}
    (hB : 0 ≤ B) (hM : 0 ≤ M) (hT : 0 ≤ T) (hgap : ρ < σ)
    (hshape : DerivativeShape A₁)
    (hA₀ : MatrixBound A₀ T c σ M) (hA₁ : MatrixBound A₁ T c σ M)
    (hF : RadialBound F T c σ B 0)
    (ha : ∀ v, AnalyticField (word A₀ A₁ v F) T c σ)
    {r : ℝ} (hr : r ∈ Icc 0 T)
    {z : ℂ} (hz : z ∈ closedBall c ρ) (i : Fin 6) :
    Summable (fun k => wordLayer A₀ A₁ F k r z i) :=
  (summable_norm_wordLayer hB hM hT hgap hshape hA₀ hA₁ hF ha hr hz i).of_norm

/-- Uniform convergence of the actual partial sums on every smaller closed
parameter disk and the entire fixed radial interval. -/
theorem tendstoUniformlyOn_wordLayer {A₀ A₁ : Coeff} {F : Field}
    {T ρ σ B M : ℝ} {c : ℂ}
    (hB : 0 ≤ B) (hM : 0 ≤ M) (hT : 0 ≤ T) (hgap : ρ < σ)
    (hshape : DerivativeShape A₁)
    (hA₀ : MatrixBound A₀ T c σ M) (hA₁ : MatrixBound A₁ T c σ M)
    (hF : RadialBound F T c σ B 0)
    (ha : ∀ v, AnalyticField (word A₀ A₁ v F) T c σ) (i : Fin 6) :
    TendstoUniformlyOn
      (fun N (p : ℝ × ℂ) => ∑ k ∈ Finset.range N, wordLayer A₀ A₁ F k p.1 p.2 i)
      (fun p => ∑' k, wordLayer A₀ A₁ F k p.1 p.2 i)
      Filter.atTop (Icc 0 T ×ˢ closedBall c ρ) :=
  tendstoUniformlyOn_tsum_nat
    (summable_wordLayers (mul_nonneg hM hT) (zero_le_one.trans (le_max_left _ _)))
    (fun k _p hp => norm_wordLayer_le hB hM hT hgap hshape hA₀ hA₁ hF ha k hp.1 hp.2 i)

end NavierStokes.VolterraAnalyticBounds
