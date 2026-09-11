/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.Complex.LocallyUniformLimit
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
public import Mathlib.Analysis.Analytic.Basic
public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Analysis.Complex.CauchyIntegral

/-!
# Symmetric extension and parity for the actual Volterra solution

The negative half is obtained by reflecting the differential equation.
The integral identity is proved for the glued function at and across the
axis; parity will follow from uniqueness, not from the definition of glue.
-/

section

/-!
# Regular Volterra inverses and the sparse parameter-derivative system

The radial inverse is an actual interval integral. Its regularity at the axis
is proved directly, without interpreting the singular differential expression
by division by zero. The analytic word estimates are supplied separately by
`VolterraAnalyticBounds`.
-/

section

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

end
end

end

@[expose] public section

noncomputable section

namespace NavierStokes.NilpotentVolterra

open Set Filter MeasureTheory
open scoped Topology ContDiff

section RadialInverse

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The normalized integral in the regular inverse of `d/dξ+c/ξ`. -/
def weightedMean (c : ℕ) (f : ℝ → E) (ξ : ℝ) : E :=
  ∫ t in (0 : ℝ)..1, (t ^ c) • f (t * ξ)

/-- The genuine zero-axis Volterra inverse. -/
def regularPrimitive (c : ℕ) (f : ℝ → E) (ξ : ℝ) : E :=
  ξ • weightedMean c f ξ

theorem weightedMean_continuous (c : ℕ) {f : ℝ → E} (hf : Continuous f) :
    Continuous (weightedMean c f) := by
  exact intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
    ((continuous_snd.pow c).smul (hf.comp (continuous_snd.mul continuous_fst))) 0 1

theorem regularPrimitive_continuous (c : ℕ) {f : ℝ → E} (hf : Continuous f) :
    Continuous (regularPrimitive c f) :=
  continuous_id.smul (weightedMean_continuous c hf)

@[simp] theorem regularPrimitive_zero (c : ℕ) (f : ℝ → E) :
    regularPrimitive c f 0 = 0 := by simp [regularPrimitive]

theorem weightedMean_zero [CompleteSpace E] (c : ℕ) (f : ℝ → E) :
    weightedMean c f 0 = (1 / ((c : ℝ) + 1)) • f 0 := by
  simp only [weightedMean, mul_zero, intervalIntegral.integral_smul_const,
    integral_pow, one_pow, zero_pow (Nat.succ_ne_zero c), sub_zero]

/-- Multiplication by the integrating factor gives the ordinary primitive. -/
theorem regularPrimitive_integratingFactor (c : ℕ) (f : ℝ → E) (ξ : ℝ) :
    ξ ^ c • regularPrimitive c f ξ = ∫ s in (0 : ℝ)..ξ, s ^ c • f s := by
  calc
    ξ ^ c • regularPrimitive c f ξ =
        ξ • ∫ t in (0 : ℝ)..1, (t * ξ) ^ c • f (t * ξ) := by
      unfold regularPrimitive weightedMean
      rw [smul_comm, ← intervalIntegral.integral_smul]
      congr 1
      apply intervalIntegral.integral_congr
      intro t ht
      simp only [mul_pow, smul_smul]
      rw [mul_comm]
    _ = _ := by
      simpa only [zero_mul, one_mul] using
        intervalIntegral.smul_integral_comp_mul_right (a := 0) (b := 1)
          (fun s => s ^ c • f s) ξ

theorem regularPrimitive_eq_div (c : ℕ) (f : ℝ → E) {ξ : ℝ} (hξ : ξ ≠ 0) :
    regularPrimitive c f ξ = (ξ ^ c)⁻¹ • ∫ s in (0 : ℝ)..ξ, s ^ c • f s := by
  rw [← regularPrimitive_integratingFactor]
  simp only [inv_smul_smul₀ (pow_ne_zero c hξ)]

/-- The axis derivative is the normalized average at zero. -/
theorem regularPrimitive_hasDerivAt_zero (c : ℕ) {f : ℝ → E} (hf : Continuous f) :
    HasDerivAt (regularPrimitive c f) (weightedMean c f 0) 0 := by
  rw [hasDerivAt_iff_tendsto_slope_zero]
  apply ((weightedMean_continuous c hf).continuousAt.tendsto.mono_left nhdsWithin_le_nhds).congr'
  filter_upwards [self_mem_nhdsWithin] with t ht
  have hne : t ≠ 0 := by simpa only [mem_compl_iff, mem_singleton_iff] using ht
  simp only [zero_add, regularPrimitive, zero_smul, sub_zero, inv_smul_smul₀ hne]

theorem weightedMean_norm_le (c : ℕ) (f : ℝ → E) (ξ M : ℝ)
    (hf : ∀ t ∈ Icc (0 : ℝ) 1, ‖f (t * ξ)‖ ≤ M) :
    ‖weightedMean c f ξ‖ ≤ M := by
  have h := intervalIntegral.norm_integral_le_of_norm_le_const (a := (0 : ℝ)) (b := 1)
    (C := M) (f := fun t => (t ^ c) • f (t * ξ)) ?_
  · simpa only [weightedMean, sub_zero, abs_one, mul_one] using h
  intro t ht
  have ht0 : t ∈ Ioc (0 : ℝ) 1 := by simpa only [uIoc_of_le zero_le_one] using ht
  have ht' : t ∈ Icc (0 : ℝ) 1 := ⟨ht0.1.le, ht0.2⟩
  rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (pow_nonneg ht'.1 c)]
  exact (mul_le_mul (pow_le_one₀ ht'.1 ht'.2) (hf t ht') (norm_nonneg _) zero_le_one).trans_eq
    (one_mul M)

theorem regularPrimitive_norm_le (c : ℕ) (f : ℝ → E) (ξ M : ℝ)
    (hf : ∀ t ∈ Icc (0 : ℝ) 1, ‖f (t * ξ)‖ ≤ M) :
    ‖regularPrimitive c f ξ‖ ≤ |ξ| * M := by
  rw [regularPrimitive, norm_smul, Real.norm_eq_abs]
  exact mul_le_mul_of_nonneg_left (weightedMean_norm_le c f ξ M hf) (abs_nonneg ξ)

/-- Differentiating the integrating-factor formula gives a nonsingular
formula for the radial derivative away from the axis. -/
theorem regularPrimitive_hasDerivAt_ne_zero [CompleteSpace E] (c : ℕ)
    {f : ℝ → E} (hf : Continuous f) {ξ : ℝ} (hξ : ξ ≠ 0) :
    HasDerivAt (regularPrimitive c f)
      (f ξ - (c : ℝ) • weightedMean c f ξ) ξ := by
  have hg : Continuous (fun s : ℝ => s ^ c • f s) := (continuous_id.pow c).smul hf
  have hi := (hasDerivAt_pow c ξ).fun_inv (pow_ne_zero c hξ)
  have hd := hi.fun_smul (hg.integral_hasStrictDerivAt 0 ξ).hasDerivAt
  have he : regularPrimitive c f =ᶠ[𝓝 ξ]
      (fun x : ℝ => (x ^ c)⁻¹ • ∫ s in (0 : ℝ)..x, s ^ c • f s) := by
    filter_upwards [eventually_ne_nhds hξ] with x hx
    exact regularPrimitive_eq_div c f hx
  have hfactor : (-(c : ℝ) * ξ ^ (c - 1) / (ξ ^ c) ^ 2) * (ξ ^ c * ξ) = -(c : ℝ) := by
    cases c with
    | zero => simp
    | succ n =>
        simp only [Nat.add_sub_cancel, pow_succ]
        field_simp
  convert! hd.congr_of_eventuallyEq he using 1
  rw [inv_smul_smul₀ (pow_ne_zero c hξ), ← regularPrimitive_integratingFactor c f ξ,
    regularPrimitive, smul_smul, smul_smul]
  rw [neg_mul] at hfactor
  rw [← mul_assoc] at hfactor
  rw [hfactor, neg_smul]
  simp only [sub_eq_add_neg]

/-- The same derivative formula is valid at zero; no singular division
is used to define or differentiate the solution there. -/
theorem regularPrimitive_hasDerivAt [CompleteSpace E] (c : ℕ)
    {f : ℝ → E} (hf : Continuous f) (ξ : ℝ) :
    HasDerivAt (regularPrimitive c f)
      (f ξ - (c : ℝ) • weightedMean c f ξ) ξ := by
  by_cases hξ : ξ = 0
  · subst ξ
    have hd := regularPrimitive_hasDerivAt_zero c hf
    convert! hd using 1
    rw [weightedMean_zero]
    calc
      _ = ((1 : ℝ) - (c : ℝ) * (1 / ((c : ℝ) + 1))) • f 0 := by
        rw [sub_smul, one_smul, mul_smul]
      _ = _ := by
        congr 1
        field_simp; ring
  · exact regularPrimitive_hasDerivAt_ne_zero c hf hξ

theorem regularPrimitive_equation [CompleteSpace E] (c : ℕ)
    {f : ℝ → E} (hf : Continuous f) {ξ : ℝ} (hξ : ξ ≠ 0) :
    deriv (regularPrimitive c f) ξ + ((c : ℝ) / ξ) • regularPrimitive c f ξ = f ξ := by
  rw [(regularPrimitive_hasDerivAt c hf ξ).deriv, regularPrimitive, smul_smul,
    div_mul_cancel₀ _ hξ, sub_add_cancel]

theorem regularPrimitive_derivative_continuous [CompleteSpace E] (c : ℕ)
    {f : ℝ → E} (hf : Continuous f) : Continuous (deriv (regularPrimitive c f)) := by
  have he : deriv (regularPrimitive c f) = fun ξ => f ξ - (c : ℝ) • weightedMean c f ξ :=
    funext fun ξ => (regularPrimitive_hasDerivAt c hf ξ).deriv
  rw [he]
  exact hf.sub (continuous_const.smul (weightedMean_continuous c hf))

end RadialInverse

/-- The six actual components of the first-order radial system. -/
abbrev Vec := Fin 6 → ℂ

/-- Continuous paths on the full fixed radial interval. -/
abbrev Path (R : ℝ) := C(Icc (0 : ℝ) R, Vec)

/-- Coefficient path: an abbreviation for `C(Icc (0 : ℝ) R, Vec →L[ℂ] Vec)`. -/
abbrev CoefficientPath (R : ℝ) := C(Icc (0 : ℝ) R, Vec →L[ℂ] Vec)

/-- Extend path, given by `f (projIcc 0 R hR ξ)`. -/
def extendPath {R : ℝ} (hR : 0 ≤ R) (f : Path R) (ξ : ℝ) : Vec :=
  f (projIcc 0 R hR ξ)

theorem extendPath_continuous {R : ℝ} (hR : 0 ≤ R) (f : Path R) :
    Continuous (extendPath hR f) :=
  f.continuous.comp continuous_projIcc

theorem extendPath_apply {R : ℝ} (hR : 0 ≤ R) (f : Path R) (ξ : Icc (0 : ℝ) R) :
    extendPath hR f ξ = f ξ := by simp only [extendPath, projIcc_val]

/-- Path inverse value as an element of `Path R`. -/
def pathInverseValue {R : ℝ} (hR : 0 ≤ R) (c : Fin 6 → ℕ) (f : Path R) : Path R :=
  ⟨fun ξ i => regularPrimitive (c i) (fun s => extendPath hR f s i) ξ,
    continuous_pi fun i =>
      (regularPrimitive_continuous (c i)
        ((continuous_apply i).comp (extendPath_continuous hR f))).comp continuous_subtype_val⟩

theorem norm_pathInverseValue_le {R : ℝ} (hR : 0 ≤ R)
    (c : Fin 6 → ℕ) (f : Path R) : ‖pathInverseValue hR c f‖ ≤ R * ‖f‖ := by
  apply (ContinuousMap.norm_le _ (mul_nonneg hR (norm_nonneg f))).mpr
  intro ξ
  apply (pi_norm_le_iff_of_nonneg (mul_nonneg hR (norm_nonneg f))).mpr
  intro i
  change ‖regularPrimitive (c i) (fun s => extendPath hR f s i) ξ‖ ≤ R * ‖f‖
  refine (regularPrimitive_norm_le (c i) _ ξ ‖f‖ ?_).trans ?_
  · intro t ht
    exact (norm_le_pi_norm (extendPath hR f (t * ξ)) i).trans (f.norm_coe_le_norm _)
  · exact mul_le_mul_of_nonneg_right
      ((abs_of_nonneg ξ.2.1).le.trans ξ.2.2) (norm_nonneg f)

/-- The diagonal integral operator is bounded and complex linear on actual paths. -/
def pathInverse {R : ℝ} (hR : 0 ≤ R) (c : Fin 6 → ℕ) : Path R →L[ℂ] Path R :=
  LinearMap.mkContinuous {
    toFun := pathInverseValue hR c
    map_add' := by
      intro f g
      ext ξ i
      change (ξ : ℝ) • (∫ t in (0 : ℝ)..1,
          (t ^ c i) • (extendPath hR f (t * ξ) i + extendPath hR g (t * ξ) i)) = _
      simp only [smul_add]
      rw [intervalIntegral.integral_add, smul_add]
      · rfl
      · exact ((continuous_id.pow (c i)).smul
          (((continuous_apply i).comp (extendPath_continuous hR f)).comp
            (continuous_id.mul continuous_const))).intervalIntegrable _ _
      · exact ((continuous_id.pow (c i)).smul
          (((continuous_apply i).comp (extendPath_continuous hR g)).comp
            (continuous_id.mul continuous_const))).intervalIntegrable _ _
    map_smul' := by
      intro a f
      ext ξ i
      change (ξ : ℝ) • (∫ t in (0 : ℝ)..1,
          (t ^ c i) • (a • extendPath hR f (t * ξ) i)) =
        a • ((ξ : ℝ) • ∫ t in (0 : ℝ)..1, (t ^ c i) • extendPath hR f (t * ξ) i)
      conv_lhs => arg 2; arg 1; ext t; rw [smul_comm (t ^ c i) a]
      rw [intervalIntegral.integral_smul, smul_comm]
  } R (norm_pathInverseValue_le hR c)

theorem pathInverse_apply {R : ℝ} (hR : 0 ≤ R) (c : Fin 6 → ℕ)
    (f : Path R) (ξ : Icc (0 : ℝ) R) (i : Fin 6) :
    pathInverse hR c f ξ i =
      (ξ : ℝ) • ∫ t in (0 : ℝ)..1, (t ^ c i) • extendPath hR f (t * ξ) i := rfl

/-- Coefficient action value, given by `⟨fun ξ => A ξ (f ξ), A.continuous.clm_apply
f.continuous⟩`. -/
noncomputable def coefficientActionValue {R : ℝ} (A : CoefficientPath R) (f : Path R) : Path R :=
  ⟨fun ξ => A ξ (f ξ), A.continuous.clm_apply f.continuous⟩

theorem norm_coefficientActionValue_le {R : ℝ} (A : CoefficientPath R) (f : Path R) :
    ‖coefficientActionValue A f‖ ≤ ‖A‖ * ‖f‖ := by
  apply (ContinuousMap.norm_le _ (mul_nonneg (norm_nonneg A) (norm_nonneg f))).mpr
  intro ξ
  exact ((A ξ).le_opNorm (f ξ)).trans
    (mul_le_mul (A.norm_coe_le_norm ξ) (f.norm_coe_le_norm ξ)
      (norm_nonneg _) (norm_nonneg _))

/-- Coefficient action linear, bundling `toFun`, `toFun`, `map_add`, `map_smul` and the required
compatibility proofs. -/
def coefficientActionLinear {R : ℝ} : CoefficientPath R →ₗ[ℂ] Path R →ₗ[ℂ] Path R where
  toFun A := {
    toFun := coefficientActionValue A
    map_add' := by intro f g; ext ξ i; exact congrFun (map_add (A ξ) (f ξ) (g ξ)) i
    map_smul' := by intro a f; ext ξ i; exact congrFun (map_smul (A ξ) a (f ξ)) i }
  map_add' := by intro A B; ext f ξ i; rfl
  map_smul' := by intro a A; ext f ξ i; rfl

/-- Pointwise matrix action is a genuine bounded bilinear map of path spaces. -/
def coefficientAction {R : ℝ} : CoefficientPath R →L[ℂ] Path R →L[ℂ] Path R :=
  (coefficientActionLinear (R := R)).mkContinuous₂
    (𝕜 := ℂ) (𝕜₂ := ℂ) (𝕜₃ := ℂ)
    (E := CoefficientPath R) (F := Path R) (G := Path R) 1
    (fun A f => by
      change ‖coefficientActionValue A f‖ ≤ 1 * ‖A‖ * ‖f‖
      simpa only [one_mul] using norm_coefficientActionValue_le A f)

theorem coefficientAction_apply {R : ℝ} (A : CoefficientPath R) (f : Path R)
    (ξ : Icc (0 : ℝ) R) : coefficientAction A f ξ = A ξ (f ξ) := rfl

/-- Path letter, defined pointwise by `pathInverse hR c (if b then coefficientAction (A₁ z)
(deriv F z) else coefficientAction (A₀ z) (F z))`. -/
def pathLetter {R : ℝ} (hR : 0 ≤ R) (c : Fin 6 → ℕ)
    (A₀ A₁ : ℂ → CoefficientPath R) (b : Bool) (F : ℂ → Path R) : ℂ → Path R :=
  fun z => pathInverse hR c
    (if b then coefficientAction (A₁ z) (deriv F z) else coefficientAction (A₀ z) (F z))

/-- Path word as an element of `w, F => pathLetter hR c A₀ A₁ b (pathWord hR c A₀ A₁ w F)`. -/
def pathWord {R : ℝ} (hR : 0 ≤ R) (c : Fin 6 → ℕ)
    (A₀ A₁ : ℂ → CoefficientPath R) : List Bool → (ℂ → Path R) → ℂ → Path R
  | [], F => F
  | b :: w, F => pathLetter hR c A₀ A₁ b (pathWord hR c A₀ A₁ w F)

theorem pathLetter_holomorphic {R : ℝ} (hR : 0 ≤ R) (c : Fin 6 → ℕ)
    {A₀ A₁ : ℂ → CoefficientPath R} {F : ℂ → Path R} {U : Set ℂ}
    (hU : IsOpen U) (hA₀ : DifferentiableOn ℂ A₀ U) (hA₁ : DifferentiableOn ℂ A₁ U)
    (hF : DifferentiableOn ℂ F U) (b : Bool) :
    DifferentiableOn ℂ (pathLetter hR c A₀ A₁ b F) U := by
  have hAction : Differentiable ℂ (coefficientAction (R := R)) :=
    ContinuousLinearMap.differentiable (𝕜 := ℂ)
      (E := CoefficientPath R) (F := Path R →L[ℂ] Path R) coefficientAction
  cases b
  · exact (pathInverse hR c).differentiable.comp_differentiableOn
      ((hAction.comp_differentiableOn hA₀).clm_apply hF)
  · exact (pathInverse hR c).differentiable.comp_differentiableOn
      ((hAction.comp_differentiableOn hA₁).clm_apply (hF.deriv hU))

/-- Every finite word is holomorphic before any convergence is asserted. -/
theorem pathWord_holomorphic {R : ℝ} (hR : 0 ≤ R) (c : Fin 6 → ℕ)
    {A₀ A₁ : ℂ → CoefficientPath R} {F : ℂ → Path R} {U : Set ℂ}
    (hU : IsOpen U) (hA₀ : DifferentiableOn ℂ A₀ U) (hA₁ : DifferentiableOn ℂ A₁ U)
    (hF : DifferentiableOn ℂ F U) (w : List Bool) :
    DifferentiableOn ℂ (pathWord hR c A₀ A₁ w F) U := by
  induction w with
  | nil => exact hF
  | cons b w ih => exact pathLetter_holomorphic hR c hU hA₀ hA₁ ih b

/-- Path evaluation, given by `(ContinuousLinearMap.proj i).comp (ContinuousMap.evalCLM ℂ ξ)`. -/
def pathEvaluation {R : ℝ} (ξ : Icc (0 : ℝ) R) (i : Fin 6) : Path R →L[ℂ] ℂ :=
  (ContinuousLinearMap.proj i).comp (ContinuousMap.evalCLM ℂ ξ)

theorem pathEvaluation_apply {R : ℝ} (ξ : Icc (0 : ℝ) R) (i : Fin 6) (f : Path R) :
    pathEvaluation ξ i f = f ξ i := rfl

/-- Coordinate evaluation commutes with the genuine complex derivative. -/
theorem pathEvaluation_deriv {R : ℝ} {F : ℂ → Path R} {z : ℂ}
    (hF : DifferentiableAt ℂ F z) (ξ : Icc (0 : ℝ) R) (i : Fin 6) :
    deriv (fun w => F w ξ i) z = deriv F z ξ i := by
  exact ((pathEvaluation ξ i).hasFDerivAt.comp_hasDerivAt z hF.hasDerivAt).deriv

/-- Raw field, defined pointwise by `extendPath hR (F z) r`. -/
def rawField {R : ℝ} (hR : 0 ≤ R) (F : ℂ → Path R) : VolterraAnalyticBounds.Field :=
  fun r z => extendPath hR (F z) r

/-- Raw coefficient, defined pointwise by `LinearMap.toMatrix' (A z (projIcc 0 R hR
r)).toLinearMap`. -/
def rawCoefficient {R : ℝ} (hR : 0 ≤ R) (A : ℂ → CoefficientPath R) :
    VolterraAnalyticBounds.Coeff :=
  fun r z => LinearMap.toMatrix' (A z (projIcc 0 R hR r)).toLinearMap

theorem rawCoefficient_mulVec {R : ℝ} (hR : 0 ≤ R) (A : ℂ → CoefficientPath R)
    (r : ℝ) (z : ℂ) (v : Vec) :
    (rawCoefficient hR A r z).mulVec v = A z (projIcc 0 R hR r) v := by
  rw [rawCoefficient, ← Matrix.toLin'_apply, Matrix.toLin'_toMatrix']
  rfl

theorem rawField_deriv {R : ℝ} (hR : 0 ≤ R) {F : ℂ → Path R} {z : ℂ}
    (hF : DifferentiableAt ℂ F z) (r : ℝ) :
    VolterraAnalyticBounds.parameterDeriv (rawField hR F) r z =
      rawField hR (deriv F) r z := by
  funext i
  exact pathEvaluation_deriv hF (projIcc 0 R hR r) i

theorem scaled_radius_mem {R r t : ℝ} (hr : r ∈ Icc (0 : ℝ) R)
    (ht : t ∈ Icc (0 : ℝ) 1) : t * r ∈ Icc (0 : ℝ) R :=
  ⟨mul_nonneg ht.1 hr.1, (mul_le_of_le_one_left hr.1 ht.2).trans hr.2⟩

/-- Every path letter is the actual integral/derivative letter on its radial interval. -/
theorem rawField_pathLetter {R : ℝ} (hR : 0 ≤ R)
    (A₀ A₁ : ℂ → CoefficientPath R) {F : ℂ → Path R} {z : ℂ}
    (hF : DifferentiableAt ℂ F z) (b : Bool) {r : ℝ} (hr : r ∈ Icc (0 : ℝ) R) :
    rawField hR (pathLetter hR VolterraAnalyticBounds.exponent A₀ A₁ b F) r z =
      VolterraAnalyticBounds.letter (rawCoefficient hR A₀) (rawCoefficient hR A₁) b
        (rawField hR F) r z := by
  change pathLetter hR VolterraAnalyticBounds.exponent A₀ A₁ b F z (projIcc 0 R hR r) = _
  rw [projIcc_of_mem hR hr]
  cases b <;> funext i <;>
    simp only [pathLetter, Bool.false_eq_true, ite_false, ite_true, pathInverse_apply,
      VolterraAnalyticBounds.letter, VolterraAnalyticBounds.radialInverse]
  · congr 1
    apply intervalIntegral.integral_congr
    intro t ht
    simp only [VolterraAnalyticBounds.matrixAction, rawCoefficient_mulVec,
      rawField, extendPath, coefficientAction_apply]
  · congr 1
    apply intervalIntegral.integral_congr
    intro t ht
    simp only [VolterraAnalyticBounds.matrixAction, rawCoefficient_mulVec, rawField_deriv hR hF,
      rawField, extendPath, coefficientAction_apply]

theorem letter_congrOn {R : ℝ} {U : Set ℂ} (hU : IsOpen U)
    (A₀ A₁ : VolterraAnalyticBounds.Coeff) (b : Bool)
    {F G : VolterraAnalyticBounds.Field}
    (hFG : ∀ r ∈ Icc (0 : ℝ) R, ∀ z ∈ U, F r z = G r z)
    {r : ℝ} (hr : r ∈ Icc (0 : ℝ) R) {z : ℂ} (hz : z ∈ U) :
    VolterraAnalyticBounds.letter A₀ A₁ b F r z =
      VolterraAnalyticBounds.letter A₀ A₁ b G r z := by
  have hd (s : ℝ) (hs : s ∈ Icc (0 : ℝ) R) :
      VolterraAnalyticBounds.parameterDeriv F s z =
        VolterraAnalyticBounds.parameterDeriv G s z := by
    funext i
    apply Filter.EventuallyEq.deriv_eq
    filter_upwards [hU.mem_nhds hz] with w hw
    exact congrFun (hFG s hs w hw) i
  cases b <;> funext i <;>
    simp only [VolterraAnalyticBounds.letter, Bool.false_eq_true, ite_false, ite_true,
      VolterraAnalyticBounds.radialInverse]
  · congr 1
    apply intervalIntegral.integral_congr
    intro t ht
    have ht' : t ∈ Icc (0 : ℝ) 1 := by simpa only [uIcc_of_le zero_le_one] using ht
    simp only [VolterraAnalyticBounds.matrixAction, hFG (t * r) (scaled_radius_mem hr ht') z hz]
  · congr 1
    apply intervalIntegral.integral_congr
    intro t ht
    have ht' : t ∈ Icc (0 : ℝ) 1 := by simpa only [uIcc_of_le zero_le_one] using ht
    simp only [VolterraAnalyticBounds.matrixAction, hd (t * r) (scaled_radius_mem hr ht')]

/-- The finite path construction represents precisely the raw Volterra words. -/
theorem rawField_pathWord {R : ℝ} (hR : 0 ≤ R)
    {A₀ A₁ : ℂ → CoefficientPath R} {F : ℂ → Path R} {U : Set ℂ}
    (hU : IsOpen U) (hA₀ : DifferentiableOn ℂ A₀ U) (hA₁ : DifferentiableOn ℂ A₁ U)
    (hF : DifferentiableOn ℂ F U) (w : List Bool)
    {r : ℝ} (hr : r ∈ Icc (0 : ℝ) R) {z : ℂ} (hz : z ∈ U) :
    VolterraAnalyticBounds.word (rawCoefficient hR A₀) (rawCoefficient hR A₁) w
        (rawField hR F) r z =
      rawField hR (pathWord hR VolterraAnalyticBounds.exponent A₀ A₁ w F) r z := by
  induction w generalizing r z with
  | nil => rfl
  | cons b w ih =>
      rw [pathWord, rawField_pathLetter hR A₀ A₁
        ((pathWord_holomorphic hR _ hU hA₀ hA₁ hF w).differentiableAt (hU.mem_nhds hz)) b hr]
      exact letter_congrOn hU _ _ b (fun r hr z hz => ih hr hz) hr hz

theorem raw_word_analytic {R : ℝ} (hR : 0 ≤ R)
    {A₀ A₁ : ℂ → CoefficientPath R} {F : ℂ → Path R} {U : Set ℂ}
    (hU : IsOpen U) (hA₀ : DifferentiableOn ℂ A₀ U) (hA₁ : DifferentiableOn ℂ A₁ U)
    (hF : DifferentiableOn ℂ F U) {center : ℂ} {ρ : ℝ}
    (hDisk : Metric.closedBall center ρ ⊆ U) (w : List Bool) :
    VolterraAnalyticBounds.AnalyticField
      (VolterraAnalyticBounds.word (rawCoefficient hR A₀) (rawCoefficient hR A₁) w
        (rawField hR F)) R center ρ := by
  intro r hr i
  have hp := pathWord_holomorphic hR VolterraAnalyticBounds.exponent hU hA₀ hA₁ hF w
  have he := (pathEvaluation (projIcc 0 R hR r) i).differentiable.comp_differentiableOn hp
  have hraw : DifferentiableOn ℂ
      (fun z => VolterraAnalyticBounds.word (rawCoefficient hR A₀) (rawCoefficient hR A₁) w
        (rawField hR F) r z i) U := by
    apply he.congr
    intro z hz
    exact congrFun (rawField_pathWord hR hU hA₀ hA₁ hF w hr hz) i
  exact (hraw.analyticOnNhd hU).mono hDisk

/-- Binary words as an element of `ℕ → List (List Bool) | 0 => [[]] | k + 1 => (binaryWords
k).map (List.cons false) ++ (binaryWords k).map (List.cons true)`. -/
def binaryWords : ℕ → List (List Bool)
  | 0 => [[]]
  | k + 1 => (binaryWords k).map (List.cons false) ++ (binaryWords k).map (List.cons true)

theorem binaryWords_length (k : ℕ) : (binaryWords k).length = 2 ^ k := by
  induction k with
  | zero => rfl
  | succ k ih => simp [binaryWords, ih, pow_succ, Nat.mul_two]

theorem length_of_mem_binaryWords {k : ℕ} {w : List Bool} (hw : w ∈ binaryWords k) :
    w.length = k := by
  induction k generalizing w with
  | zero => simpa [binaryWords] using hw
  | succ k ih =>
      simp only [binaryWords, List.mem_append, List.mem_map] at hw
      rcases hw with ⟨v, hv, rfl⟩ | ⟨v, hv, rfl⟩ <;>
        simpa only [List.length_cons] using congrArg Nat.succ (ih hv)

theorem list_sum_eval {X E : Type*} [AddCommMonoid E] (l : List (X → E)) (x : X) :
    l.sum x = (l.map (fun f => f x)).sum := by
  induction l with
  | nil => rfl
  | cons f l ih =>
      simpa only [List.sum_cons, List.map_cons, Pi.add_apply] using congrArg (f x + ·) ih

theorem norm_list_sum_le {E : Type*} [SeminormedAddCommGroup E]
    (l : List E) (M : ℝ) (h : ∀ x ∈ l, ‖x‖ ≤ M) :
    ‖l.sum‖ ≤ (l.length : ℝ) * M := by
  induction l with
  | nil => simp
  | cons x l ih =>
      simp only [List.sum_cons, List.length_cons, Nat.cast_add, Nat.cast_one]
      calc
        ‖x + l.sum‖ ≤ ‖x‖ + ‖l.sum‖ := norm_add_le _ _
        _ ≤ M + (l.length : ℝ) * M :=
          add_le_add (h x (List.mem_cons_self ..)) (ih (fun y hy => h y (List.mem_cons_of_mem _
              hy)))
        _ = _ := by ring

theorem holomorphic_list_sum {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (l : List (ℂ → E)) {U : Set ℂ} (h : ∀ f ∈ l, DifferentiableOn ℂ f U) :
    DifferentiableOn ℂ l.sum U := by
  induction l with
  | nil => exact differentiableOn_const _
  | cons f l ih =>
      exact (h f (List.mem_cons_self ..)).add (ih (fun g hg => h g (List.mem_cons_of_mem _ hg)))

/-- Layer, given by `((binaryWords k).map (fun w => pathWord hR c A₀ A₁ w F)).sum`. -/
def layer {R : ℝ} (hR : 0 ≤ R) (c : Fin 6 → ℕ)
    (A₀ A₁ : ℂ → CoefficientPath R) (F : ℂ → Path R) (k : ℕ) : ℂ → Path R :=
  ((binaryWords k).map (fun w => pathWord hR c A₀ A₁ w F)).sum

theorem layer_holomorphic {R : ℝ} (hR : 0 ≤ R) (c : Fin 6 → ℕ)
    {A₀ A₁ : ℂ → CoefficientPath R} {F : ℂ → Path R} {U : Set ℂ}
    (hU : IsOpen U) (hA₀ : DifferentiableOn ℂ A₀ U) (hA₁ : DifferentiableOn ℂ A₁ U)
    (hF : DifferentiableOn ℂ F U) (k : ℕ) :
    DifferentiableOn ℂ (layer hR c A₀ A₁ F k) U := by
  apply holomorphic_list_sum
  intro g hg
  rcases List.mem_map.mp hg with ⟨w, hw, rfl⟩
  exact pathWord_holomorphic hR c hU hA₀ hA₁ hF w

@[simp] theorem layer_zero {R : ℝ} (hR : 0 ≤ R) (c : Fin 6 → ℕ)
    (A₀ A₁ : ℂ → CoefficientPath R) (F : ℂ → Path R) :
    layer hR c A₀ A₁ F 0 = F := by simp [layer, binaryWords, pathWord]

theorem pathLetter_add {R : ℝ} (hR : 0 ≤ R) (c : Fin 6 → ℕ)
    (A₀ A₁ : ℂ → CoefficientPath R) (b : Bool) {F G : ℂ → Path R} {z : ℂ}
    (hF : DifferentiableAt ℂ F z) (hG : DifferentiableAt ℂ G z) :
    pathLetter hR c A₀ A₁ b (F + G) z =
      pathLetter hR c A₀ A₁ b F z + pathLetter hR c A₀ A₁ b G z := by
  cases b <;> simp only [pathLetter, Bool.false_eq_true, ite_false, ite_true, Pi.add_apply]
  · simp only [map_add]
  · change pathInverse hR c (coefficientAction (A₁ z) (deriv (fun w => F w + G w) z)) = _
    rw [deriv_fun_add hF hG]
    simp only [map_add]

theorem pathLetter_list_sum {R : ℝ} (hR : 0 ≤ R) (c : Fin 6 → ℕ)
    (A₀ A₁ : ℂ → CoefficientPath R) (b : Bool) (l : List (ℂ → Path R))
    {U : Set ℂ} (hU : IsOpen U) (h : ∀ F ∈ l, DifferentiableOn ℂ F U)
    {z : ℂ} (hz : z ∈ U) :
    (l.map (pathLetter hR c A₀ A₁ b)).sum z = pathLetter hR c A₀ A₁ b l.sum z := by
  induction l with
  | nil => cases b <;> simp [pathLetter]
  | cons F l ih =>
      rw [List.map_cons, List.sum_cons, Pi.add_apply, List.sum_cons,
        pathLetter_add hR c A₀ A₁ b
          ((h F (List.mem_cons_self ..)).differentiableAt (hU.mem_nhds hz))
          ((holomorphic_list_sum l (fun G hG => h G (List.mem_cons_of_mem _ hG))).differentiableAt
            (hU.mem_nhds hz)), ih (fun G hG => h G (List.mem_cons_of_mem _ hG))]

theorem layer_succ {R : ℝ} (hR : 0 ≤ R) (c : Fin 6 → ℕ)
    {A₀ A₁ : ℂ → CoefficientPath R} {F : ℂ → Path R} {U : Set ℂ}
    (hU : IsOpen U) (hA₀ : DifferentiableOn ℂ A₀ U) (hA₁ : DifferentiableOn ℂ A₁ U)
    (hF : DifferentiableOn ℂ F U) (k : ℕ) {z : ℂ} (hz : z ∈ U) :
    layer hR c A₀ A₁ F (k + 1) z =
      pathLetter hR c A₀ A₁ false (layer hR c A₀ A₁ F k) z +
        pathLetter hR c A₀ A₁ true (layer hR c A₀ A₁ F k) z := by
  have hl : ∀ G ∈ (binaryWords k).map (fun w => pathWord hR c A₀ A₁ w F),
      DifferentiableOn ℂ G U := by
    intro G hG
    rcases List.mem_map.mp hG with ⟨w, hw, rfl⟩
    exact pathWord_holomorphic hR c hU hA₀ hA₁ hF w
  have hfalse := pathLetter_list_sum hR c A₀ A₁ false _ hU hl hz
  have htrue := pathLetter_list_sum hR c A₀ A₁ true _ hU hl hz
  simpa only [layer, binaryWords, List.map_append, List.sum_append, Pi.add_apply,
    List.map_map, Function.comp_def, pathWord] using congrArg₂ (· + ·) hfalse htrue

theorem rawField_bound {R : ℝ} (hR : 0 ≤ R) (F : ℂ → Path R)
    {center : ℂ} {ρ B : ℝ} (hF : ∀ z ∈ Metric.closedBall center ρ, ‖F z‖ ≤ B) :
    VolterraAnalyticBounds.RadialBound (rawField hR F) R center ρ B 0 := by
  intro r hr z hz i
  have h := (norm_le_pi_norm (F z (projIcc 0 R hR r)) i).trans
    ((F z).norm_coe_le_norm (projIcc 0 R hR r))
  simpa only [rawField, extendPath, pow_zero, Nat.factorial_zero, Nat.cast_one,
    mul_one, div_one] using h.trans (hF z hz)

theorem rawCoefficient_bound {R : ℝ} (hR : 0 ≤ R) (A : ℂ → CoefficientPath R)
    {center : ℂ} {ρ M : ℝ} (hA : ∀ z ∈ Metric.closedBall center ρ, ‖A z‖ ≤ M) :
    VolterraAnalyticBounds.MatrixBound (rawCoefficient hR A) R center ρ (6 * M) := by
  intro r hr z hz i
  calc
    ∑ j, ‖rawCoefficient hR A r z i j‖ ≤ ∑ _j : Fin 6, M := by
      apply Finset.sum_le_sum
      intro j hj
      change ‖A z (projIcc 0 R hR r) (Pi.single j 1) i‖ ≤ M
      calc
        _ ≤ ‖A z (projIcc 0 R hR r) (Pi.single j 1)‖ := norm_le_pi_norm _ i
        _ ≤ ‖A z (projIcc 0 R hR r)‖ * ‖(Pi.single j 1 : Vec)‖ :=
          (A z (projIcc 0 R hR r)).le_opNorm (Pi.single j 1 : Vec)
        _ = ‖A z (projIcc 0 R hR r)‖ := by rw [Pi.norm_single, norm_one, mul_one]
        _ ≤ ‖A z‖ := (A z).norm_coe_le_norm _
        _ ≤ M := hA z hz
    _ = 6 * M := by simp

theorem pathWord_bound {R : ℝ} (hR : 0 ≤ R)
    {A₀ A₁ : ℂ → CoefficientPath R} {F : ℂ → Path R} {U : Set ℂ}
    (hU : IsOpen U) (hA₀ : DifferentiableOn ℂ A₀ U) (hA₁ : DifferentiableOn ℂ A₁ U)
    (hF : DifferentiableOn ℂ F U) {center : ℂ} {ρ σ B M : ℝ}
    (hDisk : Metric.closedBall center σ ⊆ U) (hgap : ρ < σ)
    (hB : 0 ≤ B) (hM : 0 ≤ M)
    (hshape : VolterraAnalyticBounds.DerivativeShape (rawCoefficient hR A₁))
    (hbA₀ : VolterraAnalyticBounds.MatrixBound (rawCoefficient hR A₀) R center σ M)
    (hbA₁ : VolterraAnalyticBounds.MatrixBound (rawCoefficient hR A₁) R center σ M)
    (hbF : ∀ z ∈ Metric.closedBall center σ, ‖F z‖ ≤ B)
    (w : List Bool) {z : ℂ} (hz : z ∈ Metric.closedBall center ρ) :
    ‖pathWord hR VolterraAnalyticBounds.exponent A₀ A₁ w F z‖ ≤
      B * VolterraAnalyticBounds.wordMajorant (M * R) (max 1 (σ - ρ)⁻¹) w.length := by
  have hc : 0 ≤ B * VolterraAnalyticBounds.wordMajorant (M * R) (max 1 (σ - ρ)⁻¹) w.length :=
    mul_nonneg hB (VolterraAnalyticBounds.wordMajorant_nonneg (mul_nonneg hM hR)
      (le_trans zero_le_one (le_max_left _ _)) _)
  apply (ContinuousMap.norm_le _ hc).mpr
  intro ξ
  apply (pi_norm_le_iff_of_nonneg hc).mpr
  intro i
  have hb := VolterraAnalyticBounds.norm_word_le hB hM hR hgap hshape hbA₀ hbA₁
    (rawField_bound hR F hbF) (fun v => raw_word_analytic hR hU hA₀ hA₁ hF hDisk v)
    w ξ.2 hz i
  rw [rawField_pathWord hR hU hA₀ hA₁ hF w ξ.2
    (hDisk (Metric.closedBall_subset_closedBall hgap.le hz))] at hb
  simpa only [rawField, extendPath, projIcc_val] using hb

theorem layer_bound {R : ℝ} (hR : 0 ≤ R)
    {A₀ A₁ : ℂ → CoefficientPath R} {F : ℂ → Path R} {U : Set ℂ}
    (hU : IsOpen U) (hA₀ : DifferentiableOn ℂ A₀ U) (hA₁ : DifferentiableOn ℂ A₁ U)
    (hF : DifferentiableOn ℂ F U) {center : ℂ} {ρ σ B M : ℝ}
    (hDisk : Metric.closedBall center σ ⊆ U) (hgap : ρ < σ)
    (hB : 0 ≤ B) (hM : 0 ≤ M)
    (hshape : VolterraAnalyticBounds.DerivativeShape (rawCoefficient hR A₁))
    (hbA₀ : VolterraAnalyticBounds.MatrixBound (rawCoefficient hR A₀) R center σ M)
    (hbA₁ : VolterraAnalyticBounds.MatrixBound (rawCoefficient hR A₁) R center σ M)
    (hbF : ∀ z ∈ Metric.closedBall center σ, ‖F z‖ ≤ B)
    (k : ℕ) {z : ℂ} (hz : z ∈ Metric.closedBall center ρ) :
    ‖layer hR VolterraAnalyticBounds.exponent A₀ A₁ F k z‖ ≤
      B * 2 ^ k * VolterraAnalyticBounds.wordMajorant (M * R) (max 1 (σ - ρ)⁻¹) k := by
  rw [layer, list_sum_eval]
  refine (norm_list_sum_le _
    (B * VolterraAnalyticBounds.wordMajorant (M * R) (max 1 (σ - ρ)⁻¹) k) ?_).trans_eq ?_
  · intro x hx
    simp only [List.mem_map] at hx
    rcases hx with ⟨G, ⟨w, hw, rfl⟩, rfl⟩
    have hb := pathWord_bound hR hU hA₀ hA₁ hF hDisk hgap hB hM hshape hbA₀ hbA₁ hbF w hz
    simpa only [length_of_mem_binaryWords hw] using hb
  · simp only [List.length_map, binaryWords_length, Nat.cast_pow, Nat.cast_ofNat]
    ring

/-- Solution series, defined pointwise by `∑' k : ℕ, layer hR VolterraAnalyticBounds.exponent A₀
A₁ F k z`. -/
def solutionSeries {R : ℝ} (hR : 0 ≤ R)
    (A₀ A₁ : ℂ → CoefficientPath R) (F : ℂ → Path R) : ℂ → Path R :=
  fun z => ∑' k : ℕ, layer hR VolterraAnalyticBounds.exponent A₀ A₁ F k z

section Summation

variable {R : ℝ} (hR : 0 ≤ R)
  {A₀ A₁ : ℂ → CoefficientPath R} {F : ℂ → Path R} {U : Set ℂ}
  (hU : IsOpen U) (hA₀ : DifferentiableOn ℂ A₀ U) (hA₁ : DifferentiableOn ℂ A₁ U)
  (hF : DifferentiableOn ℂ F U) {center : ℂ} {ρ σ B M : ℝ}
  (hDisk : Metric.closedBall center σ ⊆ U) (hgap : ρ < σ)
  (hB : 0 ≤ B) (hM : 0 ≤ M)
  (hshape : VolterraAnalyticBounds.DerivativeShape (rawCoefficient hR A₁))
  (hbA₀ : VolterraAnalyticBounds.MatrixBound (rawCoefficient hR A₀) R center σ M)
  (hbA₁ : VolterraAnalyticBounds.MatrixBound (rawCoefficient hR A₁) R center σ M)
  (hbF : ∀ z ∈ Metric.closedBall center σ, ‖F z‖ ≤ B)

include hR hU hA₀ hA₁ hF hDisk hgap hB hM hshape hbA₀ hbA₁ hbF

theorem solutionSeries_hasSum {z : ℂ} (hz : z ∈ Metric.closedBall center ρ) :
    HasSum (fun k => layer hR VolterraAnalyticBounds.exponent A₀ A₁ F k z)
      (solutionSeries hR A₀ A₁ F z) := by
  apply Summable.hasSum
  apply Summable.of_norm_bounded
    (VolterraAnalyticBounds.summable_wordLayers (mul_nonneg hM hR)
      (le_trans zero_le_one (le_max_left _ _)))
  · intro k
    exact layer_bound hR hU hA₀ hA₁ hF hDisk hgap hB hM hshape hbA₀ hbA₁ hbF k hz

/-- The infinite series is a holomorphic map into the space of actual
continuous radial paths, with no smallness restriction on the coefficients. -/
theorem solutionSeries_holomorphic :
    DifferentiableOn ℂ (solutionSeries hR A₀ A₁ F) (Metric.ball center ρ) := by
  apply Complex.differentiableOn_tsum_of_summable_norm
    (VolterraAnalyticBounds.summable_wordLayers (B := B) (mul_nonneg hM hR)
      (le_trans zero_le_one (le_max_left 1 (σ - ρ)⁻¹)))
  · intro k
    exact (layer_holomorphic hR _ hU hA₀ hA₁ hF k).mono
      (fun z hz => hDisk (Metric.closedBall_subset_closedBall hgap.le
        (Metric.ball_subset_closedBall hz)))
  · exact Metric.isOpen_ball
  · intro k z hz
    exact layer_bound hR hU hA₀ hA₁ hF hDisk hgap hB hM hshape hbA₀ hbA₁ hbF k
      (Metric.ball_subset_closedBall hz)

/-- Actual complex differentiation commutes with the convergent Volterra series. -/
theorem solutionSeries_deriv_hasSum {z : ℂ} (hz : z ∈ Metric.ball center ρ) :
    HasSum (fun k => deriv (layer hR VolterraAnalyticBounds.exponent A₀ A₁ F k) z)
      (deriv (solutionSeries hR A₀ A₁ F) z) := by
  apply Complex.hasSum_deriv_of_summable_norm
    (VolterraAnalyticBounds.summable_wordLayers (B := B) (mul_nonneg hM hR)
      (le_trans zero_le_one (le_max_left 1 (σ - ρ)⁻¹)))
  · intro k
    exact (layer_holomorphic hR _ hU hA₀ hA₁ hF k).mono
      (fun z hz => hDisk (Metric.closedBall_subset_closedBall hgap.le
        (Metric.ball_subset_closedBall hz)))
  · exact Metric.isOpen_ball
  · intro k z hz
    exact layer_bound hR hU hA₀ hA₁ hF hDisk hgap hB hM hshape hbA₀ hbA₁ hbF k
      (Metric.ball_subset_closedBall hz)
  · exact hz

/-- The convergent series solves the genuine integral equation. In
particular, convergence is not merely convergence of unrelated scalar bounds. -/
theorem solutionSeries_equation {z : ℂ} (hz : z ∈ Metric.ball center ρ) :
    solutionSeries hR A₀ A₁ F z = F z + pathInverse hR VolterraAnalyticBounds.exponent
      (coefficientAction (A₀ z) (solutionSeries hR A₀ A₁ F z) +
        coefficientAction (A₁ z) (deriv (solutionSeries hR A₀ A₁ F) z)) := by
  have hs := solutionSeries_hasSum hR hU hA₀ hA₁ hF hDisk hgap hB hM hshape hbA₀ hbA₁ hbF
    (Metric.ball_subset_closedBall hz)
  have hd := solutionSeries_deriv_hasSum hR hU hA₀ hA₁ hF hDisk hgap hB hM hshape hbA₀ hbA₁ hbF hz
  let L₀ := (pathInverse hR VolterraAnalyticBounds.exponent).comp (coefficientAction (A₀ z))
  let L₁ := (pathInverse hR VolterraAnalyticBounds.exponent).comp (coefficientAction (A₁ z))
  have hsum := (hs.mapL L₀).add (hd.mapL L₁)
  have hshift : HasSum (fun k => layer hR VolterraAnalyticBounds.exponent A₀ A₁ F (k + 1) z)
      (L₀ (solutionSeries hR A₀ A₁ F z) + L₁ (deriv (solutionSeries hR A₀ A₁ F) z)) := by
    convert! hsum using 1
    funext k
    exact layer_succ hR _ hU hA₀ hA₁ hF k
      (hDisk (Metric.closedBall_subset_closedBall hgap.le (Metric.ball_subset_closedBall hz)))
  calc
    _ = layer hR VolterraAnalyticBounds.exponent A₀ A₁ F 0 z +
        ∑' k, layer hR VolterraAnalyticBounds.exponent A₀ A₁ F (k + 1) z :=
      hs.summable.tsum_eq_zero_add
    _ = _ := by rw [layer_zero, hshift.tsum_eq, map_add]; rfl

end Summation

/-- Canonical series with the actual integrated forcing as its initial layer. -/
def integralSolution {R : ℝ} (hR : 0 ≤ R)
    (A₀ A₁ : ℂ → CoefficientPath R) (f : ℂ → Path R) : ℂ → Path R :=
  solutionSeries hR A₀ A₁ (fun z => pathInverse hR VolterraAnalyticBounds.exponent (f z))

/-- Compactness supplies all coefficient bounds. Thus the actual solution
theorem assumes neither a word bound nor convergence of its defining series. -/
theorem integralSolution_spec {R : ℝ} (hR : 0 ≤ R)
    {A₀ A₁ : ℂ → CoefficientPath R} {f : ℂ → Path R} {U : Set ℂ}
    (hU : IsOpen U) (hA₀ : DifferentiableOn ℂ A₀ U) (hA₁ : DifferentiableOn ℂ A₁ U)
    (hf : DifferentiableOn ℂ f U) {center : ℂ} {ρ σ : ℝ}
    (hDisk : Metric.closedBall center σ ⊆ U) (hgap : ρ < σ)
    (hshape : VolterraAnalyticBounds.DerivativeShape (rawCoefficient hR A₁)) :
    DifferentiableOn ℂ (integralSolution hR A₀ A₁ f) (Metric.ball center ρ) ∧
      ∀ z ∈ Metric.ball center ρ,
        integralSolution hR A₀ A₁ f z = pathInverse hR VolterraAnalyticBounds.exponent
          (f z + (coefficientAction (A₀ z) (integralSolution hR A₀ A₁ f z) +
            coefficientAction (A₁ z) (deriv (integralSolution hR A₀ A₁ f) z))) := by
  obtain ⟨K₀, hK₀⟩ := (isCompact_closedBall center σ).exists_bound_of_continuousOn
    (f := A₀) (hA₀.continuousOn.mono hDisk)
  obtain ⟨K₁, hK₁⟩ := (isCompact_closedBall center σ).exists_bound_of_continuousOn
    (f := A₁) (hA₁.continuousOn.mono hDisk)
  obtain ⟨B₀, hB₀⟩ := (isCompact_closedBall center σ).exists_bound_of_continuousOn
    (hf.continuousOn.mono hDisk)
  let K := max 0 (max K₀ K₁)
  have hK : 0 ≤ K := le_max_left _ _
  have hbA₀ : VolterraAnalyticBounds.MatrixBound (rawCoefficient hR A₀) R center σ (6 * K) :=
    rawCoefficient_bound hR A₀ (fun z hz => (hK₀ z hz).trans
      ((le_max_left K₀ K₁).trans (le_max_right 0 (max K₀ K₁))))
  have hbA₁ : VolterraAnalyticBounds.MatrixBound (rawCoefficient hR A₁) R center σ (6 * K) :=
    rawCoefficient_bound hR A₁ (fun z hz => (hK₁ z hz).trans
      ((le_max_right K₀ K₁).trans (le_max_right 0 (max K₀ K₁))))
  let F : ℂ → Path R := fun z => pathInverse hR VolterraAnalyticBounds.exponent (f z)
  have hF : DifferentiableOn ℂ F U :=
    (pathInverse hR VolterraAnalyticBounds.exponent).differentiable.comp_differentiableOn hf
  have hBF : 0 ≤ R * max 0 B₀ := mul_nonneg hR (le_max_left _ _)
  have hbF : ∀ z ∈ Metric.closedBall center σ, ‖F z‖ ≤ R * max 0 B₀ := by
    intro z hz
    exact (norm_pathInverseValue_le hR VolterraAnalyticBounds.exponent (f z)).trans
      (mul_le_mul_of_nonneg_left ((hB₀ z hz).trans (le_max_right _ _)) hR)
  have hM : 0 ≤ 6 * K := mul_nonneg (by norm_num) hK
  refine ⟨solutionSeries_holomorphic hR hU hA₀ hA₁ hF hDisk hgap hBF hM hshape hbA₀ hbA₁ hbF, ?_⟩
  intro z hz
  have he := solutionSeries_equation hR hU hA₀ hA₁ hF hDisk hgap hBF hM hshape hbA₀ hbA₁ hbF hz
  simp only [map_add] at he ⊢
  exact he

/-- Rhs path, given by `f z + (coefficientAction (A₀ z) (W z) + coefficientAction (A₁ z) (deriv
W z))`. -/
def rhsPath {R : ℝ} (A₀ A₁ : ℂ → CoefficientPath R) (f W : ℂ → Path R) (z : ℂ) : Path R :=
  f z + (coefficientAction (A₀ z) (W z) + coefficientAction (A₁ z) (deriv W z))

/-- An actual radial function extending the solved path. Its definition
uses the regular integral even at the axis and beyond the path interval. -/
def liftedField {R : ℝ} (hR : 0 ≤ R) (A₀ A₁ : ℂ → CoefficientPath R)
    (f W : ℂ → Path R) : VolterraAnalyticBounds.Field :=
  fun r z i => regularPrimitive (VolterraAnalyticBounds.exponent i)
    (fun s => extendPath hR (rhsPath A₀ A₁ f W z) s i) r

theorem liftedField_hasDerivAt {R : ℝ} (hR : 0 ≤ R) (A₀ A₁ : ℂ → CoefficientPath R)
    (f W : ℂ → Path R) (r : ℝ) (z : ℂ) (i : Fin 6) :
    HasDerivAt (fun s => liftedField hR A₀ A₁ f W s z i)
      (extendPath hR (rhsPath A₀ A₁ f W z) r i -
        (VolterraAnalyticBounds.exponent i : ℝ) • weightedMean (VolterraAnalyticBounds.exponent i)
          (fun s => extendPath hR (rhsPath A₀ A₁ f W z) s i) r) r :=
  regularPrimitive_hasDerivAt _ ((continuous_apply i).comp (extendPath_continuous hR _)) r

theorem liftedField_derivative_continuous {R : ℝ} (hR : 0 ≤ R)
    (A₀ A₁ : ℂ → CoefficientPath R) (f W : ℂ → Path R) (z : ℂ) (i : Fin 6) :
    Continuous (deriv (fun r => liftedField hR A₀ A₁ f W r z i)) :=
  regularPrimitive_derivative_continuous _ ((continuous_apply i).comp (extendPath_continuous hR _))

theorem liftedField_axis_zero {R : ℝ} (hR : 0 ≤ R)
    (A₀ A₁ : ℂ → CoefficientPath R) (f W : ℂ → Path R) (z : ℂ) :
    liftedField hR A₀ A₁ f W 0 z = 0 := by
  funext i
  exact regularPrimitive_zero _ _

theorem liftedField_eq_trace {R : ℝ} (hR : 0 ≤ R)
    (A₀ A₁ : ℂ → CoefficientPath R) (f W : ℂ → Path R) {z : ℂ}
    (hW : W z = pathInverse hR VolterraAnalyticBounds.exponent (rhsPath A₀ A₁ f W z))
    {r : ℝ} (hr : r ∈ Icc (0 : ℝ) R) :
    liftedField hR A₀ A₁ f W r z = rawField hR W r z := by
  funext i
  change regularPrimitive _ _ r = W z (projIcc 0 R hR r) i
  rw [hW, projIcc_of_mem hR hr]
  rfl

/-- Equation RHS as an element of `VolterraAnalyticBounds.Field`. -/
def equationRHS (A₀ A₁ : VolterraAnalyticBounds.Coeff)
    (f W : VolterraAnalyticBounds.Field) : VolterraAnalyticBounds.Field :=
  fun r z => f r z + (VolterraAnalyticBounds.matrixAction A₀ W r z +
    VolterraAnalyticBounds.matrixAction A₁ (VolterraAnalyticBounds.parameterDeriv W) r z)

/-- Radial derivative, defined pointwise by `deriv (fun s : ℝ => W s z i) r`. -/
def radialDeriv (W : VolterraAnalyticBounds.Field) : VolterraAnalyticBounds.Field :=
  fun r z i => deriv (fun s : ℝ => W s z i) r

/-- A genuine regular solution of the singular first-order system. Radial
regularity here is C¹, stated through ordinary derivatives and their continuity. -/
structure IsRegularSolution (R : ℝ) (U : Set ℂ)
    (A₀ A₁ : VolterraAnalyticBounds.Coeff) (f W : VolterraAnalyticBounds.Field) : Prop where
  jointly_continuous : ContinuousOn (fun p : ℝ × ℂ => W p.1 p.2) (Icc (0 : ℝ) R ×ˢ U)
  parameter_holomorphic : ∀ r ∈ Icc (0 : ℝ) R, ∀ i,
    DifferentiableOn ℂ (fun z => W r z i) U
  radial_differentiable : ∀ z ∈ U, ∀ i, Differentiable ℝ (fun r => W r z i)
  radial_derivative_continuous : ∀ z ∈ U, ∀ i, Continuous (fun r => radialDeriv W r z i)
  axis_zero : ∀ z ∈ U, W 0 z = 0
  equation : ∀ r ∈ Icc (0 : ℝ) R, r ≠ 0 → ∀ z ∈ U, ∀ i,
    radialDeriv W r z i + ((VolterraAnalyticBounds.exponent i : ℝ) / r) • W r z i =
      equationRHS A₀ A₁ f W r z i
  axis_derivative : ∀ z ∈ U, ∀ i,
    radialDeriv W 0 z i =
      (1 / ((VolterraAnalyticBounds.exponent i : ℝ) + 1)) • equationRHS A₀ A₁ f W 0 z i

section LiftSolution

variable {R : ℝ} (hR : 0 ≤ R)
  (A₀ A₁ : ℂ → CoefficientPath R) (f W : ℂ → Path R) {U : Set ℂ}
  (hU : IsOpen U) (hWholo : DifferentiableOn ℂ W U)
  (hW : ∀ z ∈ U, W z = pathInverse hR VolterraAnalyticBounds.exponent (rhsPath A₀ A₁ f W z))

include hU hWholo hW

theorem liftedField_parameterDeriv {r : ℝ} (hr : r ∈ Icc (0 : ℝ) R)
    {z : ℂ} (hz : z ∈ U) :
    VolterraAnalyticBounds.parameterDeriv (liftedField hR A₀ A₁ f W) r z =
      rawField hR (deriv W) r z := by
  rw [← rawField_deriv hR (hWholo.differentiableAt (hU.mem_nhds hz)) r]
  funext i
  apply Filter.EventuallyEq.deriv_eq
  filter_upwards [hU.mem_nhds hz] with w hw
  exact congrFun (liftedField_eq_trace hR A₀ A₁ f W (hW w hw) hr) i

omit hU in
theorem liftedField_holomorphic {r : ℝ} (hr : r ∈ Icc (0 : ℝ) R) (i : Fin 6) :
    DifferentiableOn ℂ (fun z => liftedField hR A₀ A₁ f W r z i) U := by
  have hh := (pathEvaluation (projIcc 0 R hR r) i).differentiable.comp_differentiableOn hWholo
  apply hh.congr
  intro z hz
  exact congrFun (liftedField_eq_trace hR A₀ A₁ f W (hW z hz) hr) i

theorem liftedField_rhs {r : ℝ} (hr : r ∈ Icc (0 : ℝ) R) {z : ℂ} (hz : z ∈ U) :
    extendPath hR (rhsPath A₀ A₁ f W z) r =
      equationRHS (rawCoefficient hR A₀) (rawCoefficient hR A₁) (rawField hR f)
        (liftedField hR A₀ A₁ f W) r z := by
  simp only [equationRHS, VolterraAnalyticBounds.matrixAction, rawCoefficient_mulVec]
  rw [liftedField_parameterDeriv hR A₀ A₁ f W hU hWholo hW hr hz]
  simp only [
    liftedField_eq_trace hR A₀ A₁ f W (hW z hz) hr]
  rfl

omit hU in
theorem liftedField_jointly_continuous :
    ContinuousOn (fun p : ℝ × ℂ => liftedField hR A₀ A₁ f W p.1 p.2)
      (Icc (0 : ℝ) R ×ˢ U) := by
  have hw : ContinuousOn (fun p : ℝ × ℂ => W p.2) (Icc (0 : ℝ) R ×ˢ U) :=
    hWholo.continuousOn.comp continuous_snd.continuousOn (fun p hp => hp.2)
  have hr : Continuous (fun p : ℝ × ℂ => projIcc 0 R hR p.1) :=
    continuous_projIcc.comp continuous_fst
  have he : ContinuousOn (fun p : ℝ × ℂ => rawField hR W p.1 p.2)
      (Icc (0 : ℝ) R ×ˢ U) :=
    continuous_eval.comp_continuousOn (hw.prodMk hr.continuousOn)
  apply he.congr
  intro p hp
  exact liftedField_eq_trace hR A₀ A₁ f W (hW p.2 hp.2) hp.1

theorem liftedField_isRegularSolution :
    IsRegularSolution R U (rawCoefficient hR A₀) (rawCoefficient hR A₁)
      (rawField hR f) (liftedField hR A₀ A₁ f W) := by
  refine {
    jointly_continuous := liftedField_jointly_continuous hR A₀ A₁ f W hWholo hW
    parameter_holomorphic := fun r hr i => liftedField_holomorphic hR A₀ A₁ f W hWholo hW hr i
    radial_differentiable := ?_
    radial_derivative_continuous := fun z hz i => liftedField_derivative_continuous hR A₀ A₁ f W z i
    axis_zero := fun z hz => liftedField_axis_zero hR A₀ A₁ f W z
    equation := ?_
    axis_derivative := ?_ }
  · intro z hz i r
    exact (liftedField_hasDerivAt hR A₀ A₁ f W r z i).differentiableAt
  · intro r hr hr0 z hz i
    have hg : Continuous (fun s => extendPath hR (rhsPath A₀ A₁ f W z) s i) :=
      (continuous_apply i).comp (extendPath_continuous hR _)
    have he := regularPrimitive_equation (VolterraAnalyticBounds.exponent i) hg hr0
    change radialDeriv (liftedField hR A₀ A₁ f W) r z i +
      ((VolterraAnalyticBounds.exponent i : ℝ) / r) • liftedField hR A₀ A₁ f W r z i =
        extendPath hR (rhsPath A₀ A₁ f W z) r i at he
    rw [liftedField_rhs hR A₀ A₁ f W hU hWholo hW hr hz] at he
    exact he
  · intro z hz i
    have hg : Continuous (fun s => extendPath hR (rhsPath A₀ A₁ f W z) s i) :=
      (continuous_apply i).comp (extendPath_continuous hR _)
    have he := (regularPrimitive_hasDerivAt_zero (VolterraAnalyticBounds.exponent i) hg).deriv
    rw [weightedMean_zero] at he
    change radialDeriv (liftedField hR A₀ A₁ f W) 0 z i =
      (1 / ((VolterraAnalyticBounds.exponent i : ℝ) + 1)) •
        extendPath hR (rhsPath A₀ A₁ f W z) 0 i at he
    rw [liftedField_rhs hR A₀ A₁ f W hU hWholo hW ⟨le_rfl, hR⟩ hz] at he
    exact he

end LiftSolution

/-- A regular solution on any prescribed finite radial interval. Only
the parameter neighborhood is reduced; coefficient size places no upper
bound on the length of the radial interval. -/
theorem exists_regular_solution {R : ℝ} (hR : 0 ≤ R)
    {A₀ A₁ : ℂ → CoefficientPath R} {f : ℂ → Path R} {U : Set ℂ}
    (hU : IsOpen U) (hA₀ : DifferentiableOn ℂ A₀ U) (hA₁ : DifferentiableOn ℂ A₁ U)
    (hf : DifferentiableOn ℂ f U) {center : ℂ} {ρ σ : ℝ}
    (hDisk : Metric.closedBall center σ ⊆ U) (hgap : ρ < σ)
    (hshape : VolterraAnalyticBounds.DerivativeShape (rawCoefficient hR A₁)) :
    ∃ W : VolterraAnalyticBounds.Field,
      IsRegularSolution R (Metric.ball center ρ)
        (rawCoefficient hR A₀) (rawCoefficient hR A₁) (rawField hR f) W := by
  obtain ⟨holo, heq⟩ := integralSolution_spec hR hU hA₀ hA₁ hf hDisk hgap hshape
  exact ⟨liftedField hR A₀ A₁ f (integralSolution hR A₀ A₁ f),
    liftedField_isRegularSolution hR A₀ A₁ f (integralSolution hR A₀ A₁ f)
      Metric.isOpen_ball holo heq⟩

theorem homogeneous_layer_eq {R : ℝ} (hR : 0 ≤ R)
    {A₀ A₁ : ℂ → CoefficientPath R} {V : ℂ → Path R} {U : Set ℂ}
    (hU : IsOpen U) (hA₀ : DifferentiableOn ℂ A₀ U) (hA₁ : DifferentiableOn ℂ A₁ U)
    (hV : DifferentiableOn ℂ V U)
    (heq : ∀ z ∈ U, V z = pathInverse hR VolterraAnalyticBounds.exponent
      (coefficientAction (A₀ z) (V z) + coefficientAction (A₁ z) (deriv V z)))
    (k : ℕ) {z : ℂ} (hz : z ∈ U) :
    layer hR VolterraAnalyticBounds.exponent A₀ A₁ V k z = V z := by
  induction k generalizing z with
  | zero => rw [layer_zero]
  | succ k ih =>
      have hevent : layer hR VolterraAnalyticBounds.exponent A₀ A₁ V k =ᶠ[𝓝 z] V := by
        filter_upwards [hU.mem_nhds hz] with w hw
        exact ih hw
      rw [layer_succ hR _ hU hA₀ hA₁ hV k hz]
      simp only [pathLetter, Bool.false_eq_true, ite_false, ite_true]
      rw [ih hz, hevent.deriv_eq, ← map_add]
      exact (heq z hz).symm

theorem homogeneous_zero_on_closedDisk {R : ℝ} (hR : 0 ≤ R)
    {A₀ A₁ : ℂ → CoefficientPath R} {V : ℂ → Path R} {U : Set ℂ}
    (hU : IsOpen U) (hA₀ : DifferentiableOn ℂ A₀ U) (hA₁ : DifferentiableOn ℂ A₁ U)
    (hV : DifferentiableOn ℂ V U) {center : ℂ} {ρ σ B M : ℝ}
    (hDisk : Metric.closedBall center σ ⊆ U) (hgap : ρ < σ)
    (hB : 0 ≤ B) (hM : 0 ≤ M)
    (hshape : VolterraAnalyticBounds.DerivativeShape (rawCoefficient hR A₁))
    (hbA₀ : VolterraAnalyticBounds.MatrixBound (rawCoefficient hR A₀) R center σ M)
    (hbA₁ : VolterraAnalyticBounds.MatrixBound (rawCoefficient hR A₁) R center σ M)
    (hbV : ∀ z ∈ Metric.closedBall center σ, ‖V z‖ ≤ B)
    (heq : ∀ z ∈ U, V z = pathInverse hR VolterraAnalyticBounds.exponent
      (coefficientAction (A₀ z) (V z) + coefficientAction (A₁ z) (deriv V z)))
    {z : ℂ} (hz : z ∈ Metric.closedBall center ρ) : V z = 0 := by
  have hzU := hDisk (Metric.closedBall_subset_closedBall hgap.le hz)
  have hs := VolterraAnalyticBounds.summable_wordLayers (B := B) (mul_nonneg hM hR)
    (le_trans zero_le_one (le_max_left 1 (σ - ρ)⁻¹))
  have hnorm : ‖V z‖ ≤ 0 := ge_of_tendsto' hs.tendsto_atTop_zero (fun k => by
    have hb := layer_bound hR hU hA₀ hA₁ hV hDisk hgap hB hM hshape hbA₀ hbA₁ hbV k hz
    rwa [homogeneous_layer_eq hR hU hA₀ hA₁ hV heq k hzU] at hb)
  exact norm_eq_zero.mp (le_antisymm hnorm (norm_nonneg _))

/-- Local compact bounds and the convergent majorant force every
holomorphic homogeneous zero-axis solution to vanish. -/
theorem homogeneous_solution_zero {R : ℝ} (hR : 0 ≤ R)
    {A₀ A₁ : ℂ → CoefficientPath R} {V : ℂ → Path R} {U : Set ℂ}
    (hU : IsOpen U) (hA₀ : DifferentiableOn ℂ A₀ U) (hA₁ : DifferentiableOn ℂ A₁ U)
    (hV : DifferentiableOn ℂ V U)
    (hshape : VolterraAnalyticBounds.DerivativeShape (rawCoefficient hR A₁))
    (heq : ∀ z ∈ U, V z = pathInverse hR VolterraAnalyticBounds.exponent
      (coefficientAction (A₀ z) (V z) + coefficientAction (A₁ z) (deriv V z))) :
    ∀ z ∈ U, V z = 0 := by
  intro z hz
  obtain ⟨δ, hδ, hδU⟩ := Metric.mem_nhds_iff.mp (hU.mem_nhds hz)
  have hDisk : Metric.closedBall z (δ / 2) ⊆ U := fun w hw =>
    hδU (Metric.mem_ball.mpr ((Metric.mem_closedBall.mp hw).trans_lt (by linarith)))
  obtain ⟨K₀, hK₀⟩ := (isCompact_closedBall z (δ / 2)).exists_bound_of_continuousOn
    (f := A₀) (hA₀.continuousOn.mono hDisk)
  obtain ⟨K₁, hK₁⟩ := (isCompact_closedBall z (δ / 2)).exists_bound_of_continuousOn
    (f := A₁) (hA₁.continuousOn.mono hDisk)
  obtain ⟨B₀, hB₀⟩ := (isCompact_closedBall z (δ / 2)).exists_bound_of_continuousOn
    (hV.continuousOn.mono hDisk)
  let K := max 0 (max K₀ K₁)
  have hK : 0 ≤ K := le_max_left _ _
  have hbA₀ : VolterraAnalyticBounds.MatrixBound (rawCoefficient hR A₀) R z (δ / 2) (6 * K) :=
    rawCoefficient_bound hR A₀ (fun w hw => (hK₀ w hw).trans
      ((le_max_left K₀ K₁).trans (le_max_right 0 (max K₀ K₁))))
  have hbA₁ : VolterraAnalyticBounds.MatrixBound (rawCoefficient hR A₁) R z (δ / 2) (6 * K) :=
    rawCoefficient_bound hR A₁ (fun w hw => (hK₁ w hw).trans
      ((le_max_right K₀ K₁).trans (le_max_right 0 (max K₀ K₁))))
  exact homogeneous_zero_on_closedDisk hR hU hA₀ hA₁ hV hDisk
    (show δ / 4 < δ / 2 by linarith) (le_max_left 0 B₀)
    (mul_nonneg (by norm_num) hK) hshape hbA₀ hbA₁
    (fun w hw => (hB₀ w hw).trans (le_max_right 0 B₀)) heq
    (Metric.mem_closedBall_self (show 0 ≤ δ / 4 by positivity))

/-- Uniqueness in the holomorphic continuous-path class, with all local
growth bounds derived from compactness. -/
theorem integral_solution_unique {R : ℝ} (hR : 0 ≤ R)
    {A₀ A₁ : ℂ → CoefficientPath R} {f W₀ W₁ : ℂ → Path R} {U : Set ℂ}
    (hU : IsOpen U) (hA₀ : DifferentiableOn ℂ A₀ U) (hA₁ : DifferentiableOn ℂ A₁ U)
    (hW₀ : DifferentiableOn ℂ W₀ U) (hW₁ : DifferentiableOn ℂ W₁ U)
    (hshape : VolterraAnalyticBounds.DerivativeShape (rawCoefficient hR A₁))
    (heq₀ : ∀ z ∈ U, W₀ z = pathInverse hR VolterraAnalyticBounds.exponent (rhsPath A₀ A₁ f W₀ z))
    (heq₁ : ∀ z ∈ U, W₁ z = pathInverse hR VolterraAnalyticBounds.exponent (rhsPath A₀ A₁ f W₁ z)) :
    EqOn W₀ W₁ U := by
  have hd : ∀ z ∈ U, deriv (W₀ - W₁) z = deriv W₀ z - deriv W₁ z := by
    intro z hz
    exact deriv_fun_sub (hW₀.differentiableAt (hU.mem_nhds hz))
      (hW₁.differentiableAt (hU.mem_nhds hz))
  have heq : ∀ z ∈ U, (W₀ - W₁) z = pathInverse hR VolterraAnalyticBounds.exponent
      (coefficientAction (A₀ z) ((W₀ - W₁) z) +
        coefficientAction (A₁ z) (deriv (W₀ - W₁) z)) := by
    intro z hz
    have hs := congrArg₂ (fun u v : Path R => u - v) (heq₀ z hz) (heq₁ z hz)
    rw [← map_sub] at hs
    refine hs.trans ?_
    congr 1
    rw [hd z hz]
    simp only [rhsPath, map_sub, Pi.sub_apply]
    abel
  intro z hz
  have hzero := homogeneous_solution_zero hR hU hA₀ hA₁ (hW₀.sub hW₁) hshape heq z hz
  exact sub_eq_zero.mp hzero

/-- The same canonical series works locally on every disk in an arbitrary
open parameter domain. Consequently its values are holomorphic on that
domain; uniform estimates are taken on smaller compact neighborhoods. -/
theorem integralSolution_spec_open {R : ℝ} (hR : 0 ≤ R)
    {A₀ A₁ : ℂ → CoefficientPath R} {f : ℂ → Path R} {U : Set ℂ}
    (hU : IsOpen U) (hA₀ : DifferentiableOn ℂ A₀ U) (hA₁ : DifferentiableOn ℂ A₁ U)
    (hf : DifferentiableOn ℂ f U)
    (hshape : VolterraAnalyticBounds.DerivativeShape (rawCoefficient hR A₁)) :
    DifferentiableOn ℂ (integralSolution hR A₀ A₁ f) U ∧
      ∀ z ∈ U, integralSolution hR A₀ A₁ f z =
        pathInverse hR VolterraAnalyticBounds.exponent
          (rhsPath A₀ A₁ f (integralSolution hR A₀ A₁ f) z) := by
  have hlocal : ∀ z ∈ U,
      DifferentiableAt ℂ (integralSolution hR A₀ A₁ f) z ∧
        integralSolution hR A₀ A₁ f z = pathInverse hR VolterraAnalyticBounds.exponent
          (rhsPath A₀ A₁ f (integralSolution hR A₀ A₁ f) z) := by
    intro z hz
    obtain ⟨δ, hδ, hδU⟩ := Metric.mem_nhds_iff.mp (hU.mem_nhds hz)
    have hDisk : Metric.closedBall z (δ / 2) ⊆ U := fun w hw =>
      hδU (Metric.mem_ball.mpr ((Metric.mem_closedBall.mp hw).trans_lt (by linarith)))
    have hgap : δ / 4 < δ / 2 := by linarith
    obtain ⟨hholo, heq⟩ := integralSolution_spec hR hU hA₀ hA₁ hf hDisk hgap hshape
    have hz' : z ∈ Metric.ball z (δ / 4) := Metric.mem_ball_self (by positivity)
    exact ⟨hholo.differentiableAt (Metric.isOpen_ball.mem_nhds hz'), heq z hz'⟩
  exact ⟨fun z hz => (hlocal z hz).1.differentiableWithinAt, fun z hz => (hlocal z hz).2⟩

/-- Existence on any finite radial interval and any open parameter
neighborhood carrying the fixed holomorphic input data. -/
theorem exists_regular_solution_open {R : ℝ} (hR : 0 ≤ R)
    {A₀ A₁ : ℂ → CoefficientPath R} {f : ℂ → Path R} {U : Set ℂ}
    (hU : IsOpen U) (hA₀ : DifferentiableOn ℂ A₀ U) (hA₁ : DifferentiableOn ℂ A₁ U)
    (hf : DifferentiableOn ℂ f U)
    (hshape : VolterraAnalyticBounds.DerivativeShape (rawCoefficient hR A₁)) :
    ∃ W : VolterraAnalyticBounds.Field,
      IsRegularSolution R U (rawCoefficient hR A₀) (rawCoefficient hR A₁) (rawField hR f) W := by
  obtain ⟨holo, heq⟩ := integralSolution_spec_open hR hU hA₀ hA₁ hf hshape
  exact ⟨liftedField hR A₀ A₁ f (integralSolution hR A₀ A₁ f),
    liftedField_isRegularSolution hR A₀ A₁ f (integralSolution hR A₀ A₁ f) hU holo heq⟩

/-- Zero axis data make the axis derivative depend only on the given forcing. -/
theorem IsRegularSolution.axis_derivative_eq_forcing
    {R : ℝ} {U : Set ℂ} {A₀ A₁ : VolterraAnalyticBounds.Coeff}
    {f W : VolterraAnalyticBounds.Field} (hsol : IsRegularSolution R U A₀ A₁ f W)
    (hU : IsOpen U) {z : ℂ} (hz : z ∈ U) (i : Fin 6) :
    radialDeriv W 0 z i = (1 / ((VolterraAnalyticBounds.exponent i : ℝ) + 1)) • f 0 z i := by
  have hp : VolterraAnalyticBounds.parameterDeriv W 0 z = 0 := by
    funext j
    have he : (fun w => W 0 w j) =ᶠ[𝓝 z] (fun _ : ℂ => (0 : ℂ)) := by
      filter_upwards [hU.mem_nhds hz] with w hw
      exact congrFun (hsol.axis_zero w hw) j
    exact he.deriv_eq.trans (deriv_const z 0)
  rw [hsol.axis_derivative z hz i]
  simp only [equationRHS, VolterraAnalyticBounds.matrixAction,
    hsol.axis_zero z hz, hp, Matrix.mulVec_zero, add_zero, Pi.add_apply, Pi.zero_apply]

end NavierStokes.NilpotentVolterra

end
end

end

@[expose] public section

noncomputable section

namespace NavierStokes.VolterraParity

open Set Filter MeasureTheory
open scoped Topology
open VolterraAnalyticBounds
open NilpotentVolterra (equationRHS)

/-- Parity sign, with branches according to `i.val < 4`. -/
noncomputable def paritySign (i : Fin 6) : ℂ := if i.val < 4 then 1 else -1

/-- Parity vector, given by `ContinuousLinearMap.pi (fun i => paritySign i •
ContinuousLinearMap.proj i)`. -/
noncomputable def parityVec : Vec →L[ℂ] Vec :=
  ContinuousLinearMap.pi (fun i => paritySign i • ContinuousLinearMap.proj i)

@[simp] theorem parityVec_apply (v : Vec) (i : Fin 6) :
    parityVec v i = paritySign i * v i := rfl

@[simp] theorem paritySign_mul_self (i : Fin 6) : paritySign i * paritySign i = 1 := by
  by_cases hi : i.val < 4 <;> simp [paritySign, hi]

@[simp] theorem parityVec_involutive (v : Vec) : parityVec (parityVec v) = v := by
  funext i
  simp only [parityVec_apply, ← mul_assoc, paritySign_mul_self, one_mul]

/-- Coefficient parity on, given by `∀ r ∈ S, ∀ z ∈ U, ∀ i j, A (-r) z i j = -(paritySign i *
paritySign j) * A r z i j`. -/
def CoefficientParityOn (S : Set ℝ) (U : Set ℂ) (A : Coeff) : Prop :=
  ∀ r ∈ S, ∀ z ∈ U, ∀ i j,
    A (-r) z i j = -(paritySign i * paritySign j) * A r z i j

/-- Forcing parity on, given by `∀ r ∈ S, ∀ z ∈ U, ∀ i, f (-r) z i = -(paritySign i) * f r z i`. -/
def ForcingParityOn (S : Set ℝ) (U : Set ℂ) (f : Field) : Prop :=
  ∀ r ∈ S, ∀ z ∈ U, ∀ i, f (-r) z i = -(paritySign i) * f r z i

/-- Coefficient parity, given by `∀ r z i j, A (-r) z i j = -(paritySign i * paritySign j) * A r
z i j`. -/
def CoefficientParity (A : Coeff) : Prop :=
  ∀ r z i j, A (-r) z i j = -(paritySign i * paritySign j) * A r z i j

/-- Forcing parity, given by `∀ r z i, f (-r) z i = -(paritySign i) * f r z i`. -/
def ForcingParity (f : Field) : Prop :=
  ∀ r z i, f (-r) z i = -(paritySign i) * f r z i

/-- Reflect field, defined pointwise by `W (-r) z`. -/
noncomputable def reflectField (W : Field) : Field := fun r z => W (-r) z

/-- Reflect coefficient, defined pointwise by `-A (-r) z`. -/
noncomputable def reflectCoeff (A : Coeff) : Coeff := fun r z => -A (-r) z

/-- Reflected forcing, defined pointwise by `-f (-r) z`. -/
noncomputable def reflectedForcing (f : Field) : Field := fun r z => -f (-r) z

@[simp] theorem reflectField_twice (W : Field) : reflectField (reflectField W) = W := by
  funext r z
  simp [reflectField]

@[simp] theorem reflectCoeff_twice (A : Coeff) : reflectCoeff (reflectCoeff A) = A := by
  funext r z
  simp [reflectCoeff]

@[simp] theorem reflectedForcing_twice (f : Field) :
    reflectedForcing (reflectedForcing f) = f := by
  funext r z
  simp [reflectedForcing]

@[simp] theorem parameterDeriv_reflect (W : Field) :
    parameterDeriv (reflectField W) = reflectField (parameterDeriv W) := rfl

theorem equationRHS_reflect (A₀ A₁ : Coeff) (f W : Field) :
    equationRHS (reflectCoeff A₀) (reflectCoeff A₁) (reflectedForcing f) (reflectField W) =
      reflectedForcing (equationRHS A₀ A₁ f W) := by
  funext r z i
  simp [equationRHS, reflectCoeff, reflectedForcing, reflectField, matrixAction,
    parameterDeriv, Matrix.mulVec, dotProduct, Finset.sum_neg_distrib]
  ring

/-- The sign from radial reflection is exactly the sign in the reflected
forcing. This is an identity of actual Bochner integrals. -/
theorem radialInverse_reflect (F : Field) :
    radialInverse (reflectedForcing F) = reflectField (radialInverse F) := by
  funext r z i
  simp [radialInverse, reflectedForcing, reflectField, smul_neg,
    intervalIntegral.integral_neg, mul_neg, neg_smul]

theorem radialInverse_equationRHS_reflect (A₀ A₁ : Coeff) (f W : Field) :
    radialInverse (equationRHS (reflectCoeff A₀) (reflectCoeff A₁)
      (reflectedForcing f) (reflectField W)) =
        reflectField (radialInverse (equationRHS A₀ A₁ f W)) := by
  rw [equationRHS_reflect, radialInverse_reflect]

/-- The actual regular integral equation on a specified radial set. -/
def IntegralEquationOn (S : Set ℝ) (U : Set ℂ) (A₀ A₁ : Coeff) (f W : Field) : Prop :=
  ∀ r ∈ S, ∀ z ∈ U, W r z = radialInverse (equationRHS A₀ A₁ f W) r z

theorem IntegralEquationOn.reflect {S : Set ℝ} {U : Set ℂ}
    {A₀ A₁ : Coeff} {f W : Field} (h : IntegralEquationOn S U A₀ A₁ f W) :
    IntegralEquationOn {r | -r ∈ S} U (reflectCoeff A₀) (reflectCoeff A₁)
      (reflectedForcing f) (reflectField W) := by
  intro r hr z hz
  rw [radialInverse_equationRHS_reflect]
  exact h (-r) hr z hz

theorem negativeHalf_equation {R : ℝ} {U : Set ℂ} {A₀ A₁ : Coeff} {f W : Field}
    (h : IntegralEquationOn (Icc 0 R) U (reflectCoeff A₀) (reflectCoeff A₁)
      (reflectedForcing f) W) :
    IntegralEquationOn (Icc (-R) 0) U A₀ A₁ f (reflectField W) := by
  intro r hr z hz
  have hh := h.reflect r ⟨neg_nonneg.mpr hr.2, by linarith [hr.1]⟩ z hz
  simpa using hh

/-- Glue, defined pointwise by `if 0 ≤ r then Wp r z else Wm (-r) z`. -/
noncomputable def glue (Wp Wm : Field) : Field :=
  fun r z => if 0 ≤ r then Wp r z else Wm (-r) z

theorem glue_nonneg (Wp Wm : Field) {r : ℝ} (hr : 0 ≤ r) (z : ℂ) :
    glue Wp Wm r z = Wp r z := by simp [glue, hr]

theorem glue_nonpos {Wp Wm : Field} (h0 : ∀ z, Wp 0 z = Wm 0 z)
    {r : ℝ} (hr : r ≤ 0) (z : ℂ) : glue Wp Wm r z = Wm (-r) z := by
  by_cases hr0 : r = 0
  · subst r
    simpa [glue] using h0 z
  · simp [glue, show ¬ 0 ≤ r by exact not_le.mpr (lt_of_le_of_ne hr hr0)]

theorem equationRHS_congr_at {A₀ A₁ : Coeff} {f W V : Field} {r : ℝ}
    (h : ∀ z, W r z = V r z) (z : ℂ) :
    equationRHS A₀ A₁ f W r z = equationRHS A₀ A₁ f V r z := by
  have hd : parameterDeriv W r z = parameterDeriv V r z := by
    funext i
    apply congrArg (fun g : ℂ → ℂ => deriv g z)
    funext w
    exact congrFun (h w) i
  simp only [equationRHS, matrixAction]
  rw [h z, hd]

theorem radialInverse_congr_at {F G : Field} {r : ℝ} {z : ℂ}
    (h : ∀ t ∈ Icc (0 : ℝ) 1, F (t * r) z = G (t * r) z) :
    radialInverse F r z = radialInverse G r z := by
  funext i
  unfold radialInverse
  congr 1
  apply intervalIntegral.integral_congr
  intro t ht
  change t ^ exponent i • F (t * r) z i = t ^ exponent i • G (t * r) z i
  rw [congrFun (h t (by simpa only [uIcc_of_le zero_le_one] using ht)) i]

/-- Gluing solves the equation on the entire symmetric interval. Equality
of the axis traces is the only matching fact needed for this identity. -/
theorem glue_integralEquation {R : ℝ} {U : Set ℂ} {A₀ A₁ : Coeff}
    {f Wp Wm : Field} (h0 : ∀ z, Wp 0 z = Wm 0 z)
    (hp : IntegralEquationOn (Icc 0 R) U A₀ A₁ f Wp)
    (hm : IntegralEquationOn (Icc 0 R) U (reflectCoeff A₀) (reflectCoeff A₁)
      (reflectedForcing f) Wm) :
    IntegralEquationOn (Icc (-R) R) U A₀ A₁ f (glue Wp Wm) := by
  intro r hr z hz
  by_cases hs : 0 ≤ r
  · rw [glue_nonneg Wp Wm hs, hp r ⟨hs, hr.2⟩ z hz]
    apply radialInverse_congr_at
    intro t ht
    exact (equationRHS_congr_at (fun w => glue_nonneg Wp Wm (mul_nonneg ht.1 hs) w) z).symm
  · have hs' : r ≤ 0 := le_of_not_ge hs
    have he := negativeHalf_equation hm r ⟨hr.1, hs'⟩ z hz
    change Wm (-r) z = _ at he
    rw [glue_nonpos h0 hs', he]
    apply radialInverse_congr_at
    intro t ht
    exact (equationRHS_congr_at
      (fun w => glue_nonpos h0 (mul_nonpos_of_nonneg_of_nonpos ht.1 hs') w) z).symm

theorem glue_parameter_holomorphic {R : ℝ} {U : Set ℂ} {Wp Wm : Field}
    (hp : ∀ r ∈ Icc 0 R, ∀ i, DifferentiableOn ℂ (fun z => Wp r z i) U)
    (hm : ∀ r ∈ Icc 0 R, ∀ i, DifferentiableOn ℂ (fun z => Wm r z i) U)
    {r : ℝ} (hr : r ∈ Icc (-R) R) (i : Fin 6) :
    DifferentiableOn ℂ (fun z => glue Wp Wm r z i) U := by
  by_cases hs : 0 ≤ r
  · simpa [glue, hs] using hp r ⟨hs, hr.2⟩ i
  · have hn : -r ∈ Icc 0 R := ⟨neg_nonneg.mpr (le_of_not_ge hs), by linarith [hr.1]⟩
    simpa [glue, hs] using hm (-r) hn i

theorem glue_jointly_continuous {R : ℝ} {U : Set ℂ} {Wp Wm : Field}
    (h0 : ∀ z ∈ U, Wp 0 z = Wm 0 z)
    (hp : ContinuousOn (fun p : ℝ × ℂ => Wp p.1 p.2) (Icc 0 R ×ˢ U))
    (hm : ContinuousOn (fun p : ℝ × ℂ => Wm p.1 p.2) (Icc 0 R ×ˢ U)) :
    ContinuousOn (fun p : ℝ × ℂ => glue Wp Wm p.1 p.2) (Icc (-R) R ×ˢ U) := by
  apply ContinuousOn.if
  · intro p h
    have he : (0 : ℝ) = p.1 :=
      frontier_le_subset_eq continuous_const continuous_fst h.2
    simpa only [← he, neg_zero] using h0 p.2 h.1.2
  · apply hp.mono
    intro p h
    have hh : 0 ≤ p.1 := by
      simpa only [(isClosed_le continuous_const continuous_fst).closure_eq, Set.mem_ofPred_eq]
          using h.2
    exact ⟨⟨hh, h.1.1.2⟩, h.1.2⟩
  · apply hm.comp (continuous_fst.neg.prodMk continuous_snd).continuousOn
    intro p h
    have hh : p.1 ≤ 0 :=
      closure_lt_subset_le continuous_fst continuous_const
        (show p ∈ closure {p : ℝ × ℂ | p.1 < 0} by simpa only [not_le] using h.2)
    exact ⟨⟨neg_nonneg.mpr hh, show -p.1 ≤ R by linarith [h.1.1.1]⟩, h.1.2⟩

/-- The symmetric regular integral solution, before the radial smoothness
bootstrap. No differentiability at the glued axis is assumed. -/
structure IsSymmetricIntegralSolution (R : ℝ) (U : Set ℂ)
    (A₀ A₁ : Coeff) (f W : Field) : Prop where
  jointly_continuous : ContinuousOn (fun p : ℝ × ℂ => W p.1 p.2) (Icc (-R) R ×ˢ U)
  parameter_holomorphic : ∀ r ∈ Icc (-R) R, ∀ i,
    DifferentiableOn ℂ (fun z => W r z i) U
  integral_equation : IntegralEquationOn (Icc (-R) R) U A₀ A₁ f W
  axis_zero : ∀ z ∈ U, W 0 z = 0

/-- Symmetric path: an abbreviation for `C(Icc (-R) R, E)`. -/
abbrev SymmetricPath (R : ℝ) (E : Type*) [TopologicalSpace E] := C(Icc (-R) R, E)
/-- Symmetric coefficient path: an abbreviation for `SymmetricPath R (Vec →L[ℂ] Vec)`. -/
abbrev SymmetricCoefficientPath (R : ℝ) := SymmetricPath R (Vec →L[ℂ] Vec)

/-- Positive embedding, given by `⟨fun x => ⟨x.1, ⟨(neg_nonpos.mpr hR).trans x.2.1, x.2.2⟩⟩,
continuous_subtype_val.subtype_mk _⟩`. -/
noncomputable def positiveEmbedding {R : ℝ} (hR : 0 ≤ R) :
    C(Icc (0 : ℝ) R, Icc (-R) R) :=
  ⟨fun x => ⟨x.1, ⟨(neg_nonpos.mpr hR).trans x.2.1, x.2.2⟩⟩,
    continuous_subtype_val.subtype_mk _⟩

/-- Negative embedding, given by `⟨fun x => ⟨-x.1, ⟨neg_le_neg x.2.2, (neg_nonpos.mpr
x.2.1).trans hR⟩⟩, continuous_subtype_val.neg.subtype_mk _⟩`. -/
noncomputable def negativeEmbedding {R : ℝ} (hR : 0 ≤ R) :
    C(Icc (0 : ℝ) R, Icc (-R) R) :=
  ⟨fun x => ⟨-x.1, ⟨neg_le_neg x.2.2, (neg_nonpos.mpr x.2.1).trans hR⟩⟩,
    continuous_subtype_val.neg.subtype_mk _⟩

/-- Side embedding, with branches according to `b`. -/
noncomputable def sideEmbedding {R : ℝ} (hR : 0 ≤ R) (b : Bool) :
    C(Icc (0 : ℝ) R, Icc (-R) R) :=
  if b then negativeEmbedding hR else positiveEmbedding hR

/-- Side restriction, constructed using `LinearMap.mkContinuous`. -/
noncomputable def sideRestriction {R : ℝ} {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℂ E] (hR : 0 ≤ R) (b : Bool) :
    SymmetricPath R E →L[ℂ] C(Icc (0 : ℝ) R, E) :=
  LinearMap.mkContinuous {
    toFun := fun f => f.comp (sideEmbedding hR b)
    map_add' := by intros; rfl
    map_smul' := by intros; rfl
  } 1 (by
    intro f
    rw [one_mul]
    apply (ContinuousMap.norm_le _ (norm_nonneg f)).mpr
    intro x
    exact f.norm_coe_le_norm _)

/-- Signed restriction, given by `(if b then (-1 : ℂ) else 1) • sideRestriction hR b`. -/
noncomputable def signedRestriction {R : ℝ} {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℂ E] (hR : 0 ≤ R) (b : Bool) :
    SymmetricPath R E →L[ℂ] C(Icc (0 : ℝ) R, E) :=
  (if b then (-1 : ℂ) else 1) • sideRestriction hR b

/-- Side data, defined pointwise by `signedRestriction hR b (F z)`. -/
noncomputable def sideData {R : ℝ} {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℂ E] (hR : 0 ≤ R) (b : Bool)
    (F : ℂ → SymmetricPath R E) : ℂ → C(Icc (0 : ℝ) R, E) :=
  fun z => signedRestriction hR b (F z)

@[simp] theorem sideData_false {R : ℝ} {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℂ E] (hR : 0 ≤ R)
    (F : ℂ → SymmetricPath R E) (z : ℂ) (x : Icc (0 : ℝ) R) :
    sideData hR false F z x = F z (positiveEmbedding hR x) := by
  simp [sideData, signedRestriction, sideRestriction, sideEmbedding]

@[simp] theorem sideData_true {R : ℝ} {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℂ E] (hR : 0 ≤ R)
    (F : ℂ → SymmetricPath R E) (z : ℂ) (x : Icc (0 : ℝ) R) :
    sideData hR true F z x = -F z (negativeEmbedding hR x) := by
  simp [sideData, signedRestriction, sideRestriction, sideEmbedding]

theorem sideData_holomorphic {R : ℝ} {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℂ E] (hR : 0 ≤ R) (b : Bool)
    {F : ℂ → SymmetricPath R E} {U : Set ℂ} (hF : DifferentiableOn ℂ F U) :
    DifferentiableOn ℂ (sideData hR b F) U := by
  exact (signedRestriction (E := E) hR b).differentiable.comp_differentiableOn hF

/-- Symmetric raw field, defined pointwise by `F z (projIcc (-R) R (by linarith) r)`. -/
noncomputable def symmetricRawField {R : ℝ} (hR : 0 ≤ R)
    (F : ℂ → SymmetricPath R Vec) : Field :=
  fun r z => F z (projIcc (-R) R (by linarith) r)

/-- Symmetric raw coefficient, defined pointwise by `LinearMap.toMatrix' (A z (projIcc (-R) R
(by linarith) r)).toLinearMap`. -/
noncomputable def symmetricRawCoefficient {R : ℝ} (hR : 0 ≤ R)
    (A : ℂ → SymmetricCoefficientPath R) : Coeff :=
  fun r z => LinearMap.toMatrix' (A z (projIcc (-R) R (by linarith) r)).toLinearMap

theorem sideRawField_pos {R : ℝ} (hR : 0 ≤ R)
    (F : ℂ → SymmetricPath R Vec) {r : ℝ} (hr : r ∈ Icc 0 R) (z : ℂ) :
    NilpotentVolterra.rawField hR (sideData hR false F) r z =
      symmetricRawField hR F r z := by
  simp only [NilpotentVolterra.rawField, NilpotentVolterra.extendPath, sideData_false,
    symmetricRawField]
  rw [projIcc_of_mem hR hr, projIcc_of_mem (by linarith : -R ≤ R)
    ⟨(neg_nonpos.mpr hR).trans hr.1, hr.2⟩]
  rfl

theorem sideRawField_neg {R : ℝ} (hR : 0 ≤ R)
    (F : ℂ → SymmetricPath R Vec) {r : ℝ} (hr : r ∈ Icc 0 R) (z : ℂ) :
    NilpotentVolterra.rawField hR (sideData hR true F) r z =
      reflectedForcing (symmetricRawField hR F) r z := by
  simp only [NilpotentVolterra.rawField, NilpotentVolterra.extendPath, sideData_true,
    symmetricRawField, reflectedForcing]
  rw [projIcc_of_mem hR hr, projIcc_of_mem (by linarith : -R ≤ R)
    ⟨neg_le_neg hr.2, (neg_nonpos.mpr hr.1).trans hR⟩]
  rfl

theorem sideRawCoefficient_pos {R : ℝ} (hR : 0 ≤ R)
    (A : ℂ → SymmetricCoefficientPath R) {r : ℝ} (hr : r ∈ Icc 0 R) (z : ℂ) :
    NilpotentVolterra.rawCoefficient hR (sideData hR false A) r z =
      symmetricRawCoefficient hR A r z := by
  simp only [NilpotentVolterra.rawCoefficient, sideData_false, symmetricRawCoefficient]
  rw [projIcc_of_mem hR hr, projIcc_of_mem (by linarith : -R ≤ R)
    ⟨(neg_nonpos.mpr hR).trans hr.1, hr.2⟩]
  rfl

theorem sideRawCoefficient_neg {R : ℝ} (hR : 0 ≤ R)
    (A : ℂ → SymmetricCoefficientPath R) {r : ℝ} (hr : r ∈ Icc 0 R) (z : ℂ) :
    NilpotentVolterra.rawCoefficient hR (sideData hR true A) r z =
      reflectCoeff (symmetricRawCoefficient hR A) r z := by
  simp only [NilpotentVolterra.rawCoefficient, sideData_true, symmetricRawCoefficient,
    reflectCoeff]
  rw [projIcc_of_mem hR hr, projIcc_of_mem (by linarith : -R ≤ R)
    ⟨neg_le_neg hr.2, (neg_nonpos.mpr hr.1).trans hR⟩]
  ext i j
  rfl

theorem side_shape {R : ℝ} (hR : 0 ≤ R)
    {A : ℂ → SymmetricCoefficientPath R}
    (hA : DerivativeShape (symmetricRawCoefficient hR A)) (b : Bool) :
    DerivativeShape (NilpotentVolterra.rawCoefficient hR (sideData hR b A)) := by
  intro r z i j hij
  let s := projIcc 0 R hR r
  have hs : NilpotentVolterra.rawCoefficient hR (sideData hR b A) r z =
      NilpotentVolterra.rawCoefficient hR (sideData hR b A) s z := by
    simp only [NilpotentVolterra.rawCoefficient, s, projIcc_val]
  rw [hs]
  cases b with
  | false => rw [sideRawCoefficient_pos hR A s.2 z]; exact hA s z i j hij
  | true =>
      rw [sideRawCoefficient_neg hR A s.2 z]
      change -symmetricRawCoefficient hR A (-s) z i j = 0
      rw [hA (-s) z i j hij, neg_zero]

/-- The positive solver's lifted function satisfies the normalized integral
equation, including its value at zero. -/
theorem lifted_integralEquation {R : ℝ} (hR : 0 ≤ R)
    {A₀ A₁ : ℂ → NilpotentVolterra.CoefficientPath R}
    {f W : ℂ → NilpotentVolterra.Path R} {U : Set ℂ}
    (hU : IsOpen U) (hWholo : DifferentiableOn ℂ W U)
    (hW : ∀ z ∈ U, W z = NilpotentVolterra.pathInverse hR exponent
      (NilpotentVolterra.rhsPath A₀ A₁ f W z)) :
    IntegralEquationOn (Icc 0 R) U (NilpotentVolterra.rawCoefficient hR A₀)
      (NilpotentVolterra.rawCoefficient hR A₁) (NilpotentVolterra.rawField hR f)
      (NilpotentVolterra.liftedField hR A₀ A₁ f W) := by
  intro r hr z hz
  change radialInverse (fun s z => NilpotentVolterra.extendPath hR
    (NilpotentVolterra.rhsPath A₀ A₁ f W z) s) r z = _
  apply radialInverse_congr_at
  intro t ht
  exact NilpotentVolterra.liftedField_rhs hR A₀ A₁ f W hU hWholo hW
    (NilpotentVolterra.scaled_radius_mem hr ht) hz

theorem positive_equation_change_data {R : ℝ} {U : Set ℂ}
    {A₀ A₁ B₀ B₁ : Coeff} {f g W : Field}
    (h : IntegralEquationOn (Icc 0 R) U A₀ A₁ f W)
    (h₀ : ∀ r ∈ Icc 0 R, ∀ z ∈ U, A₀ r z = B₀ r z)
    (h₁ : ∀ r ∈ Icc 0 R, ∀ z ∈ U, A₁ r z = B₁ r z)
    (hf : ∀ r ∈ Icc 0 R, ∀ z ∈ U, f r z = g r z) :
    IntegralEquationOn (Icc 0 R) U B₀ B₁ g W := by
  intro r hr z hz
  rw [h r hr z hz]
  apply radialInverse_congr_at
  intro t ht
  have htr := NilpotentVolterra.scaled_radius_mem hr ht
  simp only [equationRHS, matrixAction, h₀ _ htr _ hz, h₁ _ htr _ hz, hf _ htr _ hz]

/-- Side solution, constructed using `NilpotentVolterra.liftedField`. -/
noncomputable def sideSolution {R : ℝ} (hR : 0 ≤ R) (b : Bool)
    (A₀ A₁ : ℂ → SymmetricCoefficientPath R) (f : ℂ → SymmetricPath R Vec) : Field :=
  NilpotentVolterra.liftedField hR (sideData hR b A₀) (sideData hR b A₁) (sideData hR b f)
    (NilpotentVolterra.integralSolution hR
      (sideData hR b A₀) (sideData hR b A₁) (sideData hR b f))

/-- Two independently solved half-intervals are glued at their common zero
axis trace. No parity of the output occurs in this definition. -/
noncomputable def symmetricSolution {R : ℝ} (hR : 0 ≤ R)
    (A₀ A₁ : ℂ → SymmetricCoefficientPath R) (f : ℂ → SymmetricPath R Vec) : Field :=
  glue (sideSolution hR false A₀ A₁ f) (sideSolution hR true A₀ A₁ f)

theorem sideSolution_spec {R : ℝ} (hR : 0 ≤ R) (b : Bool)
    {A₀ A₁ : ℂ → SymmetricCoefficientPath R} {f : ℂ → SymmetricPath R Vec}
    {U : Set ℂ} (hU : IsOpen U)
    (hA₀ : DifferentiableOn ℂ A₀ U) (hA₁ : DifferentiableOn ℂ A₁ U)
    (hf : DifferentiableOn ℂ f U)
    (hshape : DerivativeShape (symmetricRawCoefficient hR A₁)) :
    NilpotentVolterra.IsRegularSolution R U
      (NilpotentVolterra.rawCoefficient hR (sideData hR b A₀))
      (NilpotentVolterra.rawCoefficient hR (sideData hR b A₁))
      (NilpotentVolterra.rawField hR (sideData hR b f)) (sideSolution hR b A₀ A₁ f) ∧
    IntegralEquationOn (Icc 0 R) U
      (NilpotentVolterra.rawCoefficient hR (sideData hR b A₀))
      (NilpotentVolterra.rawCoefficient hR (sideData hR b A₁))
      (NilpotentVolterra.rawField hR (sideData hR b f)) (sideSolution hR b A₀ A₁ f) ∧
    ∀ z, sideSolution hR b A₀ A₁ f 0 z = 0 := by
  obtain ⟨hholo, heq⟩ := NilpotentVolterra.integralSolution_spec_open hR hU
    (sideData_holomorphic hR b hA₀) (sideData_holomorphic hR b hA₁)
    (sideData_holomorphic hR b hf) (side_shape hR hshape b)
  exact ⟨NilpotentVolterra.liftedField_isRegularSolution hR _ _ _ _ hU hholo heq,
    lifted_integralEquation hR hU hholo heq,
    NilpotentVolterra.liftedField_axis_zero hR _ _ _ _⟩

/-- Actual existence on a symmetric radial interval. Only holomorphy in
the parameter and continuity in the radial coordinate are used here. -/
theorem symmetricSolution_spec {R : ℝ} (hR : 0 ≤ R)
    {A₀ A₁ : ℂ → SymmetricCoefficientPath R} {f : ℂ → SymmetricPath R Vec}
    {U : Set ℂ} (hU : IsOpen U)
    (hA₀ : DifferentiableOn ℂ A₀ U) (hA₁ : DifferentiableOn ℂ A₁ U)
    (hf : DifferentiableOn ℂ f U)
    (hshape : DerivativeShape (symmetricRawCoefficient hR A₁)) :
    IsSymmetricIntegralSolution R U (symmetricRawCoefficient hR A₀)
      (symmetricRawCoefficient hR A₁) (symmetricRawField hR f)
      (symmetricSolution hR A₀ A₁ f) := by
  obtain ⟨hp, hpEq, hpZero⟩ := sideSolution_spec hR false hU hA₀ hA₁ hf hshape
  obtain ⟨hm, hmEq, hmZero⟩ := sideSolution_spec hR true hU hA₀ hA₁ hf hshape
  have hzero : ∀ z, sideSolution hR false A₀ A₁ f 0 z =
      sideSolution hR true A₀ A₁ f 0 z := by
    intro z
    rw [hpZero z, hmZero z]
  have hpEq' : IntegralEquationOn (Icc 0 R) U (symmetricRawCoefficient hR A₀)
      (symmetricRawCoefficient hR A₁) (symmetricRawField hR f)
      (sideSolution hR false A₀ A₁ f) :=
    positive_equation_change_data hpEq
      (fun r hr z _ => sideRawCoefficient_pos hR A₀ hr z)
      (fun r hr z _ => sideRawCoefficient_pos hR A₁ hr z)
      (fun r hr z _ => sideRawField_pos hR f hr z)
  have hmEq' : IntegralEquationOn (Icc 0 R) U (reflectCoeff (symmetricRawCoefficient hR A₀))
      (reflectCoeff (symmetricRawCoefficient hR A₁)) (reflectedForcing (symmetricRawField hR f))
      (sideSolution hR true A₀ A₁ f) :=
    positive_equation_change_data hmEq
      (fun r hr z _ => sideRawCoefficient_neg hR A₀ hr z)
      (fun r hr z _ => sideRawCoefficient_neg hR A₁ hr z)
      (fun r hr z _ => sideRawField_neg hR f hr z)
  exact {
    jointly_continuous := glue_jointly_continuous (fun z _ => hzero z)
      hp.jointly_continuous hm.jointly_continuous
    parameter_holomorphic := fun _ hr i => glue_parameter_holomorphic
      hp.parameter_holomorphic hm.parameter_holomorphic hr i
    integral_equation := glue_integralEquation hzero hpEq' hmEq'
    axis_zero := fun z _ => (glue_nonneg _ _ le_rfl z).trans (hpZero z) }

theorem exists_symmetric_integral_solution {R : ℝ} (hR : 0 ≤ R)
    {A₀ A₁ : ℂ → SymmetricCoefficientPath R} {f : ℂ → SymmetricPath R Vec}
    {U : Set ℂ} (hU : IsOpen U)
    (hA₀ : DifferentiableOn ℂ A₀ U) (hA₁ : DifferentiableOn ℂ A₁ U)
    (hf : DifferentiableOn ℂ f U)
    (hshape : DerivativeShape (symmetricRawCoefficient hR A₁)) :
    ∃ W, IsSymmetricIntegralSolution R U (symmetricRawCoefficient hR A₀)
      (symmetricRawCoefficient hR A₁) (symmetricRawField hR f) W :=
  ⟨symmetricSolution hR A₀ A₁ f, symmetricSolution_spec hR hU hA₀ hA₁ hf hshape⟩

theorem reflected_matrix_parity {S : Set ℝ} {U : Set ℂ} {A : Coeff}
    (hA : CoefficientParityOn S U A) {r : ℝ} (hr : r ∈ S)
    {z : ℂ} (hz : z ∈ U) (v : Vec) :
    (reflectCoeff A r z).mulVec (parityVec v) = parityVec ((A r z).mulVec v) := by
  funext i
  simp only [Matrix.mulVec, dotProduct, parityVec_apply, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  change (-A (-r) z i j) * (paritySign j * v j) = paritySign i * (A r z i j * v j)
  rw [hA r hr z hz i j]
  calc
    _ = paritySign i * A r z i j * (paritySign j * paritySign j) * v j := by ring
    _ = _ := by rw [paritySign_mul_self]; ring

theorem reflected_forcing_parity {S : Set ℝ} {U : Set ℂ} {f : Field}
    (hf : ForcingParityOn S U f) {r : ℝ} (hr : r ∈ S) {z : ℂ} (hz : z ∈ U) :
    reflectedForcing f r z = parityVec (f r z) := by
  funext i
  change -f (-r) z i = paritySign i * f r z i
  rw [hf r hr z hz i]
  ring

/-- Parity path, given by `ContinuousLinearMap.compLeftContinuous ℂ (Icc (0 : ℝ) R) parityVec`. -/
noncomputable def parityPath (R : ℝ) :
    NilpotentVolterra.Path R →L[ℂ] NilpotentVolterra.Path R :=
  ContinuousLinearMap.compLeftContinuous ℂ (Icc (0 : ℝ) R) parityVec

@[simp] theorem parityPath_apply {R : ℝ} (W : NilpotentVolterra.Path R)
    (r : Icc (0 : ℝ) R) : parityPath R W r = parityVec (W r) := rfl

@[simp] theorem parityPath_involutive {R : ℝ} (W : NilpotentVolterra.Path R) :
    parityPath R (parityPath R W) = W := by
  ext r i
  exact congrFun (parityVec_involutive (W r)) i

theorem parityPath_deriv {R : ℝ} {W : ℂ → NilpotentVolterra.Path R} {z : ℂ}
    (hW : DifferentiableAt ℂ W z) :
    deriv (fun w => parityPath R (W w)) z = parityPath R (deriv W z) :=
  ((parityPath R).hasFDerivAt.comp_hasDerivAt z hW.hasDerivAt).deriv

/-- The diagonal parity action commutes with the actual radial integral. -/
theorem parityPath_inverse {R : ℝ} (hR : 0 ≤ R) (W : NilpotentVolterra.Path R) :
    parityPath R (NilpotentVolterra.pathInverse hR exponent W) =
      NilpotentVolterra.pathInverse hR exponent (parityPath R W) := by
  ext r i
  change paritySign i • ((r : ℝ) • (∫ t in (0 : ℝ)..1,
      (t ^ exponent i) • NilpotentVolterra.extendPath hR W (t * r) i)) =
    (r : ℝ) • (∫ t in (0 : ℝ)..1,
      (t ^ exponent i) • (paritySign i • NilpotentVolterra.extendPath hR W (t * r) i))
  rw [smul_comm (paritySign i), ← intervalIntegral.integral_smul]
  congr 1
  apply intervalIntegral.integral_congr
  intro t ht
  exact smul_comm _ _ _

theorem sideData_coefficient_parity {R : ℝ} (hR : 0 ≤ R)
    {A : ℂ → SymmetricCoefficientPath R} {U : Set ℂ}
    (hA : CoefficientParityOn (Icc 0 R) U (symmetricRawCoefficient hR A))
    {z : ℂ} (hz : z ∈ U) (r : Icc (0 : ℝ) R) (v : Vec) :
    sideData hR true A z r (parityVec v) = parityVec (sideData hR false A z r v) := by
  have hh := reflected_matrix_parity hA r.2 hz v
  rw [← sideRawCoefficient_neg hR A r.2 z, ← sideRawCoefficient_pos hR A r.2 z] at hh
  simpa only [NilpotentVolterra.rawCoefficient_mulVec, projIcc_val] using hh

theorem sideData_forcing_parity {R : ℝ} (hR : 0 ≤ R)
    {f : ℂ → SymmetricPath R Vec} {U : Set ℂ}
    (hf : ForcingParityOn (Icc 0 R) U (symmetricRawField hR f))
    {z : ℂ} (hz : z ∈ U) (r : Icc (0 : ℝ) R) :
    sideData hR true f z r = parityVec (sideData hR false f z r) := by
  have hh := reflected_forcing_parity hf r.2 hz
  rw [← sideRawField_neg hR f r.2 z, ← sideRawField_pos hR f r.2 z] at hh
  simpa only [NilpotentVolterra.rawField, NilpotentVolterra.extendPath, projIcc_val] using hh

theorem rhsPath_parity {R : ℝ} (hR : 0 ≤ R)
    {A₀ A₁ : ℂ → SymmetricCoefficientPath R} {f : ℂ → SymmetricPath R Vec}
    {W : ℂ → NilpotentVolterra.Path R} {U : Set ℂ}
    (hA₀ : CoefficientParityOn (Icc 0 R) U (symmetricRawCoefficient hR A₀))
    (hA₁ : CoefficientParityOn (Icc 0 R) U (symmetricRawCoefficient hR A₁))
    (hf : ForcingParityOn (Icc 0 R) U (symmetricRawField hR f))
    {z : ℂ} (hz : z ∈ U) (hW : DifferentiableAt ℂ W z) :
    NilpotentVolterra.rhsPath (sideData hR true A₀) (sideData hR true A₁)
      (sideData hR true f) (fun w => parityPath R (W w)) z =
    parityPath R (NilpotentVolterra.rhsPath (sideData hR false A₀)
      (sideData hR false A₁) (sideData hR false f) W z) := by
  unfold NilpotentVolterra.rhsPath
  rw [parityPath_deriv hW]
  ext r i
  change (sideData hR true f z r + ((sideData hR true A₀ z r) (parityVec (W z r)) +
    (sideData hR true A₁ z r) (parityVec (deriv W z r)))) i =
    (parityVec (sideData hR false f z r +
      ((sideData hR false A₀ z r) (W z r) +
        (sideData hR false A₁ z r) (deriv W z r)))) i
  rw [sideData_forcing_parity hR hf hz r,
    sideData_coefficient_parity hR hA₀ hz r,
    sideData_coefficient_parity hR hA₁ hz r, map_add, map_add]

/-- Parity transforms a solution of the positive equation into a solution
of the reflected positive equation. -/
theorem parity_transforms_equation {R : ℝ} (hR : 0 ≤ R)
    {A₀ A₁ : ℂ → SymmetricCoefficientPath R} {f : ℂ → SymmetricPath R Vec}
    {W : ℂ → NilpotentVolterra.Path R} {U : Set ℂ} (hU : IsOpen U)
    (hW : DifferentiableOn ℂ W U)
    (hA₀ : CoefficientParityOn (Icc 0 R) U (symmetricRawCoefficient hR A₀))
    (hA₁ : CoefficientParityOn (Icc 0 R) U (symmetricRawCoefficient hR A₁))
    (hf : ForcingParityOn (Icc 0 R) U (symmetricRawField hR f))
    (heq : ∀ z ∈ U, W z = NilpotentVolterra.pathInverse hR exponent
      (NilpotentVolterra.rhsPath (sideData hR false A₀) (sideData hR false A₁)
        (sideData hR false f) W z)) :
    ∀ z ∈ U, parityPath R (W z) = NilpotentVolterra.pathInverse hR exponent
      (NilpotentVolterra.rhsPath (sideData hR true A₀) (sideData hR true A₁)
        (sideData hR true f) (fun w => parityPath R (W w)) z) := by
  intro z hz
  rw [rhsPath_parity hR hA₀ hA₁ hf hz (hW.differentiableAt (hU.mem_nhds hz)),
    heq z hz, parityPath_inverse]

/-- The half-interval solutions have the required relation by uniqueness
of the genuine integral equation. -/
theorem side_curves_parity {R : ℝ} (hR : 0 ≤ R)
    {A₀ A₁ : ℂ → SymmetricCoefficientPath R} {f : ℂ → SymmetricPath R Vec}
    {U : Set ℂ} (hU : IsOpen U)
    (hA₀ : DifferentiableOn ℂ A₀ U) (hA₁ : DifferentiableOn ℂ A₁ U)
    (hf : DifferentiableOn ℂ f U)
    (hshape : DerivativeShape (symmetricRawCoefficient hR A₁))
    (hpA₀ : CoefficientParityOn (Icc 0 R) U (symmetricRawCoefficient hR A₀))
    (hpA₁ : CoefficientParityOn (Icc 0 R) U (symmetricRawCoefficient hR A₁))
    (hpf : ForcingParityOn (Icc 0 R) U (symmetricRawField hR f)) :
    EqOn
      (NilpotentVolterra.integralSolution hR (sideData hR true A₀)
        (sideData hR true A₁) (sideData hR true f))
      (fun z => parityPath R (NilpotentVolterra.integralSolution hR
        (sideData hR false A₀) (sideData hR false A₁) (sideData hR false f) z)) U := by
  obtain ⟨hp, hpEq⟩ := NilpotentVolterra.integralSolution_spec_open hR hU
    (sideData_holomorphic hR false hA₀) (sideData_holomorphic hR false hA₁)
    (sideData_holomorphic hR false hf) (side_shape hR hshape false)
  obtain ⟨hm, hmEq⟩ := NilpotentVolterra.integralSolution_spec_open hR hU
    (sideData_holomorphic hR true hA₀) (sideData_holomorphic hR true hA₁)
    (sideData_holomorphic hR true hf) (side_shape hR hshape true)
  exact NilpotentVolterra.integral_solution_unique hR hU
    (sideData_holomorphic hR true hA₀) (sideData_holomorphic hR true hA₁)
    hm ((parityPath R).differentiable.comp_differentiableOn hp)
    (side_shape hR hshape true) hmEq
    (parity_transforms_equation hR hU hp hpA₀ hpA₁ hpf hpEq)

theorem sideSolution_parity {R : ℝ} (hR : 0 ≤ R)
    {A₀ A₁ : ℂ → SymmetricCoefficientPath R} {f : ℂ → SymmetricPath R Vec}
    {U : Set ℂ} (hU : IsOpen U)
    (hA₀ : DifferentiableOn ℂ A₀ U) (hA₁ : DifferentiableOn ℂ A₁ U)
    (hf : DifferentiableOn ℂ f U)
    (hshape : DerivativeShape (symmetricRawCoefficient hR A₁))
    (hpA₀ : CoefficientParityOn (Icc 0 R) U (symmetricRawCoefficient hR A₀))
    (hpA₁ : CoefficientParityOn (Icc 0 R) U (symmetricRawCoefficient hR A₁))
    (hpf : ForcingParityOn (Icc 0 R) U (symmetricRawField hR f))
    {r : ℝ} (hr : r ∈ Icc 0 R) {z : ℂ} (hz : z ∈ U) :
    sideSolution hR true A₀ A₁ f r z =
      parityVec (sideSolution hR false A₀ A₁ f r z) := by
  obtain ⟨_, hpEq⟩ := NilpotentVolterra.integralSolution_spec_open hR hU
    (sideData_holomorphic hR false hA₀) (sideData_holomorphic hR false hA₁)
    (sideData_holomorphic hR false hf) (side_shape hR hshape false)
  obtain ⟨_, hmEq⟩ := NilpotentVolterra.integralSolution_spec_open hR hU
    (sideData_holomorphic hR true hA₀) (sideData_holomorphic hR true hA₁)
    (sideData_holomorphic hR true hf) (side_shape hR hshape true)
  unfold sideSolution
  rw [NilpotentVolterra.liftedField_eq_trace hR _ _ _ _ (hmEq z hz) hr,
    NilpotentVolterra.liftedField_eq_trace hR _ _ _ _ (hpEq z hz) hr]
  exact congrArg (fun V : NilpotentVolterra.Path R => V (projIcc 0 R hR r))
    (side_curves_parity hR hU hA₀ hA₁ hf hshape hpA₀ hpA₁ hpf hz)

/-- The actual symmetric solution has the prescribed vector parity.
The coefficient/source parity hypotheses are transformed through the
integral equation, and equality follows from holomorphic uniqueness. -/
theorem symmetricSolution_parity {R : ℝ} (hR : 0 ≤ R)
    {A₀ A₁ : ℂ → SymmetricCoefficientPath R} {f : ℂ → SymmetricPath R Vec}
    {U : Set ℂ} (hU : IsOpen U)
    (hA₀ : DifferentiableOn ℂ A₀ U) (hA₁ : DifferentiableOn ℂ A₁ U)
    (hf : DifferentiableOn ℂ f U)
    (hshape : DerivativeShape (symmetricRawCoefficient hR A₁))
    (hpA₀ : CoefficientParityOn (Icc 0 R) U (symmetricRawCoefficient hR A₀))
    (hpA₁ : CoefficientParityOn (Icc 0 R) U (symmetricRawCoefficient hR A₁))
    (hpf : ForcingParityOn (Icc 0 R) U (symmetricRawField hR f))
    {r : ℝ} (hr : r ∈ Icc (-R) R) {z : ℂ} (hz : z ∈ U) :
    symmetricSolution hR A₀ A₁ f (-r) z =
      parityVec (symmetricSolution hR A₀ A₁ f r z) := by
  have hzero : ∀ w, sideSolution hR false A₀ A₁ f 0 w =
      sideSolution hR true A₀ A₁ f 0 w := by
    intro w
    exact (NilpotentVolterra.liftedField_axis_zero hR _ _ _ _ w).trans
      (NilpotentVolterra.liftedField_axis_zero hR _ _ _ _ w).symm
  unfold symmetricSolution
  by_cases hs : 0 ≤ r
  · rw [glue_nonpos hzero (neg_nonpos.mpr hs), neg_neg, glue_nonneg _ _ hs]
    exact sideSolution_parity hR hU hA₀ hA₁ hf hshape hpA₀ hpA₁ hpf ⟨hs, hr.2⟩ hz
  · have hs' : r ≤ 0 := le_of_not_ge hs
    have hn : -r ∈ Icc 0 R := ⟨neg_nonneg.mpr hs', by linarith [hr.1]⟩
    rw [glue_nonneg _ _ hn.1, glue_nonpos hzero hs',
      sideSolution_parity hR hU hA₀ hA₁ hf hshape hpA₀ hpA₁ hpf hn hz,
      parityVec_involutive]

theorem symmetricSolution_parity_of_global {R : ℝ} (hR : 0 ≤ R)
    {A₀ A₁ : ℂ → SymmetricCoefficientPath R} {f : ℂ → SymmetricPath R Vec}
    {U : Set ℂ} (hU : IsOpen U)
    (hA₀ : DifferentiableOn ℂ A₀ U) (hA₁ : DifferentiableOn ℂ A₁ U)
    (hf : DifferentiableOn ℂ f U)
    (hshape : DerivativeShape (symmetricRawCoefficient hR A₁))
    (hpA₀ : CoefficientParity (symmetricRawCoefficient hR A₀))
    (hpA₁ : CoefficientParity (symmetricRawCoefficient hR A₁))
    (hpf : ForcingParity (symmetricRawField hR f))
    {r : ℝ} (hr : r ∈ Icc (-R) R) {z : ℂ} (hz : z ∈ U) :
    symmetricSolution hR A₀ A₁ f (-r) z =
      parityVec (symmetricSolution hR A₀ A₁ f r z) :=
  symmetricSolution_parity hR hU hA₀ hA₁ hf hshape
    (fun r _ z _ => hpA₀ r z) (fun r _ z _ => hpA₁ r z)
    (fun r _ z _ => hpf r z) hr hz

/-- This is the component form used by the smooth even-descent theorem. -/
theorem first_components_even {W : Field} {R : ℝ} {U : Set ℂ}
    (hW : ∀ r ∈ Icc (-R) R, ∀ z ∈ U, W (-r) z = parityVec (W r z))
    (i : Fin 6) (hi : i.val < 4) {z : ℂ} (hz : z ∈ U) :
    ∀ r ∈ Ioo (-R) R, W (-r) z i = W r z i := by
  intro r hr
  simpa [parityVec_apply, paritySign, hi] using congrFun (hW r ⟨hr.1.le, hr.2.le⟩ z hz) i

theorem last_components_odd {W : Field} {R : ℝ} {U : Set ℂ}
    (hW : ∀ r ∈ Icc (-R) R, ∀ z ∈ U, W (-r) z = parityVec (W r z))
    (i : Fin 6) (hi : 4 ≤ i.val) {z : ℂ} (hz : z ∈ U) :
    ∀ r ∈ Ioo (-R) R, W (-r) z i = -W r z i := by
  intro r hr
  simpa [parityVec_apply, paritySign, not_lt.mpr hi] using
    congrFun (hW r ⟨hr.1.le, hr.2.le⟩ z hz) i

/-- Two derivatives with the same value and axis trace glue to an ordinary
two-sided derivative. -/
theorem hasDerivAt_glue_zero {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f g : ℝ → E} {v : E} (hf : HasDerivAt f v 0) (hg : HasDerivAt g v 0)
    (h0 : f 0 = g 0) :
    HasDerivAt (fun r => if 0 ≤ r then f r else g r) v 0 := by
  apply hasDerivAt_iff_tendsto_slope_zero.mpr
  have hh := hf.tendsto_slope_zero.if' (p := fun r : ℝ => 0 ≤ r) hg.tendsto_slope_zero
  convert! hh using 1
  funext r
  by_cases hr : 0 ≤ r <;> simp [hr, h0]

/-- The derivatives from both sides match at the axis. The value is
determined by the forcing, with the exact singular-diagonal factor. -/
theorem symmetricSolution_hasDerivAt_zero {R : ℝ} (hR : 0 ≤ R)
    {A₀ A₁ : ℂ → SymmetricCoefficientPath R} {f : ℂ → SymmetricPath R Vec}
    {U : Set ℂ} (hU : IsOpen U)
    (hA₀ : DifferentiableOn ℂ A₀ U) (hA₁ : DifferentiableOn ℂ A₁ U)
    (hf : DifferentiableOn ℂ f U)
    (hshape : DerivativeShape (symmetricRawCoefficient hR A₁))
    {z : ℂ} (hz : z ∈ U) (i : Fin 6) :
    HasDerivAt (fun r => symmetricSolution hR A₀ A₁ f r z i)
      ((1 / ((exponent i : ℝ) + 1)) • symmetricRawField hR f 0 z i) 0 := by
  obtain ⟨hp, _, _⟩ := sideSolution_spec hR false hU hA₀ hA₁ hf hshape
  obtain ⟨hm, _, _⟩ := sideSolution_spec hR true hU hA₀ hA₁ hf hshape
  have hdp := (hp.radial_differentiable z hz i 0).hasDerivAt
  have heqp := hp.axis_derivative_eq_forcing hU hz i
  change deriv (fun r => sideSolution hR false A₀ A₁ f r z i) 0 = _ at heqp
  rw [heqp, sideRawField_pos hR f ⟨le_rfl, hR⟩ z] at hdp
  have hdm := (hm.radial_differentiable z hz i 0).hasDerivAt
  have heqm := hm.axis_derivative_eq_forcing hU hz i
  change deriv (fun r => sideSolution hR true A₀ A₁ f r z i) 0 = _ at heqm
  rw [heqm, sideRawField_neg hR f ⟨le_rfl, hR⟩ z] at hdm
  simp only [reflectedForcing, neg_zero, Pi.neg_apply, smul_neg] at hdm
  have hdneg : HasDerivAt (fun r => sideSolution hR true A₀ A₁ f (-r) z i)
      ((1 / ((exponent i : ℝ) + 1)) • symmetricRawField hR f 0 z i) 0 := by
    simpa only [Function.comp_def, neg_one_smul, neg_neg] using
      hdm.scomp_of_eq 0 (hasDerivAt_neg (0 : ℝ)) (by simp)
  have hzero : sideSolution hR false A₀ A₁ f 0 z i =
      sideSolution hR true A₀ A₁ f (-0) z i := by
    simpa only [neg_zero] using congrFun ((hp.axis_zero z hz).trans (hm.axis_zero z hz).symm) i
  simpa only [symmetricSolution, glue, ite_apply] using hasDerivAt_glue_zero hdp hdneg hzero

/-- Uniqueness of the glued actual lifts in the holomorphic path class.
Both sides are compared by the proved positive Volterra uniqueness
theorem; no uniqueness premise is introduced. -/
theorem glued_solution_unique {R : ℝ} (hR : 0 ≤ R) {U : Set ℂ} (hU : IsOpen U)
    {A₀ A₁ : Bool → ℂ → NilpotentVolterra.CoefficientPath R}
    {f W₀ W₁ : Bool → ℂ → NilpotentVolterra.Path R}
    (hA₀ : ∀ b, DifferentiableOn ℂ (A₀ b) U)
    (hA₁ : ∀ b, DifferentiableOn ℂ (A₁ b) U)
    (hW₀ : ∀ b, DifferentiableOn ℂ (W₀ b) U)
    (hW₁ : ∀ b, DifferentiableOn ℂ (W₁ b) U)
    (hshape : ∀ b, DerivativeShape (NilpotentVolterra.rawCoefficient hR (A₁ b)))
    (heq₀ : ∀ b z, z ∈ U → W₀ b z = NilpotentVolterra.pathInverse hR exponent
      (NilpotentVolterra.rhsPath (A₀ b) (A₁ b) (f b) (W₀ b) z))
    (heq₁ : ∀ b z, z ∈ U → W₁ b z = NilpotentVolterra.pathInverse hR exponent
      (NilpotentVolterra.rhsPath (A₀ b) (A₁ b) (f b) (W₁ b) z))
    (r : ℝ) {z : ℂ} (hz : z ∈ U) :
    glue (NilpotentVolterra.liftedField hR (A₀ false) (A₁ false) (f false) (W₀ false))
      (NilpotentVolterra.liftedField hR (A₀ true) (A₁ true) (f true) (W₀ true)) r z =
    glue (NilpotentVolterra.liftedField hR (A₀ false) (A₁ false) (f false) (W₁ false))
      (NilpotentVolterra.liftedField hR (A₀ true) (A₁ true) (f true) (W₁ true)) r z := by
  have heq (b : Bool) : EqOn (W₀ b) (W₁ b) U :=
    NilpotentVolterra.integral_solution_unique hR hU (hA₀ b) (hA₁ b) (hW₀ b) (hW₁ b)
      (hshape b) (heq₀ b) (heq₁ b)
  have hboth (b : Bool) (s : ℝ) :
      NilpotentVolterra.liftedField hR (A₀ b) (A₁ b) (f b) (W₀ b) s z =
      NilpotentVolterra.liftedField hR (A₀ b) (A₁ b) (f b) (W₁ b) s z := by
    have hder : deriv (W₀ b) z = deriv (W₁ b) z :=
      (show W₀ b =ᶠ[𝓝 z] W₁ b from Filter.eventuallyEq_of_mem (hU.mem_nhds hz) (heq b)).deriv_eq
    have hrhs : NilpotentVolterra.rhsPath (A₀ b) (A₁ b) (f b) (W₀ b) z =
        NilpotentVolterra.rhsPath (A₀ b) (A₁ b) (f b) (W₁ b) z := by
      simp only [NilpotentVolterra.rhsPath, heq b hz, hder]
    unfold NilpotentVolterra.liftedField
    rw [hrhs]
  unfold glue
  split_ifs
  · exact hboth false r
  · exact hboth true (-r)

end NavierStokes.VolterraParity
