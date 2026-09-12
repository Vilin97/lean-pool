/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import LeanPool.NavierStokesAndEuler.NavierStokes.SmoothFourierData
public import LeanPool.NavierStokesAndEuler.NavierStokes.SmoothLoop
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.MeasureTheory.Measure.Haar.Unique
public import LeanPool.NavierStokesAndEuler.NavierStokes.GaussianEnvelope
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
public import LeanPool.NavierStokesAndEuler.NavierStokes.FlatCutoff
public import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.SpecialFunctions.Sqrt
public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

/-!
# Actual torus and native-coordinate averages

The integer covering is treated as an actual surjective additive homomorphism
of the compact torus. Haar invariance is a conclusion, not an assumption.
-/

section

/-!
# Concentration of actual pulse covariance columns

We use `r = sqrt L`, so that a slot has length `r^2`.  Pointwise Gaussian
bounds on the fundamental component and an actual compactly supported cutoff
give mass of order `r` and first centered moment of order `r^2`.  Division by
the mass then gives a direction error of order `1/r`.
-/

section

/-!
# Smooth positive covariance solves

For an actual real two-by-two matrix and target, the signed areas in Cramer's
rule give an explicit strict cone. On that cone, the inverse solution and its
positive square roots depend smoothly on smooth input data. A compact family
has a uniform positive lower bound and a uniform tolerance for perturbing both
the matrix and the target.

No assertion here supplies smoothness or error estimates for the manuscript's
integrated columns. No assertion concerns extension through a zero-amplitude
edge, where the strict cone hypotheses fail.
-/

section

/-!
# Two signed covariance slots

The finite-dimensional algebra underlying Lemma 8.7 and equation (29) of the
candidate manuscript. In the orthonormal `(N,K)` coordinates, the two normalized
columns are `(-a,-b)` and `(-a,b)`, with positive column scales. A target `(-m,t)`
lies strictly between them precisely when `|a*t| < b*m`.

The actual integrated columns in the manuscript include approximation errors.
This file does not identify those columns with the exact model, or prove the
Gaussian, parameter-derivative, or flat-edge estimates.
-/

@[expose] public section

noncomputable section

namespace NavierStokes.Covariance

open Matrix

/-- The two columns, with their individual positive size factors. -/
def signedMatrix (a b scaleMinus scalePlus : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![-a * scaleMinus, -a * scalePlus;
     -b * scaleMinus,  b * scalePlus]

/-- The stress target in normal and transverse coordinates. -/
def target (m t : ℝ) : Fin 2 → ℝ := ![-m, t]

/-- Explicit squared amplitudes for the two signed slots. -/
def coefficients (a b scaleMinus scalePlus m t : ℝ) : Fin 2 → ℝ :=
  ![(b * m - a * t) / (2 * a * b * scaleMinus),
    (b * m + a * t) / (2 * a * b * scalePlus)]

theorem determinant_formula (a b scaleMinus scalePlus : ℝ) :
    (signedMatrix a b scaleMinus scalePlus).det =
      -(2 * a * b * scaleMinus * scalePlus) := by
  simp [signedMatrix, Matrix.det_fin_two]
  ring

theorem determinant_neg {a b scaleMinus scalePlus : ℝ}
    (ha : 0 < a) (hb : 0 < b)
    (hMinus : 0 < scaleMinus) (hPlus : 0 < scalePlus) :
    (signedMatrix a b scaleMinus scalePlus).det < 0 := by
  rw [determinant_formula]
  have : 0 < 2 * a * b * scaleMinus * scalePlus := by positivity
  linarith

theorem determinant_ne_zero {a b scaleMinus scalePlus : ℝ}
    (ha : 0 < a) (hb : 0 < b)
    (hMinus : 0 < scaleMinus) (hPlus : 0 < scalePlus) :
    (signedMatrix a b scaleMinus scalePlus).det ≠ 0 :=
  ne_of_lt (determinant_neg ha hb hMinus hPlus)

/-- The explicit coefficients solve the two covariance equations exactly. -/
theorem reconstruct {a b scaleMinus scalePlus : ℝ} (m t : ℝ)
    (ha : a ≠ 0) (hb : b ≠ 0)
    (hMinus : scaleMinus ≠ 0) (hPlus : scalePlus ≠ 0) :
    (signedMatrix a b scaleMinus scalePlus).mulVec
      (coefficients a b scaleMinus scalePlus m t) = target m t := by
  ext i
  fin_cases i <;>
    simp [signedMatrix, coefficients, target, Matrix.mulVec, dotProduct,
      Fin.sum_univ_two] <;>
    field_simp <;> ring

/-- Thus the explicit formula is the matrix inverse applied to the stress. -/
theorem inverse_formula {a b scaleMinus scalePlus : ℝ} (m t : ℝ)
    (ha : 0 < a) (hb : 0 < b)
    (hMinus : 0 < scaleMinus) (hPlus : 0 < scalePlus) :
    (signedMatrix a b scaleMinus scalePlus)⁻¹.mulVec (target m t) =
      coefficients a b scaleMinus scalePlus m t := by
  have hdet : IsUnit (signedMatrix a b scaleMinus scalePlus).det :=
    isUnit_iff_ne_zero.mpr (determinant_ne_zero ha hb hMinus hPlus)
  rw [← reconstruct m t (ne_of_gt ha) (ne_of_gt hb)
    (ne_of_gt hMinus) (ne_of_gt hPlus)]
  rw [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ hdet, Matrix.one_mulVec]

theorem solution_unique {a b scaleMinus scalePlus m t : ℝ}
    (ha : 0 < a) (hb : 0 < b)
    (hMinus : 0 < scaleMinus) (hPlus : 0 < scalePlus)
    (y : Fin 2 → ℝ)
    (hy : (signedMatrix a b scaleMinus scalePlus).mulVec y = target m t) :
    y = coefficients a b scaleMinus scalePlus m t := by
  have hdet : IsUnit (signedMatrix a b scaleMinus scalePlus).det :=
    isUnit_iff_ne_zero.mpr (determinant_ne_zero ha hb hMinus hPlus)
  calc
    y = (signedMatrix a b scaleMinus scalePlus)⁻¹.mulVec
        ((signedMatrix a b scaleMinus scalePlus).mulVec y) := by
      rw [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ hdet, Matrix.one_mulVec]
    _ = (signedMatrix a b scaleMinus scalePlus)⁻¹.mulVec (target m t) := by rw [hy]
    _ = coefficients a b scaleMinus scalePlus m t :=
      inverse_formula m t ha hb hMinus hPlus

/-- A strict geometric cone condition makes both squared amplitudes positive. -/
theorem coefficients_pos {a b scaleMinus scalePlus m t : ℝ}
    (ha : 0 < a) (hb : 0 < b)
    (hMinus : 0 < scaleMinus) (hPlus : 0 < scalePlus)
    (hcone : |a * t| < b * m) :
    ∀ i, 0 < coefficients a b scaleMinus scalePlus m t i := by
  have hc := abs_lt.mp hcone
  intro i
  fin_cases i
  · change 0 < (b * m - a * t) / (2 * a * b * scaleMinus)
    exact div_pos (by linarith) (by positivity)
  · change 0 < (b * m + a * t) / (2 * a * b * scalePlus)
    exact div_pos (by linarith) (by positivity)

/-- The same strict cone condition is necessary as well as sufficient. -/
theorem coefficients_pos_iff {a b scaleMinus scalePlus m t : ℝ}
    (ha : 0 < a) (hb : 0 < b)
    (hMinus : 0 < scaleMinus) (hPlus : 0 < scalePlus) :
    (∀ i, 0 < coefficients a b scaleMinus scalePlus m t i) ↔ |a * t| < b * m := by
  constructor
  · intro hy
    have hm : 0 < 2 * a * b * scaleMinus := by positivity
    have hp : 0 < 2 * a * b * scalePlus := by positivity
    have hnMinus : 0 < b * m - a * t :=
      (div_pos_iff_of_pos_right hm).mp (by simpa [coefficients] using hy 0)
    have hnPlus : 0 < b * m + a * t :=
      (div_pos_iff_of_pos_right hp).mp (by simpa [coefficients] using hy 1)
    exact abs_lt.mpr ⟨by linarith, by linarith⟩
  · exact coefficients_pos ha hb hMinus hPlus

/-- The primary velocity amplitudes are positive square roots of the solve. -/
def amplitudes (a b scaleMinus scalePlus m t : ℝ) : Fin 2 → ℝ :=
  fun i => Real.sqrt (coefficients a b scaleMinus scalePlus m t i)

theorem amplitudes_pos {a b scaleMinus scalePlus m t : ℝ}
    (ha : 0 < a) (hb : 0 < b)
    (hMinus : 0 < scaleMinus) (hPlus : 0 < scalePlus)
    (hcone : |a * t| < b * m) :
    ∀ i, 0 < amplitudes a b scaleMinus scalePlus m t i := by
  intro i
  exact Real.sqrt_pos.mpr (coefficients_pos ha hb hMinus hPlus hcone i)

theorem amplitudes_sq {a b scaleMinus scalePlus m t : ℝ}
    (ha : 0 < a) (hb : 0 < b)
    (hMinus : 0 < scaleMinus) (hPlus : 0 < scalePlus)
    (hcone : |a * t| < b * m) :
    (fun i => (amplitudes a b scaleMinus scalePlus m t i) ^ 2) =
      coefficients a b scaleMinus scalePlus m t := by
  funext i
  exact Real.sq_sqrt (le_of_lt (coefficients_pos ha hb hMinus hPlus hcone i))

/-- Squared positive velocity amplitudes reproduce the exact model covariance. -/
theorem reconstruct_from_amplitudes {a b scaleMinus scalePlus m t : ℝ}
    (ha : 0 < a) (hb : 0 < b)
    (hMinus : 0 < scaleMinus) (hPlus : 0 < scalePlus)
    (hcone : |a * t| < b * m) :
    (signedMatrix a b scaleMinus scalePlus).mulVec
        (fun i => (amplitudes a b scaleMinus scalePlus m t i) ^ 2) = target m t := by
  rw [amplitudes_sq ha hb hMinus hPlus hcone]
  exact reconstruct m t (ne_of_gt ha) (ne_of_gt hb) (ne_of_gt hMinus) (ne_of_gt hPlus)

/-- The square-root viscosity factor and any common partition mask in (29)
produce precisely the expected factor `ε * mask^2` in covariance. -/
theorem scaled_primary_covariance {a b scaleMinus scalePlus m t ε : ℝ}
    (mask : ℝ) (hε : 0 ≤ ε)
    (ha : 0 < a) (hb : 0 < b)
    (hMinus : 0 < scaleMinus) (hPlus : 0 < scalePlus)
    (hcone : |a * t| < b * m) :
    (signedMatrix a b scaleMinus scalePlus).mulVec
        (fun i => (Real.sqrt ε * amplitudes a b scaleMinus scalePlus m t i * mask) ^ 2) =
      (ε * mask ^ 2) • target m t := by
  have hsq :
      (fun i => (Real.sqrt ε * amplitudes a b scaleMinus scalePlus m t i * mask) ^ 2) =
        (ε * mask ^ 2) • (fun i => (amplitudes a b scaleMinus scalePlus m t i) ^ 2) := by
    funext i
    simp only [Pi.smul_apply, smul_eq_mul, mul_pow, Real.sq_sqrt hε]
    ring
  rw [hsq, Matrix.mulVec_smul, reconstruct_from_amplitudes ha hb hMinus hPlus hcone]

/-- Positive normal magnitude in the manuscript's signed directions. -/
def normalMagnitude (c u : ℝ) : ℝ := -c * Real.sqrt (1 + u ^ 2)

theorem normalMagnitude_pos {c u : ℝ} (hc : c < 0) : 0 < normalMagnitude c u := by
  unfold normalMagnitude
  exact mul_pos (neg_pos.mpr hc) (Real.sqrt_pos.mpr (by nlinarith [sq_nonneg u]))

/-- The manuscript's strict ratio choice for `u_*` implies the exact cone test. -/
theorem cone_of_ratio {c u m t : ℝ} (hm : 0 < m)
    (hratio : |c * t / m| < u / Real.sqrt (1 + u ^ 2)) :
    |normalMagnitude c u * t| < u * m := by
  have hs : 0 < Real.sqrt (1 + u ^ 2) :=
    Real.sqrt_pos.mpr (by nlinarith [sq_nonneg u])
  have hr : |c * t| / m < u / Real.sqrt (1 + u ^ 2) := by
    simpa only [abs_div, abs_of_pos hm] using hratio
  have hcross : |c * t| * Real.sqrt (1 + u ^ 2) < u * m :=
    (div_lt_div_iff₀ hm hs).mp hr
  calc
    |normalMagnitude c u * t| = |c * t| * Real.sqrt (1 + u ^ 2) := by
      rw [show normalMagnitude c u * t = -(c * t) * Real.sqrt (1 + u ^ 2) by
        unfold normalMagnitude
        ring]
      rw [abs_mul, abs_neg, abs_of_pos hs]
    _ < u * m := hcross

/-- The exact signed-slot model has positive primary amplitudes under the
ratio condition stated in Section 8.3. This asserts no analytic error bound. -/
theorem positive_primary {c u scaleMinus scalePlus m t : ℝ}
    (hc : c < 0) (hu : 0 < u) (hm : 0 < m)
    (hMinus : 0 < scaleMinus) (hPlus : 0 < scalePlus)
    (hratio : |c * t / m| < u / Real.sqrt (1 + u ^ 2)) :
    ∃ velocity : Fin 2 → ℝ,
      (∀ i, 0 < velocity i) ∧
      (signedMatrix (normalMagnitude c u) u scaleMinus scalePlus).mulVec
        (fun i => (velocity i) ^ 2) = target m t := by
  refine ⟨amplitudes (normalMagnitude c u) u scaleMinus scalePlus m t, ?_, ?_⟩
  · exact amplitudes_pos (normalMagnitude_pos hc) hu hMinus hPlus
      (cone_of_ratio hm hratio)
  · exact reconstruct_from_amplitudes (normalMagnitude_pos hc) hu hMinus hPlus
      (cone_of_ratio hm hratio)

end NavierStokes.Covariance

end
end

end

@[expose] public section

noncomputable section

namespace NavierStokes.SmoothCovariance

open Matrix Set
open scoped ContDiff Topology

/-- Mat2: an abbreviation for `Matrix (Fin 2) (Fin 2) ℝ`. -/
abbrev Mat2 := Matrix (Fin 2) (Fin 2) ℝ
/-- Vec2: an abbreviation for `Fin 2 → ℝ /- The entrywise sup norm makes all metric assertions
below unambiguous. -/`. -/
abbrev Vec2 := Fin 2 → ℝ

/- The entrywise sup norm makes all metric assertions below unambiguous. -/
/-- Cache the standard `NormedAddCommGroup Mat2` instance to shorten typeclass synthesis. -/
local instance instSmoothCovariance1 : NormedAddCommGroup Mat2 :=
  inferInstanceAs (NormedAddCommGroup (Fin 2 → Fin 2 → ℝ))

/-- Cache the standard `NormedSpace ℝ Mat2` instance to shorten typeclass synthesis. -/
local instance instSmoothCovariance2 : NormedSpace ℝ Mat2 :=
  inferInstanceAs (NormedSpace ℝ (Fin 2 → Fin 2 → ℝ))

/-- Datum: an abbreviation for `Mat2 × Vec2`. -/
abbrev Datum := Mat2 × Vec2

/-- Oriented areas obtained by replacing each column by the target. -/
def cramerNumerator (H : Mat2) (T : Vec2) : Vec2 :=
  ![T 0 * H 1 1 - H 0 1 * T 1, H 0 0 * T 1 - T 0 * H 1 0]

/-- Cramer's explicit formula, including Lean's total division convention. -/
def weights (H : Mat2) (T : Vec2) : Vec2 :=
  fun i => cramerNumerator H T i / H.det

/-- Both target-column oriented areas have the same nonzero orientation as
the two original columns. The definition uses only polynomial inequalities. -/
def StrictCone (H : Mat2) (T : Vec2) : Prop :=
  0 < cramerNumerator H T 0 * H.det ∧
  0 < cramerNumerator H T 1 * H.det

/-- Amplitudes, defined pointwise by `Real.sqrt (weights H T i)`. -/
def amplitudes (H : Mat2) (T : Vec2) : Vec2 :=
  fun i => Real.sqrt (weights H T i)

theorem StrictCone.det_ne_zero {H : Mat2} {T : Vec2} (h : StrictCone H T) :
    H.det ≠ 0 :=
  (mul_ne_zero_iff.mp (ne_of_gt h.1)).2

theorem weights_pos_iff (H : Mat2) (T : Vec2) :
    (∀ i, 0 < weights H T i) ↔ StrictCone H T := by
  constructor
  · intro h
    exact ⟨mul_pos_iff.mpr (div_pos_iff.mp (h 0)),
      mul_pos_iff.mpr (div_pos_iff.mp (h 1))⟩
  · intro h i
    fin_cases i
    · exact div_pos_iff.mpr (mul_pos_iff.mp h.1)
    · exact div_pos_iff.mpr (mul_pos_iff.mp h.2)

theorem StrictCone.weights_pos {H : Mat2} {T : Vec2} (h : StrictCone H T) (i : Fin 2) :
    0 < weights H T i :=
  (weights_pos_iff H T).mpr h i

theorem reconstruct (H : Mat2) (T : Vec2) (hdet : H.det ≠ 0) :
    H.mulVec (weights H T) = T := by
  have hc : H.mulVec (cramerNumerator H T) = H.det • T := by
    ext i
    fin_cases i <;>
      simp [cramerNumerator, Matrix.mulVec, dotProduct, Fin.sum_univ_two,
        Matrix.det_fin_two] <;> ring
  have hw : weights H T = H.det⁻¹ • cramerNumerator H T := by
    funext i
    simp only [weights, Pi.smul_apply, smul_eq_mul, div_eq_mul_inv]
    ring
  rw [hw, Matrix.mulVec_smul, hc, smul_smul, inv_mul_cancel₀ hdet, one_smul]

theorem inverse_formula (H : Mat2) (T : Vec2) (hdet : H.det ≠ 0) :
    H⁻¹.mulVec T = weights H T := by
  calc
    H⁻¹.mulVec T = H⁻¹.mulVec (H.mulVec (weights H T)) := by
      rw [reconstruct H T hdet]
    _ = weights H T := by
      rw [Matrix.mulVec_mulVec,
        Matrix.nonsing_inv_mul H (isUnit_iff_ne_zero.mpr hdet), Matrix.one_mulVec]

theorem StrictCone.amplitudes_pos {H : Mat2} {T : Vec2}
    (h : StrictCone H T) (i : Fin 2) : 0 < amplitudes H T i :=
  Real.sqrt_pos.mpr (h.weights_pos i)

theorem reconstruct_amplitudes {H : Mat2} {T : Vec2} (h : StrictCone H T) :
    H.mulVec (fun i => amplitudes H T i ^ 2) = T := by
  have hs : (fun i => amplitudes H T i ^ 2) = weights H T := by
    funext i
    exact Real.sq_sqrt (le_of_lt (h.weights_pos i))
  rw [hs]
  exact reconstruct H T h.det_ne_zero

/-- Agreement with the earlier exact signed-column formula. -/
theorem weights_signed_model {a b sm sp : ℝ} (m t : ℝ)
    (ha : 0 < a) (hb : 0 < b) (hm : 0 < sm) (hp : 0 < sp) :
    weights (Covariance.signedMatrix a b sm sp) (Covariance.target m t) =
      Covariance.coefficients a b sm sp m t := by
  rw [← inverse_formula _ _ (Covariance.determinant_ne_zero ha hb hm hp)]
  exact Covariance.inverse_formula m t ha hb hm hp

theorem signed_model_strictCone {a b sm sp m t : ℝ}
    (ha : 0 < a) (hb : 0 < b) (hm : 0 < sm) (hp : 0 < sp)
    (hcone : |a * t| < b * m) :
    StrictCone (Covariance.signedMatrix a b sm sp) (Covariance.target m t) := by
  apply (weights_pos_iff _ _).mp
  rw [weights_signed_model m t ha hb hm hp]
  exact Covariance.coefficients_pos ha hb hm hp hcone

section Smooth

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {s : Set E} {H : E → Mat2} {T : E → Vec2}

theorem contDiffOn_determinant
    (hH : ∀ i j, ContDiffOn ℝ ∞ (fun x => H x i j) s) :
    ContDiffOn ℝ ∞ (fun x => (H x).det) s := by
  simpa only [Pi.mul_apply, Pi.sub_apply, Matrix.det_fin_two] using
    ((hH 0 0).mul (hH 1 1)).sub ((hH 0 1).mul (hH 1 0))

theorem contDiffOn_numerator
    (hH : ∀ i j, ContDiffOn ℝ ∞ (fun x => H x i j) s)
    (hT : ∀ i, ContDiffOn ℝ ∞ (fun x => T x i) s) (i : Fin 2) :
    ContDiffOn ℝ ∞ (fun x => cramerNumerator (H x) (T x) i) s := by
  fin_cases i
  · simpa [Pi.mul_apply, Pi.sub_apply, cramerNumerator] using ((hT 0).mul (hH 1 1)).sub ((hH 0
      1).mul (hT 1))
  · simpa [Pi.mul_apply, Pi.sub_apply, cramerNumerator] using ((hH 0 0).mul (hT 1)).sub ((hT 0).mul
      (hH 1 0))

/-- Smoothness requires a nonvanishing determinant, independently of positivity. -/
theorem contDiffOn_weights
    (hH : ∀ i j, ContDiffOn ℝ ∞ (fun x => H x i j) s)
    (hT : ∀ i, ContDiffOn ℝ ∞ (fun x => T x i) s)
    (hdet : ∀ x ∈ s, (H x).det ≠ 0) (i : Fin 2) :
    ContDiffOn ℝ ∞ (fun x => weights (H x) (T x) i) s :=
  (contDiffOn_numerator hH hT i).div (contDiffOn_determinant hH) hdet

theorem contDiffOn_inverse_solution
    (hH : ∀ i j, ContDiffOn ℝ ∞ (fun x => H x i j) s)
    (hT : ∀ i, ContDiffOn ℝ ∞ (fun x => T x i) s)
    (hdet : ∀ x ∈ s, (H x).det ≠ 0) (i : Fin 2) :
    ContDiffOn ℝ ∞ (fun x => (H x)⁻¹.mulVec (T x) i) s := by
  apply (contDiffOn_weights hH hT hdet i).congr
  intro x hx
  exact congrFun (inverse_formula (H x) (T x) (hdet x hx)) i

/-- Positive square-root amplitudes are smooth on the strict cone. -/
theorem contDiffOn_amplitudes
    (hH : ∀ i j, ContDiffOn ℝ ∞ (fun x => H x i j) s)
    (hT : ∀ i, ContDiffOn ℝ ∞ (fun x => T x i) s)
    (hcone : ∀ x ∈ s, StrictCone (H x) (T x)) (i : Fin 2) :
    ContDiffOn ℝ ∞ (fun x => amplitudes (H x) (T x) i) s :=
  (contDiffOn_weights hH hT (fun x hx => (hcone x hx).det_ne_zero) i).sqrt
    (fun x hx => ne_of_gt ((hcone x hx).weights_pos i))

/-- The complete amplitude vector, not only its coordinates, is smooth. -/
theorem contDiffOn_amplitude_vector
    (hH : ∀ i j, ContDiffOn ℝ ∞ (fun x => H x i j) s)
    (hT : ∀ i, ContDiffOn ℝ ∞ (fun x => T x i) s)
    (hcone : ∀ x ∈ s, StrictCone (H x) (T x)) :
    ContDiffOn ℝ ∞ (fun x => amplitudes (H x) (T x)) s :=
  contDiffOn_pi.mpr (contDiffOn_amplitudes hH hT hcone)

/-- Smooth dependence of the coefficients as named in the original exact
signed-slot module. All six scalar input functions are genuinely smooth. -/
theorem contDiffOn_signed_coefficients {a b sm sp m t : E → ℝ}
    (ha : ContDiffOn ℝ ∞ a s) (hb : ContDiffOn ℝ ∞ b s)
    (hsm : ContDiffOn ℝ ∞ sm s) (hsp : ContDiffOn ℝ ∞ sp s)
    (hm : ContDiffOn ℝ ∞ m s) (ht : ContDiffOn ℝ ∞ t s)
    (hpos : ∀ x ∈ s, 0 < a x ∧ 0 < b x ∧ 0 < sm x ∧ 0 < sp x)
    (i : Fin 2) :
    ContDiffOn ℝ ∞
      (fun x => Covariance.coefficients (a x) (b x) (sm x) (sp x) (m x) (t x) i) s := by
  fin_cases i
  · change ContDiffOn ℝ ∞
      (fun x => (b x * m x - a x * t x) / (2 * a x * b x * sm x)) s
    apply ((hb.mul hm).sub (ha.mul ht)).div
      (((contDiffOn_const.mul ha).mul hb).mul hsm)
    intro x hx
    rcases hpos x hx with ⟨hap, hbp, hsmp, hspp⟩
    exact ne_of_gt (by positivity)
  · change ContDiffOn ℝ ∞
      (fun x => (b x * m x + a x * t x) / (2 * a x * b x * sp x)) s
    apply ((hb.mul hm).add (ha.mul ht)).div
      (((contDiffOn_const.mul ha).mul hb).mul hsp)
    intro x hx
    rcases hpos x hx with ⟨hap, hbp, hsmp, hspp⟩
    exact ne_of_gt (by positivity)

theorem contDiffOn_signed_amplitudes {a b sm sp m t : E → ℝ}
    (ha : ContDiffOn ℝ ∞ a s) (hb : ContDiffOn ℝ ∞ b s)
    (hsm : ContDiffOn ℝ ∞ sm s) (hsp : ContDiffOn ℝ ∞ sp s)
    (hm : ContDiffOn ℝ ∞ m s) (ht : ContDiffOn ℝ ∞ t s)
    (hpos : ∀ x ∈ s, 0 < a x ∧ 0 < b x ∧ 0 < sm x ∧ 0 < sp x)
    (hcone : ∀ x ∈ s, |a x * t x| < b x * m x) (i : Fin 2) :
    ContDiffOn ℝ ∞
      (fun x => Covariance.amplitudes (a x) (b x) (sm x) (sp x) (m x) (t x) i) s := by
  apply (contDiffOn_signed_coefficients ha hb hsm hsp hm ht hpos i).sqrt
  intro x hx
  rcases hpos x hx with ⟨hap, hbp, hsmp, hspp⟩
  exact ne_of_gt (Covariance.coefficients_pos hap hbp hsmp hspp (hcone x hx) i)

end Smooth

section Compact

variable {X : Type*} [TopologicalSpace X]
variable {K : Set X} {H : X → Mat2} {T : X → Vec2}

theorem continuousOn_determinant
    (hH : ∀ i j, ContinuousOn (fun x => H x i j) K) :
    ContinuousOn (fun x => (H x).det) K := by
  simpa only [Pi.mul_apply, Pi.sub_apply, Matrix.det_fin_two] using
    ((hH 0 0).fun_mul (hH 1 1)).fun_sub ((hH 0 1).fun_mul (hH 1 0))

theorem continuousOn_numerator
    (hH : ∀ i j, ContinuousOn (fun x => H x i j) K)
    (hT : ∀ i, ContinuousOn (fun x => T x i) K) (i : Fin 2) :
    ContinuousOn (fun x => cramerNumerator (H x) (T x) i) K := by
  fin_cases i
  · simpa [Pi.mul_apply, Pi.sub_apply, cramerNumerator] using ((hT 0).fun_mul (hH 1 1)).fun_sub
      ((hH 0 1).fun_mul (hT 1))
  · simpa [Pi.mul_apply, Pi.sub_apply, cramerNumerator] using ((hH 0 0).fun_mul (hT 1)).fun_sub
      ((hT 0).fun_mul (hH 1 0))

theorem continuousOn_weights
    (hH : ∀ i j, ContinuousOn (fun x => H x i j) K)
    (hT : ∀ i, ContinuousOn (fun x => T x i) K)
    (hdet : ∀ x ∈ K, (H x).det ≠ 0) (i : Fin 2) :
    ContinuousOn (fun x => weights (H x) (T x) i) K :=
  (continuousOn_numerator hH hT i).div (continuousOn_determinant hH) hdet

/-- Compactness supplies an actual common lower bound for the determinant
magnitude and both solution coordinates, including an empty parameter set. -/
theorem compact_uniform_positive (hK : IsCompact K)
    (hH : ∀ i j, ContinuousOn (fun x => H x i j) K)
    (hT : ∀ i, ContinuousOn (fun x => T x i) K)
    (hcone : ∀ x ∈ K, StrictCone (H x) (T x)) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ x ∈ K,
      δ ≤ |(H x).det| ∧ ∀ i, δ ≤ weights (H x) (T x) i := by
  have hw := continuousOn_weights hH hT (fun x hx => (hcone x hx).det_ne_zero)
  let margin : X → ℝ := fun x => min |(H x).det|
    (min (weights (H x) (T x) 0) (weights (H x) (T x) 1))
  have hm : ContinuousOn margin K :=
    continuous_min.comp_continuousOn ((continuousOn_determinant hH).abs.prodMk
      (continuous_min.comp_continuousOn ((hw 0).prodMk (hw 1))))
  have hmp : ∀ x ∈ K, 0 < margin x := by
    intro x hx
    exact lt_min (abs_pos.mpr ((hcone x hx).det_ne_zero))
      (lt_min ((hcone x hx).weights_pos 0) ((hcone x hx).weights_pos 1))
  obtain ⟨δ, hδ, hbound⟩ := hK.exists_forall_le' hm hmp
  refine ⟨δ, hδ, ?_⟩
  intro x hx
  refine ⟨(hbound x hx).trans (min_le_left _ _), ?_⟩
  intro i
  fin_cases i
  · exact (hbound x hx).trans ((min_le_right _ _).trans (min_le_left _ _))
  · exact (hbound x hx).trans ((min_le_right _ _).trans (min_le_right _ _))

/-- The same compact family keeps every positive amplitude uniformly away
from zero; no claim is made for a family touching a zero-stress edge. -/
theorem compact_uniform_amplitudes (hK : IsCompact K)
    (hH : ∀ i j, ContinuousOn (fun x => H x i j) K)
    (hT : ∀ i, ContinuousOn (fun x => T x i) K)
    (hcone : ∀ x ∈ K, StrictCone (H x) (T x)) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ x ∈ K,
      δ ≤ |(H x).det| ∧ ∀ i,
        δ ≤ weights (H x) (T x) i ∧ δ ≤ amplitudes (H x) (T x) i := by
  obtain ⟨δ, hδ, hbound⟩ := compact_uniform_positive hK hH hT hcone
  refine ⟨min δ (Real.sqrt δ), lt_min hδ (Real.sqrt_pos.mpr hδ), ?_⟩
  intro x hx
  refine ⟨(min_le_left _ _).trans (hbound x hx).1, ?_⟩
  intro i
  exact ⟨(min_le_left _ _).trans ((hbound x hx).2 i),
    (min_le_right _ _).trans (Real.sqrt_le_sqrt ((hbound x hx).2 i))⟩

end Compact

/-- The strict area inequalities define an open set of matrix-target pairs. -/
def strictConeRegion : Set Datum := {z | StrictCone z.1 z.2}

theorem isOpen_strictConeRegion : IsOpen strictConeRegion := by
  have hH : ∀ i j, Continuous (fun z : Datum => z.1 i j) := fun i j =>
    (continuous_apply j).comp ((continuous_apply i).comp continuous_fst)
  have hT : ∀ i, Continuous (fun z : Datum => z.2 i) := fun i =>
    (continuous_apply i).comp continuous_snd
  have hd : Continuous (fun z : Datum => z.1.det) := by
    exact continuousOn_univ.mp
      (continuousOn_determinant (fun i j => (hH i j).continuousOn))
  have hn : ∀ i, Continuous (fun z : Datum => cramerNumerator z.1 z.2 i) := by
    intro i
    exact continuousOn_univ.mp (continuousOn_numerator
      (fun i j => (hH i j).continuousOn) (fun i => (hT i).continuousOn) i)
  exact (isOpen_lt continuous_const ((hn 0).fun_mul hd)).inter
    (isOpen_lt continuous_const ((hn 1).fun_mul hd))

/-- The solution map itself is C-infinity on the open set of admissible
matrix-target data, without a prechosen parameterization. -/
theorem contDiffOn_universal_weights :
    ContDiffOn ℝ ∞ (fun z : Datum => weights z.1 z.2) strictConeRegion := by
  apply contDiffOn_pi.mpr
  apply contDiffOn_weights
  · intro i j
    exact ((contDiff_apply_apply ℝ ℝ i j).comp contDiff_fst).contDiffOn
  · intro i
    exact ((contDiff_apply ℝ ℝ i).comp contDiff_snd).contDiffOn
  · intro z hz
    exact StrictCone.det_ne_zero hz

/-- The positive square-root solution is C-infinity on that same open set. -/
theorem contDiffOn_universal_amplitudes :
    ContDiffOn ℝ ∞ (fun z : Datum => amplitudes z.1 z.2) strictConeRegion := by
  apply contDiffOn_amplitude_vector
  · intro i j
    exact ((contDiff_apply_apply ℝ ℝ i j).comp contDiff_fst).contDiffOn
  · intro i
    exact ((contDiff_apply ℝ ℝ i).comp contDiff_snd).contDiffOn
  · intro z hz
    exact hz

/-- A single positive perturbation radius works for every datum in a compact
subset of the strict cone. The perturbed data may be arbitrary actual matrices. -/
theorem compact_perturbation_stability {S : Set Datum} (hS : IsCompact S)
    (hcone : S ⊆ strictConeRegion) :
    ∃ ρ : ℝ, 0 < ρ ∧ ∀ z ∈ S, ∀ z' : Datum,
      dist z' z ≤ ρ → StrictCone z'.1 z'.2 := by
  obtain ⟨ρ, hρ, hsub⟩ :=
    hS.exists_cthickening_subset_open isOpen_strictConeRegion hcone
  exact ⟨ρ, hρ, fun z hz z' hdist =>
    hsub (Metric.mem_cthickening_of_dist_le z' z ρ S hz hdist)⟩

/-- Uniform perturbation stability for a continuous family on a compact
parameter set. Competing matrices need not form a continuous family. -/
theorem compact_family_perturbation_stability
    {X : Type*} [TopologicalSpace X] {K : Set X} (hK : IsCompact K)
    {H : X → Mat2} {T : X → Vec2}
    (hH : ∀ i j, ContinuousOn (fun x => H x i j) K)
    (hT : ∀ i, ContinuousOn (fun x => T x i) K)
    (hcone : ∀ x ∈ K, StrictCone (H x) (T x)) :
    ∃ ρ : ℝ, 0 < ρ ∧ ∀ x ∈ K, ∀ H' : Mat2, ∀ T' : Vec2,
      dist (H', T') (H x, T x) ≤ ρ →
        H'.det ≠ 0 ∧ (∀ i, 0 < weights H' T' i) ∧
          (∀ i, 0 < amplitudes H' T' i) := by
  let f : X → Datum := fun x => (H x, T x)
  have hf : ContinuousOn f K :=
    (continuousOn_pi.mpr (fun i => continuousOn_pi.mpr (hH i))).prodMk
      (continuousOn_pi.mpr hT)
  have himage : f '' K ⊆ strictConeRegion := by
    rintro z ⟨x, hx, rfl⟩
    exact hcone x hx
  obtain ⟨ρ, hρ, hstable⟩ :=
    compact_perturbation_stability (hK.image_of_continuousOn hf) himage
  refine ⟨ρ, hρ, ?_⟩
  intro x hx H' T' hdist
  have hc := hstable (f x) (mem_image_of_mem f hx) (H', T') hdist
  exact ⟨hc.det_ne_zero, hc.weights_pos, hc.amplitudes_pos⟩

end NavierStokes.SmoothCovariance

end
end

end

section

/-!
# Covariance amplitudes across an exponential-flat edge

The normalized matrix and target are actual smooth functions with an explicit
strict cone. Columns are then multiplied by `edge κᵢ`, and the target by
`edge σ`. Exact inverse and square-root identities exhibit a positive remaining
exponential whenever `κᵢ < σ`; in particular the squared-factor convention
`κᵢ = 2 λᵢ` is covered by `λᵢ < σ / 2`.

The coefficient quotients are proved smooth from these formulas. Their
smoothness across the singular matrix at the edge is not assumed.
-/

@[expose] public section

noncomputable section

namespace NavierStokes.FlatCovariance

open Matrix Set
open SmoothCovariance (Mat2 Vec2)
open FlatCutoff (edge)
open scoped ContDiff Topology

/-- Multiplication of column `j` by its scalar factor `c j`. -/
def columns (G : Mat2) (c : Vec2) : Mat2 := fun i j => c j * G i j

/-- Scaled target, defined pointwise by `r * T i`. -/
def scaledTarget (r : ℝ) (T : Vec2) : Vec2 := fun i => r * T i

/-- The actual edge-degenerate covariance matrix. -/
def edgeMatrix (κ : Vec2) (G : ℝ → Mat2) (x : ℝ) : Mat2 :=
  columns (G x) (fun j => edge (κ j) x)

/-- Edge target, given by `scaledTarget (edge σ x) (T x)`. -/
def edgeTarget (σ : ℝ) (T : ℝ → Vec2) (x : ℝ) : Vec2 :=
  scaledTarget (edge σ x) (T x)

/-- The actual matrix-inverse solve, also defined at the zero edge. -/
def inverseCoefficients (σ : ℝ) (κ : Vec2) (G : ℝ → Mat2) (T : ℝ → Vec2)
    (x : ℝ) : Vec2 :=
  (edgeMatrix κ G x)⁻¹.mulVec (edgeTarget σ T x)

/-- Primary amplitude, defined pointwise by `Real.sqrt (inverseCoefficients σ κ G T x i)`. -/
def primaryAmplitude (σ : ℝ) (κ : Vec2) (G : ℝ → Mat2) (T : ℝ → Vec2)
    (x : ℝ) : Vec2 :=
  fun i => Real.sqrt (inverseCoefficients σ κ G T x i)

/-- The signed covariance update divides by the fixed positive primary. -/
def signedAmplitude (σ τ : ℝ) (κ : Vec2) (G : ℝ → Mat2)
    (T R : ℝ → Vec2) (x : ℝ) : Vec2 :=
  fun i => inverseCoefficients τ κ G R x i / (2 * primaryAmplitude σ κ G T x i)

theorem sqrt_edge (c x : ℝ) : Real.sqrt (edge c x) = edge (c / 2) x := by
  by_cases hx : x ≤ 0
  · simp [FlatCutoff.edge_of_nonpos c hx, FlatCutoff.edge_of_nonpos (c / 2) hx]
  · have hp : 0 < x := lt_of_not_ge hx
    rw [FlatCutoff.edge_of_pos c hp, FlatCutoff.edge_of_pos (c / 2) hp,
      ← Real.exp_half]
    congr 1
    ring

theorem edge_mul (c d x : ℝ) : edge c x * edge d x = edge (c + d) x := by
  by_cases hx : x ≤ 0
  · simp [FlatCutoff.edge_of_nonpos c hx, FlatCutoff.edge_of_nonpos d hx,
      FlatCutoff.edge_of_nonpos (c + d) hx]
  · have hp : 0 < x := lt_of_not_ge hx
    rw [FlatCutoff.edge_of_pos c hp, FlatCutoff.edge_of_pos d hp,
      FlatCutoff.edge_of_pos (c + d) hp, ← Real.exp_add]
    congr 1
    ring

theorem edge_sq (c x : ℝ) : edge c x ^ 2 = edge (2 * c) x := by
  rw [pow_two, edge_mul]
  congr 1
  ring

theorem squared_column_factors (lam : Vec2) (G : ℝ → Mat2) (x : ℝ) :
    columns (G x) (fun j => edge (lam j) x ^ 2) =
      edgeMatrix (fun j => 2 * lam j) G x := by
  ext i j
  simp only [columns, edgeMatrix, edge_sq]

theorem determinant_columns (G : Mat2) (c : Vec2) :
    (columns G c).det = c 0 * c 1 * G.det := by
  simp only [Matrix.det_fin_two, columns]
  ring

theorem columns_det_ne_zero {G : Mat2} {c : Vec2}
    (hG : G.det ≠ 0) (hc : ∀ i, c i ≠ 0) : (columns G c).det ≠ 0 := by
  rw [determinant_columns]
  exact mul_ne_zero (mul_ne_zero (hc 0) (hc 1)) hG

/-- Cramer's formula records the exact effect of individual column factors. -/
theorem weights_columns (G : Mat2) (c : Vec2) (T : Vec2) (r : ℝ)
    (hG : G.det ≠ 0) (hc : ∀ i, c i ≠ 0) (i : Fin 2) :
    SmoothCovariance.weights (columns G c) (scaledTarget r T) i =
      (r / c i) * SmoothCovariance.weights G T i := by
  have hc0 := hc 0
  have hc1 := hc 1
  fin_cases i <;>
    simp only [SmoothCovariance.weights, determinant_columns,
      SmoothCovariance.cramerNumerator, columns, scaledTarget,
      Matrix.cons_val_zero, Matrix.cons_val_one, Fin.zero_eta, Fin.mk_one] <;>
    field_simp

theorem edgeMatrix_det_ne_zero {κ : Vec2} {G : ℝ → Mat2} {x : ℝ}
    (hG : (G x).det ≠ 0) (hx : 0 < x) : (edgeMatrix κ G x).det ≠ 0 :=
  columns_det_ne_zero hG (fun i => ne_of_gt (FlatCutoff.edge_pos (κ i) hx))

theorem inverseCoefficients_of_nonpos (σ : ℝ) (κ : Vec2)
    (G : ℝ → Mat2) (T : ℝ → Vec2) {x : ℝ} (hx : x ≤ 0) :
    inverseCoefficients σ κ G T x = 0 := by
  have ht : edgeTarget σ T x = 0 := by
    ext i
    simp [edgeTarget, scaledTarget, FlatCutoff.edge_of_nonpos σ hx]
  simp [inverseCoefficients, ht]

theorem primaryAmplitude_of_nonpos (σ : ℝ) (κ : Vec2)
    (G : ℝ → Mat2) (T : ℝ → Vec2) {x : ℝ} (hx : x ≤ 0) (i : Fin 2) :
    primaryAmplitude σ κ G T x i = 0 := by
  simp [primaryAmplitude, inverseCoefficients_of_nonpos σ κ G T hx]

theorem signedAmplitude_of_nonpos (σ τ : ℝ) (κ : Vec2)
    (G : ℝ → Mat2) (T R : ℝ → Vec2) {x : ℝ} (hx : x ≤ 0) (i : Fin 2) :
    signedAmplitude σ τ κ G T R x i = 0 := by
  simp [signedAmplitude, inverseCoefficients_of_nonpos τ κ G R hx]

/-- Exact cancellation of the column exponential in the actual inverse.
This identity includes the edge and the full zero half-line. -/
theorem inverseCoefficients_factor (σ : ℝ) (κ : Vec2)
    (G : ℝ → Mat2) (T : ℝ → Vec2) {x : ℝ} (hG : (G x).det ≠ 0) (i : Fin 2) :
    inverseCoefficients σ κ G T x i =
      edge (σ - κ i) x * SmoothCovariance.weights (G x) (T x) i := by
  by_cases hx : x ≤ 0
  · simp [inverseCoefficients_of_nonpos σ κ G T hx,
      FlatCutoff.edge_of_nonpos (σ - κ i) hx]
  · have hp : 0 < x := lt_of_not_ge hx
    have hs := SmoothCovariance.inverse_formula (edgeMatrix κ G x) (edgeTarget σ T x)
      (edgeMatrix_det_ne_zero hG hp)
    change ((edgeMatrix κ G x)⁻¹.mulVec (edgeTarget σ T x)) i = _
    rw [hs]
    dsimp only [edgeMatrix, edgeTarget]
    rw [weights_columns (G x) (fun j => edge (κ j) x) (T x) (edge σ x) hG
      (fun j => ne_of_gt (FlatCutoff.edge_pos (κ j) hp)) i]
    rw [congrFun (FlatCutoff.edge_div_edge σ (κ i)) x]

/-- Taking the square root halves the *remaining* exponential exponent. -/
theorem primaryAmplitude_factor (σ : ℝ) (κ : Vec2)
    (G : ℝ → Mat2) (T : ℝ → Vec2) {x : ℝ} (hG : (G x).det ≠ 0) (i : Fin 2) :
    primaryAmplitude σ κ G T x i = edge ((σ - κ i) / 2) x *
      SmoothCovariance.amplitudes (G x) (T x) i := by
  unfold primaryAmplitude
  rw [inverseCoefficients_factor σ κ G T hG i,
    Real.sqrt_mul (FlatCutoff.edge_nonneg (σ - κ i) x), sqrt_edge]
  rfl

/-- The signed update retains the explicitly computed exponential margin;
the target `R` may have either sign. -/
theorem signedAmplitude_factor (σ τ : ℝ) (κ : Vec2)
    (G : ℝ → Mat2) (T R : ℝ → Vec2) {x : ℝ} (hG : (G x).det ≠ 0) (i : Fin 2) :
    signedAmplitude σ τ κ G T R x i = edge (τ - (σ + κ i) / 2) x *
      (SmoothCovariance.weights (G x) (R x) i /
        (2 * SmoothCovariance.amplitudes (G x) (T x) i)) := by
  unfold signedAmplitude
  rw [inverseCoefficients_factor τ κ G R hG i, primaryAmplitude_factor σ κ G T hG i]
  calc
    _ = (edge (τ - κ i) x / edge ((σ - κ i) / 2) x) *
        (SmoothCovariance.weights (G x) (R x) i /
          (2 * SmoothCovariance.amplitudes (G x) (T x) i)) := by
      simp only [div_eq_mul_inv, _root_.mul_inv_rev]
      ring
    _ = _ := by
      rw [congrFun (FlatCutoff.edge_div_edge (τ - κ i) ((σ - κ i) / 2)) x]
      congr 2
      ring

/-- Exact linearity in a scalar target factor, with no regularity or
nonvanishing assumption on that factor. -/
theorem inverseCoefficients_target_factor (σ : ℝ) (κ : Vec2)
    (G : ℝ → Mat2) (T : ℝ → Vec2) (f : ℝ → ℝ) (x : ℝ) (i : Fin 2) :
    inverseCoefficients σ κ G (fun y j => f y * T y j) x i =
      f x * inverseCoefficients σ κ G T x i := by
  simp only [inverseCoefficients, edgeTarget, scaledTarget, Matrix.mulVec,
    dotProduct, Fin.sum_univ_two]
  ring

theorem signedAmplitude_target_factor (σ τ : ℝ) (κ : Vec2)
    (G : ℝ → Mat2) (T R : ℝ → Vec2) (f : ℝ → ℝ) (x : ℝ) (i : Fin 2) :
    signedAmplitude σ τ κ G T (fun y j => f y * R y j) x i =
      f x * signedAmplitude σ τ κ G T R x i := by
  unfold signedAmplitude
  rw [inverseCoefficients_target_factor]
  ring

theorem inverseCoefficients_pos {σ : ℝ} {κ : Vec2}
    {G : ℝ → Mat2} {T : ℝ → Vec2} {x : ℝ}
    (hcone : SmoothCovariance.StrictCone (G x) (T x)) (hx : 0 < x) (i : Fin 2) :
    0 < inverseCoefficients σ κ G T x i := by
  rw [inverseCoefficients_factor σ κ G T hcone.det_ne_zero i]
  exact mul_pos (FlatCutoff.edge_pos _ hx) (hcone.weights_pos i)

theorem primaryAmplitude_pos {σ : ℝ} {κ : Vec2}
    {G : ℝ → Mat2} {T : ℝ → Vec2} {x : ℝ}
    (hcone : SmoothCovariance.StrictCone (G x) (T x)) (hx : 0 < x) (i : Fin 2) :
    0 < primaryAmplitude σ κ G T x i :=
  Real.sqrt_pos.mpr (inverseCoefficients_pos hcone hx i)

/-- The inverse still reconstructs its target at every real point, including
the zero half-line where the matrix itself is singular. -/
theorem inverse_reconstruct (σ : ℝ) (κ : Vec2)
    (G : ℝ → Mat2) (T : ℝ → Vec2) {x : ℝ} (hG : (G x).det ≠ 0) :
    (edgeMatrix κ G x).mulVec (inverseCoefficients σ κ G T x) = edgeTarget σ T x := by
  by_cases hx : x ≤ 0
  · rw [inverseCoefficients_of_nonpos σ κ G T hx, Matrix.mulVec_zero]
    ext i
    simp [edgeTarget, scaledTarget, FlatCutoff.edge_of_nonpos σ hx]
  · have hp : 0 < x := lt_of_not_ge hx
    unfold inverseCoefficients
    rw [Matrix.mulVec_mulVec,
      Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.mpr (edgeMatrix_det_ne_zero hG hp)),
      Matrix.one_mulVec]

theorem primary_reconstruct {σ : ℝ} {κ : Vec2}
    {G : ℝ → Mat2} {T : ℝ → Vec2} {x : ℝ}
    (hcone : SmoothCovariance.StrictCone (G x) (T x)) :
    (edgeMatrix κ G x).mulVec (fun i => primaryAmplitude σ κ G T x i ^ 2) =
      edgeTarget σ T x := by
  have hy : ∀ i, 0 ≤ inverseCoefficients σ κ G T x i := by
    intro i
    by_cases hx : x ≤ 0
    · simp [inverseCoefficients_of_nonpos σ κ G T hx]
    · exact le_of_lt (inverseCoefficients_pos hcone (lt_of_not_ge hx) i)
  have hs : (fun i => primaryAmplitude σ κ G T x i ^ 2) =
      inverseCoefficients σ κ G T x := by
    funext i
    exact Real.sq_sqrt (hy i)
  rw [hs]
  exact inverse_reconstruct σ κ G T hcone.det_ne_zero

/-- Exact two-sided cross covariance of the primary and signed increment. -/
theorem signed_cross_reconstruct {σ τ : ℝ} {κ : Vec2}
    {G : ℝ → Mat2} {T R : ℝ → Vec2} {x : ℝ}
    (hcone : SmoothCovariance.StrictCone (G x) (T x)) :
    (edgeMatrix κ G x).mulVec
        (fun i => 2 * primaryAmplitude σ κ G T x i * signedAmplitude σ τ κ G T R x i) =
      edgeTarget τ R x := by
  have hcross :
      (fun i => 2 * primaryAmplitude σ κ G T x i * signedAmplitude σ τ κ G T R x i) =
        inverseCoefficients τ κ G R x := by
    funext i
    by_cases hx : x ≤ 0
    · simp [primaryAmplitude_of_nonpos σ κ G T hx,
        inverseCoefficients_of_nonpos τ κ G R hx]
    · have ha : primaryAmplitude σ κ G T x i ≠ 0 :=
        ne_of_gt (primaryAmplitude_pos hcone (lt_of_not_ge hx) i)
      unfold signedAmplitude
      field_simp
  rw [hcross]
  exact inverse_reconstruct τ κ G R hcone.det_ne_zero

section Smooth

variable {s : Set ℝ} {σ τ : ℝ} {κ : Vec2}
variable {G : ℝ → Mat2} {T R : ℝ → Vec2}

theorem edgeMatrix_contDiffOn
    (hG : ∀ i j, ContDiffOn ℝ ∞ (fun x => G x i j) s)
    (hκ : ∀ i, 0 < κ i) (i j : Fin 2) :
    ContDiffOn ℝ ∞ (fun x => edgeMatrix κ G x i j) s :=
  (FlatCutoff.edge_contDiff (hκ j) (n := ⊤)).contDiffOn.mul (hG i j)

theorem edgeTarget_contDiffOn
    (hT : ∀ i, ContDiffOn ℝ ∞ (fun x => T x i) s)
    (hσ : 0 < σ) (i : Fin 2) :
    ContDiffOn ℝ ∞ (fun x => edgeTarget σ T x i) s :=
  (FlatCutoff.edge_contDiff hσ (n := ⊤)).contDiffOn.mul (hT i)

/-- Smooth inverse coefficients at the edge, proved by the surviving
exponential factor even though the actual matrix degenerates there. -/
theorem inverseCoefficients_contDiffOn
    (hG : ∀ i j, ContDiffOn ℝ ∞ (fun x => G x i j) s)
    (hT : ∀ i, ContDiffOn ℝ ∞ (fun x => T x i) s)
    (hdet : ∀ x ∈ s, (G x).det ≠ 0)
    (hgap : ∀ i, κ i < σ) (i : Fin 2) :
    ContDiffOn ℝ ∞ (fun x => inverseCoefficients σ κ G T x i) s := by
  apply ((FlatCutoff.edge_contDiff (sub_pos.mpr (hgap i)) (n := ⊤)).contDiffOn.mul
    (SmoothCovariance.contDiffOn_weights hG hT hdet i)).congr
  intro x hx
  exact inverseCoefficients_factor σ κ G T (hdet x hx) i

theorem primaryAmplitude_contDiffOn
    (hG : ∀ i j, ContDiffOn ℝ ∞ (fun x => G x i j) s)
    (hT : ∀ i, ContDiffOn ℝ ∞ (fun x => T x i) s)
    (hcone : ∀ x ∈ s, SmoothCovariance.StrictCone (G x) (T x))
    (hgap : ∀ i, κ i < σ) (i : Fin 2) :
    ContDiffOn ℝ ∞ (fun x => primaryAmplitude σ κ G T x i) s := by
  have hp : 0 < (σ - κ i) / 2 := by linarith [hgap i]
  apply ((FlatCutoff.edge_contDiff hp (n := ⊤)).contDiffOn.mul
    (SmoothCovariance.contDiffOn_amplitudes hG hT hcone i)).congr
  intro x hx
  exact primaryAmplitude_factor σ κ G T (hcone x hx).det_ne_zero i

/-- Every fixed inverse-power loss is absorbed by the concrete primary
exponential, including at zero. -/
theorem primaryAmplitude_div_pow_contDiffOn
    (hG : ∀ i j, ContDiffOn ℝ ∞ (fun x => G x i j) s)
    (hT : ∀ i, ContDiffOn ℝ ∞ (fun x => T x i) s)
    (hcone : ∀ x ∈ s, SmoothCovariance.StrictCone (G x) (T x))
    (hgap : ∀ i, κ i < σ) (i : Fin 2) (loss : ℕ) :
    ContDiffOn ℝ ∞ (fun x => primaryAmplitude σ κ G T x i / x ^ loss) s := by
  have hp : 0 < (σ - κ i) / 2 := by linarith [hgap i]
  apply ((FlatCutoff.edge_div_pow_contDiff hp loss (n := ⊤)).contDiffOn.mul
    (SmoothCovariance.contDiffOn_amplitudes hG hT hcone i)).congr
  intro x hx
  rw [primaryAmplitude_factor σ κ G T (hcone x hx).det_ne_zero i]
  ring

/-- The normalized signed quotient is smooth because its denominator is
proved strictly positive from the explicit normalized cone. -/
theorem signed_normal_contDiffOn
    (hG : ∀ i j, ContDiffOn ℝ ∞ (fun x => G x i j) s)
    (hT : ∀ i, ContDiffOn ℝ ∞ (fun x => T x i) s)
    (hR : ∀ i, ContDiffOn ℝ ∞ (fun x => R x i) s)
    (hcone : ∀ x ∈ s, SmoothCovariance.StrictCone (G x) (T x)) (i : Fin 2) :
    ContDiffOn ℝ ∞ (fun x => SmoothCovariance.weights (G x) (R x) i /
      (2 * SmoothCovariance.amplitudes (G x) (T x) i)) s := by
  apply (SmoothCovariance.contDiffOn_weights hG hR
    (fun x hx => (hcone x hx).det_ne_zero) i).div
      (contDiffOn_const.mul (SmoothCovariance.contDiffOn_amplitudes hG hT hcone i))
  intro x hx
  exact mul_ne_zero (by norm_num) (ne_of_gt ((hcone x hx).amplitudes_pos i))

theorem signedAmplitude_contDiffOn
    (hG : ∀ i j, ContDiffOn ℝ ∞ (fun x => G x i j) s)
    (hT : ∀ i, ContDiffOn ℝ ∞ (fun x => T x i) s)
    (hR : ∀ i, ContDiffOn ℝ ∞ (fun x => R x i) s)
    (hcone : ∀ x ∈ s, SmoothCovariance.StrictCone (G x) (T x))
    (hgap : ∀ i, (σ + κ i) / 2 < τ) (i : Fin 2) :
    ContDiffOn ℝ ∞ (fun x => signedAmplitude σ τ κ G T R x i) s := by
  apply ((FlatCutoff.edge_contDiff (sub_pos.mpr (hgap i)) (n := ⊤)).contDiffOn.mul
    (signed_normal_contDiffOn hG hT hR hcone i)).congr
  intro x hx
  exact signedAmplitude_factor σ τ κ G T R (hcone x hx).det_ne_zero i

theorem signedAmplitude_div_pow_contDiffOn
    (hG : ∀ i j, ContDiffOn ℝ ∞ (fun x => G x i j) s)
    (hT : ∀ i, ContDiffOn ℝ ∞ (fun x => T x i) s)
    (hR : ∀ i, ContDiffOn ℝ ∞ (fun x => R x i) s)
    (hcone : ∀ x ∈ s, SmoothCovariance.StrictCone (G x) (T x))
    (hgap : ∀ i, (σ + κ i) / 2 < τ) (i : Fin 2) (loss : ℕ) :
    ContDiffOn ℝ ∞ (fun x => signedAmplitude σ τ κ G T R x i / x ^ loss) s := by
  apply ((FlatCutoff.edge_div_pow_contDiff (sub_pos.mpr (hgap i)) loss (n := ⊤)).contDiffOn.mul
    (signed_normal_contDiffOn hG hT hR hcone i)).congr
  intro x hx
  rw [signedAmplitude_factor σ τ κ G T R (hcone x hx).det_ne_zero i]
  ring

/-- An actual signed-stress numerator with an inverse-power loss still gives
a smooth signed amplitude. Smoothness of the singular quotient is a result. -/
theorem signed_inverse_power_target_contDiffOn
    (hG : ∀ i j, ContDiffOn ℝ ∞ (fun x => G x i j) s)
    (hT : ∀ i, ContDiffOn ℝ ∞ (fun x => T x i) s)
    (hR : ∀ i, ContDiffOn ℝ ∞ (fun x => R x i) s)
    (hcone : ∀ x ∈ s, SmoothCovariance.StrictCone (G x) (T x))
    (hgap : ∀ i, (σ + κ i) / 2 < τ) (i : Fin 2) (loss : ℕ) :
    ContDiffOn ℝ ∞ (fun x => signedAmplitude σ τ κ G T
      (fun y j => (y ^ loss)⁻¹ * R y j) x i) s := by
  apply (signedAmplitude_div_pow_contDiffOn hG hT hR hcone hgap i loss).congr
  intro x hx
  rw [signedAmplitude_target_factor]
  simp only [div_eq_mul_inv]
  ring

/-- When a fundamental column factor is `edge λᵢ` and covariance therefore
carries its square, the concrete condition is exactly `λᵢ < σ / 2`. A signed
stress with the same target envelope retains the same flat exponent. -/
theorem squared_factors_smooth {lam : Vec2}
    (hG : ∀ i j, ContDiffOn ℝ ∞ (fun x => G x i j) s)
    (hT : ∀ i, ContDiffOn ℝ ∞ (fun x => T x i) s)
    (hR : ∀ i, ContDiffOn ℝ ∞ (fun x => R x i) s)
    (hcone : ∀ x ∈ s, SmoothCovariance.StrictCone (G x) (T x))
    (hgap : ∀ i, lam i < σ / 2) (i : Fin 2) (loss : ℕ) :
    ContDiffOn ℝ ∞ (fun x => primaryAmplitude σ (fun j => 2 * lam j) G T x i / x ^ loss) s ∧
    ContDiffOn ℝ ∞ (fun x => signedAmplitude σ σ (fun j => 2 * lam j) G T R x i / x ^ loss) s := by
  constructor
  · exact primaryAmplitude_div_pow_contDiffOn hG hT hcone
      (fun j => by linarith [hgap j]) i loss
  · exact signedAmplitude_div_pow_contDiffOn hG hT hR hcone
      (fun j => by linarith [hgap j]) i loss

/-- The requested stricter half-exponent condition also suffices when the
exponential appears directly in a covariance column, without a square. -/
theorem direct_half_factors_smooth
    (hG : ∀ i j, ContDiffOn ℝ ∞ (fun x => G x i j) s)
    (hT : ∀ i, ContDiffOn ℝ ∞ (fun x => T x i) s)
    (hR : ∀ i, ContDiffOn ℝ ∞ (fun x => R x i) s)
    (hcone : ∀ x ∈ s, SmoothCovariance.StrictCone (G x) (T x))
    (hσ : 0 < σ) (hgap : ∀ i, κ i < σ / 2) (i : Fin 2) (loss : ℕ) :
    ContDiffOn ℝ ∞ (fun x => primaryAmplitude σ κ G T x i / x ^ loss) s ∧
    ContDiffOn ℝ ∞ (fun x => signedAmplitude σ σ κ G T R x i / x ^ loss) s := by
  constructor
  · exact primaryAmplitude_div_pow_contDiffOn hG hT hcone
      (fun j => by linarith [hgap j]) i loss
  · exact signedAmplitude_div_pow_contDiffOn hG hT hR hcone
      (fun j => by linarith [hgap j]) i loss

end Smooth

/-- Concrete compact-family lower bounds with the vanishing factors left
explicit. In particular the primary square-root denominator is controlled. -/
theorem compact_weighted_lower_bounds {K : Set ℝ} (hK : IsCompact K)
    {σ : ℝ} {κ : Vec2} {G : ℝ → Mat2} {T : ℝ → Vec2}
    (hG : ∀ i j, ContinuousOn (fun x => G x i j) K)
    (hT : ∀ i, ContinuousOn (fun x => T x i) K)
    (hcone : ∀ x ∈ K, SmoothCovariance.StrictCone (G x) (T x)) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ x ∈ K, ∀ i,
      δ * edge (σ - κ i) x ≤ inverseCoefficients σ κ G T x i ∧
      δ * edge ((σ - κ i) / 2) x ≤ primaryAmplitude σ κ G T x i := by
  obtain ⟨δ, hδ, hbound⟩ := SmoothCovariance.compact_uniform_amplitudes hK hG hT hcone
  refine ⟨δ, hδ, ?_⟩
  intro x hx i
  rw [inverseCoefficients_factor σ κ G T (hcone x hx).det_ne_zero i,
    primaryAmplitude_factor σ κ G T (hcone x hx).det_ne_zero i]
  constructor
  · simpa only [mul_comm] using mul_le_mul_of_nonneg_left ((hbound x hx).2 i).1
      (FlatCutoff.edge_nonneg (σ - κ i) x)
  · simpa only [mul_comm] using mul_le_mul_of_nonneg_left ((hbound x hx).2 i).2
      (FlatCutoff.edge_nonneg ((σ - κ i) / 2) x)

/-- A smooth function that is zero on the nonpositive half-line has every
derivative zero at the joining point. -/
theorem iteratedDeriv_zero_of_nonpos_zero {f : ℝ → ℝ}
    (hf : ContDiff ℝ ∞ f) (hzero : ∀ x ≤ 0, f x = 0) (n : ℕ) :
    iteratedDeriv n f 0 = 0 := by
  have hz : iteratedDeriv n (fun _ : ℝ => (0 : ℝ)) = fun _ => 0 := by
    induction n with
    | zero => rw [iteratedDeriv_zero]
    | succ n ih =>
      rw [iteratedDeriv_succ, ih]
      funext x
      exact deriv_const x 0
  have heq : EqOn f (fun _ : ℝ => (0 : ℝ)) (Iio 0) :=
    fun x hx => hzero x hx.le
  have hd := heq.iteratedDeriv_of_isOpen isOpen_Iio n
  rw [hz] at hd
  have hc : Continuous (iteratedDeriv n f) := hf.continuous_iteratedDeriv n
    (WithTop.coe_le_coe.mpr (le_top : (n : ℕ∞) ≤ ⊤))
  have hcl := hd.closure hc continuous_const
  apply hcl
  simp

section GlobalFlatness

variable {σ τ : ℝ} {κ : Vec2} {G : ℝ → Mat2} {T R : ℝ → Vec2}

theorem primaryAmplitude_div_pow_contDiff
    (hG : ∀ i j, ContDiff ℝ ∞ (fun x => G x i j))
    (hT : ∀ i, ContDiff ℝ ∞ (fun x => T x i))
    (hcone : ∀ x, SmoothCovariance.StrictCone (G x) (T x))
    (hgap : ∀ i, κ i < σ) (i : Fin 2) (loss : ℕ) :
    ContDiff ℝ ∞ (fun x => primaryAmplitude σ κ G T x i / x ^ loss) :=
  contDiffOn_univ.mp (primaryAmplitude_div_pow_contDiffOn
    (fun i j => (hG i j).contDiffOn) (fun i => (hT i).contDiffOn)
    (fun x _ => hcone x) hgap i loss)

theorem signedAmplitude_div_pow_contDiff
    (hG : ∀ i j, ContDiff ℝ ∞ (fun x => G x i j))
    (hT : ∀ i, ContDiff ℝ ∞ (fun x => T x i))
    (hR : ∀ i, ContDiff ℝ ∞ (fun x => R x i))
    (hcone : ∀ x, SmoothCovariance.StrictCone (G x) (T x))
    (hgap : ∀ i, (σ + κ i) / 2 < τ) (i : Fin 2) (loss : ℕ) :
    ContDiff ℝ ∞ (fun x => signedAmplitude σ τ κ G T R x i / x ^ loss) :=
  contDiffOn_univ.mp (signedAmplitude_div_pow_contDiffOn
    (fun i j => (hG i j).contDiffOn) (fun i => (hT i).contDiffOn)
    (fun i => (hR i).contDiffOn) (fun x _ => hcone x) hgap i loss)

/-- Actual all-order flatness of the primary, also after every fixed
inverse-power loss, obtained from the proved smooth zero extension. -/
theorem primary_weighted_derivatives_zero
    (hG : ∀ i j, ContDiff ℝ ∞ (fun x => G x i j))
    (hT : ∀ i, ContDiff ℝ ∞ (fun x => T x i))
    (hcone : ∀ x, SmoothCovariance.StrictCone (G x) (T x))
    (hgap : ∀ i, κ i < σ) (i : Fin 2) (loss n : ℕ) :
    iteratedDeriv n (fun x => primaryAmplitude σ κ G T x i / x ^ loss) 0 = 0 := by
  apply iteratedDeriv_zero_of_nonpos_zero
    (primaryAmplitude_div_pow_contDiff hG hT hcone hgap i loss)
  intro x hx
  simp [primaryAmplitude_of_nonpos σ κ G T hx i]

theorem signed_weighted_derivatives_zero
    (hG : ∀ i j, ContDiff ℝ ∞ (fun x => G x i j))
    (hT : ∀ i, ContDiff ℝ ∞ (fun x => T x i))
    (hR : ∀ i, ContDiff ℝ ∞ (fun x => R x i))
    (hcone : ∀ x, SmoothCovariance.StrictCone (G x) (T x))
    (hgap : ∀ i, (σ + κ i) / 2 < τ) (i : Fin 2) (loss n : ℕ) :
    iteratedDeriv n (fun x => signedAmplitude σ τ κ G T R x i / x ^ loss) 0 = 0 := by
  apply iteratedDeriv_zero_of_nonpos_zero
    (signedAmplitude_div_pow_contDiff hG hT hR hcone hgap i loss)
  intro x hx
  simp [signedAmplitude_of_nonpos σ τ κ G T R hx i]

end GlobalFlatness

section ParameterFamilies

variable {E : Type*}

/-- Evaluation of the actual inverse amplitude at a smooth signed edge
coordinate, with independent smooth parameters in the normalized data. -/
def parameterPrimary (σ : ℝ) (κ : Vec2) (d : E → ℝ)
    (G : E → Mat2) (T : E → Vec2) (z : E) : Vec2 :=
  primaryAmplitude σ κ (fun _ => G z) (fun _ => T z) (d z)

/-- Parameter signed, given by `signedAmplitude σ τ κ (fun _ => G z) (fun _ => T z) (fun _ => R
z) (d z)`. -/
def parameterSigned (σ τ : ℝ) (κ : Vec2) (d : E → ℝ)
    (G : E → Mat2) (T R : E → Vec2) (z : E) : Vec2 :=
  signedAmplitude σ τ κ (fun _ => G z) (fun _ => T z) (fun _ => R z) (d z)

theorem parameterPrimary_of_nonpos (σ : ℝ) (κ : Vec2) (d : E → ℝ)
    (G : E → Mat2) (T : E → Vec2) {z : E} (hz : d z ≤ 0) (i : Fin 2) :
    parameterPrimary σ κ d G T z i = 0 :=
  primaryAmplitude_of_nonpos σ κ (fun _ => G z) (fun _ => T z) hz i

theorem parameterSigned_of_nonpos (σ τ : ℝ) (κ : Vec2) (d : E → ℝ)
    (G : E → Mat2) (T R : E → Vec2) {z : E} (hz : d z ≤ 0) (i : Fin 2) :
    parameterSigned σ τ κ d G T R z i = 0 :=
  signedAmplitude_of_nonpos σ τ κ (fun _ => G z) (fun _ => T z) (fun _ => R z) hz i

variable [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Joint smoothness in the edge coordinate and all additional parameters,
after any fixed inverse power of the edge coordinate. -/
theorem parameterPrimary_div_pow_contDiffOn
    {s : Set E} {σ : ℝ} {κ : Vec2} {d : E → ℝ}
    {G : E → Mat2} {T : E → Vec2}
    (hd : ContDiffOn ℝ ∞ d s)
    (hG : ∀ i j, ContDiffOn ℝ ∞ (fun z => G z i j) s)
    (hT : ∀ i, ContDiffOn ℝ ∞ (fun z => T z i) s)
    (hcone : ∀ z ∈ s, SmoothCovariance.StrictCone (G z) (T z))
    (hgap : ∀ i, κ i < σ) (i : Fin 2) (loss : ℕ) :
    ContDiffOn ℝ ∞ (fun z => parameterPrimary σ κ d G T z i / d z ^ loss) s := by
  have hp : 0 < (σ - κ i) / 2 := by linarith [hgap i]
  apply (((FlatCutoff.edge_div_pow_contDiff hp loss (n := ⊤)).comp_contDiffOn hd).mul
    (SmoothCovariance.contDiffOn_amplitudes hG hT hcone i)).congr
  intro z hz
  unfold parameterPrimary
  rw [primaryAmplitude_factor σ κ (fun _ => G z) (fun _ => T z)
    (hcone z hz).det_ne_zero i]
  dsimp only [Function.comp_def]
  ring

theorem parameterSigned_div_pow_contDiffOn
    {s : Set E} {σ τ : ℝ} {κ : Vec2} {d : E → ℝ}
    {G : E → Mat2} {T R : E → Vec2}
    (hd : ContDiffOn ℝ ∞ d s)
    (hG : ∀ i j, ContDiffOn ℝ ∞ (fun z => G z i j) s)
    (hT : ∀ i, ContDiffOn ℝ ∞ (fun z => T z i) s)
    (hR : ∀ i, ContDiffOn ℝ ∞ (fun z => R z i) s)
    (hcone : ∀ z ∈ s, SmoothCovariance.StrictCone (G z) (T z))
    (hgap : ∀ i, (σ + κ i) / 2 < τ) (i : Fin 2) (loss : ℕ) :
    ContDiffOn ℝ ∞ (fun z => parameterSigned σ τ κ d G T R z i / d z ^ loss) s := by
  have hn : ContDiffOn ℝ ∞ (fun z => SmoothCovariance.weights (G z) (R z) i /
      (2 * SmoothCovariance.amplitudes (G z) (T z) i)) s := by
    apply (SmoothCovariance.contDiffOn_weights hG hR
      (fun z hz => (hcone z hz).det_ne_zero) i).div
        (contDiffOn_const.mul (SmoothCovariance.contDiffOn_amplitudes hG hT hcone i))
    intro z hz
    exact mul_ne_zero (by norm_num) (ne_of_gt ((hcone z hz).amplitudes_pos i))
  apply (((FlatCutoff.edge_div_pow_contDiff (sub_pos.mpr (hgap i)) loss
    (n := ⊤)).comp_contDiffOn hd).mul hn).congr
  intro z hz
  unfold parameterSigned
  rw [signedAmplitude_factor σ τ κ (fun _ => G z) (fun _ => T z) (fun _ => R z)
    (hcone z hz).det_ne_zero i]
  dsimp only [Function.comp_def]
  ring

end ParameterFamilies

end NavierStokes.FlatCovariance

end
end

end

@[expose] public section

noncomputable section

namespace NavierStokes.PulseCovariance

open Set MeasureTheory Filter
open scoped Topology

private theorem inverse_length_mass (r u v : ℝ) (hr : r ≠ 0) :
    (u / r ^ 2) * (v * r) = u * v / r := by
  field_simp

private theorem normalize_mass_product (u k r : ℝ) (hk : k ≠ 0) :
    u * r ^ 2 = (u / k) * r * (k * r) := by
  field_simp

private theorem sub_normalized_mass (u m v : ℝ) (hm : m ≠ 0) :
    u / m - v = (u - m * v) / m := by
  field_simp

private theorem normalize_direction_product (r ε K C m : ℝ) (hr : r ≠ 0) :
    ε * m + (K / r ^ 2) * (C * r * m) = (ε + K * C / r) * m := by
  field_simp

/-- Gaussian, given by `Real.exp (-b * ((v - m) / r) ^ 2)`. -/
noncomputable def gaussian (b m r v : ℝ) : ℝ :=
  Real.exp (-b * ((v - m) / r) ^ 2)

/-- First gaussian moment, given by `∫ v : ℝ, |v| * Real.exp (-b * v ^ 2)`. -/
noncomputable def firstGaussianMoment (b : ℝ) : ℝ :=
  ∫ v : ℝ, |v| * Real.exp (-b * v ^ 2)

theorem gaussian_pos (b m r v : ℝ) : 0 < gaussian b m r v := Real.exp_pos _

theorem gaussian_eq_length (b m r v : ℝ) :
    gaussian b m r v = Real.exp (-b * (v - m) ^ 2 / r ^ 2) := by
  unfold gaussian
  congr 1
  ring

/-- The reference ODE envelope already constructed in `GaussianEnvelope`
supplies the pointwise Gaussian hypotheses with constants independent of slot
length. -/
theorem reference_envelope_gaussian_bounds {lam u : ℝ} (hlam : 0 < lam) (hu : 0 < u) :
    ∃ b B : ℝ, 0 < b ∧ 0 < B ∧ ∀ r : ℝ, 0 < r → ∀ v ∈ Icc 0 (r ^ 2),
      gaussian B (r ^ 2 / 2) r v ≤
        GaussianEnvelope.envelope (GaussianEnvelope.referenceRate lam u (r ^ 2))
          (r ^ 2 / 2) v ∧
      GaussianEnvelope.envelope (GaussianEnvelope.referenceRate lam u (r ^ 2))
          (r ^ 2 / 2) v ≤ gaussian b (r ^ 2 / 2) r v := by
  obtain ⟨b, B, hb, hB, hbounds⟩ :=
    GaussianEnvelope.reference_uniform_gaussian_bounds hlam hu
  refine ⟨b, B, hb, hB, ?_⟩
  intro r hr v hv
  simpa only [gaussian_eq_length] using hbounds (r ^ 2) (sq_pos_of_pos hr) v hv

theorem integrable_gaussian {b r : ℝ} (hb : 0 < b) (hr : 0 < r) (m : ℝ) :
    Integrable (gaussian b m r) := by
  exact ((integrable_exp_neg_mul_sq hb).comp_div hr.ne').comp_sub_right m

theorem integral_gaussian_scaled (b m r : ℝ) (hr : 0 < r) :
    (∫ v : ℝ, gaussian b m r v) = r * Real.sqrt (Real.pi / b) := by
  unfold gaussian
  rw [integral_sub_right_eq_self (fun v : ℝ => Real.exp (-b * (v / r) ^ 2)) m]
  rw [Measure.integral_comp_div (fun u : ℝ => Real.exp (-b * u ^ 2)) r,
    integral_gaussian, abs_of_pos hr, smul_eq_mul]

theorem integrable_first_gaussian {b : ℝ} (hb : 0 < b) :
    Integrable (fun v : ℝ => |v| * Real.exp (-b * v ^ 2)) := by
  simpa only [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _)] using
    (integrable_mul_exp_neg_mul_sq hb).norm

theorem firstGaussianMoment_nonneg (b : ℝ) : 0 ≤ firstGaussianMoment b := by
  apply integral_nonneg
  intro v
  exact mul_nonneg (abs_nonneg _) (Real.exp_pos _).le

theorem abs_sub_scaled {r : ℝ} (hr : 0 < r) (v m : ℝ) :
    |v - m| = r * |(v - m) / r| := by
  rw [abs_div, abs_of_pos hr]
  field_simp

theorem integrable_first_gaussian_scaled {b r : ℝ} (hb : 0 < b) (hr : 0 < r)
    (m : ℝ) : Integrable (fun v : ℝ => |v - m| * gaussian b m r v) := by
  have hi := (((integrable_first_gaussian hb).comp_div hr.ne').comp_sub_right m).const_mul r
  convert! hi using 1
  ext v
  rw [abs_sub_scaled hr v m]
  simp only [gaussian]
  ring

theorem integral_first_gaussian_scaled (b m r : ℝ) (hr : 0 < r) :
    (∫ v : ℝ, |v - m| * gaussian b m r v) = r ^ 2 * firstGaussianMoment b := by
  have heq : (fun v : ℝ => |v - m| * gaussian b m r v) =
      (fun v : ℝ => r * (|(v - m) / r| * Real.exp (-b * ((v - m) / r) ^ 2))) := by
    ext v
    rw [abs_sub_scaled hr v m]
    simp only [gaussian]
    ring
  rw [heq, integral_const_mul]
  rw [integral_sub_right_eq_self
    (fun v : ℝ => |v / r| * Real.exp (-b * (v / r) ^ 2)) m]
  rw [Measure.integral_comp_div (fun u : ℝ => |u| * Real.exp (-b * u ^ 2)) r,
    abs_of_pos hr, smul_eq_mul]
  simp only [firstGaussianMoment]
  ring

/-- Weight, given by `ψ v ^ 2 * x v ^ 2`. -/
noncomputable def weight (ψ x : ℝ → ℝ) (v : ℝ) : ℝ := ψ v ^ 2 * x v ^ 2

/-- Mass, given by `∫ v : ℝ, weight ψ x v`. -/
noncomputable def mass (ψ x : ℝ → ℝ) : ℝ := ∫ v : ℝ, weight ψ x v

/-- Centered moment, given by `∫ v : ℝ, |v - m| * weight ψ x v`. -/
noncomputable def centeredMoment (ψ x : ℝ → ℝ) (m : ℝ) : ℝ :=
  ∫ v : ℝ, |v - m| * weight ψ x v

/-- All assumptions concern actual pointwise functions on the slot.  No
integrated covariance bound is an input. -/
structure PulseBounds (r a A b B : ℝ) (ψ x : ℝ → ℝ) : Prop where
  radius_one_le : 1 ≤ r
  lower_pos : 0 < a
  upper_pos : 0 < A
  decay_pos : 0 < b
  lower_decay_pos : 0 < B
  cutoff_continuous : Continuous ψ
  component_continuous : Continuous x
  cutoff_abs_le : ∀ v, |ψ v| ≤ 1
  cutoff_zero : ∀ v, v ∉ Icc (r ^ 2 / 6) (5 * r ^ 2 / 6) → ψ v = 0
  cutoff_one : ∀ v ∈ Icc (r ^ 2 / 3) (2 * r ^ 2 / 3), ψ v = 1
  component_lower : ∀ v ∈ Icc 0 (r ^ 2), a * gaussian B (r ^ 2 / 2) r v ≤ x v
  component_upper : ∀ v ∈ Icc 0 (r ^ 2), x v ≤ A * gaussian b (r ^ 2 / 2) r v

/-- The cutoff conditions, separated from the ODE envelope for the adapter. -/
structure CutoffBounds (r : ℝ) (ψ : ℝ → ℝ) : Prop where
  continuous : Continuous ψ
  abs_le : ∀ v, |ψ v| ≤ 1
  zero_outside : ∀ v, v ∉ Icc (r ^ 2 / 6) (5 * r ^ 2 / 6) → ψ v = 0
  one_inside : ∀ v ∈ Icc (r ^ 2 / 3) (2 * r ^ 2 / 3), ψ v = 1

/-- Direct adapter from the growing-mode comparison `a P ≤ x ≤ A P` and
two-sided Gaussian estimates on the actual reference envelope `P`. -/
theorem pulseBounds_of_envelope {r a A b B : ℝ} {ψ x P : ℝ → ℝ}
    (hr : 1 ≤ r) (ha : 0 < a) (hA : 0 < A) (hb : 0 < b) (hB : 0 < B)
    (hψ : CutoffBounds r ψ) (hx : Continuous x)
    (hP : ∀ v ∈ Icc 0 (r ^ 2),
      gaussian B (r ^ 2 / 2) r v ≤ P v ∧ P v ≤ gaussian b (r ^ 2 / 2) r v)
    (hcompare : ∀ v ∈ Icc 0 (r ^ 2), a * P v ≤ x v ∧ x v ≤ A * P v) :
    PulseBounds r a A b B ψ x := by
  refine ⟨hr, ha, hA, hb, hB, hψ.continuous, hx,
    hψ.abs_le, hψ.zero_outside, hψ.one_inside, ?_, ?_⟩
  · intro v hv
    exact (mul_le_mul_of_nonneg_left (hP v hv).1 ha.le).trans (hcompare v hv).1
  · intro v hv
    exact (hcompare v hv).2.trans (mul_le_mul_of_nonneg_left (hP v hv).2 hA.le)

namespace PulseBounds

variable {r a A b B : ℝ} {ψ x : ℝ → ℝ} (h : PulseBounds r a A b B ψ x)

include h

theorem radius_pos : 0 < r := lt_of_lt_of_le zero_lt_one h.radius_one_le

theorem component_pos {v : ℝ} (hv : v ∈ Icc 0 (r ^ 2)) : 0 < x v :=
  lt_of_lt_of_le (mul_pos h.lower_pos (gaussian_pos _ _ _ _)) (h.component_lower v hv)

omit h in
theorem weight_nonneg (v : ℝ) : 0 ≤ weight ψ x v := mul_nonneg (sq_nonneg _) (sq_nonneg _)

theorem weight_continuous : Continuous (weight ψ x) :=
  (h.cutoff_continuous.pow 2).mul (h.component_continuous.pow 2)

theorem weight_gaussian_upper (v : ℝ) :
    weight ψ x v ≤ A ^ 2 * gaussian (2 * b) (r ^ 2 / 2) r v := by
  by_cases hv : v ∈ Icc (r ^ 2 / 6) (5 * r ^ 2 / 6)
  · have hslot : v ∈ Icc 0 (r ^ 2) := by
      constructor <;> nlinarith [hv.1, hv.2, sq_nonneg r]
    have hx := h.component_upper v hslot
    have hx0 := (h.component_pos hslot).le
    have hg := (gaussian_pos b (r ^ 2 / 2) r v).le
    have hψ : ψ v ^ 2 ≤ 1 := by
      have hp := h.cutoff_abs_le v
      have hab := abs_le.mp hp
      nlinarith [sq_nonneg (ψ v), hab.1, hab.2]
    have he : gaussian b (r ^ 2 / 2) r v ^ 2 =
        gaussian (2 * b) (r ^ 2 / 2) r v := by
      simp only [gaussian, sq, ← Real.exp_add]
      congr 1
      ring
    calc
      weight ψ x v ≤ x v ^ 2 := by
        unfold weight
        nlinarith [mul_le_mul_of_nonneg_right hψ (sq_nonneg (x v))]
      _ ≤ (A * gaussian b (r ^ 2 / 2) r v) ^ 2 :=
        pow_le_pow_left₀ hx0 hx 2
      _ = A ^ 2 * gaussian (2 * b) (r ^ 2 / 2) r v := by rw [mul_pow, he]
  · rw [weight, h.cutoff_zero v hv]
    simpa using mul_nonneg (sq_nonneg A) (gaussian_pos (2 * b) (r ^ 2 / 2) r v).le

theorem weight_integrable : Integrable (weight ψ x) := by
  apply ((integrable_gaussian (b := 2 * b) (by linarith [h.decay_pos]) h.radius_pos
    (r ^ 2 / 2)).const_mul (A ^ 2)).mono' h.weight_continuous.aestronglyMeasurable
  filter_upwards [] with v
  simpa only [Real.norm_eq_abs, abs_of_nonneg (weight_nonneg v)] using
    h.weight_gaussian_upper v

theorem moment_integrable :
    Integrable (fun v : ℝ => |v - r ^ 2 / 2| * weight ψ x v) := by
  apply ((integrable_first_gaussian_scaled (b := 2 * b) (by linarith [h.decay_pos]) h.radius_pos
    (r ^ 2 / 2)).const_mul (A ^ 2)).mono'
      (((continuous_id.fun_sub continuous_const).abs.fun_mul
          h.weight_continuous).aestronglyMeasurable)
  filter_upwards [] with v
  rw [Real.norm_eq_abs, abs_of_nonneg
    (mul_nonneg (abs_nonneg _) (weight_nonneg v))]
  simp only [id_eq]
  nlinarith [mul_le_mul_of_nonneg_left (h.weight_gaussian_upper v) (abs_nonneg (v - r ^ 2 / 2))]

theorem mass_upper : mass ψ x ≤ A ^ 2 * Real.sqrt (Real.pi / (2 * b)) * r := by
  have hi := integral_mono h.weight_integrable
    ((integrable_gaussian (b := 2 * b) (by
        linarith [h.decay_pos]) h.radius_pos (r ^ 2 / 2)).const_mul
      (A ^ 2)) h.weight_gaussian_upper
  rw [integral_const_mul, integral_gaussian_scaled _ _ _ h.radius_pos] at hi
  exact hi.trans_eq (by ring)

theorem moment_upper :
    centeredMoment ψ x (r ^ 2 / 2) ≤ A ^ 2 * firstGaussianMoment (2 * b) * r ^ 2 := by
  have hi := integral_mono h.moment_integrable
    ((integrable_first_gaussian_scaled (b := 2 * b) (by linarith [h.decay_pos]) h.radius_pos
      (r ^ 2 / 2)).const_mul (A ^ 2)) (fun v => ?_)
  · rw [integral_const_mul, integral_first_gaussian_scaled _ _ _ h.radius_pos] at hi
    exact hi.trans_eq (by ring)
  · nlinarith [mul_le_mul_of_nonneg_left (h.weight_gaussian_upper v)
      (abs_nonneg (v - r ^ 2 / 2))]

theorem core_mem_middle {v : ℝ}
    (hv : v ∈ Icc (r ^ 2 / 2 - r / 6) (r ^ 2 / 2 + r / 6)) :
    v ∈ Icc (r ^ 2 / 3) (2 * r ^ 2 / 3) := by
  have hr := h.radius_one_le
  have hrr : r ≤ r ^ 2 := by nlinarith [mul_nonneg (sub_nonneg.mpr hr) h.radius_pos.le]
  constructor <;> nlinarith [hv.1, hv.2]

theorem core_scaled_sq {v : ℝ}
    (hv : v ∈ Icc (r ^ 2 / 2 - r / 6) (r ^ 2 / 2 + r / 6)) :
    ((v - r ^ 2 / 2) / r) ^ 2 ≤ 1 / 36 := by
  have hlo : -(1 / 6 : ℝ) ≤ (v - r ^ 2 / 2) / r := by
    apply (le_div_iff₀ h.radius_pos).mpr
    linarith [hv.1]
  have hhi : (v - r ^ 2 / 2) / r ≤ (1 / 6 : ℝ) := by
    apply (div_le_iff₀ h.radius_pos).mpr
    linarith [hv.2]
  nlinarith

theorem core_weight_lower {v : ℝ}
    (hv : v ∈ Icc (r ^ 2 / 2 - r / 6) (r ^ 2 / 2 + r / 6)) :
    a ^ 2 * Real.exp (-B / 18) ≤ weight ψ x v := by
  have hmid := h.core_mem_middle hv
  have hslot : v ∈ Icc 0 (r ^ 2) := by
    constructor <;> nlinarith [hmid.1, hmid.2, sq_nonneg r]
  have hx := h.component_lower v hslot
  have he : Real.exp (-B / 18) ≤ gaussian B (r ^ 2 / 2) r v ^ 2 := by
    unfold gaussian
    rw [pow_two, ← Real.exp_add]
    apply Real.exp_le_exp.mpr
    nlinarith [mul_le_mul_of_nonneg_left (h.core_scaled_sq hv) h.lower_decay_pos.le]
  rw [weight, h.cutoff_one v hmid]
  simp only [one_pow, one_mul]
  calc
    a ^ 2 * Real.exp (-B / 18) ≤ a ^ 2 * gaussian B (r ^ 2 / 2) r v ^ 2 :=
      mul_le_mul_of_nonneg_left he (sq_nonneg _)
    _ = (a * gaussian B (r ^ 2 / 2) r v) ^ 2 := by ring
    _ ≤ x v ^ 2 := pow_le_pow_left₀
      (mul_pos h.lower_pos (gaussian_pos _ _ _ _)).le hx 2

/-- Lower mass constant, given by `a ^ 2 * Real.exp (-B / 18) / 3`. -/
noncomputable def lowerMassConstant (a B : ℝ) : ℝ := a ^ 2 * Real.exp (-B / 18) / 3

theorem lowerMassConstant_pos : 0 < lowerMassConstant a B := by
  unfold lowerMassConstant
  have := h.lower_pos
  positivity

theorem mass_lower : lowerMassConstant a B * r ≤ mass ψ x := by
  have hv : (volume : Measure ℝ) (Icc (r ^ 2 / 2 - r / 6) (r ^ 2 / 2 + r / 6)) ≠ ⊤ :=
    ne_of_lt (isCompact_Icc.measure_lt_top)
  have hi := setIntegral_ge_of_const_le measurableSet_Icc hv
    (fun v hv => h.core_weight_lower hv) h.weight_integrable.integrableOn
  rw [Real.volume_real_Icc_of_le (by linarith [h.radius_pos])] at hi
  have hj := setIntegral_le_integral (s := Icc (r ^ 2 / 2 - r / 6) (r ^ 2 / 2 + r / 6))
    h.weight_integrable (ae_of_all _ weight_nonneg)
  change _ ≤ mass ψ x at hj
  calc
    lowerMassConstant a B * r =
        (a ^ 2 * Real.exp (-B / 18)) *
          (r ^ 2 / 2 + r / 6 - (r ^ 2 / 2 - r / 6)) := by
      unfold lowerMassConstant
      ring
    _ ≤ _ := by simpa only [smul_eq_mul, mul_comm] using hi
    _ ≤ mass ψ x := hj

theorem mass_pos : 0 < mass ψ x :=
  lt_of_lt_of_le (mul_pos h.lowerMassConstant_pos h.radius_pos) h.mass_lower

theorem cutoff_compact : HasCompactSupport ψ :=
  HasCompactSupport.intro isCompact_Icc h.cutoff_zero

theorem weight_compact : HasCompactSupport (weight ψ x) := by
  apply HasCompactSupport.intro (K := Icc (r ^ 2 / 6) (5 * r ^ 2 / 6)) isCompact_Icc
  intro v hv
  simp [weight, h.cutoff_zero v hv]

theorem weight_direction_integrable {q : ℝ → ℝ}
    (hq : ContinuousOn q (Icc 0 (r ^ 2))) :
    Integrable (fun v => weight ψ x v * q v) := by
  have hs : Function.support (fun v => weight ψ x v * q v) ⊆ Icc 0 (r ^ 2) := by
    intro v hv
    by_contra hv'
    have hout : v ∉ Icc (r ^ 2 / 6) (5 * r ^ 2 / 6) := by
      intro hin
      apply hv'
      constructor <;> nlinarith [hin.1, hin.2, sq_nonneg r]
    exact hv (by simp [weight, h.cutoff_zero v hout])
  apply (integrableOn_iff_integrable_of_support_subset hs).mp
  exact (h.weight_continuous.continuousOn.mul hq).integrableOn_Icc

/-- The positive scalar prefactor has precisely the required reciprocal-square -
root size when the column coefficient has reciprocal-slot-length size. -/
theorem scalar_size_bounds {ci clo chi : ℝ} (hclo : 0 < clo) (hchi : 0 < chi)
    (hci_lower : clo / r ^ 2 ≤ ci) (hci_upper : ci ≤ chi / r ^ 2) :
    0 < ci * mass ψ x ∧
      clo * lowerMassConstant a B / r ≤ ci * mass ψ x ∧
      ci * mass ψ x ≤ chi * (A ^ 2 * Real.sqrt (Real.pi / (2 * b))) / r := by
  have hr2 : 0 < r ^ 2 := sq_pos_of_pos h.radius_pos
  have hci : 0 < ci := lt_of_lt_of_le (div_pos hclo hr2) hci_lower
  refine ⟨mul_pos hci h.mass_pos, ?_, ?_⟩
  · calc
      clo * lowerMassConstant a B / r =
          (clo / r ^ 2) * (lowerMassConstant a B * r) :=
        (inverse_length_mass _ _ _ h.radius_pos.ne').symm
      _ ≤ ci * mass ψ x :=
        mul_le_mul hci_lower h.mass_lower
          (mul_pos h.lowerMassConstant_pos h.radius_pos).le hci.le
  · calc
      ci * mass ψ x ≤ (chi / r ^ 2) *
          (A ^ 2 * Real.sqrt (Real.pi / (2 * b)) * r) :=
        mul_le_mul hci_upper h.mass_upper h.mass_pos.le (div_pos hchi hr2).le
      _ = chi * (A ^ 2 * Real.sqrt (Real.pi / (2 * b))) / r :=
        inverse_length_mass _ _ _ h.radius_pos.ne'

end PulseBounds

/-- Averaged direction, given by `(∫ v : ℝ, weight ψ x v * q v) / mass ψ x`. -/
noncomputable def averagedDirection (ψ x q : ℝ → ℝ) : ℝ :=
  (∫ v : ℝ, weight ψ x v * q v) / mass ψ x

/-- Concentration constant, given by `A ^ 2 * firstGaussianMoment (2 * b) /
PulseBounds.lowerMassConstant a B`. -/
noncomputable def concentrationConstant (a A b B : ℝ) : ℝ :=
  A ^ 2 * firstGaussianMoment (2 * b) / PulseBounds.lowerMassConstant a B

namespace PulseBounds

variable {r a A b B : ℝ} {ψ x : ℝ → ℝ} (h : PulseBounds r a A b B ψ x)

include h

theorem concentrationConstant_nonneg : 0 ≤ concentrationConstant a A b B := by
  exact div_nonneg (mul_nonneg (sq_nonneg _) (firstGaussianMoment_nonneg _))
    h.lowerMassConstant_pos.le

theorem normalized_moment_bound :
    centeredMoment ψ x (r ^ 2 / 2) / mass ψ x ≤ concentrationConstant a A b B * r := by
  apply (div_le_iff₀ h.mass_pos).mpr
  calc
    centeredMoment ψ x (r ^ 2 / 2) ≤
        A ^ 2 * firstGaussianMoment (2 * b) * r ^ 2 := h.moment_upper
    _ = concentrationConstant a A b B * r * (lowerMassConstant a B * r) :=
      normalize_mass_product _ _ _ h.lowerMassConstant_pos.ne'
    _ ≤ concentrationConstant a A b B * r * mass ψ x :=
      mul_le_mul_of_nonneg_left h.mass_lower
        (mul_nonneg h.concentrationConstant_nonneg h.radius_pos.le)

theorem averagedDirection_sub {q : ℝ → ℝ} (hq : ContinuousOn q (Icc 0 (r ^ 2))) (q₀ : ℝ) :
    averagedDirection ψ x q - q₀ =
      (∫ v : ℝ, weight ψ x v * (q v - q₀)) / mass ψ x := by
  have he : (fun v => weight ψ x v * (q v - q₀)) =
      (fun v => weight ψ x v * q v - weight ψ x v * q₀) := by
    ext v
    ring
  rw [he, integral_sub (h.weight_direction_integrable hq)
    (h.weight_integrable.mul_const q₀), integral_mul_const]
  change (∫ v : ℝ, weight ψ x v * q v) / mass ψ x - q₀ =
    ((∫ v : ℝ, weight ψ x v * q v) - mass ψ x * q₀) / mass ψ x
  exact sub_normalized_mass _ _ _ h.mass_pos.ne'

/-- A pointwise directional error plus a pointwise linear drift gives an actual
integrated error.  The moment bounds used below are derived above, not assumed. -/
theorem averagedDirection_error {q : ℝ → ℝ} (hq : ContinuousOn q (Icc 0 (r ^ 2)))
    {q₀ ε K : ℝ} (hK : 0 ≤ K)
    (hqbound : ∀ v ∈ Icc 0 (r ^ 2),
      |q v - q₀| ≤ ε + K * |v - r ^ 2 / 2| / r ^ 2) :
    |averagedDirection ψ x q - q₀| ≤
      ε + K * concentrationConstant a A b B / r := by
  have hgi : Integrable (fun v => ε * weight ψ x v +
      (K / r ^ 2) * (|v - r ^ 2 / 2| * weight ψ x v)) :=
    (h.weight_integrable.const_mul ε).add (h.moment_integrable.const_mul (K / r ^ 2))
  have hpoint (v : ℝ) : |weight ψ x v * (q v - q₀)| ≤
      ε * weight ψ x v + (K / r ^ 2) * (|v - r ^ 2 / 2| * weight ψ x v) := by
    by_cases hv : v ∈ Icc (r ^ 2 / 6) (5 * r ^ 2 / 6)
    · have hslot : v ∈ Icc 0 (r ^ 2) := by
        constructor <;> nlinarith [hv.1, hv.2, sq_nonneg r]
      rw [abs_mul, abs_of_nonneg (weight_nonneg v)]
      convert! mul_le_mul_of_nonneg_left (hqbound v hslot) (weight_nonneg v) using 1
      ring
    · simp [weight, h.cutoff_zero v hv]
  have hi := norm_integral_le_of_norm_le (f := fun v => weight ψ x v * (q v - q₀))
    hgi (ae_of_all _ (fun v => by simpa only [Real.norm_eq_abs] using hpoint v))
  simp only [Real.norm_eq_abs] at hi
  rw [integral_add (h.weight_integrable.const_mul ε)
    (h.moment_integrable.const_mul (K / r ^ 2)), integral_const_mul, integral_const_mul] at hi
  change |∫ v : ℝ, weight ψ x v * (q v - q₀)| ≤
    ε * mass ψ x + (K / r ^ 2) * centeredMoment ψ x (r ^ 2 / 2) at hi
  rw [h.averagedDirection_sub hq q₀, abs_div, abs_of_pos h.mass_pos]
  apply (div_le_iff₀ h.mass_pos).mpr
  calc
    |∫ v : ℝ, weight ψ x v * (q v - q₀)| ≤
        ε * mass ψ x + (K / r ^ 2) * centeredMoment ψ x (r ^ 2 / 2) := hi
    _ ≤ ε * mass ψ x + (K / r ^ 2) *
        (concentrationConstant a A b B * r * mass ψ x) := by
      apply add_le_add_right
      apply mul_le_mul_of_nonneg_left _ (div_nonneg hK (sq_nonneg r))
      exact (div_le_iff₀ h.mass_pos).mp h.normalized_moment_bound
    _ = (ε + K * concentrationConstant a A b B / r) * mass ψ x :=
      normalize_direction_product _ _ _ _ _ h.radius_pos.ne'

/-- The ODE directional error `E/L` is smaller than the Gaussian concentration
error `1/sqrt L`. -/
theorem averagedDirection_error_order {q : ℝ → ℝ}
    (hq : ContinuousOn q (Icc 0 (r ^ 2))) {q₀ E K : ℝ}
    (hE : 0 ≤ E) (hK : 0 ≤ K)
    (hqbound : ∀ v ∈ Icc 0 (r ^ 2),
      |q v - q₀| ≤ E / r ^ 2 + K * |v - r ^ 2 / 2| / r ^ 2) :
    |averagedDirection ψ x q - q₀| ≤
      (E + K * concentrationConstant a A b B) / r := by
  have hi := h.averagedDirection_error hq hK hqbound
  have hEr : E / r ^ 2 ≤ E / r := by
    apply div_le_div_of_nonneg_left hE h.radius_pos
    nlinarith [mul_nonneg (sub_nonneg.mpr h.radius_one_le) h.radius_pos.le]
  apply hi.trans
  rw [add_div]
  exact add_le_add_left hEr _

end PulseBounds

/-- Vec2: an abbreviation for `SmoothCovariance.Vec2`. -/
abbrev Vec2 := SmoothCovariance.Vec2
/-- Mat2: an abbreviation for `SmoothCovariance.Mat2`. -/
abbrev Mat2 := SmoothCovariance.Mat2

/-- Radius profile, given by `Real.sqrt (1 + s ^ 2)`. -/
noncomputable def radiusProfile (s : ℝ) : ℝ := Real.sqrt (1 + s ^ 2)

theorem radiusProfile_pos (s : ℝ) : 0 < radiusProfile s := by
  apply Real.sqrt_pos.mpr
  positivity

theorem radiusProfile_sq (s : ℝ) : radiusProfile s ^ 2 = 1 + s ^ 2 :=
  Real.sq_sqrt (by positivity)

theorem abs_le_radiusProfile (s : ℝ) : |s| ≤ radiusProfile s := by
  have hp := (radiusProfile_pos s).le
  have hs := radiusProfile_sq s
  nlinarith [sq_abs s, abs_nonneg s]

/-- The square-root profile used in the actual tangent model is globally
one-Lipschitz; smoothness of a normalized direction is not assumed here. -/
theorem radiusProfile_lipschitz (s t : ℝ) :
    |radiusProfile s - radiusProfile t| ≤ |s - t| := by
  have hp : 0 < radiusProfile s + radiusProfile t :=
    add_pos (radiusProfile_pos s) (radiusProfile_pos t)
  have he : (radiusProfile s - radiusProfile t) * (radiusProfile s + radiusProfile t) =
      (s - t) * (s + t) := by
    nlinarith [radiusProfile_sq s, radiusProfile_sq t]
  have ha := congrArg abs he
  rw [abs_mul, abs_mul, abs_of_pos hp] at ha
  have hst : |s + t| ≤ radiusProfile s + radiusProfile t :=
    (abs_add_le s t).trans (add_le_add (abs_le_radiusProfile s) (abs_le_radiusProfile t))
  exact (mul_le_mul_iff_left₀ hp).mp (by
    nlinarith [mul_le_mul_of_nonneg_left hst (abs_nonneg (s - t))])

/-- Coordinates in the fixed tangent frame `(N,K)` of `h N - s K`, where
`h = c₀ sqrt(1+s²)`. -/
noncomputable def modelDirection (c₀ s : ℝ) : Vec2 := ![c₀ * radiusProfile s, -s]

theorem modelDirection_lipschitz (c₀ s t : ℝ) (i : Fin 2) :
    |modelDirection c₀ s i - modelDirection c₀ t i| ≤ (|c₀| + 1) * |s - t| := by
  fin_cases i
  · change |c₀ * radiusProfile s - c₀ * radiusProfile t| ≤ _
    rw [← mul_sub, abs_mul]
    calc
      |c₀| * |radiusProfile s - radiusProfile t| ≤ |c₀| * |s - t| :=
        mul_le_mul_of_nonneg_left (radiusProfile_lipschitz s t) (abs_nonneg _)
      _ ≤ (|c₀| + 1) * |s - t| := by nlinarith [abs_nonneg (s - t)]
  · change |(-s) - (-t)| ≤ _
    have he : |(-s) - (-t)| = |s - t| := by
      calc
        |(-s) - (-t)| = |-(s - t)| := congrArg abs (by ring)
        _ = |s - t| := abs_neg _
    rw [he]
    nlinarith [mul_nonneg (abs_nonneg c₀) (abs_nonneg (s - t))]

/-- Affine slope, given by `s₀ + slope * (v - r ^ 2 / 2) / r ^ 2`. -/
noncomputable def affineSlope (s₀ slope r v : ℝ) : ℝ :=
  s₀ + slope * (v - r ^ 2 / 2) / r ^ 2

theorem affineSlope_midpoint (s₀ slope r : ℝ) : affineSlope s₀ slope r (r ^ 2 / 2) = s₀ := by
  simp [affineSlope]

theorem hasDerivAt_affineSlope (s₀ slope r v : ℝ) :
    HasDerivAt (affineSlope s₀ slope r) (slope / r ^ 2) v := by
  unfold affineSlope
  simpa only [id_eq, mul_one] using
    (((hasDerivAt_id v).sub_const (r ^ 2 / 2)).const_mul slope).div_const (r ^ 2) |>.const_add s₀

theorem affineSlope_deriv_bound (s₀ slope r v : ℝ) {C : ℝ} (hC : |slope| ≤ C) :
    |deriv (affineSlope s₀ slope r) v| ≤ C / r ^ 2 := by
  rw [(hasDerivAt_affineSlope s₀ slope r v).deriv, abs_div, abs_of_nonneg (sq_nonneg r)]
  exact div_le_div_of_nonneg_right hC (sq_nonneg r)

theorem affineSlope_distance (s₀ slope r v : ℝ) :
    |affineSlope s₀ slope r v - s₀| = |slope| * |v - r ^ 2 / 2| / r ^ 2 := by
  simp only [affineSlope, add_sub_cancel_left, abs_div, abs_mul,
    abs_of_nonneg (sq_nonneg r)]

theorem modelDirection_affine_drift (c₀ s₀ slope r v : ℝ) (i : Fin 2) :
    |modelDirection c₀ (affineSlope s₀ slope r v) i - modelDirection c₀ s₀ i| ≤
      ((|c₀| + 1) * |slope|) * |v - r ^ 2 / 2| / r ^ 2 := by
  have hi := modelDirection_lipschitz c₀ (affineSlope s₀ slope r v) s₀ i
  rw [affineSlope_distance] at hi
  exact hi.trans_eq (by ring)

/-- Actual column, defined pointwise by `ci * ∫ v : ℝ, ψ v ^ 2 * x v * t v i`. -/
noncomputable def actualColumn (ci : ℝ) (ψ x : ℝ → ℝ) (t : ℝ → Vec2) : Vec2 :=
  fun i => ci * ∫ v : ℝ, ψ v ^ 2 * x v * t v i

/-- Normalized column, defined pointwise by `averagedDirection ψ x (fun v => t v i / x v)`. -/
noncomputable def normalizedColumn (ψ x : ℝ → ℝ) (t : ℝ → Vec2) : Vec2 :=
  fun i => averagedDirection ψ x (fun v => t v i / x v)

namespace PulseBounds

variable {r a A b B : ℝ} {ψ x : ℝ → ℝ} (h : PulseBounds r a A b B ψ x)

include h

theorem raw_integrand_eq {t : ℝ → Vec2} (v : ℝ) (i : Fin 2) :
    ψ v ^ 2 * x v * t v i = weight ψ x v * (t v i / x v) := by
  by_cases hv : v ∈ Icc 0 (r ^ 2)
  · have hx := (h.component_pos hv).ne'
    unfold weight
    field_simp
  · have hout : v ∉ Icc (r ^ 2 / 6) (5 * r ^ 2 / 6) := by
      intro hin
      apply hv
      constructor <;> nlinarith [hin.1, hin.2, sq_nonneg r]
    simp [weight, h.cutoff_zero v hout]

/-- Exact factorization of the actual covariance integral into its positive
mass and normalized direction. -/
theorem actualColumn_factorization (ci : ℝ) (t : ℝ → Vec2) :
    actualColumn ci ψ x t = fun i => (ci * mass ψ x) * normalizedColumn ψ x t i := by
  ext i
  unfold actualColumn normalizedColumn averagedDirection
  simp_rw [h.raw_integrand_eq]
  exact (mul_div_cancel_right₀
    (ci * (∫ v : ℝ, weight ψ x v * (t v i / x v))) h.mass_pos.ne').symm.trans (by ring)

theorem actualColumn_eq_intervalIntegral (ci : ℝ) (t : ℝ → Vec2) (i : Fin 2) :
    actualColumn ci ψ x t i = ci * ∫ v in (0 : ℝ)..r ^ 2, ψ v ^ 2 * x v * t v i := by
  unfold actualColumn
  congr 1
  rw [intervalIntegral.integral_of_le (sq_nonneg r)]
  symm
  apply setIntegral_eq_integral_of_forall_compl_eq_zero
  intro v hv
  have hout : v ∉ Icc (r ^ 2 / 6) (5 * r ^ 2 / 6) := by
    intro hin
    apply hv
    have hr2 : 0 < r ^ 2 := sq_pos_of_pos h.radius_pos
    constructor <;> nlinarith [hin.1, hin.2]
  simp [h.cutoff_zero v hout]

theorem ratio_continuousOn {t : ℝ → Vec2}
    (ht : ∀ i, ContinuousOn (fun v => t v i) (Icc 0 (r ^ 2))) (i : Fin 2) :
    ContinuousOn (fun v => t v i / x v) (Icc 0 (r ^ 2)) :=
  (ht i).div h.component_continuous.continuousOn (fun _ hv => (h.component_pos hv).ne')

/-- Directional concentration for actual fundamental tangent components.
The sole tangent estimate assumed is the pointwise ODE approximation to
`h(v)N-s(v)K`, with affine `s` and the exact square-root profile `h`. -/
theorem normalizedColumn_error {t : ℝ → Vec2}
    (ht : ∀ i, ContinuousOn (fun v => t v i) (Icc 0 (r ^ 2)))
    {E c₀ s₀ slope : ℝ} (hE : 0 ≤ E)
    (htmodel : ∀ v ∈ Icc 0 (r ^ 2), ∀ i,
      |t v i / x v - modelDirection c₀ (affineSlope s₀ slope r v) i| ≤ E / r ^ 2)
    (i : Fin 2) :
    |normalizedColumn ψ x t i - modelDirection c₀ s₀ i| ≤
      (E + ((|c₀| + 1) * |slope|) * concentrationConstant a A b B) / r := by
  apply h.averagedDirection_error_order (h.ratio_continuousOn ht i) hE
    (mul_nonneg (by positivity) (abs_nonneg _))
  intro v hv
  exact (abs_sub_le (t v i / x v)
    (modelDirection c₀ (affineSlope s₀ slope r v) i) (modelDirection c₀ s₀ i)).trans
      (add_le_add (htmodel v hv i) (modelDirection_affine_drift c₀ s₀ slope r v i))

/-- The ODE error may instead be supplied as `E/S` on a slot with `L ≤ κ S`.
This converts it to the preceding concentration estimate. -/
theorem normalizedColumn_error_of_outer_scale {t : ℝ → Vec2}
    (ht : ∀ i, ContinuousOn (fun v => t v i) (Icc 0 (r ^ 2)))
    {E S κ c₀ s₀ slope : ℝ} (hE : 0 ≤ E) (hS : 0 < S) (hκ : 0 ≤ κ)
    (hL : r ^ 2 ≤ κ * S)
    (htmodel : ∀ v ∈ Icc 0 (r ^ 2), ∀ i,
      |t v i / x v - modelDirection c₀ (affineSlope s₀ slope r v) i| ≤ E / S)
    (i : Fin 2) :
    |normalizedColumn ψ x t i - modelDirection c₀ s₀ i| ≤
      (E * κ + ((|c₀| + 1) * |slope|) * concentrationConstant a A b B) / r := by
  apply h.normalizedColumn_error ht (mul_nonneg hE hκ) _ i
  intro v hv j
  apply (htmodel v hv j).trans
  apply (div_le_div_iff₀ hS (sq_pos_of_pos h.radius_pos)).mpr
  nlinarith [mul_le_mul_of_nonneg_left hL hE]

end PulseBounds

/-- A single actual pulse.  Every estimate in this record is pointwise;
neither its covariance integral nor its average direction is assumed. -/
structure TangentPulse (r a A b B c₀ s₀ slope E : ℝ) where
  /-- Cutoff of `TangentPulse`, of type `ℝ → ℝ`. -/
  cutoff : ℝ → ℝ
  /-- Component of `TangentPulse`, of type `ℝ → ℝ`. -/
  component : ℝ → ℝ
  /-- Tangent of `TangentPulse`, of type `ℝ → Vec2`. -/
  tangent : ℝ → Vec2
  bounds : PulseBounds r a A b B cutoff component
  tangent_continuous : ∀ i, ContinuousOn (fun v => tangent v i) (Icc 0 (r ^ 2))
  tangent_model : ∀ v ∈ Icc 0 (r ^ 2), ∀ i,
    |tangent v i / component v - modelDirection c₀ (affineSlope s₀ slope r v) i| ≤
      E / r ^ 2

/-- Signed slopes, given by `![u, -u]`. -/
noncomputable def signedSlopes (u : ℝ) : Vec2 := ![u, -u]

/-- Signed model, defined pointwise by `modelDirection c₀ (signedSlopes u j) i`. -/
noncomputable def signedModel (c₀ u : ℝ) : Mat2 :=
  fun i j => modelDirection c₀ (signedSlopes u j) i

theorem signedModel_eq_covariance (c₀ u : ℝ) :
    signedModel c₀ u = Covariance.signedMatrix (Covariance.normalMagnitude c₀ u) u 1 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [signedModel, modelDirection, signedSlopes, Covariance.signedMatrix,
      Covariance.normalMagnitude, radiusProfile]

theorem signedModel_strictCone {c₀ u m t : ℝ} (hc₀ : c₀ < 0) (hu : 0 < u)
    (hcone : |Covariance.normalMagnitude c₀ u * t| < u * m) :
    SmoothCovariance.StrictCone (signedModel c₀ u) (Covariance.target m t) := by
  rw [signedModel_eq_covariance]
  exact SmoothCovariance.signed_model_strictCone (Covariance.normalMagnitude_pos hc₀)
    hu zero_lt_one zero_lt_one hcone

theorem signedModel_continuousOn {X : Type*} [TopologicalSpace X] {K : Set X}
    {c₀ u : X → ℝ} (hc₀ : ContinuousOn c₀ K) (hu : ContinuousOn u K) (i j : Fin 2) :
    ContinuousOn (fun p => signedModel (c₀ p) (u p) i j) K := by
  have hn : ContinuousOn (fun p => c₀ p * Real.sqrt (1 + u p ^ 2)) K :=
    hc₀.mul (Real.continuous_sqrt.comp_continuousOn (continuousOn_const.add (hu.pow 2)))
  fin_cases i <;> fin_cases j
  · simpa [signedModel, modelDirection, signedSlopes, radiusProfile] using hn
  · simpa [signedModel, modelDirection, signedSlopes, radiusProfile] using hn
  · simpa [signedModel, modelDirection, signedSlopes] using hu.fun_neg
  · simpa [signedModel, modelDirection, signedSlopes] using hu

/-- Signed pulse pair: an abbreviation for `(j : Fin 2) → TangentPulse r a A b B c₀
(signedSlopes u j) (signedSlopes u j) E`. -/
abbrev SignedPulsePair (r a A b B c₀ u E : ℝ) :=
  (j : Fin 2) → TangentPulse r a A b B c₀ (signedSlopes u j) (signedSlopes u j) E

/-- Actual matrix, defined pointwise by `actualColumn (ci j) (pulses j).cutoff (pulses
j).component (pulses j).tangent i`. -/
noncomputable def actualMatrix {r a A b B c₀ u E : ℝ}
    (pulses : SignedPulsePair r a A b B c₀ u E) (ci : Vec2) : Mat2 :=
  fun i j => actualColumn (ci j) (pulses j).cutoff (pulses j).component (pulses j).tangent i

/-- Normalized matrix, defined pointwise by `normalizedColumn (pulses j).cutoff (pulses
j).component (pulses j).tangent i`. -/
noncomputable def normalizedMatrix {r a A b B c₀ u E : ℝ}
    (pulses : SignedPulsePair r a A b B c₀ u E) : Mat2 :=
  fun i j => normalizedColumn (pulses j).cutoff (pulses j).component (pulses j).tangent i

/-- Column scales, defined pointwise by `ci j * mass (pulses j).cutoff (pulses j).component`. -/
noncomputable def columnScales {r a A b B c₀ u E : ℝ}
    (pulses : SignedPulsePair r a A b B c₀ u E) (ci : Vec2) : Vec2 :=
  fun j => ci j * mass (pulses j).cutoff (pulses j).component

theorem signedSlopes_abs (u : ℝ) (j : Fin 2) : |signedSlopes u j| = |u| := by
  fin_cases j <;> simp [signedSlopes]

theorem actualMatrix_factorization {r a A b B c₀ u E : ℝ}
    (pulses : SignedPulsePair r a A b B c₀ u E) (ci : Vec2) :
    actualMatrix pulses ci = FlatCovariance.columns (normalizedMatrix pulses) (columnScales pulses
        ci) := by
  ext i j
  exact congrFun ((pulses j).bounds.actualColumn_factorization (ci j) (pulses j).tangent) i

theorem columnScales_pos {r a A b B c₀ u E : ℝ}
    (pulses : SignedPulsePair r a A b B c₀ u E) {ci : Vec2} (hci : ∀ j, 0 < ci j)
    (j : Fin 2) : 0 < columnScales pulses ci j :=
  mul_pos (hci j) (pulses j).bounds.mass_pos

theorem normalizedMatrix_entry_error {r a A b B c₀ u E : ℝ}
    (pulses : SignedPulsePair r a A b B c₀ u E) (hE : 0 ≤ E) (i j : Fin 2) :
    |normalizedMatrix pulses i j - signedModel c₀ u i j| ≤
      (E + ((|c₀| + 1) * |u|) * concentrationConstant a A b B) / r := by
  have hi := (pulses j).bounds.normalizedColumn_error
    (pulses j).tangent_continuous hE (pulses j).tangent_model i
  unfold normalizedMatrix signedModel
  simpa only [signedSlopes_abs] using hi

theorem actualMatrix_positive_of_normalized {r a A b B c₀ u E : ℝ}
    (pulses : SignedPulsePair r a A b B c₀ u E) {ci : Vec2} (hci : ∀ j, 0 < ci j)
    (T : Vec2) (hdet : (normalizedMatrix pulses).det ≠ 0)
    (hw : ∀ i, 0 < SmoothCovariance.weights (normalizedMatrix pulses) T i) :
    (actualMatrix pulses ci).det ≠ 0 ∧
      (∀ i, 0 < SmoothCovariance.weights (actualMatrix pulses ci) T i) ∧
      (∀ i, 0 < SmoothCovariance.amplitudes (actualMatrix pulses ci) T i) := by
  have hs : ∀ j, 0 < columnScales pulses ci j := columnScales_pos pulses hci
  have hsn : ∀ j, columnScales pulses ci j ≠ 0 := fun j => (hs j).ne'
  have hT : FlatCovariance.scaledTarget 1 T = T := by
    ext i
    simp [FlatCovariance.scaledTarget]
  rw [actualMatrix_factorization]
  have hweight : ∀ i, 0 < SmoothCovariance.weights
      (FlatCovariance.columns (normalizedMatrix pulses) (columnScales pulses ci)) T i := by
    intro i
    rw [← hT, FlatCovariance.weights_columns _ _ _ _ hdet hsn]
    exact mul_pos (div_pos zero_lt_one (hs i)) (hw i)
  exact ⟨FlatCovariance.columns_det_ne_zero hdet hsn, hweight,
    fun i => Real.sqrt_pos.mpr (hweight i)⟩

/- This is the same entrywise norm used by SmoothCovariance's compact
perturbation theorem. -/
/-- Cache the standard `NormedAddCommGroup Mat2` instance to shorten typeclass synthesis. -/
local instance instPulseCovariance1 : NormedAddCommGroup Mat2 :=
  inferInstanceAs (NormedAddCommGroup (Fin 2 → Fin 2 → ℝ))

/-- Cache the standard `NormedSpace ℝ Mat2` instance to shorten typeclass synthesis. -/
local instance instPulseCovariance2 : NormedSpace ℝ Mat2 :=
  inferInstanceAs (NormedSpace ℝ (Fin 2 → Fin 2 → ℝ))

/-- A uniform slot threshold for the actual signed pulse pair over a compact
strict-cone family.  Its matrix approximation is a conclusion of the Gaussian
moment and pointwise tangent estimates in `TangentPulse`, not a hypothesis. -/
theorem compact_actual_positive_inverse
    {X : Type*} [TopologicalSpace X] {K : Set X} (hK : IsCompact K)
    {c₀ u : X → ℝ} {T : X → Vec2}
    (hmodel : ∀ i j, ContinuousOn (fun p => signedModel (c₀ p) (u p) i j) K)
    (hT : ∀ i, ContinuousOn (fun p => T p i) K)
    (hcone : ∀ p ∈ K, SmoothCovariance.StrictCone (signedModel (c₀ p) (u p)) (T p))
    {a A b B E C U : ℝ} (hE : 0 ≤ E) (hC : 0 ≤ C) (hU : 0 ≤ U)
    (hc₀ : ∀ p ∈ K, |c₀ p| ≤ C) (hu : ∀ p ∈ K, |u p| ≤ U) :
    ∃ R : ℝ, 1 ≤ R ∧ ∀ p ∈ K, ∀ r : ℝ, R ≤ r →
      ∀ pulses : SignedPulsePair r a A b B (c₀ p) (u p) E,
      ∀ ci : Vec2, (∀ j, 0 < ci j) →
        (actualMatrix pulses ci).det ≠ 0 ∧
        (∀ i, 0 < SmoothCovariance.weights (actualMatrix pulses ci) (T p) i) ∧
        (∀ i, 0 < SmoothCovariance.amplitudes (actualMatrix pulses ci) (T p) i) := by
  obtain ⟨ρ, hρ, hstable⟩ := SmoothCovariance.compact_family_perturbation_stability
    hK hmodel hT hcone
  let Q : ℝ := E + ((C + 1) * U) * |concentrationConstant a A b B|
  have hQ : 0 ≤ Q := by
    dsimp [Q]
    positivity
  refine ⟨max 1 (Q / ρ), le_max_left _ _, ?_⟩
  intro p hp r hr pulses ci hci
  have hr1 : 1 ≤ r := (le_max_left _ _).trans hr
  have hrp : 0 < r := lt_of_lt_of_le zero_lt_one hr1
  have hsmall : Q / r ≤ ρ := by
    apply (div_le_iff₀ hrp).mpr
    have hR : Q / ρ ≤ r := (le_max_right _ _).trans hr
    nlinarith [(div_le_iff₀ hρ).mp hR]
  have hentry (i j : Fin 2) :
      |normalizedMatrix pulses i j - signedModel (c₀ p) (u p) i j| ≤ ρ := by
    apply (normalizedMatrix_entry_error pulses hE i j).trans
    apply le_trans _ hsmall
    apply div_le_div_of_nonneg_right _ hrp.le
    dsimp [Q]
    apply add_le_add_right
    have hf : (|c₀ p| + 1) * |u p| ≤ (C + 1) * U :=
      mul_le_mul (add_le_add_left (hc₀ p hp) 1) (hu p hp)
        (abs_nonneg _) (by linarith)
    exact mul_le_mul hf (le_abs_self _)
      (pulses j).bounds.concentrationConstant_nonneg
      (mul_nonneg (by linarith) hU)
  have hdist : dist (normalizedMatrix pulses, T p) (signedModel (c₀ p) (u p), T p) ≤ ρ := by
    rw [dist_prod_same_right]
    apply (dist_pi_le_iff hρ.le).mpr
    intro i
    apply (dist_pi_le_iff hρ.le).mpr
    intro j
    simpa only [Real.dist_eq] using hentry i j
  obtain ⟨hd, hw, _⟩ := hstable p hp (normalizedMatrix pulses) (T p) hdist
  exact actualMatrix_positive_of_normalized pulses hci (T p) hd hw

/-- Scalar cone inequalities and continuity of the four scalar model data
suffice.  Compactness supplies both the uniform cone tolerance and the uniform
bounds on `c₀,u`, hence one slot threshold for every actual pulse pair. -/
theorem compact_actual_positive_inverse_of_scalar_cone
    {X : Type*} [TopologicalSpace X] {K : Set X} (hK : IsCompact K)
    {c₀ u m t : X → ℝ} (hc₀ : ContinuousOn c₀ K) (hu : ContinuousOn u K)
    (hm : ContinuousOn m K) (ht : ContinuousOn t K)
    (hc₀neg : ∀ p ∈ K, c₀ p < 0) (hupos : ∀ p ∈ K, 0 < u p)
    (hcone : ∀ p ∈ K, |Covariance.normalMagnitude (c₀ p) (u p) * t p| < u p * m p)
    {a A b B E : ℝ} (hE : 0 ≤ E) :
    ∃ R : ℝ, 1 ≤ R ∧ ∀ p ∈ K, ∀ r : ℝ, R ≤ r →
      ∀ pulses : SignedPulsePair r a A b B (c₀ p) (u p) E,
      ∀ ci : Vec2, (∀ j, 0 < ci j) →
        (actualMatrix pulses ci).det ≠ 0 ∧
        (∀ i, 0 < SmoothCovariance.weights (actualMatrix pulses ci) (Covariance.target (m p) (t p))
            i) ∧
        (∀ i, 0 < SmoothCovariance.amplitudes (actualMatrix pulses ci) (Covariance.target (m p) (t
            p)) i) := by
  obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn hc₀
  obtain ⟨U, hU⟩ := hK.exists_bound_of_continuousOn hu
  have htarget : ∀ i, ContinuousOn (fun p => Covariance.target (m p) (t p) i) K := by
    intro i
    fin_cases i
    · simpa [Covariance.target] using hm.fun_neg
    · simpa [Covariance.target] using ht
  apply compact_actual_positive_inverse hK (signedModel_continuousOn hc₀ hu) htarget
    (fun p hp => signedModel_strictCone (hc₀neg p hp) (hupos p hp) (hcone p hp)) hE
    (le_max_left 0 C) (le_max_left 0 U)
  · intro p hp
    exact (show |c₀ p| ≤ C by simpa only [Real.norm_eq_abs] using hC p hp).trans (le_max_right _ _)
  · intro p hp
    exact (show |u p| ≤ U by simpa only [Real.norm_eq_abs] using hU p hp).trans (le_max_right _ _)

end NavierStokes.PulseCovariance

end
end

end

@[expose] public section

noncomputable section

open Set Function MeasureTheory
open scoped BigOperators Topology ContDiff Interval

namespace NavierStokes.TorusAverages

open TorusInverse SmoothFourierData

local instance instTorusAverages1 : Fact ((0 : ℝ) < 1) := ⟨by norm_num⟩

local instance instTorusAverages2 : Measure.IsAddHaarMeasure torusMeasure := by
  unfold torusMeasure
  infer_instance

local instance planeVolumeHaar : Measure.IsAddHaarMeasure (volume : Measure Plane) := by
  change Measure.IsAddHaarMeasure ((volume : Measure ℝ).prod (volume : Measure ℝ))
  infer_instance

/-- Quotient point, given by `((z.1 : UnitAddCircle), (z.2 : UnitAddCircle))`. -/
noncomputable def quotientPoint (z : Plane) : Torus := ((z.1 : UnitAddCircle), (z.2 :
    UnitAddCircle))

/-- The manuscript's real covering matrix `[[3,1],[1,5]]`. -/
noncomputable def covering (z : Plane) : Plane := (3 * z.1 + z.2, z.1 + 5 * z.2)

/-- Torus covering, bundling `toFun`, `map_zero`, `map_add`. -/
noncomputable def torusCovering : Torus →+ Torus where
  toFun z := ((3 : ℕ) • z.1 + z.2, z.1 + (5 : ℕ) • z.2)
  map_zero' := by simp
  map_add' := by
    intro z w
    apply Prod.ext <;> simp only [Prod.fst_add, Prod.snd_add, nsmul_add] <;> abel

theorem torusCovering_continuous : Continuous torusCovering :=
  ((continuous_fst.nsmul 3).add continuous_snd).prodMk
    (continuous_fst.add (continuous_snd.nsmul 5))

theorem quotient_covering (z : Plane) :
    quotientPoint (covering z) = torusCovering (quotientPoint z) := by
  apply Prod.ext
  · change (((3 * z.1 + z.2 : ℝ) : UnitAddCircle)) =
      (3 : ℕ) • (z.1 : UnitAddCircle) + (z.2 : UnitAddCircle)
    rw [AddCircle.coe_add, ← AddCircle.coe_nsmul]
    simp only [nsmul_eq_mul, Nat.cast_ofNat]
  · change (((z.1 + 5 * z.2 : ℝ) : UnitAddCircle)) =
      (z.1 : UnitAddCircle) + (5 : ℕ) • (z.2 : UnitAddCircle)
    rw [AddCircle.coe_add, ← AddCircle.coe_nsmul]
    simp only [nsmul_eq_mul, Nat.cast_ofNat]

/-- Surjectivity is explicit: choose real lifts and apply the inverse matrix
`(1/14)[[5,-1],[-1,3]]` before projecting to the torus. -/
theorem torusCovering_surjective : Surjective torusCovering := by
  rintro ⟨x, y⟩
  refine Quotient.inductionOn' x (fun a => ?_)
  refine Quotient.inductionOn' y (fun b => ?_)
  refine ⟨quotientPoint ((5 * a - b) / 14, (-a + 3 * b) / 14), ?_⟩
  rw [← quotient_covering]
  have heq : covering ((5 * a - b) / 14, (-a + 3 * b) / 14) = (a, b) := by
    apply Prod.ext <;> dsimp [covering] <;> ring
  rw [heq]
  rfl

theorem torusCovering_measurePreserving :
    MeasurePreserving torusCovering torusMeasure torusMeasure :=
  torusCovering.measurePreserving torusCovering_continuous torusCovering_surjective rfl

theorem quotient_covering_iterate (n : ℕ) (z : Plane) :
    quotientPoint (covering^[n] z) = torusCovering^[n] (quotientPoint z) := by
  induction n with
  | zero => rfl
  | succ n ih =>
      simp only [Function.iterate_succ_apply', quotient_covering, ih]

theorem covering_continuous : Continuous covering :=
  ((continuous_const.mul continuous_fst).add continuous_snd).prodMk
    (continuous_fst.add (continuous_const.mul continuous_snd))

/-- Every covering power preserves the actual Haar integral. Continuity is
already sufficient; no Fourier-decay premise or assumed average identity occurs. -/
theorem integral_torusCovering_iterate {V : Type*} [NormedAddCommGroup V]
    [NormedSpace ℝ V] (f : Torus → V) (hf : Continuous f) (n : ℕ) :
    (∫ z, f (torusCovering^[n] z) ∂torusMeasure) = ∫ z, f z ∂torusMeasure := by
  have hp := torusCovering_measurePreserving.iterate n
  rw [← integral_map hp.measurable.aemeasurable hf.aestronglyMeasurable, hp.map_eq]

/-- Square average, given by `∫ y in (0 : ℝ)..1, ∫ x in (0 : ℝ)..1, f (x, y)`. -/
noncomputable def squareAverage {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (f : Plane → V) : V := ∫ y in (0 : ℝ)..1, ∫ x in (0 : ℝ)..1, f (x, y)

theorem squareAverage_torusLift (f : C(Torus, ℂ)) :
    squareAverage (torusLift f) = ∫ z, f z ∂torusMeasure := by
  rw [squareAverage, ← coefficient_zero_eq_integral, coefficient_zero_eq_mean]

/-- Unit-square version for a genuine continuous unit-periodic complex field. -/
theorem squareAverage_covering_iterate {f : Plane → ℂ}
    (hf : Continuous f) (hp : UnitPeriodic f) (n : ℕ) :
    squareAverage (fun z => f (covering^[n] z)) = squareAverage f := by
  let g : C(Torus, ℂ) := descendContinuous f hf hp
  let h : C(Torus, ℂ) :=
    ⟨fun z => g (torusCovering^[n] z), g.continuous.comp (torusCovering_continuous.iterate n)⟩
  have heq : torusLift h = (fun z => f (covering^[n] z)) := by
    funext z
    change g (torusCovering^[n] (quotientPoint z)) = f (covering^[n] z)
    rw [← quotient_covering_iterate]
    rfl
  have hg : squareAverage f = ∫ z, g z ∂torusMeasure := squareAverage_torusLift g
  rw [← heq, squareAverage_torusLift]
  exact (integral_torusCovering_iterate g g.continuous n).trans hg.symm

theorem squareAverage_covering_iterate_smooth {f : Plane → ℂ}
    (hf : ContDiff ℝ ∞ f) (hp : UnitPeriodic f) (n : ℕ) :
    squareAverage (fun z => f (covering^[n] z)) = squareAverage f :=
  squareAverage_covering_iterate hf.continuous hp n

/-- Real-valued form, with the same actual unit-square integral. -/
theorem squareAverage_covering_iterate_real {f : Plane → ℝ}
    (hf : Continuous f)
    (hp : ∀ z : Plane, ∀ k : Frequency, f (z + ((k.1 : ℝ), (k.2 : ℝ))) = f z)
    (n : ℕ) : squareAverage (fun z => f (covering^[n] z)) = squareAverage f := by
  have hp' : UnitPeriodic (fun z => (f z : ℂ)) := fun z k => congrArg Complex.ofReal (hp z k)
  have h := squareAverage_covering_iterate (Complex.continuous_ofReal.comp hf) hp' n
  apply Complex.ofReal_injective
  simpa only [squareAverage, Function.comp_def, ← intervalIntegral.integral_ofReal] using h

/-! ## Lattice periodization and its actual integral -/

/-- Lattice point, given by `((k.1 : ℝ), (k.2 : ℝ))`. -/
noncomputable def latticePoint (k : Frequency) : Plane := ((k.1 : ℝ), (k.2 : ℝ))

theorem latticePoint_add (k l : Frequency) :
    latticePoint (k + l) = latticePoint k + latticePoint l := by
  ext <;> simp [latticePoint]

theorem latticePoint_injective : Injective latticePoint := by
  intro k l h
  apply Prod.ext
  · have h1 := congrArg Prod.fst h
    change (k.1 : ℝ) = (l.1 : ℝ) at h1
    exact_mod_cast h1
  · have h2 := congrArg Prod.snd h
    change (k.2 : ℝ) = (l.2 : ℝ) at h2
    exact_mod_cast h2

theorem quotientPoint_lattice_add (k : Frequency) (z : Plane) :
    quotientPoint (latticePoint k + z) = quotientPoint z := by
  simp [quotientPoint, latticePoint, circle_int_eq_zero]

/-- Each translated half-open unit square is an injective coordinate chart
for the quotient to the torus. -/
theorem quotientPoint_injOn_square (a : Plane) :
    InjOn quotientPoint (Ico a.1 (a.1 + 1) ×ˢ Ico a.2 (a.2 + 1)) := by
  intro x hx y hy hxy
  apply Prod.ext
  · exact (AddCircle.coe_eq_coe_iff_of_mem_Ico hx.1 hy.1).mp (congrArg Prod.fst hxy)
  · exact (AddCircle.coe_eq_coe_iff_of_mem_Ico hx.2 hy.2).mp (congrArg Prod.snd hxy)

/-- A concrete smallness criterion for the native parallelogram. The product
norm on `Plane` is the maximum norm, so `ball 0 r` is the open native square. -/
theorem quotientPoint_injOn_small_chart (L : Plane ≃L[ℝ] Plane) (center : Plane)
    (r : ℝ) (hr : ‖(L : Plane →L[ℝ] Plane)‖ * r < 1 / 2) :
    InjOn quotientPoint ((fun z => center + L z) '' Metric.ball (0 : Plane) r) := by
  apply (quotientPoint_injOn_square (center - (1 / 2, 1 / 2))).mono
  rintro _ ⟨z, hz, rfl⟩
  have hz' : ‖z‖ < r := by simpa using hz
  have hnorm : ‖L z‖ < 1 / 2 :=
    ((L : Plane →L[ℝ] Plane).le_opNorm z).trans_lt
      ((mul_le_mul_of_nonneg_left hz'.le (norm_nonneg _)).trans_lt hr)
  have h1 : |(L z).1| < 1 / 2 := (norm_fst_le (L z)).trans_lt hnorm
  have h2 : |(L z).2| < 1 / 2 := (norm_snd_le (L z)).trans_lt hnorm
  change (center.1 + (L z).1 ∈ Ico (center.1 - 1 / 2) (center.1 - 1 / 2 + 1)) ∧
    (center.2 + (L z).2 ∈ Ico (center.2 - 1 / 2) (center.2 - 1 / 2 + 1))
  constructor <;> constructor
  · linarith [(abs_lt.mp h1).1]
  · linarith [(abs_lt.mp h1).2]
  · linarith [(abs_lt.mp h2).1]
  · linarith [(abs_lt.mp h2).2]

/-- A positive injective native radius always exists; this proof supplies the
explicit radius `1 / (4 * (‖L‖ + 1))`. -/
theorem exists_injective_native_radius (L : Plane ≃L[ℝ] Plane) (center : Plane) :
    ∃ r : ℝ, 0 < r ∧
      InjOn quotientPoint ((fun z => center + L z) '' Metric.ball (0 : Plane) r) := by
  let N : ℝ := ‖(L : Plane →L[ℝ] Plane)‖
  have hN : 0 ≤ N := norm_nonneg _
  have hpos : 0 < 4 * (N + 1) := by positivity
  refine ⟨1 / (4 * (N + 1)), by positivity,
    quotientPoint_injOn_small_chart L center _ ?_⟩
  change N * (1 / (4 * (N + 1))) < 1 / 2
  rw [mul_one_div, div_lt_iff₀ hpos]
  nlinarith

theorem latticeTranslate_unique {s : Set Plane} (hs : InjOn quotientPoint s)
    {z : Plane} {k l : Frequency} (hk : latticePoint k + z ∈ s)
    (hl : latticePoint l + z ∈ s) : k = l := by
  apply latticePoint_injective
  apply add_right_cancel (b := z)
  exact hs hk hl (by rw [quotientPoint_lattice_add, quotientPoint_lattice_add])

/-- The `AddAction Frequency Plane` structure used in torus averages. -/
local instance latticeAddAction : AddAction Frequency Plane where
  vadd k z := latticePoint k + z
  zero_vadd z := by
    change latticePoint 0 + z = z
    simp [latticePoint]
  add_vadd k l z := by
    change latticePoint (k + l) + z = latticePoint k + (latticePoint l + z)
    simp [latticePoint, Prod.add_def, add_assoc]

local instance instTorusAverages3 : MeasurableVAdd Frequency Plane where
  measurable_const_vadd _ := measurable_const.add measurable_id
  measurable_vadd_const _ := measurable_of_countable _

local instance instTorusAverages4 : VAddInvariantMeasure Frequency Plane (volume : Measure Plane)
    where
  measure_preimage_vadd k s _ :=
    measure_preimage_add (volume : Measure Plane) (latticePoint k) s

/-- Fundamental square, given by `Ico (0 : ℝ) 1 ×ˢ Ico (0 : ℝ) 1`. -/
noncomputable def fundamentalSquare : Set Plane := Ico (0 : ℝ) 1 ×ˢ Ico (0 : ℝ) 1

/-- The half-open unit square is proved to tile the plane, using integer floors. -/
theorem fundamentalSquare_isAddFundamentalDomain :
    IsAddFundamentalDomain Frequency fundamentalSquare (volume : Measure Plane) := by
  apply IsAddFundamentalDomain.mk'
    ((measurableSet_Ico.prod measurableSet_Ico).nullMeasurableSet)
  intro z
  refine ⟨(-⌊z.1⌋, -⌊z.2⌋), ?_, ?_⟩
  · change ((-⌊z.1⌋ : ℤ) : ℝ) + z.1 ∈ Ico (0 : ℝ) 1 ∧
      ((-⌊z.2⌋ : ℤ) : ℝ) + z.2 ∈ Ico (0 : ℝ) 1
    simpa only [Int.cast_neg, Int.fract, sub_eq_add_neg, add_comm]
      using And.intro ⟨Int.fract_nonneg z.1, Int.fract_lt_one z.1⟩
        ⟨Int.fract_nonneg z.2, Int.fract_lt_one z.2⟩
  · intro k hk
    have h1 : ⌊(k.1 : ℝ) + z.1⌋ = 0 := Int.floor_eq_zero_iff.mpr hk.1
    have h2 : ⌊(k.2 : ℝ) + z.2⌋ = 0 := Int.floor_eq_zero_iff.mpr hk.2
    rw [Int.floor_intCast_add] at h1 h2
    apply Prod.ext <;> dsimp
    · omega
    · omega

/-- The periodization is the actual sum over integer translates. -/
noncomputable def periodize {V : Type*} [NormedAddCommGroup V] (f : Plane → V)
    (z : Plane) : V := ∑' k : Frequency, f (latticePoint k + z)

/-- A compactly supported field has only finitely many active translates on
every bounded set. This supplies an actual local finite-sum formula. -/
theorem finite_translates_on_ball {V : Type*} [Zero V] {f : Plane → V}
    (hf : HasCompactSupport f) (R : ℝ) :
    ∃ s : Finset Frequency, ∀ z : Plane, ‖z‖ ≤ R →
      ∀ k : Frequency, k ∉ s → f (latticePoint k + z) = 0 := by
  classical
  obtain ⟨C, hC⟩ := hf.isCompact.isBounded.exists_norm_le
  let N : ℤ := ⌈C + R⌉
  refine ⟨(Finset.Icc (-N) N).product (Finset.Icc (-N) N), ?_⟩
  intro z hz k hk
  by_contra hne
  have hnorm : ‖latticePoint k‖ ≤ C + R := by
    calc
      ‖latticePoint k‖ = ‖(latticePoint k + z) - z‖ := by rw [add_sub_cancel_right]
      _ ≤ ‖latticePoint k + z‖ + ‖z‖ := norm_sub_le _ _
      _ ≤ C + R := add_le_add (hC _ (subset_tsupport f hne)) hz
  have hn : C + R ≤ (N : ℝ) := Int.le_ceil _
  have hk1 : |(k.1 : ℝ)| ≤ (N : ℝ) := (norm_fst_le (latticePoint k)).trans (hnorm.trans hn)
  have hk2 : |(k.2 : ℝ)| ≤ (N : ℝ) := (norm_snd_le (latticePoint k)).trans (hnorm.trans hn)
  have hm : k ∈ (Finset.Icc (-N) N).product (Finset.Icc (-N) N) := by
    apply Finset.mem_product.mpr
    constructor
    · apply Finset.mem_Icc.mpr
      constructor
      · exact_mod_cast (abs_le.mp hk1).1
      · exact_mod_cast (abs_le.mp hk1).2
    · apply Finset.mem_Icc.mpr
      constructor
      · exact_mod_cast (abs_le.mp hk2).1
      · exact_mod_cast (abs_le.mp hk2).2
  exact hk hm

theorem periodize_eventually_eq_sum {V : Type*} [NormedAddCommGroup V] {f : Plane → V}
    (hf : HasCompactSupport f) (z : Plane) :
    ∃ s : Finset Frequency,
      periodize f =ᶠ[𝓝 z] fun w => ∑ k ∈ s, f (latticePoint k + w) := by
  obtain ⟨s, hs⟩ := finite_translates_on_ball hf (‖z‖ + 1)
  refine ⟨s, ?_⟩
  have hnear : {w : Plane | ‖w‖ < ‖z‖ + 1} ∈ 𝓝 z :=
    (isOpen_lt continuous_norm continuous_const).mem_nhds (by simp)
  filter_upwards [hnear] with w hw
  exact tsum_eq_sum (hs w hw.le)

theorem periodize_continuous {V : Type*} [NormedAddCommGroup V] {f : Plane → V}
    (hf : Continuous f) (hcf : HasCompactSupport f) : Continuous (periodize f) := by
  rw [continuous_iff_continuousAt]
  intro z
  obtain ⟨s, hs⟩ := periodize_eventually_eq_sum hcf z
  have hsum : Continuous (fun w => ∑ k ∈ s, f (latticePoint k + w)) :=
    continuous_finsetSum _ (fun k _ => hf.comp (continuous_const.add continuous_id))
  exact hsum.continuousAt.congr_of_eventuallyEq hs

theorem periodize_contDiff {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    {f : Plane → V} (hf : ContDiff ℝ ∞ f) (hcf : HasCompactSupport f) :
    ContDiff ℝ ∞ (periodize f) := by
  rw [contDiff_iff_contDiffAt]
  intro z
  obtain ⟨s, hs⟩ := periodize_eventually_eq_sum hcf z
  have hsum : ContDiff ℝ ∞ (fun w => ∑ k ∈ s, f (latticePoint k + w)) :=
    ContDiff.sum (fun k _ => hf.comp (contDiff_const.add contDiff_id))
  exact hsum.contDiffAt.congr_of_eventuallyEq hs

theorem periodize_periodic {V : Type*} [NormedAddCommGroup V]
    (f : Plane → V) (z : Plane) (k : Frequency) :
    periodize f (z + latticePoint k) = periodize f z := by
  unfold periodize
  calc
    (∑' l : Frequency, f (latticePoint l + (z + latticePoint k))) =
        ∑' l : Frequency, f (latticePoint (l + k) + z) := by
      apply tsum_congr
      intro l
      rw [latticePoint_add]
      congr 1
      abel
    _ = ∑' l : Frequency, f (latticePoint l + z) :=
      (Equiv.addRight k).tsum_eq (fun l : Frequency => f (latticePoint l + z))

/-- On an injective slot, a periodization equals the one native copy present
there. The result includes the case that the native value itself is zero. -/
theorem periodize_eq_native_copy {V : Type*} [NormedAddCommGroup V]
    {s : Set Plane} (hs : InjOn quotientPoint s) {f : Plane → V}
    (hf : Function.support f ⊆ s) {z : Plane} {k : Frequency}
    (hk : latticePoint k + z ∈ s) : periodize f z = f (latticePoint k + z) := by
  apply tsum_eq_single k
  intro l hl
  by_contra hne
  exact hl (latticeTranslate_unique hs (hf hne) hk)

/-- Products of actual periodized fields have no cross-copy terms when both
native fields are supported in the same injective slot. -/
theorem periodize_mul_of_injective_support {s : Set Plane} (hs : InjOn quotientPoint s)
    {f g : Plane → ℝ} (hf : Function.support f ⊆ s) (hg : Function.support g ⊆ s)
    (z : Plane) : periodize f z * periodize g z = periodize (fun w => f w * g w) z := by
  have hfg : Function.support (fun w => f w * g w) ⊆ s := by
    intro w hw
    exact hf (mul_ne_zero_iff.mp hw).1
  by_cases h : ∃ k : Frequency, f (latticePoint k + z) ≠ 0
  · obtain ⟨k, hk⟩ := h
    rw [periodize_eq_native_copy hs hf (hf hk),
      periodize_eq_native_copy hs hg (hf hk),
      periodize_eq_native_copy hs hfg (hf hk)]
  · have hzero : ∀ k : Frequency, f (latticePoint k + z) = 0 := by
      simpa only [not_exists, not_not] using h
    simp [periodize, hzero]

/-- The set-integral and iterated-integral descriptions of the unit-square
average agree. Endpoint choices have zero Lebesgue measure. -/
theorem squareAverage_eq_setIntegral {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    {f : Plane → V} (hf : Continuous f) :
    squareAverage f = ∫ z in fundamentalSquare, f z := by
  have hi : Integrable f ((volume.restrict (Ico (0 : ℝ) 1)).prod
      (volume.restrict (Ico (0 : ℝ) 1))) := by
    rw [Measure.prod_restrict]
    exact (hf.continuousOn.integrableOn_compact
      (isCompact_Icc.prod isCompact_Icc)).mono_set
      (Set.prod_mono Ico_subset_Icc_self Ico_subset_Icc_self)
  have h := integral_prod_symm f hi
  rw [Measure.prod_restrict] at h
  change (∫ z in fundamentalSquare, f z) =
    ∫ y in Ico (0 : ℝ) 1, ∫ x in Ico (0 : ℝ) 1, f (x, y) at h
  simp only [restrict_Ico_eq_restrict_Ioc] at h
  simp only [squareAverage, intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1)]
  exact h.symm

/-- Every integrable field, in particular a smooth compactly supported slot,
has exactly its plane integral as the integral of its lattice periodization. -/
theorem integral_periodize {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    {f : Plane → V} (hf : Integrable f) :
    (∫ z in fundamentalSquare, periodize f z) = ∫ z, f z := by
  have hm (k : Frequency) :
      AEStronglyMeasurable (fun z => f (latticePoint k + z))
        (volume.restrict fundamentalSquare) :=
    (hf.aestronglyMeasurable.comp_measurePreserving
      (measurePreserving_add_left (volume : Measure Plane) (latticePoint k))).restrict
  have hn : (∑' k : Frequency,
      ∫⁻ z in fundamentalSquare, ‖f (latticePoint k + z)‖ₑ) ≠ ⊤ := by
    change (∑' k : Frequency, ∫⁻ z in fundamentalSquare, ‖f (k +ᵥ z)‖ₑ) ≠ ⊤
    rw [← fundamentalSquare_isAddFundamentalDomain.lintegral_eq_tsum''
      (fun z => ‖f z‖ₑ)]
    exact hf.hasFiniteIntegral.ne
  change (∫ z in fundamentalSquare, ∑' k : Frequency, f (latticePoint k + z)) = _
  rw [integral_tsum hm hn]
  exact (fundamentalSquare_isAddFundamentalDomain.integral_eq_tsum'' f hf).symm

theorem squareAverage_periodize {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    {f : Plane → V} (hf : Continuous f) (hcf : HasCompactSupport f) :
    squareAverage (periodize f) = ∫ z, f z := by
  rw [squareAverage_eq_setIntegral (periodize_continuous hf hcf),
    integral_periodize (hf.integrable_of_hasCompactSupport hcf)]

theorem squareAverage_periodize_covering {f : Plane → ℂ}
    (hf : Continuous f) (hcf : HasCompactSupport f) (n : ℕ) :
    squareAverage (fun z => periodize f (covering^[n] z)) = ∫ z, f z := by
  rw [squareAverage_covering_iterate (periodize_continuous hf hcf)
    (periodize_periodic f) n, squareAverage_periodize hf hcf]

theorem squareAverage_periodize_covering_real {f : Plane → ℝ}
    (hf : Continuous f) (hcf : HasCompactSupport f) (n : ℕ) :
    squareAverage (fun z => periodize f (covering^[n] z)) = ∫ z, f z := by
  rw [squareAverage_covering_iterate_real (periodize_continuous hf hcf)
    (periodize_periodic f) n, squareAverage_periodize hf hcf]

/-! ## Native coordinates and the determinant prefactor -/

/-- A native field placed at `center` in the linear coordinate chart `L`. -/
noncomputable def nativeField {V : Type*} (L : Plane ≃L[ℝ] Plane) (center : Plane)
    (f : Plane → V) (z : Plane) : V := f (L.symm (z - center))

theorem nativeField_continuous {V : Type*} [TopologicalSpace V]
    (L : Plane ≃L[ℝ] Plane) (center : Plane) {f : Plane → V} (hf : Continuous f) :
    Continuous (nativeField L center f) :=
  hf.comp (L.symm.continuous.comp (continuous_id.sub continuous_const))

theorem nativeField_contDiff {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (L : Plane ≃L[ℝ] Plane) (center : Plane) {f : Plane → V} (hf : ContDiff ℝ ∞ f) :
    ContDiff ℝ ∞ (nativeField L center f) :=
  hf.comp (L.symm.contDiff.comp (contDiff_id.sub contDiff_const))

theorem nativeField_hasCompactSupport {V : Type*} [Zero V]
    (L : Plane ≃L[ℝ] Plane) (center : Plane) {f : Plane → V} (hf : HasCompactSupport f) :
    HasCompactSupport (nativeField L center f) := by
  exact (hf.comp_homeomorph L.symm.toHomeomorph).comp_homeomorph
    (Homeomorph.subRight center)

/-- Actual linear change of variables, including the absolute determinant. -/
theorem integral_nativeField {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (L : Plane ≃L[ℝ] Plane) (center : Plane) (f : Plane → V) :
    (∫ z, nativeField L center f z) =
      |LinearMap.det (L : Plane →ₗ[ℝ] Plane)| • ∫ z, f z := by
  unfold nativeField
  rw [integral_sub_right_eq_self (fun z => f (L.symm z)) center]
  change (∫ x, f (L.symm.toHomeomorph.toMeasurableEquiv x)) = _
  rw [← integral_map_equiv (μ := (volume : Measure Plane)) L.symm.toHomeomorph.toMeasurableEquiv f]
  have hmap : Measure.map L.symm (volume : Measure Plane) =
      ENNReal.ofReal |(LinearMap.det (L.symm : Plane →ₗ[ℝ] Plane))⁻¹| • volume :=
    Measure.map_linearMap_addHaar_eq_smul_addHaar (volume : Measure Plane)
      (LinearEquiv.isUnit_det' L.symm.toLinearEquiv).ne_zero
  change (∫ y, f y ∂Measure.map L.symm volume) = _
  rw [hmap, integral_smul_measure]
  have hd : LinearMap.det (L.symm : Plane →ₗ[ℝ] Plane) =
      (LinearMap.det (L : Plane →ₗ[ℝ] Plane))⁻¹ :=
    LinearEquiv.det_coe_symm L.toLinearEquiv
  rw [hd, inv_inv, ENNReal.toReal_ofReal (abs_nonneg _)]

/-- The native compact-slot average is obtained from periodization and a
Jacobian theorem, with no assumed averaging identity. -/
theorem integral_periodize_nativeField {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (L : Plane ≃L[ℝ] Plane) (center : Plane) {f : Plane → V}
    (hf : Continuous f) (hcf : HasCompactSupport f) :
    (∫ z in fundamentalSquare, periodize (nativeField L center f) z) =
      |LinearMap.det (L : Plane →ₗ[ℝ] Plane)| • ∫ z, f z := by
  rw [integral_periodize ((nativeField_continuous L center hf).integrable_of_hasCompactSupport
    (nativeField_hasCompactSupport L center hcf)), integral_nativeField]

/-- The linear map with the radial and longitudinal vectors as its columns. -/
noncomputable def slotLinearMap (vr vt : Plane) : Plane →ₗ[ℝ] Plane :=
  Matrix.toLin (Module.Basis.finTwoProd ℝ) (Module.Basis.finTwoProd ℝ)
    !![vr.1, vt.1; vr.2, vt.2]

theorem slotLinearMap_apply (vr vt z : Plane) :
    slotLinearMap vr vt z = z.1 • vr + z.2 • vt := by
  rw [slotLinearMap, Matrix.toLin_finTwoProd_apply]
  ext <;> simp only [Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd, smul_eq_mul] <;> ring

theorem det_slotLinearMap (vr vt : Plane) :
    LinearMap.det (slotLinearMap vr vt) = vr.1 * vt.2 - vr.2 * vt.1 := by
  simp [slotLinearMap, LinearMap.det_toLin, Matrix.det_fin_two, mul_comm]

/-- The genuine nondegenerate native chart. -/
noncomputable def slotChart (vr vt : Plane) (hdet : vr.1 * vt.2 - vr.2 * vt.1 ≠ 0) :
    Plane ≃L[ℝ] Plane :=
  ((slotLinearMap vr vt).equivOfDetNeZero ((det_slotLinearMap vr vt).trans_ne
      hdet)).toContinuousLinearEquiv

theorem slotChart_apply (vr vt : Plane) (hdet : vr.1 * vt.2 - vr.2 * vt.1 ≠ 0) (z : Plane) :
    slotChart vr vt hdet z = z.1 • vr + z.2 • vt := slotLinearMap_apply vr vt z

theorem det_slotChart (vr vt : Plane) (hdet : vr.1 * vt.2 - vr.2 * vt.1 ≠ 0) :
    LinearMap.det (slotChart vr vt hdet : Plane →ₗ[ℝ] Plane) =
      vr.1 * vt.2 - vr.2 * vt.1 := det_slotLinearMap vr vt

theorem integral_periodize_slot {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (vr vt center : Plane) (hdet : vr.1 * vt.2 - vr.2 * vt.1 ≠ 0) {f : Plane → V}
    (hf : Continuous f) (hcf : HasCompactSupport f) :
    (∫ z in fundamentalSquare, periodize (nativeField (slotChart vr vt hdet) center f) z) =
      |vr.1 * vt.2 - vr.2 * vt.1| • ∫ z, f z := by
  rw [integral_periodize_nativeField _ center hf hcf, det_slotChart]

/-- Rescaling the transverse coordinate by `ci`. -/
noncomputable def transverseChart (ci : ℝ) (hci : ci ≠ 0) : Plane ≃L[ℝ] Plane :=
  slotChart (1, 0) (0, ci) (by simpa using hci)

theorem transverseChart_apply (ci : ℝ) (hci : ci ≠ 0) (z : Plane) :
    transverseChart ci hci z = (z.1, ci * z.2) := by
  rw [transverseChart, slotChart_apply]
  ext <;> simp [mul_comm]

theorem transverseChart_symm_apply (ci : ℝ) (hci : ci ≠ 0) (z : Plane) :
    (transverseChart ci hci).symm z = (z.1, z.2 / ci) := by
  apply (transverseChart ci hci).injective
  rw [ContinuousLinearEquiv.apply_symm_apply, transverseChart_apply]
  ext <;> simp [hci, mul_div_cancel₀]

theorem det_transverseChart (ci : ℝ) (hci : ci ≠ 0) :
    LinearMap.det (transverseChart ci hci : Plane →ₗ[ℝ] Plane) = ci := by
  rw [transverseChart, det_slotChart]
  simp

/-- `η = ci * v - r0`, written as the field in the native `(ξ,η)` coordinates. -/
noncomputable def transverseStretch {V : Type*} (ci r0 : ℝ) (f : Plane → V) (z : Plane) : V :=
  f (z.1, (z.2 + r0) / ci)

theorem transverseStretch_eq_nativeField {V : Type*} (ci r0 : ℝ) (hci : ci ≠ 0)
    (f : Plane → V) :
    transverseStretch ci r0 f = nativeField (transverseChart ci hci) (0, -r0) f := by
  funext z
  simp [transverseStretch, nativeField, transverseChart_symm_apply]

theorem transverseStretch_continuous {V : Type*} [TopologicalSpace V] (ci r0 : ℝ)
    (hci : ci ≠ 0) {f : Plane → V} (hf : Continuous f) :
    Continuous (transverseStretch ci r0 f) := by
  rw [transverseStretch_eq_nativeField ci r0 hci]
  exact nativeField_continuous _ _ hf

theorem transverseStretch_contDiff {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (ci r0 : ℝ) (hci : ci ≠ 0) {f : Plane → V} (hf : ContDiff ℝ ∞ f) :
    ContDiff ℝ ∞ (transverseStretch ci r0 f) := by
  rw [transverseStretch_eq_nativeField ci r0 hci]
  exact nativeField_contDiff _ _ hf

theorem transverseStretch_hasCompactSupport {V : Type*} [Zero V] (ci r0 : ℝ)
    (hci : ci ≠ 0) {f : Plane → V} (hf : HasCompactSupport f) :
    HasCompactSupport (transverseStretch ci r0 f) := by
  rw [transverseStretch_eq_nativeField ci r0 hci]
  exact nativeField_hasCompactSupport _ _ hf

theorem integral_transverseStretch {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (ci r0 : ℝ) (hci : ci ≠ 0) (f : Plane → V) :
    (∫ z, transverseStretch ci r0 f z) = |ci| • ∫ z, f z := by
  rw [transverseStretch_eq_nativeField ci r0 hci, integral_nativeField, det_transverseChart]

/-- The actual native-slot average after every integer covering power. The
transverse-coordinate Jacobian is positive `ci`, not an assumed model scale. -/
theorem squareAverage_covered_nativeSlot (vr vt center : Plane)
    (hdet : vr.1 * vt.2 - vr.2 * vt.1 ≠ 0) (ci r0 : ℝ) (hci : 0 < ci)
    {f : Plane → ℝ} (hf : Continuous f) (hcf : HasCompactSupport f) (n : ℕ) :
    squareAverage (fun z => periodize
      (nativeField (slotChart vr vt hdet) center (transverseStretch ci r0 f))
      (covering^[n] z)) =
      |vr.1 * vt.2 - vr.2 * vt.1| * ci * ∫ z, f z := by
  rw [squareAverage_periodize_covering_real
    (nativeField_continuous _ _ (transverseStretch_continuous ci r0 hci.ne' hf))
    (nativeField_hasCompactSupport _ _ (transverseStretch_hasCompactSupport ci r0 hci.ne' hcf)) n,
    integral_nativeField, det_slotChart, integral_transverseStretch ci r0 hci.ne',
    abs_of_pos hci, smul_eq_mul, smul_eq_mul, mul_assoc]

theorem productProfile_hasCompactSupport {a b : ℝ → ℝ}
    (ha : HasCompactSupport a) (hb : HasCompactSupport b) :
    HasCompactSupport (fun z : Plane => a z.1 * b z.2) := by
  apply HasCompactSupport.of_support_subset_isCompact (ha.isCompact.prod hb.isCompact)
  intro z hz
  exact ⟨subset_tsupport a (mul_ne_zero_iff.mp hz).1,
    subset_tsupport b (mul_ne_zero_iff.mp hz).2⟩

/-- Separation of the actual longitudinal and transverse integrals. -/
theorem squareAverage_covered_product (vr vt center : Plane)
    (hdet : vr.1 * vt.2 - vr.2 * vt.1 ≠ 0) (ci r0 : ℝ) (hci : 0 < ci)
    {a b : ℝ → ℝ} (ha : Continuous a) (hb : Continuous b)
    (hca : HasCompactSupport a) (hcb : HasCompactSupport b) (n : ℕ) :
    squareAverage (fun z => periodize
      (nativeField (slotChart vr vt hdet) center
        (transverseStretch ci r0 (fun w : Plane => a w.1 * b w.2)))
      (covering^[n] z)) =
      |vr.1 * vt.2 - vr.2 * vt.1| * (∫ ξ : ℝ, a ξ) * (ci * ∫ v : ℝ, b v) := by
  rw [squareAverage_covered_nativeSlot vr vt center hdet ci r0 hci
    (f := fun w : Plane => a w.1 * b w.2)
    ((ha.comp continuous_fst).mul (hb.comp continuous_snd))
    (productProfile_hasCompactSupport hca hcb) n]
  change |vr.1 * vt.2 - vr.2 * vt.1| * ci *
    (∫ z, a z.1 * b z.2 ∂(volume : Measure ℝ).prod (volume : Measure ℝ)) = _
  rw [integral_prod_mul]
  ring

/-- The native covariance coefficient before angular averaging. -/
noncomputable def pulseProfile (χ ψ x : ℝ → ℝ) (t : ℝ → PulseCovariance.Vec2)
    (i : Fin 2) (z : Plane) : ℝ := χ z.1 ^ 2 * (ψ z.2 ^ 2 * x z.2 * t z.2 i)

theorem squareAverage_covered_pulseColumn (vr vt center : Plane)
    (hdet : vr.1 * vt.2 - vr.2 * vt.1 ≠ 0) (ci r0 : ℝ) (hci : 0 < ci)
    {χ ψ x : ℝ → ℝ} {t : ℝ → PulseCovariance.Vec2}
    (hχ : Continuous χ) (hψ : Continuous ψ) (hx : Continuous x) (ht : Continuous t)
    (hcχ : HasCompactSupport χ) (hcψ : HasCompactSupport ψ) (i : Fin 2) (n : ℕ) :
    squareAverage (fun z => periodize
      (nativeField (slotChart vr vt hdet) center
        (transverseStretch ci r0 (pulseProfile χ ψ x t i)))
      (covering^[n] z)) =
      |vr.1 * vt.2 - vr.2 * vt.1| * (∫ ξ : ℝ, χ ξ ^ 2) *
        PulseCovariance.actualColumn ci ψ x t i := by
  have hca : HasCompactSupport (fun ξ => χ ξ ^ 2) := by
    apply hcχ.mono
    intro ξ hξ heq
    exact hξ (by simp [heq])
  have hcb : HasCompactSupport (fun v => ψ v ^ 2 * x v * t v i) := by
    apply hcψ.mono
    intro v hv heq
    exact hv (by simp [heq])
  exact squareAverage_covered_product vr vt center hdet ci r0 hci
    (hχ.pow 2) (((hψ.pow 2).mul hx).mul ((continuous_apply i).comp ht)) hca hcb n

/-! ## The real-cosine factor in Lemma 8.7 -/

/-- An arbitrary phase shift does not change the average of a nonzero integer
angular harmonic squared. -/
theorem angularMean_cos_sq_harmonic (j : ℤ) (hj : j ≠ 0) (phase : ℝ) :
    SmoothLoop.angularMean (fun θ => Real.cos ((j : ℝ) * θ + phase) ^ 2) = 1 / 2 := by
  have hjR : (j : ℝ) ≠ 0 := by exact_mod_cast hj
  have hs : Real.sin ((j : ℝ) * (2 * Real.pi) + phase) = Real.sin phase := by
    rw [add_comm]
    exact Real.sin_add_int_mul_two_pi phase j
  have hc : Real.cos ((j : ℝ) * (2 * Real.pi) + phase) = Real.cos phase := by
    rw [add_comm]
    exact Real.cos_add_int_mul_two_pi phase j
  unfold SmoothLoop.angularMean
  rw [intervalIntegral.integral_comp_mul_add (fun θ => Real.cos θ ^ 2) hjR phase,
    integral_cos_sq]
  simp only [mul_zero, zero_add, hs, hc, smul_eq_mul]
  field_simp [hjR, Real.pi_ne_zero]; ring

theorem squareAverage_const_mul (c : ℝ) (f : Plane → ℝ) :
    squareAverage (fun z => c * f z) = c * squareAverage f := by
  simp only [squareAverage, intervalIntegral.integral_const_mul]

theorem angular_cosine_covariance (a phase : Plane → ℝ) (j : ℤ) (hj : j ≠ 0) :
    squareAverage (fun z => SmoothLoop.angularMean
      (fun θ => a z * Real.cos ((j : ℝ) * θ + phase z) ^ 2)) =
      (1 / 2) * squareAverage a := by
  simp only [SmoothLoop.angularMean_const_mul, angularMean_cos_sq_harmonic j hj]
  simpa only [mul_comm] using squareAverage_const_mul (1 / 2) a

/-- The displayed native prefactor in Lemma 8.7, for actual periodized slot
coefficients and actual angular averages. The harmonic is the rounded integer
`k*p`, so its only required property here is nonzero integrality. -/
theorem primary_covariance_average (vr vt center : Plane)
    (hdet : vr.1 * vt.2 - vr.2 * vt.1 ≠ 0) (ci r0 : ℝ) (hci : 0 < ci)
    {χ ψ x : ℝ → ℝ} {t : ℝ → PulseCovariance.Vec2}
    (hχ : Continuous χ) (hψ : Continuous ψ) (hx : Continuous x) (ht : Continuous t)
    (hcχ : HasCompactSupport χ) (hcψ : HasCompactSupport ψ) (i : Fin 2) (n : ℕ)
    (phase : Plane → ℝ) (j : ℤ) (hj : j ≠ 0) :
    let a := fun z => periodize
      (nativeField (slotChart vr vt hdet) center
        (transverseStretch ci r0 (pulseProfile χ ψ x t i)))
      (covering^[n] z)
    squareAverage (fun z => SmoothLoop.angularMean
      (fun θ => a z * Real.cos ((j : ℝ) * θ + phase z) ^ 2)) =
      (|vr.1 * vt.2 - vr.2 * vt.1| / 2) * (∫ ξ : ℝ, χ ξ ^ 2) *
        PulseCovariance.actualColumn ci ψ x t i := by
  dsimp only
  rw [angular_cosine_covariance _ phase j hj,
    squareAverage_covered_pulseColumn vr vt center hdet ci r0 hci
      hχ hψ hx ht hcχ hcψ i n]
  ring

/-- The same exact prefactor with the transverse integral restricted to the
actual pulse interval, using the already verified compact pulse support. -/
theorem primary_covariance_average_interval (vr vt center : Plane)
    (hdet : vr.1 * vt.2 - vr.2 * vt.1 ≠ 0) (ci r0 : ℝ) (hci : 0 < ci)
    {r a A b B : ℝ} {χ ψ x : ℝ → ℝ} {t : ℝ → PulseCovariance.Vec2}
    (hp : PulseCovariance.PulseBounds r a A b B ψ x)
    (hχ : Continuous χ) (ht : Continuous t) (hcχ : HasCompactSupport χ)
    (i : Fin 2) (n : ℕ) (phase : Plane → ℝ) (j : ℤ) (hj : j ≠ 0) :
    let amp := fun z => periodize
      (nativeField (slotChart vr vt hdet) center
        (transverseStretch ci r0 (pulseProfile χ ψ x t i)))
      (covering^[n] z)
    squareAverage (fun z => SmoothLoop.angularMean
      (fun θ => amp z * Real.cos ((j : ℝ) * θ + phase z) ^ 2)) =
      (|vr.1 * vt.2 - vr.2 * vt.1| / 2) * (∫ ξ : ℝ, χ ξ ^ 2) *
        (ci * ∫ v in (0 : ℝ)..r ^ 2, ψ v ^ 2 * x v * t v i) := by
  rw [← hp.actualColumn_eq_intervalIntegral ci t i]
  exact primary_covariance_average vr vt center hdet ci r0 hci
    hχ hp.cutoff_continuous hp.component_continuous ht hcχ hp.cutoff_compact i n phase j hj

end NavierStokes.TorusAverages
