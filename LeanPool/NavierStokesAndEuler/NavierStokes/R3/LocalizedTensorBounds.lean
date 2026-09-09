/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.NavierStokes.R3.ComparisonSetup
import LeanPool.NavierStokesAndEuler.NavierStokes.R3.LpNormTools
import LeanPool.NavierStokesAndEuler.NavierStokes.R3.WeightedInterpolation
import LeanPool.NavierStokesAndEuler.NavierStokes.R3.WeightedSobolev

/-!
# Weighted tensor bounds for the localized pressure

The tensor difference is expanded around the reference velocity. Its two
cross terms use `L³` of that velocity and `L²` of the difference; the quadratic
term uses the cutoff interpolation estimate. All norms remain finite explicitly.
-/

@[expose] public section



noncomputable section

open MeasureTheory Filter
open scoped ENNReal

namespace NavierStokesR3.LocalizedTensorBounds

open ProblemStatement Comparison

private theorem six_fifths_ne_zero : (6 / 5 : ℝ≥0∞) ≠ 0 :=
  (ENNReal.toReal_pos_iff.mp (by norm_num : 0 < (6 / 5 : ℝ≥0∞).toReal)).1.ne'

private theorem six_fifths_ne_top : (6 / 5 : ℝ≥0∞) ≠ ⊤ :=
  (ENNReal.toReal_pos_iff.mp (by norm_num : 0 < (6 / 5 : ℝ≥0∞).toReal)).2.ne

private theorem twelve_fifths_ne_zero : (12 / 5 : ℝ≥0∞) ≠ 0 :=
  (ENNReal.toReal_pos_iff.mp (by norm_num : 0 < (12 / 5 : ℝ≥0∞).toReal)).1.ne'

/-- Scalar Hölder with finite real-valued norms. -/
theorem scalar_product_bound {p q r : ℝ≥0∞} [ENNReal.HolderTriple p q r]
    {f g : Space → ℝ} (hf : MemLp f p volume) (hg : MemLp g q volume) :
    MemLp (fun x => f x * g x) r volume ∧
      comparisonLpNorm r (fun x => f x * g x) ≤ comparisonLpNorm p f * comparisonLpNorm q g := by
  have hprod : MemLp (fun x => f x * g x) r volume := hg.mul' hf
  have hb : eLpNorm (fun x => f x * g x) r volume ≤
      eLpNorm f p volume * eLpNorm g q volume := by
    simpa using eLpNorm_le_eLpNorm_mul_eLpNorm'_of_norm hf.1 hg.1
      (fun a b : ℝ => a * b) 1
      (Eventually.of_forall fun x => by simp [norm_mul])
  refine ⟨hprod, ?_⟩
  simpa only [comparisonLpNorm, ENNReal.toReal_mul] using
    ENNReal.toReal_mono (ENNReal.mul_ne_top hf.eLpNorm_ne_top hg.eLpNorm_ne_top) hb

/-- The scalar product of the two vector magnitudes belongs to `L^(6/5)`. -/
theorem cross_norm_bound {u w : Space → Space}
    (hu : MemLp u 3 volume) (hw : MemLp w 2 volume) :
    MemLp (fun x => ‖u x‖ * ‖w x‖) (6 / 5) volume ∧
      comparisonLpNorm (6 / 5) (fun x => ‖u x‖ * ‖w x‖) ≤ comparisonLpNorm 3 u * comparisonLpNorm 2
          w := by
  let : ENNReal.HolderTriple (3 : ℝ≥0∞) 2 (6 / 5) := ⟨by
    apply (ENNReal.toReal_eq_toReal_iff' (by finiteness)
      (ENNReal.inv_ne_top.mpr six_fifths_ne_zero)).mp
    rw [ENNReal.toReal_add (by finiteness) (by finiteness)]
    norm_num⟩
  simpa only [comparisonLpNorm, eLpNorm_norm] using scalar_product_bound (r := 6 / 5) hu.norm
      hw.norm

/-- The quadratic weighted difference has the endpoint interpolation bound. -/
theorem quadratic_cutoff_bound {φ : Space → ℝ} {w : Space → Space}
    (hφm : AEStronglyMeasurable φ volume) (hφ0 : ∀ x, 0 ≤ φ x)
    (hw : MemLp w 2 volume)
    (hweighted : MemLp (fun x => φ x ^ 4 • w x) 6 volume) :
    MemLp (fun x => ‖φ x • w x‖ ^ 2) (6 / 5) volume ∧
      comparisonLpNorm (6 / 5) (fun x => ‖φ x • w x‖ ^ 2) ≤
        comparisonLpNorm 2 w ^ (3 / 2 : ℝ) *
          comparisonLpNorm 6 (fun x => φ x ^ 4 • w x) ^ (1 / 2 : ℝ) := by
  obtain ⟨hmem, hb⟩ := WeightedInterpolation.cutoff_interpolation_twelve_fifths
    hφm hφ0 hw hweighted
  let : ENNReal.HolderTriple (12 / 5 : ℝ≥0∞) (12 / 5) (6 / 5) := ⟨by
    have h12 := ENNReal.inv_ne_top.mpr twelve_fifths_ne_zero
    apply (ENNReal.toReal_eq_toReal_iff' (ENNReal.add_ne_top.mpr ⟨h12, h12⟩)
      (ENNReal.inv_ne_top.mpr six_fifths_ne_zero)).mp
    rw [ENNReal.toReal_add h12 h12]
    norm_num⟩
  obtain ⟨hprod, hprodb⟩ := scalar_product_bound (r := 6 / 5) hmem.norm hmem.norm
  have hQ : MemLp (fun x => ‖φ x • w x‖ ^ 2) (6 / 5) volume := by
    simpa only [pow_two] using hprod
  have hQb : comparisonLpNorm (6 / 5) (fun x => ‖φ x • w x‖ ^ 2) ≤
      comparisonLpNorm (12 / 5) (fun x => φ x • w x) ^ 2 := by
    simpa only [pow_two, comparisonLpNorm, eLpNorm_norm] using hprodb
  have hA := LpNormTools.lpNorm_nonneg (12 / 5) (fun x => φ x • w x)
  have hM := LpNormTools.lpNorm_nonneg 2 w
  have hB := LpNormTools.lpNorm_nonneg 6 (fun x => φ x ^ 4 • w x)
  refine ⟨hQ, hQb.trans ?_⟩
  calc
    comparisonLpNorm (12 / 5) (fun x => φ x • w x) ^ 2 ≤
        (comparisonLpNorm 2 w ^ (3 / 4 : ℝ) *
          comparisonLpNorm 6 (fun x => φ x ^ 4 • w x) ^ (1 / 4 : ℝ)) ^ 2 := by
      exact pow_le_pow_left₀ hA hb 2
    _ = comparisonLpNorm 2 w ^ (3 / 2 : ℝ) *
        comparisonLpNorm 6 (fun x => φ x ^ 4 • w x) ^ (1 / 2 : ℝ) := by
      rw [← Real.rpow_natCast _ 2,
        Real.mul_rpow (Real.rpow_nonneg hM _) (Real.rpow_nonneg hB _),
        ← Real.rpow_mul hM, ← Real.rpow_mul hB]
      norm_num

/-- The tensor identity uses the actual difference of the two velocities. -/
theorem tensorDiff_eq (u v : VelocityField) (t : ℝ) (i j : Fin 3) (x : Space) :
    tensorDiff u v t i j x =
      u (t, x) i * (u - v) (t, x) j +
        (u - v) (t, x) i * u (t, x) j -
        (u - v) (t, x) i * (u - v) (t, x) j := by
  change u (t, x) i * u (t, x) j - v (t, x) i * v (t, x) j =
    u (t, x) i * (u (t, x) j - v (t, x) j) +
      (u (t, x) i - v (t, x) i) * u (t, x) j -
      (u (t, x) i - v (t, x) i) * (u (t, x) j - v (t, x) j)
  ring

theorem continuous_component {f : Space → Space} (hf : Continuous f) (i : Fin 3) :
    Continuous (fun x => f x i) :=
  (continuous_apply i).comp ((EuclideanSpace.equiv (Fin 3) ℝ).continuous.comp hf)

theorem continuous_tensorDiff {u v : VelocityField} {t : ℝ}
    (hu : Continuous (fun x => u (t, x))) (hv : Continuous (fun x => v (t, x)))
    (i j : Fin 3) : Continuous (tensorDiff u v t i j) :=
  ((continuous_component hu i).mul (continuous_component hu j)).sub
    ((continuous_component hv i).mul (continuous_component hv j))

/-- Pointwise domination is uniform in both tensor indices. -/
theorem norm_weighted_tensorDiff_le (u v : VelocityField) (t : ℝ) (i j : Fin 3)
    (x : Space) {s : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1) :
    ‖s ^ 2 * tensorDiff u v t i j x‖ ≤
      2 * (‖u (t, x)‖ * ‖(u - v) (t, x)‖) + ‖s • (u - v) (t, x)‖ ^ 2 := by
  let a := u (t, x)
  let w := (u - v) (t, x)
  have hcross1 : ‖a i * w j‖ ≤ ‖a‖ * ‖w‖ := by
    rw [norm_mul]
    exact mul_le_mul (PiLp.norm_apply_le a i) (PiLp.norm_apply_le w j)
      (norm_nonneg _) (norm_nonneg _)
  have hcross2 : ‖w i * a j‖ ≤ ‖w‖ * ‖a‖ := by
    rw [norm_mul]
    exact mul_le_mul (PiLp.norm_apply_le w i) (PiLp.norm_apply_le a j)
      (norm_nonneg _) (norm_nonneg _)
  have hquad : ‖w i * w j‖ ≤ ‖w‖ * ‖w‖ := by
    rw [norm_mul]
    exact mul_le_mul (PiLp.norm_apply_le w i) (PiLp.norm_apply_le w j)
      (norm_nonneg _) (norm_nonneg _)
  have ht : ‖tensorDiff u v t i j x‖ ≤ 2 * (‖a‖ * ‖w‖) + ‖w‖ ^ 2 := by
    rw [tensorDiff_eq]
    calc
      ‖a i * w j + w i * a j - w i * w j‖ ≤
          ‖a i * w j + w i * a j‖ + ‖w i * w j‖ := norm_sub_le _ _
      _ ≤ (‖a i * w j‖ + ‖w i * a j‖) + ‖w i * w j‖ :=
        add_le_add_left (norm_add_le _ _) _
      _ ≤ (‖a‖ * ‖w‖ + ‖w‖ * ‖a‖) + ‖w‖ * ‖w‖ :=
        add_le_add (add_le_add hcross1 hcross2) hquad
      _ = _ := by ring
  have hs2 : s ^ 2 ≤ 1 := pow_le_one₀ hs0 hs1
  calc
    ‖s ^ 2 * tensorDiff u v t i j x‖ = s ^ 2 * ‖tensorDiff u v t i j x‖ := by
      rw [norm_mul, Real.norm_eq_abs, abs_of_nonneg (sq_nonneg s)]
    _ ≤ s ^ 2 * (2 * (‖a‖ * ‖w‖) + ‖w‖ ^ 2) :=
      mul_le_mul_of_nonneg_left ht (sq_nonneg s)
    _ ≤ 2 * (‖a‖ * ‖w‖) + ‖s • w‖ ^ 2 := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hs0]
      nlinarith [mul_nonneg (sub_nonneg.mpr hs2) (mul_nonneg (norm_nonneg a) (norm_nonneg w))]

/-- Compactness supplies finite weighted tensor norms without any growth
assumption on either velocity. -/
theorem weighted_tensorDiff_memLp {φ : Space → ℝ} {u v : VelocityField} {t : ℝ}
    (hφ : Continuous φ) (hs : HasCompactSupport φ)
    (hu : Continuous (fun x => u (t, x))) (hv : Continuous (fun x => v (t, x)))
    (i j : Fin 3) (p : ℝ≥0∞) :
    MemLp (fun x => φ x ^ 2 * tensorDiff u v t i j x) p volume := by
  have hp : HasCompactSupport (fun x => φ x ^ 2) :=
    hs.comp_left (g := fun r : ℝ => r ^ 2) (by norm_num)
  exact ((hφ.pow 2).mul (continuous_tensorDiff hu hv i j)).memLp_of_hasCompactSupport hp.mul_right

/-- The weighted tensor estimate used by the localized pressure argument.
It has the same constant for every pair of indices. -/
theorem weighted_tensorDiff_bound {φ : Space → ℝ} {u v : VelocityField} {t : ℝ}
    (hφ : Continuous φ) (hs : HasCompactSupport φ)
    (hu : Continuous (fun x => u (t, x))) (hv : Continuous (fun x => v (t, x)))
    (hw2 : MemLp (fun x => (u - v) (t, x)) 2 volume)
    (hu3 : MemLp (fun x => u (t, x)) 3 volume)
    (hφ0 : ∀ x, 0 ≤ φ x) (hφ1 : ∀ x, φ x ≤ 1) (i j : Fin 3) :
    MemLp (fun x => φ x ^ 2 * tensorDiff u v t i j x) (6 / 5) volume ∧
      comparisonLpNorm (6 / 5) (fun x => φ x ^ 2 * tensorDiff u v t i j x) ≤
        comparisonLpNorm 2 (fun x => (u - v) (t, x)) ^ (3 / 2 : ℝ) *
          cutoffL6 φ (u - v) t ^ (1 / 2 : ℝ) +
        2 * comparisonLpNorm 2 (fun x => (u - v) (t, x)) * comparisonLpNorm 3 (fun x => u (t, x))
            := by
  let P : Space → ℝ := fun x => ‖u (t, x)‖ * ‖(u - v) (t, x)‖
  let Q : Space → ℝ := fun x => ‖φ x • (u - v) (t, x)‖ ^ 2
  obtain ⟨hP, hPb⟩ := cross_norm_bound hu3 hw2
  have hweighted := WeightedSobolev.memLp_cutoff_pow_smul hφ hs (hu.sub hv)
    (by norm_num : (4 : ℕ) ≠ 0) 6
  obtain ⟨hQ, hQb⟩ := quadratic_cutoff_bound hφ.aestronglyMeasurable hφ0 hw2 hweighted
  change MemLp P (6 / 5) volume at hP
  change comparisonLpNorm (6 / 5) P ≤ _ at hPb
  change MemLp Q (6 / 5) volume at hQ
  change comparisonLpNorm (6 / 5) Q ≤ _ at hQb
  have h2P : MemLp (fun x => (2 : ℝ) • P x) (6 / 5) volume := hP.const_smul (2 : ℝ)
  refine ⟨weighted_tensorDiff_memLp hφ hs hu hv i j (6 / 5), ?_⟩
  calc
    comparisonLpNorm (6 / 5) (fun x => φ x ^ 2 * tensorDiff u v t i j x) ≤
        comparisonLpNorm (6 / 5) (fun x => (2 : ℝ) • P x + Q x) := by
      apply LpNormTools.lpNorm_mono_of_norm_le (h2P.add hQ)
      intro x
      change ‖φ x ^ 2 * tensorDiff u v t i j x‖ ≤ ‖2 * P x + Q x‖
      have hn : ‖2 * P x + Q x‖ = 2 * P x + Q x := by
        rw [Real.norm_eq_abs, abs_of_nonneg]
        dsimp [P, Q]
        positivity
      rw [hn]
      exact norm_weighted_tensorDiff_le u v t i j x (hφ0 x) (hφ1 x)
    _ ≤ comparisonLpNorm (6 / 5) (fun x => (2 : ℝ) • P x) + comparisonLpNorm (6 / 5) Q :=
      LpNormTools.lpNorm_add_le (by
        apply (ENNReal.toReal_le_toReal ENNReal.one_ne_top six_fifths_ne_top).mp
        norm_num) h2P hQ
    _ = 2 * comparisonLpNorm (6 / 5) P + comparisonLpNorm (6 / 5) Q := by
      rw [LpNormTools.lpNorm_const_smul]
      norm_num
    _ ≤ _ := by
      change 2 * comparisonLpNorm (6 / 5) P + comparisonLpNorm (6 / 5) Q ≤
        comparisonLpNorm 2 (fun x => (u - v) (t, x)) ^ (3 / 2 : ℝ) *
          comparisonLpNorm 6 (fun x => φ x ^ 4 • (u - v) (t, x)) ^ (1 / 2 : ℝ) +
        2 * comparisonLpNorm 2 (fun x => (u - v) (t, x)) * comparisonLpNorm 3 (fun x => u (t, x))
      nlinarith

end NavierStokesR3.LocalizedTensorBounds
