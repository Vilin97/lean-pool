/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

import LeanPool.CoarseGraining.Homogenization.Besov.Positive.ExactOverlap
import LeanPool.CoarseGraining.Homogenization.Ambient.Euclidean

/-!
# Exact Euclidean-valued overlapping positive-order Besov kernel

This module specializes the exact Chapter 1 overlap kernel to the source-facing
fractional full norm for vector fields at `p = q = 2`.  Both the seminorm and
the root mean are aggregated over coordinates with the Euclidean `ℓ²` norm.
All quantities remain `ENNReal`-valued, so no finiteness assumption is hidden
in the definition.
-/

namespace Homogenization

open scoped BigOperators ENNReal

private theorem coordinate_le_euclideanENorm {d : ℕ} (a : Fin d → ℝ≥0∞) (i : Fin d) :
    a i ≤ (∑ j : Fin d, a j ^ 2) ^ ((2 : ℝ)⁻¹) := by
  have hsquare : a i ^ (2 : ℕ) ≤ ∑ j : Fin d, a j ^ (2 : ℕ) := by
    exact Finset.single_le_sum
      (fun j _ => (zero_le : (0 : ℝ≥0∞) ≤ a j ^ (2 : ℕ))) (Finset.mem_univ i)
  have hroot := ENNReal.rpow_le_rpow hsquare (show 0 ≤ (2 : ℝ)⁻¹ by norm_num)
  calc
    a i = (a i ^ (2 : ℕ)) ^ ((2 : ℝ)⁻¹) := by
      rw [← ENNReal.rpow_natCast, ← ENNReal.rpow_mul]
      norm_num
    _ ≤ (∑ j : Fin d, a j ^ (2 : ℕ)) ^ ((2 : ℝ)⁻¹) := hroot

private theorem euclideanENorm_lt_top_iff {d : ℕ} (a : Fin d → ℝ≥0∞) :
    (∑ i : Fin d, a i ^ 2) ^ ((2 : ℝ)⁻¹) < ∞ ↔ ∀ i, a i < ∞ := by
  constructor
  · intro h i
    by_contra hi
    have hi_top : a i = ∞ := top_unique (not_lt.mp hi)
    have hsum_top : (∑ k : Fin d, a k ^ (2 : ℕ)) = ∞ := by
      rw [ENNReal.sum_eq_top]
      refine ⟨i, Finset.mem_univ i, ?_⟩
      exact (ENNReal.pow_eq_top_iff).2 ⟨hi_top, by norm_num⟩
    rw [hsum_top, ENNReal.top_rpow_of_pos (by norm_num)] at h
    exact lt_irrefl ∞ h
  · intro h
    apply ENNReal.rpow_lt_top_of_nonneg (by norm_num)
    apply (ENNReal.sum_ne_top).2
    intro i _
    exact ENNReal.pow_ne_top (ne_of_lt (h i))

private theorem euclideanENorm_eq_ofReal_euclideanNorm {d : ℕ} (x : Vec d) :
    (∑ i : Fin d, (ENNReal.ofReal |x i|) ^ 2) ^ ((2 : ℝ)⁻¹) =
      ENNReal.ofReal (euclideanNorm x) := by
  unfold euclideanNorm vecNormSq vecDot
  have hsquares : (∑ i : Fin d, x i * x i) = ∑ i : Fin d, x i ^ 2 := by
    apply Finset.sum_congr rfl
    intro i _
    rw [pow_two]
  rw [hsquares, Real.sqrt_eq_rpow, one_div]
  rw [← ENNReal.ofReal_rpow_of_nonneg (Finset.sum_nonneg fun _ _ => sq_nonneg _)
    (by norm_num)]
  congr 1
  rw [ENNReal.ofReal_sum_of_nonneg (fun _ _ => sq_nonneg _)]
  apply Finset.sum_congr rfl
  intro i _
  rw [← ENNReal.ofReal_pow (abs_nonneg (x i)), sq_abs]

private theorem exactOverlapRootWeight_lt_top_aux {d : ℕ} (Q : TriadicCube d) (s : ℝ) :
    exactOverlapRootWeight Q s < ∞ := by
  unfold exactOverlapRootWeight
  rw [lt_top_iff_ne_top, ne_eq, ENNReal.rpow_eq_top_iff]
  norm_num

/-- The exact finite-overlap parameters with `p = q = 2` and `0 < s < 1`. -/
noncomputable def exactOverlapTwoParameters (s : Set.Ioo (0 : ℝ) 1) :
    ExactOverlapFiniteParameters where
  s := s.1
  p := 2
  q := 2
  admissible := ⟨s.2.1, s.2.2, by norm_num, by norm_num⟩

/-- Coordinatewise integrability certificates for a Euclidean-valued field.
Each coordinate is certified on the root cube and on every enlarged overlap
cube used by the exact scalar kernel. -/
structure ExactOverlapEuclideanIntegrable {d : ℕ} (Q : TriadicCube d)
    (F : Vec d → Vec d) : Prop where
  coordinate : ∀ i : Fin d, ExactOverlapIntegrable Q (fun x => F x i)

/-- Canonical coordinatewise certificates for the zero vector field. -/
theorem exactOverlapEuclideanZeroIntegrable {d : ℕ} (Q : TriadicCube d) :
    ExactOverlapEuclideanIntegrable Q (fun _ : Vec d => (0 : Vec d)) where
  coordinate := fun _ => exactOverlapZeroIntegrable Q

/-- Euclidean magnitude of the certified coordinate root means, retained in
`ENNReal`. -/
noncomputable def exactOverlapEuclideanRootMeanENorm {d : ℕ} (Q : TriadicCube d)
    (F : Vec d → Vec d) (hF : ExactOverlapEuclideanIntegrable Q F) : ℝ≥0∞ :=
  (∑ i : Fin d,
    (ENNReal.ofReal |exactOverlapRootMean Q (fun x => F x i)
      (hF.coordinate i).root|) ^ 2) ^ ((2 : ℝ)⁻¹)

/-- Exact Euclidean-valued overlap Besov seminorm at `p = q = 2`, obtained by
Euclidean aggregation of the exact scalar coordinate seminorms. -/
noncomputable def exactOverlapEuclideanSeminormTwo {d : ℕ} (s : Set.Ioo (0 : ℝ) 1)
    (Q : TriadicCube d) (F : Vec d → Vec d)
    (hF : ExactOverlapEuclideanIntegrable Q F) : ℝ≥0∞ :=
  (∑ i : Fin d,
    (exactOverlapFiniteSeminorm (exactOverlapTwoParameters s) Q
      (fun x => F x i) (hF.coordinate i)) ^ 2) ^ ((2 : ℝ)⁻¹)

/-- The source-facing fractional full norm: the exact Euclidean `p = q = 2`
seminorm plus `3^(-s m)` times the Euclidean magnitude of the coordinate root
means. -/
noncomputable def exactOverlapEuclideanNormTwo {d : ℕ} (s : Set.Ioo (0 : ℝ) 1)
    (Q : TriadicCube d) (F : Vec d → Vec d)
    (hF : ExactOverlapEuclideanIntegrable Q F) : ℝ≥0∞ :=
  exactOverlapEuclideanSeminormTwo s Q F hF +
    exactOverlapRootWeight Q s.1 * exactOverlapEuclideanRootMeanENorm Q F hF

/-- Evaluation of the Euclidean root-mean magnitude. -/
theorem exactOverlapEuclideanRootMeanENorm_eq {d : ℕ} (Q : TriadicCube d)
    (F : Vec d → Vec d) (hF : ExactOverlapEuclideanIntegrable Q F) :
    exactOverlapEuclideanRootMeanENorm Q F hF =
      (∑ i : Fin d,
        (ENNReal.ofReal |exactOverlapRootMean Q (fun x => F x i)
          (hF.coordinate i).root|) ^ 2) ^ ((2 : ℝ)⁻¹) :=
  rfl

/-- Evaluation of the exact Euclidean `p = q = 2` seminorm. -/
theorem exactOverlapEuclideanSeminormTwo_eq {d : ℕ} (s : Set.Ioo (0 : ℝ) 1)
    (Q : TriadicCube d) (F : Vec d → Vec d)
    (hF : ExactOverlapEuclideanIntegrable Q F) :
    exactOverlapEuclideanSeminormTwo s Q F hF =
      (∑ i : Fin d,
        (exactOverlapFiniteSeminorm (exactOverlapTwoParameters s) Q
          (fun x => F x i) (hF.coordinate i)) ^ 2) ^ ((2 : ℝ)⁻¹) :=
  rfl

/-- Evaluation of the source-facing fractional full norm. -/
theorem exactOverlapEuclideanNormTwo_eq {d : ℕ} (s : Set.Ioo (0 : ℝ) 1)
    (Q : TriadicCube d) (F : Vec d → Vec d)
    (hF : ExactOverlapEuclideanIntegrable Q F) :
    exactOverlapEuclideanNormTwo s Q F hF =
      exactOverlapEuclideanSeminormTwo s Q F hF +
        exactOverlapRootWeight Q s.1 * exactOverlapEuclideanRootMeanENorm Q F hF :=
  rfl

/-- The coordinate formula for the root means is exactly the `ENNReal`
embedding of their explicit Euclidean magnitude. -/
theorem exactOverlapEuclideanRootMeanENorm_eq_ofReal_euclideanNorm {d : ℕ}
    (Q : TriadicCube d) (F : Vec d → Vec d)
    (hF : ExactOverlapEuclideanIntegrable Q F) :
    exactOverlapEuclideanRootMeanENorm Q F hF =
      ENNReal.ofReal (euclideanNorm (fun i =>
        exactOverlapRootMean Q (fun x => F x i) (hF.coordinate i).root)) :=
  euclideanENorm_eq_ofReal_euclideanNorm _

/-- Each coordinate root mean is bounded by the Euclidean root-mean
magnitude. -/
theorem exactOverlapEuclideanRootMean_coordinate_le {d : ℕ} (Q : TriadicCube d)
    (F : Vec d → Vec d) (hF : ExactOverlapEuclideanIntegrable Q F) (i : Fin d) :
    ENNReal.ofReal |exactOverlapRootMean Q (fun x => F x i)
      (hF.coordinate i).root| ≤ exactOverlapEuclideanRootMeanENorm Q F hF := by
  rw [exactOverlapEuclideanRootMeanENorm_eq]
  exact coordinate_le_euclideanENorm _ i

/-- Each exact scalar coordinate seminorm is bounded by the exact Euclidean
seminorm. -/
theorem exactOverlapEuclideanSeminormTwo_coordinate_le {d : ℕ}
    (s : Set.Ioo (0 : ℝ) 1) (Q : TriadicCube d) (F : Vec d → Vec d)
    (hF : ExactOverlapEuclideanIntegrable Q F) (i : Fin d) :
    exactOverlapFiniteSeminorm (exactOverlapTwoParameters s) Q
      (fun x => F x i) (hF.coordinate i) ≤
        exactOverlapEuclideanSeminormTwo s Q F hF := by
  rw [exactOverlapEuclideanSeminormTwo_eq]
  exact coordinate_le_euclideanENorm _ i

/-- Each exact scalar coordinate full norm is bounded by the source-facing
Euclidean full norm. -/
theorem exactOverlapEuclideanNormTwo_coordinate_le {d : ℕ}
    (s : Set.Ioo (0 : ℝ) 1) (Q : TriadicCube d) (F : Vec d → Vec d)
    (hF : ExactOverlapEuclideanIntegrable Q F) (i : Fin d) :
    exactOverlapFiniteNorm (exactOverlapTwoParameters s) Q
      (fun x => F x i) (hF.coordinate i) ≤
        exactOverlapEuclideanNormTwo s Q F hF := by
  rw [exactOverlapFiniteNorm_eq, exactOverlapEuclideanNormTwo_eq]
  apply add_le_add (exactOverlapEuclideanSeminormTwo_coordinate_le s Q F hF i)
  exact mul_le_mul_right
    (exactOverlapEuclideanRootMean_coordinate_le Q F hF i) _

/-- The Euclidean root-mean magnitude is finite exactly when all coordinate
magnitudes are finite. -/
theorem exactOverlapEuclideanRootMeanENorm_lt_top_iff {d : ℕ} (Q : TriadicCube d)
    (F : Vec d → Vec d) (hF : ExactOverlapEuclideanIntegrable Q F) :
    exactOverlapEuclideanRootMeanENorm Q F hF < ∞ ↔
      ∀ i : Fin d, ENNReal.ofReal |exactOverlapRootMean Q (fun x => F x i)
        (hF.coordinate i).root| < ∞ :=
  euclideanENorm_lt_top_iff _

/-- The exact Euclidean seminorm is finite exactly when every exact scalar
coordinate seminorm is finite. -/
theorem exactOverlapEuclideanSeminormTwo_lt_top_iff {d : ℕ}
    (s : Set.Ioo (0 : ℝ) 1) (Q : TriadicCube d) (F : Vec d → Vec d)
    (hF : ExactOverlapEuclideanIntegrable Q F) :
    exactOverlapEuclideanSeminormTwo s Q F hF < ∞ ↔
      ∀ i : Fin d, exactOverlapFiniteSeminorm (exactOverlapTwoParameters s) Q
        (fun x => F x i) (hF.coordinate i) < ∞ :=
  euclideanENorm_lt_top_iff _

/-- The Euclidean root-mean magnitude is always finite because it is a finite
coordinate sum of embedded real means. -/
theorem exactOverlapEuclideanRootMeanENorm_lt_top {d : ℕ} (Q : TriadicCube d)
    (F : Vec d → Vec d) (hF : ExactOverlapEuclideanIntegrable Q F) :
    exactOverlapEuclideanRootMeanENorm Q F hF < ∞ := by
  rw [exactOverlapEuclideanRootMeanENorm_lt_top_iff]
  intro i
  exact ENNReal.ofReal_lt_top

/-- The source-facing Euclidean full norm is finite exactly when every exact
scalar coordinate seminorm is finite.  The root-mean term is automatically
finite. -/
theorem exactOverlapEuclideanNormTwo_lt_top_iff {d : ℕ}
    (s : Set.Ioo (0 : ℝ) 1) (Q : TriadicCube d) (F : Vec d → Vec d)
    (hF : ExactOverlapEuclideanIntegrable Q F) :
    exactOverlapEuclideanNormTwo s Q F hF < ∞ ↔
      ∀ i : Fin d, exactOverlapFiniteSeminorm (exactOverlapTwoParameters s) Q
        (fun x => F x i) (hF.coordinate i) < ∞ := by
  rw [exactOverlapEuclideanNormTwo_eq, ENNReal.add_lt_top,
    exactOverlapEuclideanSeminormTwo_lt_top_iff]
  have hrootTerm : exactOverlapRootWeight Q s.1 *
      exactOverlapEuclideanRootMeanENorm Q F hF < ∞ :=
    ENNReal.mul_lt_top (exactOverlapRootWeight_lt_top_aux Q s.1)
      (exactOverlapEuclideanRootMeanENorm_lt_top Q F hF)
  constructor
  · exact fun h => h.1
  · exact fun h => ⟨h, hrootTerm⟩

/-- Coordinatewise a.e. equality on the root cube preserves the Euclidean
root-mean magnitude. -/
theorem exactOverlapEuclideanRootMeanENorm_congr_ae {d : ℕ} (Q : TriadicCube d)
    {F G : Vec d → Vec d} (hF : ExactOverlapEuclideanIntegrable Q F)
    (hG : ExactOverlapEuclideanIntegrable Q G)
    (hroot : ∀ i : Fin d, (fun x => F x i) =ᵐ[normalizedCubeMeasure Q]
      (fun x => G x i)) :
    exactOverlapEuclideanRootMeanENorm Q F hF =
      exactOverlapEuclideanRootMeanENorm Q G hG := by
  unfold exactOverlapEuclideanRootMeanENorm
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  rw [exactOverlapRootMean_congr_ae Q (hF.coordinate i).root
    (hG.coordinate i).root (hroot i)]

/-- Coordinatewise a.e. equality on every enlarged overlap cube preserves the
exact Euclidean seminorm. -/
theorem exactOverlapEuclideanSeminormTwo_congr_ae {d : ℕ}
    (s : Set.Ioo (0 : ℝ) 1) (Q : TriadicCube d) {F G : Vec d → Vec d}
    (hF : ExactOverlapEuclideanIntegrable Q F)
    (hG : ExactOverlapEuclideanIntegrable Q G)
    (hoverlap : ∀ (i : Fin d) (j : ℕ) (S : TriadicCube d),
      S ∈ ScalarOverlap.centersAtDepth Q j →
        (fun x => F x i) =ᵐ[ScalarOverlap.normalizedCubeMeasure S]
          (fun x => G x i)) :
    exactOverlapEuclideanSeminormTwo s Q F hF =
      exactOverlapEuclideanSeminormTwo s Q G hG := by
  unfold exactOverlapEuclideanSeminormTwo
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  rw [exactOverlapFiniteSeminorm_congr_ae (exactOverlapTwoParameters s) Q
    (hF.coordinate i) (hG.coordinate i) (hoverlap i)]

/-- Coordinatewise a.e. equality on the root and enlarged overlap cubes
preserves the source-facing fractional full norm. -/
theorem exactOverlapEuclideanNormTwo_congr_ae {d : ℕ}
    (s : Set.Ioo (0 : ℝ) 1) (Q : TriadicCube d) {F G : Vec d → Vec d}
    (hF : ExactOverlapEuclideanIntegrable Q F)
    (hG : ExactOverlapEuclideanIntegrable Q G)
    (hroot : ∀ i : Fin d, (fun x => F x i) =ᵐ[normalizedCubeMeasure Q]
      (fun x => G x i))
    (hoverlap : ∀ (i : Fin d) (j : ℕ) (S : TriadicCube d),
      S ∈ ScalarOverlap.centersAtDepth Q j →
        (fun x => F x i) =ᵐ[ScalarOverlap.normalizedCubeMeasure S]
          (fun x => G x i)) :
    exactOverlapEuclideanNormTwo s Q F hF =
      exactOverlapEuclideanNormTwo s Q G hG := by
  unfold exactOverlapEuclideanNormTwo
  rw [exactOverlapEuclideanSeminormTwo_congr_ae s Q hF hG hoverlap,
    exactOverlapEuclideanRootMeanENorm_congr_ae Q hF hG hroot]

/-- The Euclidean root-mean magnitude vanishes on the zero vector field. -/
theorem exactOverlapEuclideanRootMeanENorm_zero {d : ℕ} (Q : TriadicCube d) :
    exactOverlapEuclideanRootMeanENorm Q (fun _ => (0 : Vec d))
      (exactOverlapEuclideanZeroIntegrable Q) = 0 := by
  rw [exactOverlapEuclideanRootMeanENorm_eq]
  simp only [Pi.zero_apply, exactOverlapRootMean_zero, abs_zero, ENNReal.ofReal_zero]
  norm_num

/-- The exact Euclidean seminorm vanishes on the zero vector field. -/
theorem exactOverlapEuclideanSeminormTwo_zero {d : ℕ} (s : Set.Ioo (0 : ℝ) 1)
    (Q : TriadicCube d) :
    exactOverlapEuclideanSeminormTwo s Q (fun _ => (0 : Vec d))
      (exactOverlapEuclideanZeroIntegrable Q) = 0 := by
  rw [exactOverlapEuclideanSeminormTwo_eq]
  simp only [Pi.zero_apply, exactOverlapFiniteSeminorm_zero]
  norm_num

/-- The source-facing fractional full norm vanishes on the zero vector field. -/
theorem exactOverlapEuclideanNormTwo_zero {d : ℕ} (s : Set.Ioo (0 : ℝ) 1)
    (Q : TriadicCube d) :
    exactOverlapEuclideanNormTwo s Q (fun _ => (0 : Vec d))
      (exactOverlapEuclideanZeroIntegrable Q) = 0 := by
  rw [exactOverlapEuclideanNormTwo_eq, exactOverlapEuclideanSeminormTwo_zero,
    exactOverlapEuclideanRootMeanENorm_zero]
  simp only [mul_zero, add_zero]

/-- Every exact Euclidean root-mean magnitude is nonnegative. -/
theorem exactOverlapEuclideanRootMeanENorm_nonneg {d : ℕ} (Q : TriadicCube d)
    (F : Vec d → Vec d) (hF : ExactOverlapEuclideanIntegrable Q F) :
    0 ≤ exactOverlapEuclideanRootMeanENorm Q F hF :=
  bot_le

/-- Every exact Euclidean `p = q = 2` seminorm is nonnegative. -/
theorem exactOverlapEuclideanSeminormTwo_nonneg {d : ℕ} (s : Set.Ioo (0 : ℝ) 1)
    (Q : TriadicCube d) (F : Vec d → Vec d)
    (hF : ExactOverlapEuclideanIntegrable Q F) :
    0 ≤ exactOverlapEuclideanSeminormTwo s Q F hF :=
  bot_le

/-- Every source-facing fractional full norm is nonnegative. -/
theorem exactOverlapEuclideanNormTwo_nonneg {d : ℕ} (s : Set.Ioo (0 : ℝ) 1)
    (Q : TriadicCube d) (F : Vec d → Vec d)
    (hF : ExactOverlapEuclideanIntegrable Q F) :
    0 ≤ exactOverlapEuclideanNormTwo s Q F hF :=
  bot_le

end Homogenization
