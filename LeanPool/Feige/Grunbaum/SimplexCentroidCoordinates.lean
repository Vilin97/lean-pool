/-
Copyright (c) 2026 Zhengqing Zhou and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zhengqing Zhou, GPT-5.6 Pro
-/
import LeanPool.Feige.Grunbaum.Sharpness

/-!
# Coordinates of the standard-simplex centroid

Coordinate permutations preserve both Euclidean volume and the standard
simplex.  Hence all centroid coordinates agree; their value follows from
the already computed coordinate sum.
-/

noncomputable section

open MeasureTheory Set

namespace Grunbaum

theorem simplexSet_image_piLpCongrLeft (n : ℕ) (σ : Equiv.Perm (Fin n)) :
    LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ σ '' simplexSet n =
      simplexSet n := by
  let L : SimplexE n ≃ₗᵢ[ℝ] SimplexE n :=
    LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ σ
  apply Set.Subset.antisymm
  · rintro y ⟨x, hx, rfl⟩
    constructor
    · intro i
      change 0 ≤ x (σ.symm i)
      exact hx.1 _
    · rw [coordinateSum_apply]
      change (∑ i, x (σ.symm i)) ≤ 1
      rw [Equiv.sum_comp σ.symm]
      simpa [coordinateSum_apply] using hx.2
  · intro y hy
    refine ⟨L.symm y, ?_, L.apply_symm_apply y⟩
    constructor
    · intro i
      unfold L
      rw [LinearIsometryEquiv.piLpCongrLeft_symm]
      change 0 ≤ y (σ i)
      exact hy.1 _
    · unfold L
      rw [LinearIsometryEquiv.piLpCongrLeft_symm]
      rw [coordinateSum_apply]
      change (∑ i, y (σ i)) ≤ 1
      rw [Equiv.sum_comp σ]
      simpa [coordinateSum_apply] using hy.2

theorem integral_simplex_coordinate_eq (n : ℕ) (i j : Fin n) :
    (∫ x in simplexSet n, x i ∂volume) =
      ∫ x in simplexSet n, x j ∂volume := by
  let σ : Equiv.Perm (Fin n) := Equiv.swap i j
  let L : SimplexE n ≃ₗᵢ[ℝ] SimplexE n :=
    LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ σ
  have hchange :=
    L.measurePreserving.setIntegral_image_emb
      L.toContinuousLinearEquiv.toHomeomorph.measurableEmbedding
      (fun x : SimplexE n ↦ x i) (simplexSet n)
  rw [simplexSet_image_piLpCongrLeft n σ] at hchange
  simpa [L, σ, LinearIsometryEquiv.piLpCongrLeft_apply,
    Equiv.piCongrLeft'] using hchange

theorem simplexCentroid_coordinate_eq (n : ℕ) (i j : Fin n) :
    simplexCentroid n i = simplexCentroid n j := by
  have h_id : Integrable (fun x : SimplexE n ↦ x)
      (volume.restrict (simplexSet n)) := by
    change IntegrableOn (fun x : SimplexE n ↦ x) (simplexSet n) volume
    exact continuous_id.continuousOn.integrableOn_compact
      (isCompact_simplexSet n)
  have hi :
      (∫ x in simplexSet n, x ∂volume) i =
        ∫ x in simplexSet n, x i ∂volume :=
    ((EuclideanSpace.proj i).integral_comp_comm h_id).symm
  have hj :
      (∫ x in simplexSet n, x ∂volume) j =
        ∫ x in simplexSet n, x j ∂volume :=
    ((EuclideanSpace.proj j).integral_comp_comm h_id).symm
  unfold simplexCentroid
  rw [setAverage_eq]
  simp only [PiLp.smul_apply, smul_eq_mul]
  rw [hi, hj, integral_simplex_coordinate_eq n i j]

/-- Every coordinate of the volume centroid of the standard `n`-simplex
equals `1 / (n + 1)`. -/
theorem simplexCentroid_apply (n : ℕ) (i : Fin n) :
    simplexCentroid n i = ((n : ℝ) + 1)⁻¹ := by
  have hn : 0 < n := lt_of_le_of_lt (Nat.zero_le i.val) i.isLt
  have hall :
      ∑ j : Fin n, simplexCentroid n j =
        (n : ℝ) * simplexCentroid n i := by
    simp_rw [simplexCentroid_coordinate_eq n _ i]
    simp
  have hsum := coordinateSum_simplexCentroid n
  rw [coordinateSum_apply, hall] at hsum
  have hnR : (n : ℝ) ≠ 0 := by positivity
  field_simp [hnR] at hsum ⊢
  nlinarith

end Grunbaum
