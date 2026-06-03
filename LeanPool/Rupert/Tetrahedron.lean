/-
Copyright (c) 2026 David Renshaw. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Renshaw
-/

import LeanPool.Rupert.Basic
import LeanPool.Rupert.Convex
import LeanPool.Rupert.MatrixSimps
import LeanPool.Rupert.Quaternion
import LeanPool.Rupert.Equivalences.RupertEquivRupertPrime
import LeanPool.Rupert.FinCases

/-!
# LeanPool.Rupert.Tetrahedron

Imported Lean Pool material for `LeanPool.Rupert.Tetrahedron`.
-/

namespace Tetrahedron

open scoped Matrix

/-- Vertices of a regular tetrahedron. -/
def vertices : Fin 4 → ℝ³ :=
  ![!₂[ 1,  1,  1],
    !₂[ 1, -1, -1],
    !₂[-1,  1, -1],
    !₂[-1, -1,  1]]

/-- Quaternion certificate for the outer tetrahedron rotation. -/
def outerQuat : Quaternion ℝ := ⟨0.338990, -0.426182, 0.173602, -0.820558⟩

/-- Rotation matrix for the outer tetrahedron. -/
noncomputable def outerRot := matrixOfQuat outerQuat

lemma outerRot_so3 : outerRot ∈ SO3 := by
  have h : outerQuat.normSq ≠ 0 := by norm_num [outerQuat, Quaternion.normSq_def]
  exact matrixOfQuat_is_s03 h

/-- Quaternion certificate for the inner tetrahedron rotation. -/
def innerQuat : Quaternion ℝ := ⟨0.857701, -0.119161, 0.443971, 0.230299⟩

/-- Rotation matrix for the inner tetrahedron. -/
noncomputable def innerRot := matrixOfQuat innerQuat

lemma innerRot_so3 : innerRot ∈ SO3 := by
  have h : innerQuat.normSq ≠ 0 := by norm_num [innerQuat, Quaternion.normSq_def]
  exact matrixOfQuat_is_s03 h

/-- Translation offset for the inner tetrahedron shadow. -/
def innerOffset : ℝ² := !₂[0.098412,-0.165800]

theorem rupert : IsRupert vertices := by
  rw [rupert_iff_rupert']
  use innerRot, innerRot_so3, innerOffset, outerRot, outerRot_so3
  intro inner_shadow outerShadow
  let ε₀ : ℝ := 0.001
  have hε₀ : ε₀ ∈ Set.Ioo 0 1 := by norm_num
  have hb : Metric.ball 0 ε₀ ⊆ convexHull ℝ outerShadow := by
    refine Convex.ball_in_hull_of_corners_in_hull hε₀ ?_ ?_ ?_ ?_ <;>
      apply mem_convexHull_iff_exists_fintype.mpr <;>
      use Fin 4, inferInstance
    <;> [
      use ![14470757879961/43300505182000,
            14426795957911/43300505182000,
            0,
            900184459008/2706281573875];
      use ![72265247417243/216502525910000,
            72310753372299/216502525910000,
            0,
            35963262560229/108251262955000];
      use ![14483649997239/43300505182000,
            14462186725689/43300505182000,
            0,
            897166778692/2706281573875];
      use ![72506791968757/216502525910000,
            72134160045701/216502525910000,
            0,
            35930786947771/108251262955000]
    ]
    all_goals
      use fun i ↦ projXy (outerRot.toEuclideanLin (vertices i))
      refine ⟨?_, ?_, ?_, ?_⟩
      · intro i; fin_cases i <;> norm_num
      · simp [Fin.sum_univ_four]; norm_num
      · exact fun i ↦ ⟨i, rfl⟩
      · simp only [projXy, outerRot, matrixOfQuat, outerQuat, vertices, Fin.sum_univ_four,
                   ε₀, matrix_simps]
        ext i; fin_cases i <;> norm_num
  intro v hv
  let ε₁ : ℝ := 0.0001
  have hε₁ : ε₁ ∈ Set.Ioo 0 1 := by norm_num
  refine Convex.mem_interior_hull hε₀.1 hε₁ hb ?_
  simp only [inner_shadow] at hv
  obtain ⟨y, hy⟩ := hv
  rw [mem_convexHull_iff_exists_fintype]
  fin_cases y <;>
    simp only [vertices, Fin.reduceFinMk, Matrix.cons_val] at hy <;>
    use Fin 4, inferInstance
  <;> [
    use ![10743981448378145233579223/2255005124571996596714809125,
          64386129031453492435586819/13530030747431979580288854750,
          0,
          13401180729710257216451792593/13530030747431979580288854750];
    use ![5556134647331086902480487669/6765015373715989790144427375,
          2352935973121235655284086819/13530030747431979580288854750,
          0,
          21608493216190040014597531/4510010249143993193429618250];
    use ![4608766371145456006819667/966430767673712827163489625,
          1914434962235023371784298117/1932861535347425654326979250,
          0,
          3069680123370456843013933/644287178449141884775659750];
    use ![5556788588822333700340487669/6765015373715989790144427375,
          64569206997427958451586819/13530030747431979580288854750,
          0,
          2351884362789884221156292593/13530030747431979580288854750]
  ]
  all_goals
    use fun i ↦ (1 - ε₁) • (projXy (outerRot.toEuclideanLin (vertices i)))
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro i; fin_cases i <;> norm_num
    · simp only [Fin.sum_univ_four, matrix_simps]; norm_num
    · exact fun i ↦ ⟨projXy (outerRot.toEuclideanLin (vertices i)), by simp [outerShadow]⟩
    · rw [←hy]
      simp only [projXy, outerRot, matrixOfQuat, outerQuat, vertices, Fin.sum_univ_four,
                 innerOffset, innerRot, innerQuat, ε₁, matrix_simps]
      ext i; fin_cases i <;> norm_num

end Tetrahedron
