/-
Copyright (c) 2026 David Renshaw. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Renshaw
-/

import LeanPool.Rupert.Basic
import LeanPool.Rupert.Convex
import LeanPool.Rupert.FinCases
import LeanPool.Rupert.MatrixSimps
import LeanPool.Rupert.Quaternion
import LeanPool.Rupert.Equivalences.RupertEquivRupertPrime

/-!
# LeanPool.Rupert.TriakisTetrahedron

Imported Lean Pool material for `LeanPool.Rupert.TriakisTetrahedron`.
-/

namespace TriakisTetrahedron

open scoped Matrix

/-- Vertices of tom7's triakis tetrahedron, scaled by `3 / 5`. -/
noncomputable def vertices : Fin 8 → ℝ³ :=
  ![!₂[   1,    1,    1],
    !₂[   1,   -1,   -1],
    !₂[  -1,    1,   -1],
    !₂[  -1,   -1,    1],
    !₂[-3/5,  3/5,  3/5],
    !₂[ 3/5, -3/5,  3/5],
    !₂[ 3/5,  3/5, -3/5],
    !₂[-3/5, -3/5, -3/5]]

/-- Quaternion certificate for the inner rotation. -/
def innerQuat : Quaternion ℝ := ⟨0.144873924, 0.365747659, -0.854692880, -0.338733344⟩

/-- Translation offset for the inner shadow. -/
def innerOffset : ℝ² := !₂[8.5629464761e-05, 8.9387250451e-05]

/-- Quaternion certificate for the outer rotation. -/
def outerQuat : Quaternion ℝ := ⟨0.858732110, -0.148912807, -0.352436516, -0.340870417⟩

/-- Rotation matrix for the inner triakis tetrahedron. -/
noncomputable def innerRot := matrixOfQuat innerQuat

lemma innerRot_so3 : innerRot ∈ SO3 := by
  have h : innerQuat.normSq ≠ 0 := by norm_num [innerQuat, Quaternion.normSq_def]
  exact matrixOfQuat_is_s03 h

/-- Rotation matrix for the outer triakis tetrahedron. -/
noncomputable def outerRot := matrixOfQuat outerQuat

lemma outerRot_so3 : outerRot ∈ SO3 := by
  have h : outerQuat.normSq ≠ 0 := by norm_num [outerQuat, Quaternion.normSq_def]
  exact matrixOfQuat_is_s03 h

lemma outer_ball_subset :
    Metric.ball 0 (0.006 : ℝ) ⊆
      convexHull ℝ { projXy (outerRot.toEuclideanLin (vertices i)) | i } := by
  let ε₀ : ℝ := 0.006
  have hε₀ : ε₀ ∈ Set.Ioo 0 1 := by norm_num
  refine Convex.ball_in_hull_of_corners_in_hull hε₀ ?_ ?_ ?_ ?_ <;>
    apply mem_convexHull_iff_exists_fintype.mpr <;>
    use Fin 8, Fin.fintype 8
  <;> [
    use ![0, 0, 0,
          209107410810126884571/565617601328354816800,
          245824061168864729/35351100083022176050,
          0,
          70515401107905219313/113123520265670963360,
          0];
    use ![0,
          1051981313303264779479/2828088006641774084000,
          0,
          19719000787634436/6798288477504264625,
          353580717802170675829/565617601328354816800,
          0, 0, 0];
    use ![3938334956654107739/8031045263445271000,
          2045224314929433491/8031045263445271000,
          0,
          204748599186172977/803104526344527100,
          0, 0, 0, 0];
    use ![0,
          1095105012905906001/353511000830221760500,
          0,
          1052120747247162610137/2828088006641774084000,
          0, 0,
          353441283858272845171/565617601328354816800,
          0]
  ]
  all_goals
    use fun i ↦ projXy (outerRot.toEuclideanLin (vertices i))
    refine ⟨?_, ?_, ?_, ?_⟩
    · apply all_fin_8_vec <;> norm_num
    · simp [Fin.sum_univ_eight]; norm_num
    · exact fun i ↦ ⟨i, rfl⟩
    · simp only [projXy, outerRot, matrixOfQuat, outerQuat, vertices,
                 Fin.sum_univ_eight, matrix_simps]
      ext i; fin_cases i <;> norm_num

theorem rupert : IsRupert vertices := by
  rw [rupert_iff_rupert']
  use innerRot, innerRot_so3, innerOffset, outerRot, outerRot_so3
  intro inner_shadow outerShadow
  let ε₀ : ℝ := 0.006
  have hε₀ : ε₀ ∈ Set.Ioo 0 1 := by norm_num
  have hb : Metric.ball 0 ε₀ ⊆ convexHull ℝ outerShadow := by
    simpa [ε₀, outerShadow] using outer_ball_subset
  intro v hv
  let ε₁ : ℝ := 1e-11
  have hε₁ : ε₁ ∈ Set.Ioo 0 1 := by norm_num
  refine Convex.mem_interior_hull hε₀.1 hε₁ hb ?_
  simp only [inner_shadow] at hv
  obtain ⟨y, hy⟩ := hv
  rw [mem_convexHull_iff_exists_fintype]
  fin_cases y <;>
    simp only [vertices, Fin.reduceFinMk, Matrix.cons_val] at hy <;>
    use Fin 8, Fin.fintype 8
  <;> [
    use ![320050956502833201167751985054675539223111361/
          158836228761182627011085302790150062539835294740000,
          37478789684155822552149249633100762035628799779/
          158836228761182627011085302790150062539835294740000,
          0,
          2646640498675699472588866429808865118371007380481/
          2647270479353043783518088379835834375663921579000,
          0, 0, 0, 0];
    use ![2690065380721338931107844675930079853008002249/
          1429526058850643643099767725111350562858517652660000,
          1429185801354497250493132886580886682858320659198011/
          1429526058850643643099767725111350562858517652660000,
          0,
          5626123846094521128395511429799165339066424329/
          23825434314177394051662795418522509380975294211000,
          0, 0, 0, 0];
    use ![282844578280123522478732365155221962237373746450249/
          298290854644984786267344341448022649016038391108000,
          0, 0, 0,
          1716079538871724601954309613272108094228427903699/
          33143428293887198474149371272002516557337599012000,
          0,
          78025750787118551159488667585696530439676223/
          14914542732249239313367217072401132450801919555400,
          0];
    use ![283117566838487610246913017563019376237373746450249/
          298290854644984786267344341448022649016038391108000,
          0, 0, 0,
          1574537650882650012051296636476848055851133291/
          298290854644984786267344341448022649016038391108000,
          0,
          758585663442314668520963629418339796530439676223/
          14914542732249239313367217072401132450801919555400,
          0];
    use ![15381264075549739501273188093551493041527383361/
          33143428293887198474149371272002516557337599012000,
          0, 0, 0,
          99383630567848375480456938122952631882685283711097/
          99430284881661595422448113816007549672012797036000,
          0,
          25526079328536174367806438713165510146558741/
          4971514244083079771122405690800377483600639851800,
          0];
    use ![31436375570010867744955561974649501075539223111361/
          158836228761182627011085302790150062539835294740000,
          65162484389967530498892502615908096362035628799779/
          158836228761182627011085302790150062539835294740000,
          0,
          3111868440060211438361861909979623255113022141443/
          7941811438059131350554265139507503126991764737000,
          0, 0, 0, 0];
    use ![31418176332786595227076851814129673475539223111361/
          158836228761182627011085302790150062539835294740000,
          62237357220617638995747652173682152362035628799779/
          158836228761182627011085302790150062539835294740000,
          0,
          1086344920129639879804346646705637278371007380481/
          2647270479353043783518088379835834375663921579000,
          0, 0, 0, 0];
    use ![46105713581088386527939179642742079124582150083/
          99430284881661595422448113816007549672012797036000,
          0, 0, 0,
          499295037844618876866011627687882685283711097/
          99430284881661595422448113816007549672012797036000,
          0,
          4969183993652133120852165431236855985510146558741/
          4971514244083079771122405690800377483600639851800,
          0]
  ]
  all_goals
    use fun i ↦ (1 - ε₁) • (projXy (outerRot.toEuclideanLin (vertices i)))
    refine ⟨?_, ?_, ?_, ?_⟩
    · apply all_fin_8_vec <;> norm_num
    · simp only [Fin.sum_univ_eight, matrix_simps]; norm_num
    · exact fun i ↦ ⟨projXy (outerRot.toEuclideanLin (vertices i)), by simp [outerShadow]⟩
    · rw [←hy]
      simp only [projXy, outerRot, matrixOfQuat, outerQuat, vertices,
        Fin.sum_univ_eight, innerOffset, innerRot, innerQuat, ε₁, matrix_simps]
      ext i; fin_cases i <;> norm_num

end TriakisTetrahedron
