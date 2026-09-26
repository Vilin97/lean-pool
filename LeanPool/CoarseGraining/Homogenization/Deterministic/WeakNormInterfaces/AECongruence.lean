/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/
module


public import LeanPool.CoarseGraining.Homogenization.Deterministic.WeakNormInterfacesQTwo

/-! # AECongruence -/

@[expose] public section

namespace Homogenization

noncomputable section

open scoped BigOperators

theorem cubeAverage_eq_of_ae_eq_on_cubeSet {d : ℕ} {Q : TriadicCube d}
    {f g : Vec d → ℝ}
    (hfg : f =ᵐ[MeasureTheory.volume.restrict (cubeSet Q)] g) :
    cubeAverage Q f = cubeAverage Q g := by
  unfold cubeAverage
  congr 1
  exact MeasureTheory.integral_congr_ae hfg

theorem cubeAverageVec_eq_of_ae_eq_on_cubeSet {d : ℕ} {Q : TriadicCube d}
    {f g : Vec d → Vec d}
    (hfg : f =ᵐ[MeasureTheory.volume.restrict (cubeSet Q)] g) :
    cubeAverageVec Q f = cubeAverageVec Q g := by
  funext i
  exact cubeAverage_eq_of_ae_eq_on_cubeSet
    (hfg.mono fun x hx => congrArg (fun v : Vec d => v i) hx)

theorem cubeBesovNegativeVectorDepthAverage_eq_of_ae_eq_on_cubeSet
    {d : ℕ} {Q : TriadicCube d} {u v : Vec d → Vec d}
    (huv : u =ᵐ[MeasureTheory.volume.restrict (cubeSet Q)] v) (j : ℕ) :
    cubeBesovNegativeVectorDepthAverage Q u j =
      cubeBesovNegativeVectorDepthAverage Q v j := by
  unfold cubeBesovNegativeVectorDepthAverage descendantsAverage
  refine congrArg (fun t : ℝ => ((descendantsAtDepth Q j).card : ℝ)⁻¹ * t) ?_
  refine Finset.sum_congr rfl ?_
  intro R hR
  have hle :
      MeasureTheory.volume.restrict (cubeSet R) ≤
        MeasureTheory.volume.restrict (cubeSet Q) :=
    MeasureTheory.Measure.restrict_mono_set MeasureTheory.volume
      (cubeSet_subset_of_mem_descendantsAtDepth hR)
  have huvR : u =ᵐ[MeasureTheory.volume.restrict (cubeSet R)] v :=
    huv.filter_mono (MeasureTheory.ae_mono hle)
  exact congrArg vecNormSq <| cubeAverageVec_eq_of_ae_eq_on_cubeSet huvR

theorem cubeBesovNegativeVectorDepthSeminorm_eq_of_ae_eq_on_cubeSet
    {d : ℕ} {Q : TriadicCube d} {u v : Vec d → Vec d}
    (s : ℝ) (huv : u =ᵐ[MeasureTheory.volume.restrict (cubeSet Q)] v) (j : ℕ) :
    cubeBesovNegativeVectorDepthSeminorm Q s u j =
      cubeBesovNegativeVectorDepthSeminorm Q s v j := by
  unfold cubeBesovNegativeVectorDepthSeminorm
  rw [cubeBesovNegativeVectorDepthAverage_eq_of_ae_eq_on_cubeSet huv]

theorem cubeBesovNegativeVectorPartialSeminorm_eq_of_ae_eq_on_cubeSet
    {d : ℕ} {Q : TriadicCube d} {u v : Vec d → Vec d}
    (s : ℝ) (N : ℕ)
    (huv : u =ᵐ[MeasureTheory.volume.restrict (cubeSet Q)] v) :
    cubeBesovNegativeVectorPartialSeminorm Q s N u =
      cubeBesovNegativeVectorPartialSeminorm Q s N v := by
  unfold cubeBesovNegativeVectorPartialSeminorm
  refine Finset.sum_congr rfl ?_
  intro j _hj
  rw [cubeBesovNegativeVectorDepthSeminorm_eq_of_ae_eq_on_cubeSet s huv j]

theorem cubeBesovNegativeVectorSeminorm_eq_of_ae_eq_on_cubeSet
    {d : ℕ} {Q : TriadicCube d} {u v : Vec d → Vec d}
    (s : ℝ) (huv : u =ᵐ[MeasureTheory.volume.restrict (cubeSet Q)] v) :
    cubeBesovNegativeVectorSeminorm Q s u =
      cubeBesovNegativeVectorSeminorm Q s v := by
  unfold cubeBesovNegativeVectorSeminorm
  apply congrArg sSup
  ext y
  constructor
  · rintro ⟨N, rfl⟩
    exact ⟨N, (cubeBesovNegativeVectorPartialSeminorm_eq_of_ae_eq_on_cubeSet
      (Q := Q) (u := u) (v := v) s N huv).symm⟩
  · rintro ⟨N, rfl⟩
    exact ⟨N, cubeBesovNegativeVectorPartialSeminorm_eq_of_ae_eq_on_cubeSet
      (Q := Q) (u := u) (v := v) s N huv⟩

theorem cubeBesovNegativeVectorPartialSeminormTwo_eq_of_ae_eq_on_cubeSet
    {d : ℕ} {Q : TriadicCube d} {u v : Vec d → Vec d}
    (s : ℝ) (N : ℕ)
    (huv : u =ᵐ[MeasureTheory.volume.restrict (cubeSet Q)] v) :
    cubeBesovNegativeVectorPartialSeminormTwo Q s N u =
      cubeBesovNegativeVectorPartialSeminormTwo Q s N v := by
  unfold cubeBesovNegativeVectorPartialSeminormTwo
  congr 1
  refine Finset.sum_congr rfl ?_
  intro j _hj
  rw [cubeBesovNegativeVectorDepthSeminorm_eq_of_ae_eq_on_cubeSet s huv j]

theorem cubeBesovNegativeVectorSeminormTwo_eq_of_ae_eq_on_cubeSet
    {d : ℕ} {Q : TriadicCube d} {u v : Vec d → Vec d}
    (s : ℝ) (huv : u =ᵐ[MeasureTheory.volume.restrict (cubeSet Q)] v) :
    cubeBesovNegativeVectorSeminormTwo Q s u =
      cubeBesovNegativeVectorSeminormTwo Q s v := by
  unfold cubeBesovNegativeVectorSeminormTwo
  apply congrArg sSup
  ext y
  constructor
  · rintro ⟨N, rfl⟩
    exact ⟨N, (cubeBesovNegativeVectorPartialSeminormTwo_eq_of_ae_eq_on_cubeSet
      (Q := Q) (u := u) (v := v) s N huv).symm⟩
  · rintro ⟨N, rfl⟩
    exact ⟨N, cubeBesovNegativeVectorPartialSeminormTwo_eq_of_ae_eq_on_cubeSet
      (Q := Q) (u := u) (v := v) s N huv⟩

@[simp] theorem cubeBesovNegativeVectorDepthAverage_zero {d : ℕ}
    (Q : TriadicCube d) (j : ℕ) :
    cubeBesovNegativeVectorDepthAverage Q (0 : Vec d → Vec d) j = 0 := by
  unfold cubeBesovNegativeVectorDepthAverage descendantsAverage
  have hsum :
      ∑ R ∈ descendantsAtDepth Q j,
          vecNormSq (cubeAverageVec R (0 : Vec d → Vec d)) = 0 := by
    refine Finset.sum_eq_zero ?_
    intro R _hR
    have havg : cubeAverageVec R (0 : Vec d → Vec d) = 0 := by
      funext i
      unfold cubeAverageVec cubeAverage
      simp
    rw [havg]
    exact vecNormSq_eq_zero_iff.mpr rfl
  simp [hsum]

@[simp] theorem cubeBesovNegativeVectorDepthSeminorm_zero {d : ℕ}
    (Q : TriadicCube d) (s : ℝ) (j : ℕ) :
    cubeBesovNegativeVectorDepthSeminorm Q s (0 : Vec d → Vec d) j = 0 := by
  unfold cubeBesovNegativeVectorDepthSeminorm
  simp

@[simp] theorem cubeBesovNegativeVectorPartialSeminormTwo_zero {d : ℕ}
    (Q : TriadicCube d) (s : ℝ) (N : ℕ) :
    cubeBesovNegativeVectorPartialSeminormTwo Q s N (0 : Vec d → Vec d) = 0 := by
  unfold cubeBesovNegativeVectorPartialSeminormTwo
  simp

@[simp] theorem cubeBesovNegativeVectorSeminormTwo_zero {d : ℕ}
    (Q : TriadicCube d) (s : ℝ) :
    cubeBesovNegativeVectorSeminormTwo Q s (0 : Vec d → Vec d) = 0 := by
  unfold cubeBesovNegativeVectorSeminormTwo
  rw [show Set.range (fun N : ℕ =>
      cubeBesovNegativeVectorPartialSeminormTwo Q s N (0 : Vec d → Vec d)) =
        ({0} : Set ℝ) by
    ext x
    constructor
    · rintro ⟨N, rfl⟩
      simp
    · intro hx
      refine ⟨0, ?_⟩
      calc
        cubeBesovNegativeVectorPartialSeminormTwo Q s 0 (0 : Vec d → Vec d) = 0 := by simp
        _ = x := hx.symm]
  simp

end

end Homogenization
