/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/
module


public import LeanPool.CoarseGraining.Homogenization.Geometry.CubeMeasure
public import LeanPool.CoarseGraining.Homogenization.Sobolev.Foundations.CubeReflection.Reflections
public import Mathlib.MeasureTheory.Group.Measure

/-! # Homeomorphism -/

@[expose] public section

namespace Homogenization

open MeasureTheory
open scoped BigOperators ENNReal Topology

noncomputable section

theorem injective_coordFaceReflection {d : ℕ}
    (a : ℝ) (i : Fin d) :
    Function.Injective (coordFaceReflection (d := d) a i) := by
  intro x y hxy
  have h := congrArg (coordFaceReflection a i) hxy
  simpa using h

def coordFaceReflectionHomeomorph {d : ℕ}
    (a : ℝ) (i : Fin d) : Vec d ≃ₜ Vec d where
  toFun := coordFaceReflection a i
  invFun := coordFaceReflection a i
  left_inv := coordFaceReflection_involutive a i
  right_inv := coordFaceReflection_involutive a i
  continuous_toFun := continuous_coordFaceReflection a i
  continuous_invFun := continuous_coordFaceReflection a i

def cubeUpperFaceReflectionHomeomorph {d : ℕ}
    (Q : TriadicCube d) (i : Fin d) : Vec d ≃ₜ Vec d :=
  coordFaceReflectionHomeomorph (cubeUpperFaceCoord Q i) i

def cubeLowerFaceReflectionHomeomorph {d : ℕ}
    (Q : TriadicCube d) (i : Fin d) : Vec d ≃ₜ Vec d :=
  coordFaceReflectionHomeomorph (cubeLowerFaceCoord Q i) i

theorem measurableEmbedding_coordFaceReflection {d : ℕ}
    (a : ℝ) (i : Fin d) :
    MeasurableEmbedding (coordFaceReflection (d := d) a i) :=
  (continuous_coordFaceReflection a i).measurableEmbedding
    (injective_coordFaceReflection a i)

theorem measurableEmbedding_cubeUpperFaceReflection {d : ℕ}
    (Q : TriadicCube d) (i : Fin d) :
    MeasurableEmbedding (cubeUpperFaceReflection Q i) := by
  simpa [cubeUpperFaceReflection] using
    measurableEmbedding_coordFaceReflection (d := d) (cubeUpperFaceCoord Q i) i

theorem measurableEmbedding_cubeLowerFaceReflection {d : ℕ}
    (Q : TriadicCube d) (i : Fin d) :
    MeasurableEmbedding (cubeLowerFaceReflection Q i) := by
  simpa [cubeLowerFaceReflection] using
    measurableEmbedding_coordFaceReflection (d := d) (cubeLowerFaceCoord Q i) i

theorem preimage_cubeUpperFaceReflection_openCubeSet {d : ℕ}
    (Q : TriadicCube d) (i : Fin d) :
    cubeUpperFaceReflection Q i ⁻¹' openCubeSet Q =
      openCubeSet (cubeUpperFaceNeighbor Q i) := by
  ext x
  constructor
  · intro hx
    have hmem :=
      cubeUpperFaceReflection_mem_neighbor_of_mem_openCubeSet Q i (x := cubeUpperFaceReflection Q i x) hx
    simpa [cubeUpperFaceReflection] using hmem
  · intro hx
    exact cubeUpperFaceReflection_mem_openCubeSet_of_mem_neighbor Q i hx

theorem preimage_cubeUpperFaceReflection_neighbor {d : ℕ}
    (Q : TriadicCube d) (i : Fin d) :
    cubeUpperFaceReflection Q i ⁻¹' openCubeSet (cubeUpperFaceNeighbor Q i) =
      openCubeSet Q := by
  ext x
  constructor
  · intro hx
    have hmem :=
      cubeUpperFaceReflection_mem_openCubeSet_of_mem_neighbor Q i
        (x := cubeUpperFaceReflection Q i x) hx
    simpa [cubeUpperFaceReflection] using hmem
  · intro hx
    exact cubeUpperFaceReflection_mem_neighbor_of_mem_openCubeSet Q i hx

theorem preimage_cubeLowerFaceReflection_openCubeSet {d : ℕ}
    (Q : TriadicCube d) (i : Fin d) :
    cubeLowerFaceReflection Q i ⁻¹' openCubeSet Q =
      openCubeSet (cubeLowerFaceNeighbor Q i) := by
  ext x
  constructor
  · intro hx
    have hmem :=
      cubeLowerFaceReflection_mem_neighbor_of_mem_openCubeSet Q i (x := cubeLowerFaceReflection Q i x) hx
    simpa [cubeLowerFaceReflection] using hmem
  · intro hx
    exact cubeLowerFaceReflection_mem_openCubeSet_of_mem_neighbor Q i hx

theorem preimage_cubeLowerFaceReflection_neighbor {d : ℕ}
    (Q : TriadicCube d) (i : Fin d) :
    cubeLowerFaceReflection Q i ⁻¹' openCubeSet (cubeLowerFaceNeighbor Q i) =
      openCubeSet Q := by
  ext x
  constructor
  · intro hx
    have hmem :=
      cubeLowerFaceReflection_mem_openCubeSet_of_mem_neighbor Q i
        (x := cubeLowerFaceReflection Q i x) hx
    simpa [cubeLowerFaceReflection] using hmem
  · intro hx
    exact cubeLowerFaceReflection_mem_neighbor_of_mem_openCubeSet Q i hx

theorem setIntegral_cubeUpperFaceNeighbor_comp_reflection {d : ℕ}
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (Q : TriadicCube d) (i : Fin d) (g : Vec d → E) :
    ∫ x in openCubeSet (cubeUpperFaceNeighbor Q i),
        g (cubeUpperFaceReflection Q i x) ∂volume =
      ∫ y in openCubeSet Q, g y ∂volume := by
  rw [← preimage_cubeUpperFaceReflection_openCubeSet Q i]
  exact (measurePreserving_cubeUpperFaceReflection Q i).setIntegral_preimage_emb
    (measurableEmbedding_cubeUpperFaceReflection Q i) g (openCubeSet Q)

theorem setIntegral_openCubeSet_comp_cubeUpperFaceReflection {d : ℕ}
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (Q : TriadicCube d) (i : Fin d) (g : Vec d → E) :
    ∫ x in openCubeSet Q, g (cubeUpperFaceReflection Q i x) ∂volume =
      ∫ y in openCubeSet (cubeUpperFaceNeighbor Q i), g y ∂volume := by
  rw [← preimage_cubeUpperFaceReflection_neighbor Q i]
  exact (measurePreserving_cubeUpperFaceReflection Q i).setIntegral_preimage_emb
    (measurableEmbedding_cubeUpperFaceReflection Q i) g
    (openCubeSet (cubeUpperFaceNeighbor Q i))

theorem setIntegral_cubeLowerFaceNeighbor_comp_reflection {d : ℕ}
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (Q : TriadicCube d) (i : Fin d) (g : Vec d → E) :
    ∫ x in openCubeSet (cubeLowerFaceNeighbor Q i),
        g (cubeLowerFaceReflection Q i x) ∂volume =
      ∫ y in openCubeSet Q, g y ∂volume := by
  rw [← preimage_cubeLowerFaceReflection_openCubeSet Q i]
  exact (measurePreserving_cubeLowerFaceReflection Q i).setIntegral_preimage_emb
    (measurableEmbedding_cubeLowerFaceReflection Q i) g (openCubeSet Q)

theorem setIntegral_openCubeSet_comp_cubeLowerFaceReflection {d : ℕ}
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (Q : TriadicCube d) (i : Fin d) (g : Vec d → E) :
    ∫ x in openCubeSet Q, g (cubeLowerFaceReflection Q i x) ∂volume =
      ∫ y in openCubeSet (cubeLowerFaceNeighbor Q i), g y ∂volume := by
  rw [← preimage_cubeLowerFaceReflection_neighbor Q i]
  exact (measurePreserving_cubeLowerFaceReflection Q i).setIntegral_preimage_emb
    (measurableEmbedding_cubeLowerFaceReflection Q i) g
    (openCubeSet (cubeLowerFaceNeighbor Q i))

/-- Integrability of a reflected scalar forcing/test product transports from
`Q` to the upper face neighbor. -/
theorem integrable_cubeUpperFaceNeighbor_reflectedScalar_mul {d : ℕ}
    {F φ : Vec d → ℝ} (Q : TriadicCube d) (i : Fin d)
    (hreflected :
      MeasureTheory.Integrable
        (fun y => F y * φ (cubeUpperFaceReflection Q i y))
        (volume.restrict (openCubeSet Q))) :
    MeasureTheory.Integrable
      (fun x => F (cubeUpperFaceReflection Q i x) * φ x)
      (volume.restrict (openCubeSet (cubeUpperFaceNeighbor Q i))) := by
  let B : Vec d → ℝ := fun x => F (cubeUpperFaceReflection Q i x) * φ x
  have hcomp :
      MeasureTheory.Integrable
        (fun y => B (cubeUpperFaceReflection Q i y))
        (volume.restrict (openCubeSet Q)) := by
    refine hreflected.congr ?_
    filter_upwards with y
    simp [B]
  have hpre :
      MeasureTheory.IntegrableOn
        (fun y => B (cubeUpperFaceReflection Q i y))
        (cubeUpperFaceReflection Q i ⁻¹'
          openCubeSet (cubeUpperFaceNeighbor Q i)) volume := by
    simpa [MeasureTheory.IntegrableOn,
      preimage_cubeUpperFaceReflection_neighbor Q i] using hcomp
  have hiff := MeasureTheory.MeasurePreserving.integrableOn_comp_preimage
    (measurePreserving_cubeUpperFaceReflection Q i)
    (measurableEmbedding_cubeUpperFaceReflection Q i)
    (f := B) (s := openCubeSet (cubeUpperFaceNeighbor Q i))
  have hB :
      MeasureTheory.IntegrableOn B
        (openCubeSet (cubeUpperFaceNeighbor Q i)) volume :=
    hiff.mp hpre
  simpa [MeasureTheory.IntegrableOn, B] using hB

/-- Integrability of a reflected scalar forcing/test product transports from
`Q` to the lower face neighbor. -/
theorem integrable_cubeLowerFaceNeighbor_reflectedScalar_mul {d : ℕ}
    {F φ : Vec d → ℝ} (Q : TriadicCube d) (i : Fin d)
    (hreflected :
      MeasureTheory.Integrable
        (fun y => F y * φ (cubeLowerFaceReflection Q i y))
        (volume.restrict (openCubeSet Q))) :
    MeasureTheory.Integrable
      (fun x => F (cubeLowerFaceReflection Q i x) * φ x)
      (volume.restrict (openCubeSet (cubeLowerFaceNeighbor Q i))) := by
  let B : Vec d → ℝ := fun x => F (cubeLowerFaceReflection Q i x) * φ x
  have hcomp :
      MeasureTheory.Integrable
        (fun y => B (cubeLowerFaceReflection Q i y))
        (volume.restrict (openCubeSet Q)) := by
    refine hreflected.congr ?_
    filter_upwards with y
    simp [B]
  have hpre :
      MeasureTheory.IntegrableOn
        (fun y => B (cubeLowerFaceReflection Q i y))
        (cubeLowerFaceReflection Q i ⁻¹'
          openCubeSet (cubeLowerFaceNeighbor Q i)) volume := by
    simpa [MeasureTheory.IntegrableOn,
      preimage_cubeLowerFaceReflection_neighbor Q i] using hcomp
  have hiff := MeasureTheory.MeasurePreserving.integrableOn_comp_preimage
    (measurePreserving_cubeLowerFaceReflection Q i)
    (measurableEmbedding_cubeLowerFaceReflection Q i)
    (f := B) (s := openCubeSet (cubeLowerFaceNeighbor Q i))
  have hB :
      MeasureTheory.IntegrableOn B
        (openCubeSet (cubeLowerFaceNeighbor Q i)) volume :=
    hiff.mp hpre
  simpa [MeasureTheory.IntegrableOn, B] using hB

/-- Scalar `L²` membership transports from `Q` to the upper face neighbor by
precomposition with the upper face reflection. -/
theorem memScalarL2_cubeUpperFaceNeighbor_comp_reflection {d : ℕ}
    {F : Vec d → ℝ} (Q : TriadicCube d) (i : Fin d)
    (hF : MemScalarL2 (openCubeSet Q) F) :
    MemScalarL2 (openCubeSet (cubeUpperFaceNeighbor Q i))
      (fun x => F (cubeUpperFaceReflection Q i x)) := by
  have hmp :=
    (measurePreserving_cubeUpperFaceReflection Q i).restrict_preimage_emb
      (measurableEmbedding_cubeUpperFaceReflection Q i) (openCubeSet Q)
  simpa [MemScalarL2, volumeMeasureOn,
    preimage_cubeUpperFaceReflection_openCubeSet Q i, Function.comp_def] using
    hF.comp_measurePreserving hmp

/-- Scalar `L²` membership transports from `Q` to the lower face neighbor by
precomposition with the lower face reflection. -/
theorem memScalarL2_cubeLowerFaceNeighbor_comp_reflection {d : ℕ}
    {F : Vec d → ℝ} (Q : TriadicCube d) (i : Fin d)
    (hF : MemScalarL2 (openCubeSet Q) F) :
    MemScalarL2 (openCubeSet (cubeLowerFaceNeighbor Q i))
      (fun x => F (cubeLowerFaceReflection Q i x)) := by
  have hmp :=
    (measurePreserving_cubeLowerFaceReflection Q i).restrict_preimage_emb
      (measurableEmbedding_cubeLowerFaceReflection Q i) (openCubeSet Q)
  simpa [MemScalarL2, volumeMeasureOn,
    preimage_cubeLowerFaceReflection_openCubeSet Q i, Function.comp_def] using
    hF.comp_measurePreserving hmp

/-- Vector `L²` membership transports from `Q` to the upper face neighbor under
the reflected vector-field rule. -/
theorem memVectorL2_cubeUpperFaceNeighbor_reflected {d : ℕ}
    {G : Vec d → Vec d} (Q : TriadicCube d) (i : Fin d)
    (hG : MemVectorL2 (openCubeSet Q) G) :
    MemVectorL2 (openCubeSet (cubeUpperFaceNeighbor Q i))
      (fun x => coordReflectionLinear i (G (cubeUpperFaceReflection Q i x))) := by
  have hmp :=
    (measurePreserving_cubeUpperFaceReflection Q i).restrict_preimage_emb
      (measurableEmbedding_cubeUpperFaceReflection Q i) (openCubeSet Q)
  have hcomp :
      MemVectorL2 (openCubeSet (cubeUpperFaceNeighbor Q i))
        (fun x => G (cubeUpperFaceReflection Q i x)) := by
    simpa [MemVectorL2, volumeMeasureOn,
      preimage_cubeUpperFaceReflection_openCubeSet Q i, Function.comp_def] using
      hG.comp_measurePreserving hmp
  simpa [Function.comp_def] using
    (coordReflectionLinear i).comp_memLp' hcomp

/-- Vector `L²` membership transports from `Q` to the lower face neighbor under
the reflected vector-field rule. -/
theorem memVectorL2_cubeLowerFaceNeighbor_reflected {d : ℕ}
    {G : Vec d → Vec d} (Q : TriadicCube d) (i : Fin d)
    (hG : MemVectorL2 (openCubeSet Q) G) :
    MemVectorL2 (openCubeSet (cubeLowerFaceNeighbor Q i))
      (fun x => coordReflectionLinear i (G (cubeLowerFaceReflection Q i x))) := by
  have hmp :=
    (measurePreserving_cubeLowerFaceReflection Q i).restrict_preimage_emb
      (measurableEmbedding_cubeLowerFaceReflection Q i) (openCubeSet Q)
  have hcomp :
      MemVectorL2 (openCubeSet (cubeLowerFaceNeighbor Q i))
        (fun x => G (cubeLowerFaceReflection Q i x)) := by
    simpa [MemVectorL2, volumeMeasureOn,
      preimage_cubeLowerFaceReflection_openCubeSet Q i, Function.comp_def] using
      hG.comp_measurePreserving hmp
  simpa [Function.comp_def] using
    (coordReflectionLinear i).comp_memLp' hcomp

/-- The scalar square integral is preserved when transported to the upper face
neighbor by reflection. -/
theorem setIntegral_cubeUpperFaceNeighbor_reflectedScalar_sq {d : ℕ}
    {F : Vec d → ℝ} (Q : TriadicCube d) (i : Fin d) :
    ∫ x in openCubeSet (cubeUpperFaceNeighbor Q i),
        F (cubeUpperFaceReflection Q i x) *
          F (cubeUpperFaceReflection Q i x) ∂volume =
      ∫ y in openCubeSet Q, F y * F y ∂volume := by
  simpa using
    setIntegral_cubeUpperFaceNeighbor_comp_reflection Q i
      (fun y => F y * F y)

/-- The scalar square integral is preserved when transported to the lower face
neighbor by reflection. -/
theorem setIntegral_cubeLowerFaceNeighbor_reflectedScalar_sq {d : ℕ}
    {F : Vec d → ℝ} (Q : TriadicCube d) (i : Fin d) :
    ∫ x in openCubeSet (cubeLowerFaceNeighbor Q i),
        F (cubeLowerFaceReflection Q i x) *
          F (cubeLowerFaceReflection Q i x) ∂volume =
      ∫ y in openCubeSet Q, F y * F y ∂volume := by
  simpa using
    setIntegral_cubeLowerFaceNeighbor_comp_reflection Q i
      (fun y => F y * F y)

/-- The vector self-pairing integral is preserved when the vector field is
reflected to the upper face neighbor. -/
theorem setIntegral_cubeUpperFaceNeighbor_reflectedField_self_pairing {d : ℕ}
    {G : Vec d → Vec d} (Q : TriadicCube d) (i : Fin d) :
    ∫ x in openCubeSet (cubeUpperFaceNeighbor Q i),
        vecDot
          (coordReflectionLinear i (G (cubeUpperFaceReflection Q i x)))
          (coordReflectionLinear i (G (cubeUpperFaceReflection Q i x)))
          ∂volume =
      ∫ y in openCubeSet Q, vecDot (G y) (G y) ∂volume := by
  calc
    ∫ x in openCubeSet (cubeUpperFaceNeighbor Q i),
        vecDot
          (coordReflectionLinear i (G (cubeUpperFaceReflection Q i x)))
          (coordReflectionLinear i (G (cubeUpperFaceReflection Q i x)))
          ∂volume
        = ∫ y in openCubeSet Q,
            vecDot (coordReflectionLinear i (G y))
              (coordReflectionLinear i (G y)) ∂volume := by
            simpa using
              setIntegral_cubeUpperFaceNeighbor_comp_reflection Q i
                (fun y =>
                  vecDot (coordReflectionLinear i (G y))
                    (coordReflectionLinear i (G y)))
    _ = ∫ y in openCubeSet Q, vecDot (G y) (G y) ∂volume := by
          refine MeasureTheory.setIntegral_congr_fun
            (measurableSet_openCubeSet Q) ?_
          intro y _hy
          exact vecDot_coordReflectionLinear_coordReflectionLinear i (G y) (G y)

/-- The vector self-pairing integral is preserved when the vector field is
reflected to the lower face neighbor. -/
theorem setIntegral_cubeLowerFaceNeighbor_reflectedField_self_pairing {d : ℕ}
    {G : Vec d → Vec d} (Q : TriadicCube d) (i : Fin d) :
    ∫ x in openCubeSet (cubeLowerFaceNeighbor Q i),
        vecDot
          (coordReflectionLinear i (G (cubeLowerFaceReflection Q i x)))
          (coordReflectionLinear i (G (cubeLowerFaceReflection Q i x)))
          ∂volume =
      ∫ y in openCubeSet Q, vecDot (G y) (G y) ∂volume := by
  calc
    ∫ x in openCubeSet (cubeLowerFaceNeighbor Q i),
        vecDot
          (coordReflectionLinear i (G (cubeLowerFaceReflection Q i x)))
          (coordReflectionLinear i (G (cubeLowerFaceReflection Q i x)))
          ∂volume
        = ∫ y in openCubeSet Q,
            vecDot (coordReflectionLinear i (G y))
              (coordReflectionLinear i (G y)) ∂volume := by
            simpa using
              setIntegral_cubeLowerFaceNeighbor_comp_reflection Q i
                (fun y =>
                  vecDot (coordReflectionLinear i (G y))
                    (coordReflectionLinear i (G y)))
    _ = ∫ y in openCubeSet Q, vecDot (G y) (G y) ∂volume := by
          refine MeasureTheory.setIntegral_congr_fun
            (measurableSet_openCubeSet Q) ?_
          intro y _hy
          exact vecDot_coordReflectionLinear_coordReflectionLinear i (G y) (G y)

end

end Homogenization
