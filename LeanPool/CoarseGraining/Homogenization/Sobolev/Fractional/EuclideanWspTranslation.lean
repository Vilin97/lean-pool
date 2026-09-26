/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/
module


public import LeanPool.CoarseGraining.Homogenization.Sobolev.Fractional.EuclideanWsp
public import LeanPool.CoarseGraining.Homogenization.Sobolev.Fractional.DefinitionsAPI

/-!
# Triadic translation covariance for finite-p Euclidean fractional norms

The translation is represented by the lattice vector attached to
`translateCube`.  All identities preserve the normalized measures exactly.
-/

@[expose] public section

namespace Homogenization

open MeasureTheory
open scoped ENNReal

noncomputable section

/-- Translation by the lattice shift, as a measurable equivalence of Euclidean space. -/
noncomputable def euclideanWspTranslationEquiv {d : ℕ}
    (shift : Fin d → ℤ) (Q : TriadicCube d) : Vec d ≃ᵐ Vec d :=
  MeasurableEquiv.addRight (Gagliardo.cubeShiftVector shift Q)

private theorem euclideanWspTranslation_measurePreserving {d : ℕ}
    (shift : Fin d → ℤ) (Q : TriadicCube d) :
    MeasurePreserving (euclideanWspTranslationEquiv shift Q)
      (normalizedCubeMeasure Q)
      (normalizedCubeMeasure (translateCube shift Q)) := by
  let v := Gagliardo.cubeShiftVector shift Q
  let T := euclideanWspTranslationEquiv shift Q
  have hTapp : ∀ x, T x = x + v := fun x => rfl
  have hmapT : Measure.map T volume = volume := by
    have hco : (T : Vec d → Vec d) = (· + v) := rfl
    rw [hco]
    exact (measurePreserving_add_right volume v).map_eq
  have hpre : (T : Vec d → Vec d) ⁻¹' cubeSet (translateCube shift Q) = cubeSet Q := by
    ext x
    simp only [Set.mem_preimage, hTapp, mem_cubeSet_translateCube_iff]
    have hx : x + v - (fun i => (shift i : ℝ) * cubeScaleFactor Q) = x := by
      funext i
      simp [v, Gagliardo.cubeShiftVector]
    rw [hx]
  have hres : volume.restrict (cubeSet (translateCube shift Q)) =
      Measure.map T (volume.restrict (cubeSet Q)) := by
    rw [← hpre, ← Measure.restrict_map T.measurable
      (measurableSet_cubeSet (translateCube shift Q)), hmapT]
  have hvol : cubeVolume (translateCube shift Q) = cubeVolume Q := rfl
  refine ⟨T.measurable, ?_⟩
  rw [normalizedCubeMeasure, normalizedCubeMeasure, cubeMeasure, cubeMeasure,
    hvol, hres, Measure.map_smul _ T.measurable.aemeasurable]

private theorem euclideanWspTranslation_pair_measurePreserving {d : ℕ}
    (shift : Fin d → ℤ) (Q : TriadicCube d) :
    MeasurePreserving
      ((euclideanWspTranslationEquiv shift Q).prodCongr
        (euclideanWspTranslationEquiv shift Q))
      (Gagliardo.gagliardoCubeMeasure Q)
      (Gagliardo.gagliardoCubeMeasure (translateCube shift Q)) := by
  let T := euclideanWspTranslationEquiv shift Q
  have hT := euclideanWspTranslation_measurePreserving shift Q
  have hTapp : ∀ x, T x = x + Gagliardo.cubeShiftVector shift Q := fun x => rfl
  have hvol : cubeVolume (translateCube shift Q) = cubeVolume Q := rfl
  have hmap : normalizedCubeMeasure (translateCube shift Q) =
      Measure.map T (normalizedCubeMeasure Q) := by
    simpa [T] using hT.map_eq.symm
  have hres : cubeMeasure (translateCube shift Q) =
      Measure.map T (cubeMeasure Q) := by
    have hpre : (T : Vec d → Vec d) ⁻¹' cubeSet (translateCube shift Q) = cubeSet Q := by
      ext x
      simp only [Set.mem_preimage, hTapp, mem_cubeSet_translateCube_iff]
      have hx : x + Gagliardo.cubeShiftVector shift Q -
          (fun i => (shift i : ℝ) * cubeScaleFactor Q) = x := by
        funext i
        simp [Gagliardo.cubeShiftVector]
      rw [hx]
    have hmapT : Measure.map T volume = volume := by
      change Measure.map (· + Gagliardo.cubeShiftVector shift Q) volume = volume
      exact (measurePreserving_add_right volume _).map_eq
    rw [cubeMeasure, cubeMeasure, ← hpre, ← Measure.restrict_map T.measurable
      (measurableSet_cubeSet (translateCube shift Q)), hmapT]
  have : SFinite (cubeMeasure Q) := by
    unfold cubeMeasure
    infer_instance
  refine ⟨(T.prodCongr T).measurable, ?_⟩
  rw [Gagliardo.gagliardoCubeMeasure, Gagliardo.gagliardoCubeMeasure, hmap, hres,
    Measure.map_prod_map _ _ T.measurable T.measurable]
  rfl

/-- Pointwise covariance of the Euclidean fractional kernel under translating
both variables by the triadic lattice vector. -/
theorem cubeEuclideanWspKernel_translate {d : ℕ}
    (shift : Fin d → ℤ) (Q : TriadicCube d) (s : FractionalOrder)
    (p : FiniteLpExponent) (F : Vec d → Vec d) (z : Vec d × Vec d) :
    cubeEuclideanWspKernel s p F
        (((euclideanWspTranslationEquiv shift Q).prodCongr
          (euclideanWspTranslationEquiv shift Q)) z) =
      cubeEuclideanWspKernel s p
        (fun x => F (x + Gagliardo.cubeShiftVector shift Q)) z := by
  change cubeEuclideanWspKernel s p F
      (z.1 + Gagliardo.cubeShiftVector shift Q,
        z.2 + Gagliardo.cubeShiftVector shift Q) = _
  rw [cubeEuclideanWspKernel_apply, cubeEuclideanWspKernel_apply,
    euclideanDist_add_right]

/-- Exact covariance of the normalized Euclidean `L^p` term under a triadic
lattice translation. -/
theorem cubeEuclideanNormalizedLpENorm_translate {d : ℕ}
    (shift : Fin d → ℤ) (Q : TriadicCube d) (p : FiniteLpExponent)
    (F : Vec d → Vec d) :
    (cubeBoundedMeasurableDomain (translateCube shift Q)).normalizedEuclideanLpENorm
        p.exponent F =
      (cubeBoundedMeasurableDomain Q).normalizedEuclideanLpENorm p.exponent
        (fun x => F (x + Gagliardo.cubeShiftVector shift Q)) := by
  let T := euclideanWspTranslationEquiv shift Q
  have hMP := euclideanWspTranslation_measurePreserving shift Q
  unfold BoundedMeasurableDomain.normalizedEuclideanLpENorm
  unfold BoundedMeasurableDomain.normalizedLpENorm
  rw [cubeBoundedMeasurableDomain_normalizedVolume_eq_normalizedCubeMeasure,
    cubeBoundedMeasurableDomain_normalizedVolume_eq_normalizedCubeMeasure]
  simp only [ite_eq_right (ne_of_gt (lt_trans zero_lt_one p.one_lt)),
    ite_eq_right p.lt_top.ne, eLpNorm'_eq_lintegral_enorm]
  congr 1
  rw [MeasurePreserving.lintegral_map_equiv _ T hMP]
  rfl

/-- Exact covariance of the Euclidean fractional seminorm under a triadic
lattice translation. -/
theorem cubeEuclideanWspESeminorm_translate {d : ℕ}
    (shift : Fin d → ℤ) (Q : TriadicCube d) (s : FractionalOrder)
    (p : FiniteLpExponent) (F : Vec d → Vec d) :
    cubeEuclideanWspESeminorm (translateCube shift Q) s p F =
      cubeEuclideanWspESeminorm Q s p
        (fun x => F (x + Gagliardo.cubeShiftVector shift Q)) := by
  let T := euclideanWspTranslationEquiv shift Q
  let TP := T.prodCongr T
  have hMP := euclideanWspTranslation_pair_measurePreserving shift Q
  rw [cubeEuclideanWspESeminorm_eq_lintegral,
    cubeEuclideanWspESeminorm_eq_lintegral]
  congr 1
  rw [MeasurePreserving.lintegral_map_equiv _ TP hMP]
  refine lintegral_congr fun z => ?_
  rw [cubeEuclideanWspKernel_translate]

/-- Fractional Sobolev membership is exactly transported by a triadic lattice
translation. -/
theorem memCubeEuclideanWsp_translate_iff {d : ℕ}
    (shift : Fin d → ℤ) (Q : TriadicCube d) (s : FractionalOrder)
    (p : FiniteLpExponent) (F : Vec d → Vec d) :
    MemCubeEuclideanWsp (translateCube shift Q) s p F ↔
      MemCubeEuclideanWsp Q s p
        (fun x => F (x + Gagliardo.cubeShiftVector shift Q)) := by
  let T := euclideanWspTranslationEquiv shift Q
  let TP := T.prodCongr T
  have hMP := euclideanWspTranslation_pair_measurePreserving shift Q
  have hker : cubeEuclideanWspKernel s p
      (fun x => F (x + Gagliardo.cubeShiftVector shift Q)) =
      cubeEuclideanWspKernel s p F ∘ TP := by
    funext z
    symm
    exact cubeEuclideanWspKernel_translate shift Q s p F z
  rw [memCubeEuclideanWsp_iff, memCubeEuclideanWsp_iff]
  constructor
  · rintro ⟨hmeas, hfinite⟩
    constructor
    · rw [hker]
      exact (hMP.aestronglyMeasurable_comp_iff TP.measurableEmbedding).2 hmeas
    · change cubeEuclideanWspESeminorm Q s p
          (fun x => F (x + Gagliardo.cubeShiftVector shift Q)) < ∞
      rwa [← cubeEuclideanWspESeminorm_translate shift Q s p F]
  · rintro ⟨hmeas, hfinite⟩
    constructor
    · apply (hMP.aestronglyMeasurable_comp_iff TP.measurableEmbedding).1
      rw [← hker]
      exact hmeas
    · change cubeEuclideanWspESeminorm (translateCube shift Q) s p F < ∞
      rwa [cubeEuclideanWspESeminorm_translate shift Q s p F]

/-- Exact covariance of the full normalized Euclidean fractional power norm
under a triadic lattice translation. -/
theorem cubeEuclideanWspFullENorm_translate {d : ℕ}
    (shift : Fin d → ℤ) (Q : TriadicCube d) (s : FractionalOrder)
    (p : FiniteLpExponent) (F : Vec d → Vec d) :
    cubeEuclideanWspFullENorm (translateCube shift Q) s p F =
      cubeEuclideanWspFullENorm Q s p
        (fun x => F (x + Gagliardo.cubeShiftVector shift Q)) := by
  unfold cubeEuclideanWspFullENorm
  rw [show cubeEuclideanWspScalePowerWeight (translateCube shift Q) s p =
      cubeEuclideanWspScalePowerWeight Q s p by
        unfold cubeEuclideanWspScalePowerWeight
        rw [cubeScaleFactor_translateCube],
    cubeEuclideanNormalizedLpENorm_translate,
    cubeEuclideanWspESeminorm_translate]

end

end Homogenization
