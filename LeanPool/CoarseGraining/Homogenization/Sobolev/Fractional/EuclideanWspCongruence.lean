/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

import LeanPool.CoarseGraining.Homogenization.Sobolev.Fractional.CongruenceAE
import LeanPool.CoarseGraining.Homogenization.Sobolev.Fractional.EuclideanWsp

/-!
# Almost-everywhere congruence for Euclidean fractional `W^{s,p}`

The Euclidean finite-exponent fractional kernel and its associated seminorm,
membership predicate, and full power norm depend only on the normalized-cube
almost-everywhere representative of the field.
-/

namespace Homogenization

open MeasureTheory
open scoped ENNReal

noncomputable section

/-- Modifying a Euclidean field on a normalized-cube null set modifies its
fractional `W^{s,p}` kernel only on a Gagliardo product-measure null set. -/
theorem cubeEuclideanWspKernel_congr_ae {d : ℕ} {Q : TriadicCube d}
    {s : FractionalOrder} {p : FiniteLpExponent} {F G : Vec d → Vec d}
    (hFG : F =ᵐ[normalizedCubeMeasure Q] G) :
    cubeEuclideanWspKernel s p F =ᵐ[Gagliardo.gagliardoCubeMeasure Q]
      cubeEuclideanWspKernel s p G := by
  have : SFinite (cubeMeasure Q) := by
    unfold cubeMeasure
    infer_instance
  have hcube : F =ᵐ[cubeMeasure Q] G :=
    Gagliardo.ae_normalizedCubeMeasure_iff.mp hFG
  have hfst : (fun z : Vec d × Vec d => F z.1) =ᵐ[Gagliardo.gagliardoCubeMeasure Q]
      fun z => G z.1 := by
    rw [Gagliardo.gagliardoCubeMeasure]
    exact Measure.quasiMeasurePreserving_fst.ae_eq hFG
  have hsnd : (fun z : Vec d × Vec d => F z.2) =ᵐ[Gagliardo.gagliardoCubeMeasure Q]
      fun z => G z.2 := by
    rw [Gagliardo.gagliardoCubeMeasure]
    exact Measure.quasiMeasurePreserving_snd.ae_eq hcube
  filter_upwards [hfst, hsnd] with z hzfst hzsnd
  rw [cubeEuclideanWspKernel_apply, cubeEuclideanWspKernel_apply, hzfst, hzsnd]

/-- The Euclidean fractional `W^{s,p}` seminorm depends only on the
normalized-cube almost-everywhere representative. -/
theorem cubeEuclideanWspESeminorm_congr_ae {d : ℕ} {Q : TriadicCube d}
    {s : FractionalOrder} {p : FiniteLpExponent} {F G : Vec d → Vec d}
    (hFG : F =ᵐ[normalizedCubeMeasure Q] G) :
    cubeEuclideanWspESeminorm Q s p F = cubeEuclideanWspESeminorm Q s p G := by
  unfold cubeEuclideanWspESeminorm
  exact eLpNorm_congr_ae (cubeEuclideanWspKernel_congr_ae hFG)

/-- Euclidean fractional `W^{s,p}` membership is invariant under
normalized-cube almost-everywhere replacement. -/
theorem memCubeEuclideanWsp_congr_ae {d : ℕ} {Q : TriadicCube d}
    {s : FractionalOrder} {p : FiniteLpExponent} {F G : Vec d → Vec d}
    (hFG : F =ᵐ[normalizedCubeMeasure Q] G) :
    MemCubeEuclideanWsp Q s p F ↔ MemCubeEuclideanWsp Q s p G :=
  memLp_congr_ae (cubeEuclideanWspKernel_congr_ae hFG)

/-- The normalized Euclidean `L^p` term on a cube is invariant under
normalized-cube almost-everywhere replacement. -/
theorem cubeEuclideanNormalizedLpENorm_congr_ae {d : ℕ} (Q : TriadicCube d)
    (p : ℝ≥0∞) {F G : Vec d → Vec d}
    (hFG : F =ᵐ[normalizedCubeMeasure Q] G) :
    (cubeBoundedMeasurableDomain Q).normalizedEuclideanLpENorm p F =
      (cubeBoundedMeasurableDomain Q).normalizedEuclideanLpENorm p G := by
  apply (cubeBoundedMeasurableDomain Q).normalizedEuclideanLpENorm_congr_ae
  rw [cubeBoundedMeasurableDomain_normalizedVolume_eq_normalizedCubeMeasure]
  exact hFG

/-- The Euclidean fractional full power norm depends only on the
normalized-cube almost-everywhere representative. -/
theorem cubeEuclideanWspFullENorm_congr_ae {d : ℕ} {Q : TriadicCube d}
    {s : FractionalOrder} {p : FiniteLpExponent} {F G : Vec d → Vec d}
    (hFG : F =ᵐ[normalizedCubeMeasure Q] G) :
    cubeEuclideanWspFullENorm Q s p F = cubeEuclideanWspFullENorm Q s p G := by
  unfold cubeEuclideanWspFullENorm
  rw [cubeEuclideanNormalizedLpENorm_congr_ae Q p.exponent hFG,
    cubeEuclideanWspESeminorm_congr_ae hFG]

end
