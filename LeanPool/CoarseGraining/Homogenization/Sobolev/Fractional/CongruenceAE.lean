/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

import LeanPool.CoarseGraining.Homogenization.Sobolev.Fractional.Definitions
import LeanPool.CoarseGraining.Homogenization.Besov.Positive.Full

/-!
# Almost-everywhere congruence for the fractional Sobolev and Besov seminorms

All quantities in the `W^{s,p}` versus `B^s_{p,p}` comparison are invariant
under modifying `u` on a null set of the cube.  This file proves the
congruence lemmas once, against the canonical hypothesis
`u =ᵐ[cubeMeasure Q] v`:

* `gagliardoKernel_congr_ae`, `cubeGagliardoESeminorm_congr_ae`,
  `memWsp_congr_ae` (generic target `E`);
* `cubeBesovOverlapSeminorm_congr_ae` (scalar, all `q`);
* the `ae`-filter equivalence between `normalizedCubeMeasure Q` and
  `cubeMeasure Q`.

These discharge the `congr_ae` item of the frozen API surface and enable the
measurability-free public wrapper of CG Lemma 1.3.
-/

namespace Homogenization
namespace Gagliardo

noncomputable section

open MeasureTheory ScalarOverlap
open scoped ENNReal BigOperators

variable {d : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The normalized and plain cube measures have the same `ae` filter. -/
theorem ae_normalizedCubeMeasure_iff {Q : TriadicCube d} {prop : Vec d → Prop} :
    (∀ᵐ x ∂normalizedCubeMeasure Q, prop x) ↔
      ∀ᵐ x ∂Homogenization.cubeMeasure Q, prop x := by
  have hc0 : ENNReal.ofReal (cubeVolume Q)⁻¹ ≠ 0 := by
    rw [Ne, ENNReal.ofReal_eq_zero, not_le]
    exact inv_pos.2 (cubeVolume_pos Q)
  constructor
  · intro hp
    rw [normalizedCubeMeasure, Filter.eventually_iff, mem_ae_iff,
      Measure.smul_apply, smul_eq_mul, mul_eq_zero] at hp
    rw [Filter.eventually_iff, mem_ae_iff]
    exact hp.resolve_left hc0
  · intro hp
    rw [normalizedCubeMeasure]
    exact Measure.ae_smul_measure hp _

/-- Kernel congruence: modifying `u` on a cube-null set changes the Gagliardo
kernel only on a `gagliardoCubeMeasure`-null set of pairs. -/
theorem gagliardoKernel_congr_ae {Q : TriadicCube d} {s : ℝ} {p : ℝ≥0∞}
    {u v : Vec d → E} (h : u =ᵐ[Homogenization.cubeMeasure Q] v) :
    gagliardoKernel s p u =ᵐ[gagliardoCubeMeasure Q] gagliardoKernel s p v := by
  have : SFinite (Homogenization.cubeMeasure Q) := by
    unfold Homogenization.cubeMeasure
    infer_instance
  have hnorm : u =ᵐ[normalizedCubeMeasure Q] v :=
    ae_normalizedCubeMeasure_iff.2 h
  have h1 : (fun z : Vec d × Vec d => u z.1) =ᵐ[gagliardoCubeMeasure Q]
      fun z => v z.1 := by
    rw [gagliardoCubeMeasure]
    exact Measure.quasiMeasurePreserving_fst.ae_eq hnorm
  have h2 : (fun z : Vec d × Vec d => u z.2) =ᵐ[gagliardoCubeMeasure Q]
      fun z => v z.2 := by
    rw [gagliardoCubeMeasure]
    exact Measure.quasiMeasurePreserving_snd.ae_eq h
  filter_upwards [h1, h2] with z hz1 hz2
  rw [gagliardoKernel_apply, gagliardoKernel_apply, hz1, hz2]

/-- A.e.-congruence of the fractional Sobolev seminorm. -/
theorem cubeGagliardoESeminorm_congr_ae {Q : TriadicCube d} {s : ℝ}
    {p : ℝ≥0∞} {u v : Vec d → E}
    (h : u =ᵐ[Homogenization.cubeMeasure Q] v) :
    cubeGagliardoESeminorm Q s p u = cubeGagliardoESeminorm Q s p v := by
  rw [Internal.cubeGagliardoESeminorm_def, Internal.cubeGagliardoESeminorm_def]
  exact eLpNorm_congr_ae (gagliardoKernel_congr_ae h)

/-- A.e.-congruence of `W^{s,p}` membership. -/
theorem memWsp_congr_ae {Q : TriadicCube d} {s : ℝ} {p : ℝ≥0∞}
    {u v : Vec d → E} (h : u =ᵐ[Homogenization.cubeMeasure Q] v) :
    MemWsp Q s p u ↔ MemWsp Q s p v :=
  memLp_congr_ae (gagliardoKernel_congr_ae h)

section BesovCongruence

variable {Q : TriadicCube d} {u v : Vec d → ℝ}

/-- Restriction of the congruence hypothesis to an overlap center's enlarged
cube. -/
theorem ae_overlap_of_ae_cube {j : ℕ} {S : TriadicCube d}
    (hS : S ∈ ScalarOverlap.centersAtDepth Q j)
    (h : u =ᵐ[Homogenization.cubeMeasure Q] v) :
    u =ᵐ[MeasureTheory.volume.restrict (ScalarOverlap.cubeSet S)] v := by
  have hsub : ScalarOverlap.cubeSet S ⊆ Homogenization.cubeSet Q :=
    cubeSet_subset_cubeSet_of_mem_centersAtDepth hS
  rw [Homogenization.cubeMeasure] at h
  exact ae_restrict_of_ae_restrict_of_subset hsub h

theorem overlap_cubeAverage_congr_ae {j : ℕ} {S : TriadicCube d}
    (hS : S ∈ ScalarOverlap.centersAtDepth Q j)
    (h : u =ᵐ[Homogenization.cubeMeasure Q] v) :
    ScalarOverlap.cubeAverage S u = ScalarOverlap.cubeAverage S v := by
  unfold ScalarOverlap.cubeAverage
  congr 1
  exact integral_congr_ae (ae_overlap_of_ae_cube hS h)

theorem overlap_oscillation_congr_ae {p : ℝ≥0∞} {j : ℕ} {S : TriadicCube d}
    (hS : S ∈ ScalarOverlap.centersAtDepth Q j)
    (h : u =ᵐ[Homogenization.cubeMeasure Q] v) :
    cubeBesovOverlapOscillation S p u = cubeBesovOverlapOscillation S p v := by
  unfold cubeBesovOverlapOscillation ScalarOverlap.cubeLpNorm
  congr 1
  refine eLpNorm_congr_ae ?_
  have hres := ae_overlap_of_ae_cube hS h
  have hresn : u =ᵐ[ScalarOverlap.normalizedCubeMeasure S] v := by
    rw [ScalarOverlap.normalizedCubeMeasure, ScalarOverlap.cubeMeasure]
    exact Measure.ae_smul_measure hres _
  filter_upwards [hresn] with x hx
  rw [hx, overlap_cubeAverage_congr_ae hS h]

theorem overlap_depthAverage_congr_ae {p : ℝ≥0∞} {j : ℕ}
    (h : u =ᵐ[Homogenization.cubeMeasure Q] v) :
    cubeBesovOverlapDepthAverage Q p u j = cubeBesovOverlapDepthAverage Q p v j := by
  have hsum : (∑ S ∈ ScalarOverlap.centersAtDepth Q j,
      cubeBesovOverlapOscillation S p u ^ p.toReal) =
      ∑ S ∈ ScalarOverlap.centersAtDepth Q j,
        cubeBesovOverlapOscillation S p v ^ p.toReal :=
    Finset.sum_congr rfl fun S hS => by
      rw [overlap_oscillation_congr_ae hS h]
  unfold cubeBesovOverlapDepthAverage ScalarOverlap.centersAverage
  simpa using congrArg (((ScalarOverlap.centersAtDepth Q j).card : ℝ)⁻¹ * ·) hsum

theorem overlap_partialSeminorm_congr_ae {s : ℝ} {p q : ℝ≥0∞} {N : ℕ}
    (h : u =ᵐ[Homogenization.cubeMeasure Q] v) :
    cubeBesovOverlapPartialSeminorm Q s p q N u =
      cubeBesovOverlapPartialSeminorm Q s p q N v := by
  unfold cubeBesovOverlapPartialSeminorm
  congr 1
  refine Finset.sum_congr rfl fun j _hj => ?_
  unfold cubeBesovOverlapDepthSeminorm
  rw [overlap_depthAverage_congr_ae h]

/-- A.e.-congruence of the full overlapping Besov seminorm (any `q`). -/
theorem cubeBesovOverlapSeminorm_congr_ae {s : ℝ} {p q : ℝ≥0∞}
    (h : u =ᵐ[Homogenization.cubeMeasure Q] v) :
    cubeBesovOverlapSeminorm Q s p q u = cubeBesovOverlapSeminorm Q s p q v := by
  unfold cubeBesovOverlapSeminorm cubeBesovOverlapSeminormValueSet
  congr 1
  ext x
  constructor
  · rintro ⟨N, rfl⟩
    exact ⟨N, (overlap_partialSeminorm_congr_ae h).symm⟩
  · rintro ⟨N, rfl⟩
    exact ⟨N, overlap_partialSeminorm_congr_ae h⟩

end BesovCongruence

end

end Gagliardo
end Homogenization
