/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

import LeanPool.CoarseGraining.Homogenization.Probability.RegCoeffField.Differentiation
import LeanPool.CoarseGraining.Homogenization.Probability.LocalEllipticitySlices
import LeanPool.CoarseGraining.Homogenization.Geometry.OriginCubeBoundaryPush

/-!
# Genuine `LocalSigmaR`-measurability of the AEE quantitative-slice event

This file completes the honest slice-measurability route (Packet P4b).  Using the
rational-ball characterization of spatial a.e. ellipticity
(`RegCoeffField/Differentiation.lean`), it proves that the carrier slice event

`{a : RegCoeffField d | AEEQuantitativeEllipticSlice (cubeSet Q) k a.toFun}`

is genuinely measurable for the **local entry-test carrier σ-algebra**
`LocalSigmaR (cubeSet Q)` — not merely null-measurable, and with **no hypothesis
on any law**.  This is the P4 report's honest replacement for the comap slice
field, which could not descend to null-measurability.

The event is written as a countable intersection, over rational balls inside the
open core `openCubeSet Q`, of preimages of the closed elliptic matrix locus under
the `LocalSigmaR`-measurable ball-average maps `avgMat B`
(`measurable_avgMat`).  The two free conjuncts of the raw
`IsAEEllipticFieldOn` predicate (measurability of the domain and a.e.-strong
measurability of the coefficient entries) hold for *every* carrier element, by
type (`aeeQuantitativeEllipticSlice_carrier_iff`); the boundary of the half-open
cube is Lebesgue-null, so rational balls in the open core suffice, and
`LocalSigmaR (openCubeSet Q) ≤ LocalSigmaR (cubeSet Q)` upgrades the result to the
consumer's cube.

Reference: the paper (Armstrong–Kuusi–Loher, to appear).
-/

namespace Homogenization

open MeasureTheory Metric

noncomputable section

variable {d : ℕ}

/-! ## `LocalSigmaR` generators and monotonicity -/

/-- A localized entry-test generator is `LocalSigmaR U`-measurable when its probe
is supported in `U`. -/
theorem measurable_entryTestR_localSigmaR {U : Set (Vec d)} (i j : Fin d) {φ : Vec d → ℝ}
    (hφ : IsProbeR φ) (hsupp : Function.support φ ⊆ U) :
    @Measurable (RegCoeffField d) ℝ (LocalSigmaR U) _ (entryTestR i j φ) := by
  intro t ht
  exact MeasurableSpace.measurableSet_generateFrom ⟨i, j, φ, hφ, hsupp, t, ht, rfl⟩

/-- **Monotonicity of the local entry-test σ-algebra under set inclusion.** -/
theorem localSigmaR_mono {U V : Set (Vec d)} (hUV : U ⊆ V) :
    LocalSigmaR U ≤ LocalSigmaR V := by
  refine MeasurableSpace.generateFrom_le ?_
  rintro s ⟨i, j, φ, hφ, hsupp, t, ht, rfl⟩
  exact MeasurableSpace.measurableSet_generateFrom
    ⟨i, j, φ, hφ, hsupp.trans hUV, t, ht, rfl⟩

/-! ## `LocalSigmaR`-measurability of the ball averages -/

/-- **The ball average is a `LocalSigmaR U`-measurable function of the carrier
field** whenever the (compact measurable) ball lies in `U`.  Each entry is a
scalar multiple of a localized entry-test generator (`avgMat_entry_eq_smul_entryTestR`).
This is the measurable-average half of Packet P4b's deliverable 1. -/
theorem measurable_avgMat {U B : Set (Vec d)} (hBcpt : IsCompact B) (hBmeas : MeasurableSet B)
    (hBU : B ⊆ U) :
    @Measurable (RegCoeffField d) (Mat d) (LocalSigmaR U) _ (avgMat B) := by
  refine @measurable_matrix_of_entries d (RegCoeffField d) (LocalSigmaR U) (avgMat B) ?_
  intro i j
  have hsupp : Function.support (Set.indicator B (fun _ => (1 : ℝ))) ⊆ U :=
    (support_indicator_one_subset B).trans hBU
  have hgen : @Measurable (RegCoeffField d) ℝ (LocalSigmaR U) _
      (entryTestR i j (Set.indicator B (fun _ => (1 : ℝ)))) :=
    measurable_entryTestR_localSigmaR i j (isProbeR_indicator hBcpt hBmeas) hsupp
  have heq : (fun a : RegCoeffField d => avgMat B a i j)
      = fun a => (volume B).toReal⁻¹ • entryTestR i j (Set.indicator B (fun _ => (1 : ℝ))) a := by
    funext a; exact avgMat_entry_eq_smul_entryTestR i j B hBmeas a
  rw [heq]
  exact hgen.const_smul ((volume B).toReal⁻¹)

/-! ## The rational-ball intersection -/

/-- The rational-ball intersection: over all rational balls inside `U`, the
carrier fields whose ball average is elliptic.  This is the countable
`LocalSigmaR U`-measurable presentation of the a.e.-ellipticity event. -/
def slicePart (U : Set (Vec d)) (lam Lam : ℝ) : Set (RegCoeffField d) :=
  ⋂ (q : Fin d → ℚ) (r : ℚ) (_ : 0 < (r : ℝ)) (_ : closedBall (ratPt q) (r : ℝ) ⊆ U),
    {a | IsEllipticMatrix lam Lam (avgMat (closedBall (ratPt q) (r : ℝ)) a)}

/-- The rational-ball intersection is `LocalSigmaR U`-measurable: a countable
intersection of preimages of the closed elliptic locus under the measurable
ball-average maps. -/
theorem measurableSet_slicePart {U : Set (Vec d)} (lam Lam : ℝ) :
    MeasurableSet[LocalSigmaR U] (slicePart U lam Lam) := by
  refine MeasurableSet.iInter (fun q => ?_)
  refine MeasurableSet.iInter (fun r => ?_)
  refine MeasurableSet.iInter (fun hpos => ?_)
  refine MeasurableSet.iInter (fun hsub => ?_)
  have hBcpt : IsCompact (closedBall (ratPt q) (r : ℝ)) := isCompact_closedBall _ _
  have hpre :
      {a : RegCoeffField d | IsEllipticMatrix lam Lam (avgMat (closedBall (ratPt q) (r : ℝ)) a)}
        = (avgMat (closedBall (ratPt q) (r : ℝ))) ⁻¹' {A : Mat d | IsEllipticMatrix lam Lam A} :=
    rfl
  rw [hpre]
  exact (measurable_avgMat hBcpt hBcpt.measurableSet hsub) measurableSet_isEllipticMatrix

/-- The a.e.-ellipticity event on an open set equals the rational-ball
intersection (the characterization of `Differentiation.lean`, as a set). -/
theorem setOf_aeRestrict_isEllipticMatrix_eq_slicePart {U : Set (Vec d)} (hUopen : IsOpen U)
    (lam Lam : ℝ) :
    {a : RegCoeffField d | ∀ᵐ x ∂(volume.restrict U), IsEllipticMatrix lam Lam (a x)}
      = slicePart U lam Lam := by
  ext a
  simp only [slicePart, Set.mem_ofPred_eq, Set.mem_iInter]
  exact aeRestrict_isEllipticMatrix_iff_forall_ratBall hUopen lam Lam a

/-! ## The free conjuncts of the AEE slice on the carrier -/

/-- The restricted coefficient entry of a carrier field is a.e.-strongly
measurable — free from the carrier type (entrywise Borel measurability). -/
theorem aestronglyMeasurable_restrictCoeffField_carrier (U : Set (Vec d))
    (hU : MeasurableSet U) (a : RegCoeffField d) (i j : Fin d) :
    AEStronglyMeasurable
      (fun x => restrictCoeffField U a.toFun x i j) (volumeMeasureOn U) := by
  classical
  have hmeas : Measurable (fun x => restrictCoeffField U a.toFun x i j) := by
    have heq : (fun x => restrictCoeffField U a.toFun x i j)
        = Set.indicator U (fun x => a x i j) := by
      funext x
      by_cases hx : x ∈ U
      · simp [restrictCoeffField, hx]
      · simp [restrictCoeffField, hx]
    rw [heq]
    exact (a.entry_measurable i j).indicator hU
  exact hmeas.aestronglyMeasurable

/-- **The AEE quantitative-slice predicate on a carrier field reduces to its a.e.
ellipticity conjunct.**  The two measurability conjuncts of `IsAEEllipticFieldOn`
are free by the carrier type. -/
theorem aeeQuantitativeEllipticSlice_carrier_iff (U : Set (Vec d)) (hU : MeasurableSet U)
    (k : ℕ) (a : RegCoeffField d) :
    AEEQuantitativeEllipticSlice U k a.toFun ↔
      ∀ᵐ x ∂(volumeMeasureOn U), IsEllipticMatrix ((k + 1 : ℝ)⁻¹) (k + 1 : ℝ) (a x) := by
  constructor
  · exact fun h => h.2.2
  · intro h
    exact ⟨hU, fun i j => aestronglyMeasurable_restrictCoeffField_carrier U hU a i j, h⟩

/-! ## The main theorem -/

/-- **Genuine `LocalSigmaR (cubeSet Q)`-measurability of the AEE quantitative-slice
event.**  No law hypothesis: the event is a countable intersection of
`LocalSigmaR`-measurable rational-ball average preimages.  This is Packet P4b's
deliverable 3, replacing the P4 comap slice field. -/
theorem measurableSet_localSigmaR_aeeSlice (Q : TriadicCube d) (k : ℕ) :
    MeasurableSet[LocalSigmaR (cubeSet Q)]
      {a : RegCoeffField d | AEEQuantitativeEllipticSlice (cubeSet Q) k a.toFun} := by
  set lam : ℝ := (k + 1 : ℝ)⁻¹
  set Lam : ℝ := (k + 1 : ℝ)
  -- rewrite the slice event as the a.e.-ellipticity event on the open core
  have hEvent :
      {a : RegCoeffField d | AEEQuantitativeEllipticSlice (cubeSet Q) k a.toFun}
        = {a : RegCoeffField d |
            ∀ᵐ x ∂(volume.restrict (openCubeSet Q)), IsEllipticMatrix lam Lam (a x)} := by
    ext a
    simp only [Set.mem_ofPred_eq]
    rw [aeeQuantitativeEllipticSlice_carrier_iff (cubeSet Q) (measurableSet_cubeSet Q) k a]
    show (∀ᵐ x ∂(volume.restrict (cubeSet Q)), IsEllipticMatrix lam Lam (a x)) ↔ _
    exact ae_restrict_cubeSet_iff
  rw [hEvent, setOf_aeRestrict_isEllipticMatrix_eq_slicePart (isOpen_openCubeSet Q) lam Lam]
  exact localSigmaR_mono (openCubeSet_subset_cubeSet Q) _ (measurableSet_slicePart lam Lam)

end

end Homogenization
