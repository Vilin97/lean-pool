/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

import LeanPool.CoarseGraining.Homogenization.Examples.RandomCheckerboard.Basic
import LeanPool.CoarseGraining.Homogenization.Book.Ch04.Theorems.DilationLaw
import LeanPool.CoarseGraining.Homogenization.Book.MainResults
import LeanPool.CoarseGraining.Homogenization.CoarseGraining.ThetaEllipticity

/-!
# The Bernoulli checkerboard carrier law and its instances

This file packages the carrier-valued checkerboard sample map of `Basic.lean`
as a law on the honest-fields carrier and re-proves the full law-level
instance stack on the carrier:

* `law` — the pushforward `Measure.map (checkerRegField lam Lam)` of the
  Bernoulli product measure, a probability measure on `RegCoeffField d`;
* `lawCarrier` — via `lawCarrier_of_aeLocallyUniformlyElliptic` (a.e.
  ellipticity holds per sample, everywhere, with deterministic constants);
* `structuralLaw` — stationarity/isotropy/adjoint invariance from the carrier
  endomorphism commutations of `Basic.lean`, and genuine restriction-unit-range
  dependence (`IsRestrictionUnitRangeDependentR`) through `RestrictionSigmaR`
  and the coin σ-algebras;
* `thetaEllipticLaw` — the conjunct-free `Θ`-ellipticity class membership;
* the triadically scaled family (`scaledLaw`, `checkerboardSetup`) and the
  public quenched-comparison corollary.
-/

namespace Homogenization
namespace Examples
namespace RandomCheckerboard

open MeasureTheory
open scoped ENNReal NNReal

noncomputable section

/-- The unscaled checkerboard law on the honest-fields carrier. -/
def law (d : ℕ) (lam Lam : ℝ) (p : ℝ≥0) (hp : p ≤ 1) : Book.Ch04.RestrictionCoeffLaw d :=
  Measure.map (checkerRegField lam Lam) (sampleMeasure d p hp)

instance instIsProbabilityMeasure_law (d : ℕ) (lam Lam : ℝ) (p : ℝ≥0) (hp : p ≤ 1) :
    IsProbabilityMeasure (law d lam Lam p hp) := by
  rw [law]
  exact Measure.isProbabilityMeasure_map
    (measurable_checkerRegField (d := d) lam Lam).aemeasurable

theorem isProbabilityMeasure_law (d : ℕ) (lam Lam : ℝ) (p : ℝ≥0) (hp : p ≤ 1) :
    IsProbabilityMeasure (law d lam Lam p hp) :=
  inferInstance

/-! ## Uniform ellipticity and the law carrier -/

theorem law_uniformEllipticityBounds {d : ℕ} {lam Lam : ℝ}
    (hlam : 0 < lam) (hle : lam ≤ Lam) (p : ℝ≥0) (hp : p ≤ 1) :
    Book.MainResults.UniformEllipticityBounds (law d lam Lam p hp) lam Lam where
  lam_pos := hlam
  lam_le_Lam := hle
  aee_elliptic := by
    rw [law]
    refine (ae_map_iff (measurable_checkerRegField (d := d) lam Lam).aemeasurable
      ?_).2 ?_
    · exact measurableSet_forall_openCubeSet_isAEEllipticFieldOn lam Lam
    · exact Filter.Eventually.of_forall fun ω Q =>
        checkerRegField_isAEEllipticFieldOn (measurableSet_openCubeSet Q) hlam hle ω

theorem lawCarrier {d : ℕ} {lam Lam : ℝ}
    (hlam : 0 < lam) (hle : lam ≤ Lam) (p : ℝ≥0) (hp : p ≤ 1) :
    Book.Ch04.RestrictionLawCarrier (law d lam Lam p hp) :=
  Book.Ch04.lawCarrier_of_aeLocallyUniformlyElliptic
    (law_uniformEllipticityBounds (d := d) hlam hle p hp).toAELocallyUniformlyEllipticLaw

/-! ## Structural law -/

theorem stationary_law {d : ℕ} {lam Lam : ℝ} (p : ℝ≥0) (hp : p ≤ 1) :
    Book.Ch04.RestrictionStationaryLaw (law d lam Lam p hp) := by
  intro z
  rw [law]
  calc
    Measure.map (translateReg (intVecToRealVec z))
        (Measure.map (checkerRegField lam Lam) (sampleMeasure d p hp))
        =
          Measure.map
            (fun ω : Sample d => translateReg (intVecToRealVec z) (checkerRegField lam Lam ω))
            (sampleMeasure d p hp) := by
          simpa [Function.comp_def] using!
            (Measure.map_map
              (measurable_translateReg (d := d) (intVecToRealVec z))
              (measurable_checkerRegField (d := d) lam Lam)
              (μ := sampleMeasure d p hp))
    _ =
          Measure.map
            (fun ω : Sample d => checkerRegField lam Lam (shiftSample z ω))
            (sampleMeasure d p hp) := by
          congr 1
          funext ω
          exact translateReg_checkerRegField z ω
    _ =
          Measure.map (checkerRegField lam Lam)
            (Measure.map (shiftSample z) (sampleMeasure d p hp)) := by
          symm
          simpa [Function.comp_def] using!
            (Measure.map_map
              (measurable_checkerRegField (d := d) lam Lam)
              (measurable_shiftSample z)
              (μ := sampleMeasure d p hp))
    _ = Measure.map (checkerRegField lam Lam) (sampleMeasure d p hp) := by
          rw [sampleMeasure_map_shiftSample z p hp]

theorem adjointInvariant_law {d : ℕ} {lam Lam : ℝ} (p : ℝ≥0) (hp : p ≤ 1) :
    Book.Ch04.RestrictionAdjointInvariantLaw (law d lam Lam p hp) := by
  show Measure.map adjointReg (law d lam Lam p hp) = law d lam Lam p hp
  rw [law]
  calc
    Measure.map adjointReg (Measure.map (checkerRegField lam Lam) (sampleMeasure d p hp))
        =
          Measure.map
            (fun ω : Sample d => adjointReg (checkerRegField lam Lam ω))
            (sampleMeasure d p hp) := by
          simpa [Function.comp_def] using!
            (Measure.map_map
              (measurable_adjointReg (d := d))
              (measurable_checkerRegField (d := d) lam Lam)
              (μ := sampleMeasure d p hp))
    _ = Measure.map (checkerRegField lam Lam) (sampleMeasure d p hp) := by
          congr 1
          funext ω
          exact adjointReg_checkerRegField ω

theorem isotropic_law {d : ℕ} {lam Lam : ℝ} (p : ℝ≥0) (hp : p ≤ 1) :
    Book.Ch04.RestrictionIsotropicLaw (law d lam Lam p hp) := by
  intro R hR
  obtain ⟨σ, s, hs, hRdef⟩ := id hR
  rw [law]
  let e : Lattice d ≃ Lattice d := signedLatticeEquiv σ s hs
  calc
    Measure.map (rotateReg R hR)
        (Measure.map (checkerRegField lam Lam) (sampleMeasure d p hp))
        =
          Measure.map
            (fun ω : Sample d => rotateReg R hR (checkerRegField lam Lam ω))
            (sampleMeasure d p hp) := by
          simpa [Function.comp_def] using!
            (Measure.map_map
              (measurable_rotateReg (d := d) R hR)
              (measurable_checkerRegField (d := d) lam Lam)
              (μ := sampleMeasure d p hp))
    _ =
          Measure.map
            (fun ω : Sample d => checkerRegField lam Lam (reindexSample e ω))
            (sampleMeasure d p hp) := by
          congr 1
          funext ω
          exact rotateReg_checkerRegField (lam := lam) (Lam := Lam) hs hRdef hR ω
    _ =
          Measure.map (checkerRegField lam Lam)
            (Measure.map (reindexSample e) (sampleMeasure d p hp)) := by
          symm
          simpa [Function.comp_def, e] using!
            (Measure.map_map
              (measurable_checkerRegField (d := d) lam Lam)
              (measurable_reindexSample e)
              (μ := sampleMeasure d p hp))
    _ = Measure.map (checkerRegField lam Lam) (sampleMeasure d p hp) := by
          rw [sampleMeasure_map_reindexSample e p hp]

/-- **Genuine restriction-unit-range dependence on the carrier**: the restriction
σ-algebras of unit-separated measurable sets pull back through the sample map
into the coin σ-algebras of disjoint cell families, which are independent under
the Bernoulli product law. -/
theorem restrictionUnitRangeDependent_law {d : ℕ} {lam Lam : ℝ}
    (p : ℝ≥0) (hp : p ≤ 1) :
    Book.Ch04.RestrictionUnitRangeDependentLaw (law d lam Lam p hp) := by
  intro U V hU hV hUV
  rw [law]
  have hcells : Disjoint (cellsMeeting U) (cellsMeeting V) :=
    disjoint_cellsMeeting_of_areUnitSeparated hUV
  have hIndCells :
      ProbabilityTheory.Indep
        (sampleCellsSigma (cellsMeeting U))
        (sampleCellsSigma (cellsMeeting V))
        (sampleMeasure d p hp) :=
    indep_sampleCellsSigma_of_disjoint hcells p hp
  rw [ProbabilityTheory.Indep_iff]
  intro s t hs ht
  have hmeas := measurable_checkerRegField (d := d) lam Lam
  have hs_ambient : MeasurableSet s := restrictionSigmaR_le U hU s hs
  have ht_ambient : MeasurableSet t := restrictionSigmaR_le V hV t ht
  have hst_ambient : MeasurableSet (s ∩ t) := hs_ambient.inter ht_ambient
  have hs_pre :
      @MeasurableSet (Sample d) (sampleCellsSigma (cellsMeeting U))
        (checkerRegField lam Lam ⁻¹' s) :=
    (measurable_checkerRegField_restrictionSigmaR lam Lam U hU) hs
  have ht_pre :
      @MeasurableSet (Sample d) (sampleCellsSigma (cellsMeeting V))
        (checkerRegField lam Lam ⁻¹' t) :=
    (measurable_checkerRegField_restrictionSigmaR lam Lam V hV) ht
  have hpre_ind :=
    (ProbabilityTheory.Indep_iff
      (sampleCellsSigma (cellsMeeting U))
      (sampleCellsSigma (cellsMeeting V))
      (sampleMeasure d p hp)).1 hIndCells
      (checkerRegField lam Lam ⁻¹' s)
      (checkerRegField lam Lam ⁻¹' t)
      hs_pre ht_pre
  rw [Measure.map_apply hmeas hst_ambient,
    Measure.map_apply hmeas hs_ambient,
    Measure.map_apply hmeas ht_ambient]
  simpa [Set.preimage_inter] using hpre_ind

/-- The unscaled Bernoulli checkerboard law satisfies all structural
assumptions used by the public main results. -/
theorem structuralLaw {d : ℕ} {lam Lam : ℝ} (p : ℝ≥0) (hp : p ≤ 1) :
    Book.Ch04.RestrictionStructuralLaw (law d lam Lam p hp) where
  stationary := stationary_law p hp
  unit_range := restrictionUnitRangeDependent_law p hp
  isotropic := isotropic_law p hp
  adjoint_invariant := adjointInvariant_law p hp

/-! ## The `Θ`-ellipticity class -/

/-- **Conjunct-free `Θ`-ellipticity of the checkerboard law**: when
`1 ≤ lam ≤ Lam ≤ Θ`, almost every realization lies a.e. (in fact everywhere)
in the `(1, Θ)` ellipticity class.  The measurability conjunct of the paper's
class `Ω_Θ` is free by the carrier type (decision E-2). -/
theorem thetaEllipticLaw {d : ℕ} {lam Lam Θ : ℝ}
    (h1 : 1 ≤ lam) (hle : lam ≤ Lam) (hΘ : Lam ≤ Θ) (p : ℝ≥0) (hp : p ≤ 1) :
    Homogenization.ThetaEllipticLaw Θ (law d lam Lam p hp) := by
  unfold Homogenization.ThetaEllipticLaw
  rw [law]
  refine (ae_map_iff (measurable_checkerRegField (d := d) lam Lam).aemeasurable
    (measurableSet_ae_isEllipticMatrix_univ 1 Θ)).2 ?_
  refine Filter.Eventually.of_forall fun ω => ?_
  refine Filter.Eventually.of_forall fun x => ?_
  exact (scalarMatrix_isEllipticMatrix_between (d := d)
      (lt_of_lt_of_le one_pos h1) hle
      (scalarAt_eq_lam_or_Lam (lam := lam) (Lam := Lam) ω x)).mono
    one_pos h1 hΘ

/-! ## The scaled law and the public setup -/

/-- The scaled checkerboard law used by the public corollary. -/
def scaledLaw (d : ℕ) (lam Lam : ℝ) (p : ℝ≥0) (hp : p ≤ 1) (k : ℕ) :
    Book.Ch04.RestrictionCoeffLaw d :=
  Book.Ch04.restrictionScaleNormalizedLaw k (law d lam Lam p hp)

/-- The reader-facing checkerboard scale.  A single triadic downscaling already
makes the application visibly a scaled law while preserving all constants as
dimension-only constants in the main theorem. -/
def publicScale : ℕ := 1

/-- The scaled checkerboard law has the Chapter 4 law carrier. -/
theorem scaledLawCarrier {d : ℕ} {lam Lam : ℝ}
    (hlam : 0 < lam) (hle : lam ≤ Lam) (p : ℝ≥0) (hp : p ≤ 1) (k : ℕ) :
    Book.Ch04.RestrictionLawCarrier (scaledLaw d lam Lam p hp k) := by
  simpa [scaledLaw] using
    (lawCarrier (d := d) (lam := lam) (Lam := Lam) hlam hle p hp).scaleNormalized k

/-- Every triadically rescaled checkerboard realization keeps the deterministic
ellipticity constants. -/
theorem rescaleReg_checkerRegField_isAEEllipticFieldOn {d : ℕ} {lam Lam : ℝ}
    (k : ℕ) {U : Set (Vec d)} (hU : MeasurableSet U)
    (hlam : 0 < lam) (hle : lam ≤ Lam) (ω : Sample d) :
    IsAEEllipticFieldOn lam Lam U (rescaleReg k (checkerRegField lam Lam ω)).toFun := by
  rw [isAEEllipticFieldOn_carrier_iff hU lam Lam]
  refine Filter.Eventually.of_forall fun x => ?_
  exact scalarMatrix_isEllipticMatrix_between (d := d) hlam hle
    (scalarAt_eq_lam_or_Lam (lam := lam) (Lam := Lam) ω (((3 : ℝ) ^ k) • x))

/-- The scaled checkerboard law remains uniformly elliptic with the same
deterministic constants. -/
theorem scaledUniformEllipticityBounds {d : ℕ} {lam Lam : ℝ}
    (hlam : 0 < lam) (hle : lam ≤ Lam) (p : ℝ≥0) (hp : p ≤ 1) (k : ℕ) :
    Book.MainResults.UniformEllipticityBounds (scaledLaw d lam Lam p hp k) lam Lam where
  lam_pos := hlam
  lam_le_Lam := hle
  aee_elliptic := by
    rw [scaledLaw, Book.Ch04.restrictionScaleNormalizedLaw_eq_map_rescaleReg, law,
      Measure.map_map (measurable_rescaleReg (d := d) k)
        (measurable_checkerRegField (d := d) lam Lam)]
    have hcomp : Measurable (rescaleReg (d := d) k ∘ checkerRegField lam Lam) :=
      (measurable_rescaleReg (d := d) k).comp (measurable_checkerRegField (d := d) lam Lam)
    refine (ae_map_iff hcomp.aemeasurable ?_).2 ?_
    · exact measurableSet_forall_openCubeSet_isAEEllipticFieldOn lam Lam
    · exact Filter.Eventually.of_forall fun ω Q =>
        rescaleReg_checkerRegField_isAEEllipticFieldOn k
          (measurableSet_openCubeSet Q) hlam hle ω

/-- The scaled checkerboard law satisfies the structural assumptions. -/
theorem scaledStructuralLaw {d : ℕ} {lam Lam : ℝ}
    (p : ℝ≥0) (hp : p ≤ 1) (k : ℕ) :
    Book.Ch04.RestrictionStructuralLaw (scaledLaw d lam Lam p hp k) := by
  simpa [scaledLaw] using
    (structuralLaw (d := d) (lam := lam) (Lam := Lam) p hp).scaleNormalized k

/-- The main-result setup associated with the scaled Bernoulli checkerboard. -/
def checkerboardSetup {d : ℕ} [NeZero d]
    (two_le_dim : 2 ≤ d) (lam Lam : ℝ) (hlam : 0 < lam) (hle : lam ≤ Lam)
    (p : ℝ≥0) (hp : p ≤ 1) : Book.MainResults.Setup d where
  two_le_dim := two_le_dim
  P := scaledLaw d lam Lam p hp publicScale
  hP := scaledLawCarrier (d := d) (lam := lam) (Lam := Lam)
    hlam hle p hp publicScale
  hStruct := scaledStructuralLaw (d := d) (lam := lam) (Lam := Lam)
    p hp publicScale
  lam := lam
  Lam := Lam
  hUE := scaledUniformEllipticityBounds (d := d) (lam := lam) (Lam := Lam)
    hlam hle p hp publicScale

/-- **Quenched comparison for the Bernoulli checkerboard.**

For the triadically scaled Bernoulli checkerboard with coin parameter `p` and
conductances `lam`, `Lam`, all law assumptions in the public uniform-ellipticity
comparison theorem are discharged by the construction.  The constants are chosen
before `lam`, `Lam`, `p`, the realization, the cube, the forcing, and the
solutions. -/
theorem randomCheckerboard_quenchedComparison
    {d : ℕ} [NeZero d] :
    ∃ C α Cscale : ℝ,
      0 < C ∧ 0 < α ∧ 0 < Cscale ∧
      ∀ (two_le_dim : 2 ≤ d) (lam Lam : ℝ)
        (hlam : 0 < lam) (hle : lam ≤ Lam)
        (p : ℝ≥0) (hp : p ≤ 1),
        let S : Book.MainResults.Setup d :=
          checkerboardSetup two_le_dim lam Lam hlam hle p hp
        ∃ sigmaBar : ℝ,
          0 < sigmaBar ∧
          ∃ X : RegCoeffField d → ℝ,
            S.IsMinimalScale X Cscale ∧
            ∀ᵐ aω ∂S.P,
              ∀ (ha : Book.Ch04.AELocallyUniformlyEllipticField aω)
                {m : ℕ} {g : Vec d → Vec d}
                (pair : S.ComparisonPair aω ha m g),
                X aω ≤ (3 : ℝ) ^ m →
                Book.Ch03.Legacy.ForceSobolevRegularity
                  (Book.MainResults.originCube d m) Book.MainResults.fixedComparisonS g →
                S.comparisonDefect Book.MainResults.fixedComparisonS pair ≤
                  C * ((3 : ℝ) ^ m / X aω) ^ (-α) *
                    S.comparisonData Book.MainResults.fixedComparisonS pair := by
  classical
  obtain ⟨C, α, Cscale, hC, hα, hCscale, hmain⟩ :=
    Book.MainResults.homogenizationComparison_uniformEllipticity (d := d)
  refine ⟨C, α, Cscale, hC, hα, hCscale, ?_⟩
  intro two_le_dim lam Lam hlam hle p hp
  exact hmain (checkerboardSetup two_le_dim lam Lam hlam hle p hp)

end

end RandomCheckerboard
end Examples
end Homogenization
