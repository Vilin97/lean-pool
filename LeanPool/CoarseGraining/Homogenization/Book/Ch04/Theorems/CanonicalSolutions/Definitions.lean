/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

import LeanPool.CoarseGraining.Homogenization.Book.Ch04.Measurability
import LeanPool.CoarseGraining.Homogenization.Book.Ch04.Theorems.CoarseObservables
import LeanPool.CoarseGraining.Homogenization.Book.Ch02.Theorems.SolutionIntegrability
import LeanPool.CoarseGraining.Homogenization.Book.Ch04.Internal.AEESliceAssembly.MuFamily

/-! # Definitions -/

namespace Homogenization
namespace Book
namespace Ch04

open scoped ENNReal
open MeasureTheory

/-!
# Canonical solution-field measurability

This file is the public Ch4 handoff for selected canonical doubled-`Mu`
Hilbert minimizers.  The definition below is total: on coefficient fields that
lie in some AEE quantitative slice it uses the least slice index, and outside
that support it returns `0`.  Under a `RestrictionLawCarrier`, the outside branch is null.
-/

/-- The canonical totalized selected doubled-`Mu` Hilbert minimizer on a
deterministic cube.  On fields that belong to some AEE quantitative slice it
uses the least such slice index; outside the AEE slice cover it is `0`.

The law-facing theorem
`RestrictionLawCarrier.aestronglyMeasurable_canonicalMuHilbertMinimizer_cubeSet` shows
that this totalization is harmless under a `RestrictionLawCarrier`. -/
noncomputable def canonicalMuHilbertMinimizerCubeSet
    {d : ℕ} (Q : TriadicCube d) (P0 : BlockVec d) :
    CoeffField d → HilbertBlockL2 (cubeSet Q) := by
  classical
  intro a
  by_cases h : ∃ k : ℕ, AEEQuantitativeEllipticSlice (cubeSet Q) k a
  · let k : ℕ := Nat.find h
    let ak : {a : CoeffField d // AEEQuantitativeEllipticSlice (cubeSet Q) k a} :=
      ⟨a, by simpa [k] using Nat.find_spec h⟩
    exact ((canonicalAEEMuOperatorSystemData Q k ak).toMuHilbertRealization).minimizerMap P0
  · exact 0

/-- Potential component of the selected doubled-`Mu` Hilbert minimizer on a
deterministic cube. -/
noncomputable def canonicalMuHilbertPotentialCubeSet
    {d : ℕ} (Q : TriadicCube d) (P0 : BlockVec d) :
    CoeffField d → HilbertVectorL2 (cubeSet Q) :=
  fun a => hilbertBlockL2PotentialCLM (U := cubeSet Q)
    (canonicalMuHilbertMinimizerCubeSet Q P0 a)

/-- Flux component of the selected doubled-`Mu` Hilbert minimizer on a
deterministic cube. -/
noncomputable def canonicalMuHilbertFluxCubeSet
    {d : ℕ} (Q : TriadicCube d) (P0 : BlockVec d) :
    CoeffField d → HilbertVectorL2 (cubeSet Q) :=
  fun a => hilbertBlockL2FluxCLM (U := cubeSet Q)
    (canonicalMuHilbertMinimizerCubeSet Q P0 a)

/-- Ch4 selected doubled-`Mu` potential field with response loading `(-p, q)`.

This object is measurable and useful for the doubled-`Mu` problem, but it is
not, by definition, the raw scalar response-maximizer gradient
`∇ v(·, Q, p, q; a)`.  Section 5.3 weak norms should use the scalar-response
average and weak-norm observables below, which add the selected doubled-`Mu`
projection to its coefficient-operator image averages. -/
noncomputable def canonicalDoubledMuResponsePotentialFieldCubeSet
    {d : ℕ} (Q : TriadicCube d) (p q : Vec d) :
    CoeffField d → HilbertVectorL2 (cubeSet Q) :=
  canonicalMuHilbertPotentialCubeSet Q (-p, q)

/-- Ch4 selected doubled-`Mu` flux field with response loading `(-p, q)`.

This is the flux projection of the selected doubled-`Mu` minimizer.  It is not,
by definition, the raw scalar response flux `a ∇ v(·, Q, p, q; a)`. -/
noncomputable def canonicalDoubledMuResponseFluxFieldCubeSet
    {d : ℕ} (Q : TriadicCube d) (p q : Vec d) :
    CoeffField d → HilbertVectorL2 (cubeSet Q) :=
  canonicalMuHilbertFluxCubeSet Q (-p, q)

/-- The selected doubled-`Mu` potential field averaged over `R`, viewed as a
continuous postcomposition of the parent-cube Hilbert `L²` field on `Q`.

The intended use is `R ∈ descendantsAtDepth Q j`, but the definition is total. -/
noncomputable def canonicalDoubledMuResponsePotentialFieldAverageCubeSet
    {d : ℕ} (Q R : TriadicCube d) (p q : Vec d) :
    CoeffField d → Vec d :=
  fun a i =>
    (cubeVolume R)⁻¹ *
      hilbertVectorL2CoordSetIntegralCLM (U := cubeSet Q)
        (cubeSet R) (measurableSet_cubeSet R) i
        (canonicalDoubledMuResponsePotentialFieldCubeSet Q p q a)

/-- The selected doubled-`Mu` flux field averaged over `R`, viewed as a continuous
postcomposition of the parent-cube Hilbert `L²` field on `Q`.

The intended use is `R ∈ descendantsAtDepth Q j`, but the definition is total. -/
noncomputable def canonicalDoubledMuResponseFluxFieldAverageCubeSet
    {d : ℕ} (Q R : TriadicCube d) (p q : Vec d) :
    CoeffField d → Vec d :=
  fun a i =>
    (cubeVolume R)⁻¹ *
      hilbertVectorL2CoordSetIntegralCLM (U := cubeSet Q)
        (cubeSet R) (measurableSet_cubeSet R) i
        (canonicalDoubledMuResponseFluxFieldCubeSet Q p q a)

/-- Finite descendant average of the selected doubled-`Mu` potential averages. -/
noncomputable def descendantsAverageCanonicalDoubledMuResponsePotentialFieldAverageCubeSet
    {d : ℕ} (Q : TriadicCube d) (j : ℕ) (p q : Vec d) :
    CoeffField d → Vec d :=
  fun a i =>
    descendantsAverage Q j
      (fun R => canonicalDoubledMuResponsePotentialFieldAverageCubeSet Q R p q a i)

/-- Finite descendant average of the selected doubled-`Mu` flux averages. -/
noncomputable def descendantsAverageCanonicalDoubledMuResponseFluxFieldAverageCubeSet
    {d : ℕ} (Q : TriadicCube d) (j : ℕ) (p q : Vec d) :
    CoeffField d → Vec d :=
  fun a i =>
    descendantsAverage Q j
      (fun R => canonicalDoubledMuResponseFluxFieldAverageCubeSet Q R p q a i)

/-- Finite-depth selected doubled-`Mu` potential weak norm, expressed only through
descendant averages of the selected doubled-`Mu` Hilbert field. -/
noncomputable def canonicalDoubledMuResponsePotentialWeakNormPartialCubeSet
    {d : ℕ} (Q : TriadicCube d) (s : ℝ) (N : ℕ) (p q p0 : Vec d) :
    CoeffField d → ℝ :=
  fun a =>
    ∑ j ∈ Finset.range (N + 1),
      Real.rpow (3 : ℝ) (-s * (j : ℝ)) *
        Real.sqrt
          (descendantsAverage Q j fun R =>
            vecNormSq (canonicalDoubledMuResponsePotentialFieldAverageCubeSet Q R p q a - p0))

/-- Finite-depth selected doubled-`Mu` flux weak norm, expressed only through
descendant averages of the selected doubled-`Mu` Hilbert field. -/
noncomputable def canonicalDoubledMuResponseFluxWeakNormPartialCubeSet
    {d : ℕ} (Q : TriadicCube d) (t : ℝ) (N : ℕ) (p q q0 : Vec d) :
    CoeffField d → ℝ :=
  fun a =>
    ∑ j ∈ Finset.range (N + 1),
      Real.rpow (3 : ℝ) (-t * (j : ℝ)) *
        Real.sqrt
          (descendantsAverage Q j fun R =>
            vecNormSq (canonicalDoubledMuResponseFluxFieldAverageCubeSet Q R p q a - q0))

/-- Full selected doubled-`Mu` potential weak norm, as the countable supremum of the
finite-depth norms. -/
noncomputable def canonicalDoubledMuResponsePotentialWeakNormCubeSet
    {d : ℕ} (Q : TriadicCube d) (s : ℝ) (p q p0 : Vec d) :
    CoeffField d → ℝ :=
  fun a => ⨆ N : ℕ, canonicalDoubledMuResponsePotentialWeakNormPartialCubeSet Q s N p q p0 a

/-- Full selected doubled-`Mu` flux weak norm, as the countable supremum of the
finite-depth norms. -/
noncomputable def canonicalDoubledMuResponseFluxWeakNormCubeSet
    {d : ℕ} (Q : TriadicCube d) (t : ℝ) (p q q0 : Vec d) :
    CoeffField d → ℝ :=
  fun a => ⨆ N : ℕ, canonicalDoubledMuResponseFluxWeakNormPartialCubeSet Q t N p q q0 a

/-- Totalized fixed-test Hilbert energy pairing against the selected
canonical doubled-`Mu` minimizer. On the AEE elliptic support it uses the least
quantitative slice; outside that support it is set to `0`.

This is an internal Ch4 scalar-response source: fixed indicator tests recover
averages of the coefficient-operator image of the selected minimizer. -/
noncomputable def canonicalMuHilbertEnergyBilinFixedCubeSet
    {d : ℕ} (Q : TriadicCube d) (P0 : BlockVec d)
    (Y : BlockState d) (hY : MemBlockL2 (cubeSet Q) Y.eval) :
    CoeffField d → ℝ := by
  classical
  intro a
  by_cases h : ∃ k : ℕ, AEEQuantitativeEllipticSlice (cubeSet Q) k a
  · let k : ℕ := Nat.find h
    let ak : {a : CoeffField d // AEEQuantitativeEllipticSlice (cubeSet Q) k a} :=
      ⟨a, by simpa [k] using Nat.find_spec h⟩
    exact
      ((canonicalAEEMuOperatorSystemData Q k ak).toMuHilbertRealization).energyBilin
        (toHilbertBlockL2OfBlockField (U := cubeSet Q) hY)
        (((canonicalAEEMuOperatorSystemData Q k ak).toMuHilbertRealization).minimizerMap P0)
  · exact 0

noncomputable def canonicalUpperImageIndicatorTestStateCubeSet
    {d : ℕ} (R : TriadicCube d) (i : Fin d) : BlockState d :=
  { potential := fun x => (cubeSet R).indicator (fun _ => Pi.single i 1) x
    flux := fun _ => 0 }

noncomputable def canonicalLowerImageIndicatorTestStateCubeSet
    {d : ℕ} (R : TriadicCube d) (i : Fin d) : BlockState d :=
  { potential := fun _ => 0
    flux := fun x => (cubeSet R).indicator (fun _ => Pi.single i 1) x }

theorem canonicalUpperImageIndicatorTestStateCubeSet_memBlockL2
    {d : ℕ} (Q R : TriadicCube d) (i : Fin d) :
    MemBlockL2 (cubeSet Q) (canonicalUpperImageIndicatorTestStateCubeSet R i).eval := by
  classical
  have hR_ne_top : volumeMeasureOn (cubeSet Q) (cubeSet R) ≠ ⊤ := by
    have hle :
        volumeMeasureOn (cubeSet Q) (cubeSet R) ≤
          volumeMeasureOn (cubeSet Q) Set.univ :=
      MeasureTheory.measure_mono (Set.subset_univ (cubeSet R))
    have hUniv_lt : volumeMeasureOn (cubeSet Q) Set.univ < ⊤ := by
      simp [volumeMeasureOn, volume_cubeSet_lt_top Q]
    exact ne_of_lt (lt_of_le_of_lt hle hUniv_lt)
  have hEq :
      (canonicalUpperImageIndicatorTestStateCubeSet R i).eval =
        (cubeSet R).indicator
          (fun _ : Vec d => ((Pi.single i 1, 0) : BlockVec d)) := by
    funext x
    by_cases hx : x ∈ cubeSet R
    · simp [canonicalUpperImageIndicatorTestStateCubeSet, BlockState.eval, hx]
    · simp [canonicalUpperImageIndicatorTestStateCubeSet, BlockState.eval, hx]
  rw [hEq]
  exact
    MeasureTheory.memLp_indicator_const
      (μ := volumeMeasureOn (cubeSet Q)) (p := (2 : ℝ≥0∞))
      (s := cubeSet R) (hs := measurableSet_cubeSet R)
      (c := ((Pi.single i 1, 0) : BlockVec d)) (Or.inr hR_ne_top)

theorem canonicalLowerImageIndicatorTestStateCubeSet_memBlockL2
    {d : ℕ} (Q R : TriadicCube d) (i : Fin d) :
    MemBlockL2 (cubeSet Q) (canonicalLowerImageIndicatorTestStateCubeSet R i).eval := by
  classical
  have hR_ne_top : volumeMeasureOn (cubeSet Q) (cubeSet R) ≠ ⊤ := by
    have hle :
        volumeMeasureOn (cubeSet Q) (cubeSet R) ≤
          volumeMeasureOn (cubeSet Q) Set.univ :=
      MeasureTheory.measure_mono (Set.subset_univ (cubeSet R))
    have hUniv_lt : volumeMeasureOn (cubeSet Q) Set.univ < ⊤ := by
      simp [volumeMeasureOn, volume_cubeSet_lt_top Q]
    exact ne_of_lt (lt_of_le_of_lt hle hUniv_lt)
  have hEq :
      (canonicalLowerImageIndicatorTestStateCubeSet R i).eval =
        (cubeSet R).indicator
          (fun _ : Vec d => ((0, Pi.single i 1) : BlockVec d)) := by
    funext x
    by_cases hx : x ∈ cubeSet R
    · simp [canonicalLowerImageIndicatorTestStateCubeSet, BlockState.eval, hx]
    · simp [canonicalLowerImageIndicatorTestStateCubeSet, BlockState.eval, hx]
  rw [hEq]
  exact
    MeasureTheory.memLp_indicator_const
      (μ := volumeMeasureOn (cubeSet Q)) (p := (2 : ℝ≥0∞))
      (s := cubeSet R) (hs := measurableSet_cubeSet R)
      (c := ((0, Pi.single i 1) : BlockVec d)) (Or.inr hR_ne_top)

/-- Average over `R` of the upper component of the coefficient-operator image
of the selected doubled-`Mu` minimizer on `Q`. -/
noncomputable def canonicalDoubledMuResponseUpperImageAverageCubeSet
    {d : ℕ} (Q R : TriadicCube d) (p q : Vec d) :
    CoeffField d → Vec d :=
  fun a i =>
    cubeVolume Q * (cubeVolume R)⁻¹ *
      canonicalMuHilbertEnergyBilinFixedCubeSet Q (-p, q)
        (canonicalUpperImageIndicatorTestStateCubeSet R i)
        (canonicalUpperImageIndicatorTestStateCubeSet_memBlockL2 Q R i) a

/-- Average over `R` of the lower component of the coefficient-operator image
of the selected doubled-`Mu` minimizer on `Q`. -/
noncomputable def canonicalDoubledMuResponseLowerImageAverageCubeSet
    {d : ℕ} (Q R : TriadicCube d) (p q : Vec d) :
    CoeffField d → Vec d :=
  fun a i =>
    cubeVolume Q * (cubeVolume R)⁻¹ *
      canonicalMuHilbertEnergyBilinFixedCubeSet Q (-p, q)
        (canonicalLowerImageIndicatorTestStateCubeSet R i)
        (canonicalLowerImageIndicatorTestStateCubeSet_memBlockL2 Q R i) a

/-- Ch4 measurable representative of the raw scalar response-maximizer gradient
average over a descendant cube `R`.

Mathematically this is `avg_R grad v(·, Q, p, q; a)`: it is extracted from the
selected doubled-`Mu` minimizer by adding its potential projection and the
lower coefficient-operator image. -/
noncomputable def canonicalScalarResponseGradientAverageCubeSet
    {d : ℕ} (Q R : TriadicCube d) (p q : Vec d) :
    CoeffField d → Vec d :=
  fun a =>
    canonicalDoubledMuResponsePotentialFieldAverageCubeSet Q R p q a +
      canonicalDoubledMuResponseLowerImageAverageCubeSet Q R p q a

/-- Ch4 measurable representative of the raw scalar response-maximizer flux
average over a descendant cube `R`.

Mathematically this is `avg_R a grad v(·, Q, p, q; a)`: it is extracted from
the selected doubled-`Mu` minimizer by adding its flux projection and the upper
coefficient-operator image. -/
noncomputable def canonicalScalarResponseFluxAverageCubeSet
    {d : ℕ} (Q R : TriadicCube d) (p q : Vec d) :
    CoeffField d → Vec d :=
  fun a =>
    canonicalDoubledMuResponseFluxFieldAverageCubeSet Q R p q a +
      canonicalDoubledMuResponseUpperImageAverageCubeSet Q R p q a

/-- Finite-depth weak norm of the raw scalar response-maximizer gradient
defect `grad v_m - p0`. -/
noncomputable def canonicalScalarResponseGradientWeakNormPartialCubeSet
    {d : ℕ} (Q : TriadicCube d) (s : ℝ) (N : ℕ) (p q p0 : Vec d) :
    CoeffField d → ℝ :=
  fun a =>
    ∑ j ∈ Finset.range (N + 1),
      Real.rpow (3 : ℝ) (-s * (j : ℝ)) *
        Real.sqrt
          (descendantsAverage Q j fun R =>
            vecNormSq (canonicalScalarResponseGradientAverageCubeSet Q R p q a - p0))

/-- Finite-depth weak norm of the raw scalar response-maximizer flux defect
`a grad v_m - q0`. -/
noncomputable def canonicalScalarResponseFluxWeakNormPartialCubeSet
    {d : ℕ} (Q : TriadicCube d) (t : ℝ) (N : ℕ) (p q q0 : Vec d) :
    CoeffField d → ℝ :=
  fun a =>
    ∑ j ∈ Finset.range (N + 1),
      Real.rpow (3 : ℝ) (-t * (j : ℝ)) *
        Real.sqrt
          (descendantsAverage Q j fun R =>
            vecNormSq (canonicalScalarResponseFluxAverageCubeSet Q R p q a - q0))

/-- Full weak norm of the raw scalar response-maximizer gradient defect. -/
noncomputable def canonicalScalarResponseGradientWeakNormCubeSet
    {d : ℕ} (Q : TriadicCube d) (s : ℝ) (p q p0 : Vec d) :
    CoeffField d → ℝ :=
  fun a => ⨆ N : ℕ, canonicalScalarResponseGradientWeakNormPartialCubeSet Q s N p q p0 a

/-- Full weak norm of the raw scalar response-maximizer flux defect. -/
noncomputable def canonicalScalarResponseFluxWeakNormCubeSet
    {d : ℕ} (Q : TriadicCube d) (t : ℝ) (p q q0 : Vec d) :
    CoeffField d → ℝ :=
  fun a => ⨆ N : ℕ, canonicalScalarResponseFluxWeakNormPartialCubeSet Q t N p q q0 a

private theorem isPotentialZeroTraceOn_of_potentialZeroTraceFieldOn
    {d : ℕ} {U : Set (Vec d)} {f : Vec d → Vec d}
    (hf : Book.Ch01.PotentialZeroTraceFieldOn U f) :
    IsPotentialZeroTraceOn U f := by
  rcases hf with ⟨_hmem, φ, hφ⟩
  exact IsPotentialZeroTraceOn.congr_ae hφ.symm φ.isPotentialZeroTraceOn

private theorem isBlockMuAdmissible_openCubeSet_of_isDoubledMuAdmissible
    {d : ℕ} {Q : TriadicCube d} {P0 : BlockVec d} {X : Ch02.DoubledField d}
    (hX : Ch02.IsDoubledMuAdmissible (Ch02.cubeDomain Q) P0 X) :
    IsBlockMuAdmissible (openCubeSet Q) P0
      ({ potential := X.potential, flux := X.flux } : BlockState d) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · simpa [Ch02.cubeDomain_coe] using hX.1.1
  · simpa [Ch02.cubeDomain_coe] using
      isPotentialZeroTraceOn_of_potentialZeroTraceFieldOn hX.1
  · simpa [Ch02.cubeDomain_coe] using hX.2.1
  · simpa [Ch02.cubeDomain_coe] using! hX.2.2

/-- A pointwise Ch2 doubled-`Mu` minimizer on the open cube represents the
canonical Ch4 Hilbert minimizer selected on the corresponding half-open cube.

This is the bridge from the pointwise variational theorem used by Ch2
extraction to the measurable Hilbert minimizer used by Ch4. -/
theorem exists_isBlockMuAdmissible_cubeSet_and_hilbert_eq_canonicalAEEMuHilbertMinimizer_of_isDoubledMuMinimizer
    {d : ℕ} [NeZero d] (Q : TriadicCube d) (k : ℕ)
    (a : {a : CoeffField d // AEEQuantitativeEllipticSlice (cubeSet Q) k a})
    (P0 : BlockVec d) (aQ : Ch02.CoeffOn (Ch02.cubeDomain Q))
    (haQ : aQ.toCoeffField = a.1) {X : Ch02.DoubledField d}
    (hX : Ch02.IsDoubledMuMinimizer (Ch02.cubeDomain Q) aQ P0 X) :
    ∃ hAdm :
        IsBlockMuAdmissible (cubeSet Q) P0
          ({ potential := X.potential, flux := X.flux } : BlockState d),
      toHilbertBlockL2OfBlockField (U := cubeSet Q) hAdm.memBlockL2_eval =
        ((canonicalAEEMuOperatorSystemData Q k a).toMuHilbertRealization).minimizerMap P0 := by
  classical
  let Xold : BlockState d := { potential := X.potential, flux := X.flux }
  have hOpen : IsBlockMuAdmissible (openCubeSet Q) P0 Xold := by
    simpa [Xold] using
      isBlockMuAdmissible_openCubeSet_of_isDoubledMuAdmissible (Q := Q) (P0 := P0) hX.1
  have hCube : IsBlockMuAdmissible (cubeSet Q) P0 Xold :=
    (isBlockMuAdmissible_cubeSet_triadicCube_iff_openCubeSet (Q := Q)).2 hOpen
  refine ⟨hCube, ?_⟩
  let system : AEEMuOperatorSystemData (cubeSet Q) a.1 :=
    canonicalAEEMuOperatorSystemData Q k a
  let H : MuHilbertRealization (cubeSet Q) a.1 := system.toMuHilbertRealization
  let HX : HilbertBlockL2 (cubeSet Q) :=
    toHilbertBlockL2OfBlockField (U := cubeSet Q) hCube.memBlockL2_eval
  have hEnergyOpen :
      blockEnergyAverage (openCubeSet Q) a.1 Xold =
        Mu (openCubeSet Q) P0 a.1 := by
    calc
      blockEnergyAverage (openCubeSet Q) a.1 Xold =
          blockEnergyAverage (openCubeSet Q) aQ.toCoeffField Xold := by
            simp [haQ]
      _ = Ch02.doubledMuValue (Ch02.cubeDomain Q) aQ X := by
            rfl
      _ = Ch02.doubledMu (Ch02.cubeDomain Q) aQ P0 :=
            hX.doubledMuValue_eq_doubledMu
      _ = Mu (openCubeSet Q) P0 aQ.toCoeffField := by
            rw [Ch02.doubledMu_eq_Mu]
            simp [Ch02.cubeDomain_coe]
      _ = Mu (openCubeSet Q) P0 a.1 := by
            simp [haQ]
  have hEnergyCube :
      blockEnergyAverage (cubeSet Q) a.1 Xold =
        Mu (cubeSet Q) P0 a.1 := by
    calc
      blockEnergyAverage (cubeSet Q) a.1 Xold =
          blockEnergyAverage (openCubeSet Q) a.1 Xold :=
            ScalarCanonicalMaximizer.volumeAverage_cubeSet_eq_openCubeSet_of_triadicCube
              Q (blockEnergyDensity a.1 Xold)
      _ = Mu (openCubeSet Q) P0 a.1 := hEnergyOpen
      _ = Mu (cubeSet Q) P0 a.1 := by
            exact (Mu_cubeSet_eq_openCubeSet_of_triadicCube
              (Q := Q) (P := P0) (a := a.1)).symm
  have hcorr :
      HX - H.constantField P0 ∈ H.correctionSpace.correctionSpace := by
    have hsplit := hCube.toHilbertBlockL2OfBlockField_eq_blockVecToHilbertBlockL2Const_add
    rw [show HX = toHilbertBlockL2OfBlockField (U := cubeSet Q) hCube.memBlockL2_eval
      from rfl, hsplit]
    have hmem := hCube.toCorrectionFieldData_mem_correctionSpace
    simpa [H, system, AEEMuOperatorSystemData.toMuHilbertRealization,
      MuOperatorRealization.toMuHilbertRealization, MuHilbertRealization.ofOperator,
      canonicalAEEMuOperatorSystemData, canonicalAEEMuCorrectionSpaceData,
      canonicalAEEPotentialSolenoidalL2Data, MuCorrectionSpaceData.ofSubmoduleClosures,
      sub_eq_add_neg, add_assoc, add_comm] using hmem
  have hQuadEq :
      quadraticEnergy H.energyBilin HX =
        blockEnergyAverage (cubeSet Q) a.1 Xold := by
    simpa [H, system, HX, Xold, AEEMuOperatorSystemData.toMuHilbertRealization,
      MuOperatorRealization.toMuHilbertRealization, MuHilbertRealization.ofOperator] using
      system.toMuOperatorRealization.quadraticEnergy_eq_blockEnergyAverage_of_blockState
        (X := Xold) hCube.memBlockL2_eval
  have hQuadLe : quadraticEnergy H.energyBilin HX ≤ H.muCandidate P0 := by
    exact le_of_eq <| by
      calc
        quadraticEnergy H.energyBilin HX =
            blockEnergyAverage (cubeSet Q) a.1 Xold := hQuadEq
        _ = Mu (cubeSet Q) P0 a.1 := hEnergyCube
        _ = H.muCandidate P0 := by
              simpa [H, system] using mu_eq_canonicalAEEMuCandidate Q k a P0
  have hEq : HX = H.minimizerMap P0 :=
    H.eq_minimizerMap_of_quadraticEnergy_le_muCandidate P0 HX hcorr hQuadLe
  simpa [HX, H, system, Xold] using hEq


end Ch04
end Book
end Homogenization
