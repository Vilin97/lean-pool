/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, OpenAI GPT-5.6 Thinking
-/
module

public import LeanPool.DavisKahan.DavisKahan.Sources.DavisKahan1970.Ideals.All
public import LeanPool.DavisKahan.DavisKahan.Sources.DavisKahan1970.SineTheta.All
public import LeanPool.DavisKahan.DavisKahan.Sources.DavisKahan1970.SineTheta.FiniteMultiplicity
public import LeanPool.DavisKahan.DavisKahan.Sources.DavisKahan1970.GeneralSinTheta

/-! # Sine Theta Source Inventory -/

@[expose] public section

open TauCeti.DavisKahan.Sylvester

/-!
# Literal Davis--Kahan 1970 sine-theta surface

This source facade names every sine-theta declaration needed for a line-by-line
comparison with Sections 1 and 6 and the unbounded appendix of the paper.  The
previous `GeneralSinTheta` facade remains the accepted central theorem.  This
module adds the exact source norm, source angle, symmetric theorem, second
generalized theorem, common-domain forms, and optimality statements.
-/

namespace TauCeti
namespace DavisKahan1970

-- Lean has no namespace-alias command, so the paper implementation namespace
-- is opened directly; every unprefixed `Paper...` name below resolves into it.
open DavisKahan.ExactSinTheta

/-! ## Source norm class -/

-- `SymmetricNormingFunction` and its `.Axiomatic` presentation are named
-- directly; the former `UnitaryInvariantNorm` / `SymmetricNormingFunction`
-- aliases duplicated the canonical names and are gone.
/-- The dimension-coherent and axiomatic presentations of a normalized symmetric
norming function are equivalent, so quantifying over the former excludes no norm
in the source class. -/
alias symmetricNormingFunctionEquivAxiomatic :=
  SymmetricNormingFunction.Axiomatic.equiv

/-- The induced norm is submultiplicative under composition with bounded
operators, which is what makes its finiteness locus an operator ideal. -/
alias symmetricNormingFunction_operator_laws :=
  SymmetricNormingFunction.gauge_comp_le

/-- The induced norm is definite on its ideal: it vanishes only at zero. -/
alias symmetricNormingFunction_definite :=
  SymmetricNormingFunction.gauge_eq_zero_iff
alias nuclearNorm := nuclearNormingFunction
/-- The source norm class is inhabited, so the universally quantified Section 2
theorems are not vacuous. -/
alias sourceNormClass_nonempty := symmetricNormingFunction_nonempty

/-! ## Literal angle objects -/

alias directedCosineBlock := cosineBlockC
alias directedSineBlock := sineBlockC
alias directedCosineOperator := cosineBlockModulusC
alias directedAngleComplex := directedAngleBlockC
alias directedSinAngleComplex := directedSinAngleBlockC
alias directedCosAngleComplex := directedCosAngleBlockC
alias directedCosAngle_eq_modulus := sourceDirectedCosC_eq
alias directedSinAngle_eq_modulus :=
  directedSinAngleBlockC_eq_sineBlockModulusC
alias directedSinAngle_singularValues :=
  directedSinAngleBlock_same_sineBlock
alias directedAngle_eq_arcsin_sineModulus :=
  sourceDirectedAngleC_eq_arcsin_sineModulus
alias directedAngle_real_eq_arcsin_sineModulus :=
  sourceDirectedAngleR_eq_arcsin_sineModulus
alias directedAngleReal := sourceDirectedAngleR
alias directedSinAngleReal := sourceDirectedSinR
alias directedCosAngleReal := sourceDirectedCosR
alias fullAngleCoordinatesComplex := fullAngleBlockC
alias fullSinAngleCoordinatesComplex := fullSinAngleBlockC
alias fullSinAngle_singularValues_projectionDifference :=
  sourceFullSin_same_projectionDifference
alias fullSinAngle_norm_projectionDifference :=
  sourceFullSin_mem_iff_and_gauge_eq
alias ambientEquivalentAngle := DavisKahan.Angle.angleOperatorC
alias ambientEquivalentSinAngle := DavisKahan.Angle.sinAngleOperatorC
alias fullAngleCoordinatesReal := sourceFullAngleR
alias fullSinAngleCoordinatesReal := sourceFullSinR

/-! ## Lemmas 6.1 and 6.2 -/

alias lemma6_1_kyFan := lemma61_all_kyFan
alias lemma6_1 := lemma61_every_unitarilyInvariantNorm
alias lemma6_1_converse := lemma61_converse
alias lemma6_2 := diagonalPair_normingGauge_le
alias lemma6_2_kyFan := diagonalPair_all_kyFan_le

/-! ## Original and generalized sine theorems -/

alias GeneralSinThetaIdealFamilyProblem := GeneralSinThetaRepresentativeProblem
alias IsometricSinThetaIdealFamilyProblem := IsometricSinThetaRepresentativeProblem
alias RealGeneralSinThetaIdealFamilyProblem := RealGeneralSinThetaRepresentativeProblem
alias RealIsometricSinThetaIdealFamilyProblem := RealIsometricSinThetaRepresentativeProblem
alias sinTheta_generalized_idealFamily_complex := GeneralSinThetaRepresentativeProblem.result
alias sinTheta_idealFamily_complex := IsometricSinThetaRepresentativeProblem.result
alias sinTheta_generalized_idealFamily_real :=
  RealGeneralSinThetaRepresentativeProblem.result
alias sinTheta_idealFamily_real := RealIsometricSinThetaRepresentativeProblem.result

alias IsometricSinThetaPaperData := IsometricTheoremData
alias sinTheta_paperData_complex :=
  IsometricTheoremData.result_every_unitarilyInvariantNorm_across
alias RealIsometricSinThetaPaperData := RealIsometricTheoremData
alias sinTheta_paperData_real :=
  RealIsometricTheoremData.result_every_unitarilyInvariantNorm_across

alias Theorem6Point1Data := Theorem61Data
-- **The canonical source theorems are `DavisKahan1970.theorem6_1_complex`
-- and `..._real`** in `Sources/DavisKahan1970/Theorem61.lean`.  They take the
-- components -- ambient/trial/complementary operators, coordinate maps, residual,
-- `IsTrialResidualEquation`, `IsExactSpectralDecomposition`, the frame bound and
-- the gap -- rather than a `Theorem61Data` record.  The capitalized
-- `Theorem6_1_{complex,real}` aliases for the record methods were deleted on
-- 2026-09-05: they differed from the canonical names only in case, which the
-- 2026-09-04 hostile review flagged (F6.2) as a name a reader cannot tell apart
-- from the theorem it is not.  Cite `Theorem61Data.result_*` for the record form.
alias Theorem6Point1RealData := RealTheorem61Data
alias sinTheta_generalized_paperData_complex :=
  Theorem61Data.result_every_unitarilyInvariantNorm_across
alias sinTheta_generalized_paperData_real :=
  RealTheorem61Data.result_every_unitarilyInvariantNorm_across

/-! ## Proposition 6.1

**The canonical source theorems are `DavisKahan1970.proposition6_1_complex`
and `..._real` in `Sources/DavisKahan1970/Proposition61.lean`.**  They take the
operators, the reducing subspaces, the gap and the two separations directly.
The aliases below are the implementation and compatibility API: a caller who
already holds a `SymmetricSinThetaProblem` can still use them, but nobody should
have to build one.  The two capitalized `Proposition6_1_{complex,real}` aliases
were deleted on 2026-09-05 as case twins of the canonical names (F6.2); cite
`SymmetricSinThetaProblem.result_*` for the record form. -/

alias SymmetricSinThetaProblem := SymmetricSinThetaProblem

-- The real-scalar form.  A unitarily invariant norm sees only the complete
-- singular-value sequence, so the real conclusion is carried by
-- `crossSineSum U V` rather than by a functional-calculus sine: no real
-- continuous functional calculus is needed, and none is assumed.
-- `proposition6_1_real_sinTheta_singularValues` is the compiled certificate that
-- this operator carries exactly the paper's whole-space `sin Theta` sequence,
-- and `proposition6_1_real_representative` states the estimate for an arbitrary
-- operator with that sequence.
alias RealSymmetricSinThetaProblem := RealSymmetricSinThetaProblem
alias proposition6_1_real_kyFan :=
  RealSymmetricSinThetaProblem.symmetric_all_kyFan_real
alias proposition6_1_real_sinTheta_singularValues :=
  RealSymmetricSinThetaProblem.crossSineSum_normingMem_iff_and_gauge_eq
alias proposition6_1_real_sinTheta_eq_literalFullSinAngle :=
  approximationNumber_sourceFullSinR_eq_crossSineSum
alias proposition6_1_real_representative :=
  RealSymmetricSinThetaProblem.result_every_unitarilyInvariantNorm_representative_real

/-! ## Theorem 6.2 and its printed finite-rank consequence

**The canonical source theorems are `DavisKahan1970.theorem6_2_complex`
and `..._real`** in `Sources/DavisKahan1970/Theorem61.lean`, on the same
component hypotheses as Theorem 6.1.  The aliases below are the record methods
they call; the two capitalized `Theorem6_2_{complex,real}` case twins were
deleted on 2026-09-05 (F6.2), so cite `Theorem62Data.result_across` and
`RealTheorem62Data.result_across` for the record form. -/

alias PairwiseSpectrumGap := PairwiseSpectrumGap
alias Theorem6Point2Data := Theorem62Data
alias Theorem6_2_boundNorm_of_finiteRank :=
  Theorem62Data.operatorNorm_result_across_of_rank_le
alias Theorem6Point2RealData := RealTheorem62Data
alias Theorem6_2_real_boundNorm_of_finiteRank :=
  RealTheorem62Data.operatorNorm_result_across_of_rank_le

/-! ## Exact unbounded appendix forms -/

alias CommonDomainSinThetaData := CommonDomainSinThetaData
alias CommonDomainTheorem6Point1Data := CommonDomainTheorem61Data
alias theorem6_1_commonDomain :=
  CommonDomainTheorem61Data.result_every_unitarilyInvariantNorm_across
alias CommonDomainTheorem6Point2Data := CommonDomainTheorem62Data
alias Theorem6_2_commonDomain := CommonDomainTheorem62Data.result_across
alias Theorem6_2_commonDomain_boundNorm_of_finiteRank :=
  CommonDomainTheorem62Data.operatorNorm_result_of_rank_le
-- The Appendix says "the hypotheses of Proposition 6.1 and Theorem 6.1 may be
-- relaxed similarly".  This is that relaxation of Proposition 6.1: two closed
-- self-adjoint operators on one dense domain, whose difference there is the
-- paper's bounded `H`.  `proposition6Point1CommonDomainOfBounded` records that the
-- bounded inputs are an instance, so nothing is assumed that Proposition 6.1 did
-- not already assume.
alias CommonDomainSymmetricSinThetaProblem :=
  CommonDomainSymmetricSinThetaProblem
alias proposition6_1_commonDomain :=
  CommonDomainSymmetricSinThetaProblem.result_every_unitarilyInvariantNorm
alias proposition6_1_commonDomain_kyFan :=
  CommonDomainSymmetricSinThetaProblem.symmetric_all_kyFan
alias proposition6Point1CommonDomainOfBounded :=
  CommonDomainSymmetricSinThetaProblem.ofBounded
-- The common-domain Proposition 6.1 is stated over any `RCLike` field.  Its
-- scalar-generic conclusion is carried by `crossSineSum U V` rather than by
-- a functional-calculus sine, for the same reason as in the bounded real file:
-- a unitarily invariant norm sees only the singular-value sequence, and the block
-- form is what the proof produces.  Until 2026-09-03 the reason given was that no
-- real continuous functional calculus was constructed; one now is, at every
-- `RCLike` field, so `TauCeti.DavisKahan.Angle.sinAngleOperator` could name the
-- conclusion directly.  Restating it that way is a separate change and would move
-- this theorem's statement pin.
-- `proposition6_1_commonDomain_sinTheta_singularValues` is the compiled
-- certificate that this operator carries exactly the paper's whole-space
-- `sin Theta` sequence.  Over `ℂ` the literal form is `proposition6_1_commonDomain`
-- itself.  `proposition6Point1RealCommonDomainOfBounded` records that the real
-- bounded inputs are an instance, so the real form is a relaxation of the real
-- Proposition 6.1 rather than a statement parallel to it.
alias proposition6_1_commonDomain_crossSineSum :=
  CommonDomainSymmetricSinThetaProblem.result_every_unitarilyInvariantNorm_crossSineSum
alias proposition6_1_commonDomain_crossSineSum_kyFan :=
  CommonDomainSymmetricSinThetaProblem.symmetric_all_kyFan_crossSineSum
alias proposition6_1_commonDomain_sinTheta_singularValues :=
  CommonDomainSymmetricSinThetaProblem.crossSineSum_normingMem_iff_and_gauge_eq
alias proposition6_1_real_commonDomain :=
  CommonDomainSymmetricSinThetaProblem.result_every_unitarilyInvariantNorm_real
alias proposition6_1_real_commonDomain_kyFan :=
  CommonDomainSymmetricSinThetaProblem.symmetric_all_kyFan_real
alias proposition6Point1RealCommonDomainOfBounded :=
  CommonDomainSymmetricSinThetaProblem.ofBoundedReal
alias RealCommonDomainTheorem6Point1Data :=
  RealCommonDomainTheorem61Data
alias theorem6_1_real_commonDomain :=
  RealCommonDomainTheorem61Data.result_every_unitarilyInvariantNorm_across
alias RealCommonDomainTheorem6Point2Data :=
  RealCommonDomainTheorem62Data
alias theorem6_2_real_commonDomain :=
  RealCommonDomainTheorem62Data.result_across
alias Theorem6_2_real_commonDomain_boundNorm_of_finiteRank :=
  RealCommonDomainTheorem62Data.operatorNorm_result_of_rank_le

/-! ## Graph-core appendix forms -/

alias IsGraphCore := PartialMap.IsGraphCore
alias CommonCoreResidualData := CommonCoreResidualData
alias commonCoreResidual_extends_to_domain :=
  CommonCoreResidualData.extends_to_domain
alias CommonCoreTheorem6Point1Data := CommonCoreTheorem61Data
alias theorem6_1_commonCore :=
  CommonCoreTheorem61Data.result_every_unitarilyInvariantNorm_across
alias CommonCoreTheorem6Point2Data := CommonCoreTheorem62Data
alias Theorem6_2_commonCore := CommonCoreTheorem62Data.result_across
alias RealCommonCoreTheorem6Point1Data := RealCommonCoreTheorem61Data
alias theorem6_1_real_commonCore :=
  RealCommonCoreTheorem61Data.result_every_unitarilyInvariantNorm_across
alias RealCommonCoreTheorem6Point2Data := RealCommonCoreTheorem62Data
alias theorem6_2_real_commonCore :=
  RealCommonCoreTheorem62Data.result_across

/-! ## Sharpness and necessity -/

alias Theorem6_1_equality_every_norm :=
  theorem61_planar_equality_every_norm
alias sineTheta_constant_one_optimal := sinTheta_constant_one_optimal
alias oneGap_counterexample_sine_squareNorm :=
  counterexample_sine_square_norm
alias oneGap_counterexample_perturbation_squareNorm :=
  counterexample_perturbation_square_norm
alias oneGap_does_not_imply_Proposition6_1 :=
  oneGap_does_not_imply_symmetric_square_estimate

end DavisKahan1970
end TauCeti
