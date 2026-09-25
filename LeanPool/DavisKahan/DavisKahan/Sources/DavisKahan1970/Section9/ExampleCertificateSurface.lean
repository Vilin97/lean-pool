/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, OpenAI GPT-5.6 Thinking
-/
module


public import LeanPool.DavisKahan.DavisKahan.Sources.DavisKahan1970.Section9.DomainLimitation
public import LeanPool.DavisKahan.DavisKahan.Sources.DavisKahan1970.Section9.IndividualAngles
public import LeanPool.DavisKahan.DavisKahan.Sources.DavisKahan1970.Section9.TrialSubspace
public import LeanPool.DavisKahan.DavisKahan.Sources.DavisKahan1970.Section9.WeinbergerComparison

/-!
# Davis--Kahan 1970, Section 9: end-to-end certificate surface

This file assembles the numerical example into an explicit certificate API.
The exact affine calculations are already proved.  The remaining bridge fields
are precisely the outputs that the general sine, tangent, double-angle, and
continuation theorems must supply for the free-beam realization.

Keeping this boundary explicit prevents a finite numerical calculation from
being mistaken for a construction of the unbounded fourth-derivative operator
or a proof of its third-eigenvalue gap.
-/

@[expose] public section

namespace TauCeti
namespace DavisKahan1970
namespace Section9

/-- Exact theorem outputs required to instantiate every numerical conclusion
in Section 9. -/
structure TheoremOutputCertificate (ε : ℝ) where
  /-- The scalar tracked by the largest sine-angle estimate. -/
  sinTheta₁ : ℝ
  /-- The scalar tracked by the largest double-angle sine estimate. -/
  sinTwoTheta₁ : ℝ
  /-- The scalar tracked by the sum-of-sines estimate. -/
  sinThetaSum : ℝ
  /-- The scalar tracked by the sum of double-angle sines. -/
  sinTwoThetaSum : ℝ
  /-- The scalar tracked by the largest tangent-angle estimate. -/
  tanTheta₁ : ℝ
  /-- The scalar tracked by the sum-of-tangents estimate. -/
  tanThetaSum : ℝ
  /-- The scalar tracked by the largest double-angle tangent estimate. -/
  tanTwoTheta₁ : ℝ
  /-- The scalar tracked by the sum of double-angle tangents. -/
  tanTwoThetaSum : ℝ
  /-- The lower individual tangent quantity in the Weinberger comparison. -/
  weinbergerTanPhi₁ : ℝ
  /-- The upper individual tangent quantity in the Weinberger comparison. -/
  weinbergerTanPhi₂ : ℝ
  /-- The lower individual tangent quantity in the direct residual bound. -/
  directTanPhi₁ : ℝ
  /-- The upper individual tangent quantity in the direct residual bound. -/
  directTanPhi₂ : ℝ
  /-- The lower individual angle quantity in the final numerical estimate. -/
  omega₁ : ℝ
  /-- The upper individual angle quantity in the final numerical estimate. -/
  omega₂ : ℝ
  sinTheta₁_exact : sinTheta₁ ≤ residualTopSingularValue ε / 500
  sinTwoTheta₁_exact : sinTwoTheta₁ < 2 * ε / 500
  sinThetaSum_exact : sinThetaSum ≤ residualKyFanTwo ε / 500
  sinTwoThetaSum_exact : sinTwoThetaSum < 4 * ε / 500
  tanTheta₁_exact : tanTheta₁ ≤ tangentThetaExactBound ε
  tanThetaSum_exact : tanThetaSum ≤ tangentThetaExactBound ε
  tanTwoTheta₁_exact : tanTwoTheta₁ ≤ tangentTwoThetaExactBound ε
  tanTwoThetaSum_exact : tanTwoThetaSum ≤ tangentTwoThetaExactBound ε
  weinbergerTanPhi₁_exact :
    weinbergerTanPhi₁ ≤ weinbergerLowerTangentExactBound ε
  weinbergerTanPhi₂_exact :
    weinbergerTanPhi₂ ≤ weinbergerUpperTangentExactBound ε
  directTanPhi₁_exact : directTanPhi₁ ≤ lowerIndividualTangentExactBound ε
  directTanPhi₂_exact : directTanPhi₂ ≤ upperIndividualTangentExactBound ε
  omega₁_exact : omega₁ ≤ lowerIndividualAngleExactBound ε
  omega₂_exact : omega₂ ≤ upperIndividualAngleExactBound ε

/-- Full Section 9 package: analytic finite-data certificate plus outputs of the
perturbation theorems. -/
structure NumericalExampleCertificate (ε : ℝ) where
  /-- The finite beam data required by the numerical example. -/
  finiteData : FreeBeamFiniteDataCertificate ε
  /-- The angle estimates obtained from the perturbation theorems. -/
  theoremOutputs : TheoremOutputCertificate ε

/-- The printed rational bounds, represented without decimal notation. -/
structure PrintedConclusions (ε : ℝ) where
  /-- The scalar tracked by the largest sine-angle estimate. -/
  sinTheta₁ : ℝ
  /-- The scalar tracked by the largest double-angle sine estimate. -/
  sinTwoTheta₁ : ℝ
  /-- The scalar tracked by the sum-of-sines estimate. -/
  sinThetaSum : ℝ
  /-- The scalar tracked by the sum of double-angle sines. -/
  sinTwoThetaSum : ℝ
  /-- The scalar tracked by the largest tangent-angle estimate. -/
  tanTheta₁ : ℝ
  /-- The scalar tracked by the sum-of-tangents estimate. -/
  tanThetaSum : ℝ
  /-- The scalar tracked by the largest double-angle tangent estimate. -/
  tanTwoTheta₁ : ℝ
  /-- The scalar tracked by the sum of double-angle tangents. -/
  tanTwoThetaSum : ℝ
  /-- The lower individual tangent quantity in the Weinberger comparison. -/
  weinbergerTanPhi₁ : ℝ
  /-- The upper individual tangent quantity in the Weinberger comparison. -/
  weinbergerTanPhi₂ : ℝ
  /-- The lower individual tangent quantity in the direct residual bound. -/
  directTanPhi₁ : ℝ
  /-- The upper individual tangent quantity in the direct residual bound. -/
  directTanPhi₂ : ℝ
  /-- The lower individual angle quantity in the final numerical estimate. -/
  omega₁ : ℝ
  /-- The upper individual angle quantity in the final numerical estimate. -/
  omega₂ : ℝ
  bound_9_1 : sinTheta₁ < (811 : ℝ) / 500000 * ε
  bound_9_2 : sinTwoTheta₁ < (1 : ℝ) / 250 * ε
  bound_9_3 : sinThetaSum < (109 : ℝ) / 50000 * ε
  bound_9_4 : sinTwoThetaSum < (1 : ℝ) / 125 * ε
  bound_9_6 : tanTheta₁ <
    ((1291 : ℝ) / 2500000 * ε) /
      (1 - (7887 : ℝ) / 5000000 * ε)
  bound_9_6_sum : tanThetaSum <
    ((1291 : ℝ) / 2500000 * ε) /
      (1 - (7887 : ℝ) / 5000000 * ε)
  bound_9_7 : tanTwoTheta₁ <
    ((1291 : ℝ) / 1250000 * ε) /
      (1 - (7887 : ℝ) / 5000000 * ε)
  bound_9_7_sum : tanTwoThetaSum <
    ((1291 : ℝ) / 1250000 * ε) /
      (1 - (7887 : ℝ) / 5000000 * ε)
  bound_9_8_lower : weinbergerTanPhi₁ <
    ((1291 : ℝ) / 2500000 * ε) /
      (1 - (4227 : ℝ) / 10000000 * ε)
  bound_9_8_upper : weinbergerTanPhi₂ <
    ((1291 : ℝ) / 2500000 * ε) /
      (1 - (7887 : ℝ) / 5000000 * ε)
  direct_lower : directTanPhi₁ <
    ((913 : ℝ) / 2500000 * ε) /
      (1 - (4227 : ℝ) / 10000000 * ε)
  direct_upper : directTanPhi₂ <
    ((913 : ℝ) / 2500000 * ε) /
      (1 - (7887 : ℝ) / 5000000 * ε)
  final_lower : omega₁ <
    ((53 : ℝ) / 100000 * ε) /
      (1 - (43 : ℝ) / 100000 * ε)
  final_upper : omega₂ <
    ((53 : ℝ) / 100000 * ε) /
      (1 - (1 : ℝ) / 625 * ε)

/-- Every printed numerical conclusion follows from the exact certificate. -/
def NumericalExampleCertificate.printedConclusions
    {ε : ℝ} (C : NumericalExampleCertificate ε) : PrintedConclusions ε where
  sinTheta₁ := C.theoremOutputs.sinTheta₁
  sinTwoTheta₁ := C.theoremOutputs.sinTwoTheta₁
  sinThetaSum := C.theoremOutputs.sinThetaSum
  sinTwoThetaSum := C.theoremOutputs.sinTwoThetaSum
  tanTheta₁ := C.theoremOutputs.tanTheta₁
  tanThetaSum := C.theoremOutputs.tanThetaSum
  tanTwoTheta₁ := C.theoremOutputs.tanTwoTheta₁
  tanTwoThetaSum := C.theoremOutputs.tanTwoThetaSum
  weinbergerTanPhi₁ := C.theoremOutputs.weinbergerTanPhi₁
  weinbergerTanPhi₂ := C.theoremOutputs.weinbergerTanPhi₂
  directTanPhi₁ := C.theoremOutputs.directTanPhi₁
  directTanPhi₂ := C.theoremOutputs.directTanPhi₂
  omega₁ := C.theoremOutputs.omega₁
  omega₂ := C.theoremOutputs.omega₂
  bound_9_1 := equation_9_1 ε C.theoremOutputs.sinTheta₁
    C.finiteData.epsilon_pos C.theoremOutputs.sinTheta₁_exact
  bound_9_2 := equation_9_2 ε C.theoremOutputs.sinTwoTheta₁
    C.theoremOutputs.sinTwoTheta₁_exact
  bound_9_3 := equation_9_3 ε C.theoremOutputs.sinThetaSum
    C.finiteData.epsilon_pos C.theoremOutputs.sinThetaSum_exact
  bound_9_4 := equation_9_4 ε C.theoremOutputs.sinTwoThetaSum
    C.theoremOutputs.sinTwoThetaSum_exact
  bound_9_6 := equation_9_6 ε C.theoremOutputs.tanTheta₁
    C.finiteData.epsilon_pos C.finiteData.epsilon_lt_hundred
    C.theoremOutputs.tanTheta₁_exact
  bound_9_6_sum := equation_9_6 ε C.theoremOutputs.tanThetaSum
    C.finiteData.epsilon_pos C.finiteData.epsilon_lt_hundred
    C.theoremOutputs.tanThetaSum_exact
  bound_9_7 := equation_9_7 ε C.theoremOutputs.tanTwoTheta₁
    C.finiteData.epsilon_pos C.finiteData.epsilon_lt_hundred
    C.theoremOutputs.tanTwoTheta₁_exact
  bound_9_7_sum := equation_9_7 ε C.theoremOutputs.tanTwoThetaSum
    C.finiteData.epsilon_pos C.finiteData.epsilon_lt_hundred
    C.theoremOutputs.tanTwoThetaSum_exact
  bound_9_8_lower := equation_9_8_lower ε C.theoremOutputs.weinbergerTanPhi₁
    C.finiteData.epsilon_pos C.finiteData.epsilon_lt_hundred
    C.theoremOutputs.weinbergerTanPhi₁_exact
  bound_9_8_upper := equation_9_8_upper ε C.theoremOutputs.weinbergerTanPhi₂
    C.finiteData.epsilon_pos C.finiteData.epsilon_lt_hundred
    C.theoremOutputs.weinbergerTanPhi₂_exact
  direct_lower := direct_lower_individual_vector_bound ε C.theoremOutputs.directTanPhi₁
    C.finiteData.epsilon_pos C.finiteData.epsilon_lt_hundred
    C.theoremOutputs.directTanPhi₁_exact
  direct_upper := direct_upper_individual_vector_bound ε C.theoremOutputs.directTanPhi₂
    C.finiteData.epsilon_pos C.finiteData.epsilon_lt_hundred
    C.theoremOutputs.directTanPhi₂_exact
  final_lower := final_lower_individual_angle_bound ε C.theoremOutputs.omega₁
    C.finiteData.epsilon_pos C.finiteData.epsilon_lt_hundred
    C.theoremOutputs.omega₁_exact
  final_upper := final_upper_individual_angle_bound ε C.theoremOutputs.omega₂
    C.finiteData.epsilon_pos C.finiteData.epsilon_lt_hundred
    C.theoremOutputs.omega₂_exact

end Section9
end DavisKahan1970
end TauCeti
