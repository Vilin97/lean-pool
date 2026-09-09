/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.PacketConstructedProfiles
public import LeanPool.NavierStokesAndEuler.Euler.PacketSourceOperators

/-!
# Qualitative admissibility of the actual source packet recursion

The data are the prescribed coefficients, the common time interval and the
initial transverse datum. Every profile and every later forcing witness is
constructed; no prefix regularity hypothesis remains.
-/

@[expose] public section


noncomputable section

namespace EulerPacketCylinderField

open Set EulerSmoothLimit EulerPacketProfileRecursion

variable (P : ℝ) [Fact (0 < P)] (M : EulerMeanPacketProvider.Data)
  {U : Type*} [NormedAddCommGroup U] [InnerProductSpace ℝ U] [CompleteSpace U]
  (D : EulerTransversePacketProvider.Data U) (hT : M.T = D.T)
  (I Iprimary : EulerTransversePacketProvider.InitialData P D)

/-- Source profiles, given by `profiles (sourceOperators P M D I) (homogeneousPrimary D Iprimary
(sourceOperators P M D I))`. -/
def sourceProfiles : ℕ → Profile :=
  profiles (sourceOperators P M D I) (homogeneousPrimary D Iprimary (sourceOperators P M D I))

/-- Source profile witness, given by `constructedProfileWitness M D hT I Iprimary
(sourceCoefficientData P M D I hT) rfl rfl rfl p`. -/
def sourceProfileWitness (p : ℕ) :
    ProfileRegularity P M.T M.T_pos.le D.support (sourceProfiles P M D I Iprimary p) :=
  constructedProfileWitness M D hT I Iprimary (sourceCoefficientData P M D I hT) rfl rfl rfl p

/-- Source mean forcing, given by `constructedMeanForcing M D hT I Iprimary
(sourceCoefficientData P M D I hT) rfl rfl rfl p hp`. -/
def sourceMeanForcing (p : ℕ) (hp : 2 ≤ p) :
    EulerMeanPacketProvider.Forcing M
      (meanForce (sourceOperators P M D I) p (sourceProfiles P M D I Iprimary)) :=
  constructedMeanForcing M D hT I Iprimary (sourceCoefficientData P M D I hT) rfl rfl rfl p hp

/-- Source high forcing, given by `constructedHighForcing M D hT I Iprimary
(sourceCoefficientData P M D I hT) rfl rfl rfl p hp`. -/
def sourceHighForcing (p : ℕ) (hp : 2 ≤ p) :
    EulerTransversePacketProvider.Forcing P D
      (highForce (sourceOperators P M D I) p (sourceProfiles P M D I Iprimary)) :=
  constructedHighForcing M D hT I Iprimary (sourceCoefficientData P M D I hT) rfl rfl rfl p hp

end EulerPacketCylinderField
