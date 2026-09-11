/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import LeanPool.NavierStokesAndEuler.Euler.PacketSourceOperators
public import LeanPool.NavierStokesAndEuler.Euler.PacketProfilesRegularity
public import LeanPool.NavierStokesAndEuler.Euler.PacketPrimaryRegularity

/-!
# Qualitative admissibility of the actual source packet recursion

The data are the prescribed coefficients, the common time interval and the
initial transverse datum. Every profile and every later forcing witness is
constructed; no prefix regularity hypothesis remains.
-/

section

/-!
# Actual homogeneous primary and recursively solved profiles

The initial transverse datum and coefficient data determine every profile.
Admissibility at all later grades follows from the genuine nonlinear paths,
the source mean inverse and the source transverse inverse.
-/

@[expose] public section

noncomputable section

namespace EulerPacketCylinderField

open Set EulerSmoothLimit EulerPacketProfileRecursion

variable {P : ℝ} [Fact (0 < P)] (M : EulerMeanPacketProvider.Data)
  {U : Type*} [NormedAddCommGroup U] [InnerProductSpace ℝ U] [CompleteSpace U]
  (D : EulerTransversePacketProvider.Data U) (hT : M.T = D.T)
  (I Iprimary : EulerTransversePacketProvider.InitialData P D)
  {O : Operators} (C : CoefficientData P M.T O)
  (hmean : O.meanSolve = EulerMeanPacketProvider.meanSolve M)
  (hhigh : O.highSolve = EulerTransversePacketProvider.highSolve P D I)
  (hcorrector : O.curlCorrector = D.curlCorrector P)

/-- Constructed profile witness, constructed using `profileWitness`. -/
def constructedProfileWitness (p : ℕ) :
    ProfileRegularity P M.T M.T_pos.le D.support (profiles O (homogeneousPrimary D Iprimary O) p) :=
  profileWitness M D hT I C hmean hhigh hcorrector (homogeneousPrimary D Iprimary O)
    ((homogeneousPrimaryRegularity D Iprimary O hcorrector).changeTime hT.symm M.T_pos.le) p

/-- Constructed mean forcing, constructed using `profilesMeanForcing`. -/
def constructedMeanForcing (p : ℕ) (hp : 2 ≤ p) :
    EulerMeanPacketProvider.Forcing M
      (meanForce O p (profiles O (homogeneousPrimary D Iprimary O))) :=
  profilesMeanForcing M D hT I C hmean hhigh hcorrector (homogeneousPrimary D Iprimary O)
    ((homogeneousPrimaryRegularity D Iprimary O hcorrector).changeTime hT.symm M.T_pos.le) p hp

/-- Constructed high forcing, constructed using `profilesHighForcing`. -/
def constructedHighForcing (p : ℕ) (hp : 2 ≤ p) :
    EulerTransversePacketProvider.Forcing P D
      (highForce O p (profiles O (homogeneousPrimary D Iprimary O))) :=
  profilesHighForcing M D hT I C hmean hhigh hcorrector (homogeneousPrimary D Iprimary O)
    ((homogeneousPrimaryRegularity D Iprimary O hcorrector).changeTime hT.symm M.T_pos.le) p hp

end EulerPacketCylinderField

end
end

end

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
