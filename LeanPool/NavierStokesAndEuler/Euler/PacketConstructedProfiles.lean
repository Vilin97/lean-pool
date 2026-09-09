/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.PacketProfilesRegularity
public import LeanPool.NavierStokesAndEuler.Euler.PacketPrimaryRegularity

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
