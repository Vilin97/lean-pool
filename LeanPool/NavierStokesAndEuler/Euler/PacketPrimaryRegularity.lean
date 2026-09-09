/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.PacketProfileRegularity
public import LeanPool.NavierStokesAndEuler.Euler.PacketRecursiveBase
public import LeanPool.NavierStokesAndEuler.Euler.TransversePacketPressureGradientProperties
public import LeanPool.NavierStokesAndEuler.Euler.TransversePacketCorrectorOperator

@[expose] public section

/-! The genuine homogeneous high-mode solution supplies the primary profile's regularity. -/

noncomputable section

namespace EulerPacketCylinderField

open Set MeasureTheory EulerSmoothLimit EulerPacketPointJets EulerPacketProfileRecursion

variable {P T : ℝ} [Fact (0 < P)]

def ProfileRegularity.changeTime {T' : ℝ} {hT : 0 ≤ T} {S : Set Space} {a : Profile}
    (G : ProfileRegularity P T hT S a) (h : T = T') (hT' : 0 ≤ T') :
    ProfileRegularity P T' hT' S a := by
  subst T'
  exact G

variable {U : Type*} [NormedAddCommGroup U] [InnerProductSpace ℝ U] [CompleteSpace U]
  {D : EulerTransversePacketProvider.Data U} {raw : VectorField}

def ProfileRegularity.primary (G : EulerTransversePacketProvider.Forcing P D raw)
    (I : EulerTransversePacketProvider.InitialData P D) (O : Operators)
    (hcorrector : O.curlCorrector = D.curlCorrector P) :
    ProfileRegularity P D.T D.T_pos.le D.support (primaryProfile O (G.vector I) (G.scalar I)) where
  high := G.vectorField I
  mean := Field.zero P D.T
  corrector := (G.curlCorrectorField I).congr (fun _ _ _ => by
    change O.curlCorrector (G.vector I) _ = D.curlCorrector P (G.vector I) _
    rw [hcorrector])
  pressure := G.scalarGradientField I
  high_t := G.vectorDerivative I
  mean_t := 0
  corrector_t := G.correctorDerivative I
  highDerivative := G.vectorDerivativeField I
  meanDerivative := Field.zero P D.T
  correctorDerivative := G.correctorDerivativeField I
  high_time := G.vectorField_time I
  mean_time := Field.zero_time D.T_pos.le
  corrector_time := G.curlCorrectorField_time I
  high_zero t x hx θ := G.vector_zero_outside I t x hx θ
  corrector_zero t x hx θ := by
    change O.curlCorrector (G.vector I) (t,(x,θ)) = 0
    rw [hcorrector,G.curlCorrector_eq I t x θ]
    exact G.corrector_zero_outside I t x hx θ
  pressure_zero t x hx θ := G.scalarGradient_zero_outside I t x hx θ
  mean_angle _ _ _ := rfl

/-- Zero forcing is an actual supported smooth cylinder path with zero angular integral. -/
def homogeneousForcing (D : EulerTransversePacketProvider.Data U) :
    EulerTransversePacketProvider.Forcing P D (0 : VectorField) :=
  (Field.zero P D.T).transverseForcingOfRaw D (fun _ _ _ _ => rfl) (fun _ _ => by simp)

def homogeneousPrimary (D : EulerTransversePacketProvider.Data U)
    (I : EulerTransversePacketProvider.InitialData P D) (O : Operators) : Profile :=
  primaryProfile O ((homogeneousForcing (P := P) D).vector I) ((homogeneousForcing (P := P)
    D).scalar I)

def homogeneousPrimaryRegularity (D : EulerTransversePacketProvider.Data U)
    (I : EulerTransversePacketProvider.InitialData P D) (O : Operators)
    (hcorrector : O.curlCorrector = D.curlCorrector P) :
    ProfileRegularity P D.T D.T_pos.le D.support (homogeneousPrimary D I O) :=
  ProfileRegularity.primary (homogeneousForcing D) I O hcorrector

end EulerPacketCylinderField
