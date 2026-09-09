/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.PacketCylinderMeanStep
public import LeanPool.NavierStokesAndEuler.Euler.PacketCylinderHighForcing
public import LeanPool.NavierStokesAndEuler.Euler.PacketCylinderHighSupport

/-! The literal recursive high forcing is admissible for the constructed transverse inverse. -/

@[expose] public section


noncomputable section

namespace EulerPacketCylinderField

open Set MeasureTheory EulerSmoothLimit EulerPacketPointJets EulerPacketProfileRecursion

variable {P T : ℝ} [Fact (0 < P)]

/-- Change time, given by `h ▸ G`. -/
def Field.changeTime {raw : VectorField} {T' : ℝ} (G : Field P T raw) (h : T = T') :
    Field P T' raw := h ▸ G

theorem Field.changeTime_derivative {raw raw_t : VectorField} {T' : ℝ}
    (G : Field P T raw) (H : Field P T raw_t) (h : T = T') (hT : 0 ≤ T) (hT' : 0 ≤ T')
    (hd : TimeDerivative hT G H) :
    TimeDerivative hT' (G.changeTime h) (H.changeTime h) := by
  subst T'
  exact hd

/-- Transverse forcing of raw time as an element of `EulerTransversePacketProvider.Forcing P D
raw`. -/
def Field.transverseForcingOfRawTime
    {U : Type*} [NormedAddCommGroup U] [InnerProductSpace ℝ U]
    (D : EulerTransversePacketProvider.Data U) {raw : VectorField} (G : Field P T raw)
    (hT : T = D.T)
    (hs : ∀ (t : Icc (0 : ℝ) T) x, x ∉ D.support → ∀ θ : ℝ, raw (t,(x,θ)) = 0)
    (hm : ∀ (t : Icc (0 : ℝ) T) x, (∫ θ in (0 : ℝ)..P, raw (t,(x,θ))) = 0) :
    EulerTransversePacketProvider.Forcing P D raw := by
  subst T
  exact G.transverseForcingOfRaw D hs hm

variable (M : EulerMeanPacketProvider.Data)
  {U : Type*} [NormedAddCommGroup U] [InnerProductSpace ℝ U] [CompleteSpace U]
  (D : EulerTransversePacketProvider.Data U) (hT : M.T = D.T)
  {O : Operators} {p : ℕ} {a : ℕ → Profile}

/-- Every hypothesis concerns already constructed prefix fields or the actual prescribed
coefficients. -/
def PrefixFields.highForcing (F : PrefixFields P M.T p a) (C : CoefficientData P M.T O)
    (hp : 2 ≤ p) {correctorT : VectorField} (Ct : Field P M.T correctorT)
    (hCt : TimeDerivative M.T_pos.le (F.corrector (p - 1) (Nat.sub_one_lt_of_lt hp)) Ct)
    (pressure : Field P M.T (pressureGradient (a (p - 1)).highPressure))
    (hmean : O.meanSolve = EulerMeanPacketProvider.meanSolve M)
    (L : PrefixLocality M.T p a D.support)
    (hpressure : ∀ (t : Icc (0 : ℝ) M.T) x, x ∉ D.support → ∀ θ : ℝ,
      pressureGradient (a (p-1)).highPressure (t,(x,θ)) = 0) :
    EulerTransversePacketProvider.Forcing P D (EulerPacketProfileRecursion.highForce O p a) :=
  (F.actualHighForce M C hp Ct hCt pressure hmean).transverseForcingOfRawTime D hT
    (F.highForce_zero_outside C hp M.T_pos Ct hCt D.support D.support_compact.isClosed L hpressure)
    (F.actualHighForce_mean_zero M C hp Ct hCt pressure hmean)

end EulerPacketCylinderField
