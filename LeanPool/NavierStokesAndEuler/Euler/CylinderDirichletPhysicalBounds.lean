/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.FixedEvolutionSobolev
public import LeanPool.NavierStokesAndEuler.Euler.CylinderDirichletData
import LeanPool.NavierStokesAndEuler.Euler.CylinderDirichletRegularity
import LeanPool.NavierStokesAndEuler.Euler.CylinderDirichletTimeBounds
import LeanPool.NavierStokesAndEuler.Euler.LpCylinderRectangularRegularity
import LeanPool.NavierStokesAndEuler.Euler.PacketMajorantShift

/-!
# Actual physical history fields at the same external radius

The frame products below act on the constructed cylinder coordinate paths.
They retain the fixed spatial/angular Sobolev block and use the true
continuous time derivative, including both endpoints.
-/

@[expose] public section


noncomputable section

namespace EulerCylinderDirichlet.Coefficients

open Set MeasureTheory ContinuousLinearMap InnerProductSpace EulerSmoothLimit
  EulerLiftedGradientSpace EulerLpCylinderTranslation EulerLpCylinderRectangular
  EulerTimeLp EulerTimeLpBoundedMap EulerMeanCoefficients EulerTransverseFixedSobolev
  EulerParameterWordGevrey EulerGevrey EulerFixedEvolutionSobolev
  EulerTimeLpGramSobolev
open scoped BoundedContinuousFunction ContDiff

variable (P : ℝ) [Fact (0 < P)] {T : ℝ} {U E : Type*}
  [NormedAddCommGroup U] [InnerProductSpace ℝ U] [CompleteSpace U]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  (D : Coefficients T U E)

/-- Cache the standard `NormedAddCommGroup (CylinderL2 P U)` instance to shorten typeclass
synthesis. -/
local instance instCylinderDirichletPhysicalBounds1 : NormedAddCommGroup (CylinderL2 P U) :=
    inferInstance
/-- Cache the standard `NormedSpace ℝ (CylinderL2 P U)` instance to shorten typeclass synthesis. -/
local instance instCylinderDirichletPhysicalBounds2 : NormedSpace ℝ (CylinderL2 P U) :=
    inferInstance
/-- Cache the standard `NormedAddCommGroup (CylinderL2 P E)` instance to shorten typeclass
synthesis. -/
local instance instCylinderDirichletPhysicalBounds3 : NormedAddCommGroup (CylinderL2 P E) :=
    inferInstance
/-- Cache the standard `NormedSpace ℝ (CylinderL2 P E)` instance to shorten typeclass synthesis. -/
local instance instCylinderDirichletPhysicalBounds4 : NormedSpace ℝ (CylinderL2 P E) :=
    inferInstance
/-- Cache the standard `NormedAddCommGroup (CylinderL2 P U →L[ℝ] CylinderL2 P E)` instance to
shorten typeclass synthesis. -/
local instance instCylinderDirichletPhysicalBounds5 : NormedAddCommGroup (CylinderL2 P U →L[ℝ]
    CylinderL2 P E) := inferInstance
/-- Cache the standard `NormedSpace ℝ (CylinderL2 P U →L[ℝ] CylinderL2 P E)` instance to shorten
typeclass synthesis. -/
local instance instCylinderDirichletPhysicalBounds6 : NormedSpace ℝ (CylinderL2 P U →L[ℝ]
    CylinderL2 P E) := inferInstance
/-- Cache the standard `NormedAddCommGroup (CylinderL2 P E →L[ℝ] CylinderL2 P E)` instance to
shorten typeclass synthesis. -/
local instance instCylinderDirichletPhysicalBounds7 : NormedAddCommGroup (CylinderL2 P E →L[ℝ]
    CylinderL2 P E) := inferInstance
/-- Cache the standard `NormedSpace ℝ (CylinderL2 P E →L[ℝ] CylinderL2 P E)` instance to shorten
typeclass synthesis. -/
local instance instCylinderDirichletPhysicalBounds8 : NormedSpace ℝ (CylinderL2 P E →L[ℝ]
    CylinderL2 P E) := inferInstance
/-- Cache the standard `NormedAddCommGroup C(Icc (0 : ℝ) T,CylinderL2 P U →L[ℝ] CylinderL2 P E)`
instance to shorten typeclass synthesis. -/
local instance instCylinderDirichletPhysicalBounds9 : NormedAddCommGroup C(Icc (0 : ℝ) T,CylinderL2
    P U →L[ℝ] CylinderL2 P E) :=
    inferInstance
/-- Cache the standard `NormedSpace ℝ C(Icc (0 : ℝ) T,CylinderL2 P U →L[ℝ] CylinderL2 P E)`
instance to shorten typeclass synthesis. -/
local instance instCylinderDirichletPhysicalBounds10 : NormedSpace ℝ C(Icc (0 : ℝ) T,CylinderL2 P U
    →L[ℝ] CylinderL2 P E) :=
    inferInstance
/-- Cache the standard `NormedAddCommGroup C(Icc (0 : ℝ) T,CylinderL2 P E →L[ℝ] CylinderL2 P E)`
instance to shorten typeclass synthesis. -/
local instance instCylinderDirichletPhysicalBounds11 : NormedAddCommGroup C(Icc (0 : ℝ)
    T,CylinderL2 P E →L[ℝ] CylinderL2 P E) :=
    inferInstance
/-- Cache the standard `NormedSpace ℝ C(Icc (0 : ℝ) T,CylinderL2 P E →L[ℝ] CylinderL2 P E)`
instance to shorten typeclass synthesis. -/
local instance instCylinderDirichletPhysicalBounds12 : NormedSpace ℝ C(Icc (0 : ℝ) T,CylinderL2 P E
    →L[ℝ] CylinderL2 P E) :=
    inferInstance

variable {ι : Type*} [Fintype ι]
  (directions : ι → LiftTangent) (hdir : ∀ i, ‖directions i‖ ≤ 1) (q : ℕ)
  (hQ : ContDiff ℝ ∞ (translateCoefficientPath D.Q))
  (hQ₁ : ContDiff ℝ ∞ (translateCoefficientPath D.Q₁))
  (hH : ContDiff ℝ ∞ (translateCoefficientPath D.H))
  (Rc C₀ C₁ CH Cf R : ℝ) (hRc : 0 ≤ Rc)
  (hC₀ : 0 ≤ C₀) (hC₁ : 0 ≤ C₁) (hCH : 0 ≤ CH) (hCf : 0 ≤ Cf)
  (hbQ : ∀ n a, ‖iteratedFDeriv ℝ n (translateCoefficientPath D.Q) a‖ ≤ C₀ * majorant Rc 0 n)
  (hbQ₁ : ∀ n a, ‖iteratedFDeriv ℝ n (translateCoefficientPath D.Q₁) a‖ ≤ C₁ * majorant Rc 0 n)
  (hbH : ∀ n a, ‖iteratedFDeriv ℝ n (translateCoefficientPath D.H) a‖ ≤ CH * majorant Rc 0 n)
  (hRweak : 2 * blockCost ι q T Rc C₀ C₁ CH D.lower Cf * (sobolevCoefficientRadius ι Rc + 1) ≤ R)
  (hRstrong : 2 * gramBlockCost ι q D.lower Rc C₀
    (accelerationBlockAmplitude ι q Rc C₀ C₁ Cf 1) *
 (sobolevCoefficientRadius ι Rc + 1) ≤ R)


include hdir hQ hQ₁ hH hRc hC₀ hC₁ hCH hCf hbQ hbQ₁ hbH hRweak hRstrong

/-- The physical history velocity A=Q ξ_t, as a true cylinder path. -/
theorem physicalVelocity_block_bound (hT1 : T ≤ 1)
    (f : C(Icc (0 : ℝ) T, CylinderL2 P E))
    (hf : ContDiff ℝ ∞ (fun a => pathTranslate P a f))
    (d : ℕ) (hfb : ∀ n, block directions q (fun a => pathTranslate P a f) n 0 ≤ Cf * majorant R d n)
    (n : ℕ) :
    block directions q (fun a => pathTranslate P a (D.physicalVelocity P f)) n 0 ≤
      (3*sobolevCoefficientAmplitude ι q Rc C₀*traceCost T)*majorant R (d+2) n := by
  have hRcR := (weak_radius_bounds ι q T Rc C₀ C₁ CH D.lower Cf R
    D.time_pos.le hRc hC₀ hC₁ hCH hCf hRweak).2
  have hv := D.velocityPath_orbit_contDiff P hQ hQ₁ hH f hf
  have hb (k) := D.continuousVelocity_block_bound P directions hdir q hQ hQ₁ hH
    Rc C₀ C₁ CH Cf R hRc hC₀ hC₁ hCH hCf hbQ hbQ₁ hbH hRweak hRstrong hT1 f hf d hfb k 0
  have he : D.physicalVelocity P f =
      fullMultiplierMap P D.Q (D.velocityPath P (pathLp T D.time_pos.le f)) := by
    apply ContinuousMap.ext
    intro t
    rfl
  rw [he]
  exact product_orbit_block_bound P D.Q hQ directions hdir q
    (D.velocityPath P (pathLp T D.time_pos.le f)) hv Rc C₀ R (traceCost T)
    hRc hC₀ (traceCost_nonneg T D.time_pos.le) hRcR hbQ (d+2) hb n

/-- The actual derivative A_t=Q_t ξ_t+Q ξ_tt, with no loss of spatial radius. -/
theorem physicalDerivative_block_bound (hT1 : T ≤ 1)
    (hRuniform : 2 * gramBlockCost ι q D.lower Rc C₀
      (accelerationBlockAmplitude ι q Rc C₀ C₁ Cf (traceCost T)) *
 (sobolevCoefficientRadius ι Rc + 1)
          ≤ R)
    (f : C(Icc (0 : ℝ) T, CylinderL2 P E))
    (hf : ContDiff ℝ ∞ (fun a => pathTranslate P a f))
    (d : ℕ) (hfb : ∀ n, block directions q (fun a => pathTranslate P a f) n 0 ≤ Cf * majorant R d n)
    (n : ℕ) :
    block directions q (fun a => pathTranslate P a (D.physicalDerivative P f)) n 0 ≤
      (3*sobolevCoefficientAmplitude ι q Rc C₁*traceCost T +
        3*sobolevCoefficientAmplitude ι q Rc C₀)*majorant R (d+3) n := by
  obtain ⟨hR1,hRcR⟩ := weak_radius_bounds ι q T Rc C₀ C₁ CH D.lower Cf R
    D.time_pos.le hRc hC₀ hC₁ hCH hCf hRweak
  let v := D.velocityPath P (pathLp T D.time_pos.le f)
  let a := D.accelerationPath P f
  have hv : ContDiff ℝ ∞ (fun b => pathTranslate P b v) :=
    D.velocityPath_orbit_contDiff P hQ hQ₁ hH f hf
  have ha : ContDiff ℝ ∞ (fun b => pathTranslate P b a) :=
    D.accelerationPath_orbit_contDiff P hQ hQ₁ hH f hf
  have hbv (k) : block directions q (fun b => pathTranslate P b v) k 0 ≤
      traceCost T*majorant R (d+3) k := by
    have hb := D.continuousVelocity_block_bound P directions hdir q hQ hQ₁ hH
      Rc C₀ C₁ CH Cf R hRc hC₀ hC₁ hCH hCf hbQ hbQ₁ hbH hRweak hRstrong hT1 f hf d hfb k 0
    exact hb.trans (mul_le_mul_of_nonneg_left
      (majorant_mono_shift R hR1 (d+2) (d+3) k (by omega)) (traceCost_nonneg T D.time_pos.le))
  have hba (k) : block directions q (fun b => pathTranslate P b a) k 0 ≤
      1*majorant R (d+3) k := by
    simpa only [one_mul] using D.accelerationPath_block_bound P directions hdir q hQ hQ₁ hH
      Rc C₀ C₁ CH Cf R hRc hC₀ hC₁ hCH hCf hbQ hbQ₁ hbH hRweak hRstrong hT1 hRuniform f hf d hfb k 0
  have h₁ := product_orbit_block_bound P D.Q₁ hQ₁ directions hdir q v hv
    Rc C₁ R (traceCost T) hRc hC₁ (traceCost_nonneg T D.time_pos.le) hRcR hbQ₁ (d+3) hbv n
  have h₂ := product_orbit_block_bound P D.Q hQ directions hdir q a ha
    Rc C₀ R 1 hRc hC₀ zero_le_one hRcR hbQ (d+3) hba n
  have he : D.physicalDerivative P f = fullMultiplierMap P D.Q₁ v+fullMultiplierMap P D.Q a := by
    apply ContinuousMap.ext
    intro t
    rfl
  have he' : (fun b => pathTranslate P b (D.physicalDerivative P f)) =
      fun b => pathTranslate P b (fullMultiplierMap P D.Q₁ v) +
        pathTranslate P b (fullMultiplierMap P D.Q a) := by
    funext b
    rw [he,map_add]
  rw [he']
  exact (block_add_le directions q _ _ (product_orbit_contDiff P D.Q₁ hQ₁ v hv)
    (product_orbit_contDiff P D.Q hQ a ha) n 0).trans
      (by simpa only [mul_one,add_mul] using add_le_add h₁ h₂)

end EulerCylinderDirichlet.Coefficients
