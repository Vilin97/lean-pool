/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import LeanPool.NavierStokesAndEuler.Euler.TransversePacketIntervalForcing
public import LeanPool.NavierStokesAndEuler.Euler.FixedEvolutionSobolev
import LeanPool.NavierStokesAndEuler.Euler.CylinderDirichletTimeBounds
import LeanPool.NavierStokesAndEuler.Euler.MeanCoefficientPathJets
import LeanPool.NavierStokesAndEuler.Euler.ParameterSobolevLinear
public import LeanPool.NavierStokesAndEuler.Euler.CylinderDirichletData
import LeanPool.NavierStokesAndEuler.Euler.CylinderDirichletRegularity
import LeanPool.NavierStokesAndEuler.Euler.LpCylinderRectangularRegularity
import LeanPool.NavierStokesAndEuler.Euler.PacketMajorantShift

/-!
# Source bounds for the actual transverse history and its terminal trace

The only quantitative inputs are the literal source coefficient jets and
the forcing's fixed-Sobolev mixed-word bounds. The output is the constructed
history path and its actual terminal coordinate, at the identical radius.
-/

section

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

end
end

end

@[expose] public section

noncomputable section

namespace EulerTransversePacketProvider.Data

open Set ContinuousLinearMap EulerSmoothLimit EulerMeanCoefficients
  EulerTransverseBoundedFrame EulerGevrey
open scoped ContDiff BoundedContinuousFunction

variable {U : Type*} [NormedAddCommGroup U] [InnerProductSpace ℝ U] (D : Data U)

theorem frame_spatial_bound (n : ℕ) (C : ℝ)
    (hb : ∀ t x, ‖iteratedFDeriv ℝ n (D.F.field t : Space → Space →L[ℝ] Space) x‖ ≤ C)
    (t : Icc (0 : ℝ) D.T) (x : Space) :
    ‖iteratedFDeriv ℝ n (D.frame.field t : Space → U →L[ℝ] Space) x‖ ≤ C :=
  coefficient_derivative_bound D.m₀ D.R D.F n C hb t x

theorem frameDerivative_spatial_bound (n : ℕ) (C : ℝ)
    (hb : ∀ t x, ‖iteratedFDeriv ℝ n (D.F₁.field t : Space → Space →L[ℝ] Space) x‖ ≤ C)
    (t : Icc (0 : ℝ) D.T) (x : Space) :
    ‖iteratedFDeriv ℝ n (D.frameDerivative.field t : Space → U →L[ℝ] Space) x‖ ≤ C :=
  coefficient_derivative_bound D.m₀ D.R D.F₁ n C hb t x

end EulerTransversePacketProvider.Data

namespace EulerLpCylinderTranslation

open Set ContinuousLinearMap EulerSmoothLimit EulerLiftedGradientSpace EulerParameterWordGevrey
open scoped ContDiff

theorem trace_block_le (P : ℝ) [Fact (0 < P)]
    {K V ι : Type*} [TopologicalSpace K] [CompactSpace K]
    [NormedAddCommGroup V] [NormedSpace ℝ V] [Fintype ι]
    (directions : ι → LiftTangent) (q : ℕ) (p : C(K, CylinderL2 P V))
    (hp : ContDiff ℝ ∞ (fun a => pathTranslate P a p)) (t : K) (n : ℕ) (a : LiftTangent) :
    block directions q (fun b => translate P b (p t)) n a ≤
      block directions q (fun b => pathTranslate P b p) n a := by
  let L : C(K,CylinderL2 P V) →L[ℝ] CylinderL2 P V := ContinuousMap.evalCLM ℝ t
  have hL : ‖L‖ ≤ 1 := by
    apply opNorm_le_bound _ zero_le_one
    intro f
    change ‖f t‖ ≤ 1*‖f‖
    simpa only [one_mul] using f.norm_coe_le_norm t
  exact (block_comp_clm_le directions q L _ hp n a).trans
    ((mul_le_mul_of_nonneg_right hL (block_nonneg directions q _ n a)).trans_eq (one_mul _))

end EulerLpCylinderTranslation

namespace EulerTransversePacketProvider.HistoryData

open Set ContinuousLinearMap EulerSmoothLimit EulerMeanCoefficients
  EulerLiftedGradientSpace EulerLpCylinderTranslation EulerLpCylinderPaths
  EulerPacketProfileRecursion EulerGevrey EulerParameterWordGevrey
  EulerTransverseFixedSobolev EulerFixedEvolutionSobolev
  EulerTimeLpGramSobolev
open scoped ContDiff BoundedContinuousFunction

variable {P : ℝ} [Fact (0 < P)]
  {U : Type*} [NormedAddCommGroup U] [InnerProductSpace ℝ U] [CompleteSpace U]
  {D : Data U} (B : HistoryData D) {raw : VectorField} (G : Forcing P D raw)
  {ι : Type*} [Fintype ι] (directions : ι → LiftTangent) (hdir : ∀ i, ‖directions i‖ ≤ 1) (q : ℕ)
  (Rc C₀ C₁ CH Cf R : ℝ) (hRc : 0 ≤ Rc) (hC₀ : 0 ≤ C₀)
  (hC₁ : 0 ≤ C₁) (hCH : 0 ≤ CH) (hCf : 0 ≤ Cf)
  (hbF : ∀ n t x, ‖iteratedFDeriv ℝ n (D.F.field t : Space → Space →L[ℝ] Space) x‖ ≤ C₀ * majorant
      Rc
      0 n)
  (hbF₁ : ∀ n t x, ‖iteratedFDeriv ℝ n (D.F₁.field t : Space → Space →L[ℝ] Space) x‖ ≤ C₁ * majorant
      Rc 0 n)
  (hbH : ∀ n t x, ‖iteratedFDeriv ℝ n (B.H.field t : Space → Space →L[ℝ] Space) x‖ ≤ CH * majorant
      Rc
      0 n)
  (hRweak : 2 * blockCost ι q D.T Rc C₀ C₁ CH D.frameLower Cf * (sobolevCoefficientRadius ι Rc + 1)
      ≤ R)
  (hRstrong : 2 * gramBlockCost ι q D.frameLower Rc C₀
    (accelerationBlockAmplitude ι q Rc C₀ C₁ Cf 1) *
 (sobolevCoefficientRadius ι Rc + 1) ≤ R)
  (hT1 : D.T ≤ 1) (d : ℕ)
  (hforce : ∀ n, block directions q (fun a => pathTranslate P a (forcingPath G)) n 0 ≤ Cf * majorant
      R d n)

include hdir hRc hC₀ hC₁ hCH hCf hbF hbF₁ hbH hRweak hRstrong hT1 hforce

/-- True continuous coordinate velocity of the actual zero-endpoint solve. -/
theorem source_coordinate_bound (n : ℕ) :
    block directions q (fun a => pathTranslate P a (B.coordinatePath G)) n 0 ≤
      traceCost D.T*majorant R (d+2) n := by
  exact B.coefficients.continuousVelocity_block_bound P directions hdir q
    D.frame.translation_contDiff D.frameDerivative.translation_contDiff B.H.translation_contDiff
    Rc C₀ C₁ CH Cf R hRc hC₀ hC₁ hCH hCf
    (fun j a => D.frame.norm_iteratedFDeriv_translation_le j _
      (mul_nonneg hC₀ (majorant_nonneg Rc hRc 0 j)) (D.frame_spatial_bound j _ (hbF j)) a)
    (fun j a => D.frameDerivative.norm_iteratedFDeriv_translation_le j _
      (mul_nonneg hC₁ (majorant_nonneg Rc hRc 0 j)) (D.frameDerivative_spatial_bound j _ (hbF₁ j))
          a)
    (fun j a => B.H.norm_iteratedFDeriv_translation_le j _
      (mul_nonneg hCH (majorant_nonneg Rc hRc 0 j)) (hbH j) a)
    hRweak hRstrong hT1 (forcingPath G) G.path_orbit d hforce n 0

/-- The actual terminal trace used by the forward solve has the same bound. -/
theorem source_terminal_bound (n : ℕ) :
    block directions q (fun a => translate P a ((B.terminalInitial G).value : CylinderL2 P U)) n 0 ≤
      traceCost D.T*majorant R (d+2) n :=
  (trace_block_le P directions q (B.coordinatePath G) (B.coordinatePath_orbit G)
    ⟨D.T,D.T_pos.le,le_rfl⟩ n 0).trans
      (B.source_coordinate_bound G directions hdir q Rc C₀ C₁ CH Cf R hRc hC₀ hC₁ hCH hCf
        hbF hbF₁ hbH hRweak hRstrong hT1 d hforce n)

/-- Literal history velocity, with the fixed reference-plane contraction already discharged. -/
theorem source_velocity_bound (n : ℕ) :
    block directions q (fun a => pathTranslate P a (B.velocityPath G)) n 0 ≤
      (3*sobolevCoefficientAmplitude ι q Rc C₀*traceCost D.T)*majorant R (d+2) n := by
  exact B.coefficients.physicalVelocity_block_bound P directions hdir q
    D.frame.translation_contDiff D.frameDerivative.translation_contDiff B.H.translation_contDiff
    Rc C₀ C₁ CH Cf R hRc hC₀ hC₁ hCH hCf
    (fun j a => D.frame.norm_iteratedFDeriv_translation_le j _
      (mul_nonneg hC₀ (majorant_nonneg Rc hRc 0 j)) (D.frame_spatial_bound j _ (hbF j)) a)
    (fun j a => D.frameDerivative.norm_iteratedFDeriv_translation_le j _
      (mul_nonneg hC₁ (majorant_nonneg Rc hRc 0 j)) (D.frameDerivative_spatial_bound j _ (hbF₁ j))
          a)
    (fun j a => B.H.norm_iteratedFDeriv_translation_le j _
      (mul_nonneg hCH (majorant_nonneg Rc hRc 0 j)) (hbH j) a)
    hRweak hRstrong hT1 (forcingPath G) G.path_orbit d hforce n

/-- The genuine history time derivative, at the identical spatial radius. -/
theorem source_derivative_bound
    (hRuniform : 2 * gramBlockCost ι q D.frameLower Rc C₀
      (accelerationBlockAmplitude ι q Rc C₀ C₁ Cf (traceCost D.T)) *
 (sobolevCoefficientRadius ι
          Rc + 1) ≤ R)
    (n : ℕ) :
    block directions q (fun a => pathTranslate P a (B.derivativePath G)) n 0 ≤
      (3*sobolevCoefficientAmplitude ι q Rc C₁*traceCost D.T +
        3*sobolevCoefficientAmplitude ι q Rc C₀)*majorant R (d+3) n := by
  exact B.coefficients.physicalDerivative_block_bound P directions hdir q
    D.frame.translation_contDiff D.frameDerivative.translation_contDiff B.H.translation_contDiff
    Rc C₀ C₁ CH Cf R hRc hC₀ hC₁ hCH hCf
    (fun j a => D.frame.norm_iteratedFDeriv_translation_le j _
      (mul_nonneg hC₀ (majorant_nonneg Rc hRc 0 j)) (D.frame_spatial_bound j _ (hbF j)) a)
    (fun j a => D.frameDerivative.norm_iteratedFDeriv_translation_le j _
      (mul_nonneg hC₁ (majorant_nonneg Rc hRc 0 j)) (D.frameDerivative_spatial_bound j _ (hbF₁ j))
          a)
    (fun j a => B.H.norm_iteratedFDeriv_translation_le j _
      (mul_nonneg hCH (majorant_nonneg Rc hRc 0 j)) (hbH j) a)
    hRweak hRstrong hT1 hRuniform (forcingPath G) G.path_orbit d hforce n

end EulerTransversePacketProvider.HistoryData
