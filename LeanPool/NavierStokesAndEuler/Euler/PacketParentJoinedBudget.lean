/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.PacketParentTransverseCosts
public import LeanPool.NavierStokesAndEuler.Euler.TransversePacketBudget
public import LeanPool.NavierStokesAndEuler.Euler.PacketParentCoefficientBounds
public import LeanPool.NavierStokesAndEuler.Euler.PacketParentJacobiCoefficient

/-! Construct the joined transverse budget from the parent deformation,
its two actual time derivatives, and the source weighted propagator.
Every radius guard is discharged by the fixed polynomial source envelopes;
the construction is independent of forcing amplitude and recursive grade. -/

@[expose] public section


noncomputable section

namespace EulerPacketParentJoinedBudget

open Set ContinuousLinearMap EulerSmoothLimit EulerMeanCoefficients
  EulerTransversePacketProvider EulerTransversePacketJoin EulerPacketPiola EulerPacketCofactor
  EulerPacketParentTransverseCosts EulerPacketParentMeanCoercivity EulerGevrey
  EulerParameterWordGevrey EulerFixedEvolutionSobolev EulerTransverseFixedSobolev
  EulerTimeLpGramSobolev  EulerTimeLpGramGevrey
  EulerSourceForwardCoefficient EulerLinearFundamentalExistence EulerVolterraConvolution
  EulerTimeIntervalRestriction
open scoped ContDiff BoundedContinuousFunction

variable {U : Type*} [NormedAddCommGroup U] [InnerProductSpace ℝ U] [CompleteSpace U]

/-- Cache the standard `NormedRing (U →L[ℝ] U)` instance to shorten typeclass synthesis. -/
local instance instPacketParentJoinedBudget1 : NormedRing (U →L[ℝ] U) := inferInstance
/-- Cache the standard `NormedRing (Space →ᵇ U →L[ℝ] U)` instance to shorten typeclass
synthesis. -/
local instance instPacketParentJoinedBudget2 : NormedRing (Space →ᵇ U →L[ℝ] U) := inferInstance

/-- Source joined budget as an element of `Budget D τ hτ hτT B (Fin 4) q`. -/
def sourceJoinedBudget (D : Data U) (τ : ℝ) (hτ : 0 < τ) (hτT : τ < D.T)
    (B : HistoryData (D.initial τ hτ hτT.le)) (q : ℕ)
    (Ti R C C₁ C₂ Cp : ℝ) (hτ1 : τ ≤ 1) (hTi : τ⁻¹ ≤ Ti)
    (hR : 0 ≤ R) (hC : 0 ≤ C) (hC₁ : 0 ≤ C₁) (hC₂ : 0 ≤ C₂) (hCp : 0 ≤ Cp)
    (hdet : ∀ t x, (operatorMatrix (D.F.field t x)).det = 1)
    (hF : ∀ n t x, ‖iteratedFDeriv ℝ n (D.F.field t : Space → EndSpace) x‖ ≤ C * majorant R 0 n)
    (hF₁ : ∀ n t x, ‖iteratedFDeriv ℝ n (D.F₁.field t : Space → EndSpace) x‖ ≤ C₁ * majorant R 0 n)
    (F₂ : SmoothCoefficientPath (Icc (0 : ℝ) τ) EndSpace)
    (h₂ : ∀ t ∈ Icc (0 : ℝ) τ, ∀ x : Space,
      HasDerivWithinAt (fun s => extendPath τ hτ.le (D.initial τ hτ hτT.le).F₁.field s x)
        (extendPath τ hτ.le F₂.field t x) (Icc (0 : ℝ) τ) t)
    (hF₂ : ∀ n t x, ‖iteratedFDeriv ℝ n (F₂.field t : Space → EndSpace) x‖ ≤ C₂*majorant R 0 n)
    (g : C(Icc (0 : ℝ) (D.T-τ),ℝ)) (hg : ∀ t, 0 < g t)
    (hg0 : g ⟨0,le_rfl,(sub_pos.mpr hτT).le⟩ = 1)
    (Ω : Set Space) (hΩ : MeasurableSet Ω) (hΩo : IsOpen Ω)
    (hsub : D.support ⊆ Ω) (hΩball : ∀ x ∈ Ω, ‖x‖ ≤ (1/2 : ℝ))
    (hprop : ∀ t s : Icc (0 : ℝ) (D.T-τ), s ≤ t → ∀ x : Space, ‖x‖ ≤ (1/2 : ℝ) →
      ‖((fundamentalPath (D.T-τ) (sub_pos.mpr hτT).le
          (sourceGenerator (D.tail τ hτ.le hτT).frame (D.tail τ hτ.le hτT).frameDerivative
            (D.tail τ hτ.le hτT).frameLower (D.tail τ hτ.le hτT).frameLower_pos
            (D.tail τ hτ.le hτT).frame_lower)).forward t x).comp
        ((fundamentalPath (D.T-τ) (sub_pos.mpr hτT).le
          (sourceGenerator (D.tail τ hτ.le hτT).frame (D.tail τ hτ.le hτT).frameDerivative
            (D.tail τ hτ.le hτT).frameLower (D.tail τ hτ.le hτT).frameLower_pos
            (D.tail τ hτ.le hτT).frame_lower)).backward s x)‖ ≤ Cp*g t/g s) :
    Budget D τ hτ hτT B (Fin 4) q := by
  have hTi0 : 0 ≤ Ti := (inv_nonneg.mpr hτ.le).trans hTi
  have hzero : ∀ t x, ‖D.F.field t x‖ ≤ C := by
    intro t x
    simpa only [norm_iteratedFDeriv_zero,majorant,Nat.zero_add,Nat.factorial_zero,
      Nat.cast_one,pow_zero,mul_one,one_pow] using hF 0 t x
  have hhdet : ∀ t x, (operatorMatrix ((D.initial τ hτ hτT.le).F.field t x)).det = 1 :=
    fun t x => hdet (initialInclusion D.T τ hτT.le t) x
  have hfdet : ∀ t x, (operatorMatrix ((D.tail τ hτ.le hτT).F.field t x)).det = 1 :=
    fun t x => hdet (tailInclusion D.T τ hτ.le t) x
  have hhF : ∀ n t x, ‖iteratedFDeriv ℝ n ((D.initial τ hτ hτT.le).F.field t : Space → EndSpace) x‖
      ≤
      C*majorant R 0 n := fun n t x => hF n (initialInclusion D.T τ hτT.le t) x
  have hhzero : ∀ t x, ‖(D.initial τ hτ hτT.le).F.field t x‖ ≤ C :=
    fun t x => hzero (initialInclusion D.T τ hτT.le t) x
  have hfzero : ∀ t x, ‖(D.tail τ hτ.le hτT).F.field t x‖ ≤ C :=
    fun t x => hzero (tailInclusion D.T τ hτ.le t) x
  have hih : (D.initial τ hτ hτT.le).frameLower⁻¹ ≤ gramInverseEnvelope C := by
    simpa only [gramInverseEnvelope,add_comm] using
      (D.initial τ hτ hτT.le).frameLower_inv_le_of_frame C hC hhdet hhzero
  have hif : (D.tail τ hτ.le hτT).frameLower⁻¹ ≤ gramInverseEnvelope C := by
    simpa only [gramInverseEnvelope,add_comm] using
      (D.tail τ hτ.le hτT).frameLower_inv_le_of_frame C hC hfdet hfzero
  have hw := historyCost_bound q τ R C C₁ C₂ (D.initial τ hτ hτT.le).frameLower
    hτ.le hτ1 hR hC hC₁ hC₂ (D.initial τ hτ hτT.le).frameLower_pos hih
  have hs := accelerationCost_bound q R C C₁ (D.initial τ hτ hτT.le).frameLower 1 1
    hR hC hC₁ (D.initial τ hτ hτT.le).frameLower_pos hih zero_le_one le_rfl
  have ht := traceCost_le τ Ti hτ hτ1 hTi
  have hu := accelerationCost_bound q R C C₁ (D.initial τ hτ hτT.le).frameLower (traceCost τ) (Ti+2)
    hR hC hC₁ (D.initial τ hτ hτT.le).frameLower_pos hih (traceCost_nonneg τ hτ.le) ht
  have hf := forwardCost_bound q (D.T-τ) Ti R C C₁ Cp (traceCost τ)
    (sub_pos.mpr hτT).le hR hC hC₁ hCp ht
  have hr := EulerPacketParentTransverseCosts.radius_guards q τ (D.T-τ) Ti R C C₁ C₂ Cp
    hτ.le (sub_pos.mpr hτT).le hTi0 hR hC hC₁ hC₂ hCp
  have hr0 : 0 ≤ sobolevCoefficientRadius (Fin 4) R+1 :=
    add_nonneg (sobolevCoefficientRadius_nonneg (ι := Fin 4) R hR) zero_le_one
  have hri : 0 ≤ sobolevCoefficientRadius (Fin 4) (4*inverseRadius R C)+1 :=
    add_nonneg (sobolevCoefficientRadius_nonneg (ι := Fin 4) _
      (mul_nonneg (by norm_num) (inverseRadius_nonneg R C hR))) zero_le_one
  refine {
    g := g
    positive := hg
    initial_one := hg0
    neighborhood := Ω
    neighborhood_measurable := hΩ
    neighborhood_open := hΩo
    support_subset := hsub
    neighborhood_halfball := hΩball
    Rc := R
    C₀ := C
    C₁ := C₁
    CH := curvatureAmplitude C C₂
    C := Cp
    Ri := inverseRadius R C
    R := radius q τ (D.T-τ) Ti R C C₁ C₂ Cp
    Rc_nonneg := hR
    C₀_nonneg := hC
    C₁_nonneg := hC₁
    CH_nonneg := by unfold curvatureAmplitude; positivity
    C_nonneg := hCp
    history_length := hτ1
    frame_bound := hF
    frameDerivative_bound := hF₁
    hessian_bound := B.curvature_bound_of_second F₂ h₂ R C C₂ hR hC hC₂ hhdet hhF hF₂
    history_weak := ?_
    history_strong := ?_
    history_uniform := ?_
    forward_inverse := inverseRadius_bound R C _ hR hif
    forcing_radius := hr.2.2.2.1
    forward_radius := ?_
    propagator := hprop }
  · exact (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hw (by norm_num)) hr0).trans hr.1
  · exact (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hs (by norm_num)) hr0).trans hr.2.1
  · exact (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hu (by
      norm_num)) hr0).trans hr.2.2.1
  · simpa only [mul_one] using
      (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hf (by norm_num)) hri).trans hr.2.2.2.2

end EulerPacketParentJoinedBudget
