/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import LeanPool.NavierStokesAndEuler.Euler.PacketParentLabelBudgets
public import LeanPool.NavierStokesAndEuler.Euler.PacketParentForwardBudget
public import LeanPool.NavierStokesAndEuler.Euler.PacketSourcePropagator
public import LeanPool.NavierStokesAndEuler.Euler.PacketParentTransverseCosts
public import LeanPool.NavierStokesAndEuler.Euler.TransversePacketBudget
public import LeanPool.NavierStokesAndEuler.Euler.PacketParentCoefficientBounds
public import LeanPool.NavierStokesAndEuler.Euler.TransversePacketHistoryData
public import LeanPool.NavierStokesAndEuler.Euler.PacketCofactorOperator

/-! Source-budget constructors using the literal parent fields in (21) and
the physical tangent growth estimate.  H3 for the constructed coordinate
propagator, the Hessian jets, and every inverse radius guard are conclusions.
The curvature/smallness hypotheses remain in the genuine source data. -/

section

/-! Construct the joined transverse budget from the parent deformation,
its two actual time derivatives, and the source weighted propagator.
Every radius guard is discharged by the fixed polynomial source envelopes;
the construction is independent of forcing amplitude and recursive grade. -/

section

/-! The Hessian multiplier bound follows from the actual second time
derivative of the deformation and the Jacobi equation.  Uniqueness of
within-interval derivatives includes both endpoints of the interval. -/

@[expose] public section

noncomputable section

namespace EulerTransversePacketProvider.HistoryData

open Set ContinuousLinearMap EulerSmoothLimit EulerMeanCoefficients
  EulerPacketPiola EulerPacketCofactor EulerVolterraConvolution EulerGevrey
open scoped ContDiff BoundedContinuousFunction

variable {U : Type*} [NormedAddCommGroup U] [InnerProductSpace ℝ U]
  {D : Data U} (B : HistoryData D)
  (F₂ : SmoothCoefficientPath (Icc (0 : ℝ) D.T) EndSpace)
  (h₂ : ∀ t ∈ Icc (0 : ℝ) D.T, ∀ x : Space,
    HasDerivWithinAt (fun s => extendPath D.T D.T_pos.le D.F₁.field s x)
      (extendPath D.T D.T_pos.le F₂.field t x) (Icc (0 : ℝ) D.T) t)

include h₂

theorem second_eq_jacobi (t : Icc (0 : ℝ) D.T) (x v : Space) :
    F₂.field t x v = -(B.H.field t x (D.F.field t x v)) := by
  have hu := uniqueDiffOn_Icc D.T_pos (t : ℝ) t.property
  have he := ((h₂ t t.property x).derivWithin hu).symm.trans
    ((B.jacobi t t.property x).derivWithin hu)
  have hval := congrArg (fun A : EndSpace => A v) he
  simpa only [extendPath,projIcc_of_mem D.T_pos.le t.property,
    neg_apply,ContinuousLinearMap.comp_apply] using hval

theorem curvature_bound_of_second (R C C₂ : ℝ)
    (hR : 0 ≤ R) (hC : 0 ≤ C) (hC₂ : 0 ≤ C₂)
    (hdet : ∀ t x, (operatorMatrix (D.F.field t x)).det = 1)
    (hF : ∀ n t x, ‖iteratedFDeriv ℝ n (D.F.field t : Space → EndSpace) x‖ ≤ C * majorant R 0 n)
    (hF₂ : ∀ n t x, ‖iteratedFDeriv ℝ n (F₂.field t : Space → EndSpace) x‖ ≤ C₂ * majorant R 0 n)
    (n : ℕ) (t : Icc (0 : ℝ) D.T) (x : Space) :
    ‖iteratedFDeriv ℝ n (B.H.field t : Space → EndSpace) x‖ ≤
      (27*C^2*C₂)*majorant R 0 n :=
  coefficientCurvature_bound D.F F₂ B.H hdet (B.second_eq_jacobi F₂ h₂)
    R C C₂ hR hC hC₂ hF hF₂ n t x

end EulerTransversePacketProvider.HistoryData

end
end

end

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

end
end

end

@[expose] public section

noncomputable section

namespace EulerPacketParentPhysicalBudgets

open Set ContinuousLinearMap EulerSmoothLimit EulerMeanCoefficients EulerLpTranslation
  EulerPacketCofactor EulerPacketPiola EulerPacketParentLabelBounds EulerPacketSourcePropagator
  EulerTransversePacketProvider EulerGevrey EulerVolterraConvolution EulerTimeIntervalRestriction
open scoped ContDiff BoundedContinuousFunction

variable {U : Type*} [NormedAddCommGroup U] [InnerProductSpace ℝ U] [CompleteSpace U]

/-- Half ball, given by `{x | ‖x‖ ≤ (1/2 : ℝ)}`. -/
def halfBall : Set Space := {x | ‖x‖ ≤ (1/2 : ℝ)}

/-- Physical cost, given by `3*(frameAmplitude K)^3*Cp`. -/
def physicalCost (K Cp : ℝ) : ℝ := 3*(frameAmplitude K)^3*Cp

theorem physicalCost_nonneg (K Cp : ℝ) (hCp : 0 ≤ Cp) : 0 ≤ physicalCost K Cp := by
  have h := frameAmplitude_nonneg K
  unfold physicalCost
  positivity

/-- At a zero-history stage the real label bounds and physical propagator
construct the complete source forward budget, before any forcing is chosen. -/
def forwardBudget (D : Data U) (q : ℕ)
    (A V : Icc (0 : ℝ) D.T → SmoothL2Field Space)
    (ℓ K Cp : ℝ) (hℓ : 0 ≤ ℓ) (hℓ1 : ℓ ≤ 1) (hK : 0 ≤ K) (hCp : 0 ≤ Cp)
    (hA : ∀ t, HasLabelBound K (A t)) (hV : ∀ t, HasLabelBound K (V t))
    (hF : ∀ t x, D.F.field t x = ContinuousLinearMap.id ℝ Space + fderiv ℝ (A t).field (ℓ • x))
    (hF₁ : ∀ t x, D.F₁.field t x = fderiv ℝ (V t).field (ℓ • x))
    (hdet : ∀ t x, (operatorMatrix (D.F.field t x)).det = 1)
    (g : C(Icc (0 : ℝ) D.T, ℝ)) (hg : ∀ t, 0 < g t)
    (hg0 : g ⟨0, le_rfl, D.T_pos.le⟩ = 1)
    (Ω : Set Space) (hΩ : MeasurableSet Ω) (hΩo : IsOpen Ω)
    (hsub : D.support ⊆ Ω) (hΩball : ∀ x ∈ Ω, ‖x‖ ≤ (1 / 2 : ℝ))
    (hphysical : PhysicalGrowth D halfBall g Cp) : EulerTransversePacketForward.Budget D (Fin 4) q
        := by
  have hbF := coefficient_deformation_bound D.F A (ℓ • ContinuousLinearMap.id ℝ Space)
    (labelScaling_norm_le ℓ hℓ hℓ1) hF K hK hA
  have hbF₁ := coefficient_gradient_bound D.F₁ V (ℓ • ContinuousLinearMap.id ℝ Space)
    (labelScaling_norm_le ℓ hℓ hℓ1) hF₁ K hK hV
  have hz : ∀ t x, ‖D.F.field t x‖ ≤ frameAmplitude K := by
    intro t x
    simpa only [norm_iteratedFDeriv_zero,majorant,Nat.zero_add,Nat.factorial_zero,
      Nat.cast_one,pow_zero,mul_one,one_pow] using hbF 0 t x
  apply EulerPacketParentForwardBudget.sourceForwardBudget D q (coefficientRadius K)
    (frameAmplitude K) (gradientAmplitude K) (physicalCost K Cp)
    (coefficientRadius_nonneg K) (frameAmplitude_nonneg K) (gradientAmplitude_nonneg K)
    (physicalCost_nonneg K Cp hCp) hdet hbF hbF₁ g hg hg0 Ω hΩ hΩo hsub hΩball
  intro t s hst x hx
  exact propagator_bound_of_deformation D halfBall g hg Cp (frameAmplitude K)
    hCp (frameAmplitude_nonneg K) hphysical (fun r y _ => hdet r y)
    (fun r y _ => hz r y) t s hst x hx

/-- Positive history uses the actual acceleration in (21) and its true
within-time derivative identity.  Jacobi and determinant one then supply
the Hessian multiplier bound needed by the joined variational inverse. -/
def joinedBudget (D : Data U) (τ : ℝ) (hτ : 0 < τ) (hτT : τ < D.T)
    (B : HistoryData (D.initial τ hτ hτT.le)) (q : ℕ)
    (A V : Icc (0 : ℝ) D.T → SmoothL2Field Space)
    (W : Icc (0 : ℝ) τ → SmoothL2Field Space)
    (F₂ : SmoothCoefficientPath (Icc (0 : ℝ) τ) EndSpace)
    (ℓ K Ti Cp : ℝ) (hℓ : 0 ≤ ℓ) (hℓ1 : ℓ ≤ 1) (hK : 0 ≤ K)
    (hτ1 : τ ≤ 1) (hTi : τ⁻¹ ≤ Ti) (hCp : 0 ≤ Cp)
    (hA : ∀ t, HasLabelBound K (A t)) (hV : ∀ t, HasLabelBound K (V t))
    (hW : ∀ t, HasLabelBound K (W t))
    (hF : ∀ t x, D.F.field t x = ContinuousLinearMap.id ℝ Space + fderiv ℝ (A t).field (ℓ • x))
    (hF₁ : ∀ t x, D.F₁.field t x = fderiv ℝ (V t).field (ℓ • x))
    (hF₂ : ∀ t x, F₂.field t x = fderiv ℝ (W t).field (ℓ • x))
    (h₂ : ∀ t ∈ Icc (0 : ℝ) τ, ∀ x : Space,
      HasDerivWithinAt (fun s => extendPath τ hτ.le (D.initial τ hτ hτT.le).F₁.field s x)
        (extendPath τ hτ.le F₂.field t x) (Icc (0 : ℝ) τ) t)
    (hdet : ∀ t x, (operatorMatrix (D.F.field t x)).det = 1)
    (g : C(Icc (0 : ℝ) (D.T-τ),ℝ)) (hg : ∀ t, 0 < g t)
    (hg0 : g ⟨0,le_rfl,(sub_pos.mpr hτT).le⟩ = 1)
    (Ω : Set Space) (hΩ : MeasurableSet Ω) (hΩo : IsOpen Ω)
    (hsub : D.support ⊆ Ω) (hΩball : ∀ x ∈ Ω, ‖x‖ ≤ (1/2 : ℝ))
    (hphysical : PhysicalGrowth (D.tail τ hτ.le hτT) halfBall g Cp) :
    EulerTransversePacketJoin.Budget D τ hτ hτT B (Fin 4) q := by
  have hbF := coefficient_deformation_bound D.F A (ℓ • ContinuousLinearMap.id ℝ Space)
    (labelScaling_norm_le ℓ hℓ hℓ1) hF K hK hA
  have hbF₁ := coefficient_gradient_bound D.F₁ V (ℓ • ContinuousLinearMap.id ℝ Space)
    (labelScaling_norm_le ℓ hℓ hℓ1) hF₁ K hK hV
  have hbF₂ := coefficient_gradient_bound F₂ W (ℓ • ContinuousLinearMap.id ℝ Space)
    (labelScaling_norm_le ℓ hℓ hℓ1) hF₂ K hK hW
  have hz : ∀ t x, ‖D.F.field t x‖ ≤ frameAmplitude K := by
    intro t x
    simpa only [norm_iteratedFDeriv_zero,majorant,Nat.zero_add,Nat.factorial_zero,
      Nat.cast_one,pow_zero,mul_one,one_pow] using hbF 0 t x
  apply EulerPacketParentJoinedBudget.sourceJoinedBudget D τ hτ hτT B q Ti (coefficientRadius K)
    (frameAmplitude K) (gradientAmplitude K) (gradientAmplitude K) (physicalCost K Cp)
    hτ1 hTi (coefficientRadius_nonneg K) (frameAmplitude_nonneg K) (gradientAmplitude_nonneg K)
    (gradientAmplitude_nonneg K) (physicalCost_nonneg K Cp hCp) hdet hbF hbF₁ F₂ h₂ hbF₂
    g hg hg0 Ω hΩ hΩo hsub hΩball
  intro t s hst x hx
  exact propagator_bound_of_deformation (D.tail τ hτ.le hτT) halfBall g hg Cp (frameAmplitude K)
    hCp (frameAmplitude_nonneg K) hphysical
    (fun r y _ => hdet (tailInclusion D.T τ hτ.le r) y)
    (fun r y _ => hz (tailInclusion D.T τ hτ.le r) y) t s hst x hx

end EulerPacketParentPhysicalBudgets
