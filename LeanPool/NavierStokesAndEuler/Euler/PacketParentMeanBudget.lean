/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.PacketParentMeanCoercivity
public import LeanPool.NavierStokesAndEuler.Euler.MeanPacketBudget
public import LeanPool.NavierStokesAndEuler.Euler.PacketParentCoefficientBounds
public import LeanPool.NavierStokesAndEuler.Euler.ParameterSobolevCostMonotone

/-! A genuine mean-solver budget from parent deformation jets.  All inverse
costs and the final radius are explicit finite polynomials in those jets,
the initial boundary size, and an upper bound for the inverse time length. -/

@[expose] public section


noncomputable section

namespace EulerPacketParentMeanBudget

open Set Real EulerSmoothLimit EulerMeanCoefficients EulerPacketPiola EulerPacketCofactor
  EulerGevrey EulerParameterWordGevrey EulerMeanBoundary EulerMeanFixedSobolevGevrey
  EulerMeanTranslatedGevrey EulerMeanSourceFixedInverse EulerMeanStrongContinuousGevrey
  EulerTimeLpGramSobolev EulerPacketParentMeanCoercivity

/-- Curvature amplitude, given by `27*C^2*C₂`. -/
def curvatureAmplitude (C C₂ : ℝ) : ℝ := 27*C^2*C₂

/-- Operator cost, given by `operatorBlockAmplitude (Fin 4) q T R C C₁ (curvatureAmplitude C C₂)
C₁ scaledBoundaryOperatorAmplitude L`. -/
def operatorCost (q : ℕ) (T R C C₁ C₂ L : ℝ) : ℝ :=
  operatorBlockAmplitude (Fin 4) q T R C C₁ (curvatureAmplitude C C₂) C₁
    scaledBoundaryOperatorAmplitude L

/-- Forcing cost, given by `forcingBlockAmplitude (Fin 4) q T R C C₁ 1`. -/
def forcingCost (q : ℕ) (T R C C₁ : ℝ) : ℝ :=
  forcingBlockAmplitude (Fin 4) q T R C C₁ 1

/-- Weak cost as an element of `ℝ`. -/
def weakCost (q : ℕ) (T R C C₁ C₂ L : ℝ) : ℝ :=
  1+sobolevInverseCost (inverseEnvelope C C₁) (operatorCost q T R C C₁ C₂ L) q *
    (operatorCost q T R C C₁ C₂ L+forcingCost q T R C C₁)

/-- Gram cost, given by `inverseBlockCost (Fin 4) q (gramInverseEnvelope C) R (3*C^2)
(accelerationBlockAmplitude (Fin 4) q R C C₁ 1 V)`. -/
def gramCost (q : ℕ) (R C C₁ V : ℝ) : ℝ :=
  inverseBlockCost (Fin 4) q (gramInverseEnvelope C) R (3*C^2)
    (accelerationBlockAmplitude (Fin 4) q R C C₁ 1 V)

/-- Radius, given by `1+2*(weakCost q T R C C₁ C₂ L+gramCost q R C C₁ 1+gramCost q R C C₁
(Ti+2)) * (sobolevCoefficientRadius (Fin 4) R+1)`. -/
def radius (q : ℕ) (T Ti R C C₁ C₂ L : ℝ) : ℝ :=
  1+2*(weakCost q T R C C₁ C₂ L+gramCost q R C C₁ 1+gramCost q R C C₁ (Ti+2)) *
    (sobolevCoefficientRadius (Fin 4) R+1)

theorem operatorCost_nonneg (q : ℕ) (T R C C₁ C₂ L : ℝ)
    (hT : 0 ≤ T) (hR : 0 ≤ R) (hC₁ : 0 ≤ C₁) (hC₂ : 0 ≤ C₂) :
    0 ≤ operatorCost q T R C C₁ C₂ L :=
  sobolevCoefficientAmplitude_nonneg q R _ hR
    (operatorAmplitude_nonneg T C C₁ (curvatureAmplitude C C₂) C₁
      scaledBoundaryOperatorAmplitude L hT (by unfold curvatureAmplitude; positivity)
      hC₁ scaledBoundaryOperatorAmplitude_nonneg)

theorem forcingCost_nonneg (q : ℕ) (T R C C₁ : ℝ)
    (hT : 0 ≤ T) (hR : 0 ≤ R) (hC : 0 ≤ C) (hC₁ : 0 ≤ C₁) :
    0 ≤ forcingCost q T R C C₁ := by
  have ha := sobolevCoefficientAmplitude_nonneg (ι := Fin 4) q R (T*(T*C₁+C)) hR (by positivity)
  unfold forcingCost forcingBlockAmplitude
  positivity

theorem weakCost_one_le (q : ℕ) (T R C C₁ C₂ L : ℝ)
    (hT : 0 ≤ T) (hR : 0 ≤ R) (hC : 0 ≤ C) (hC₁ : 0 ≤ C₁) (hC₂ : 0 ≤ C₂) :
    1 ≤ weakCost q T R C C₁ C₂ L := by
  have ho := operatorCost_nonneg q T R C C₁ C₂ L hT hR hC₁ hC₂
  have hf := forcingCost_nonneg q T R C C₁ hT hR hC hC₁
  have hi := sobolevInverseCost_nonneg (inverseEnvelope C C₁) _
    (inverseEnvelope_nonneg C C₁) ho q
  unfold weakCost
  exact le_add_of_nonneg_right (mul_nonneg hi (add_nonneg ho hf))

theorem gramCost_nonneg (q : ℕ) (R C C₁ V : ℝ)
    (hR : 0 ≤ R) (hC : 0 ≤ C) (hC₁ : 0 ≤ C₁) (hV : 0 ≤ V) :
    0 ≤ gramCost q R C C₁ V := by
  have hi : 0 ≤ gramInverseEnvelope C := by unfold gramInverseEnvelope; positivity
  have hb := sobolevCoefficientAmplitude_nonneg (ι := Fin 4) q R (3*C^2) hR (by positivity)
  have hs := sobolevInverseCost_nonneg (gramInverseEnvelope C) _ hi hb q
  have hd := accelerationBlockAmplitude_nonneg (ι := Fin 4) q R C C₁ 1 V hR hC hC₁ zero_le_one hV
  unfold gramCost inverseBlockCost
  positivity

theorem radius_guards (q : ℕ) (T Ti R C C₁ C₂ L : ℝ)
    (hT : 0 ≤ T) (hTi : 0 ≤ Ti) (hR : 0 ≤ R) (hC : 0 ≤ C) (hC₁ : 0 ≤ C₁) (hC₂ : 0 ≤ C₂) :
    2*weakCost q T R C C₁ C₂ L*(sobolevCoefficientRadius (Fin 4) R+1) ≤ radius q T Ti R C C₁ C₂ L ∧
    2*gramCost q R C C₁ 1*(sobolevCoefficientRadius (Fin 4) R+1) ≤ radius q T Ti R C C₁ C₂ L ∧
    2*gramCost q R C C₁ (Ti+2)*(sobolevCoefficientRadius (Fin 4) R+1) ≤ radius q T Ti R C C₁ C₂ L
        := by
  have hw := zero_le_one.trans (weakCost_one_le q T R C C₁ C₂ L hT hR hC hC₁ hC₂)
  have hg := gramCost_nonneg q R C C₁ 1 hR hC hC₁ zero_le_one
  have hgc := gramCost_nonneg q R C C₁ (Ti+2) hR hC hC₁ (by positivity)
  have hr := add_nonneg (sobolevCoefficientRadius_nonneg (ι := Fin 4) R hR) zero_le_one
  have hw' := mul_nonneg hw hr
  have hg' := mul_nonneg hg hr
  have hgc' := mul_nonneg hgc hr
  unfold radius
  constructor
  · linarith
  constructor <;> linarith

variable (D : EulerMeanPacketProvider.Data) (q : ℕ) (Ti R C C₁ C₂ : ℝ)
  (hT : D.T ≤ 1) (hTi : D.T⁻¹ ≤ Ti) (hR : 1024 ≤ R)
  (hC : 0 ≤ C) (hC₁ : 0 ≤ C₁) (hC₂ : 0 ≤ C₂)
  (hdet : ∀ t x, (operatorMatrix (D.F.field t x)).det = 1)
  (hF : ∀ n t x, ‖iteratedFDeriv ℝ n (D.F.field t : Space → EndSpace) x‖ ≤ C * majorant R 0 n)
  (hF₁ : ∀ n t x, ‖iteratedFDeriv ℝ n (D.F₁.field t : Space → EndSpace) x‖ ≤ C₁ * majorant R 0 n)
  (hF₂ : ∀ n t x, ‖iteratedFDeriv ℝ n (D.F₂.field t : Space → EndSpace) x‖ ≤ C₂ * majorant R 0 n)

/-- Source mean budget as an element of `EulerMeanPacketProvider.Budget D q (radius q D.T Ti R C
C₁ C₂ D.L)`. -/
def sourceMeanBudget : EulerMeanPacketProvider.Budget D q (radius q D.T Ti R C C₁ C₂ D.L) := by
  have hR0 : 0 ≤ R := (by norm_num : (0 : ℝ) ≤ 1024).trans hR
  have hTi0 : 0 ≤ Ti := (inv_nonneg.mpr D.T_pos.le).trans hTi
  have hzero : ∀ t x, ‖D.F.field t x‖ ≤ C := by
    intro t x
    simpa only [norm_iteratedFDeriv_zero,majorant,Nat.zero_add,Nat.factorial_zero,
      Nat.cast_one,pow_zero,mul_one,one_pow] using hF 0 t x
  have hone : ∀ t x, ‖D.F₁.field t x‖ ≤ C₁ := by
    intro t x
    simpa only [norm_iteratedFDeriv_zero,majorant,Nat.zero_add,Nat.factorial_zero,
      Nat.cast_one,pow_zero,mul_one,one_pow] using hF₁ 0 t x
  have hInv := sourceInverse_bound D C C₁ hC hC₁ hdet hzero hone hT
  have hGram := gramInverse_bound D C hC hdet hzero
  have hi0 : 0 ≤ (sourceFixedCoercivity D.T D.F D.F₁ D.opInv)⁻¹ :=
    inv_nonneg.mpr (sourceFixedCoercivity_pos D.T D.T_pos.le D.F D.F₁ D.opInv).le
  have ho := operatorCost_nonneg q D.T R C C₁ C₂ D.L D.T_pos.le hR0 hC₁ hC₂
  have hf := forcingCost_nonneg q D.T R C C₁ D.T_pos.le hR0 hC hC₁
  have hs0 := sobolevInverseCost_nonneg (inverseEnvelope C C₁) _ (inverseEnvelope_nonneg C C₁) ho q
  have hs := sobolevInverseCost_mono hi0 ho hInv le_rfl q
  have hop : sobolevInverseCost (sourceFixedCoercivity D.T D.F D.F₁ D.opInv)⁻¹
      (operatorCost q D.T R C C₁ C₂ D.L) q*operatorCost q D.T R C C₁ C₂ D.L ≤
      weakCost q D.T R C C₁ C₂ D.L := by
    apply (mul_le_mul_of_nonneg_right hs ho).trans
    unfold weakCost
    linarith [mul_nonneg hs0 hf]
  have hfp : sobolevInverseCost (sourceFixedCoercivity D.T D.F D.F₁ D.opInv)⁻¹
      (operatorCost q D.T R C C₁ C₂ D.L) q*forcingCost q D.T R C C₁ ≤
      weakCost q D.T R C C₁ C₂ D.L := by
    apply (mul_le_mul_of_nonneg_right hs hf).trans
    unfold weakCost
    linarith [mul_nonneg hs0 ho]
  have hsqrt : sqrt D.T ≤ 1 := by nlinarith [sqrt_nonneg D.T, sq_sqrt D.T_pos.le]
  have htrace : coordinateTraceCost D.T ≤ Ti+2 := by
    unfold coordinateTraceCost
    have hmul := mul_le_mul hTi hsqrt (sqrt_nonneg D.T) hTi0
    linarith
  have ht0 := coordinateTraceCost_nonneg D.T D.T_pos.le
  have hg0 : 0 ≤ D.frameLower⁻¹ := inv_nonneg.mpr D.frameLower_pos.le
  have hd0 := accelerationBlockAmplitude_nonneg (ι := Fin 4) q R C C₁ 1 1 hR0 hC hC₁ zero_le_one
      zero_le_one
  have hdt := accelerationBlockAmplitude_nonneg (ι := Fin 4) q R C C₁ 1 (coordinateTraceCost D.T)
    hR0 hC hC₁ zero_le_one ht0
  have hacc : accelerationBlockAmplitude (Fin 4) q R C C₁ 1 (coordinateTraceCost D.T) ≤
      accelerationBlockAmplitude (Fin 4) q R C C₁ 1 (Ti+2) := by
    have ha := sobolevCoefficientAmplitude_nonneg (ι := Fin 4) q R C hR0 hC
    have hb := sobolevCoefficientAmplitude_nonneg (ι := Fin 4) q R C₁ hR0 hC₁
    unfold accelerationBlockAmplitude
    gcongr
  have hg := inverseBlockCost_mono (ι := Fin 4) q hg0 hR0 (by
      positivity : 0 ≤ 3*C^2) hd0 hGram le_rfl le_rfl
  have hgc := inverseBlockCost_mono (ι := Fin 4) q hg0 hR0 (by
      positivity : 0 ≤ 3*C^2) hdt hGram le_rfl hacc
  have hr := radius_guards q D.T Ti R C C₁ C₂ D.L D.T_pos.le hTi0 hR0 hC hC₁ hC₂
  have hr0 := add_nonneg (sobolevCoefficientRadius_nonneg (ι := Fin 4) R hR0) zero_le_one
  refine {
    Rc := R
    M := weakCost q D.T R C C₁ C₂ D.L
    CF := C
    CF₁ := C₁
    CH := curvatureAmplitude C C₂
    CM := C₁
    Cf := 1
    radius_lower := hR
    inverse_cost_lower := weakCost_one_le q D.T R C C₁ C₂ D.L D.T_pos.le hR0 hC hC₁ hC₂
    CF_nonneg := hC
    CF₁_nonneg := hC₁
    CH_nonneg := by unfold curvatureAmplitude; positivity
    CM_nonneg := hC₁
    Cf_nonneg := zero_le_one
    operator_budget := hop
    forcing_budget := hfp
    radius_budget := hr.1
    acceleration_budget := ?_
    continuous_acceleration_budget := ?_
    frame_bound := hF
    frame_derivative_bound := hF₁
    curvature_bound := coefficientCurvature_bound D.F D.F₂ D.H hdet D.second_equation
      R C C₂ hR0 hC hC₂ hF hF₂
    initial_strain_bound := ?_
    forcing_one := le_rfl
    forcing_time := hsqrt }
  · exact (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hg (by
      norm_num : (0 : ℝ) ≤ 2)) hr0).trans hr.2.1
  · exact (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hgc (by
      norm_num : (0 : ℝ) ≤ 2)) hr0).trans hr.2.2
  · intro n x
    have he : (D.M0.field : Space → EndSpace) = D.F₁.field ⟨0,le_rfl,D.T_pos.le⟩ :=
      funext (fun y => (D.derivative_initial y).symm)
    rw [he]
    exact hF₁ n ⟨0,le_rfl,D.T_pos.le⟩ x

end EulerPacketParentMeanBudget
