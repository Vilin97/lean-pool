/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import LeanPool.NavierStokesAndEuler.Euler.PacketCorrectionOutputPolynomial
public import LeanPool.NavierStokesAndEuler.Euler.PacketInitializedHessianError
public import LeanPool.NavierStokesAndEuler.Euler.PacketLiftedCoefficientBounds
public import LeanPool.NavierStokesAndEuler.Euler.PacketRadiusCostPolynomial
import LeanPool.NavierStokesAndEuler.Euler.PacketInitializedRadiusPolynomial
public import LeanPool.NavierStokesAndEuler.Euler.PacketExactShearError
import LeanPool.NavierStokesAndEuler.Euler.PacketCylinderBoundTransfer
import LeanPool.NavierStokesAndEuler.Euler.PacketFieldGraphBounds
import LeanPool.NavierStokesAndEuler.Euler.PacketPrimaryGlobalShear
import LeanPool.NavierStokesAndEuler.Euler.PacketProfileCoarseBounds

/-! Fixed polynomial envelopes for the physical remainder, correction
error and lifted-flow input costs. All spatial derivative orders here are
fixed (H6 and one physical derivative). -/

section

/-! The actual finite and exact packets have the source shear at every
physical point. The slow primary derivative and finite tail contribute
only a fixed source constant divided by the frequency. -/

@[expose] public section

noncomputable section

namespace EulerPacketTerminalDatum

open Set InnerProductSpace ContinuousLinearMap EulerSmoothLimit EulerSpatialCutoffs
  EulerTransversePacketProvider EulerPacketCylinderField EulerPacketProfileRecursion
  EulerPacketPointJets EulerPacketTimeProfile EulerParameterWordGevrey
  EulerPacketCoarseMajorant EulerCylinderSobolevSpace EulerCylinderCoordinates
  EulerPacketPrimaryShear EulerPacketPrimaryFactorization EulerTransversePacketPrimary
  EulerLiftedGradientSpace EulerGraphPressurePotential EulerAllOrderDriftCorrection
  EulerPeriodicProfile EulerGevrey
open scoped ContDiff

/-- Initialized global shear cost as an element of `ℝ`. -/
def initializedGlobalShearCost (R H0 C : ℝ) : ℝ :=
  ‖coordinateEquiv.symm.toContinuousLinearMap‖*
      (sobolevEmbeddingConstant period 3*fixedVelocityGradeCost R H0 1*(4*R))*C +
    |initializedRemainderDerivativeCost R H0| *C

variable (M : EulerMeanPacketProvider.Data)
  {U : Type*} [NormedAddCommGroup U] [InnerProductSpace ℝ U] [CompleteSpace U]
  (D : Data U) (hTime : M.T = D.T) (τ : ℝ) (hτ : 0 < τ) (hτT : τ < D.T)
  (B : HistoryData (D.initial τ hτ hτT.le))
  (δ : ℝ) (hδ : 0 < δ) (ξ : U) (hs : tsupport innerCutoff ⊆ D.support) (α : ℝ)
  (L : EulerTransversePacketJoin.Budget D τ hτ hτT B (Fin 4) 6)
  (H : EulerTransversePacketPrimary.Budget L)
  (NB : EulerTransversePacketJoin.NormalBudget D 6 L.R)
  (W : EulerTransversePacketJoin.Budget.GradeGuards (P := period) L NB)
  (LM : EulerMeanPacketProvider.Budget M 6 L.R)
  (WM : EulerMeanPacketProvider.Budget.GradeGuards LM)
  (BC : CoefficientBudget (joinedSourceCoefficientData period M D τ hτ hτT B hTime))
  (hRc : sobolevCoefficientRadius (Fin 4) BC.Rc ≤ L.R) (hcost : BC.termCost ≤ L.R)
  (hδ1 : δ ≤ 1) (hα : 0 < α) (hR : wordRadius (Fin 4) δ ≤ L.R)
  (WP : EulerTransversePacketPrimary.Budget.GradeGuards (P := period) H NB (wordCost (Fin 4) 6
      δ * ‖ξ‖))
  (S : Scales (Icc (0 : ℝ) M.T))
  (hgrowth : timeProfileChange S.growth hTime = α • L.fullProfile)

include H NB W LM WM BC hRc hcost hδ1 hα hR WP hgrowth

theorem initializedPrimary_global_bound :
    (vectorField τ hτ hτT B (initialData D δ hδ (α • ξ) hs)).WordBound
      6 (4*L.R) (fixedVelocityGradeCost L.R S.H0 1) 0 := by
  have hG := initialized_profile_budgets M D hTime τ hτ hτT B δ hδ ξ hs α
    L H NB W LM WM BC hRc hcost hδ1 hα hR WP S hgrowth 1 le_rfl
  have hb := hG.high.remove_profile M.T_pos.le (S.high 1) (S.high_pos 1)
    (S.H0^(2*1)) (pow_nonneg S.H0_pos.le _) (S.high_le_coarse 1 le_rfl)
  simp only [mul_one] at hb
  have ha : S.H0^2 ≤ 3*S.H0^(2*1) := by
    norm_num only [Nat.mul_one]
    nlinarith [sq_nonneg S.H0]
  have hc := (hb.mono_amplitude (zero_le_one.trans L.radius_bounds.1) ha).fixed_velocity_grade
    (n := 1) (zero_le_one.trans L.radius_bounds.1) S.H0_pos.le
  exact (hc.changeTime hTime).ofRawEq _
    (fun _ _ _ => by rw [initializedProfiles_one_high])

theorem initializedVelocity_global_gradient_error (N : ℕ) (hN : 1 ≤ N)
    (k : ℝ) (hk : 4 ≤ k) (hbase : tailBase L.R S.H0 BC.termCost N ≤ k ^ (1 / 100 : ℝ))
    (t : Icc (0 : ℝ) D.T) (Y : Space → Space) (x : Space)
    (hY : HasFDerivAt Y (D.FInv.field t (Y x)) x) :
    ‖fderiv ℝ (fun y => initializedVelocity M D τ hτ hτT B δ hδ ξ hs α N k⁻¹
      (t,(Y y,k*⟪D.m₀,Y y⟫_ℝ))) x -
      (α*deriv (profile δ) (k*⟪D.m₀,Y x⟫_ℝ)) •
        rankOne ℝ (canonicalVelocity τ hτ hτT B ξ hs t (Y x)) (D.normal.field t (Y x))‖ ≤
      initializedGlobalShearCost L.R S.H0 NB.C/k := by
  have hk0 : 0 < k := by linarith
  have hr0 : 0 ≤ L.R := zero_le_one.trans L.radius_bounds.1
  have hc0 := fixedVelocityGradeCost_nonneg L.R S.H0 hr0 1
  have hinv : ‖D.FInv.field t (Y x)‖ ≤ NB.C := by
    simpa [majorant] using NB.inverse_bound 0 t (Y x)
  have hprimary := scaled_terminal_global_gradient_bound τ hτ hτT B δ hδ ξ hs α k hk0
    (4*L.R) (fixedVelocityGradeCost L.R S.H0 1) NB.C (by positivity) hc0 NB.C_nonneg
    (initializedPrimary_global_bound M D hTime τ hτ hτT B δ hδ ξ hs α
      L H NB W LM WM BC hRc hcost hδ1 hα hR WP S hgrowth) t Y x hY hinv
  have htail := initializedPrimaryRemainder_physical_fderiv_inv M D hTime τ hτ hτT B δ hδ ξ hs α
    L H NB W LM WM BC hRc hcost hδ1 hα hR WP S hgrowth N hN k hk hbase t Y x hY.differentiableAt
  rw [hY.fderiv] at htail
  have htail' : ‖fderiv ℝ (fun y => initializedPrimaryRemainder M D τ hτ hτT B δ hδ ξ hs α N k⁻¹
      (t,(Y y,k*⟪D.m₀,Y y⟫_ℝ))) x‖ ≤ |initializedRemainderDerivativeCost L.R S.H0| *NB.C/k := by
    apply htail.trans
    calc
      _ ≤ (|initializedRemainderDerivativeCost L.R S.H0|/k)*‖D.FInv.field t (Y x)‖ :=
        mul_le_mul_of_nonneg_right (div_le_div_of_nonneg_right (le_abs_self _) hk0.le) (norm_nonneg
            _)
      _ ≤ (|initializedRemainderDerivativeCost L.R S.H0|/k)*NB.C :=
        mul_le_mul_of_nonneg_left hinv (by positivity)
      _ = _ := by ring
  have hp := (((vectorField τ hτ hτT B (initialData D δ hδ (α • ξ) hs)).smul k⁻¹).raw_graph_contDiff
    t k D.m₀).differentiable (by simp) (Y x)
  have hpd : DifferentiableAt ℝ (fun y => k⁻¹ • vector τ hτ hτT B (initialData D δ hδ (α • ξ) hs)
      (t,(Y y,k*⟪D.m₀,Y y⟫_ℝ))) x := by
    simpa only [Function.comp_def,Pi.smul_apply] using hp.comp x hY.differentiableAt
  have hr := ((initializedPrimaryRemainderField M D hTime τ hτ hτT B δ hδ ξ hs α N hN
      k⁻¹).raw_graph_contDiff
    t k D.m₀).differentiable (by simp) (Y x)
  have hrd : DifferentiableAt ℝ (fun y => initializedPrimaryRemainder M D τ hτ hτT B δ hδ ξ hs α N
      k⁻¹
      (t,(Y y,k*⟪D.m₀,Y y⟫_ℝ))) x := by
    simpa only [Function.comp_def] using hr.comp x hY.differentiableAt
  have he : (fun y => initializedVelocity M D τ hτ hτT B δ hδ ξ hs α N k⁻¹
      (t,(Y y,k*⟪D.m₀,Y y⟫_ℝ))) =
      (fun y => k⁻¹ • vector τ hτ hτT B (initialData D δ hδ (α • ξ) hs)
        (t,(Y y,k*⟪D.m₀,Y y⟫_ℝ))) +
      (fun y => initializedPrimaryRemainder M D τ hτ hτT B δ hδ ξ hs α N k⁻¹
        (t,(Y y,k*⟪D.m₀,Y y⟫_ℝ))) := by
    funext y
    dsimp only [initializedPrimaryRemainder,Pi.add_apply,Pi.sub_apply,Pi.smul_apply]
    abel
  rw [he,fderiv_add hpd hrd]
  have ha : ∀ A E R : Space →L[ℝ] Space, A+E-R=(A-R)+E := by intros; abel
  rw [ha]
  exact (norm_add_le _ _).trans ((add_le_add hprimary htail').trans_eq (by
    unfold initializedGlobalShearCost
    ring))

theorem initializedExactPhysicalVelocity_global_gradient_error
    (Cagree : SourceCoefficientAgreement M D) (N : ℕ) (hN : 1 ≤ N) (k : ℝ) (hk : 4 ≤ k)
    (Q : Budget period D.T_pos
      (initializedCorrectionData M D hTime τ hτ hτT B δ hδ ξ hs α Cagree N hN k hk))
    (hbase : tailBase L.R S.H0 BC.termCost N ≤ k ^ (1 / 100 : ℝ))
    (t : Icc (0 : ℝ) D.T) (Y : Space → Space) (x : Space)
    (hY : HasFDerivAt Y (D.FInv.field t (Y x)) x) :
    ‖fderiv ℝ (initializedExactPhysicalVelocity M D hTime τ hτ hτT B δ hδ ξ hs α
      Cagree N hN k hk Q t Y) x -
      (α*deriv (profile δ) (k*⟪D.m₀,Y x⟫_ℝ)) •
        rankOne ℝ (canonicalVelocity τ hτ hτT B ξ hs t (Y x)) (D.normal.field t (Y x))‖ ≤
      initializedGlobalShearCost L.R S.H0 NB.C/k +
        ‖fderiv ℝ (fun y => k⁻¹ • D.F.field t (Y y)
          (Q.pointField period t (cylinderGraph period k D.m₀ (Y y)))) x‖ := by
  rw [initializedExactPhysicalVelocity_fderiv M D hTime τ hτ hτT B δ hδ ξ hs α
    Cagree N hN k hk Q t Y x hY.differentiableAt]
  have ha : ∀ A E R : Space →L[ℝ] Space, A+E-R=(A-R)+E := by intros; abel
  rw [ha]
  exact (norm_add_le _ _).trans (add_le_add
    (initializedVelocity_global_gradient_error M D hTime τ hτ hτT B δ hδ ξ hs α
      L H NB W LM WM BC hRc hcost hδ1 hα hR WP S hgrowth N hN k hk hbase t Y x hY) le_rfl)

end EulerPacketTerminalDatum

end
end

end

@[expose] public section

noncomputable section

namespace EulerPacketPhysicalCost

open EulerSmoothLimit EulerPacketTerminalDatum EulerPacketProfileRecursion
  EulerPacketCylinderField EulerPacketCorrectionConstants EulerPacketCorrectionScalar
  EulerPacketCorrectionOutput EulerPacketFiveCost EulerCylinderSobolevSpace
  EulerCylinderCoordinates EulerPacketPhysicalGevrey EulerPacketInverseFlowGevrey
  EulerAllOrderDriftCorrection EulerPacketGraphHessian EulerPolynomialCost
  EulerParameterWordGevrey

/-- Coordinate cost, given by `‖coordinateEquiv.symm.toContinuousLinearMap‖`. -/
def coordinateCost : ℝ := ‖coordinateEquiv.symm.toContinuousLinearMap‖

/-- Physical envelope, given by `3*X*((1+18*X^2*X)*(9*X^2*(X+coordinateCost*2*S)+2))`. -/
def physicalEnvelope (X S : ℝ) : ℝ :=
  3*X*((1+18*X^2*X)*(9*X^2*(X+coordinateCost*2*S)+2))

/-- Shear envelope as an element of `ℝ`. -/
def shearEnvelope (X : ℝ) : ℝ :=
  coordinateCost*(sobolevEmbeddingConstant period 3*fixedVelocityGradeCost X X 1*(4*X))*X +
    (8*coordinateCost*sobolevEmbeddingConstant period 3*X*(fixedVelocityGradeCost X X 2+2))*X

/-- Hessian envelope, constructed using `sobolevEmbeddingConstant`. -/
def hessianEnvelope (X : ℝ) : ℝ :=
  sobolevEmbeddingConstant period 3*fixedVelocityGradeCost X X 1*X^2*(X+coordinateCost*(4*X)) +
    9*X*physicalEnvelope X (4*X)*sobolevEmbeddingConstant period 3*(fixedVelocityGradeCost X X 2+2)

/-- Time envelope, given by `6*EulerPacketRadiusPolynomial.normalEnvelope X *
(fixedVelocityGradeCost X X 1+fixedVelocityGradeCost X X 2+1)`. -/
def timeEnvelope (X : ℝ) : ℝ :=
  6*EulerPacketRadiusPolynomial.normalEnvelope X *
    (fixedVelocityGradeCost X X 1+fixedVelocityGradeCost X X 2+1)

/-- Radius envelope, given by `1+coordinateCost*(4*X+4*inverseRadiusEnvelope X)`. -/
def radiusEnvelope (X : ℝ) : ℝ := 1+coordinateCost*(4*X+4*inverseRadiusEnvelope X)

/-- Velocity input envelope, given by `liftedInputConstant period*(velocity X X X+normal X X
X)`. -/
def velocityInputEnvelope (X : ℝ) : ℝ := liftedInputConstant period*(velocity X X X+normal X X X)
/-- Error input envelope, given by `2*liftedInputConstant period*outputEnvelope period X`. -/
def errorInputEnvelope (X : ℝ) : ℝ := 2*liftedInputConstant period*outputEnvelope period X
/-- Time input envelope, given by `2*liftedInputConstant period*(timeEnvelope X+outputEnvelope
period X)`. -/
def timeInputEnvelope (X : ℝ) : ℝ := 2*liftedInputConstant period*(timeEnvelope X+outputEnvelope
    period X)
/-- Weighted error envelope, given by `(1+9*X)*physicalEnvelope X (4*inverseRadiusEnvelope
X)*sobolevEmbeddingConstant period 3 * outputEnvelope period X`. -/
def weightedErrorEnvelope (X : ℝ) : ℝ :=
  (1+9*X)*physicalEnvelope X (4*inverseRadiusEnvelope X)*sobolevEmbeddingConstant period 3 *
    outputEnvelope period X

/-- Extra envelope as an element of `ℝ`. -/
def extraEnvelope (X : ℝ) : ℝ :=
  1+outputEnvelope period X+radiusEnvelope X+velocityInputEnvelope X+errorInputEnvelope X +
    timeInputEnvelope X+weightedErrorEnvelope X+shearEnvelope X+hessianEnvelope X

/-- Extra polynomial as an element of `Polynomial ℝ`. -/
def extraPolynomial : Polynomial ℝ :=
  let X : Polynomial ℝ := Polynomial.X
  let c := Polynomial.C coordinateCost
  let e := Polynomial.C (sobolevEmbeddingConstant period 3)
  let l := Polynomial.C (liftedInputConstant period)
  let o := outputPolynomial period
  let i := 1+8*X+4*X^2+X
  let a1 := gradePolynomial 1
  let a2 := gradePolynomial 2
  let v := velocityPolynomial
  let n := X*(a2+2)
  let nb := coefficientPolynomial 6 (5*X+1) (1+X+6*X^2+729*X^6)
  let ti := 6*nb*(a1+a2+1)
  let pp := fun S : Polynomial ℝ => 3*X*((1+18*X^2*X)*(9*X^2*(X+c*2*S)+2))
  let sh := c*(e*a1*(4*X))*X+(8*c*e*X*(a2+2))*X
  let he := e*a1*X^2*(X+c*(4*X))+9*X*pp (4*X)*e*(a2+2)
  1+o+(1+c*(4*X+4*i))+l*(v+n)+2*l*o+2*l*(ti+o)+(1+9*X)*pp (4*i)*e*o+sh+he

theorem extraPolynomial_eval (X : ℝ) : extraPolynomial.eval X=extraEnvelope X := by
  unfold extraPolynomial extraEnvelope radiusEnvelope velocityInputEnvelope errorInputEnvelope
    timeInputEnvelope weightedErrorEnvelope shearEnvelope hessianEnvelope physicalEnvelope
    timeEnvelope EulerPacketRadiusPolynomial.normalEnvelope EulerPacketRadiusPolynomial.coeff
    inverseRadiusEnvelope normal
  dsimp only
  simp only [Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_one,
    Polynomial.eval_ofNat,Polynomial.eval_C,Polynomial.eval_pow,Polynomial.eval_X,
    outputPolynomial_eval,gradePolynomial_eval,velocityPolynomial_eval,coefficientPolynomial_eval]

/-- Extra constant, given by `coefficientCost extraPolynomial`. -/
def extraConstant : ℝ := coefficientCost extraPolynomial
/-- Extra power, given by `extraPolynomial.natDegree`. -/
def extraPower : ℕ := extraPolynomial.natDegree

theorem extraConstant_pos : 0 < extraConstant := coefficientCost_pos _

theorem extraEnvelope_power (X : ℝ) (hX : 1 ≤ X) : extraEnvelope X ≤ extraConstant*X^extraPower :=
    by
  rw [← extraPolynomial_eval]
  exact (le_abs_self _).trans (eval_bound extraPolynomial X hX)

theorem physicalEnvelope_nonneg (X S : ℝ) (hX : 0 ≤ X) (hS : 0 ≤ S) :
    0 ≤ physicalEnvelope X S := by
  have hc : 0 ≤ coordinateCost := norm_nonneg _
  unfold physicalEnvelope
  positivity

theorem extra_components (X : ℝ) (hX : 0 ≤ X) :
    outputEnvelope period X ≤ extraEnvelope X ∧ radiusEnvelope X ≤ extraEnvelope X ∧
    velocityInputEnvelope X ≤ extraEnvelope X ∧ errorInputEnvelope X ≤ extraEnvelope X ∧
    timeInputEnvelope X ≤ extraEnvelope X ∧ weightedErrorEnvelope X ≤ extraEnvelope X ∧
    shearEnvelope X ≤ extraEnvelope X ∧ hessianEnvelope X ≤ extraEnvelope X := by
  have hc : 0 ≤ coordinateCost := norm_nonneg _
  have he := sobolevEmbeddingConstant_nonneg period 3
  have hl := zero_le_one.trans (liftedInputConstant_one_le period)
  have ho := zero_le_one.trans (output_components period X hX).1
  have hi : 0 ≤ inverseRadiusEnvelope X := by unfold inverseRadiusEnvelope; positivity
  have hr : 0 ≤ radiusEnvelope X := by unfold radiusEnvelope; positivity
  have hv := velocity_nonneg X X X hX hX
  have hn := normal_nonneg X X X hX hX
  have hvi : 0 ≤ velocityInputEnvelope X := by unfold velocityInputEnvelope; positivity
  have hei : 0 ≤ errorInputEnvelope X := by unfold errorInputEnvelope; positivity
  have ha1 := fixedVelocityGradeCost_nonneg X X hX 1
  have ha2 := fixedVelocityGradeCost_nonneg X X hX 2
  have hb := EulerPacketRadiusPolynomial.normalEnvelope_nonneg X hX
  have ht : 0 ≤ timeEnvelope X := by unfold timeEnvelope; positivity
  have hti : 0 ≤ timeInputEnvelope X := by unfold timeInputEnvelope; positivity
  have hpp1 := physicalEnvelope_nonneg X (4*X) hX (by positivity)
  have hpp2 := physicalEnvelope_nonneg X (4*inverseRadiusEnvelope X) hX (by positivity)
  have hw : 0 ≤ weightedErrorEnvelope X := by unfold weightedErrorEnvelope; positivity
  have hsh : 0 ≤ shearEnvelope X := by unfold shearEnvelope; positivity
  have hhe : 0 ≤ hessianEnvelope X := by unfold hessianEnvelope; positivity
  unfold extraEnvelope
  refine ⟨?_,?_,?_,?_,?_,?_,?_,?_⟩ <;> linarith

theorem gradeCost_mono (R H X : ℝ) (hR : 0 ≤ R) (hH : 0 ≤ H)
    (hRX : R ≤ X) (hHX : H ≤ X) (n : ℕ) :
    fixedVelocityGradeCost R H n ≤ fixedVelocityGradeCost X X n := by
  have hX := hR.trans hRX
  unfold fixedVelocityGradeCost
  gcongr

variable {U : Type*} [NormedAddCommGroup U] [InnerProductSpace ℝ U]
  (D : EulerTransversePacketProvider.Data U)

theorem physicalFixedCost_one_le (R C S X Y : ℝ) (hR : 0 ≤ R) (hC : 0 ≤ C) (hS : 0 ≤ S)
    (hRX : R ≤ X) (hCX : C ≤ X) (hSY : S ≤ Y) :
    physicalFixedCost D R C S 1 ≤ physicalEnvelope X Y := by
  have hX := hR.trans hRX
  have hY := hS.trans hSY
  have hc : 0 ≤ coordinateCost := norm_nonneg _
  simp only [physicalFixedCost,physicalRadiusCost,sourceInverseRadius,physicalEnvelope,
    coordinateCost,D.m₀_unit,Nat.factorial_one,Nat.cast_one,pow_one,one_pow,mul_one]
  norm_num only
  gcongr

theorem shearCost_le (R H C X : ℝ) (hR : 0 ≤ R) (hH : 0 ≤ H) (hC : 0 ≤ C)
    (hRX : R ≤ X) (hHX : H ≤ X) (hCX : C ≤ X) :
    initializedGlobalShearCost R H C ≤ shearEnvelope X := by
  have hX := hR.trans hRX
  have he := sobolevEmbeddingConstant_nonneg period 3
  have hc : 0 ≤ coordinateCost := norm_nonneg _
  have ha1 := gradeCost_mono R H X hR hH hRX hHX 1
  have ha2 := gradeCost_mono R H X hR hH hRX hHX 2
  have hg1 := fixedVelocityGradeCost_nonneg R H hR 1
  have hg2 := fixedVelocityGradeCost_nonneg R H hR 2
  have hg1X := hg1.trans ha1
  have hg2X := hg2.trans ha2
  have hrem : 0 ≤ initializedRemainderDerivativeCost R H := by
    unfold initializedRemainderDerivativeCost
    positivity
  unfold initializedGlobalShearCost shearEnvelope
  rw [abs_of_nonneg hrem]
  unfold initializedRemainderDerivativeCost coordinateCost
  gcongr

theorem hessianCost_le {q : ℕ} {R₀ : ℝ}
    (N : EulerTransversePacketJoin.NormalBudget D q R₀)
    (R H Rc C X : ℝ) (hR : 0 ≤ R) (hH : 0 ≤ H) (hRc : 0 ≤ Rc) (hC : 0 ≤ C)
    (hRX : R ≤ X) (hHX : H ≤ X) (hRcX : Rc ≤ X) (hCX : C ≤ X)
    (hNR : N.Rc ≤ X) (hNC : N.C ≤ X) :
    initializedPressureHessianCost N R H Rc C ≤ hessianEnvelope X := by
  have hX := hR.trans hRX
  have he := sobolevEmbeddingConstant_nonneg period 3
  have hc : 0 ≤ coordinateCost := norm_nonneg _
  have ha1 := gradeCost_mono R H X hR hH hRX hHX 1
  have ha2 := gradeCost_mono R H X hR hH hRX hHX 2
  have hg1 := fixedVelocityGradeCost_nonneg R H hR 1
  have hg2 := fixedVelocityGradeCost_nonneg R H hR 2
  have hg1X := hg1.trans ha1
  have hg2X := hg2.trans ha2
  have hpp := physicalFixedCost_one_le D Rc C (4*R) X (4*X) hRc hC (by positivity)
    hRcX hCX (by gcongr)
  have hp0 := physicalFixedCost_nonneg D Rc C (4*R) 1 hRc hC (by positivity)
  have hpX := hp0.trans hpp
  have hNC0 := N.C_nonneg
  have hNR0 := N.Rc_nonneg
  unfold initializedPressureHessianCost fastHessianCost hessianEnvelope coordinateCost
  gcongr

end EulerPacketPhysicalCost
