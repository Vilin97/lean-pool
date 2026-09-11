/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.PacketPressureFastHessian
public import LeanPool.NavierStokesAndEuler.Euler.PacketPhysicalPressureGevrey
public import LeanPool.NavierStokesAndEuler.Euler.TransversePacketNormalBudget
public import LeanPool.NavierStokesAndEuler.Euler.PacketCylinderFieldBounds
import LeanPool.NavierStokesAndEuler.Euler.PacketFieldGraphBounds
import LeanPool.NavierStokesAndEuler.Euler.PacketFieldTensorBounds
import Mathlib.Algebra.Order.Star.Real
public import LeanPool.NavierStokesAndEuler.Euler.PacketInitializedPressureBudgets
public import LeanPool.NavierStokesAndEuler.Euler.PacketPressureCovector
public import LeanPool.NavierStokesAndEuler.Euler.PacketFiniteCoarseBounds
public import LeanPool.NavierStokesAndEuler.Euler.PacketFiniteFieldAlgebra
public import LeanPool.NavierStokesAndEuler.Euler.PacketFiniteRemainderBounds
import LeanPool.NavierStokesAndEuler.Euler.PacketCylinderHighPartBounds
import LeanPool.NavierStokesAndEuler.Euler.PacketCylinderWeightedLinear
import LeanPool.NavierStokesAndEuler.Euler.PacketExponentialTail
import LeanPool.NavierStokesAndEuler.Euler.PacketFiniteAssemblyBounds
import LeanPool.NavierStokesAndEuler.Euler.PacketFiniteFrequencyBounds
import LeanPool.NavierStokesAndEuler.Euler.PacketProfileCoarseBounds

/-! Related estimates used together by the same construction modules. -/

section

/-! Quantitative Hessian errors retain one inverse-frequency factor.
The coefficient bounds are those of the actual source deformation. -/

@[expose] public section

noncomputable section

namespace EulerPacketGraphHessian

open Set InnerProductSpace ContinuousLinearMap EulerSmoothLimit EulerGraphPullback
  EulerLiftedGradientSpace EulerPacketCylinderField EulerPacketProfileRecursion
  EulerPacketPointJets EulerGevrey EulerCylinderCoordinates EulerCylinderSobolevSpace
  EulerTransversePacketProvider EulerPacketPhysicalGevrey EulerCylinderPhysicalTensor
      EulerCylinderSobolev
open scoped ContDiff

variable {P : ℝ} [Fact (0 < P)]
  {U : Type*} [NormedAddCommGroup U] [InnerProductSpace ℝ U]
  {D : Data U} {q : ℕ} {R₀ : ℝ} (NB : EulerTransversePacketJoin.NormalBudget D q R₀)

/-- Fast hessian cost, given by `sobolevEmbeddingConstant P
3*A*NB.C^2*(NB.Rc+‖coordinateEquiv.symm.toContinuousLinearMap‖*R)`. -/
def fastHessianCost (R A : ℝ) : ℝ :=
  sobolevEmbeddingConstant P 3*A*NB.C^2*(NB.Rc+‖coordinateEquiv.symm.toContinuousLinearMap‖*R)

theorem fastHessianRemainder_bound (a : ScalarField)
    (G : Field P D.T (fun z => a z • D.m₀))
    (R A : ℝ) (hR : 0 ≤ R) (hA : 0 ≤ A) (hG : G.WordBound 6 R A 0)
    (k : ℝ) (hk : 0 < k) (t : Icc (0 : ℝ) D.T) (Y : Space → Space)
    (x : Space) (hY : HasFDerivAt Y (D.FInv.field t (Y x)) x)
    (ha : DifferentiableAt ℝ (fun z => a (t, z)) (graphMap k D.m₀ (Y x))) :
    ‖fastHessianRemainder (fun z => a (t,z)) k D.m₀ Y
      (fun y => D.FInv.field t (Y y)) x‖ ≤ fastHessianCost (P := P) NB R A/k := by
  let z := graphMap k D.m₀ (Y x)
  have hs := sobolevEmbeddingConstant_nonneg P 3
  have hC := NB.C_nonneg
  have hRc := NB.Rc_nonneg
  have hval : |a (t,z)| ≤ sobolevEmbeddingConstant P 3*A := by
    have h := hG.raw_graph_norm_le (by norm_num) t k D.m₀ (Y x)
    simpa only [z,graphMap_apply,norm_smul,Real.norm_eq_abs,D.m₀_unit,mul_one] using h
  have hda : ‖fderiv ℝ (fun z => a (t,z)) z‖ ≤
      ‖coordinateEquiv.symm.toContinuousLinearMap‖*(sobolevEmbeddingConstant P 3*A*R) := by
    have h := hG.raw_fderiv_le (by norm_num) t z
    rw [norm_fderiv_smul_unit (fun z => a (t,z)) D.m₀ D.m₀_unit z ha] at h
    simpa [majorant] using h
  have hJ : ‖D.FInv.field t (Y x)‖ ≤ NB.C := by simpa [majorant] using NB.inverse_bound 0 t (Y x)
  have hn : ‖D.normal.field t (Y x)‖ ≤ NB.C := by simpa [majorant] using NB.normal_bound 0 t (Y x)
  have hnd : ‖fderiv ℝ (D.normal.field t : Space → Space) (Y x)‖ ≤ NB.C*NB.Rc := by
    simpa [majorant] using NB.normal_bound 1 t (Y x)
  have hnder : fderiv ℝ (transportedNormal D.m₀ (fun y => D.FInv.field t (Y y))) x =
      (fderiv ℝ (D.normal.field t : Space → Space) (Y x)).comp (D.FInv.field t (Y x)) :=
    (((D.normal.smooth t).differentiable (by simp) (Y x)).hasFDerivAt.comp x hY).fderiv
  have hnD : ‖fderiv ℝ (transportedNormal D.m₀ (fun y => D.FInv.field t (Y y))) x‖ ≤
      (NB.C*NB.Rc)*NB.C := by
    rw [hnder]
    exact (opNorm_comp_le _ _).trans (mul_le_mul hnd hJ (norm_nonneg _) (mul_nonneg hC hRc))
  have h1 := mul_le_mul hval hnD (norm_nonneg _) (mul_nonneg hs hA)
  have h2 := mul_le_mul hda hJ (norm_nonneg _) (by positivity)
  have h3 := mul_le_mul h2 hn (norm_nonneg _) (by positivity)
  have h := fastHessianRemainder_norm_le (fun z => a (t,z)) k D.m₀ Y
    (fun y => D.FInv.field t (Y y)) x
  rw [abs_of_pos (inv_pos.mpr hk)] at h
  exact h.trans ((mul_le_mul_of_nonneg_left (add_le_add h1 h3) (inv_pos.mpr hk).le).trans_eq
    (by unfold fastHessianCost; ring))

variable (D) {raw : VectorField} (G : Field P D.T raw)

/-- Physical covector, given by `(D.FInv.field t (Y t x)).adjoint (raw (t,(Y t x,k*⟪D.m₀,Y t
x⟫_ℝ)))`. -/
def physicalCovector (_G : Field P D.T raw) (k : ℝ) (Y : Icc (0 : ℝ) D.T → Space → Space)
    (t : Icc (0 : ℝ) D.T) (x : Space) : Space :=
  (D.FInv.field t (Y t x)).adjoint (raw (t,(Y t x,k*⟪D.m₀,Y t x⟫_ℝ)))

theorem physicalCovector_error_bound (R A : ℝ) (hR : 0 ≤ R) (hA : 0 ≤ A)
    (k : ℝ) (hk : 1 ≤ k) (hG : G.WordBound 6 R (A / k ^ 2) 0)
    (Rc C : ℝ) (hRc : 0 ≤ Rc) (hC : 0 ≤ C)
    (hdet : ∀ t x, (EulerPacketPiola.operatorMatrix (D.F.field t x)).det = 1)
    (hF : ∀ n t x,
      ‖iteratedFDeriv ℝ n (D.F.field t : Space → Space →L[ℝ] Space) x‖ ≤ C * majorant Rc 0 n)
    (X Y : Icc (0 : ℝ) D.T → Space → Space)
    (hX : ∀ t x, HasFDerivAt (X t) (D.F.field t x) x)
    (hY : ∀ t, Differentiable ℝ (Y t)) (hXY : ∀ t x, X t (Y t x) = x)
    (t : Icc (0 : ℝ) D.T) (x : Space) :
    ‖fderiv ℝ (physicalCovector D G k Y t) x‖ ≤
      (9*C*physicalFixedCost D Rc C R 1*sobolevEmbeddingConstant P 3*A)/k := by
  have hk0 : k ≠ 0 := by linarith
  have hb : ∀ n t z, (∑ w : Fin n → Fin 4,
      ‖iteratedFieldDerivative P w (G.toFieldTower.pointField t) z‖) ≤
      (sobolevEmbeddingConstant P 3*(A/k^2))*R^n*(n.factorial : ℝ)^2 := by
    intro n s z
    simpa [majorant,mul_assoc] using hG.pointField_wordSum_le (by norm_num) s n z
  have h := physicalPressureForce_power_bound D P 1 k G.toFieldTower.pointField
    G.toFieldTower.pointField_smooth Rc C (sobolevEmbeddingConstant P 3*(A/k^2)) R
    hRc hC (mul_nonneg (sobolevEmbeddingConstant_nonneg P 3) (div_nonneg hA (sq_nonneg k)))
    hR hdet hF hb X Y hX hY hXY hk (by norm_num) 1 t x
  have he : physicalPressureForce D P 1 k G.toFieldTower.pointField Y t =
      physicalCovector D G k Y t := by
    funext y
    simp only [physicalPressureForce,graphPressureForce,physicalField,
      EulerGraphPressurePotential.cylinderGraph,one_smul,physicalCovector,
      G.toFieldTower_pointField_raw]
  rw [he,norm_iteratedFDeriv_one] at h
  exact h.trans_eq (by simp only [pow_one]; field_simp)

end EulerPacketGraphHessian

end
end

end

section

/-! The finite pressure covector differs from the leading angular
primary by an actual O(k⁻²) cylinder field, uniformly in the truncation
length selected by the source frequency guard. -/

@[expose] public section

noncomputable section

namespace EulerPacketPressure

open Set EulerSmoothLimit EulerPacketPointJets EulerPacketProfileRecursion
  EulerPacketCylinderField EulerPacketTimeProfile EulerPacketShiftArithmetic
  EulerPacketCoarseMajorant EulerPacketFiniteFrequency EulerFiniteGrades

variable {P T : ℝ} [Fact (0 < P)] {N : ℕ} {a : ℕ → Profile} {support : Set Space}
  (hT : 0 < T) (m : Space)
  (G : ∀ i, i ≤ N → ProfileRegularity P T hT.le support (a i))
  {S : Scales (Icc (0 : ℝ) T)} {R : ℝ}
  (K : ∀ i, i ≤ N → PressureBudget P T hT.le m (a i) S R i)

/-- Covector grade field, constructed using `Field.assembleFamily`. -/
def covectorGradeField (i : ℕ) : Field P T (covectorGrades N m a i) :=
  Field.assembleFamily N
    (fun j => pressureGradient (a j).meanPressure+angularPressure m (a j).highPressure)
    (fun j => pressureGradient (a j).highPressure)
    (fun j hj => (K j hj).mean.add (K j hj).angular) (fun j hj => (G j hj).pressure) i

variable (hG : ∀ i (hi : i ≤ N), 1 ≤ i → ProfileBudget (G i hi) S R i)
  (hR : 1 ≤ R) (ha : a 0 = 0)

include hG hR ha in
theorem covectorGrade_bound (i : ℕ) :
    (covectorGradeField hT m G K i).WordBound 6 R (3*S.H0^(2*i)) (highShift i) := by
  apply Field.wordBound_assembleFamily N _ _ _ _ R S.H0 hR S.H0_one_le
  · intro j hj
    by_cases hj0 : j=0
    · subst j
      have hz : ∀ (t : Icc (0 : ℝ) T) x θ,
          (pressureGradient (a 0).meanPressure+angularPressure m (a 0).highPressure) (t,(x,θ))=0 :=
              by
        intro t x θ
        rw [ha]
        simp [pressureGradient,angularPressure,pressureJet_zero]
      exact (Field.wordBound_of_zero ((K 0 hj).mean.add (K 0 hj).angular) hz 6 R (highShift
          0)).mono_amplitude
        (zero_le_one.trans hR) (by norm_num)
    · have hm := (K j hj).mean_bound.remove_profile hT.le (S.mean j) (S.mean_pos j)
        (S.H0^(2*j)) (pow_nonneg S.H0_pos.le _) (S.mean_le_coarse j)
      have hq := (K j hj).angular_bound.remove_profile hT.le (S.high j) (S.high_pos j)
        (S.H0^(2*j)) (pow_nonneg S.H0_pos.le _) (S.high_le_coarse j (by omega))
      simp only [mul_one] at hm hq
      have hm' := hm.mono_shift hR (pow_nonneg S.H0_pos.le _)
        (show meanShift j ≤ highShift j by unfold meanShift highShift; omega)
      change ((K j hj).mean.add (K j hj).angular).WordBound 6 R (2*S.H0^(2*j)) (highShift j)
      rw [two_mul (S.H0^(2*j))]
      exact hm'.add hq
  · intro j hj
    by_cases hj0 : j=0
    · subst j
      exact (Field.wordBound_of_zero (G 0 hj).pressure
        (fun _ _ _ => by rw [ha]; simp [pressureGradient,pressureJet_zero])
        6 R (highShift 0)).mono_amplitude (zero_le_one.trans hR) (by norm_num)
    · exact (hG j hj (by omega)).pressure_unnormalized (by omega)

include ha in
theorem covectorGrades_zero : covectorGrades N m a 0=0 := by
  apply assemble_zero
  rw [ha]
  funext z
  simp [pressureGradient,angularPressure,pressureJet_zero]

include ha in
theorem covectorGrades_one (hN : 1 ≤ N) (hm : (a 1).meanPressure = 0) :
    covectorGrades N m a 1=angularPressure m (a 1).highPressure := by
  rw [covectorGrades,assemble_interior N 1 le_rfl hN]
  simp only [Nat.sub_self,hm,ha]
  funext z
  simp [pressureGradient,angularPressure,pressureJet_zero]

/-- Covector remainder, given by `fieldSum (N+1) κ (covectorGrades N m a)-κ • angularPressure m
(a 1).highPressure`. -/
def covectorRemainder (κ : ℝ) : VectorField :=
  fieldSum (N+1) κ (covectorGrades N m a)-κ • angularPressure m (a 1).highPressure

/-- Covector remainder field as an element of `Field P T (covectorRemainder (N := N) (a := a) m
κ)`. -/
def covectorRemainderField (hN : 1 ≤ N) (hm : (a 1).meanPressure = 0) (κ : ℝ) :
    Field P T (covectorRemainder (N := N) (a := a) m κ) :=
  (Field.evaluateRemainder (N+1) (by omega) κ (covectorGrades N m a)
    (covectorGradeField hT m G K)).congr
      (fun _ _ _ => by rw [covectorGrades_one m ha hN hm]; rfl)

include hG hR in
theorem covectorRemainder_bound (hN : 1 ≤ N) (hm : (a 1).meanPressure = 0)
    {O : Operators} {C : CoefficientData P T O} (BC : CoefficientBudget C)
    (k : ℝ) (hk : 4 ≤ k) (hbase : tailBase R S.H0 BC.termCost N ≤ k ^ (1 / 100 : ℝ)) :
    (covectorRemainderField hT m G K ha hN hm k⁻¹).WordBound 6 (4*R)
      ((fixedVelocityGradeCost R S.H0 2+2)/k^2) 0 := by
  have hk0 : 0 < k := by linarith
  let B := tailBase R S.H0 BC.termCost N
  have hB : 0 ≤ B := tailBase_nonneg R S.H0 BC.termCost BC.termCost_nonneg N
  have hsmall : k⁻¹*B ≤ 1/2 := by
    simpa only [div_eq_mul_inv,mul_comm] using EulerPacketTailBound.grade_ratio_le_half k B hk hbase
  have hz := covectorGrades_zero (N := N) m ha
  have h := Field.wordBound_evaluateRemainder N hN k⁻¹ B (fixedVelocityGradeCost R S.H0 2)
    (inv_nonneg.mpr hk0.le) hB hsmall (covectorGrades N m a) (covectorGradeField hT m G K)
    6 (4*R) (by linarith) (fun _ _ _ => by rw [hz]; rfl)
    ((covectorGrade_bound hT m G K hG hR ha 2).fixed_velocity_grade (zero_le_one.trans hR)
        S.H0_pos.le)
    (fun n _ hn => (covectorGrade_bound hT m G K hG hR ha n).coarse_velocity_grade
      hR S.H0_one_le BC.termCost BC.one_le_termCost N hN (by omega))
  exact (h.mono_amplitude (by linarith)
    (remainder_low_high_le k B (fixedVelocityGradeCost R S.H0 2) hk0
      (fourth_power_le_frequency k B (by linarith) hB hbase))).of_path_eq _ rfl

end EulerPacketPressure

end
end

end
