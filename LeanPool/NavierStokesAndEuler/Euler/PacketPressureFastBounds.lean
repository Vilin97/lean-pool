/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.PacketPressureFastHessian
public import LeanPool.NavierStokesAndEuler.Euler.PacketPhysicalPressureGevrey
public import LeanPool.NavierStokesAndEuler.Euler.TransversePacketNormalBudget

@[expose] public section

/-! Quantitative Hessian errors retain one inverse-frequency factor.
The coefficient bounds are those of the actual source deformation. -/

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

def fastHessianCost (R A : ℝ) : ℝ :=
  sobolevEmbeddingConstant P 3*A*NB.C^2*(NB.Rc+‖coordinateEquiv.symm.toContinuousLinearMap‖*R)

theorem fastHessianRemainder_bound (a : ScalarField)
    (G : Field P D.T (fun z => a z • D.m₀))
    (R A : ℝ) (hR : 0 ≤ R) (hA : 0 ≤ A) (hG : G.WordBound 6 R A 0)
    (k : ℝ) (hk : 0 < k) (t : Icc (0 : ℝ) D.T) (Y : Space → Space)
    (x : Space) (hY : HasFDerivAt Y (D.FInv.field t (Y x)) x)
    (ha : DifferentiableAt ℝ (fun z => a (t,z)) (graphMap k D.m₀ (Y x))) :
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

def physicalCovector (_G : Field P D.T raw) (k : ℝ) (Y : Icc (0 : ℝ) D.T → Space → Space)
    (t : Icc (0 : ℝ) D.T) (x : Space) : Space :=
  (D.FInv.field t (Y t x)).adjoint (raw (t,(Y t x,k*⟪D.m₀,Y t x⟫_ℝ)))

theorem physicalCovector_error_bound (R A : ℝ) (hR : 0 ≤ R) (hA : 0 ≤ A)
    (k : ℝ) (hk : 1 ≤ k) (hG : G.WordBound 6 R (A/k^2) 0)
    (Rc C : ℝ) (hRc : 0 ≤ Rc) (hC : 0 ≤ C)
    (hdet : ∀ t x, (EulerPacketPiola.operatorMatrix (D.F.field t x)).det=1)
    (hF : ∀ n t x,
      ‖iteratedFDeriv ℝ n (D.F.field t : Space → Space →L[ℝ] Space) x‖ ≤ C*majorant Rc 0 n)
    (X Y : Icc (0 : ℝ) D.T → Space → Space)
    (hX : ∀ t x, HasFDerivAt (X t) (D.F.field t x) x)
    (hY : ∀ t, Differentiable ℝ (Y t)) (hXY : ∀ t x, X t (Y t x)=x)
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
