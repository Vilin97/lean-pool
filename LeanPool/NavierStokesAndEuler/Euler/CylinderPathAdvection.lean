/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import LeanPool.NavierStokesAndEuler.Euler.CylinderPathBilinear
import LeanPool.NavierStokesAndEuler.Euler.ClassicalPressureCurl
import LeanPool.NavierStokesAndEuler.Euler.CylinderTimeGradient
import LeanPool.NavierStokesAndEuler.Euler.ParameterSobolevFiniteSum
public import LeanPool.NavierStokesAndEuler.Euler.CylinderPathProductBounds
public import LeanPool.NavierStokesAndEuler.Euler.CylinderPathWords

/-! Literal spatial advection of smooth continuous cylinder paths, with unchanged word radius. -/

section

/-! A literal product with one mixed cylinder derivative consumes exactly one shift. -/

@[expose] public section

noncomputable section

namespace EulerCylinderPathProduct

open Set MeasureTheory ContinuousLinearMap EulerSmoothLimit EulerLiftedGradientSpace
  EulerCylinderSmoothOrbit EulerLpCylinderTranslation EulerCylinderSobolev
  EulerParameterWordGevrey EulerGevrey EulerMetricTransport EulerLiftedWeakDerivative
open scoped ContDiff

variable (P : ℝ) [Fact (0 < P)] {K : Type*} [TopologicalSpace K] [CompactSpace K]
  (L : Space →L[ℝ] ℝ) (hL : ‖L‖ ≤ 1) (p q : C(K, LiftL2 P))
  (hp : ContDiff ℝ ∞ (fun a : LiftTangent => pathTranslate P a p))
  (hq : ContDiff ℝ ∞ (fun a : LiftTangent => pathTranslate P a q))
  (i : Fin 4)

/-- The continuous L² path for one factor times an actual spatial or angular derivative. -/
def scalarDerivativeProductPath : C(K,LiftL2 P) :=
  scalarProductPath P L hL p (derivativePath P q i) hp (derivativePath_orbit P q hq i)

theorem scalarDerivativeProductPath_orbit :
    ContDiff ℝ ∞ (fun a : LiftTangent =>
      pathTranslate P a (scalarDerivativeProductPath P L hL p q hp hq i)) :=
  scalarProductPath_orbit P L hL p (derivativePath P q i) hp (derivativePath_orbit P q hq i)

theorem pointField_scalarDerivativeProductPath (t : K) (x : LiftDomain P) :
    pointField P (scalarDerivativeProductPath P L hL p q hp hq i)
      (scalarDerivativeProductPath_orbit P L hL p q hp hq i) t x =
      L (pointField P p hp t x) •
        fieldFDeriv P (pointField P q hq t) x (standardDirection i) := by
  have h := pointField_scalarProductPath P L hL p (derivativePath P q i)
    hp (derivativePath_orbit P q hq i) t x
  rw [pointField_derivativePath P q hq] at h
  exact h

/-- Fixed-H6 external word bounds preserve the same radius, with one derivative shift. -/
theorem scalarDerivativeProductPath_majorant (R A C : ℝ)
    (hR : 0 ≤ R) (hA : 0 ≤ A) (hC : 0 ≤ C) (d e : ℕ) (a : LiftTangent)
    (hb : ∀ n, block standardDirection 6 (fun b : LiftTangent => pathTranslate P b p) n a ≤
      A*majorant R d n)
    (hc : ∀ n, block standardDirection 6 (fun b : LiftTangent => pathTranslate P b q) n a ≤
      C*majorant R e n) (n : ℕ) :
    block standardDirection 6 (fun b : LiftTangent =>
      pathTranslate P b (scalarDerivativeProductPath P L hL p q hp hq i)) n a ≤
      (3*productBlockConstant P*A*C)*majorant R (d+e+1) n := by
  have hd (j : ℕ) : block standardDirection 6
      (fun b : LiftTangent => pathTranslate P b (derivativePath P q i)) j a ≤
        C*majorant R (e+1) j := by
    have h := (derivativePath_block_bound P q hq i 6 j a).trans (hc (j+1))
    simpa only [majorant, show j+1+e=j+(e+1) by omega] using h
  simpa only [scalarDerivativeProductPath, Nat.add_assoc] using
    scalarProductPath_majorant P L hL p (derivativePath P q i)
      hp (derivativePath_orbit P q hq i) R A C hR hA hC d (e+1) a hb hd n

end EulerCylinderPathProduct

end
end

end

@[expose] public section

noncomputable section

namespace EulerCylinderPathProduct

open Set MeasureTheory ContinuousLinearMap Finset EulerSmoothLimit EulerLiftedGradientSpace
  EulerCylinderSmoothOrbit EulerLpCylinderTranslation EulerCylinderSobolev
  EulerParameterWordGevrey EulerGevrey EulerMetricTransport EulerLiftedWeakDerivative
open scoped ContDiff

theorem sum_spatial_components (u : Space) :
    (∑ i : Fin 3, component i u • standardDirection i.succ) = (u,0) := by
  have h := congrArg (ContinuousLinearMap.inl ℝ Space ℝ) (sum_components u)
  simpa only [map_sum, map_smul, standardDirection_succ, basisVector, inl_apply] using h

theorem spatial_advection_components (D : LiftTangent →L[ℝ] Space) (u : Space) :
    (∑ i : Fin 3, component i u • D (standardDirection i.succ)) = D (u,0) := by
  simpa only [map_sum, map_smul] using congrArg D (sum_spatial_components u)

variable (P : ℝ) [Fact (0 < P)] {K : Type*} [TopologicalSpace K] [CompactSpace K]
  (p q : C(K, LiftL2 P))
  (hp : ContDiff ℝ ∞ (fun a : LiftTangent => pathTranslate P a p))
  (hq : ContDiff ℝ ∞ (fun a : LiftTangent => pathTranslate P a q))

/-- The actual path representing p·∇q, where the derivative is spatial and the angle is retained. -/
def advectionPath : C(K,LiftL2 P) :=
  ∑ i : Fin 3, scalarDerivativeProductPath P (component i) (component_norm i) p q hp hq i.succ

theorem advectionPath_orbit :
    ContDiff ℝ ∞ (fun a : LiftTangent => pathTranslate P a (advectionPath P p q hp hq)) := by
  simp only [advectionPath, map_sum]
  exact ContDiff.sum (fun i _ =>
    scalarDerivativeProductPath_orbit P (component i) (component_norm i) p q hp hq i.succ)

theorem advectionPath_ae (t : K) :
    (advectionPath P p q hp hq t : LiftDomain P → Space) =ᵐ[liftMeasure P]
      fun x => fieldFDeriv P (pointField P q hq t) x (pointField P p hp t x,0) := by
  let r := fun i : Fin 3 =>
    scalarDerivativeProductPath P (component i) (component_norm i) p q hp hq i.succ
  have ht (i : Fin 3) : (r i t : LiftDomain P → Space) =ᵐ[liftMeasure P]
      fun x => component i (pointField P p hp t x) •
        fieldFDeriv P (pointField P q hq t) x (standardDirection i.succ) := by
    filter_upwards [pointField_ae P (r i)
      (scalarDerivativeProductPath_orbit P (component i) (component_norm i) p q hp hq i.succ) t]
      with x hx
    exact hx.trans (pointField_scalarDerivativeProductPath P (component i) (component_norm i)
      p q hp hq i.succ t x)
  have hall := Filter.eventually_all.mpr ht
  have hs := Lp.coeFn_fun_finsetSum (univ : Finset (Fin 3)) (fun i => r i t)
  filter_upwards [hs,hall] with x hs hx
  change (∑ i : Fin 3, r i t) x = _
  rw [hs]
  exact (sum_congr rfl (fun i _ => hx i)).trans
    (spatial_advection_components _ (pointField P p hp t x))

theorem pointField_advectionPath (t : K) (x : LiftDomain P) :
    pointField P (advectionPath P p q hp hq) (advectionPath_orbit P p q hp hq) t x =
      fieldFDeriv P (pointField P q hq t) x (pointField P p hp t x,0) := by
  have hD := (pointField_fderiv_joint_continuous P q hq).comp
    ((continuous_const : Continuous (fun _ : LiftDomain P => t)).prodMk continuous_id)
  have he := Measure.eq_of_ae_eq
    ((pointField_ae P _ (advectionPath_orbit P p q hp hq) t).symm.trans
      (advectionPath_ae P p q hp hq t))
    (smoothField_continuous P _ (pointField_smooth P _ _ t))
    (hD.clm_apply ((smoothField_continuous P _ (pointField_smooth P p hp t)).prodMk
        continuous_const))
  exact congrFun he x

/-- Actual H6 word blocks for spatial advection consume just one derivative shift. -/
theorem advectionPath_majorant (R A C : ℝ) (hR : 0 ≤ R) (hA : 0 ≤ A) (hC : 0 ≤ C)
    (d e : ℕ) (a : LiftTangent)
    (hb : ∀ n, block standardDirection 6 (fun b : LiftTangent => pathTranslate P b p) n a ≤
      A*majorant R d n)
    (hc : ∀ n, block standardDirection 6 (fun b : LiftTangent => pathTranslate P b q) n a ≤
      C*majorant R e n) (n : ℕ) :
    block standardDirection 6 (fun b : LiftTangent => pathTranslate P b (advectionPath P p q hp
        hq)) n a ≤
      (9*productBlockConstant P*A*C)*majorant R (d+e+1) n := by
  let f := fun i : Fin 3 => fun b : LiftTangent => pathTranslate P b
    (scalarDerivativeProductPath P (component i) (component_norm i) p q hp hq i.succ)
  have he : (fun b : LiftTangent => pathTranslate P b (advectionPath P p q hp hq)) =
      ∑ i : Fin 3, f i := by
    funext b
    simp only [advectionPath, map_sum, f, Finset.sum_apply]
  rw [he]
  have h := block_finset_sum_le standardDirection 6 univ f
    (fun i _ => scalarDerivativeProductPath_orbit P (component i) (component_norm i) p q hp hq
        i.succ) n a
  exact h.trans ((sum_le_sum (fun i _ => scalarDerivativeProductPath_majorant P
    (component i) (component_norm i) p q hp hq i.succ R A C hR hA hC d e a hb hc n)).trans_eq
      (by simp only [sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul, Nat.cast_ofNat]; ring))

end EulerCylinderPathProduct
