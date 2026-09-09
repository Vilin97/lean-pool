/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.CylinderPathProduct
public import LeanPool.NavierStokesAndEuler.Euler.CylinderConstantMap

@[expose] public section

/-! Literal bounded bilinear nonlinearities preserve smooth continuous cylinder L² paths. -/

noncomputable section

namespace EulerCylinderPathProduct

open Set MeasureTheory ContinuousLinearMap Finset EulerSmoothLimit EulerLiftedGradientSpace
  EulerCylinderSobolevSpace EulerCylinderSmoothOrbit EulerLpCylinderTranslation
  EulerCylinderConstantMap EulerMetricTransport
open scoped ContDiff

def component (i : Fin 3) : Space →L[ℝ] ℝ := EuclideanSpace.proj i

theorem component_norm (i : Fin 3) : ‖component i‖ ≤ 1 := by
  apply opNorm_le_bound _ zero_le_one
  intro u
  change ‖u i‖ ≤ (1 : ℝ)*‖u‖
  simpa only [one_mul] using PiLp.norm_apply_le u i

def basisVector (i : Fin 3) : Space := EuclideanSpace.single i 1

theorem sum_components (u : Space) : (∑ i : Fin 3, component i u • basisVector i) = u := by
  ext i
  simp [component, basisVector, Pi.single_apply, mul_ite]

theorem bilinear_components (B : Space →L[ℝ] Space →L[ℝ] Space) (u v : Space) :
    (∑ i : Fin 3, B (basisVector i) (component i u • v)) = B u v := by
  have h := congrArg (fun z : Space => B z v) (sum_components u)
  simpa only [map_sum, _root_.sum_apply, map_smul, smul_apply] using h

variable (P : ℝ) [Fact (0 < P)] {K : Type*} [TopologicalSpace K] [CompactSpace K]
  (B : Space →L[ℝ] Space →L[ℝ] Space) (p q : C(K,LiftL2 P))
  (hp : ContDiff ℝ ∞ (fun a : LiftTangent => pathTranslate P a p))
  (hq : ContDiff ℝ ∞ (fun a : LiftTangent => pathTranslate P a q))

def bilinearTerm (i : Fin 3) : C(K,LiftL2 P) :=
  pathMap P (B (basisVector i))
    (scalarProductPath P (component i) (component_norm i) p q hp hq)

theorem bilinearTerm_orbit (i : Fin 3) :
    ContDiff ℝ ∞ (fun a : LiftTangent => pathTranslate P a (bilinearTerm P B p q hp hq i)) :=
  pathMap_orbit_contDiff P (B (basisVector i)) _
    (scalarProductPath_orbit P (component i) (component_norm i) p q hp hq)

/-- An arbitrary fixed bilinear vector operation on the actual L² paths. -/
def bilinearProductPath : C(K,LiftL2 P) := ∑ i : Fin 3, bilinearTerm P B p q hp hq i

theorem bilinearProductPath_orbit :
    ContDiff ℝ ∞ (fun a : LiftTangent => pathTranslate P a (bilinearProductPath P B p q hp hq)) :=
      by
  simp only [bilinearProductPath, map_sum]
  exact ContDiff.sum (fun i _ => bilinearTerm_orbit P B p q hp hq i)

theorem bilinearTerm_ae (i : Fin 3) (t : K) :
    (bilinearTerm P B p q hp hq i t : LiftDomain P → Space) =ᵐ[liftMeasure P]
      fun x => B (basisVector i) (component i (pointField P p hp t x) • pointField P q hq t x) := by
  filter_upwards [map_ae P (B (basisVector i))
      (scalarProductPath P (component i) (component_norm i) p q hp hq t),
    scalarProductPath_ae P (component i) (component_norm i) p q hp hq t] with x hm hp
  exact hm.trans (congrArg (B (basisVector i)) hp)

theorem bilinearProductPath_ae (t : K) :
    (bilinearProductPath P B p q hp hq t : LiftDomain P → Space) =ᵐ[liftMeasure P]
      fun x => B (pointField P p hp t x) (pointField P q hq t x) := by
  have ht : ∀ᶠ x in ae (liftMeasure P), ∀ i : Fin 3,
      bilinearTerm P B p q hp hq i t x =
        B (basisVector i) (component i (pointField P p hp t x) • pointField P q hq t x) :=
    Filter.eventually_all.mpr (fun i => bilinearTerm_ae P B p q hp hq i t)
  have hs := Lp.coeFn_fun_finsetSum (univ : Finset (Fin 3))
    (fun i => bilinearTerm P B p q hp hq i t)
  filter_upwards [hs,ht] with x hs ht
  change (∑ i : Fin 3, bilinearTerm P B p q hp hq i t) x = _
  rw [hs]
  exact (sum_congr rfl (fun i _ => ht i)).trans
    (bilinear_components B (pointField P p hp t x) (pointField P q hq t x))

/-- The reconstructed field agrees everywhere with the literal nonlinearity. -/
theorem pointField_bilinearProductPath (t : K) (x : LiftDomain P) :
    pointField P (bilinearProductPath P B p q hp hq)
      (bilinearProductPath_orbit P B p q hp hq) t x =
        B (pointField P p hp t x) (pointField P q hq t x) := by
  have he := Measure.eq_of_ae_eq
    ((pointField_ae P _ (bilinearProductPath_orbit P B p q hp hq) t).symm.trans
      (bilinearProductPath_ae P B p q hp hq t))
    (smoothField_continuous P _ (pointField_smooth P _ _ t))
    ((B.continuous.comp (smoothField_continuous P _ (pointField_smooth P p hp t))).clm_apply
      (smoothField_continuous P _ (pointField_smooth P q hq t)))
  exact congrFun he x

end EulerCylinderPathProduct
