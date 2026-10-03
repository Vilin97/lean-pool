/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Flow.InverseC1
public import Mathlib.Analysis.Calculus.MeanValue

/-! The determinant evolution of the two-dimensional variational flow. -/

@[expose] public section

open Homogenization
open scoped ContDiff

namespace AVenhance.Infra.Flow

/-- First coordinate basis vector used in the two-dimensional Liouville calculation. -/
def Liouville.flowBasis0 : Vec 2 := Pi.single 0 1
/-- Second coordinate basis vector used in the two-dimensional Liouville calculation. -/
def Liouville.flowBasis1 : Vec 2 := Pi.single 1 1

theorem Liouville.linearMap_apply_two (A : Vec 2 →L[ℝ] Vec 2) (v : Vec 2) (i : Fin 2) :
    A v i = A Liouville.flowBasis0 i * v 0 + A Liouville.flowBasis1 i * v 1 := by
  have hv : v = v 0 • Liouville.flowBasis0 + v 1 • Liouville.flowBasis1 := by
    ext j
    fin_cases j <;> simp [Liouville.flowBasis0, Liouville.flowBasis1]
  rw [hv, map_add, map_smul, map_smul]
  change v 0 * A Liouville.flowBasis0 i + v 1 * A Liouville.flowBasis1 i =
    A Liouville.flowBasis0 i * (v 0 * Liouville.flowBasis0 0 + v 1 * Liouville.flowBasis1 0) +
      A Liouville.flowBasis1 i * (v 0 * Liouville.flowBasis0 1 + v 1 * Liouville.flowBasis1 1)
  simp [Liouville.flowBasis0, Liouville.flowBasis1]
  ring

/-- The divergence of a spatial vector field is the trace of its spatial
Fréchet derivative. -/
noncomputable def spatialDivergence
    (b : ℝ → Vec 2 → Vec 2) (t : ℝ) (x : Vec 2) : ℝ :=
  jointSpatialFDeriv b t x Liouville.flowBasis0 0 +
    jointSpatialFDeriv b t x Liouville.flowBasis1 1

/-- The determinant of the spatial Fréchet derivative of a two-dimensional
flow map, written in the canonical coordinate basis. -/
noncomputable def flowSpatialJacobianDet
    (X : ℝ → Vec 2 → ℝ → Vec 2) (t : ℝ) (x : Vec 2) (s : ℝ) : ℝ :=
  let J := fderiv ℝ (fun y => X t y s) x
  J Liouville.flowBasis0 0 * J Liouville.flowBasis1 1 - J Liouville.flowBasis1 0 * J
      Liouville.flowBasis0 1

theorem Liouville.continuousLinearMap_det_two (J : Vec 2 →L[ℝ] Vec 2) :
    J.det = J Liouville.flowBasis0 0 * J Liouville.flowBasis1 1 - J Liouville.flowBasis1 0 * J
        Liouville.flowBasis0 1 := by
  change LinearMap.det J.toLinearMap = _
  rw [← LinearMap.det_toMatrix' J.toLinearMap, Matrix.det_fin_two]
  simp [LinearMap.toMatrix'_apply, Liouville.flowBasis0, Liouville.flowBasis1]

/-- The explicit coordinate expression above is Mathlib's determinant on the
Fréchet derivative. -/
theorem flowSpatialJacobianDet_eq_fderiv_det
    (X : ℝ → Vec 2 → ℝ → Vec 2) (t : ℝ) (x : Vec 2) (s : ℝ) :
    flowSpatialJacobianDet X t x s = (fderiv ℝ (fun y => X t y s) x).det := by
  exact (Liouville.continuousLinearMap_det_two _).symm

/-- Under the divergence-free condition, the determinant of the variational
flow stays equal to one. The variational solution is the same unique system
already characterized as the spatial derivative of the flow. -/
theorem exists_flow_liouville_determinant
    {b : ℝ → Vec 2 → Vec 2} (hb : SmoothPeriodicField b)
    {X : ℝ → Vec 2 → ℝ → Vec 2} (hX : AVenhance.IsFlow b X)
    (x : Vec 2) (s : ℝ)
    (hdiv : ∀ r, spatialDivergence b r (X r x s) = 0) :
    ∃ V : ℝ → Vec 2 → ℝ → Vec 2,
      AVenhance.IsFlow (linearizedFieldAlongFlow b X x s) V ∧
      ∀ t,
        (V t Liouville.flowBasis0 s 0 * V t Liouville.flowBasis1 s 1 -
          V t Liouville.flowBasis1 s 0 * V t Liouville.flowBasis0 s 1) = 1 := by
  obtain ⟨V, hV, _⟩ := existsUnique_flow_variationalEquation hb hX x s
  let A : ℝ → Vec 2 →L[ℝ] Vec 2 :=
    fun r => jointSpatialFDeriv b r (X r x s)
  let a : ℝ → ℝ := fun r => V r Liouville.flowBasis0 s 0
  let b₁ : ℝ → ℝ := fun r => V r Liouville.flowBasis1 s 0
  let c : ℝ → ℝ := fun r => V r Liouville.flowBasis0 s 1
  let d : ℝ → ℝ := fun r => V r Liouville.flowBasis1 s 1
  let a₀₀ : ℝ → ℝ := fun r => A r Liouville.flowBasis0 0
  let a₀₁ : ℝ → ℝ := fun r => A r Liouville.flowBasis1 0
  let a₁₀ : ℝ → ℝ := fun r => A r Liouville.flowBasis0 1
  let a₁₁ : ℝ → ℝ := fun r => A r Liouville.flowBasis1 1
  let jacDet : ℝ → ℝ := fun r => a r * d r - b₁ r * c r
  have ha (r : ℝ) : HasDerivAt a (a₀₀ r * a r + a₀₁ r * c r) r := by
    have hv : HasDerivAt (fun q => V q Liouville.flowBasis0 s)
        (A r (V r Liouville.flowBasis0 s)) r := by
      simpa [A, linearizedFieldAlongFlow] using hV.2 Liouville.flowBasis0 s r
    have hcoord := (hasDerivAt_pi.mp hv) 0
    have hrepr : A r (V r Liouville.flowBasis0 s) 0 =
        a₀₀ r * a r + a₀₁ r * c r := by
      simpa [a₀₀, a₀₁, a, c, A] using
        Liouville.linearMap_apply_two (A r) (V r Liouville.flowBasis0 s) 0
    rw [← hrepr]
    exact hcoord
  have hb₁ (r : ℝ) : HasDerivAt b₁ (a₀₀ r * b₁ r + a₀₁ r * d r) r := by
    have hv : HasDerivAt (fun q => V q Liouville.flowBasis1 s)
        (A r (V r Liouville.flowBasis1 s)) r := by
      simpa [A, linearizedFieldAlongFlow] using hV.2 Liouville.flowBasis1 s r
    have hcoord := (hasDerivAt_pi.mp hv) 0
    have hrepr : A r (V r Liouville.flowBasis1 s) 0 =
        a₀₀ r * b₁ r + a₀₁ r * d r := by
      simpa [a₀₀, a₀₁, b₁, d, A] using
        Liouville.linearMap_apply_two (A r) (V r Liouville.flowBasis1 s) 0
    rw [← hrepr]
    exact hcoord
  have hc (r : ℝ) : HasDerivAt c (a₁₀ r * a r + a₁₁ r * c r) r := by
    have hv : HasDerivAt (fun q => V q Liouville.flowBasis0 s)
        (A r (V r Liouville.flowBasis0 s)) r := by
      simpa [A, linearizedFieldAlongFlow] using hV.2 Liouville.flowBasis0 s r
    have hcoord := (hasDerivAt_pi.mp hv) 1
    have hrepr : A r (V r Liouville.flowBasis0 s) 1 =
        a₁₀ r * a r + a₁₁ r * c r := by
      simpa [a₁₀, a₁₁, a, c, A] using
        Liouville.linearMap_apply_two (A r) (V r Liouville.flowBasis0 s) 1
    rw [← hrepr]
    exact hcoord
  have hd (r : ℝ) : HasDerivAt d (a₁₀ r * b₁ r + a₁₁ r * d r) r := by
    have hv : HasDerivAt (fun q => V q Liouville.flowBasis1 s)
        (A r (V r Liouville.flowBasis1 s)) r := by
      simpa [A, linearizedFieldAlongFlow] using hV.2 Liouville.flowBasis1 s r
    have hcoord := (hasDerivAt_pi.mp hv) 1
    have hrepr : A r (V r Liouville.flowBasis1 s) 1 =
        a₁₀ r * b₁ r + a₁₁ r * d r := by
      simpa [a₁₀, a₁₁, b₁, d, A] using
        Liouville.linearMap_apply_two (A r) (V r Liouville.flowBasis1 s) 1
    rw [← hrepr]
    exact hcoord
  have hdet (r : ℝ) : HasDerivAt jacDet
      ((a₀₀ r + a₁₁ r) * jacDet r) r := by
    have hprod := (ha r).mul (hd r)
    have hprod' := (hb₁ r).mul (hc r)
    have hsub := hprod.sub hprod'
    convert hsub using 1
    simp only [jacDet]
    ring
  have hjacDeriv (r : ℝ) : deriv jacDet r = 0 := by
    rw [(hdet r).deriv]
    have htrace : a₀₀ r + a₁₁ r = spatialDivergence b r (X r x s) := by
      rfl
    rw [htrace, hdiv r]
    ring
  have hjacDiff : Differentiable ℝ jacDet := fun r => (hdet r).differentiableAt
  have hjacConst : ∀ q, jacDet q = jacDet s := by
    intro q
    exact is_const_of_deriv_eq_zero hjacDiff hjacDeriv q s
  have hjacStart : jacDet s = 1 := by
    simp [jacDet, a, b₁, c, d, hV.1, Liouville.flowBasis0, Liouville.flowBasis1]
  refine ⟨V, hV, ?_⟩
  intro t
  change jacDet t = 1
  rw [hjacConst t, hjacStart]

/-- A divergence-free smooth field has unit spatial Jacobian determinant at
every point and every pair of times. -/
theorem flow_spatial_jacobian_det_eq_one_of_divergence_free
    {b : ℝ → Vec 2 → Vec 2} (hb : SmoothPeriodicField b)
    {X : ℝ → Vec 2 → ℝ → Vec 2} (hX : AVenhance.IsFlow b X)
    (hdiv : ∀ t x, spatialDivergence b t x = 0)
    (x : Vec 2) (s t : ℝ) : (fderiv ℝ (fun y => X t y s) x).det = 1 := by
  obtain ⟨V, hV, hdet⟩ := exists_flow_liouville_determinant hb hX x s
    (fun r => hdiv r (X r x s))
  obtain ⟨Vd, Jd, hVd, hJd, hD⟩ :=
    exists_flow_hasFDerivAt_spatial hb hX x s t
  obtain ⟨_, _, hUnique⟩ := existsUnique_flow_variationalEquation hb hX x s
  have hVdEq : Vd = V := (hUnique Vd hVd).trans (hUnique V hV).symm
  rw [← flowSpatialJacobianDet_eq_fderiv_det]
  change
    (fderiv ℝ (fun y => X t y s) x Liouville.flowBasis0 0 *
      fderiv ℝ (fun y => X t y s) x Liouville.flowBasis1 1 -
      fderiv ℝ (fun y => X t y s) x Liouville.flowBasis1 0 *
      fderiv ℝ (fun y => X t y s) x Liouville.flowBasis0 1) = 1
  rw [hD.fderiv, hJd Liouville.flowBasis0, hJd Liouville.flowBasis1, hVdEq]
  exact hdet t

end AVenhance.Infra.Flow
