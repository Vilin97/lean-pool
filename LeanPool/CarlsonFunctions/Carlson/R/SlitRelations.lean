/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/

/- Copyright (c) 2026 Bastiaan J Braams. All rights reserved. -/
module

public import LeanPool.CarlsonFunctions.Carlson.R.SlitJointAnalytic
public import LeanPool.CarlsonFunctions.Carlson.R.Relations

/-! # Associated R-relations on the full slit domain -/

open Complex MeasureTheory ProbabilityTheory Filter Set
open scoped Classical Topology
@[expose] public noncomputable section
namespace DirichletTransform
variable {ι : Type*} [Fintype ι]

/-- The parameter-raising identity on the full slit domain, without dividing by
the exponent or total parameter. -/
theorem regCarlsonRSlit_eq_addDirichletUnit (t : ℂ) (b : ι → ℂ)
    {z : ι → ℂ} (hz : z ∈ carlsonRSlitDomain) (i : ι) :
    regCarlsonRSlit t b z =
      ((∑ j, b j) + t) * regCarlsonRSlit t (addDirichletUnit b i) z -
        t * z i * regCarlsonRSlit (t - 1) (addDirichletUnit b i) z := by
  have hright : AnalyticOnNhd ℂ (fun w =>
      ((∑ j, b j) + t) * regCarlsonRSlit t (addDirichletUnit b i) w -
        t * w i * regCarlsonRSlit (t - 1) (addDirichletUnit b i) w) carlsonRSlitDomain := by
    intro w hw
    exact (analyticAt_const.mul (analyticOnNhd_regCarlsonRSlit t _ w hw)).sub
      ((analyticAt_const.mul ((ContinuousLinearMap.proj i : (ι → ℂ) →L[ℂ] ℂ).analyticAt w)).mul
        (analyticOnNhd_regCarlsonRSlit (t - 1) _ w hw))
  apply eqOn_carlsonRSlitDomain_of_eqOn_rightHalfPlane
    (analyticOnNhd_regCarlsonRSlit t b) hright ?_ hz
  intro w hw
  simp_rw [regCarlsonRSlit_eq_continued _ _ hw]
  exact regCarlsonRContinued_eq_addDirichletUnit t b hw i

/-- Parameter lowering without dividing by the total parameter minus one. -/
theorem regCarlsonRSlit_sub_dirichletUnit (t : ℂ) (b : ι → ℂ)
    {z : ι → ℂ} (hz : z ∈ carlsonRSlitDomain) (i : ι) :
    regCarlsonRSlit t (b - Pi.single i 1) z =
      ((∑ j, b j) + t - 1) * regCarlsonRSlit t b z -
        t * z i * regCarlsonRSlit (t - 1) b z := by
  have hunit : addDirichletUnit (b - Pi.single i 1) i = b := by
    ext j
    by_cases hji : j = i
    · subst j
      simp [addDirichletUnit]
    · simp [addDirichletUnit, hji]
  have hsum : (∑ j, ((b - Pi.single i (1 : ℂ)) : ι → ℂ) j) = (∑ j, b j) - 1 := by
    simp [Pi.sub_apply, Finset.sum_sub_distrib]
  have h := regCarlsonRSlit_eq_addDirichletUnit t (b - Pi.single i 1) hz i
  rw [hunit, hsum] at h
  convert h using 1
  ring

/-- The backward-shift tangential relation, including equal indices and coincident nodes. -/
theorem regCarlsonRSlit_tangent_sub (t : ℂ) (b : ι → ℂ)
    {z : ι → ℂ} (hz : z ∈ carlsonRSlitDomain) (i j : ι) :
    (z i - z j) * (t * regCarlsonRSlit (t - 1) b z) =
      regCarlsonRSlit t (b - Pi.single j 1) z -
        regCarlsonRSlit t (b - Pi.single i 1) z := by
  rw [regCarlsonRSlit_sub_dirichletUnit t b hz j,
    regCarlsonRSlit_sub_dirichletUnit t b hz i]
  ring

/-- The parameter-raised tangential relation on the full slit domain. -/
theorem regCarlsonRSlit_tangent (t : ℂ) (b : ι → ℂ)
    {z : ι → ℂ} (hz : z ∈ carlsonRSlitDomain) (i j : ι) :
    (z i - z j) * (t *
      regCarlsonRSlit (t - 1) (addDirichletUnit (addDirichletUnit b j) i) z) =
      regCarlsonRSlit t (addDirichletUnit b i) z -
        regCarlsonRSlit t (addDirichletUnit b j) z := by
  by_cases hij : i = j
  · subst j; simp
  have h₁ : addDirichletUnit (addDirichletUnit b j) i - Pi.single j 1 =
      addDirichletUnit b i := by
    ext k
    by_cases hki : k = i <;> by_cases hkj : k = j <;>
      simp_all [addDirichletUnit]
  have h₂ : addDirichletUnit (addDirichletUnit b j) i - Pi.single i 1 =
      addDirichletUnit b j := by
    ext k
    by_cases hki : k = i <;> simp_all [addDirichletUnit]
  simpa only [h₁, h₂] using
    regCarlsonRSlit_tangent_sub t (addDirichletUnit (addDirichletUnit b j) i) hz i j

end DirichletTransform
