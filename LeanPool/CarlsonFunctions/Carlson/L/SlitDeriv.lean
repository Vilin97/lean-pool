/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/

/- Copyright (c) 2026 Bastiaan J Braams. All rights reserved. -/
module

public import LeanPool.CarlsonFunctions.Carlson.L.SlitRelations
public import LeanPool.CarlsonFunctions.Carlson.L.Deriv

/-!
# Node derivatives and translations on the slit domain

The node derivative formula (3.5) of Carlson (1987) extends from the native integral
to all complex Dirichlet parameters and all slit-plane nodes. Joint analyticity is
essential: it makes the node derivative analytic in the parameters, so permanence
of functional relations applies. Summation gives (2.8)–(2.10), including scalar
translation, with the inhomogeneous R-term and without convergence restrictions.
-/

open Complex Filter Set
open scoped Topology
@[expose] public noncomputable section
namespace DirichletTransform
variable {ι : Type*} [Fintype ι]

open scoped Classical in
/-- A node derivative is jointly holomorphic in all arguments of L. -/
theorem analyticOnNhd_carlsonPartialDeriv_regCarlsonLSlit_joint (i : ι) :
    AnalyticOnNhd ℂ (fun p : Option (ι ⊕ ι) → ℂ =>
      carlsonPartialDeriv i (regCarlsonLSlit (p none) (fun j => p (some (.inl j))))
        (fun j => p (some (.inr j))))
      {p | (fun j => p (some (.inr j))) ∈ carlsonRSlitDomain} := by
  have h := analyticOnNhd_regCarlsonLSlit_joint (ι := ι) |>.partialDeriv
    (isOpen_carlsonRSlitDomain.preimage (by fun_prop)) (some (Sum.inr i))
  have heq : SeveralComplexVariables.partialDeriv (some (Sum.inr i))
      (fun p : Option (ι ⊕ ι) → ℂ => regCarlsonLSlit (p none)
        (fun j => p (some (.inl j))) (fun j => p (some (.inr j)))) =
      (fun p => carlsonPartialDeriv i (regCarlsonLSlit (p none)
        (fun j => p (some (.inl j)))) (fun j => p (some (.inr j)))) := by
    funext p
    unfold SeveralComplexVariables.partialDeriv carlsonPartialDeriv
    congr 1
    funext w
    simp [Function.update_apply]
    congr 1
    funext j
    simp [Function.update_apply]
  rwa [heq] at h

theorem analyticAt_carlsonPartialDeriv_regCarlsonLSlit_comp
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {t : E → ℂ} {b z : E → ι → ℂ} {p : E}
    (ht : AnalyticAt ℂ t p) (hb : AnalyticAt ℂ b p) (hz : AnalyticAt ℂ z p)
    (hslit : z p ∈ carlsonRSlitDomain) (i : ι) :
    AnalyticAt ℂ (fun q => carlsonPartialDeriv i (regCarlsonLSlit (t q) (b q)) (z q)) p := by
  let f : E → Option (ι ⊕ ι) → ℂ := fun q k => k.elim (t q) (Sum.elim (b q) (z q))
  have hf : AnalyticAt ℂ f p := by
    apply analyticAt_pi_iff.mpr
    intro k
    cases k with
    | none => exact ht
    | some k =>
      cases k with
      | inl j => exact (analyticAt_pi_iff.mp hb) j
      | inr j => exact (analyticAt_pi_iff.mp hz) j
  exact (analyticOnNhd_carlsonPartialDeriv_regCarlsonLSlit_joint i (f p) hslit).comp_of_eq hf rfl

open scoped Classical in
private theorem partialDeriv_regCarlsonLSlit_of_right (t : ℂ) (b : ι → ℂ)
    {z : ι → ℂ} (hz : z ∈ carlsonRVariableDomain) (i : ι) :
    carlsonPartialDeriv i (regCarlsonLSlit t b) z =
      b i * (t * regCarlsonLSlit (t - 1) (addDirichletUnit b i) z +
        regCarlsonRSlit (t - 1) (addDirichletUnit b i) z) := by
  have hz' := carlsonRVariableDomain_subset_slitDomain hz
  have hleft : AnalyticOnNhd ℂ (fun b => carlsonPartialDeriv i (regCarlsonLSlit t b) z) univ :=
    fun _ _ => analyticAt_carlsonPartialDeriv_regCarlsonLSlit_comp
      analyticAt_const analyticAt_id analyticAt_const hz' i
  have hright : AnalyticOnNhd ℂ (fun b : ι → ℂ =>
      b i * (t * regCarlsonLSlit (t - 1) (addDirichletUnit b i) z +
        regCarlsonRSlit (t - 1) (addDirichletUnit b i) z)) univ := by
    intro b _
    have hshift : AnalyticAt ℂ (fun b : ι → ℂ => addDirichletUnit b i) b := by
      apply analyticAt_pi_iff.mpr
      intro j
      by_cases hji : j = i
      · subst j
        simpa only [addDirichletUnit, Function.update_self] using!
          ((ContinuousLinearMap.proj i : (ι → ℂ) →L[ℂ] ℂ).analyticAt b).add analyticAt_const
      · simpa only [addDirichletUnit, Function.update_of_ne hji] using!
          (ContinuousLinearMap.proj j : (ι → ℂ) →L[ℂ] ℂ).analyticAt b
    exact ((ContinuousLinearMap.proj i : (ι → ℂ) →L[ℂ] ℂ).analyticAt b).mul
      ((analyticAt_const.mul (analyticAt_regCarlsonLSlit_comp
        analyticAt_const hshift analyticAt_const hz')).add
        (analyticAt_regCarlsonRSlit_comp analyticAt_const hshift analyticAt_const hz'))
  apply congrFun (analyticOnNhd_eq_of_eqOn_mvBetaConvergent hleft hright ?_) b
  intro b hb
  have hevent : regCarlsonLSlit t b =ᶠ[nhds z] regCarlsonLIntegral t b := by
    filter_upwards [isOpen_carlsonRVariableDomain.mem_nhds hz] with w hw
    exact regCarlsonLSlit_eq_integral t hw hb
  have hD := SeveralComplexVariables.partialDeriv_congr hevent i
  change carlsonPartialDeriv i (regCarlsonLSlit t b) z =
    carlsonPartialDeriv i (regCarlsonLIntegral t b) z at hD
  change carlsonPartialDeriv i (regCarlsonLSlit t b) z =
    b i * (t * regCarlsonLSlit (t - 1) (addDirichletUnit b i) z +
      regCarlsonRSlit (t - 1) (addDirichletUnit b i) z)
  rw [hD, carlsonPartialDeriv_regCarlsonLIntegral t hb hz,
    regCarlsonLSlit_eq_integral _ hz (addDirichletUnit_mem_mvBetaConvergent hb i),
    regCarlsonRSlit_eq_integral _ (addDirichletUnit_mem_mvBetaConvergent hb i) hz]

/-- Carlson (1987), (3.5), on the entire parameter domain and the full node slit domain. -/
theorem carlsonPartialDeriv_regCarlsonLSlit (t : ℂ) (b : ι → ℂ)
    {z : ι → ℂ} (hz : z ∈ carlsonRSlitDomain) (i : ι) :
    carlsonPartialDeriv i (regCarlsonLSlit t b) z =
      b i * (t * regCarlsonLSlit (t - 1) (addDirichletUnit b i) z +
        regCarlsonRSlit (t - 1) (addDirichletUnit b i) z) := by
  have hleft : AnalyticOnNhd ℂ (carlsonPartialDeriv i (regCarlsonLSlit t b)) carlsonRSlitDomain :=
    (analyticOnNhd_regCarlsonLSlit t b).partialDeriv isOpen_carlsonRSlitDomain i
  have hright : AnalyticOnNhd ℂ (fun w =>
      b i * (t * regCarlsonLSlit (t - 1) (addDirichletUnit b i) w +
        regCarlsonRSlit (t - 1) (addDirichletUnit b i) w)) carlsonRSlitDomain :=
    analyticOnNhd_const.mul ((analyticOnNhd_const.mul (analyticOnNhd_regCarlsonLSlit (t - 1) _)).add
      (analyticOnNhd_regCarlsonRSlit (t - 1) _))
  exact eqOn_carlsonRSlitDomain_of_eqOn_rightHalfPlane hleft hright
    (fun _ hw => partialDeriv_regCarlsonLSlit_of_right t b hw i) hz

/-- Equation (2.9), the translation differential-difference identity. -/
theorem sum_carlsonPartialDeriv_regCarlsonLSlit (t : ℂ) (b : ι → ℂ)
    {z : ι → ℂ} (hz : z ∈ carlsonRSlitDomain) :
    ∑ i, carlsonPartialDeriv i (regCarlsonLSlit t b) z =
      t * regCarlsonLSlit (t - 1) b z + regCarlsonRSlit (t - 1) b z := by
  simp_rw [carlsonPartialDeriv_regCarlsonLSlit t b hz]
  rw [regCarlsonLSlit_eq_sum_addDirichletUnit (t - 1) b hz,
    regCarlsonRSlit_eq_sum_addDirichletUnit (t - 1) b hz,
    Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  ring

/-- Equation (2.8): the Euler differential identity includes the R-term. -/
theorem sum_mul_carlsonPartialDeriv_regCarlsonLSlit (t : ℂ) (b : ι → ℂ)
    {z : ι → ℂ} (hz : z ∈ carlsonRSlitDomain) :
    ∑ i, z i * carlsonPartialDeriv i (regCarlsonLSlit t b) z =
      t * regCarlsonLSlit t b z + regCarlsonRSlit t b z := by
  have hL := regCarlsonLSlit_add_one_eq_sum_mul_addDirichletUnit (t - 1) b hz
  have hR := regCarlsonRSlit_add_one_eq_sum_mul_addDirichletUnit (t - 1) b hz
  simp only [sub_add_cancel] at hL hR
  simp_rw [carlsonPartialDeriv_regCarlsonLSlit t b hz]
  rw [hL, hR, Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  ring

/-- Equation (2.10): scalar translation, locally wherever every translated node is in
the slit plane. No global translation or branch-crossing assumption is needed. -/
theorem hasDerivAt_regCarlsonLSlit_translate (t : ℂ) (b z : ι → ℂ) {x : ℂ}
    (hx : (fun i => x + z i) ∈ carlsonRSlitDomain) :
    HasDerivAt (fun y => regCarlsonLSlit t b (fun i => y + z i))
      (t * regCarlsonLSlit (t - 1) b (fun i => x + z i) +
        regCarlsonRSlit (t - 1) b (fun i => x + z i)) x := by
  have hd := (analyticOnNhd_regCarlsonLSlit t b _ hx).differentiableAt
  have hvec : HasDerivAt (fun y : ℂ => fun i => y + z i) (fun _ => 1) x :=
    hasDerivAt_pi.mpr fun i => (hasDerivAt_id x).add_const (z i)
  have h := hd.hasFDerivAt.comp_hasDerivAt x hvec
  apply h.congr_deriv
  rw [SeveralComplexVariables.fderiv_eq_sum_partialDeriv hd]
  simpa only [one_smul, ← carlsonPartialDeriv_eq_partialDeriv] using
    sum_carlsonPartialDeriv_regCarlsonLSlit t b hx

/-- Carlson (1987), (3.6), including the inhomogeneous R-term and all parameter values. -/
theorem mul_carlsonPartialDeriv_add_mul_regCarlsonLSlit (t : ℂ) (b : ι → ℂ)
    {z : ι → ℂ} (hz : z ∈ carlsonRSlitDomain) (i : ι) :
    z i * carlsonPartialDeriv i (regCarlsonLSlit t b) z + b i * regCarlsonLSlit t b z =
      b i * ((∑ j, b j) + t) * regCarlsonLSlit t (addDirichletUnit b i) z +
        b i * regCarlsonRSlit t (addDirichletUnit b i) z := by
  rw [carlsonPartialDeriv_regCarlsonLSlit t b hz]
  linear_combination b i * regCarlsonLSlit_eq_addDirichletUnit t b hz i

end DirichletTransform
