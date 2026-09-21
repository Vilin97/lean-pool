/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/

/- Copyright (c) 2026 Bastiaan J Braams. All rights reserved. -/
module

public import LeanPool.CarlsonFunctions.Carlson.L.Continuation
public import LeanPool.CarlsonFunctions.Carlson.R.SlitJointAnalytic

/-!
# Carlson's L-function on the full product slit plane

The exponent derivative of `regCarlsonRSlit` is jointly holomorphic in the exponent,
Dirichlet parameters, and slit-plane nodes. This completes the domain assertion of
Carlson (1987), (2.1), in regularized form. The original right-half-plane continuation
is retained and agrees with this extension. No equality with a principal-power simplex
integral is asserted for arbitrary slit-plane nodes.
-/

open Complex Filter Set
open scoped Topology
@[expose] public noncomputable section
namespace DirichletTransform
variable {ι : Type*} [Fintype ι]

/-- The entire regularized L-function, defined by differentiating R in its exponent.
Values outside the product slit plane are unspecified. -/
def regCarlsonLSlit (t : ℂ) (b z : ι → ℂ) : ℂ :=
  deriv (fun s => regCarlsonRSlit s b z) t

/-- The ordinary L-function on slit-plane nodes. At total-parameter Gamma poles,
this is only Lean's totalized expression, not a claimed finite value. -/
def carlsonLSlit (t : ℂ) (b z : ι → ℂ) : ℂ :=
  Gamma (∑ i, b i) * regCarlsonLSlit t b z

theorem hasDerivAt_regCarlsonRSlit_L (t : ℂ) (b : ι → ℂ) {z : ι → ℂ}
    (hz : z ∈ carlsonRSlitDomain) :
    HasDerivAt (fun s => regCarlsonRSlit s b z) (regCarlsonLSlit t b z) t :=
  (analyticAt_regCarlsonRSlit_comp analyticAt_id analyticAt_const analyticAt_const hz).differentiableAt.hasDerivAt

/-- Carlson (1987), (2.1): full joint holomorphy, with no parameter exceptions after
Gamma regularization. The coordinates are exponent, parameters, then nodes. -/
theorem analyticOnNhd_regCarlsonLSlit_joint :
    AnalyticOnNhd ℂ (fun p : Option (ι ⊕ ι) → ℂ =>
      regCarlsonLSlit (p none) (fun i => p (some (.inl i))) (fun i => p (some (.inr i))))
      {p | (fun i => p (some (.inr i))) ∈ carlsonRSlitDomain} := by
  have h := analyticOnNhd_regCarlsonRSlit_joint (ι := ι) |>.partialDeriv
    (isOpen_carlsonRSlitDomain.preimage (by fun_prop)) none
  have heq : SeveralComplexVariables.partialDeriv none
      (fun p : Option (ι ⊕ ι) → ℂ => regCarlsonRSlit (p none)
        (fun i => p (some (.inl i))) (fun i => p (some (.inr i)))) =
      (fun p => regCarlsonLSlit (p none)
        (fun i => p (some (.inl i))) (fun i => p (some (.inr i)))) := by
    funext p
    simp only [SeveralComplexVariables.partialDeriv, regCarlsonLSlit,
      Function.update_self, Function.update_of_ne (Option.some_ne_none _)]
  rwa [heq] at h

/-- Analytic substitutions in all arguments preserve analyticity on the slit domain. -/
theorem analyticAt_regCarlsonLSlit_comp
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {t : E → ℂ} {b z : E → ι → ℂ} {p : E}
    (ht : AnalyticAt ℂ t p) (hb : AnalyticAt ℂ b p) (hz : AnalyticAt ℂ z p)
    (hslit : z p ∈ carlsonRSlitDomain) :
    AnalyticAt ℂ (fun q => regCarlsonLSlit (t q) (b q) (z q)) p := by
  let f : E → Option (ι ⊕ ι) → ℂ := fun q k => k.elim (t q) (Sum.elim (b q) (z q))
  have hf : AnalyticAt ℂ f p := by
    apply analyticAt_pi_iff.mpr
    intro k
    cases k with
    | none => exact ht
    | some k =>
      cases k with
      | inl i => exact (analyticAt_pi_iff.mp hb) i
      | inr i => exact (analyticAt_pi_iff.mp hz) i
  exact (analyticOnNhd_regCarlsonLSlit_joint (f p) hslit).comp_of_eq hf rfl

theorem analyticOnNhd_regCarlsonLSlit (t : ℂ) (b : ι → ℂ) :
    AnalyticOnNhd ℂ (regCarlsonLSlit t b) carlsonRSlitDomain :=
  fun _ hz => analyticAt_regCarlsonLSlit_comp analyticAt_const analyticAt_const analyticAt_id hz

theorem analyticOnNhd_regCarlsonLSlit_exponent_parameters {z : ι → ℂ}
    (hz : z ∈ carlsonRSlitDomain) :
    AnalyticOnNhd ℂ (fun p : Option ι → ℂ =>
      regCarlsonLSlit (p none) (fun i => p (some i)) z) univ := by
  intro p _
  apply analyticAt_regCarlsonLSlit_comp _ _ analyticAt_const hz
  · exact (ContinuousLinearMap.proj none : (Option ι → ℂ) →L[ℂ] ℂ).analyticAt p
  · exact analyticAt_pi_iff.mpr fun i =>
      (ContinuousLinearMap.proj (some i) : (Option ι → ℂ) →L[ℂ] ℂ).analyticAt p

theorem analyticAt_carlsonLSlit_comp
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {t : E → ℂ} {b z : E → ι → ℂ} {p : E}
    (ht : AnalyticAt ℂ t p) (hb : AnalyticAt ℂ b p) (hz : AnalyticAt ℂ z p)
    (hslit : z p ∈ carlsonRSlitDomain) (hc : ∀ n : ℕ, (∑ i, b p i) ≠ -n) :
    AnalyticAt ℂ (fun q => carlsonLSlit (t q) (b q) (z q)) p := by
  have hsum : AnalyticAt ℂ (fun q => ∑ i, b q i) p :=
    Finset.analyticAt_fun_sum _ fun i _ => (analyticAt_pi_iff.mp hb) i
  have hrecip := (differentiable_one_div_Gamma.analyticAt (∑ i, b p i)).comp_of_eq hsum rfl
  have hgamma : AnalyticAt ℂ (fun q => Gamma (∑ i, b q i)) p := by
    have h := hrecip.inv (inv_ne_zero (Gamma_ne_zero hc))
    change AnalyticAt ℂ (fun q => ((Gamma (∑ i, b q i))⁻¹)⁻¹) p at h
    simpa only [inv_inv] using h
  exact hgamma.mul (analyticAt_regCarlsonLSlit_comp ht hb hz hslit)

theorem regCarlsonLSlit_eq_continued (t : ℂ) (b : ι → ℂ) {z : ι → ℂ}
    (hz : z ∈ carlsonRVariableDomain) :
    regCarlsonLSlit t b z = regCarlsonLContinued t z hz b := by
  unfold regCarlsonLSlit regCarlsonLContinued
  simp_rw [regCarlsonRSlit_eq_continued _ b hz]

theorem regCarlsonLSlit_eq_integral (t : ℂ) {b z : ι → ℂ}
    (hz : z ∈ carlsonRVariableDomain) (hb : b ∈ mvBetaConvergent) :
    regCarlsonLSlit t b z = regCarlsonLIntegral t b z := by
  rw [regCarlsonLSlit_eq_continued t b hz, regCarlsonLContinued_eq_integral t hz hb]

theorem carlsonLSlit_eq_continued (t : ℂ) (b : ι → ℂ) {z : ι → ℂ}
    (hz : z ∈ carlsonRVariableDomain) :
    carlsonLSlit t b z = carlsonLContinued t z hz b := by
  rw [carlsonLSlit, carlsonLContinued, regCarlsonLSlit_eq_continued t b hz]

theorem carlsonLSlit_eq_integral (t : ℂ) {b z : ι → ℂ}
    (hz : z ∈ carlsonRVariableDomain) (hb : b ∈ mvBetaConvergent) :
    carlsonLSlit t b z = carlsonLIntegral t b z := by
  rw [carlsonLSlit_eq_continued t b hz, carlsonLContinued_eq_integral t hz hb]

/-- The continuation is uniquely determined by its right-half-plane values. -/
theorem eqOn_regCarlsonLSlit_of_eq_continued {t : ℂ} {b : ι → ℂ} {F : (ι → ℂ) → ℂ}
    (hF : AnalyticOnNhd ℂ F carlsonRSlitDomain)
    (heq : ∀ z (hz : z ∈ carlsonRVariableDomain), F z = regCarlsonLContinued t z hz b) :
    EqOn F (regCarlsonLSlit t b) carlsonRSlitDomain :=
  eqOn_carlsonRSlitDomain_of_eqOn_rightHalfPlane hF (analyticOnNhd_regCarlsonLSlit t b)
    (fun z hz => (heq z hz).trans (regCarlsonLSlit_eq_continued t b hz).symm)

/-- Differentiating the ordinary R-function gives the ordinary L-function. -/
theorem hasDerivAt_carlsonRSlit_L (t : ℂ) (b : ι → ℂ) {z : ι → ℂ}
    (hz : z ∈ carlsonRSlitDomain) :
    HasDerivAt (fun s => carlsonRSlit s b z) (carlsonLSlit t b z) t :=
  (hasDerivAt_regCarlsonRSlit_L t b hz).const_mul (Gamma (∑ i, b i))

@[simp] theorem regCarlsonLSlit_empty [IsEmpty ι] (t : ℂ) (b : ι → ℂ)
    {z : ι → ℂ} (hz : z ∈ carlsonRSlitDomain) : regCarlsonLSlit t b z = 0 := by
  unfold regCarlsonLSlit
  simp_rw [regCarlsonRSlit_eq_zero_of_isEmpty _ b hz]
  exact deriv_const t 0

end DirichletTransform
