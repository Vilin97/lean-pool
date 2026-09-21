/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/

/- Copyright (c) 2026 Bastiaan J Braams. All rights reserved. -/
module

public import LeanPool.CarlsonFunctions.Carlson.R.SingleIntegral.Continuation
public import LeanPool.CarlsonFunctions.Carlson.R.Relations

/-!
# Continuation of Carlson's R-function in the nodes

For every complex exponent and every complex Dirichlet parameter vector, the regularized
`R`-function has a unique holomorphic extension to the product slit plane. The construction
starts with Carlson's beta-weighted single integral (Theorem 6.8-1). Two division-free
associated relations move any parameters into its convergence strip. In particular, no
exceptional parameter hyperplanes are removed by this construction.

Uniqueness is on the slit domain, not on the arbitrary values of a total Lean function
outside that domain. This file does not assert the contour representation (6.8-7).
-/

open Complex Filter
open scoped Classical Topology
@[expose] public noncomputable section
namespace DirichletTransform
variable {ι : Type*} [Fintype ι]

/-- A holomorphic extension in the nodes of the existing parameter continuation. -/
def IsCarlsonRSlitContinuation (t : ℂ) (b : ι → ℂ) (F : (ι → ℂ) → ℂ) : Prop :=
  AnalyticOnNhd ℂ F carlsonRSlitDomain ∧
    ∀ z (hz : z ∈ carlsonRVariableDomain), F z = regCarlsonRContinued t z hz b

/-- Agreement on the right half-plane determines a holomorphic function on the product
slit plane uniquely. This is the node-variable permanence principle. -/
theorem eqOn_carlsonRSlitDomain_of_eqOn_rightHalfPlane
    {F G : (ι → ℂ) → ℂ} (hF : AnalyticOnNhd ℂ F carlsonRSlitDomain)
    (hG : AnalyticOnNhd ℂ G carlsonRSlitDomain)
    (hFG : Set.EqOn F G carlsonRVariableDomain) : Set.EqOn F G carlsonRSlitDomain := by
  have hone : (fun _ : ι => (1 : ℂ)) ∈ carlsonRVariableDomain :=
    fun _ => by simp [carlsonRightHalfPlane]
  apply hF.eqOn_of_preconnected_of_eventuallyEq hG isPreconnected_carlsonRSlitDomain
    one_mem_carlsonRSlitDomain
  filter_upwards [isOpen_carlsonRVariableDomain.mem_nhds hone] with z hz
  exact hFG hz

theorem IsCarlsonRSlitContinuation.eqOn {t : ℂ} {b : ι → ℂ} {F G : (ι → ℂ) → ℂ}
    (hF : IsCarlsonRSlitContinuation t b F) (hG : IsCarlsonRSlitContinuation t b G) :
    Set.EqOn F G carlsonRSlitDomain :=
  eqOn_carlsonRSlitDomain_of_eqOn_rightHalfPlane hF.1 hG.1
    (fun z hz => (hF.2 z hz).trans (hG.2 z hz).symm)

private theorem exists_slitContinuation_of_strip (t : ℂ) (b : ι → ℂ)
    (ht : t.re < 0) (hb : 0 < ((∑ i, b i) + t).re) :
    ∃ F, IsCarlsonRSlitContinuation t b F := by
  let a := -t
  let a' := (∑ i, b i) + t
  have ha : 0 < a.re := by simpa [a] using neg_pos.mpr ht
  have ha' : 0 < a'.re := hb
  refine ⟨fun z => carlsonRUnitIntervalIntegral a a' b z / (Gamma a * Gamma a'),
    (analyticOnNhd_carlsonRUnitIntervalIntegral_slit a a' b ha ha').div_const, ?_⟩
  intro z hz
  dsimp only
  rw [carlsonRUnitIntervalIntegral_eq_gamma_mul_continued ha ha'
    (show a + a' = ∑ i, b i by dsimp [a, a']; ring) hz]
  have hG := mul_ne_zero (Gamma_ne_zero_of_re_pos ha) (Gamma_ne_zero_of_re_pos ha')
  rw [mul_comm, mul_div_cancel_right₀ _ hG]
  simp [a]

private theorem exists_slitContinuation_raise_b (t : ℂ) (b : ι → ℂ)
    (h : ∀ i, ∃ F, IsCarlsonRSlitContinuation t (addDirichletUnit b i) F) :
    ∃ F, IsCarlsonRSlitContinuation t b F := by
  choose F hF using h
  refine ⟨fun z => ∑ i, b i * F i z, ?_, ?_⟩
  · intro z hz
    exact Finset.analyticAt_fun_sum _ fun i _ => analyticAt_const.mul (hF i |>.1 z hz)
  · intro z hz
    simp_rw [show ∀ i, F i z = regCarlsonRContinued t z hz (addDirichletUnit b i)
      from fun i => (hF i).2 z hz]
    exact (regCarlsonRContinued_eq_sum_addDirichletUnit t b hz).symm

private theorem exists_slitContinuation_raise_t (t : ℂ) (b : ι → ℂ)
    (h : ∀ i, ∃ F, IsCarlsonRSlitContinuation (t - 1) (addDirichletUnit b i) F) :
    ∃ F, IsCarlsonRSlitContinuation t b F := by
  choose F hF using h
  refine ⟨fun z => ∑ i, b i * z i * F i z, ?_, ?_⟩
  · intro z hz
    exact Finset.analyticAt_fun_sum _ fun i _ =>
      (analyticAt_const.mul ((ContinuousLinearMap.proj i : (ι → ℂ) →L[ℂ] ℂ).analyticAt z)).mul
        ((hF i).1 z hz)
  · intro z hz
    simp_rw [show ∀ i, F i z = regCarlsonRContinued (t - 1) z hz (addDirichletUnit b i)
      from fun i => (hF i).2 z hz]
    simpa using (regCarlsonRContinued_add_one_eq_sum_mul_addDirichletUnit (t - 1) b hz).symm

/-- Every complex exponent and parameter vector admits a holomorphic extension in the nodes.
The proof works for empty index types as well: the associated sums are then empty. -/
theorem exists_carlsonRSlitContinuation (t : ℂ) (b : ι → ℂ) :
    ∃ F, IsCarlsonRSlitContinuation t b F := by
  have hshift (n m : ℕ) : ∀ (t : ℂ) (b : ι → ℂ),
      t.re < n → 0 < ((∑ i, b i) + t).re + m →
      ∃ F, IsCarlsonRSlitContinuation t b F := by
    induction n with
    | zero =>
      induction m with
      | zero =>
        intro t b ht hb
        exact exists_slitContinuation_of_strip t b (by simpa using ht) (by simpa using hb)
      | succ m ih =>
        intro t b ht hb
        apply exists_slitContinuation_raise_b t b
        intro i
        apply ih t (addDirichletUnit b i) ht
        simp only [sum_addDirichletUnit, add_re, one_re, Nat.cast_add, Nat.cast_one] at *
        linarith
    | succ n ih =>
      intro t b ht hb
      apply exists_slitContinuation_raise_t t b
      intro i
      apply ih (t - 1) (addDirichletUnit b i)
      · simp only [sub_re, one_re, Nat.cast_add, Nat.cast_one] at *
        linarith
      · simp only [sum_addDirichletUnit, add_re, sub_re, one_re] at *
        linarith
  obtain ⟨n, hn⟩ := exists_nat_gt t.re
  obtain ⟨m, hm⟩ := exists_nat_gt (-((∑ i, b i) + t).re)
  exact hshift n m t b hn (by linarith)

/-- The regularized Carlson function on the full product slit plane, for arbitrary complex
`t` and `b`. Values outside `carlsonRSlitDomain` are unspecified. -/
def regCarlsonRSlit (t : ℂ) (b z : ι → ℂ) : ℂ :=
  (exists_carlsonRSlitContinuation t b).choose z

theorem isCarlsonRSlitContinuation_regCarlsonRSlit (t : ℂ) (b : ι → ℂ) :
    IsCarlsonRSlitContinuation t b (regCarlsonRSlit t b) :=
  (exists_carlsonRSlitContinuation t b).choose_spec

theorem analyticOnNhd_regCarlsonRSlit (t : ℂ) (b : ι → ℂ) :
    AnalyticOnNhd ℂ (regCarlsonRSlit t b) carlsonRSlitDomain :=
  (isCarlsonRSlitContinuation_regCarlsonRSlit t b).1

theorem regCarlsonRSlit_eq_continued (t : ℂ) (b : ι → ℂ) {z : ι → ℂ}
    (hz : z ∈ carlsonRVariableDomain) :
    regCarlsonRSlit t b z = regCarlsonRContinued t z hz b :=
  (isCarlsonRSlitContinuation_regCarlsonRSlit t b).2 z hz

/-- The ordinary Carlson function on the slit domain, away from poles of the total-parameter
Gamma factor. At those poles this definition is only Lean's totalized expression. -/
def carlsonRSlit (t : ℂ) (b z : ι → ℂ) : ℂ :=
  Gamma (∑ i, b i) * regCarlsonRSlit t b z

theorem analyticOnNhd_carlsonRSlit (t : ℂ) (b : ι → ℂ) :
    AnalyticOnNhd ℂ (carlsonRSlit t b) carlsonRSlitDomain :=
  fun z hz => analyticAt_const.mul (analyticOnNhd_regCarlsonRSlit t b z hz)

/-- The slit continuation agrees with the native simplex integral wherever the latter
was already used to define Carlson's principal branch. -/
theorem regCarlsonRSlit_eq_integral (t : ℂ) {b z : ι → ℂ}
    (hb : b ∈ mvBetaConvergent) (hz : z ∈ carlsonRVariableDomain) :
    regCarlsonRSlit t b z = regCarlsonRIntegral t b z := by
  rw [regCarlsonRSlit_eq_continued t b hz, regCarlsonRContinued_eq_integral t hz hb]

theorem carlsonRSlit_eq_integral (t : ℂ) {b z : ι → ℂ}
    (hb : b ∈ mvBetaConvergent) (hz : z ∈ carlsonRVariableDomain) :
    carlsonRSlit t b z = carlsonRIntegral t b z := by
  rw [carlsonRSlit, carlsonRIntegral, regCarlsonRSlit_eq_integral t hb hz]

/-- Carlson's single-integral representation now holds on the full product slit plane. -/
theorem carlsonRUnitIntervalIntegral_eq_gamma_mul_slit
    {a a' : ℂ} {b z : ι → ℂ} (ha : 0 < a.re) (ha' : 0 < a'.re)
    (hsum : a + a' = ∑ i, b i) (hz : z ∈ carlsonRSlitDomain) :
    carlsonRUnitIntervalIntegral a a' b z =
      (Gamma a * Gamma a') * regCarlsonRSlit (-a) b z := by
  apply eqOn_carlsonRSlitDomain_of_eqOn_rightHalfPlane
    (analyticOnNhd_carlsonRUnitIntervalIntegral_slit a a' b ha ha')
    (fun z hz => analyticAt_const.mul (analyticOnNhd_regCarlsonRSlit (-a) b z hz)) ?_ hz
  intro w hw
  change carlsonRUnitIntervalIntegral a a' b w =
    (Gamma a * Gamma a') * regCarlsonRSlit (-a) b w
  rw [regCarlsonRSlit_eq_continued (-a) b hw]
  exact carlsonRUnitIntervalIntegral_eq_gamma_mul_continued ha ha' hsum hw

/-- The first associated relation on the full node domain, without parameter exceptions. -/
theorem regCarlsonRSlit_eq_sum_addDirichletUnit (t : ℂ) (b : ι → ℂ)
    {z : ι → ℂ} (hz : z ∈ carlsonRSlitDomain) :
    regCarlsonRSlit t b z = ∑ i, b i * regCarlsonRSlit t (addDirichletUnit b i) z := by
  apply eqOn_carlsonRSlitDomain_of_eqOn_rightHalfPlane
    (analyticOnNhd_regCarlsonRSlit t b) (fun w hw =>
      Finset.analyticAt_fun_sum _ fun i _ => analyticAt_const.mul
        (analyticOnNhd_regCarlsonRSlit t (addDirichletUnit b i) w hw)) ?_ hz
  intro w hw
  change regCarlsonRSlit t b w = ∑ i, b i * regCarlsonRSlit t (addDirichletUnit b i) w
  simp_rw [regCarlsonRSlit_eq_continued t _ hw]
  exact regCarlsonRContinued_eq_sum_addDirichletUnit t b hw

/-- The second associated relation on the full node domain, without parameter exceptions. -/
theorem regCarlsonRSlit_add_one_eq_sum_mul_addDirichletUnit (t : ℂ) (b : ι → ℂ)
    {z : ι → ℂ} (hz : z ∈ carlsonRSlitDomain) :
    regCarlsonRSlit (t + 1) b z =
      ∑ i, b i * z i * regCarlsonRSlit t (addDirichletUnit b i) z := by
  apply eqOn_carlsonRSlitDomain_of_eqOn_rightHalfPlane
    (analyticOnNhd_regCarlsonRSlit (t + 1) b) (fun w hw =>
      Finset.analyticAt_fun_sum _ fun i _ =>
        (analyticAt_const.mul ((ContinuousLinearMap.proj i : (ι → ℂ) →L[ℂ] ℂ).analyticAt w)).mul
          (analyticOnNhd_regCarlsonRSlit t (addDirichletUnit b i) w hw)) ?_ hz
  intro w hw
  change regCarlsonRSlit (t + 1) b w =
    ∑ i, b i * w i * regCarlsonRSlit t (addDirichletUnit b i) w
  simp_rw [regCarlsonRSlit_eq_continued _ _ hw]
  exact regCarlsonRContinued_add_one_eq_sum_mul_addDirichletUnit t b hw

/-- The empty-index convention is preserved by the node continuation. -/
theorem regCarlsonRSlit_eq_zero_of_isEmpty [IsEmpty ι] (t : ℂ) (b : ι → ℂ)
    {z : ι → ℂ} (hz : z ∈ carlsonRSlitDomain) : regCarlsonRSlit t b z = 0 := by
  rw [regCarlsonRSlit_eq_sum_addDirichletUnit t b hz]
  simp

end DirichletTransform
