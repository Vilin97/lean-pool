/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/

/- Copyright (c) 2026 Bastiaan J Braams. All rights reserved. -/
module

public import LeanPool.CarlsonFunctions.Carlson.TwoVariable.RPolynomial
public import LeanPool.CarlsonFunctions.Carlson.R.SlitJointAnalytic

/-!
# Interchanging an exponent and a Dirichlet parameter

The two numerator parameters in the Gauss series are symmetric. We establish
this symmetry first near the all-one node vector, then continue in the parameters
and in the slit-plane node. This is the R-identity underlying Carlson (1987), (2.12).
-/

open Complex Filter Set
open scoped Topology
@[expose] public noncomputable section
namespace DirichletTransform.TwoVariable

private theorem analyticAt_coordinate (p : Fin 3 → ℂ) (i : Fin 3) :
    AnalyticAt ℂ (fun q : Fin 3 → ℂ => q i) p :=
  (analyticAt_pi_iff.mp analyticAt_id) i

/-- Only one monomial survives when the first polynomial node vanishes. -/
theorem carlsonRPolynomialNumerator₂_zero_left (n : ℕ) (u v y : ℂ) :
    carlsonRPolynomialNumerator₂ n u v 0 y = (ascPochhammer ℂ n).eval v * y ^ n := by
  unfold carlsonRPolynomialNumerator₂
  rw [Finset.sum_eq_single (0, n)]
  · simp
  · intro ij hij hne
    have hi : ij.1 ≠ 0 := by
      intro h
      apply hne
      have hs := Finset.mem_antidiagonal.mp hij
      ext <;> simp_all
    simp [zero_pow hi]
  · simp

private theorem parameterSymmetry_native_near_one (a u v y : ℂ)
    (hb : pair u v ∈ mvBetaConvergent)
    (hB : pair (u + v - a) a ∈ mvBetaConvergent) (hy : ‖y‖ < 1) :
    regCarlsonRIntegral (-a) (pair u v) (pair 1 (1 - y)) =
      regCarlsonRIntegral (-v) (pair (u + v - a) a) (pair 1 (1 - y)) := by
  have hnode : ∀ i, ‖pair 0 y i‖ < 1 := by
    intro i; fin_cases i
    · simp [pair]
    · exact hy
  have h₁ := hasSum_regCarlsonRIntegral_near_one a (pair u v) (pair 0 y) hb hnode
  have h₂ := hasSum_regCarlsonRIntegral_near_one v (pair (u + v - a) a) (pair 0 y) hB hnode
  have heq : (fun n : ℕ => (ascPochhammer ℂ n).eval a / (n.factorial : ℂ) *
      regCarlsonR n (pair 0 y) (pair u v)) =
      (fun n => (ascPochhammer ℂ n).eval v / (n.factorial : ℂ) *
      regCarlsonR n (pair 0 y) (pair (u + v - a) a)) := by
    funext n
    change _ * regRPolynomial n u v 0 y = _ * regRPolynomial n (u + v - a) a 0 y
    rw [regRPolynomial_eq_numerator₂_mul_one_div_Gamma,
      regRPolynomial_eq_numerator₂_mul_one_div_Gamma,
      carlsonRPolynomialNumerator₂_zero_left, carlsonRPolynomialNumerator₂_zero_left]
    rw [sub_add_cancel]
    ring
  rw [heq] at h₁
  have hn : (fun i => 1 - pair 0 y i) = pair 1 (1 - y) := by
    ext i; fin_cases i <;> simp [pair]
  simpa only [hn] using h₁.unique h₂

private theorem parameterSymmetry_near_one (a u v y : ℂ) (hy : ‖y‖ < 1) :
    regCarlsonRSlit (-a) (pair u v) (pair 1 (1 - y)) =
      regCarlsonRSlit (-v) (pair (u + v - a) a) (pair 1 (1 - y)) := by
  have hz : pair 1 (1 - y) ∈ carlsonRVariableDomain := by
    intro i; fin_cases i
    · change 0 < (1 : ℂ).re
      norm_num
    · change 0 < (1 - y).re
      have := re_le_norm y
      simp only [sub_re, one_re]
      linarith
  have hs := carlsonRVariableDomain_subset_slitDomain hz
  let B : (Fin 3 → ℂ) → Fin 2 → ℂ := fun p => pair (p 1 + p 2 - p 0) (p 0)
  have hB (p : Fin 3 → ℂ) : AnalyticAt ℂ B p := by
    apply analyticAt_pi_iff.mpr
    intro i; fin_cases i
    · exact ((analyticAt_coordinate p 1).add (analyticAt_coordinate p 2)).sub (analyticAt_coordinate p 0)
    · exact analyticAt_coordinate p 0
  have hb (p : Fin 3 → ℂ) : AnalyticAt ℂ (fun q => pair (q 1) (q 2)) p := by
    apply analyticAt_pi_iff.mpr
    intro i; fin_cases i
    · exact analyticAt_coordinate p 1
    · exact analyticAt_coordinate p 2
  have hleft : AnalyticOnNhd ℂ (fun p : Fin 3 → ℂ =>
      regCarlsonRSlit (-(p 0)) (pair (p 1) (p 2)) (pair 1 (1 - y))) univ :=
    fun p _ => analyticAt_regCarlsonRSlit_comp (analyticAt_coordinate p 0).neg
      (hb p) analyticAt_const hs
  have hright : AnalyticOnNhd ℂ (fun p : Fin 3 → ℂ =>
      regCarlsonRSlit (-(p 2)) (B p) (pair 1 (1 - y))) univ :=
    fun p _ => analyticAt_regCarlsonRSlit_comp (analyticAt_coordinate p 2).neg
      (hB p) analyticAt_const hs
  have heq := hleft.eq_of_eventuallyEq hright (z₀ := fun _ => 1) (by
    have hl := (hb (fun _ => 1)).continuousAt.tendsto.eventually
      (isOpen_mvBetaConvergent.mem_nhds (by intro i; fin_cases i <;> norm_num [pair]))
    have hr := (hB (fun _ => 1)).continuousAt.tendsto.eventually
      (isOpen_mvBetaConvergent.mem_nhds (by intro i; fin_cases i <;> norm_num [B, pair]))
    filter_upwards [hl, hr] with p hp hP
    rw [regCarlsonRSlit_eq_integral _ hp hz, regCarlsonRSlit_eq_integral _ hP hz]
    exact parameterSymmetry_native_near_one (p 0) (p 1) (p 2) y hp hP hy)
  exact congrFun heq ![a, u, v]

/-- Gauss numerator-parameter symmetry on the entire slit plane, with all
complex parameters allowed by reciprocal-Gamma regularization. -/
theorem regCarlsonRSlit_parameterSymmetry (a u v : ℂ) {w : ℂ} (hw : w ∈ slitPlane) :
    regCarlsonRSlit (-a) (pair u v) (pair 1 w) =
      regCarlsonRSlit (-v) (pair (u + v - a) a) (pair 1 w) := by
  have hn {w : ℂ} (hw : w ∈ slitPlane) : pair 1 w ∈ carlsonRSlitDomain := by
    intro i; fin_cases i
    · simp [pair]
    · exact hw
  have hnode (w : ℂ) : AnalyticAt ℂ (fun w => pair 1 w) w := by
    apply analyticAt_pi_iff.mpr
    intro i; fin_cases i
    · exact analyticAt_const
    · exact analyticAt_id
  have ha (t : ℂ) (b : Fin 2 → ℂ) :
      AnalyticOnNhd ℂ (fun w => regCarlsonRSlit t b (pair 1 w)) slitPlane :=
    fun w hw => analyticAt_regCarlsonRSlit_comp analyticAt_const analyticAt_const (hnode w) (hn hw)
  apply (ha (-a) (pair u v)).eqOn_of_preconnected_of_eventuallyEq
    (ha (-v) (pair (u + v - a) a))
    (starConvex_one_slitPlane.isPathConnected (by simp)).isConnected.isPreconnected
    (show (1 : ℂ) ∈ slitPlane by simp) ?_ hw
  have hnear : ∀ᶠ w : ℂ in 𝓝 1, ‖1 - w‖ < 1 :=
    (isOpen_lt (by fun_prop) continuous_const).mem_nhds (by simp)
  filter_upwards [hnear] with w hw
  simpa using parameterSymmetry_near_one a u v (1 - w) hw

/-- A ratio of two right-half-plane numbers cannot lie on the nonpositive real axis. -/
theorem div_mem_slitPlane_of_re_pos {x y : ℂ} (hx : 0 < x.re) (hy : 0 < y.re) :
    x / y ∈ slitPlane := by
  apply mem_slitPlane_iff.mpr
  by_cases hi : (x / y).im = 0
  · left
    have h := congrArg Complex.re (div_mul_cancel₀ x (ne_zero_of_re_pos hy))
    rw [mul_re, hi, zero_mul, sub_zero] at h
    nlinarith
  · exact Or.inr hi

/-- Normalize the first node, with branch control for arbitrary right-half-plane nodes.
The normalized second node need only belong to the slit plane. -/
theorem regCarlsonRSlit_normalize_first (t : ℂ) (b : Fin 2 → ℂ) {x y : ℂ}
    (hx : 0 < x.re) (hy : 0 < y.re) :
    regCarlsonRSlit t b (pair x y) = x ^ t * regCarlsonRSlit t b (pair 1 (y / x)) := by
  let q : (Fin 2 → ℂ) → Fin 2 → ℂ := fun z => pair 1 (z 1 / z 0)
  have hq {z : Fin 2 → ℂ} (hz : z ∈ carlsonRVariableDomain) : AnalyticAt ℂ q z := by
    apply analyticAt_pi_iff.mpr
    intro i; fin_cases i
    · exact analyticAt_const
    · exact ((analyticAt_pi_iff.mp analyticAt_id) 1).div
        ((analyticAt_pi_iff.mp analyticAt_id) 0) (ne_zero_of_re_pos (hz 0))
  have hqs {z : Fin 2 → ℂ} (hz : z ∈ carlsonRVariableDomain) : q z ∈ carlsonRSlitDomain := by
    intro i; fin_cases i
    · simp [q, pair]
    · exact div_mem_slitPlane_of_re_pos (hz 1) (hz 0)
  have hnative {z : Fin 2 → ℂ} (hz : z ∈ carlsonRVariableDomain)
      (hQ : q z ∈ carlsonRVariableDomain) :
      regCarlsonRSlit t b z = z 0 ^ t * regCarlsonRSlit t b (q z) := by
    apply congrFun (analyticOnNhd_eq_of_eqOn_mvBetaConvergent
      (fun _ _ => analyticAt_regCarlsonRSlit_comp analyticAt_const analyticAt_id
        analyticAt_const (carlsonRVariableDomain_subset_slitDomain hz))
      (fun _ _ => analyticAt_const.mul (analyticAt_regCarlsonRSlit_comp analyticAt_const
        analyticAt_id analyticAt_const (hqs hz))) ?_) b
    intro B hB
    change regCarlsonRSlit t B z = z 0 ^ t * regCarlsonRSlit t B (q z)
    rw [regCarlsonRSlit_eq_integral _ hB hz, regCarlsonRSlit_eq_integral _ hB hQ]
    have h := regCarlsonRIntegral_smul_of_re_pos (b := B) t (hz 0) hQ
    have heq : (fun i => z 0 * q z i) = z := by
      ext i; fin_cases i
      · simp [q]
      · dsimp [q]
        field_simp [ne_zero_of_re_pos (hz 0)]
    rwa [heq] at h
  have hleft : AnalyticOnNhd ℂ (regCarlsonRSlit t b) carlsonRVariableDomain :=
    (analyticOnNhd_regCarlsonRSlit t b).mono carlsonRVariableDomain_subset_slitDomain
  have hright : AnalyticOnNhd ℂ (fun z => z 0 ^ t * regCarlsonRSlit t b (q z))
      carlsonRVariableDomain := by
    intro z hz
    have hcoord : AnalyticAt ℂ (fun w : Fin 2 → ℂ => w 0) z :=
      (analyticAt_pi_iff.mp analyticAt_id) 0
    exact (hcoord.cpow analyticAt_const
      (carlsonRightHalfPlane_subset_slitPlane (hz 0))).mul
        (analyticAt_regCarlsonRSlit_comp analyticAt_const analyticAt_const (hq hz) (hqs hz))
  have hc : Convex ℝ (carlsonRVariableDomain : Set (Fin 2 → ℂ)) := by
    intro z hz w hw a c ha hc hac i
    exact convex_carlsonRightHalfPlane (hz i) (hw i) ha hc hac
  have hone : (fun _ : Fin 2 => (1 : ℂ)) ∈ carlsonRVariableDomain :=
    fun _ => by norm_num [carlsonRightHalfPlane]
  have hevent : (regCarlsonRSlit t b) =ᶠ[𝓝 (fun _ : Fin 2 => 1)]
      (fun z => z 0 ^ t * regCarlsonRSlit t b (q z)) := by
    have hQ := (hq hone).continuousAt.tendsto.eventually
      (isOpen_carlsonRVariableDomain.mem_nhds (by
        intro i; fin_cases i <;> norm_num [q, carlsonRightHalfPlane]))
    filter_upwards [isOpen_carlsonRVariableDomain.mem_nhds hone, hQ] with z hz hQ
    exact hnative hz hQ
  apply hleft.eqOn_of_preconnected_of_eventuallyEq hright hc.isPreconnected hone hevent
  intro i; fin_cases i
  · exact hx
  · exact hy

/-- Exponent-parameter interchange at two right-half-plane nodes, with no parameter
restrictions and a slit-plane ratio on the transformed side. -/
theorem regCarlsonRSlit_parameterInterchange (t u v : ℂ) {x y : ℂ}
    (hx : 0 < x.re) (hy : 0 < y.re) :
    regCarlsonRSlit t (pair u v) (pair x y) =
      x ^ t * regCarlsonRSlit (-v) (pair (u + v + t) (-t)) (pair 1 (y / x)) := by
  rw [regCarlsonRSlit_normalize_first t _ hx hy]
  have h := regCarlsonRSlit_parameterSymmetry (-t) u v (div_mem_slitPlane_of_re_pos hy hx)
  simpa using congrArg (fun w => x ^ t * w) h

/-- Simultaneously swapping the two parameters and nodes on the slit domain. -/
theorem regCarlsonRSlit_pair_swap (t u v : ℂ) {x y : ℂ}
    (hx : x ∈ slitPlane) (hy : y ∈ slitPlane) :
    regCarlsonRSlit t (pair v u) (pair y x) = regCarlsonRSlit t (pair u v) (pair x y) := by
  have hperm (b : Fin 2 → ℂ) : AnalyticAt ℂ (fun B => B ∘ swap) b :=
    analyticAt_pi_iff.mpr fun i => (analyticAt_pi_iff.mp analyticAt_id) (swap i)
  have hright {z : Fin 2 → ℂ} (hz : z ∈ carlsonRVariableDomain) (b : Fin 2 → ℂ) :
      regCarlsonRSlit t (b ∘ swap) (z ∘ swap) = regCarlsonRSlit t b z := by
    apply congrFun (analyticOnNhd_eq_of_eqOn_mvBetaConvergent
      (fun B _ => analyticAt_regCarlsonRSlit_comp analyticAt_const (hperm B) analyticAt_const
        (carlsonRVariableDomain_subset_slitDomain (fun i => hz (swap i))))
      (fun _ _ => analyticAt_regCarlsonRSlit_comp analyticAt_const analyticAt_id analyticAt_const
        (carlsonRVariableDomain_subset_slitDomain hz)) ?_) b
    intro B hB
    change regCarlsonRSlit t (B ∘ swap) (z ∘ swap) = regCarlsonRSlit t B z
    dsimp only [Function.comp_def]
    rw [regCarlsonRSlit_eq_integral _ (fun i => hB (swap i)) (fun i => hz (swap i)),
      regCarlsonRSlit_eq_integral _ hB hz]
    exact regCarlsonDirichletAverage_perm B z (fun w => w ^ t) swap
  have hleft : AnalyticOnNhd ℂ (fun z : Fin 2 → ℂ =>
      regCarlsonRSlit t ((pair u v) ∘ swap) (z ∘ swap)) carlsonRSlitDomain :=
    fun z hz => analyticAt_regCarlsonRSlit_comp analyticAt_const analyticAt_const (hperm z)
      (fun i => hz (swap i))
  have hz : pair x y ∈ carlsonRSlitDomain := by
    intro i; fin_cases i
    · exact hx
    · exact hy
  have h := eqOn_carlsonRSlitDomain_of_eqOn_rightHalfPlane hleft
    (analyticOnNhd_regCarlsonRSlit t (pair u v)) (fun z hz => hright hz (pair u v)) hz
  simpa only [pair_comp_swap] using h

/-- The second form of the exponent-parameter interchange, normalized at the last node. -/
theorem regCarlsonRSlit_parameterInterchange_last (t u v : ℂ) {x y : ℂ}
    (hx : 0 < x.re) (hy : 0 < y.re) :
    regCarlsonRSlit t (pair u v) (pair x y) =
      y ^ t * regCarlsonRSlit (-u) (pair (-t) (u + v + t)) (pair (x / y) 1) := by
  rw [← regCarlsonRSlit_pair_swap t u v
    (carlsonRightHalfPlane_subset_slitPlane hx) (carlsonRightHalfPlane_subset_slitPlane hy),
    regCarlsonRSlit_parameterInterchange t v u hy hx]
  rw [← regCarlsonRSlit_pair_swap (-u) (v + u + t) (-t)
    (show (1 : ℂ) ∈ slitPlane by simp) (div_mem_slitPlane_of_re_pos hx hy), add_comm v u]

end DirichletTransform.TwoVariable
