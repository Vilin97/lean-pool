/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import LeanPool.CarlsonFunctions.Carlson.L.Continuation
public import LeanPool.CarlsonFunctions.Carlson.Aggregation
public import LeanPool.CarlsonFunctions.Carlson.R.ZeroParameter

/-!
# Symmetry, aggregation, and scaling of Carlson's L-function

Carlson (1987), (2.2)–(2.5). Continued identities impose no convergence
restriction on Dirichlet parameters. Positive real scaling preserves the
principal branch and the right-half-plane node domain.
-/

open Complex ProbabilityTheory
@[expose] public noncomputable section
namespace DirichletTransform
variable {ι : Type*} [Fintype ι]

/-- Equation (2.4): equal nodes may be aggregated by any surjective partition. -/
theorem regCarlsonLContinued_aggregate {κ : Type*} [Fintype κ]
    {q : ι → κ} (hq : Function.Surjective q) (t : ℂ)
    {z : κ → ℂ} (hz : z ∈ carlsonRVariableDomain) (b : ι → ℂ) :
    regCarlsonLContinued t (z ∘ q) (fun i => hz (q i)) b =
      regCarlsonLContinued t z hz (stdSimplexAggregate q b) := by
  unfold regCarlsonLContinued
  congr 1
  funext s
  exact regCarlsonRContinued_aggregate hq s hz b

/-- Equation (2.3): a zero parameter and its node can be deleted. The remaining
index type is nonempty, as in the existing R-deletion theorem used here. -/
theorem regCarlsonLContinued_option_zero [Nonempty ι] (t : ℂ)
    {b : Option ι → ℂ} (hb : b none = 0)
    {z : Option ι → ℂ} (hz : z ∈ carlsonRVariableDomain) :
    regCarlsonLContinued t z hz b =
      regCarlsonLContinued t (z ∘ some) (fun i => hz (some i)) (b ∘ some) := by
  unfold regCarlsonLContinued
  congr 1
  funext s
  exact regCarlsonRContinued_option_zero s hb hz

/-- Equation (2.2), for arbitrary complex Dirichlet parameters. -/
theorem regCarlsonLContinued_perm (t : ℂ) (b : ι → ℂ)
    {z : ι → ℂ} (hz : z ∈ carlsonRVariableDomain) (σ : Equiv.Perm ι) :
    regCarlsonLContinued t (z ∘ σ) (fun i => hz (σ i)) (b ∘ σ) =
      regCarlsonLContinued t z hz b := by
  apply congrFun (analyticOnNhd_eq_of_eqOn_mvBetaConvergent ?_
    (analyticOnNhd_regCarlsonLContinued t hz) ?_) b
  · intro b _
    exact analyticAt_regCarlsonLContinued_comp (fun i => hz (σ i)) analyticAt_const
      (analyticAt_pi_iff.mpr (fun i =>
        (ContinuousLinearMap.proj (σ i) : (ι → ℂ) →L[ℂ] ℂ).analyticAt b))
  · intro b hb
    calc
      _ = regCarlsonLIntegral t (b ∘ σ) (z ∘ σ) :=
        regCarlsonLContinued_eq_integral t (fun i => hz (σ i)) (fun i => hb (σ i))
      _ = regCarlsonLIntegral t b z := regCarlsonLIntegral_perm t b z σ
      _ = _ := (regCarlsonLContinued_eq_integral t hz hb).symm

/-- Coincident nodes reduce L to the elementary power-logarithm kernel. -/
theorem regCarlsonLContinued_const (t w : ℂ) (hw : w ∈ carlsonRightHalfPlane)
    (b : ι → ℂ) :
    regCarlsonLContinued t (fun _ => w) (fun _ => hw) b =
      (w ^ t * log w) / Gamma (∑ i, b i) := by
  apply congrFun (analyticOnNhd_eq_of_eqOn_mvBetaConvergent
    (analyticOnNhd_regCarlsonLContinued t (fun _ => hw)) ?_ ?_) b
  · intro b _
    have hsum : AnalyticAt ℂ (fun c : ι → ℂ => ∑ i, c i) b :=
      Finset.analyticAt_fun_sum _ (fun i _ =>
        (ContinuousLinearMap.proj i : (ι → ℂ) →L[ℂ] ℂ).analyticAt b)
    have hγ := Complex.differentiable_one_div_Gamma.analyticAt (∑ i, b i)
    simpa only [div_eq_mul_inv, one_mul, Function.comp_def, Pi.mul_apply] using!
      analyticAt_const.mul (hγ.comp hsum)
  · intro b hb
    rw [regCarlsonLContinued_eq_integral t (fun _ => hw) hb]
    exact regCarlsonDirichletAverage_const (carlsonLKernel t) w hb

/-- The all-one node vector gives zero for every exponent and parameter. -/
@[simp] theorem regCarlsonLContinued_one (t : ℂ) (b : ι → ℂ) :
    regCarlsonLContinued t (fun _ : ι => 1) (fun _ => by norm_num [carlsonRightHalfPlane]) b = 0 := by
  simpa using regCarlsonLContinued_const t 1 (by norm_num [carlsonRightHalfPlane]) b

/-- The empty-index native integral vanishes. -/
@[simp] theorem regCarlsonLIntegral_empty [IsEmpty ι] (t : ℂ) (b z : ι → ℂ) :
    regCarlsonLIntegral t b z = 0 := by
  simp [regCarlsonLIntegral, regCarlsonDirichletAverage, regDirichletIntegral]

/-- The entire continuation respects the empty-index convention. -/
@[simp] theorem regCarlsonLContinued_empty [IsEmpty ι] (t : ℂ) (b z : ι → ℂ)
    (hz : z ∈ carlsonRVariableDomain) : regCarlsonLContinued t z hz b = 0 := by
  rw [regCarlsonLContinued_eq_integral t hz (fun i => isEmptyElim i)]
  simp

/-- The one-node case of Carlson's definition, with its regularizing Gamma factor. -/
theorem regCarlsonLContinued_unique [Unique ι] (t : ℂ) (b z : ι → ℂ)
    (hz : z ∈ carlsonRVariableDomain) :
    regCarlsonLContinued t z hz b =
      (z default ^ t * log (z default)) / Gamma (b default) := by
  have hz' : z = fun _ => z default := funext fun i => congrArg z (Subsingleton.elim i default)
  generalize hw : z default = w at hz' ⊢
  subst z
  simpa using regCarlsonLContinued_const t _ (hz default) b

omit [Fintype ι] in
/-- Positive real scaling preserves the node domain. -/
theorem carlsonRVariableDomain_smul_pos {z : ι → ℂ} (hz : z ∈ carlsonRVariableDomain)
    {a : ℝ} (ha : 0 < a) : (fun i => (a : ℂ) * z i) ∈ carlsonRVariableDomain := by
  intro i
  change 0 < ((a : ℂ) * z i).re
  simpa using mul_pos ha (hz i)

/-- Equation (2.5) for the native integral, including the logarithmic correction. -/
theorem regCarlsonLIntegral_smul_of_pos (t : ℂ) {b z : ι → ℂ}
    (hb : b ∈ mvBetaConvergent) (hz : z ∈ carlsonRVariableDomain)
    {a : ℝ} (ha : 0 < a) :
    regCarlsonLIntegral t b (fun i => (a : ℂ) * z i) =
      (a : ℂ) ^ t * (regCarlsonLIntegral t b z + regCarlsonRIntegral t b z * log (a : ℂ)) := by
  have h := hasDerivAt_regCarlsonRIntegral_L t hb (carlsonRVariableDomain_smul_pos hz ha)
  have heq : (fun s => regCarlsonRIntegral s b (fun i => (a : ℂ) * z i)) =
      (fun s => (a : ℂ) ^ s * regCarlsonRIntegral s b z) :=
    funext fun s => regCarlsonRIntegral_smul_of_pos s hz ha
  rw [heq] at h
  have hp : HasDerivAt (fun s : ℂ => (a : ℂ) ^ s)
      ((a : ℂ) ^ t * log (a : ℂ)) t :=
    (Complex.hasStrictDerivAt_const_cpow (Or.inl (ofReal_ne_zero.mpr ha.ne'))).hasDerivAt
  have H := h.unique (hp.mul (hasDerivAt_regCarlsonRIntegral_L t hb hz))
  linear_combination H

/-- Equation (2.5) for every complex Dirichlet parameter after regularization. -/
theorem regCarlsonLContinued_smul_of_pos (t : ℂ) (b : ι → ℂ)
    {z : ι → ℂ} (hz : z ∈ carlsonRVariableDomain) {a : ℝ} (ha : 0 < a) :
    regCarlsonLContinued t (fun i => (a : ℂ) * z i)
        (carlsonRVariableDomain_smul_pos hz ha) b =
      (a : ℂ) ^ t *
        (regCarlsonLContinued t z hz b + regCarlsonRContinued t z hz b * log (a : ℂ)) := by
  apply congrFun (analyticOnNhd_eq_of_eqOn_mvBetaConvergent
    (analyticOnNhd_regCarlsonLContinued t (carlsonRVariableDomain_smul_pos hz ha))
    (analyticOnNhd_const.mul ((analyticOnNhd_regCarlsonLContinued t hz).add
      ((analyticOnNhd_regCarlsonRContinued t hz).mul analyticOnNhd_const))) ?_) b
  intro b hb
  simp only [Pi.add_apply, regCarlsonLContinued_eq_integral _ _ hb,
    regCarlsonRContinued_eq_integral _ _ hb]
  exact regCarlsonLIntegral_smul_of_pos t hb hz ha

end DirichletTransform
end
