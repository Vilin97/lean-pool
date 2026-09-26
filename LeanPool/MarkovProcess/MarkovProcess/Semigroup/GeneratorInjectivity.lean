/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import LeanPool.MarkovProcess.MarkovProcess.Semigroup.Generator
public import Mathlib.Analysis.ODE.Gronwall


/-!
# Eigenvectors of a generator, and injectivity of `μ - L`

Let `S` be a strongly continuous contraction semigroup with generator `L`.  If `f` lies in the
generator domain with `L f = μ f`, then the orbit of `f` is the scalar exponential
`S t f = exp (μ t) f`: the defect `w t = S t f - exp (μ t) f` vanishes at `t = 0` and has right
derivative `μ w t`, so Grönwall's inequality forces it to vanish
(`operator_eq_exp_smul_of_generator_eq_smul`).

Since `S` is contractive, an eigenvalue `μ > 0` therefore forces `f = 0`
(`eq_zero_of_generator_eq_smul`); equivalently, `μ - L` is injective on the generator domain
(`eq_of_smul_sub_generator_eq`).  This is the uniqueness half of the assertion that the resolvent
`(μ - L)⁻¹` is a well-defined operator.
-/

@[expose] public section

noncomputable section PortComputability

open Filter Set Topology
open scoped NNReal

namespace MarkovProcess.Semigroup.StronglyContinuousContractionSemigroup

section

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable (S : StronglyContinuousContractionSemigroup E)

/-- The defect between the orbit of a vector and the scalar exponential `exp (μ t)` times it. -/
private def exponentialDefect (μ : ℝ) (f : E) (s : ℝ) : E :=
  S (Real.toNNReal s) f - Real.exp (μ * s) • f

private theorem continuous_exponentialDefect (μ : ℝ) (f : E) :
    Continuous (S.exponentialDefect μ f) :=
  (S.continuous_operator_toNNReal f).sub
    ((Real.continuous_exp.comp (continuous_const.mul continuous_id)).smul continuous_const)

private theorem exponentialDefect_zero (μ : ℝ) (f : E) : S.exponentialDefect μ f 0 = 0 := by
  rw [exponentialDefect, Real.toNNReal_zero, S.zero_apply, mul_zero, Real.exp_zero, one_smul,
    sub_self]

private theorem hasDerivWithinAt_exponentialDefect {μ : ℝ} (f : S.generatorDomain)
    (hgen : S.generator f = μ • (f : E)) {s : ℝ} (hs : 0 ≤ s) :
    HasDerivWithinAt (S.exponentialDefect μ f) (μ • S.exponentialDefect μ f s) (Ici s) s := by
  have horbit := S.hasDerivWithinAt_Ici f (Real.toNNReal s)
  rw [Real.coe_toNNReal s hs] at horbit
  have hlin : HasDerivAt (fun u : ℝ ↦ μ * u) μ s := by
    simpa using (hasDerivAt_id s).const_mul μ
  have hexp : HasDerivAt (fun u : ℝ ↦ Real.exp (μ * u) • (f : E))
      ((Real.exp (μ * s) * μ) • (f : E)) s := hlin.exp.smul_const (f : E)
  have hsub := horbit.sub hexp.hasDerivWithinAt
  rw [hgen, map_smul] at hsub
  have hval : μ • S (Real.toNNReal s) (f : E) - (Real.exp (μ * s) * μ) • (f : E)
      = μ • S.exponentialDefect μ (f : E) s := by
    rw [exponentialDefect, smul_sub, smul_smul, mul_comm μ (Real.exp (μ * s))]
  rw [hval] at hsub
  exact hsub

/-- **An eigenvector of the generator has an exponential orbit.**  If `f` lies in the generator
domain and `L f = μ f`, then `S t f = exp (μ t) f` at every time `t`. -/
theorem operator_eq_exp_smul_of_generator_eq_smul {μ : ℝ} (f : S.generatorDomain)
    (hgen : S.generator f = μ • (f : E)) (t : NNReal) :
    S t (f : E) = Real.exp (μ * t) • (f : E) := by
  have hzero := eq_zero_of_abs_deriv_le_mul_abs_self_of_eq_zero_right
    (f := S.exponentialDefect μ f) (f' := fun s ↦ μ • S.exponentialDefect μ f s) (K := |μ|)
    (a := 0) (b := (t : ℝ)) (S.continuous_exponentialDefect μ f).continuousOn
    (fun s hs ↦ S.hasDerivWithinAt_exponentialDefect f hgen hs.1)
    (S.exponentialDefect_zero μ f)
    (fun s _ ↦ by rw [norm_smul, Real.norm_eq_abs])
    (t : ℝ) ⟨t.coe_nonneg, le_rfl⟩
  rw [exponentialDefect, Real.toNNReal_coe, sub_eq_zero] at hzero
  exact hzero

/-- **Positive eigenvalues are excluded.**  For `μ > 0`, a vector of the generator domain with
`L f = μ f` vanishes: its orbit would grow like `exp (μ t)`, contradicting contractivity. -/
theorem eq_zero_of_generator_eq_smul {μ : ℝ} (hμ : 0 < μ) (f : S.generatorDomain)
    (hgen : S.generator f = μ • (f : E)) : (f : E) = 0 := by
  have hcontract : Real.exp μ * ‖(f : E)‖ ≤ ‖(f : E)‖ := by
    have hle := S.norm_apply_le 1 (f : E)
    rw [S.operator_eq_exp_smul_of_generator_eq_smul f hgen 1, norm_smul, Real.norm_eq_abs,
      abs_of_pos (Real.exp_pos _), NNReal.coe_one, mul_one] at hle
    exact hle
  have hone : 1 < Real.exp μ := by
    have hexp := Real.add_one_le_exp μ
    linarith only [hexp, hμ]
  rw [← norm_le_zero_iff]
  by_contra hpos
  push Not at hpos
  have hstrict : 1 * ‖(f : E)‖ < Real.exp μ * ‖(f : E)‖ := by
    exact mul_lt_mul_of_pos_right hone hpos
  rw [one_mul] at hstrict
  linarith only [hstrict, hcontract]

/-- **Injectivity of `μ - L`.**  For `μ > 0`, two vectors of the generator domain with the same
image under `μ - L` are equal.  Together with surjectivity onto the whole space this says that
the resolvent `(μ - L)⁻¹` is well defined. -/
theorem eq_of_smul_sub_generator_eq {μ : ℝ} (hμ : 0 < μ) (f g : S.generatorDomain)
    (h : μ • (f : E) - S.generator f = μ • (g : E) - S.generator g) : (f : E) = (g : E) := by
  have hker : S.generator (f - g) = μ • ((f - g : S.generatorDomain) : E) := by
    rw [map_sub, Submodule.coe_sub, smul_sub]
    have h0 : μ • (f : E) - S.generator f - (μ • (g : E) - S.generator g) = 0 :=
      sub_eq_zero_of_eq h
    refine eq_of_sub_eq_zero ?_
    rw [← neg_zero, ← h0]
    abel
  have hzero := S.eq_zero_of_generator_eq_smul hμ (f - g) hker
  rw [Submodule.coe_sub, sub_eq_zero] at hzero
  exact hzero

end

end MarkovProcess.Semigroup.StronglyContinuousContractionSemigroup

end PortComputability
