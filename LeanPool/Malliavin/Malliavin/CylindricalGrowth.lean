/-
Copyright (c) 2026 The lean-malliavin contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-malliavin contributors
-/
module

public import LeanPool.Malliavin.Malliavin.DualDerivative
public import Mathlib.Analysis.Calculus.ContDiff.Polynomial
public import Mathlib.Analysis.Calculus.Deriv.Polynomial

/-!
# Cylindrical functionals of polynomial growth lie in `𝔻₁,₂`

The domain `domD12 μ` of the closed Malliavin derivative was built from *bounded* smooth
cylindrical functionals.  This file extends it to the natural class of textbook examples:
for `f : ℝⁿ → ℝ` of class `C¹` with `|f|` and `‖f'‖` of polynomial growth and continuous linear
functionals `L₁, …, Lₙ`, the functional `x ↦ f (L₁ x, …, Lₙ x)` belongs to `𝔻₁,₂` and its
closed derivative is the classical one,

  `D_cl (f ∘ L) = ∑ᵢ ∂ᵢ f (L x) • ofDual Lᵢ`  (`cylinder_growth_mem_domD12`).

In particular every polynomial in finitely many Brownian coordinates `B t₁, …, B tₙ` lies in
`𝔻₁,₂`, with the textbook time derivative
`Dₜ p(B) = ∑ᵢ ∂ᵢ p(B) 1_{(0, tᵢ]}(t)` (`timeDerivative_mderivClosure_cylinder_growth`).

## Method

The coordinates are truncated by the odd, `C^∞`, non-decreasing functions
`cutoff m x = (m + 1) arctan (x / (m + 1))` (from `DualDerivative.lean`), which are bounded,
`1`-Lipschitz, `|cutoff m x| ≤ |x|`, and converge to the identity together with their
derivatives.  The truncated functionals `f ∘ truncCoord m L` are smooth and bounded, hence in
the domain of the derivative, and the chain rule (`mderiv_comp_truncCoord`) computes their
derivative.  Since `|f|, ‖f'‖ ≤ C (1 + ‖y‖)ᵏ` and `1 + ‖truncCoord m L x‖ ≤ gaussWeight L x`,
where the Gaussian weight `gaussWeight L x = 1 + ∑ᵢ |Lᵢ x|` has all moments
(`integrable_gaussWeight_pow`), dominated convergence in `L²` yields convergence of the
functionals and of their derivatives, and closedness of the graph (`mem_domD12_of_tendsto`)
concludes.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal InnerProductSpace

namespace Malliavin

section Truncation

variable {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]

/-- The truncated coordinate map `x ↦ (cutoff m (L i x))ᵢ`. -/
noncomputable def truncCoord (m : ℕ) {n : ℕ} (L : Fin n → StrongDual ℝ W) (x : W) : Fin n → ℝ :=
  fun i ↦ cutoff m (L i x)

theorem contDiff_truncCoord (m : ℕ) {n : ℕ} (L : Fin n → StrongDual ℝ W) :
    ContDiff ℝ 1 (truncCoord m L) :=
  contDiff_pi.mpr fun i ↦ (cutoff_contDiff m).comp (L i).contDiff

theorem norm_truncCoord_le (m : ℕ) {n : ℕ} (L : Fin n → StrongDual ℝ W) (x : W) :
    ‖truncCoord m L x‖ ≤ (m + 1) * (Real.pi / 2) := by
  rw [pi_norm_le_iff_of_nonneg (by positivity)]
  intro i
  rw [Real.norm_eq_abs]
  exact abs_cutoff_le_const m _

theorem norm_truncCoord_le_norm (m : ℕ) {n : ℕ} (L : Fin n → StrongDual ℝ W) (x : W) :
    ‖truncCoord m L x‖ ≤ ‖fun i ↦ L i x‖ := by
  rw [pi_norm_le_iff_of_nonneg (norm_nonneg _)]
  intro i
  rw [Real.norm_eq_abs]
  exact (abs_cutoff_le m _).trans (norm_le_pi_norm (fun i ↦ L i x) i)

/-- The derivative of the truncated coordinate map is bounded by `max ‖L i‖`. -/
theorem norm_fderiv_truncCoord_le (m : ℕ) {n : ℕ} (L : Fin n → StrongDual ℝ W) (x : W) :
    ‖fderiv ℝ (truncCoord m L) x‖ ≤ ∑ i, ‖L i‖ := by
  have hd : ∀ i, DifferentiableAt ℝ (fun x ↦ cutoff m (L i x)) x := fun i ↦
    ((cutoff_contDiff m).differentiable one_ne_zero (L i x)).comp x (L i).differentiableAt
  change ‖fderiv ℝ (fun x (i : Fin n) ↦ cutoff m (L i x)) x‖ ≤ _
  rw [fderiv_pi hd]
  refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun v ↦ ?_
  rw [pi_norm_le_iff_of_nonneg (by positivity)]
  intro i
  rw [ContinuousLinearMap.pi_apply]
  have hcomp : (fun x ↦ cutoff m (L i x)) = cutoff m ∘ L i := rfl
  rw [hcomp, fderiv_comp x ((cutoff_contDiff m).differentiable one_ne_zero _)
    (L i).differentiableAt, (L i).fderiv, ContinuousLinearMap.comp_apply, fderiv_eq_smul_deriv,
    norm_smul, Real.norm_eq_abs]
  calc |L i v| * ‖deriv (cutoff m) (L i x)‖
      ≤ ‖L i‖ * ‖v‖ * 1 := by
        gcongr
        · exact (L i).le_opNorm v
        · rw [Real.norm_eq_abs]
          exact abs_deriv_cutoff_le m _
    _ ≤ (∑ i, ‖L i‖) * ‖v‖ := by
        rw [mul_one]
        gcongr
        exact Finset.single_le_sum (fun j _ ↦ norm_nonneg (L j)) (Finset.mem_univ i)

/-- `f ∘ truncCoord` is smooth bounded for every `C¹` function `f`. -/
theorem isSmoothBounded_comp_truncCoord {n : ℕ} {f : (Fin n → ℝ) → ℝ} (hf : ContDiff ℝ 1 f)
    (m : ℕ) (L : Fin n → StrongDual ℝ W) :
    IsSmoothBounded (fun x ↦ f (truncCoord m L x)) where
  contDiff := hf.comp (contDiff_truncCoord m L)
  bounded := by
    obtain ⟨C, hC⟩ := (isCompact_closedBall (0 : Fin n → ℝ) ((m + 1) * (Real.pi / 2)))
      |>.exists_bound_of_continuousOn hf.continuous.continuousOn
    exact ⟨C, fun x ↦ by
      rw [← Real.norm_eq_abs]
      exact hC _ (mem_closedBall_zero_iff.mpr (norm_truncCoord_le m L x))⟩
  bounded_fderiv := by
    obtain ⟨C, hC⟩ := (isCompact_closedBall (0 : Fin n → ℝ) ((m + 1) * (Real.pi / 2)))
      |>.exists_bound_of_continuousOn (hf.continuous_fderiv one_ne_zero).continuousOn
    refine ⟨C * ∑ i, ‖L i‖, fun x ↦ ?_⟩
    have hcomp : (fun x ↦ f (truncCoord m L x)) = f ∘ truncCoord m L := rfl
    rw [hcomp, fderiv_comp x (hf.differentiable one_ne_zero _)
      ((contDiff_truncCoord m L).differentiable one_ne_zero _)]
    refine (ContinuousLinearMap.opNorm_comp_le _ _).trans ?_
    exact mul_le_mul (hC _ (mem_closedBall_zero_iff.mpr (norm_truncCoord_le m L x)))
      (norm_fderiv_truncCoord_le m L x) (norm_nonneg _)
      ((norm_nonneg _).trans (hC _ (mem_closedBall_zero_iff.mpr (norm_truncCoord_le m L x))))

end Truncation

section Growth

open CameronMartin

variable {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]
  [CompleteSpace W] [MeasurableSpace W] [BorelSpace W]
  [SecondCountableTopology W]
  (μ : Measure W) [IsGaussian μ]

/-- The Gaussian weight `1 + ∑ᵢ |Lᵢ x|`, which dominates `1 + ‖(Lᵢ x)ᵢ‖`. -/
noncomputable def gaussWeight {n : ℕ} (L : Fin n → StrongDual ℝ W) (x : W) : ℝ :=
  1 + ∑ i, |L i x|

omit [CompleteSpace W] [MeasurableSpace W] [BorelSpace W] [SecondCountableTopology W] in
theorem one_le_gaussWeight {n : ℕ} (L : Fin n → StrongDual ℝ W) (x : W) : 1 ≤ gaussWeight L x :=
  le_add_of_nonneg_right (Finset.sum_nonneg fun _ _ ↦ abs_nonneg _)

omit [CompleteSpace W] [MeasurableSpace W] [BorelSpace W] [SecondCountableTopology W] in
theorem one_add_norm_le_gaussWeight {n : ℕ} (L : Fin n → StrongDual ℝ W) (x : W) :
    1 + ‖fun i ↦ L i x‖ ≤ gaussWeight L x := by
  unfold gaussWeight
  gcongr
  exact (pi_norm_le_iff_of_nonneg (Finset.sum_nonneg fun _ _ ↦ abs_nonneg _)).mpr fun i ↦
    (Real.norm_eq_abs _).le.trans (Finset.single_le_sum (fun j _ ↦ abs_nonneg (L j x))
      (Finset.mem_univ i))

omit [CompleteSpace W] [SecondCountableTopology W] in
/-- Powers of the Gaussian weight are integrable. -/
theorem integrable_gaussWeight_pow {n : ℕ} (L : Fin n → StrongDual ℝ W) (k : ℕ) :
    Integrable (fun x ↦ gaussWeight L x ^ k) μ := by
  have hsum : MemLp (fun x ↦ ∑ i, |L i x|) k μ :=
    memLp_finsetSum (f := fun i x ↦ |L i x|) Finset.univ fun i _ ↦
      (IsGaussian.memLp_dual μ (L i) k (by simp)).norm
  have hmem : MemLp (gaussWeight L) k μ := (memLp_const (1 : ℝ)).add hsum
  have := hmem.integrable_norm_pow'
  refine this.congr (Filter.Eventually.of_forall fun x ↦ ?_)
  simp only [Real.norm_eq_abs, abs_of_nonneg (zero_le_one.trans (one_le_gaussWeight L x))]

omit [CompleteSpace W] [MeasurableSpace W] [BorelSpace W] [SecondCountableTopology W]
  [IsGaussian μ] in
/-- The derivative of the truncated coordinate map, applied to a vector. -/
theorem fderiv_truncCoord_apply (m : ℕ) {n : ℕ} (L : Fin n → StrongDual ℝ W) (x w : W) :
    fderiv ℝ (truncCoord m L) x w =
      ∑ i, (deriv (cutoff m) (L i x) * L i w) • Pi.single i (1 : ℝ) := by
  have hd : ∀ i, DifferentiableAt ℝ (fun x ↦ cutoff m (L i x)) x := fun i ↦
    ((cutoff_contDiff m).differentiable one_ne_zero (L i x)).comp x (L i).differentiableAt
  change fderiv ℝ (fun x (i : Fin n) ↦ cutoff m (L i x)) x w = _
  rw [fderiv_pi hd]
  ext j
  rw [ContinuousLinearMap.pi_apply, Finset.sum_apply]
  have hcomp : (fun x ↦ cutoff m (L j x)) = cutoff m ∘ L j := rfl
  rw [hcomp, fderiv_comp x ((cutoff_contDiff m).differentiable one_ne_zero _)
    (L j).differentiableAt, (L j).fderiv, ContinuousLinearMap.comp_apply, fderiv_eq_smul_deriv,
    smul_eq_mul]
  simp only [mul_comm, Pi.smul_apply, Pi.single_apply, smul_eq_mul, ite_mul, one_mul, zero_mul,
    Finset.sum_ite_eq, Finset.mem_univ, ↓reduceIte]

/-- **Chain rule for truncated cylindrical functionals**. -/
theorem mderiv_comp_truncCoord {n : ℕ} (f : (Fin n → ℝ) → ℝ) (hf : ContDiff ℝ 1 f) (m : ℕ)
    (L : Fin n → StrongDual ℝ W) (x : W) :
    mderiv μ (fun y ↦ f (truncCoord m L y)) x =
      ∑ i, (fderiv ℝ f (truncCoord m L x) (Pi.single i 1) * deriv (cutoff m) (L i x)) •
        ofDual μ (L i) := by
  apply ext_inner_right ℝ
  intro v
  rw [inner_mderiv, Submodule.coe_inner, Submodule.coe_sum, sum_inner]
  simp only [Submodule.coe_smul, real_inner_smul_left]
  simp_rw [← Submodule.coe_inner, ← apply_inclusion]
  have hcomp : (fun y ↦ f (truncCoord m L y)) = f ∘ truncCoord m L := rfl
  rw [hcomp, fderiv_comp x (hf.differentiable one_ne_zero _)
    ((contDiff_truncCoord m L).differentiable one_ne_zero _), ContinuousLinearMap.comp_apply,
    fderiv_truncCoord_apply, map_sum]
  simp_rw [map_smul, smul_eq_mul]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  ring

/-- The partial derivatives are bounded by the operator norm of the derivative. -/
theorem abs_fderiv_single_le {n : ℕ} (f : (Fin n → ℝ) → ℝ) (y : Fin n → ℝ) (i : Fin n) :
    |fderiv ℝ f y (Pi.single i 1)| ≤ ‖fderiv ℝ f y‖ := by
  rw [← Real.norm_eq_abs]
  refine (ContinuousLinearMap.le_opNorm _ _).trans ?_
  refine mul_le_of_le_one_right (norm_nonneg _) ?_
  rw [pi_norm_le_iff_of_nonneg zero_le_one]
  intro j
  by_cases hij : j = i <;> simp [hij]

/-- Pointwise bound for the Malliavin derivative of a truncated cylindrical functional, in
terms of a dominating function `φ ≥ ‖f'‖`. -/
theorem norm_mderiv_comp_truncCoord_le {n : ℕ} {f : (Fin n → ℝ) → ℝ} (hf : ContDiff ℝ 1 f)
    {φ : (Fin n → ℝ) → ℝ} (hφ : ∀ y, ‖fderiv ℝ f y‖ ≤ φ y) (m : ℕ)
    (L : Fin n → StrongDual ℝ W) (x : W) :
    ‖mderiv μ (fun y ↦ f (truncCoord m L y)) x‖ ≤
      φ (truncCoord m L x) * ∑ i, ‖ofDual μ (L i)‖ := by
  rw [mderiv_comp_truncCoord μ f hf m L x]
  refine (norm_sum_le _ _).trans ?_
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun i _ ↦ ?_
  rw [norm_smul, Real.norm_eq_abs, abs_mul]
  have h1 : |fderiv ℝ f (truncCoord m L x) (Pi.single i 1)| ≤ φ (truncCoord m L x) :=
    (abs_fderiv_single_le f _ i).trans (hφ _)
  have h0 : 0 ≤ φ (truncCoord m L x) := (abs_nonneg _).trans h1
  calc |fderiv ℝ f (truncCoord m L x) (Pi.single i 1)| * |deriv (cutoff m) (L i x)| *
        ‖ofDual μ (L i)‖
      ≤ φ (truncCoord m L x) * 1 * ‖ofDual μ (L i)‖ := by
        gcongr
        exact abs_deriv_cutoff_le m _
    _ = φ (truncCoord m L x) * ‖ofDual μ (L i)‖ := by ring

/-- Pointwise bound for the Malliavin derivative of a cylindrical functional, in terms of a
dominating function `φ ≥ ‖f'‖`. -/
theorem norm_mderiv_cylinder_le {n : ℕ} {f : (Fin n → ℝ) → ℝ} (hf : ContDiff ℝ 1 f)
    {φ : (Fin n → ℝ) → ℝ} (hφ : ∀ y, ‖fderiv ℝ f y‖ ≤ φ y) (L : Fin n → StrongDual ℝ W)
    (x : W) :
    ‖mderiv μ (fun y ↦ f (fun i ↦ L i y)) x‖ ≤ φ (fun i ↦ L i x) * ∑ i, ‖ofDual μ (L i)‖ := by
  rw [mderiv_cylindrical μ f L x (hf.differentiable one_ne_zero _)]
  refine (norm_sum_le _ _).trans ?_
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun i _ ↦ ?_
  rw [norm_smul, Real.norm_eq_abs]
  have h1 : |fderiv ℝ f (fun i ↦ L i x) (Pi.single i 1)| ≤ φ (fun i ↦ L i x) :=
    (abs_fderiv_single_le f _ i).trans (hφ _)
  gcongr

/-- The Malliavin derivative of a `C¹` cylindrical functional is continuous. -/
theorem continuous_mderiv_cylinder {n : ℕ} {f : (Fin n → ℝ) → ℝ} (hf : ContDiff ℝ 1 f)
    (L : Fin n → StrongDual ℝ W) :
    Continuous (mderiv μ (fun y ↦ f (fun i ↦ L i y))) := by
  have h : mderiv μ (fun y ↦ f (fun i ↦ L i y)) =
      fun x ↦ ∑ i, fderiv ℝ f (fun i ↦ L i x) (Pi.single i 1) • ofDual μ (L i) := by
    funext x
    exact mderiv_cylindrical μ f L x (hf.differentiable one_ne_zero _)
  rw [h]
  refine continuous_finsetSum _ fun i _ ↦ ?_
  have hc : Continuous fun x ↦ fderiv ℝ f (fun i ↦ L i x) (Pi.single i (1 : ℝ)) :=
    ((hf.continuous_fderiv one_ne_zero).comp (continuous_pi fun i ↦ (L i).continuous)).clm_apply
      continuous_const
  exact hc.smul continuous_const

/-! ### The dominated theorem

The general statement: `f ∘ L ∈ 𝔻₁,₂` as soon as `|f|` and `‖f'‖` are dominated by some
`φ : ℝⁿ → ℝ` such that `φ (truncCoord m L x)` and `φ (L x)` are dominated by a single
square-integrable `ψ : W → ℝ`. -/

omit [NormedAddCommGroup W] [NormedSpace ℝ W] [CompleteSpace W] [BorelSpace W]
  [SecondCountableTopology W] [IsGaussian μ] in
/-- A measurable function dominated by a square-integrable function is in `L²`. -/
theorem memLp_of_le_of_integrable_sq {E : Type*} [NormedAddCommGroup E] {g : W → E}
    (hg : AEStronglyMeasurable g μ) {ψ : W → ℝ} (hint : Integrable (fun x ↦ ψ x ^ 2) μ)
    (h : ∀ x, ‖g x‖ ≤ ψ x) : MemLp g 2 μ := by
  refine (memLp_two_iff_integrable_sq_norm hg).mpr ?_
  refine hint.mono' (hg.norm.pow 2) (Filter.Eventually.of_forall fun x ↦ ?_)
  rw [Real.norm_eq_abs, abs_pow, abs_norm]
  exact pow_le_pow_left₀ (norm_nonneg _) (h x) 2

omit [CompleteSpace W] [SecondCountableTopology W] [IsGaussian μ] in
/-- A dominated `C¹` cylindrical functional is square integrable. -/
theorem memLp_cylinder_of_dominated {n : ℕ} {f : (Fin n → ℝ) → ℝ} (hf : ContDiff ℝ 1 f)
    (L : Fin n → StrongDual ℝ W) {φ : (Fin n → ℝ) → ℝ} {ψ : W → ℝ} (hφf : ∀ y, |f y| ≤ φ y)
    (hψ' : ∀ x, φ (fun i ↦ L i x) ≤ ψ x) (hint : Integrable (fun x ↦ ψ x ^ 2) μ) :
    MemLp (fun x ↦ f (fun i ↦ L i x)) 2 μ :=
  memLp_of_le_of_integrable_sq μ
    (hf.continuous.comp (continuous_pi fun i ↦ (L i).continuous)).aestronglyMeasurable hint
    fun x ↦ (Real.norm_eq_abs _).le.trans ((hφf _).trans (hψ' x))

/-- The Malliavin derivative of a `C¹` cylindrical functional with dominated derivative is
square integrable. -/
theorem memLp_mderiv_cylinder_of_dominated {n : ℕ} {f : (Fin n → ℝ) → ℝ} (hf : ContDiff ℝ 1 f)
    (L : Fin n → StrongDual ℝ W) {φ : (Fin n → ℝ) → ℝ} {ψ : W → ℝ}
    (hφf' : ∀ y, ‖fderiv ℝ f y‖ ≤ φ y) (hψ' : ∀ x, φ (fun i ↦ L i x) ≤ ψ x)
    (hint : Integrable (fun x ↦ ψ x ^ 2) μ) :
    MemLp (mderiv μ (fun y ↦ f (fun i ↦ L i y))) 2 μ :=
  memLp_of_le_of_integrable_sq μ (continuous_mderiv_cylinder μ hf L).aestronglyMeasurable
    (ψ := fun x ↦ ψ x * ∑ i, ‖ofDual μ (L i)‖)
    (by simpa [mul_pow] using hint.mul_const ((∑ i, ‖ofDual μ (L i)‖) ^ 2)) fun x ↦
    (norm_mderiv_cylinder_le μ hf hφf' L x).trans
      (mul_le_mul_of_nonneg_right (hψ' x) (Finset.sum_nonneg fun _ _ ↦ norm_nonneg _))

/-- **Dominated cylindrical functionals lie in `𝔻₁,₂`**, and the closed Malliavin derivative is
the classical one: if `f` is `C¹` with `|f|, ‖f'‖ ≤ φ`, and `φ (truncCoord m L x)`,
`φ (L x)` are bounded by a square-integrable `ψ x`, then `x ↦ f (L₁ x, …, Lₙ x)` belongs to the
domain of the closure, with derivative `∑ᵢ ∂ᵢ f(L x) • ofDual Lᵢ`. -/
theorem cylinder_mem_domD12_of_dominated {n : ℕ} {f : (Fin n → ℝ) → ℝ} (hf : ContDiff ℝ 1 f)
    (L : Fin n → StrongDual ℝ W) {φ : (Fin n → ℝ) → ℝ} {ψ : W → ℝ}
    (hφf : ∀ y, |f y| ≤ φ y) (hφf' : ∀ y, ‖fderiv ℝ f y‖ ≤ φ y)
    (hψ : ∀ m x, φ (truncCoord m L x) ≤ ψ x) (hψ' : ∀ x, φ (fun i ↦ L i x) ≤ ψ x)
    (hint : Integrable (fun x ↦ ψ x ^ 2) μ) :
    (memLp_cylinder_of_dominated μ hf L hφf hψ' hint).toLp _ ∈ domD12 μ ∧
      mderivClosure μ ((memLp_cylinder_of_dominated μ hf L hφf hψ' hint).toLp _) =
        (memLp_mderiv_cylinder_of_dominated μ hf L hφf' hψ' hint).toLp _ := by
  set Fm : ∀ m : ℕ, IsSmoothBounded (fun x ↦ f (truncCoord m L x)) :=
    fun m ↦ isSmoothBounded_comp_truncCoord hf m L with hFm
  have hlim : ∀ x, Tendsto (fun m ↦ truncCoord m L x) atTop (𝓝 (fun i ↦ L i x)) := fun x ↦
    tendsto_pi_nhds.mpr fun i ↦ tendsto_cutoff (L i x)
  have hψ0 : ∀ x, 0 ≤ ψ x := fun x ↦ (abs_nonneg _).trans ((hφf _).trans (hψ' x))
  refine mem_domD12_of_tendsto μ (F := fun m ↦ (Fm m).toLp μ) (fun m ↦ (Fm m).toLp_mem_domD12 μ)
    ?_ ?_
  · refine tendsto_toLp_of_dominated (fun m ↦ (Fm m).memLp μ 2)
      (memLp_cylinder_of_dominated μ hf L hφf hψ' hint)
      (bound := fun x ↦ 2 ^ 2 * ψ x ^ 2) (hint.const_mul _)
      (fun m ↦ Eventually.of_forall fun x ↦ ?_) (Eventually.of_forall fun x ↦ ?_)
    · have h1 : |f (truncCoord m L x)| ≤ ψ x := (hφf _).trans (hψ m x)
      have h2 : |f (fun i ↦ L i x)| ≤ ψ x := (hφf _).trans (hψ' x)
      rw [Real.norm_eq_abs, ← mul_pow]
      gcongr
      calc |f (truncCoord m L x) - f (fun i ↦ L i x)|
          ≤ |f (truncCoord m L x)| + |f (fun i ↦ L i x)| := abs_sub _ _
        _ ≤ ψ x + ψ x := add_le_add h1 h2
        _ = 2 * ψ x := by ring
    · exact (hf.continuous.tendsto _).comp (hlim x)
  · simp_rw [mderivClosure_toLp]
    unfold IsSmoothBounded.mderivLp
    refine tendsto_toLp_of_dominated (fun m ↦ (Fm m).memLp_mderiv μ 2)
      (memLp_mderiv_cylinder_of_dominated μ hf L hφf' hψ' hint)
      (bound := fun x ↦ (2 * ∑ i, ‖ofDual μ (L i)‖) ^ 2 * ψ x ^ 2) (hint.const_mul _)
      (fun m ↦ Eventually.of_forall fun x ↦ ?_) (Eventually.of_forall fun x ↦ ?_)
    · have hK : 0 ≤ ∑ i, ‖ofDual μ (L i)‖ := Finset.sum_nonneg fun _ _ ↦ norm_nonneg _
      have h1 := (norm_mderiv_comp_truncCoord_le μ hf hφf' m L x).trans
        (mul_le_mul_of_nonneg_right (hψ m x) hK)
      have h2 := (norm_mderiv_cylinder_le μ hf hφf' L x).trans
        (mul_le_mul_of_nonneg_right (hψ' x) hK)
      rw [← mul_pow]
      gcongr
      calc ‖mderiv μ (fun y ↦ f (truncCoord m L y)) x - mderiv μ (fun y ↦ f (fun i ↦ L i y)) x‖
          ≤ ‖mderiv μ (fun y ↦ f (truncCoord m L y)) x‖ +
              ‖mderiv μ (fun y ↦ f (fun i ↦ L i y)) x‖ := norm_sub_le _ _
        _ ≤ ψ x * ∑ i, ‖ofDual μ (L i)‖ + ψ x * ∑ i, ‖ofDual μ (L i)‖ := add_le_add h1 h2
        _ = 2 * (∑ i, ‖ofDual μ (L i)‖) * ψ x := by ring
    · rw [mderiv_cylindrical μ f L x (hf.differentiable one_ne_zero _)]
      simp_rw [mderiv_comp_truncCoord μ f hf _ L x]
      refine tendsto_finsetSum _ fun i _ ↦ ?_
      refine Tendsto.smul_const ?_ _
      have hfd : Tendsto (fun m ↦ fderiv ℝ f (truncCoord m L x) (Pi.single i 1)) atTop
          (𝓝 (fderiv ℝ f (fun i ↦ L i x) (Pi.single i 1))) := by
        have hc : Continuous fun y ↦ fderiv ℝ f y (Pi.single i (1 : ℝ)) :=
          (hf.continuous_fderiv one_ne_zero).clm_apply continuous_const
        exact (hc.tendsto _).comp (hlim x)
      simpa using hfd.mul (tendsto_deriv_cutoff (L i x))

/-! ### Polynomial growth -/

omit [CompleteSpace W] [MeasurableSpace W] [BorelSpace W] [SecondCountableTopology W] in
/-- The growth weight `C (1 + ‖y‖)ᵏ` of the truncated coordinates is dominated by the Gaussian
weight. -/
theorem growth_truncCoord_le {n k : ℕ} {C : ℝ} (hC : 0 ≤ C) (L : Fin n → StrongDual ℝ W)
    (m : ℕ) (x : W) :
    C * (1 + ‖truncCoord m L x‖) ^ k ≤ C * gaussWeight L x ^ k := by
  gcongr
  exact (add_le_add_right (norm_truncCoord_le_norm m L x) 1).trans
    (one_add_norm_le_gaussWeight L x)

omit [CompleteSpace W] [MeasurableSpace W] [BorelSpace W] [SecondCountableTopology W] in
/-- The growth weight `C (1 + ‖y‖)ᵏ` of the coordinates is dominated by the Gaussian weight. -/
theorem growth_coord_le {n k : ℕ} {C : ℝ} (hC : 0 ≤ C) (L : Fin n → StrongDual ℝ W) (x : W) :
    C * (1 + ‖fun i ↦ L i x‖) ^ k ≤ C * gaussWeight L x ^ k := by
  gcongr
  exact one_add_norm_le_gaussWeight L x

omit [CompleteSpace W] [SecondCountableTopology W] in
/-- The squared Gaussian growth weight is integrable. -/
theorem integrable_growth_sq {n k : ℕ} (C : ℝ) (L : Fin n → StrongDual ℝ W) :
    Integrable (fun x ↦ (C * gaussWeight L x ^ k) ^ 2) μ := by
  simpa [mul_pow, ← pow_mul, mul_comm k 2] using
    (integrable_gaussWeight_pow μ L (2 * k)).const_mul (C ^ 2)

omit [CompleteSpace W] [SecondCountableTopology W] in
/-- A `C¹` cylindrical functional of polynomial growth is square integrable. -/
theorem memLp_cylinder_growth {n k : ℕ} {f : (Fin n → ℝ) → ℝ} (hf : ContDiff ℝ 1 f)
    {C : ℝ} (hC : 0 ≤ C) (hfg : ∀ y, |f y| ≤ C * (1 + ‖y‖) ^ k) (L : Fin n → StrongDual ℝ W) :
    MemLp (fun x ↦ f (fun i ↦ L i x)) 2 μ :=
  memLp_cylinder_of_dominated μ hf L hfg (growth_coord_le hC L) (integrable_growth_sq μ C L)

/-- The Malliavin derivative of a `C¹` cylindrical functional whose derivative has polynomial
growth is square integrable. -/
theorem memLp_mderiv_cylinder_growth {n k : ℕ} {f : (Fin n → ℝ) → ℝ} (hf : ContDiff ℝ 1 f)
    {C : ℝ} (hC : 0 ≤ C) (hfg' : ∀ y, ‖fderiv ℝ f y‖ ≤ C * (1 + ‖y‖) ^ k)
    (L : Fin n → StrongDual ℝ W) :
    MemLp (mderiv μ (fun y ↦ f (fun i ↦ L i y))) 2 μ :=
  memLp_mderiv_cylinder_of_dominated μ hf L hfg' (growth_coord_le hC L)
    (integrable_growth_sq μ C L)

/-- **Cylindrical functionals of polynomial growth lie in `𝔻₁,₂`**, and the closed Malliavin
derivative is the classical one: if `f` is `C¹` with `|f|` and `‖f'‖` of polynomial growth,
then `x ↦ f (L₁ x, …, Lₙ x)` belongs to the domain of the closure, with derivative
`∑ᵢ ∂ᵢ f(L x) • ofDual Lᵢ`. -/
theorem cylinder_growth_mem_domD12 {n k : ℕ} {f : (Fin n → ℝ) → ℝ} (hf : ContDiff ℝ 1 f)
    {C : ℝ} (hC : 0 ≤ C) (hfg : ∀ y, |f y| ≤ C * (1 + ‖y‖) ^ k)
    (hfg' : ∀ y, ‖fderiv ℝ f y‖ ≤ C * (1 + ‖y‖) ^ k) (L : Fin n → StrongDual ℝ W) :
    (memLp_cylinder_growth μ hf hC hfg L).toLp _ ∈ domD12 μ ∧
      mderivClosure μ ((memLp_cylinder_growth μ hf hC hfg L).toLp _) =
        (memLp_mderiv_cylinder_growth μ hf hC hfg' L).toLp _ :=
  cylinder_mem_domD12_of_dominated μ hf L hfg hfg' (growth_truncCoord_le hC L)
    (growth_coord_le hC L) (integrable_growth_sq μ C L)

/-! ### Exponential growth

By Fernique's theorem `x ↦ exp (a ‖x‖)` is integrable for every `a`, so the same argument
covers `C¹` functions with `|f|, ‖f'‖ ≤ C exp (c ‖y‖)`, such as exponentials of Brownian
coordinates. -/

/-- **Fernique, linear form**: `exp (a ‖x‖)` is integrable for every Gaussian measure. -/
theorem integrable_exp_mul_norm (a : ℝ) : Integrable (fun x ↦ Real.exp (a * ‖x‖)) μ := by
  obtain ⟨C, hC, hint⟩ := IsGaussian.exists_integrable_exp_sq μ
  refine (hint.const_mul (Real.exp (a ^ 2 / (4 * C)))).mono'
    (by fun_prop) (Filter.Eventually.of_forall fun x ↦ ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg (Real.exp_nonneg _), ← Real.exp_add, Real.exp_le_exp]
  have h : 0 ≤ (2 * C * ‖x‖ - a) ^ 2 := sq_nonneg _
  have hC' : 0 < 4 * C := by positivity
  rw [← sub_nonneg]
  calc (0 : ℝ) = (2 * C * ‖x‖ - a) ^ 2 / (4 * C) - (2 * C * ‖x‖ - a) ^ 2 / (4 * C) := by ring
    _ ≤ (2 * C * ‖x‖ - a) ^ 2 / (4 * C) := by
        rw [sub_le_self_iff]
        positivity
    _ = a ^ 2 / (4 * C) + C * ‖x‖ ^ 2 - a * ‖x‖ := by
        field_simp
        ring

omit [CompleteSpace W] [MeasurableSpace W] [BorelSpace W] [SecondCountableTopology W]
  [IsGaussian μ] in
/-- The coordinates are bounded by `(∑ᵢ ‖Lᵢ‖) ‖x‖`. -/
theorem norm_coord_le {n : ℕ} (L : Fin n → StrongDual ℝ W) (x : W) :
    ‖fun i ↦ L i x‖ ≤ (∑ i, ‖L i‖) * ‖x‖ := by
  rw [pi_norm_le_iff_of_nonneg (by positivity)]
  intro i
  refine ((L i).le_opNorm x).trans (mul_le_mul_of_nonneg_right ?_ (norm_nonneg _))
  exact Finset.single_le_sum (fun j _ ↦ norm_nonneg (L j)) (Finset.mem_univ i)

omit [CompleteSpace W] [MeasurableSpace W] [BorelSpace W] [SecondCountableTopology W] in
/-- The exponential weight of the truncated coordinates is dominated by
`C exp (c (∑ᵢ ‖Lᵢ‖) ‖x‖)`. -/
theorem expGrowth_truncCoord_le {n : ℕ} {C c : ℝ} (hC : 0 ≤ C) (hc : 0 ≤ c)
    (L : Fin n → StrongDual ℝ W) (m : ℕ) (x : W) :
    C * Real.exp (c * ‖truncCoord m L x‖) ≤ C * Real.exp (c * ((∑ i, ‖L i‖) * ‖x‖)) := by
  gcongr
  exact (norm_truncCoord_le_norm m L x).trans (norm_coord_le L x)

omit [CompleteSpace W] [MeasurableSpace W] [BorelSpace W] [SecondCountableTopology W] in
/-- The exponential weight of the coordinates is dominated by `C exp (c (∑ᵢ ‖Lᵢ‖) ‖x‖)`. -/
theorem expGrowth_coord_le {n : ℕ} {C c : ℝ} (hC : 0 ≤ C) (hc : 0 ≤ c)
    (L : Fin n → StrongDual ℝ W) (x : W) :
    C * Real.exp (c * ‖fun i ↦ L i x‖) ≤ C * Real.exp (c * ((∑ i, ‖L i‖) * ‖x‖)) := by
  gcongr
  exact norm_coord_le L x

/-- The squared exponential weight is integrable. -/
theorem integrable_expGrowth_sq (C c K : ℝ) :
    Integrable (fun x ↦ (C * Real.exp (c * (K * ‖x‖))) ^ 2) μ := by
  refine ((integrable_exp_mul_norm μ (2 * (c * K))).const_mul (C ^ 2)).congr
    (Filter.Eventually.of_forall fun x ↦ ?_)
  have h : Real.exp (2 * (c * K) * ‖x‖) = Real.exp (c * (K * ‖x‖)) ^ 2 := by
    rw [sq, ← Real.exp_add]
    congr 1
    ring
  simp only [h, mul_pow]

/-- A `C¹` cylindrical functional of exponential growth is square integrable. -/
theorem memLp_cylinder_expGrowth {n : ℕ} {f : (Fin n → ℝ) → ℝ} (hf : ContDiff ℝ 1 f)
    {C c : ℝ} (hC : 0 ≤ C) (hc : 0 ≤ c) (hfg : ∀ y, |f y| ≤ C * Real.exp (c * ‖y‖))
    (L : Fin n → StrongDual ℝ W) :
    MemLp (fun x ↦ f (fun i ↦ L i x)) 2 μ :=
  memLp_cylinder_of_dominated μ hf L (ψ := fun x ↦ C * Real.exp (c * ((∑ i, ‖L i‖) * ‖x‖)))
    hfg (expGrowth_coord_le hC hc L) (integrable_expGrowth_sq μ C c _)

/-- The Malliavin derivative of a `C¹` cylindrical functional whose derivative has exponential
growth is square integrable. -/
theorem memLp_mderiv_cylinder_expGrowth {n : ℕ} {f : (Fin n → ℝ) → ℝ} (hf : ContDiff ℝ 1 f)
    {C c : ℝ} (hC : 0 ≤ C) (hc : 0 ≤ c) (hfg' : ∀ y, ‖fderiv ℝ f y‖ ≤ C * Real.exp (c * ‖y‖))
    (L : Fin n → StrongDual ℝ W) :
    MemLp (mderiv μ (fun y ↦ f (fun i ↦ L i y))) 2 μ :=
  memLp_mderiv_cylinder_of_dominated μ hf L
    (ψ := fun x ↦ C * Real.exp (c * ((∑ i, ‖L i‖) * ‖x‖))) hfg' (expGrowth_coord_le hC hc L)
    (integrable_expGrowth_sq μ C c _)

/-- **Cylindrical functionals of exponential growth lie in `𝔻₁,₂`**, with the classical
derivative. -/
theorem cylinder_expGrowth_mem_domD12 {n : ℕ} {f : (Fin n → ℝ) → ℝ} (hf : ContDiff ℝ 1 f)
    {C c : ℝ} (hC : 0 ≤ C) (hc : 0 ≤ c) (hfg : ∀ y, |f y| ≤ C * Real.exp (c * ‖y‖))
    (hfg' : ∀ y, ‖fderiv ℝ f y‖ ≤ C * Real.exp (c * ‖y‖)) (L : Fin n → StrongDual ℝ W) :
    (memLp_cylinder_expGrowth μ hf hC hc hfg L).toLp _ ∈ domD12 μ ∧
      mderivClosure μ ((memLp_cylinder_expGrowth μ hf hC hc hfg L).toLp _) =
        (memLp_mderiv_cylinder_expGrowth μ hf hC hc hfg' L).toLp _ :=
  cylinder_mem_domD12_of_dominated μ hf L (ψ := fun x ↦ C * Real.exp (c * ((∑ i, ‖L i‖) * ‖x‖)))
    hfg hfg' (expGrowth_truncCoord_le hC hc L) (expGrowth_coord_le hC hc L)
    (integrable_expGrowth_sq μ C c _)

end Growth

section OneCoord

/-! ### Functions of one coordinate

For `g : ℝ → ℝ` of class `C¹`, the cylindrical function `y ↦ g (y 0)` on `ℝ¹` has derivative
`g' (y 0) • proj 0`; exponential bounds on `g, g'` transfer to it. -/

variable {g : ℝ → ℝ}

theorem contDiff_oneCoord (hg : ContDiff ℝ 1 g) :
    ContDiff ℝ 1 (fun y : Fin 1 → ℝ ↦ g (y 0)) :=
  hg.comp (contDiff_apply ℝ ℝ 0)

theorem abs_oneCoord_le {C c : ℝ} (hC : 0 ≤ C) (hc : 0 ≤ c)
    (hg : ∀ x, |g x| ≤ C * Real.exp (c * |x|)) (y : Fin 1 → ℝ) :
    |g (y 0)| ≤ C * Real.exp (c * ‖y‖) := by
  refine (hg _).trans ?_
  gcongr
  exact (Real.norm_eq_abs _).symm.le.trans (norm_le_pi_norm y 0)

theorem fderiv_oneCoord (hg : ContDiff ℝ 1 g) (y : Fin 1 → ℝ) :
    fderiv ℝ (fun y : Fin 1 → ℝ ↦ g (y 0)) y =
      deriv g (y 0) • ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 1 ↦ ℝ) 0 := by
  have h : HasFDerivAt (g ∘ fun y : Fin 1 → ℝ ↦ y 0)
      (deriv g (y 0) • ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 1 ↦ ℝ) 0) y :=
    (hg.differentiable one_ne_zero (y 0)).hasDerivAt.comp_hasFDerivAt y (hasFDerivAt_apply 0 y)
  exact h.fderiv

theorem norm_proj_zero_le : ‖ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 1 ↦ ℝ) 0‖ ≤ 1 :=
  ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun z ↦ by
    rw [one_mul, ContinuousLinearMap.proj_apply]
    exact norm_le_pi_norm z 0

theorem norm_fderiv_oneCoord_le (hg : ContDiff ℝ 1 g) {C c : ℝ} (hC : 0 ≤ C) (hc : 0 ≤ c)
    (hg' : ∀ x, |deriv g x| ≤ C * Real.exp (c * |x|)) (y : Fin 1 → ℝ) :
    ‖fderiv ℝ (fun y : Fin 1 → ℝ ↦ g (y 0)) y‖ ≤ C * Real.exp (c * ‖y‖) := by
  rw [fderiv_oneCoord hg, norm_smul, Real.norm_eq_abs]
  calc |deriv g (y 0)| * ‖ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 1 ↦ ℝ) 0‖
      ≤ (C * Real.exp (c * ‖y‖)) * 1 := by
        gcongr
        · refine (hg' _).trans ?_
          gcongr
          exact (Real.norm_eq_abs _).symm.le.trans (norm_le_pi_norm y 0)
        · exact norm_proj_zero_le
    _ = C * Real.exp (c * ‖y‖) := mul_one _

/-! The exponential. -/

theorem abs_exp_le_exp_abs (x : ℝ) : |Real.exp x| ≤ 1 * Real.exp (1 * |x|) := by
  rw [abs_of_pos (Real.exp_pos _), one_mul, one_mul]
  exact Real.exp_le_exp.mpr (le_abs_self x)

theorem abs_deriv_exp_le_exp_abs (x : ℝ) : |deriv Real.exp x| ≤ 1 * Real.exp (1 * |x|) := by
  rw [Real.deriv_exp]
  exact abs_exp_le_exp_abs x

/-! Polynomials: `|p(x)| ≤ (∑ᵢ |aᵢ|) exp (deg p · |x|)`. -/

theorem abs_pow_le_exp_mul_abs (x : ℝ) {i n : ℕ} (hi : i ≤ n) :
    |x| ^ i ≤ Real.exp (n * |x|) := by
  calc |x| ^ i ≤ Real.exp |x| ^ i := by
        gcongr
        exact (le_add_of_nonneg_right zero_le_one).trans (Real.add_one_le_exp |x|)
    _ = Real.exp (i * |x|) := by rw [← Real.exp_nat_mul]
    _ ≤ Real.exp (n * |x|) := by
        gcongr

theorem contDiff_polynomial_eval (p : Polynomial ℝ) : ContDiff ℝ 1 (fun x ↦ p.eval x) := by
  simpa [Polynomial.aeval_def, Polynomial.eval₂_eq_eval_map] using p.contDiff_aeval (𝕜 := ℝ) 1

/-- A polynomial is dominated by `(∑ᵢ |aᵢ|) exp (n |x|)` whenever `deg p ≤ n`. -/
theorem abs_polynomial_eval_le (p : Polynomial ℝ) {n : ℕ} (hn : p.natDegree ≤ n) (x : ℝ) :
    |p.eval x| ≤ (∑ i ∈ Finset.range (p.natDegree + 1), |p.coeff i|) * Real.exp (n * |x|) := by
  rw [Polynomial.eval_eq_sum_range, Finset.sum_mul]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun i hi ↦ ?_)
  rw [abs_mul, abs_pow]
  gcongr
  exact abs_pow_le_exp_mul_abs x ((Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)).trans hn)

theorem abs_polynomial_deriv_le (p : Polynomial ℝ) {n : ℕ} (hn : p.natDegree ≤ n) (x : ℝ) :
    |deriv (fun x ↦ p.eval x) x| ≤
      (∑ i ∈ Finset.range (p.derivative.natDegree + 1), |p.derivative.coeff i|) *
        Real.exp (n * |x|) := by
  rw [Polynomial.deriv]
  exact abs_polynomial_eval_le p.derivative
    (p.natDegree_derivative_le.trans ((Nat.sub_le _ _).trans hn)) x

/-- The coefficient mass `∑ᵢ |aᵢ|` of a polynomial. -/
noncomputable def coeffMass (p : Polynomial ℝ) : ℝ :=
  ∑ i ∈ Finset.range (p.natDegree + 1), |p.coeff i|

theorem coeffMass_nonneg (p : Polynomial ℝ) : 0 ≤ coeffMass p :=
  Finset.sum_nonneg fun _ _ ↦ abs_nonneg _

/-- A common exponential bound for a polynomial and its derivative. -/
theorem abs_polynomial_eval_le' (p : Polynomial ℝ) (x : ℝ) :
    |p.eval x| ≤ (coeffMass p + coeffMass p.derivative) * Real.exp (p.natDegree * |x|) :=
  (abs_polynomial_eval_le p le_rfl x).trans
    (mul_le_mul_of_nonneg_right (le_add_of_nonneg_right (coeffMass_nonneg _))
      (Real.exp_nonneg _))

theorem abs_polynomial_deriv_le' (p : Polynomial ℝ) (x : ℝ) :
    |deriv (fun x ↦ p.eval x) x| ≤
      (coeffMass p + coeffMass p.derivative) * Real.exp (p.natDegree * |x|) :=
  (abs_polynomial_deriv_le p le_rfl x).trans
    (mul_le_mul_of_nonneg_right (le_add_of_nonneg_left (coeffMass_nonneg _))
      (Real.exp_nonneg _))

/-! The shifted exponential `x ↦ exp (x - c)`. -/

theorem abs_exp_sub_le_exp_abs (c x : ℝ) (hc : 0 ≤ c) :
    |Real.exp (x - c)| ≤ 1 * Real.exp (1 * |x|) := by
  rw [abs_of_pos (Real.exp_pos _), one_mul, one_mul, Real.exp_le_exp]
  linarith [le_abs_self x]

theorem deriv_exp_sub (c : ℝ) : deriv (fun x ↦ Real.exp (x - c)) = fun x ↦ Real.exp (x - c) := by
  funext x
  have h : HasDerivAt (fun x ↦ Real.exp (x - c)) (Real.exp (x - c) * 1) x :=
    ((hasDerivAt_id x).sub_const c).exp
  rw [h.deriv, mul_one]

theorem contDiff_exp_sub (c : ℝ) : ContDiff ℝ 1 (fun x ↦ Real.exp (x - c)) :=
  Real.contDiff_exp.comp (contDiff_id.sub contDiff_const)

/-! The sine and cosine. -/

theorem abs_sin_le_exp_abs (x : ℝ) : |Real.sin x| ≤ 1 * Real.exp (1 * |x|) := by
  rw [one_mul, one_mul]
  exact (Real.abs_sin_le_one x).trans (Real.one_le_exp (abs_nonneg x))

theorem abs_deriv_sin_le_exp_abs (x : ℝ) : |deriv Real.sin x| ≤ 1 * Real.exp (1 * |x|) := by
  rw [Real.deriv_sin, one_mul, one_mul]
  exact (Real.abs_cos_le_one x).trans (Real.one_le_exp (abs_nonneg x))

theorem abs_cos_le_exp_abs (x : ℝ) : |Real.cos x| ≤ 1 * Real.exp (1 * |x|) := by
  rw [one_mul, one_mul]
  exact (Real.abs_cos_le_one x).trans (Real.one_le_exp (abs_nonneg x))

theorem abs_deriv_cos_le_exp_abs (x : ℝ) : |deriv Real.cos x| ≤ 1 * Real.exp (1 * |x|) := by
  rw [Real.deriv_cos, abs_neg, one_mul, one_mul]
  exact (Real.abs_sin_le_one x).trans (Real.one_le_exp (abs_nonneg x))

end OneCoord

/-! ### Brownian coordinates -/

section Brownian

open CameronMartin

variable {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]
  [CompleteSpace W] [MeasurableSpace W] [BorelSpace W]
  [SecondCountableTopology W]
  {P : Measure W} [IsGaussian P] {B : ℝ≥0 → W → ℝ}
  (hB : IsPreBrownianReal B P) (L : ℝ≥0 → StrongDual ℝ W) (hL : ∀ t w, B t w = L t w)

include L hL

omit [CompleteSpace W] [SecondCountableTopology W] [IsGaussian P] in
/-- A dominated `C¹` function of finitely many Brownian coordinates is square integrable. -/
theorem memLp_cylinder_brownian_of_dominated {n : ℕ} {f : (Fin n → ℝ) → ℝ}
    (hf : ContDiff ℝ 1 f) {φ : (Fin n → ℝ) → ℝ} {ψ : W → ℝ} (hφf : ∀ y, |f y| ≤ φ y)
    (t : Fin n → ℝ≥0) (hψ' : ∀ x, φ (fun i ↦ L (t i) x) ≤ ψ x)
    (hint : Integrable (fun x ↦ ψ x ^ 2) P) :
    MemLp (fun w ↦ f (fun i ↦ B (t i) w)) 2 P := by
  have h : (fun w ↦ f (fun i ↦ B (t i) w)) = fun w ↦ f (fun i ↦ L (t i) w) := by
    funext w
    simp only [hL]
  rw [h]
  exact memLp_cylinder_of_dominated P hf _ hφf hψ' hint

omit [CompleteSpace W] [SecondCountableTopology W] [IsGaussian P] in
/-- The partial derivative `∂ᵢ f (B t₁, …, B tₙ)` is square integrable when `f'` is
dominated. -/
theorem memLp_cylinderPartial_of_dominated {n : ℕ} {f : (Fin n → ℝ) → ℝ}
    (hf : ContDiff ℝ 1 f) {φ : (Fin n → ℝ) → ℝ} {ψ : W → ℝ}
    (hφf' : ∀ y, ‖fderiv ℝ f y‖ ≤ φ y) (t : Fin n → ℝ≥0)
    (hψ' : ∀ x, φ (fun i ↦ L (t i) x) ≤ ψ x) (hint : Integrable (fun x ↦ ψ x ^ 2) P)
    (i : Fin n) :
    MemLp (fun w ↦ fderiv ℝ f (fun j ↦ B (t j) w) (Pi.single i 1)) 2 P := by
  have h : (fun w ↦ fderiv ℝ f (fun j ↦ B (t j) w) (Pi.single i 1)) =
      fun w ↦ fderiv ℝ f (fun j ↦ L (t j) w) (Pi.single i 1) := by
    funext w
    simp only [hL]
  rw [h]
  have hc : Continuous fun w ↦ fderiv ℝ f (fun j ↦ L (t j) w) (Pi.single i (1 : ℝ)) :=
    ((hf.continuous_fderiv one_ne_zero).comp (continuous_pi fun j ↦ (L (t j)).continuous)).clm_apply
      continuous_const
  refine memLp_of_le_of_integrable_sq P hc.aestronglyMeasurable hint fun w ↦ ?_
  rw [Real.norm_eq_abs]
  exact (abs_fderiv_single_le f _ i).trans ((hφf' _).trans (hψ' w))

/-- The partial derivative `∂ᵢ f (B t₁, …, B tₙ)` as an element of `L²(P)`, for dominated
`f'`. -/
noncomputable def cylinderPartialD {n : ℕ} {f : (Fin n → ℝ) → ℝ} (hf : ContDiff ℝ 1 f)
    {φ : (Fin n → ℝ) → ℝ} {ψ : W → ℝ} (hφf' : ∀ y, ‖fderiv ℝ f y‖ ≤ φ y) (t : Fin n → ℝ≥0)
    (hψ' : ∀ x, φ (fun i ↦ L (t i) x) ≤ ψ x) (hint : Integrable (fun x ↦ ψ x ^ 2) P)
    (i : Fin n) : Lp ℝ 2 P :=
  (memLp_cylinderPartial_of_dominated L hL hf hφf' t hψ' hint i).toLp _

/-- **Dominated functions of Brownian coordinates lie in `𝔻₁,₂`**, with the closed derivative
`∑ᵢ ∂ᵢ f (B) • ofDual (L tᵢ)`. -/
theorem cylinder_brownian_mem_domD12_of_dominated {n : ℕ} {f : (Fin n → ℝ) → ℝ}
    (hf : ContDiff ℝ 1 f) {φ : (Fin n → ℝ) → ℝ} {ψ : W → ℝ} (hφf : ∀ y, |f y| ≤ φ y)
    (hφf' : ∀ y, ‖fderiv ℝ f y‖ ≤ φ y) (t : Fin n → ℝ≥0)
    (hψ : ∀ m x, φ (truncCoord m (fun i ↦ L (t i)) x) ≤ ψ x)
    (hψ' : ∀ x, φ (fun i ↦ L (t i) x) ≤ ψ x) (hint : Integrable (fun x ↦ ψ x ^ 2) P) :
    (memLp_cylinder_brownian_of_dominated L hL hf hφf t hψ' hint).toLp _ ∈ domD12 P ∧
      mderivClosure P ((memLp_cylinder_brownian_of_dominated L hL hf hφf t hψ' hint).toLp _) =
        ∑ i, smulLp (ofDual P (L (t i))) (cylinderPartialD L hL hf hφf' t hψ' hint i) := by
  have hF : (memLp_cylinder_brownian_of_dominated L hL hf hφf t hψ' hint).toLp _ =
      (memLp_cylinder_of_dominated P hf (fun i ↦ L (t i)) hφf hψ' hint).toLp _ := by
    apply Lp.ext
    filter_upwards [MemLp.coeFn_toLp (memLp_cylinder_brownian_of_dominated L hL hf hφf t hψ' hint),
      MemLp.coeFn_toLp (memLp_cylinder_of_dominated P hf (fun i ↦ L (t i)) hφf hψ' hint)]
      with w h1 h2
    rw [h1, h2]
    simp only [hL]
  obtain ⟨hmem, hder⟩ :=
    cylinder_mem_domD12_of_dominated P hf (fun i ↦ L (t i)) hφf hφf' hψ hψ' hint
  rw [hF]
  refine ⟨hmem, hder.trans ?_⟩
  apply Lp.ext
  have hpart : ∀ᵐ w ∂P, ∀ i : Fin n,
      (smulLp (ofDual P (L (t i))) (cylinderPartialD L hL hf hφf' t hψ' hint i) : W → Space P) w =
        fderiv ℝ f (fun j ↦ L (t j) w) (Pi.single i 1) • ofDual P (L (t i)) :=
    ae_all_iff.2 fun i ↦ by
      filter_upwards [coeFn_smulLp (ofDual P (L (t i)))
          (cylinderPartialD L hL hf hφf' t hψ' hint i),
        MemLp.coeFn_toLp (memLp_cylinderPartial_of_dominated L hL hf hφf' t hψ' hint i)]
        with w h1 h2
      rw [h1, cylinderPartialD, h2]
      simp only [hL]
  filter_upwards [MemLp.coeFn_toLp
      (memLp_mderiv_cylinder_of_dominated P hf (fun i ↦ L (t i)) hφf' hψ' hint),
    Lp.coeFn_finsetSum Finset.univ
      (fun i ↦ smulLp (ofDual P (L (t i))) (cylinderPartialD L hL hf hφf' t hψ' hint i)), hpart]
    with w h1 h2 h3
  rw [h1, h2, Finset.sum_apply]
  simp_rw [h3]
  exact mderiv_cylindrical P f (fun i ↦ L (t i)) w (hf.differentiable one_ne_zero _)

/-- **The textbook time derivative of a dominated function of Brownian coordinates**:
`Dₜ f(B t₁, …, B tₙ) = ∑ᵢ ∂ᵢ f (B t₁, …, B tₙ) · 1_{(0, tᵢ]}(t)` in `L²(ℝ≥0 × W)`. -/
theorem timeDerivative_mderivClosure_cylinder_of_dominated (hgen : IsWienerGenerated B)
    {n : ℕ} {f : (Fin n → ℝ) → ℝ} (hf : ContDiff ℝ 1 f) {φ : (Fin n → ℝ) → ℝ} {ψ : W → ℝ}
    (hφf : ∀ y, |f y| ≤ φ y) (hφf' : ∀ y, ‖fderiv ℝ f y‖ ≤ φ y) (t : Fin n → ℝ≥0)
    (hψ : ∀ m x, φ (truncCoord m (fun i ↦ L (t i)) x) ≤ ψ x)
    (hψ' : ∀ x, φ (fun i ↦ L (t i) x) ≤ ψ x) (hint : Integrable (fun x ↦ ψ x ^ 2) P) :
    timeDerivative hB L hL hgen
        (mderivClosure P ((memLp_cylinder_brownian_of_dominated L hL hf hφf t hψ' hint).toLp _)) =
      ∑ i, tensor (intervalIndicator (t i)) (cylinderPartialD L hL hf hφf' t hψ' hint i) := by
  rw [(cylinder_brownian_mem_domD12_of_dominated L hL hf hφf hφf' t hψ hψ' hint).2]
  have hsum := map_sum (timeDerivative hB L hL hgen).toLinearMap
    (fun i ↦ smulLp (ofDual P (L (t i))) (cylinderPartialD L hL hf hφf' t hψ' hint i))
    Finset.univ
  simp only [LinearIsometry.coe_toLinearMap] at hsum
  rw [hsum]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [timeDerivative_smulLp hB L hL hgen, wienerIntegralEquiv_symm_ofDual hB L hL hgen]

/-! #### Polynomial growth -/

omit [CompleteSpace W] [SecondCountableTopology W] in
/-- A `C¹` function of polynomial growth of finitely many Brownian coordinates is square
integrable. -/
theorem memLp_cylinder_growth_brownian {n k : ℕ} {f : (Fin n → ℝ) → ℝ} (hf : ContDiff ℝ 1 f)
    {C : ℝ} (hC : 0 ≤ C) (hfg : ∀ y, |f y| ≤ C * (1 + ‖y‖) ^ k) (t : Fin n → ℝ≥0) :
    MemLp (fun w ↦ f (fun i ↦ B (t i) w)) 2 P :=
  memLp_cylinder_brownian_of_dominated L hL hf hfg t (growth_coord_le hC _)
    (integrable_growth_sq P C _)

/-- The partial derivative `∂ᵢ f (B t₁, …, B tₙ)` as an element of `L²(P)`, for `f'` of
polynomial growth. -/
noncomputable def cylinderPartialGrowth {n k : ℕ} {f : (Fin n → ℝ) → ℝ} (hf : ContDiff ℝ 1 f)
    {C : ℝ} (hC : 0 ≤ C) (hfg' : ∀ y, ‖fderiv ℝ f y‖ ≤ C * (1 + ‖y‖) ^ k) (t : Fin n → ℝ≥0)
    (i : Fin n) : Lp ℝ 2 P :=
  cylinderPartialD L hL hf hfg' t (growth_coord_le hC _) (integrable_growth_sq P C _) i

/-- **Polynomial-growth functions of Brownian coordinates lie in `𝔻₁,₂`**, with the closed
derivative `∑ᵢ ∂ᵢ f (B) • ofDual (L tᵢ)`. -/
theorem cylinder_growth_brownian_mem_domD12 {n k : ℕ} {f : (Fin n → ℝ) → ℝ}
    (hf : ContDiff ℝ 1 f) {C : ℝ} (hC : 0 ≤ C) (hfg : ∀ y, |f y| ≤ C * (1 + ‖y‖) ^ k)
    (hfg' : ∀ y, ‖fderiv ℝ f y‖ ≤ C * (1 + ‖y‖) ^ k) (t : Fin n → ℝ≥0) :
    (memLp_cylinder_growth_brownian L hL hf hC hfg t).toLp _ ∈ domD12 P ∧
      mderivClosure P ((memLp_cylinder_growth_brownian L hL hf hC hfg t).toLp _) =
        ∑ i, smulLp (ofDual P (L (t i))) (cylinderPartialGrowth L hL hf hC hfg' t i) :=
  cylinder_brownian_mem_domD12_of_dominated L hL hf hfg hfg' t (growth_truncCoord_le hC _)
    (growth_coord_le hC _) (integrable_growth_sq P C _)

/-- **The textbook time derivative of a polynomial-growth function of Brownian coordinates**:
`Dₜ f(B t₁, …, B tₙ) = ∑ᵢ ∂ᵢ f (B t₁, …, B tₙ) · 1_{(0, tᵢ]}(t)` in `L²(ℝ≥0 × W)`. -/
theorem timeDerivative_mderivClosure_cylinder_growth (hgen : IsWienerGenerated B) {n k : ℕ}
    {f : (Fin n → ℝ) → ℝ} (hf : ContDiff ℝ 1 f) {C : ℝ} (hC : 0 ≤ C)
    (hfg : ∀ y, |f y| ≤ C * (1 + ‖y‖) ^ k) (hfg' : ∀ y, ‖fderiv ℝ f y‖ ≤ C * (1 + ‖y‖) ^ k)
    (t : Fin n → ℝ≥0) :
    timeDerivative hB L hL hgen
        (mderivClosure P ((memLp_cylinder_growth_brownian L hL hf hC hfg t).toLp _)) =
      ∑ i, tensor (intervalIndicator (t i)) (cylinderPartialGrowth L hL hf hC hfg' t i) :=
  timeDerivative_mderivClosure_cylinder_of_dominated hB L hL hgen hf hfg hfg' t
    (growth_truncCoord_le hC _) (growth_coord_le hC _) (integrable_growth_sq P C _)

/-! #### Exponential growth -/

/-- A `C¹` function of exponential growth of finitely many Brownian coordinates is square
integrable. -/
theorem memLp_cylinder_expGrowth_brownian {n : ℕ} {f : (Fin n → ℝ) → ℝ} (hf : ContDiff ℝ 1 f)
    {C c : ℝ} (hC : 0 ≤ C) (hc : 0 ≤ c) (hfg : ∀ y, |f y| ≤ C * Real.exp (c * ‖y‖))
    (t : Fin n → ℝ≥0) :
    MemLp (fun w ↦ f (fun i ↦ B (t i) w)) 2 P :=
  memLp_cylinder_brownian_of_dominated L hL hf hfg t
    (ψ := fun x ↦ C * Real.exp (c * ((∑ i, ‖L (t i)‖) * ‖x‖))) (expGrowth_coord_le hC hc _)
    (integrable_expGrowth_sq P C c _)

/-- The partial derivative `∂ᵢ f (B t₁, …, B tₙ)` as an element of `L²(P)`, for `f'` of
exponential growth. -/
noncomputable def cylinderPartialExp {n : ℕ} {f : (Fin n → ℝ) → ℝ} (hf : ContDiff ℝ 1 f)
    {C c : ℝ} (hC : 0 ≤ C) (hc : 0 ≤ c) (hfg' : ∀ y, ‖fderiv ℝ f y‖ ≤ C * Real.exp (c * ‖y‖))
    (t : Fin n → ℝ≥0) (i : Fin n) : Lp ℝ 2 P :=
  cylinderPartialD L hL hf hfg' t (ψ := fun x ↦ C * Real.exp (c * ((∑ i, ‖L (t i)‖) * ‖x‖)))
    (expGrowth_coord_le hC hc _) (integrable_expGrowth_sq P C c _) i

/-- **Exponential-growth functions of Brownian coordinates lie in `𝔻₁,₂`**, with the closed
derivative `∑ᵢ ∂ᵢ f (B) • ofDual (L tᵢ)`. -/
theorem cylinder_expGrowth_brownian_mem_domD12 {n : ℕ} {f : (Fin n → ℝ) → ℝ}
    (hf : ContDiff ℝ 1 f) {C c : ℝ} (hC : 0 ≤ C) (hc : 0 ≤ c)
    (hfg : ∀ y, |f y| ≤ C * Real.exp (c * ‖y‖))
    (hfg' : ∀ y, ‖fderiv ℝ f y‖ ≤ C * Real.exp (c * ‖y‖)) (t : Fin n → ℝ≥0) :
    (memLp_cylinder_expGrowth_brownian L hL hf hC hc hfg t).toLp _ ∈ domD12 P ∧
      mderivClosure P ((memLp_cylinder_expGrowth_brownian L hL hf hC hc hfg t).toLp _) =
        ∑ i, smulLp (ofDual P (L (t i))) (cylinderPartialExp L hL hf hC hc hfg' t i) :=
  cylinder_brownian_mem_domD12_of_dominated L hL hf hfg hfg' t
    (ψ := fun x ↦ C * Real.exp (c * ((∑ i, ‖L (t i)‖) * ‖x‖))) (expGrowth_truncCoord_le hC hc _)
    (expGrowth_coord_le hC hc _) (integrable_expGrowth_sq P C c _)

/-- **The textbook time derivative of an exponential-growth function of Brownian
coordinates**: `Dₜ f(B t₁, …, B tₙ) = ∑ᵢ ∂ᵢ f (B t₁, …, B tₙ) · 1_{(0, tᵢ]}(t)`. -/
theorem timeDerivative_mderivClosure_cylinder_expGrowth (hgen : IsWienerGenerated B) {n : ℕ}
    {f : (Fin n → ℝ) → ℝ} (hf : ContDiff ℝ 1 f) {C c : ℝ} (hC : 0 ≤ C) (hc : 0 ≤ c)
    (hfg : ∀ y, |f y| ≤ C * Real.exp (c * ‖y‖))
    (hfg' : ∀ y, ‖fderiv ℝ f y‖ ≤ C * Real.exp (c * ‖y‖)) (t : Fin n → ℝ≥0) :
    timeDerivative hB L hL hgen
        (mderivClosure P ((memLp_cylinder_expGrowth_brownian L hL hf hC hc hfg t).toLp _)) =
      ∑ i, tensor (intervalIndicator (t i)) (cylinderPartialExp L hL hf hC hc hfg' t i) :=
  timeDerivative_mderivClosure_cylinder_of_dominated hB L hL hgen hf hfg hfg' t
    (ψ := fun x ↦ C * Real.exp (c * ((∑ i, ‖L (t i)‖) * ‖x‖))) (expGrowth_truncCoord_le hC hc _)
    (expGrowth_coord_le hC hc _) (integrable_expGrowth_sq P C c _)

/-! #### Functions of one Brownian coordinate

`g (B T) ∈ 𝔻₁,₂` with `Dₜ g (B T) = g' (B T) 1_{(0, T]}(t)` for `C¹` functions `g` of exponential
growth; in particular `Dₜ exp (B T) = exp (B T) 1_{(0, T]}(t)`. -/

variable {g : ℝ → ℝ}

/-- `g (B T)` is square integrable for `g` of exponential growth. -/
theorem memLp_comp_brownian (hg : ContDiff ℝ 1 g) {C c : ℝ} (hC : 0 ≤ C) (hc : 0 ≤ c)
    (hgb : ∀ x, |g x| ≤ C * Real.exp (c * |x|)) (T : ℝ≥0) :
    MemLp (fun w ↦ g (B T w)) 2 P :=
  memLp_cylinder_expGrowth_brownian L hL (contDiff_oneCoord hg) hC hc (abs_oneCoord_le hC hc hgb)
    (fun _ ↦ T)

/-- The partial derivative of `y ↦ g (y 0)` at the Brownian coordinate is `g' (B T)`. -/
theorem cylinderPartialExp_oneCoord (hg : ContDiff ℝ 1 g) {C c : ℝ} (hC : 0 ≤ C) (hc : 0 ≤ c)
    (hgb' : ∀ x, |deriv g x| ≤ C * Real.exp (c * |x|)) (T : ℝ≥0)
    (hd : MemLp (fun w ↦ deriv g (B T w)) 2 P) :
    cylinderPartialExp (P := P) L hL (contDiff_oneCoord hg) hC hc
        (norm_fderiv_oneCoord_le hg hC hc hgb') (fun _ ↦ T) 0 =
      hd.toLp _ := by
  apply Lp.ext
  filter_upwards [MemLp.coeFn_toLp (memLp_cylinderPartial_of_dominated L hL (contDiff_oneCoord hg)
      (norm_fderiv_oneCoord_le hg hC hc hgb') (fun _ ↦ T) (expGrowth_coord_le hC hc _)
      (integrable_expGrowth_sq P C c _) 0),
    MemLp.coeFn_toLp hd] with w h1 h2
  rw [cylinderPartialExp, cylinderPartialD, h1, h2, fderiv_oneCoord hg]
  simp only [Fin.isValue, smul_apply, ContinuousLinearMap.proj_apply, Pi.single_eq_same,
    smul_eq_mul, mul_one]

/-- **`Dₜ g (B T) = g' (B T) 1_{(0, T]}(t)`** for `C¹` functions `g` of exponential growth. -/
theorem timeDerivative_mderivClosure_comp_brownian (hgen : IsWienerGenerated B)
    (hg : ContDiff ℝ 1 g) {C c : ℝ} (hC : 0 ≤ C) (hc : 0 ≤ c)
    (hgb : ∀ x, |g x| ≤ C * Real.exp (c * |x|)) (hgb' : ∀ x, |deriv g x| ≤ C * Real.exp (c * |x|))
    (T : ℝ≥0) (hd : MemLp (fun w ↦ deriv g (B T w)) 2 P) :
    timeDerivative hB L hL hgen
        (mderivClosure P ((memLp_comp_brownian L hL hg hC hc hgb T).toLp _)) =
      tensor (intervalIndicator T) (hd.toLp _) := by
  have h := timeDerivative_mderivClosure_cylinder_expGrowth hB L hL hgen (contDiff_oneCoord hg)
    hC hc (abs_oneCoord_le hC hc hgb) (norm_fderiv_oneCoord_le hg hC hc hgb') (fun _ ↦ T)
  rw [Fin.sum_univ_one, cylinderPartialExp_oneCoord L hL hg hC hc hgb' T hd] at h
  exact h

/-- `g (B T)` lies in `𝔻₁,₂` for `g` of exponential growth. -/
theorem comp_brownian_mem_domD12 (hg : ContDiff ℝ 1 g) {C c : ℝ} (hC : 0 ≤ C) (hc : 0 ≤ c)
    (hgb : ∀ x, |g x| ≤ C * Real.exp (c * |x|)) (hgb' : ∀ x, |deriv g x| ≤ C * Real.exp (c * |x|))
    (T : ℝ≥0) : (memLp_comp_brownian L hL hg hC hc hgb T).toLp _ ∈ domD12 P :=
  (cylinder_expGrowth_brownian_mem_domD12 L hL (contDiff_oneCoord hg) hC hc
    (abs_oneCoord_le hC hc hgb) (norm_fderiv_oneCoord_le hg hC hc hgb') (fun _ ↦ T)).1

/-- `exp (B T)` is square integrable. -/
theorem memLp_exp_brownian (T : ℝ≥0) : MemLp (fun w ↦ Real.exp (B T w)) 2 P :=
  memLp_comp_brownian L hL Real.contDiff_exp zero_le_one zero_le_one abs_exp_le_exp_abs T

/-- **`exp (B T) ∈ 𝔻₁,₂` with `Dₜ exp (B T) = exp (B T) 1_{(0, T]}(t)`**. -/
theorem timeDerivative_mderivClosure_exp_brownian (hgen : IsWienerGenerated B) (T : ℝ≥0) :
    timeDerivative hB L hL hgen (mderivClosure P ((memLp_exp_brownian L hL T).toLp _)) =
      tensor (intervalIndicator T) ((memLp_exp_brownian L hL T).toLp _) := by
  have h := timeDerivative_mderivClosure_comp_brownian hB L hL hgen Real.contDiff_exp zero_le_one
    zero_le_one abs_exp_le_exp_abs abs_deriv_exp_le_exp_abs T
    (by simpa [Real.deriv_exp] using memLp_exp_brownian L hL T)
  simpa only [Real.deriv_exp] using h

/-! The Wick exponential `exp (B T - T / 2)` (geometric Brownian motion at time `T`). -/

/-- The Wick exponential `exp (B T - T / 2)` is square integrable. -/
theorem memLp_wickExp_brownian (T : ℝ≥0) : MemLp (fun w ↦ Real.exp (B T w - T / 2)) 2 P :=
  memLp_comp_brownian L hL (contDiff_exp_sub (T / 2)) zero_le_one zero_le_one
    (fun x ↦ abs_exp_sub_le_exp_abs (T / 2) x (by positivity)) T

/-- **`Dₜ exp (B T - T / 2) = exp (B T - T / 2) 1_{(0, T]}(t)`**: the Wick exponential is in
`𝔻₁,₂` and reproduces itself under the time derivative. -/
theorem timeDerivative_mderivClosure_wickExp_brownian (hgen : IsWienerGenerated B) (T : ℝ≥0) :
    timeDerivative hB L hL hgen (mderivClosure P ((memLp_wickExp_brownian L hL T).toLp _)) =
      tensor (intervalIndicator T) ((memLp_wickExp_brownian L hL T).toLp _) := by
  have h := timeDerivative_mderivClosure_comp_brownian hB L hL hgen (contDiff_exp_sub (T / 2))
    zero_le_one zero_le_one (fun x ↦ abs_exp_sub_le_exp_abs (T / 2) x (by positivity))
    (fun x ↦ by rw [deriv_exp_sub]; exact abs_exp_sub_le_exp_abs (T / 2) x (by positivity)) T
    (by simpa only [deriv_exp_sub] using memLp_wickExp_brownian L hL T)
  simpa only [deriv_exp_sub] using h

/-! The sine of a Brownian coordinate. -/

/-- `sin (B T)` is square integrable. -/
theorem memLp_sin_brownian (T : ℝ≥0) : MemLp (fun w ↦ Real.sin (B T w)) 2 P :=
  memLp_comp_brownian L hL Real.contDiff_sin zero_le_one zero_le_one abs_sin_le_exp_abs T

omit [CompleteSpace W] [SecondCountableTopology W] in
/-- `cos (B T)` is square integrable. -/
theorem memLp_cos_brownian (T : ℝ≥0) : MemLp (fun w ↦ Real.cos (B T w)) 2 P := by
  have h : (fun w ↦ Real.cos (B T w)) = fun w ↦ Real.cos (L T w) := by
    funext w
    rw [hL]
  rw [h]
  exact MemLp.of_bound (Real.continuous_cos.comp (L T).continuous).aestronglyMeasurable 1
    (Filter.Eventually.of_forall fun w ↦ by
      rw [Real.norm_eq_abs]; exact Real.abs_cos_le_one _)

/-- **`Dₜ sin (B T) = cos (B T) 1_{(0, T]}(t)`**. -/
theorem timeDerivative_mderivClosure_sin_brownian (hgen : IsWienerGenerated B) (T : ℝ≥0) :
    timeDerivative hB L hL hgen (mderivClosure P ((memLp_sin_brownian L hL T).toLp _)) =
      tensor (intervalIndicator T) ((memLp_cos_brownian L hL T).toLp _) := by
  have h := timeDerivative_mderivClosure_comp_brownian hB L hL hgen Real.contDiff_sin
    zero_le_one zero_le_one abs_sin_le_exp_abs abs_deriv_sin_le_exp_abs T
    (by simpa only [Real.deriv_sin] using memLp_cos_brownian L hL T)
  simpa only [Real.deriv_sin] using h

/-- **`Dₜ cos (B T) = -sin (B T) 1_{(0, T]}(t)`**. -/
theorem timeDerivative_mderivClosure_cos_brownian (hgen : IsWienerGenerated B) (T : ℝ≥0) :
    timeDerivative hB L hL hgen (mderivClosure P ((memLp_cos_brownian L hL T).toLp _)) =
      tensor (intervalIndicator T) (-(memLp_sin_brownian L hL T).toLp _) := by
  have hd : MemLp (fun w ↦ deriv Real.cos (B T w)) 2 P := by
    have h := (memLp_sin_brownian (P := P) L hL T).neg
    refine MemLp.ae_eq (Filter.Eventually.of_forall fun w ↦ ?_) h
    change -Real.sin (B T w) = deriv Real.cos (B T w)
    rw [Real.deriv_cos]
  have h := timeDerivative_mderivClosure_comp_brownian hB L hL hgen Real.contDiff_cos
    zero_le_one zero_le_one abs_cos_le_exp_abs abs_deriv_cos_le_exp_abs T hd
  rw [h]
  congr 1
  apply Lp.ext
  filter_upwards [MemLp.coeFn_toLp hd, Lp.coeFn_neg ((memLp_sin_brownian L hL T).toLp _),
    MemLp.coeFn_toLp (memLp_sin_brownian L hL T)] with w h1 h2 h3
  rw [h1, h2, Pi.neg_apply, h3, Real.deriv_cos]

/-- `exp (B T)` lies in `𝔻₁,₂`. -/
theorem exp_brownian_mem_domD12 (T : ℝ≥0) : (memLp_exp_brownian L hL T).toLp _ ∈ domD12 P :=
  comp_brownian_mem_domD12 L hL Real.contDiff_exp zero_le_one zero_le_one abs_exp_le_exp_abs
    abs_deriv_exp_le_exp_abs T

/-! #### Polynomials of a Brownian coordinate -/

/-- `p (B T)` is square integrable for every real polynomial `p`. -/
theorem memLp_polynomial_brownian (p : Polynomial ℝ) (T : ℝ≥0) :
    MemLp (fun w ↦ p.eval (B T w)) 2 P :=
  memLp_comp_brownian L hL (contDiff_polynomial_eval p)
    (add_nonneg (coeffMass_nonneg _) (coeffMass_nonneg _)) (Nat.cast_nonneg _)
    (abs_polynomial_eval_le' p) T

/-- `p' (B T)` is square integrable for every real polynomial `p`. -/
theorem memLp_polynomial_derivative_brownian (p : Polynomial ℝ) (T : ℝ≥0) :
    MemLp (fun w ↦ p.derivative.eval (B T w)) 2 P :=
  memLp_polynomial_brownian L hL p.derivative T

/-- **`Dₜ p (B T) = p' (B T) 1_{(0, T]}(t)`** for every real polynomial `p`; in particular all
polynomials in a Brownian coordinate lie in `𝔻₁,₂`. -/
theorem timeDerivative_mderivClosure_polynomial_brownian (hgen : IsWienerGenerated B)
    (p : Polynomial ℝ) (T : ℝ≥0) :
    timeDerivative hB L hL hgen
        (mderivClosure P ((memLp_polynomial_brownian L hL p T).toLp _)) =
      tensor (intervalIndicator T) ((memLp_polynomial_derivative_brownian L hL p T).toLp _) := by
  have h := timeDerivative_mderivClosure_comp_brownian hB L hL hgen (contDiff_polynomial_eval p)
    (add_nonneg (coeffMass_nonneg _) (coeffMass_nonneg _)) (Nat.cast_nonneg _)
    (abs_polynomial_eval_le' p) (abs_polynomial_deriv_le' p) T
    (by simpa only [Polynomial.deriv] using memLp_polynomial_derivative_brownian L hL p T)
  simpa only [Polynomial.deriv] using h

/-- `p (B T)` lies in `𝔻₁,₂` for every real polynomial `p`. -/
theorem polynomial_brownian_mem_domD12 (p : Polynomial ℝ) (T : ℝ≥0) :
    (memLp_polynomial_brownian L hL p T).toLp _ ∈ domD12 P :=
  comp_brownian_mem_domD12 L hL (contDiff_polynomial_eval p)
    (add_nonneg (coeffMass_nonneg _) (coeffMass_nonneg _)) (Nat.cast_nonneg _)
    (abs_polynomial_eval_le' p) (abs_polynomial_deriv_le' p) T

end Brownian

/-! ### The product of two Brownian coordinates

`Dₜ (B S · B T) = B T 1_{(0, S]}(t) + B S 1_{(0, T]}(t)`, the first example beyond the first
chaos. -/

section TwoCoord

/-- The product of the two coordinates on `ℝ²`. -/
def mulCoord (y : Fin 2 → ℝ) : ℝ := y 0 * y 1

theorem contDiff_mulCoord : ContDiff ℝ 1 mulCoord :=
  (contDiff_apply ℝ ℝ 0).mul (contDiff_apply ℝ ℝ 1)

theorem fderiv_mulCoord (y : Fin 2 → ℝ) :
    fderiv ℝ mulCoord y = y 1 • ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 2 ↦ ℝ) 0 +
      y 0 • ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 2 ↦ ℝ) 1 := by
  have h : HasFDerivAt (fun y : Fin 2 → ℝ ↦ y 0 * y 1)
      (y 1 • ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 2 ↦ ℝ) 0 +
        y 0 • ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 2 ↦ ℝ) 1) y := by
    have h0 := hasFDerivAt_apply (𝕜 := ℝ) (F' := fun _ : Fin 2 ↦ ℝ) 0 y
    have h1 := hasFDerivAt_apply (𝕜 := ℝ) (F' := fun _ : Fin 2 ↦ ℝ) 1 y
    have := h0.mul h1
    rw [add_comm]
    exact this
  exact h.fderiv

theorem abs_mulCoord_le (y : Fin 2 → ℝ) : |mulCoord y| ≤ 2 * (1 + ‖y‖) ^ 2 := by
  unfold mulCoord
  rw [abs_mul]
  have h0 : |y 0| ≤ ‖y‖ := (Real.norm_eq_abs _).symm.le.trans (norm_le_pi_norm y 0)
  have h1 : |y 1| ≤ ‖y‖ := (Real.norm_eq_abs _).symm.le.trans (norm_le_pi_norm y 1)
  calc |y 0| * |y 1| ≤ ‖y‖ * ‖y‖ := mul_le_mul h0 h1 (abs_nonneg _) (norm_nonneg _)
    _ = ‖y‖ ^ 2 := (sq _).symm
    _ ≤ 2 * (1 + ‖y‖) ^ 2 := by linarith [norm_nonneg y, sq_nonneg ‖y‖, sq_nonneg (1 + ‖y‖)]

theorem norm_fderiv_mulCoord_le (y : Fin 2 → ℝ) : ‖fderiv ℝ mulCoord y‖ ≤ 2 * (1 + ‖y‖) ^ 2 := by
  rw [fderiv_mulCoord]
  have hp : ∀ i : Fin 2, ‖ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 2 ↦ ℝ) i‖ ≤ 1 :=
    fun i ↦ ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun z ↦ by
      rw [one_mul, ContinuousLinearMap.proj_apply]
      exact norm_le_pi_norm z i
  have h0 : |y 0| ≤ ‖y‖ := (Real.norm_eq_abs _).symm.le.trans (norm_le_pi_norm y 0)
  have h1 : |y 1| ≤ ‖y‖ := (Real.norm_eq_abs _).symm.le.trans (norm_le_pi_norm y 1)
  calc ‖y 1 • ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 2 ↦ ℝ) 0 +
        y 0 • ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 2 ↦ ℝ) 1‖
      ≤ ‖y 1‖ * ‖ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 2 ↦ ℝ) 0‖ +
        ‖y 0‖ * ‖ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 2 ↦ ℝ) 1‖ := by
        refine (norm_add_le _ _).trans ?_
        rw [norm_smul, norm_smul]
    _ ≤ ‖y‖ * 1 + ‖y‖ * 1 := by
        gcongr
        · rw [Real.norm_eq_abs]; exact h1
        · exact hp 0
        · rw [Real.norm_eq_abs]; exact h0
        · exact hp 1
    _ ≤ 2 * (1 + ‖y‖) ^ 2 := by linarith [norm_nonneg y, sq_nonneg ‖y‖, sq_nonneg (1 + ‖y‖)]

end TwoCoord

section Brownian

open CameronMartin

variable {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]
  [CompleteSpace W] [MeasurableSpace W] [BorelSpace W]
  [SecondCountableTopology W]
  {P : Measure W} [IsGaussian P] {B : ℝ≥0 → W → ℝ}
  (hB : IsPreBrownianReal B P) (L : ℝ≥0 → StrongDual ℝ W) (hL : ∀ t w, B t w = L t w)

include L hL

omit [CompleteSpace W] [SecondCountableTopology W] in
/-- `B S · B T` is square integrable. -/
theorem memLp_mul_brownian (S T : ℝ≥0) : MemLp (fun w ↦ B S w * B T w) 2 P :=
  memLp_cylinder_growth_brownian L hL contDiff_mulCoord zero_le_two abs_mulCoord_le ![S, T]

omit [CompleteSpace W] [SecondCountableTopology W] in
theorem memLp_brownian (T : ℝ≥0) : MemLp (B T) 2 P := by
  have h : B T = fun w ↦ L T w := by
    funext w
    exact hL T w
  rw [h]
  exact (IsGaussian.memLp_dual P (L T) 2 (by simp))

omit [CompleteSpace W] [SecondCountableTopology W] in
/-- The partial derivatives of `B S · B T` are `B T` and `B S`. -/
theorem cylinderPartialGrowth_mulCoord_zero (S T : ℝ≥0) :
    cylinderPartialGrowth (P := P) L hL contDiff_mulCoord zero_le_two norm_fderiv_mulCoord_le
        ![S, T] 0 = (memLp_brownian L hL T).toLp _ := by
  apply Lp.ext
  filter_upwards [MemLp.coeFn_toLp (memLp_cylinderPartial_of_dominated L hL contDiff_mulCoord
      norm_fderiv_mulCoord_le ![S, T] (growth_coord_le zero_le_two _)
      (integrable_growth_sq P 2 _) 0),
    MemLp.coeFn_toLp (memLp_brownian L hL T)] with w h1 h2
  rw [cylinderPartialGrowth, cylinderPartialD, h1, h2, fderiv_mulCoord]
  simp only [Fin.isValue, Matrix.cons_val_one, Matrix.cons_val_fin_one, Matrix.cons_val_zero,
    add_apply,
    smul_apply, ContinuousLinearMap.proj_apply, Pi.single_eq_same, smul_eq_mul, mul_one, ne_eq,
    one_ne_zero,
    not_false_eq_true, Pi.single_eq_of_ne, mul_zero, add_zero]

omit [CompleteSpace W] [SecondCountableTopology W] in
theorem cylinderPartialGrowth_mulCoord_one (S T : ℝ≥0) :
    cylinderPartialGrowth (P := P) L hL contDiff_mulCoord zero_le_two norm_fderiv_mulCoord_le
        ![S, T] 1 = (memLp_brownian L hL S).toLp _ := by
  apply Lp.ext
  filter_upwards [MemLp.coeFn_toLp (memLp_cylinderPartial_of_dominated L hL contDiff_mulCoord
      norm_fderiv_mulCoord_le ![S, T] (growth_coord_le zero_le_two _)
      (integrable_growth_sq P 2 _) 1),
    MemLp.coeFn_toLp (memLp_brownian L hL S)] with w h1 h2
  rw [cylinderPartialGrowth, cylinderPartialD, h1, h2, fderiv_mulCoord]
  simp only [Fin.isValue, Matrix.cons_val_one, Matrix.cons_val_fin_one, Matrix.cons_val_zero,
    add_apply,
    smul_apply, ContinuousLinearMap.proj_apply, ne_eq, zero_ne_one, not_false_eq_true,
    Pi.single_eq_of_ne, smul_eq_mul,
    mul_zero, Pi.single_eq_same, mul_one, zero_add]

/-- **`Dₜ (B S · B T) = B T 1_{(0, S]}(t) + B S 1_{(0, T]}(t)`**. -/
theorem timeDerivative_mderivClosure_mul_brownian (hgen : IsWienerGenerated B) (S T : ℝ≥0) :
    timeDerivative hB L hL hgen (mderivClosure P ((memLp_mul_brownian L hL S T).toLp _)) =
      tensor (intervalIndicator S) ((memLp_brownian L hL T).toLp _) +
        tensor (intervalIndicator T) ((memLp_brownian L hL S).toLp _) := by
  have h := timeDerivative_mderivClosure_cylinder_growth hB L hL hgen contDiff_mulCoord
    zero_le_two abs_mulCoord_le norm_fderiv_mulCoord_le ![S, T]
  rw [Fin.sum_univ_two, cylinderPartialGrowth_mulCoord_zero, cylinderPartialGrowth_mulCoord_one]
    at h
  exact h

end Brownian

end Malliavin

/- Adapted for Lean Pool: module imports and compatibility with its pinned toolchain. -/
