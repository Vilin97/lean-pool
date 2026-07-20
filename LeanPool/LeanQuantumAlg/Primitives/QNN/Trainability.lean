/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import LeanPool.LeanQuantumAlg.Init
public import Mathlib.Analysis.SpecificLimits.Basic
public import Mathlib.Analysis.Normed.Group.Basic

/-!
# Trainability: exponential concentration and barren plateaus

The unifying notion behind **barren plateaus** (McClean et al. 2018) and
**quantum-kernel concentration** (Thanasilp et al. 2022, Def. 1) is *exponential
concentration*: a quantity indexed by system size `n` (a loss, a gradient variance,
or a kernel value) deviates from a fixed value `μ` by at most `C / b ^ n` for some
`b > 1`. The practical consequence is that the quantity becomes exponentially
flat — it converges to `μ`, so resolving it requires exponentially many samples.

This module gives the definition and its convergence consequence, and records the
barren-plateau models on top of it in the `GroverModel`/`ParamShiftModel` style: the
hard Haar / `t`-design / Weingarten input (the variance bound) is bundled as a
hypothesis, and the trainability consequence is derived.

Sources: McClean, Boixo, Smelyanskiy, Babbush, Neven (2018); Cerezo, Sone, Volkoff,
Cincio, Coles (2021); Ragone et al. (2023); Thanasilp, Wang, Cerezo, Holmes (2022).
-/

@[expose] public section

namespace QuantumAlg

open Filter Topology

/-- **Exponential concentration.** `X n` deviates from `μ` by at most `C / b ^ n`
for some base `b > 1` (McClean 2018; Thanasilp 2022, Def. 1). -/
def ExpConcentrated (X : ℕ → ℝ) (μ : ℝ) : Prop :=
  ∃ b : ℝ, 1 < b ∧ ∃ C : ℝ, 0 ≤ C ∧ ∀ n, |X n - μ| ≤ C / b ^ n

/-- An exponentially concentrated quantity converges to its concentration value:
the landscape becomes exponentially flat. -/
theorem ExpConcentrated.tendsto {X : ℕ → ℝ} {μ : ℝ} (h : ExpConcentrated X μ) :
    Filter.Tendsto X Filter.atTop (nhds μ) := by
  obtain ⟨b, hb, C, _, hbnd⟩ := h
  have key : Filter.Tendsto (fun n => C / b ^ n) Filter.atTop (nhds 0) := by
    have hbpow : Filter.Tendsto (fun n => b ^ n) Filter.atTop Filter.atTop :=
      tendsto_pow_atTop_atTop_of_one_lt hb
    have hinv : Filter.Tendsto (fun n => (b ^ n)⁻¹) Filter.atTop (nhds 0) :=
      tendsto_inv_atTop_zero.comp hbpow
    simpa [div_eq_mul_inv] using hinv.const_mul C
  have hsq : Filter.Tendsto (fun n => |X n - μ|) Filter.atTop (nhds 0) :=
    squeeze_zero (fun n => abs_nonneg _) hbnd key
  rw [tendsto_iff_dist_tendsto_zero]
  simpa [Real.dist_eq] using hsq

/-- A model has a **barren plateau** when its loss/gradient variance is
exponentially concentrated to `0` (so the trainable signal vanishes with system
size). -/
def HasBarrenPlateau (variance : ℕ → ℝ) : Prop := ExpConcentrated variance 0

/-- Under a barren plateau the variance vanishes in the large-system limit. -/
theorem HasBarrenPlateau.variance_tendsto_zero {variance : ℕ → ℝ}
    (h : HasBarrenPlateau variance) :
    Filter.Tendsto variance Filter.atTop (nhds 0) :=
  h.tendsto

/-! ### Lie-algebraic barren plateaus -/

/-- **Lie-algebraic barren plateaus** (Ragone et al. 2023). In the simple-DLA case the
loss variance is `P_g(ρ) P_g(O) / dim(g)` (their Eq. (10)); bundling the numerator and
the DLA dimension, an exponentially large dynamical Lie algebra forces a barren
plateau. -/
structure LieAlgebraicVariance where
  /-- `dim g` as a function of the system size. -/
  gdim : ℕ → ℝ
  /-- The `g`-purity numerator `P_g(ρ) P_g(O)`. -/
  numer : ℝ
  /-- The numerator is nonnegative. -/
  numer_nonneg : 0 ≤ numer
  /-- The DLA dimension is positive. -/
  gdim_pos : ∀ n, 0 < gdim n
  /-- The loss variance. -/
  variance : ℕ → ℝ
  /-- Ragone et al. (2023), Eq. (10): variance `= P_g(ρ) P_g(O) / dim(g)`. -/
  variance_eq : ∀ n, variance n = numer / gdim n

/-- An exponentially large dynamical Lie algebra forces a barren plateau. -/
theorem LieAlgebraicVariance.hasBarrenPlateau_of_exp_dim (M : LieAlgebraicVariance)
    {b : ℝ} (hb : 1 < b) (hdim : ∀ n, b ^ n ≤ M.gdim n) :
    HasBarrenPlateau M.variance := by
  refine ⟨b, hb, M.numer, M.numer_nonneg, fun n => ?_⟩
  have hbn : 0 < b ^ n := pow_pos (one_pos.trans hb) n
  rw [M.variance_eq, sub_zero,
    abs_of_nonneg (div_nonneg M.numer_nonneg (M.gdim_pos n).le)]
  exact div_le_div_of_nonneg_left M.numer_nonneg hbn (hdim n)

/-! ### Cost-function-dependent barren plateaus -/

/-- **Cost-function-dependent barren plateaus** (Cerezo et al. 2021): a global cost
exhibits a barren plateau (exponentially concentrated gradient variance), whereas a
local cost is trainable (its gradient variance has a polynomial lower bound). -/
structure CostDependentBP where
  /-- Gradient variance of the global cost. -/
  globalVariance : ℕ → ℝ
  /-- Gradient variance of the local cost. -/
  localVariance : ℕ → ℝ
  /-- The global cost has a barren plateau. -/
  global_bp : HasBarrenPlateau globalVariance
  /-- The local cost keeps a polynomial lower bound. -/
  local_lb : ∀ n : ℕ, 0 < n → 1 / (n : ℝ) ≤ localVariance n

/-- The global cost's gradient vanishes (barren plateau). -/
theorem CostDependentBP.global_tendsto_zero (M : CostDependentBP) :
    Filter.Tendsto M.globalVariance Filter.atTop (nhds 0) :=
  M.global_bp.variance_tendsto_zero

/-- The local cost's gradient variance stays strictly positive (trainable). -/
theorem CostDependentBP.local_pos (M : CostDependentBP) {n : ℕ} (hn : 0 < n) :
    0 < M.localVariance n :=
  lt_of_lt_of_le (one_div_pos.mpr (Nat.cast_pos.mpr hn)) (M.local_lb n hn)

/-! ### Quantum-kernel concentration -/

/-- **Quantum-kernel concentration** (Thanasilp et al. 2022): the kernel value
concentrates exponentially to a fixed `κ₀`, so a polynomial number of measurement
shots cannot distinguish inputs (the model becomes input-independent).

This is the abstract deterministic-sequence form. The genuine probabilistic result —
a concrete quantum kernel whose data-averaged value provably concentrates exponentially,
derived from first principles with no Haar assumption — is
`LeanPool.LeanQuantumAlg.ryKernel_concentrates` in `QuantumAlg/Primitives/KernelConcentration.lean`,
built on the probabilistic engine `LeanPool.LeanQuantumAlg.ExpConcentratedProb`. -/
def KernelConcentration (kernel : ℕ → ℝ) (κ₀ : ℝ) : Prop := ExpConcentrated kernel κ₀

/-- A concentrated kernel converges to its concentration value. -/
theorem KernelConcentration.tendsto {kernel : ℕ → ℝ} {κ₀ : ℝ}
    (h : KernelConcentration kernel κ₀) :
    Filter.Tendsto kernel Filter.atTop (nhds κ₀) :=
  ExpConcentrated.tendsto h

/-! ### Geometric/equivariant QML trainability -/

/-- **Geometric/equivariant QML trainability** (Ragone et al. 2022 + the DLA variance
law). A symmetry-structured model whose dynamical Lie algebra has only polynomial
dimension keeps a polynomial lower bound on its gradient variance, hence avoids a
barren plateau. -/
structure GeometricQMLTrainable where
  /-- Gradient variance. -/
  variance : ℕ → ℝ
  /-- Polynomial degree of the lower bound. -/
  deg : ℕ
  /-- The variance is bounded below by `1 / n ^ deg` (polynomial trainability). -/
  variance_lb : ∀ n : ℕ, 0 < n → 1 / (n : ℝ) ^ deg ≤ variance n

/-- A geometric/equivariant model with polynomial dynamical Lie algebra has strictly
positive (not exponentially vanishing) gradient variance: it is trainable. -/
theorem GeometricQMLTrainable.variance_pos (M : GeometricQMLTrainable) {n : ℕ}
    (hn : 0 < n) : 0 < M.variance n :=
  lt_of_lt_of_le (one_div_pos.mpr (pow_pos (Nat.cast_pos.mpr hn) M.deg)) (M.variance_lb n hn)

end QuantumAlg
