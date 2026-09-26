/-
Copyright (c) 2026 Joris Roos. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joris Roos
-/
module

public import Mathlib.Tactic
public import LeanPool.Superorthogonality.LeanSuperorthogonality.Defs

import LeanPool.Superorthogonality.LeanSuperorthogonality.Codex.MainTheorem

/-!
Formalizing arXiv:2212.08956
-/

@[expose] public noncomputable section

namespace Superorthogonal

open MeasureTheory Nat Set Complex
open scoped ComplexConjugate

variable {α : Type*} [MeasurableSpace α]
variable (μ : Measure α)
variable {ι : Type*}

variable {r : ℕ}

/-- Theorem 1 of arXiv:2212.08956 for the special case of finite index sets. -/
theorem sqfct_estimate_of_type_iv_superorthogonal_finite [Finite ι] {f : ι → α → ℂ}
    (hr : 1 ≤ r) (hf : TypeIVSuperorthogonal μ f r) (hsq : MemLp (sqfct f) (2 * r) μ) :
    eLpNorm (∑' j, f j) (2 * r) μ ≤ C r * eLpNorm (sqfct f) (2 * r) μ  :=
  Codex.sqfct_estimate_of_type_iv_superorthogonal_finite μ hr hf hsq

/-- Theorem 1 of arXiv:2212.08956 -/
theorem sqfct_estimate_of_type_iv_superorthogonal [Countable ι]
    [Fact (1 ≤ (2 * (r : ENNReal)))] (hr : 1 ≤ r)
    {f : ι → Lp ℂ (2 * r) μ} (hf : TypeIVSuperorthogonal μ (fun i ↦ f i) r)
    (hsum : ∀ᵐ x ∂μ, Summable fun j ↦ ‖f j x‖ ^ 2)
    (hsq : MemLp (sqfct <| fun i ↦ f i) (2 * r) μ) :
    Summable f ∧ ENNReal.ofReal ‖∑' j, f j‖ ≤ C r * eLpNorm (sqfct <| fun i ↦ f i) (2 * r) μ  :=
  Codex.sqfct_estimate_of_type_iv_superorthogonal μ hr hf hsum hsq

end Superorthogonal

end

/- Adapted for Lean Pool: module imports and compatibility with its pinned toolchain. -/
