/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.HMinusTools
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.Terms

/-! Test duality for the divergence-form part of the tiny residual.
The separate nondivergence summand needs the mean-zero and L² estimates, which are proved
elsewhere; this file does not assume them. -/

@[expose] public section

noncomputable section
open MeasureTheory Homogenization
namespace AVenhance.Infra.Section5

open AVenhance

/-- At each time, the divergence part of `tiny` has the HDot⁻¹ bound
given by the L² norm of its vector flux. -/
theorem hMinusOneNorm_tiny_divergencePart_le
    (d e : ℝ → Vec 2 → Vec 2) (t : ℝ)
    (hF : ContDiff ℝ (⊤ : ℕ∞) (fun x => d t x + e t x))
    (hper : IsZ2Periodic (fun x => d t x + e t x)) :
    hMinusOneNorm (fun x => vecDiv (fun y => d t y + e t y) x) ≤
      ENNReal.ofReal (Real.sqrt (gradNormSq (fun x => d t x + e t x))) := by
  change hMinusOneNorm
      (cellDivergence (fun x => d t x + e t x)) ≤ _
  exact hMinusOneNorm_divergence_le _ hF hper

end AVenhance.Infra.Section5
end
