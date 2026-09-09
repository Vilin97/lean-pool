/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.CorrectionDifferencePDE

/-! The literal difference equation of two actual inviscid corrections. -/

@[expose] public section


noncomputable section

namespace EulerInviscidDifferencePDE

open Set EulerLiftedGradientSpace EulerCylinderSobolevSpace EulerCorrectionOperators
  EulerCorrectionDifferencePDE EulerVolterraConvolution

variable (period : ℝ) [Fact (0 < period)]

/-- Subtracting the actual inviscid correction equations gives the zero-viscosity difference
equation. -/
theorem inviscid_difference_hasDerivAt {q : ℕ} (hq : 6 ≤ q) (T : ℝ) (hT : 0 ≤ T)
    (D : CorrectionData period q (Icc (0 : ℝ) T))
    (u v : C(Icc (0 : ℝ) T, SobolevSpace period (q + 1)))
    (hu : ∀ t (ht : t ∈ Ioo 0 T),
      HasDerivAt (fun r => value period (extendPath T hT u r))
        (value period ((D.coefficients period hq).apply ⟨t, ht.1.le, ht.2.le⟩ (u
            ⟨t, ht.1.le, ht.2.le⟩))) t)
    (hv : ∀ t (ht : t ∈ Ioo 0 T),
      HasDerivAt (fun r => value period (extendPath T hT v r))
        (value period ((D.coefficients period hq).apply ⟨t, ht.1.le, ht.2.le⟩ (v
            ⟨t, ht.1.le, ht.2.le⟩))) t)
    (t : ℝ) (ht : t ∈ Ioo 0 T) :
    HasDerivAt (fun r => value period (extendPath T hT u r)-value period (extendPath T hT v r))
      (differenceRhs period D hq 0 0 ⟨t,ht.1.le,ht.2.le⟩ (u ⟨t,ht.1.le,ht.2.le⟩) (v
          ⟨t,ht.1.le,ht.2.le⟩)) t := by
  have hd := (hu t ht).sub (hv t ht)
  rw [D.source_value period hq,D.source_value period hq] at hd
  apply hd.congr_deriv
  have he := differenceRhs_eq_sub period D hq 0 0 ⟨t,ht.1.le,ht.2.le⟩
    (u ⟨t,ht.1.le,ht.2.le⟩) (v ⟨t,ht.1.le,ht.2.le⟩)
  simpa only [zero_smul,zero_sub] using he.symm

end EulerInviscidDifferencePDE
