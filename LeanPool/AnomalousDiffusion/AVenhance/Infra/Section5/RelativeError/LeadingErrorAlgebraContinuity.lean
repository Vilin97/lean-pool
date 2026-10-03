/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.RelativeError.LeadingErrorAlgebraDefs
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section3.CorrTimeRegularity

/-! # Joint continuity of the three remainder fields of `e.grad.tildetheta.again`

For `T` jointly `C^∞` on `[0,∞) × ℝ²`, the fields `leadingErrFlowInv`, `leadingErrFlowFwd`,
`leadingErrHessian` (`LeadingErrorAlgebraDefs`) are jointly continuous on `Ici 0 ×ˢ univ`.  Every
ingredient (entries of `∇X^{±1}`, `∇X∘X⁻¹`, `∂²X∘X⁻¹`, `Χ∘X⁻¹`, `∇Χ∘X⁻¹`) is continuous on all
of `ℝ × ℝ²`; only the derivatives of `T` need the set `Ici 0 ×ˢ univ`. -/

@[expose] public section

open Homogenization
open scoped ContDiff

noncomputable section

namespace AVenhance.Infra.Section5.RelativeError

open AVenhance AVenhance.Infra.Section5

variable {β : ℝ} (I : Ingredients β) {Φ : ℕ → ℝ → Vec 2 → ℝ}

/-! ### Flow ingredients (continuous on all of `ℝ × ℝ²`) -/

/-! ### Derivatives of `T` (continuous on `Ici 0 ×ˢ univ`) -/

section TDerivs

variable {T : ℝ → Vec 2 → ℝ}

theorem LeadingErrorAlgebraContinuity.hsu_Ici : UniqueDiffOn ℝ (Set.Ici (0 : ℝ) ×ˢ (Set.univ : Set
    (Vec 2))) :=
  UniqueDiffOn.prod (uniqueDiffOn_Ici 0) uniqueDiffOn_univ

/-- The spatial derivative `∂_p T` is `C^∞` on `Ici 0 ×ˢ univ`. -/
theorem contDiffOn_spaceGrad_joint
    (hT : ContDiffOn ℝ ∞ (fun p : ℝ × Vec 2 => T p.1 p.2) (Set.Ici (0 : ℝ) ×ˢ Set.univ))
    (p : Fin 2) :
    ContDiffOn ℝ ∞ (fun r : ℝ × Vec 2 => spaceGrad (T r.1) r.2 p)
      (Set.Ici (0 : ℝ) ×ˢ Set.univ) := by
  have h : ContDiffOn ℝ ∞ (fun r : ℝ × Vec 2 =>
      fderivWithin ℝ (fun q : ℝ × Vec 2 => T q.1 q.2) (Set.Ici (0 : ℝ) ×ˢ Set.univ) r
        (0, basisVec p)) (Set.Ici (0 : ℝ) ×ˢ Set.univ) :=
    (hT.fderivWithin LeadingErrorAlgebraContinuity.hsu_Ici (by simp)).clm_apply contDiffOn_const
  refine h.congr ?_
  rintro ⟨t, x⟩ ⟨ht, -⟩
  exact Integration.spaceGrad_slice_eq (F := fun q : ℝ × Vec 2 => T q.1 q.2)
    (s := Set.Ici (0 : ℝ) ×ˢ Set.univ) t x (fun y => ⟨ht, trivial⟩)
    (hT.differentiableOn (by simp) (t, x) ⟨ht, trivial⟩) p

theorem continuousOn_spaceGrad_joint
    (hT : ContDiffOn ℝ ∞ (fun p : ℝ × Vec 2 => T p.1 p.2) (Set.Ici (0 : ℝ) ×ˢ Set.univ))
    (p : Fin 2) :
    ContinuousOn (fun r : ℝ × Vec 2 => spaceGrad (T r.1) r.2 p) (Set.Ici (0 : ℝ) ×ˢ Set.univ) :=
  (contDiffOn_spaceGrad_joint hT p).continuousOn

theorem continuousOn_spaceHess_joint
    (hT : ContDiffOn ℝ ∞ (fun p : ℝ × Vec 2 => T p.1 p.2) (Set.Ici (0 : ℝ) ×ˢ Set.univ))
    (i p : Fin 2) :
    ContinuousOn (fun r : ℝ × Vec 2 => spaceHess (T r.1) r.2 i p)
      (Set.Ici (0 : ℝ) ×ˢ Set.univ) := by
  have hP := contDiffOn_spaceGrad_joint hT p
  have h : ContinuousOn (fun r : ℝ × Vec 2 =>
      fderivWithin ℝ (fun r' : ℝ × Vec 2 => spaceGrad (T r'.1) r'.2 p)
        (Set.Ici (0 : ℝ) ×ˢ Set.univ) r (0, basisVec i)) (Set.Ici (0 : ℝ) ×ˢ Set.univ) :=
    ((hP.fderivWithin (m := ∞) LeadingErrorAlgebraContinuity.hsu_Ici (by
        simp)).continuousOn).clm_apply continuousOn_const
  refine h.congr ?_
  rintro ⟨t, x⟩ ⟨ht, -⟩
  exact Integration.spaceGrad_slice_eq (F := fun r' : ℝ × Vec 2 => spaceGrad (T r'.1) r'.2 p)
    (s := Set.Ici (0 : ℝ) ×ˢ Set.univ) t x (fun y => ⟨ht, trivial⟩)
    (hP.differentiableOn (by simp) (t, x) ⟨ht, trivial⟩) i

end TDerivs

/-! ### The three remainder fields -/

section Fields

variable {T : ℝ → Vec 2 → ℝ}

end Fields

end AVenhance.Infra.Section5.RelativeError
