/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.InjectivePathDerivative

@[expose] public section

/-! Genuine closed-interval derivatives lift through injective bounded embeddings. -/

noncomputable section

namespace EulerInjectivePathDerivative

open Set MeasureTheory EulerVolterraConvolution EulerIntegralPathLimit

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]

/-- A continuous stronger-space derivative is genuine even at the interval endpoints. -/
theorem hasDerivWithinAt_of_injective_map (L : E →L[ℝ] F) (hL : Function.Injective L)
    (T : ℝ) (hT : 0 ≤ T) (u f : C(Icc (0 : ℝ) T,E))
    (hd : ∀ t ∈ Ioo 0 T, HasDerivAt (fun r => L (extendPath T hT u r))
      (L (extendPath T hT f t)) t) (t : Icc (0 : ℝ) T) :
    HasDerivWithinAt (extendPath T hT u) (f t) (Icc (0 : ℝ) T) t := by
  have heq := integral_equation_of_injective_map L hL T hT u f hd
  have hg := ((extendPath_continuous T hT f).integral_hasStrictDerivAt 0 (t :
    ℝ)).hasDerivAt.const_add
    (u ⟨0,le_rfl,hT⟩)
  have hg' := hg.hasDerivWithinAt (s := Icc (0 : ℝ) T)
  rw [show extendPath T hT f (t : ℝ) = f t by simp only [extendPath,projIcc_of_mem hT t.property]]
    at hg'
  apply hg'.congr_of_mem _ t.property
  intro r hr
  change u (projIcc 0 T hT r) = _
  rw [projIcc_of_mem hT hr]
  exact heq ⟨r,hr⟩

end EulerInjectivePathDerivative
