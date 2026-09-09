/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.SmoothTimeFieldJoint
import LeanPool.NavierStokesAndEuler.Euler.SmoothTimeFieldTimeJets

/-! Two actual time-derivative pairs give genuine joint C² regularity
for a smooth spatial coefficient path on interior times. -/

@[expose] public section


noncomputable section

open scoped ContDiff Topology

namespace SmoothTimeField

open Set Filter

variable {E V : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  (T : ℝ) (hT : 0 ≤ T) (A A₁ A₂ : SmoothTimeField (Icc (0 : ℝ) T) E V)

theorem jointDerivative_contDiffAt_one
    (hA : TimeDerivative T hT A A₁) (hA₁ : TimeDerivative T hT A₁ A₂)
    (t : ℝ) (ht : t ∈ Ioo 0 T) (x : E) :
    ContDiffAt ℝ 1 (Function.uncurry (jointDerivative T hT A A₁)) (t,x) := by
  have hq := realField_contDiffAt_one T hT A₁ A₂ hA₁ t ht x
  have hJ := realField_contDiffAt_one T hT A.derivative A₁.derivative
    (TimeDerivative.derivative T hT A A₁ hA) t ht x
  have hs := (ContinuousLinearMap.toSpanSingletonLIE ℝ
      V).toContinuousLinearEquiv.contDiff.contDiffAt.comp
    (t,x) hq
  let L : ((ℝ →L[ℝ] V) × (E →L[ℝ] V)) →L[ℝ] ((ℝ × E) →L[ℝ] V) :=
    (ContinuousLinearMap.coprodEquivL (𝕜 := ℝ) (E := ℝ) (F := E) (G := V) ℝ).toContinuousLinearMap
  exact (ContinuousLinearMap.contDiff (𝕜 := ℝ) (n := 1)
    (E := (ℝ →L[ℝ] V) × (E →L[ℝ] V)) (F := (ℝ × E) →L[ℝ] V) L).contDiffAt.comp
    (t,x) (hs.prodMk hJ)

theorem realField_contDiffAt_two
    (hA : TimeDerivative T hT A A₁) (hA₁ : TimeDerivative T hT A₁ A₂)
    (t : ℝ) (ht : t ∈ Ioo 0 T) (x : E) :
    ContDiffAt ℝ 2 (Function.uncurry (A.realField T hT)) (t,x) := by
  rw [show (2 : ℕ∞ω) = ((1 : ℕ)+1) from rfl,contDiffAt_succ_iff_hasFDerivAt]
  refine ⟨Function.uncurry (jointDerivative T hT A A₁),
    ⟨{p : ℝ × E | p.1 ∈ Ioo 0 T},?_,?_⟩,
    jointDerivative_contDiffAt_one T hT A A₁ A₂ hA hA₁ t ht x⟩
  · exact (continuous_fst.tendsto (t,x)).eventually (Ioo_mem_nhds ht.1 ht.2)
  · intro p hp
    exact realField_hasFDerivAt T hT A A₁ hA p.1 hp p.2

end SmoothTimeField
