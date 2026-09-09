/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.CylinderSobolevDerivatives

@[expose] public section

/-! Translation is strongly differentiable in the actual Sobolev topology with one more derivative.
  -/

noncomputable section

namespace EulerCylinderSobolevSpace

open EulerLiftedGradientSpace EulerPressureSpatialRegularity EulerCylinderSobolev
open scoped Topology

variable (period : ℝ) [Fact (0 < period)]

/-- Differentiating cylinder translation in Hq costs precisely one Sobolev derivative. -/
theorem sobolevTranslation_hasDerivAt {q : ℕ} (i : Fin 4) (u : SobolevSpace period (q+1)) :
    HasDerivAt (fun t => sobolevTranslation period q (translationPath period (standardDirection i)
      t)
      (truncateOperator period q u)) (derivativeOperator period q i u) 0 := by
  let f : ℝ → SobolevSpace period q := fun t =>
    sobolevTranslation period q (translationPath period (standardDirection i) t) (truncateOperator
      period q u)
  let d : SobolevWord q → LiftL2 period := fun w =>
    u.val ⟨⟨w.1.val+1, Nat.succ_lt_succ w.1.isLt⟩, Fin.cons i w.2⟩
  have hd : HasDerivAt (fun t => (f t).val) d 0 := by
    apply hasDerivAt_pi.mpr
    intro w
    exact word_hasDerivAt period u w.1.isLt w.2 i
  have hdmem : d ∈ sobolevSubspace period q := by
    apply (sobolevSubspace period q).isClosed.mem_of_tendsto hd.tendsto_slope
    apply Filter.Eventually.of_forall
    intro t
    change (t-0)⁻¹ • ((f t).val - (f 0).val) ∈ sobolevSubspace period q
    exact (sobolevSubspace period q).smul_mem _ ((sobolevSubspace period q).sub_mem (f t).property
      (f 0).property)
  let v : SobolevSpace period q := ⟨d, hdmem⟩
  have hv : HasDerivAt f v 0 := by
    apply hasDerivAt_iff_tendsto_slope.mpr
    rw [tendsto_subtype_rng]
    exact hd.tendsto_slope
  have hval : HasDerivAt (fun t => value period (f t)) (value period v) 0 :=
    (valueOperator period q).hasFDerivAt.comp_hasDerivAt 0 hv
  have he : v = derivativeOperator period q i u := by
    apply value_injective period
    exact hval.unique (derivativeOperator_hasDerivAt period i u)
  rw [he] at hv
  exact hv

end EulerCylinderSobolevSpace
