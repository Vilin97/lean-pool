/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini, Aristotle
-/

module

public import LeanPool.AsymptoticTrianglePacking.Internal.Basic
public import LeanPool.AsymptoticTrianglePacking.Internal.Survival
public import LeanPool.AsymptoticTrianglePacking.Internal.Prelude

/-!
# LeanPool.AsymptoticTrianglePacking.Internal — existence of a Bernoulli retention space

Standalone, Mathlib-only. The measure-theoretic prerequisite for the nibble iteration (step 2):
for any finite hypergraph `H` on a finite vertex type and any retention probability `p ∈ [0,1]`,
there EXISTS a probability space carrying a `BernoulliRetention` on `H` at `p` — an independent
family of events `A e` (`e` retained) each of probability `p`.

Standard construction: `Ω := Finset V → Bool` (finite, since `V` is a `Fintype`) with the product
Bernoulli(`p`) measure `Measure.pi (fun _ => (Bernoulli) p)`; `A e := {ω | ω e = true}`. The
coordinate events are independent (product measure) and each has probability `p`.

Must be placeholder-free and axiom-clean `[propext, Classical.choice, Quot.sound]`.
-/

public section

open MeasureTheory ProbabilityTheory

namespace LeanPool.AsymptoticTrianglePacking.Internal

universe u

/-- **Existence of a Bernoulli retention.** For any finite hypergraph `H` on a finite vertex type
and any `p ∈ [0,1]`, there is a probability space carrying a `BernoulliRetention` on `H` at `p`. -/
theorem exists_bernoulliRetention {V : Type u} [Finite V] [DecidableEq V]
    (H : Finset (Finset V)) {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    ∃ (Ω : Type u) (mΩ : MeasureSpace Ω),
      IsProbabilityMeasure (@MeasureSpace.volume Ω mΩ) ∧
        Nonempty (@BernoulliRetention V _ Ω mΩ H p) := by
  let _ : Fintype V := Fintype.ofFinite V
  let t : unitInterval := ⟨p, hp0, hp1⟩
  let μ : Measure Bool := bernoulliMeasure true false t
  let Ω := Finset V → Bool
  let mΩ : MeasureSpace Ω := ⟨Measure.pi (fun _ => μ)⟩
  refine ⟨Ω, mΩ, ?_, ?_⟩
  · let _ : MeasureSpace Ω := mΩ
    exact Measure.pi.instIsProbabilityMeasure (fun _ : Finset V => μ)
  · let _ : MeasureSpace Ω := mΩ
    let A : Finset V → Set Ω := fun e => {ω | ω e = true}
    have hmeas : ∀ e, MeasurableSet (A e) := by
      intro e
      change MeasurableSet ((fun ω : Ω => ω e) ⁻¹' ({true} : Set Bool))
      exact (measurable_pi_apply e) (measurableSet_singleton true)
    have hfun : iIndepFun (fun e (ω : Ω) => ω e)
        (Measure.pi (fun _ : Finset V => μ)) := by
      simpa only [id_eq] using
        (iIndepFun_pi (μ := fun _ : Finset V => μ) (X := fun _ => id)
          (fun _ => measurable_id.aemeasurable))
    have hpred : iIndepFun (fun e (ω : Ω) => ω e = true)
        (Measure.pi (fun _ : Finset V => μ)) := by
      change iIndepFun (fun e => (fun b => b = true) ∘ fun ω : Ω => ω e)
        (Measure.pi (fun _ : Finset V => μ))
      exact hfun.comp (fun _ b => b = true) (fun _ => Measurable.of_discrete)
    have hind : iIndepSet A (Measure.pi (fun _ : Finset V => μ)) := by
      rw [← iIndep_comap_mem_iff]
      apply (iIndepFun_iff_iIndep _ _ _).1
      simpa [A] using hpred
    refine ⟨⟨A, hmeas, ?_, ?_⟩⟩
    · change iIndepSet A (Measure.pi (fun _ : Finset V => μ))
      exact hind
    · intro e he
      rw [show (ℙ : Measure Ω) = Measure.pi (fun _ : Finset V => μ) by rfl]
      rw [show A e = Function.eval e ⁻¹' ({true} : Set Bool) by rfl]
      rw [← Measure.map_apply (measurable_pi_apply e) (measurableSet_singleton true)]
      rw [Measure.pi_map_eval]
      have hμuniv : μ Set.univ = 1 := measure_univ
      rw [show ∏ j ∈ Finset.univ.erase e, μ Set.univ = 1 by
        exact Finset.prod_eq_one (fun _ _ => hμuniv)]
      rw [one_smul]
      change bernoulliMeasure true false t {true} = ENNReal.ofReal p
      rw [bernoulliMeasure_apply t (measurableSet_singleton true)]
      simpa [t] using ENNReal.coe_nnreal_eq (unitInterval.toNNReal t)

end LeanPool.AsymptoticTrianglePacking.Internal
