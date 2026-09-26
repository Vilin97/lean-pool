/-
Copyright (c) 2026 Yoshito Ishiki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yoshito Ishiki
-/
module

public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.Analysis.RCLike.Basic
public import Mathlib.Analysis.SpecificLimits.Basic
public import Mathlib.Tactic


/-!
# Cardinal control from a dense range

Every point of a metric space is determined by a sequence from any specified
dense range.  Besides its later cardinal consequences, the explicit embedding
keeps the completion estimates independent of the internal representation of
Mathlib's completion.
-/

@[expose] public section

namespace ScottishBook155

open Filter

universe u v

namespace DenseSequenceCardinal

variable {D : Type u} {X : Type v} [MetricSpace X]
variable (f : D → X) (hf : DenseRange f)

private theorem exists_approx (hf : DenseRange f) (x : X) (n : ℕ) :
    ∃ d : D, dist (f d) x < (1 : ℝ) / (n + 1) := by
  have hx : x ∈ closure (Set.range f) := hf x
  obtain ⟨y, ⟨d, rfl⟩, hyd⟩ :=
    (Metric.mem_closure_iff.mp hx) ((1 : ℝ) / (n + 1)) (by positivity)
  exact ⟨d, by simpa [dist_comm] using hyd⟩

/-- A chosen `1 / (n+1)` approximation from the dense source. -/
noncomputable def approx (hf : DenseRange f) (x : X) (n : ℕ) : D :=
  Classical.choose (show ∃ d : D, dist (f d) x < (1 : ℝ) / (n + 1) from by
    exact exists_approx f hf x n)

theorem approx_spec (hf : DenseRange f) (x : X) (n : ℕ) :
    dist (f (approx f hf x n)) x < (1 : ℝ) / (n + 1) :=
  Classical.choose_spec (exists_approx f hf x n)

theorem approx_tendsto (hf : DenseRange f) (x : X) :
    Tendsto (fun n => f (approx f hf x n)) atTop (nhds x) := by
  rw [tendsto_iff_dist_tendsto_zero]
  exact squeeze_zero (fun n => dist_nonneg)
    (fun n => (approx_spec f hf x n).le)
    (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))

/-- A metric space embeds into the type of sequences from any dense source. -/
noncomputable def sequenceEmbedding (hf : DenseRange f) : X ↪ (ℕ → D) where
  toFun x := approx f hf x
  inj' := by
    intro x y hxy
    apply tendsto_nhds_unique (approx_tendsto f hf x)
    convert approx_tendsto f hf y using 1
    funext n
    exact congrArg f (congrFun hxy n)

/-- Cardinal form of `sequenceEmbedding`. -/
theorem mk_le_sequences (hf : DenseRange f) :
    Cardinal.lift.{u} (Cardinal.mk X) ≤
      Cardinal.lift.{v} (Cardinal.mk (ℕ → D)) := by
  exact Cardinal.lift_mk_le'.mpr ⟨sequenceEmbedding f hf⟩

end DenseSequenceCardinal

end ScottishBook155
