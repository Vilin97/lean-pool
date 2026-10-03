/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/
module


public import Mathlib.MeasureTheory.Covering.Vitali
public import Mathlib.MeasureTheory.Integral.Layercake

/-! # Good Lambda -/

@[expose] public section

namespace Homogenization

open scoped ENNReal NNReal BigOperators

noncomputable section

/-!
# The real-variable core of the cube Calderón--Zygmund argument

This file records the two source-independent steps in the global
Caffarelli--Peral argument from `CZestimates.tex`:

* a bounded family of stopping balls has a disjoint Vitali subfamily whose
  fixed enlargements cover the original family; and
* once layer-cake has turned a one-level good-`λ` estimate into a scalar
  inequality, the term carrying the unknown quantity can be reabsorbed.

The construction of the stopping balls, the cube doubling estimate, and the
conversion of local comparison estimates to the one-level estimate belong to
the later cube-specific packet.  In particular, neither a harmonic
approximant nor a final Calderón--Zygmund estimate is made a hypothesis here.
-/

namespace CubeCalderonZygmund

/-- A bounded family of closed balls admits a pairwise disjoint subfamily
whose `τ`-enlargements cover the union of the original family.  This is the
form of Vitali selection used after the stopping-radius construction in the
global good-`λ` argument. -/
theorem exists_disjoint_closedBall_subfamily_covering_union
    {α ι : Type*} [PseudoMetricSpace α] (t : Set ι)
    (centre : ι → α) (radius : ι → ℝ) (R : ℝ)
    (hradius : ∀ a ∈ t, radius a ≤ R) (τ : ℝ) (hτ : 3 < τ) :
    ∃ u ⊆ t,
      (u.PairwiseDisjoint fun a => Metric.closedBall (centre a) (radius a)) ∧
        (⋃ a ∈ t, Metric.closedBall (centre a) (radius a)) ⊆
          ⋃ b ∈ u, Metric.closedBall (centre b) (τ * radius b) := by
  obtain ⟨u, hu, hdisjoint, hcover⟩ :=
    Vitali.exists_disjoint_subfamily_covering_enlargement_closedBall
      t centre radius R hradius τ hτ
  refine ⟨u, hu, hdisjoint, ?_⟩
  rintro y hy
  rcases Set.mem_iUnion₂.mp hy with ⟨a, ha, hya⟩
  obtain ⟨b, hb, hab⟩ := hcover a ha
  exact Set.mem_iUnion₂.mpr ⟨b, hb, hab hya⟩

/-- The scalar reabsorption step at the end of a good-`λ` proof.  Typically
`X` is the weighted layer-cake integral of the solution, `Y` that of the data,
and `θ < 1` is arranged by choosing the good-`λ` parameters internally. -/
theorem goodLambda_reabsorb {θ X C Y : ℝ}
    (hθ : θ < 1) (h : X ≤ θ * X + C * Y) :
    X ≤ (C / (1 - θ)) * Y := by
  have hdenom : 0 < 1 - θ := sub_pos.mpr hθ
  have hscaled : (1 - θ) * X ≤ C * Y := by
    calc
      (1 - θ) * X = X - θ * X := by ring
      _ ≤ C * Y := sub_le_iff_le_add.mpr (by simpa [add_comm] using h)
  calc
    X ≤ (C * Y) / (1 - θ) := by
      apply (le_div_iff₀ hdenom).2
      simpa [mul_comm] using hscaled
    _ = (C / (1 - θ)) * Y := by ring

end CubeCalderonZygmund

end

end Homogenization
