/-
Copyright (c) 2026 Arseniy Akopyan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arseniy Akopyan
-/
module


public import Mathlib.Analysis.Normed.Order.Lattice
public import Mathlib.Tactic

/-!
# `NRR.EMP.VariableBody.WeightBox` — a compact codomain for bounded weights

For a fixed arity `n` and a real bound `M`, the weight box is the subtype of weight vectors whose
coordinates are all bounded in absolute value by `M`:

```
WeightBox n M = {w : Fin n → ℝ // ∀ i, |w i| ≤ M}
```

Carrying the inherited subtype topology, the box is a compact Hausdorff space for **every** real
`M`;
when `M < 0` it is empty, which is still compact. Identifying the defining condition with a finite
product of closed intervals `Set.Icc (-M) M` gives compactness from finite-product compactness of
the intervals (each interval is compact even when it is empty).

This compact box is the intended codomain for the equal-area weight selection, whose closed graph
together with uniqueness will yield continuity of the selection.
-/

@[expose] public section

namespace NRR.EMP.VariableBody

/-- The **weight box**: weight vectors of arity `n` whose coordinates are bounded by `M` in absolute
value. It is realized as an `abbrev` over a subtype so that the subtype topology and Hausdorff
structure are inherited automatically (no `TopologicalSpace` instance is redeclared). -/
abbrev WeightBox (n : ℕ) (M : ℝ) :=
  {w : Fin n → ℝ // ∀ i, |w i| ≤ M}

namespace WeightBox

variable {n : ℕ} {M : ℝ}

/-- The defining condition of the weight box, phrased as membership in a finite product of the
closed
interval `Set.Icc (-M) M`. -/
theorem setOf_eq_pi :
    {w : Fin n → ℝ | ∀ i, |w i| ≤ M} = Set.pi Set.univ (fun _ : Fin n => Set.Icc (-M) M) := by
  ext w
  simp only [Set.mem_ofPred_eq, Set.mem_pi, Set.mem_univ, forall_true_left, Set.mem_Icc]
  exact ⟨fun h i => abs_le.mp (h i), fun h i => abs_le.mpr (h i)⟩

/-- The defining set of the weight box is compact, being a finite product of compact intervals. -/
theorem isCompact_setOf : IsCompact {w : Fin n → ℝ | ∀ i, |w i| ≤ M} := by
  rw [setOf_eq_pi]
  exact isCompact_univ_pi (fun _ => isCompact_Icc)

/-- The weight box is a compact space for every real `M`; when `M < 0` it is empty but still
compact. -/
noncomputable instance instCompactSpace : CompactSpace (WeightBox n M) :=
  isCompact_iff_compactSpace.mp isCompact_setOf

/-- The coordinate projection of the weight box as a bundled continuous map. -/
def valContinuous (n : ℕ) (M : ℝ) : C(WeightBox n M, Fin n → ℝ) :=
  ⟨fun w => (w : Fin n → ℝ), continuous_subtype_val⟩

@[simp] theorem valContinuous_apply (w : WeightBox n M) :
    valContinuous n M w = (w : Fin n → ℝ) := rfl

/-- The range of the coordinate projection is exactly the defining set of the weight box. -/
theorem range_val :
    (Set.range fun w : WeightBox n M => (w : Fin n → ℝ)) = {w : Fin n → ℝ | ∀ i, |w i| ≤ M} := by
  ext w
  simp only [Set.mem_range, Set.mem_ofPred_eq, Subtype.exists]
  exact ⟨fun ⟨v, hv, hvw⟩ => hvw ▸ hv, fun h => ⟨w, h, rfl⟩⟩

/-- The range of the coordinate projection is closed (it is a finite product of closed intervals).
-/
theorem isClosed_range :
    IsClosed (Set.range fun w : WeightBox n M => (w : Fin n → ℝ)) := by
  rw [range_val, setOf_eq_pi]
  exact isClosed_set_pi (fun _ _ => isClosed_Icc)

/-- Extensionality for the weight box: elements are equal when their coordinate vectors agree. -/
@[ext] theorem ext {u v : WeightBox n M}
    (h : (u : Fin n → ℝ) = (v : Fin n → ℝ)) :
    u = v :=
  Subtype.ext h

end WeightBox

end NRR.EMP.VariableBody
