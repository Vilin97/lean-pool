/-
Copyright (c) 2026 Dmitrii Zakharov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dmitrii Zakharov
-/
module


public import LeanPool.ErdosGinzburgZiv.EGZ.Decomposition.IterationEvents
public import LeanPool.ErdosGinzburgZiv.EGZ.Decomposition.LineageMassMaps

/-!
# Lineage systems associated with certified progress sequences

The progress certificate supplies every field of the geometric mass-map
sequence. A lower bound on event colors supplies the uniform cutoff needed
for low-level ancestor bookkeeping.
-/

@[expose] public section

namespace EGZ.FlagDecomposition.Iteration

variable {p d : ℕ} [Fact p.Prime] {f : FpCoord p d → ℕ}
    {s : ℕ → State p d f} {ε : ℝ} {δ : ℕ → ℝ} {g : ℕ → ℕ}
    (P : ∀ i, Progress (s i) (s (i + 1)) ε (δ i) g)

/-- The lineage mass maps induced by a sequence of iteration progress steps. -/
noncomputable def lineageMassMaps : LineageMassMaps (fun i ↦ (s i).decomposition) where
  minimal i := (s i).minimal
  step i := (P i).subdivision
  cutoff i := (P i).event.cutoff
  level_parent i := (P i).level_parent
  stable i := (P i).stable
  stable_real i := (P i).stable_real
  injective_below i _L hL := (P i).parent_injective.mono (fun _ hx ↦ hx.trans hL)

theorem cutoff_ge_of_colors_ge {L : ℕ} (h : ∀ i, 2 * L ≤ (P i).event.color) :
    ∀ i, L ≤ (lineageMassMaps P).cutoff i :=
  fun i ↦ (P i).event.cutoff_ge_of_color_ge (h i)

include P in
/-- The certified node-count recurrence gives the usual doubling bound. -/
theorem card_nodes_le_pow (n : ℕ) :
    Fintype.card (s n).decomposition.flag.Node ≤
      2 ^ n * Fintype.card (s 0).decomposition.flag.Node := by
  induction n with
  | zero => simp
  | succ n ih =>
    exact (P n).card_le.trans (by
      have hm := Nat.mul_le_mul_left 2 ih
      simpa only [pow_succ, Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm] using hm)

end EGZ.FlagDecomposition.Iteration
