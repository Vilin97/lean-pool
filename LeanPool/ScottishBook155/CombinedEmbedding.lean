/-
Copyright (c) 2026 Yoshito Ishiki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yoshito Ishiki
-/
import LeanPool.ScottishBook155.CollapsedQuotient

/-!
# Combining the relative and injectivity coordinates

This module formalizes the abstract final assembly in the protected-extension
proof.  The still-missing relative Banach-envelope map is represented by an
arbitrary first coordinate.  Pairing it with the quotient Kuratowski coordinate
in the max product preserves its metric estimates and supplies global
injectivity once the first coordinate separates the collapsed subset.
-/

namespace ScottishBook155

open ENNReal lp

universe u v

/-- Pair an arbitrary relative coordinate with the quotient Kuratowski
coordinate used to recover injectivity. -/
noncomputable def combinedEmbedding
    {P : Type u} [MetricSpace P] {E : Type v} (relative : P → E) (S : Set P) (base : P) (x : P) :
      E × lp (fun _ : CollapsedQuotient P S ↦ ℝ) ∞ :=
  (relative x, quotientKuratowski S base x)

theorem combinedEmbedding_of_mem
    {P : Type u} [MetricSpace P] {E : Type v} {relative : P → E} {S : Set P} {base x : P}
    (hbase : base ∈ S) (hx : x ∈ S) :
    combinedEmbedding relative S base x = (relative x, 0) := by
  simp [combinedEmbedding, quotientKuratowski_of_mem hbase hx]

theorem combinedEmbedding_eq_iff
    {P : Type u} [MetricSpace P] {E : Type v} {relative : P → E} {S : Set P}
    (hne : S.Nonempty) (hclosed : IsClosed S)
    (base x y : P) :
    combinedEmbedding relative S base x = combinedEmbedding relative S base y ↔
      relative x = relative y ∧ (x = y ∨ (x ∈ S ∧ y ∈ S)) := by
  constructor
  · intro h
    constructor
    · exact congrArg Prod.fst h
    · apply (quotientKuratowski_eq_iff hne hclosed base x y).1
      exact congrArg Prod.snd h
  · rintro ⟨hrelative, hquotient⟩
    apply Prod.ext hrelative
    exact (quotientKuratowski_eq_iff hne hclosed base x y).2 hquotient

/-- The second coordinate separates all pairs except pairs in `S`; hence
injectivity of the first coordinate on `S` implies global injectivity. -/
theorem combinedEmbedding_injective
    {P : Type u} [MetricSpace P] {E : Type v} {relative : P → E} {S : Set P}
    (hne : S.Nonempty) (hclosed : IsClosed S)
    (hrelative : Set.InjOn relative S) (base : P) :
    Function.Injective (combinedEmbedding relative S base) := by
  intro x y hxy
  obtain ⟨hfirst, hsecond⟩ :=
    (combinedEmbedding_eq_iff hne hclosed base x y).1 hxy
  rcases hsecond with h | ⟨hx, hy⟩
  · exact h
  · exact hrelative hx hy hfirst

/-- Pairing two nonexpansive coordinates in the max product is nonexpansive. -/
theorem combinedEmbedding_dist_le
    {P : Type u} [MetricSpace P] {E : Type v} [PseudoMetricSpace E]
    {relative : P → E} (hrelative : ∀ x y, dist (relative x) (relative y) ≤ dist x y)
    (S : Set P) (base x y : P) :
    dist (combinedEmbedding relative S base x) (combinedEmbedding relative S base y) ≤
      dist x y := by
  rw [Prod.dist_eq]
  exact max_le (hrelative x y) (quotientKuratowski_dist_le S base x y)

/-- If the first coordinate preserves a selected distance, then the combined
max-product coordinate preserves it as well. -/
theorem combinedEmbedding_dist_eq
    {P : Type u} [MetricSpace P] {E : Type v} [PseudoMetricSpace E]
    {relative : P → E} {x y : P}
    (hrelative : dist (relative x) (relative y) = dist x y)
    (S : Set P) (base : P) :
    dist (combinedEmbedding relative S base x) (combinedEmbedding relative S base y) =
      dist x y := by
  rw [Prod.dist_eq]
  change max (dist (relative x) (relative y))
      (dist (quotientKuratowski S base x) (quotientKuratowski S base y)) = dist x y
  rw [hrelative]
  exact max_eq_left (quotientKuratowski_dist_le S base x y)

end ScottishBook155
