/-
Copyright (c) 2026 Adam Benenson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Benenson
-/
import LeanPool.CencovPetz.Simplex


/-!
# `CencovPetz.SufficientStatistic`

Deterministic “sufficient statistics” in the finite/discrete setting, and monotonicity of the
Fisher quadratic form under such maps.

In classical information geometry (Čencov/Chentsov), a key input is that the Fisher metric is
monotone under sufficient statistics.  For a finite type `α` of outcomes and a surjection
`g : α → β`, the pushforward distribution is obtained by summing over fibers:

`q(b) = ∑_{a : g a = b} p(a)`.

The corresponding tangent vector pushforward is the same fiberwise sum, and the Fisher inequality
reduces to Titu's lemma / Engel form of Cauchy–Schwarz on each fiber.

## Main definitions

- `CencovPetz.Simplex.pushforward`: pushforward of a strictly positive distribution along
  a surjective map, by summing over fibers.
- `CencovPetz.tangentPushforward`: pushforward of a tangent vector along a map, by
  summing over fibers.

## Main results

- `CencovPetz.fisherBilin_pushforward_le`: Fisher quadratic form monotonicity under a
  surjective map (finite sufficient statistic).
-/

namespace LeanPool.CencovPetz
open scoped BigOperators

variable {α β : Type*} [Fintype α] [Fintype β] [DecidableEq β]

namespace Simplex

/-- Pushforward of a strictly positive distribution along a surjective map,
by summing over fibers. -/
noncomputable def pushforward (g : α → β) (hg : Function.Surjective g) (p : Simplex α) :
    Simplex β := by
  classical
  refine
    { p := fun b => ∑ a with g a = b, p.p a
      pos := ?_
      sum_eq_one := ?_ }
  · intro b
    rcases hg b with ⟨a0, rfl⟩
    -- The fiber `{a | g a = g a0}` contains `a0`, and every `p.p a` is nonnegative.
    have h_nonneg : ∀ a : α, 0 ≤ p.p a := fun a => (p.pos a).le
    have h_pos : 0 < ∑ a ∈ (Finset.univ.filter fun a : α => g a = g a0), p.p a := by
      refine Finset.sum_pos' (s := (Finset.univ.filter fun a : α => g a = g a0))
        (f := p.p) (h := fun a _ => h_nonneg a) ?_
      exact ⟨a0, by simp, p.pos a0⟩
    simpa using h_pos
  · -- Normalization follows from summing over fibers.
    have hfib :
        (∑ b : β, ∑ a with g a = b, p.p a) = ∑ a : α, p.p a := by
      simpa using (Finset.sum_fiberwise (s := (Finset.univ : Finset α)) (g := g) (f := p.p))
    simpa [hfib] using p.sum_eq_one

@[simp] lemma pushforward_apply (g : α → β) (hg : Function.Surjective g) (p : Simplex α) (b : β) :
    (pushforward g hg p).p b = ∑ a with g a = b, p.p a :=
  rfl

end Simplex

/-- Pushforward of a tangent vector along a map, by summing over fibers. -/
noncomputable def tangentPushforward (g : α → β) (u : tangentSpace (α := α)) :
    tangentSpace (α := β) := by
  classical
  refine ⟨fun b => ∑ a with g a = b, ((u : α → ℝ) a), ?_⟩
  -- Sum over fibers gives back the original total sum.
  have hfib :
      (∑ b : β, ∑ a with g a = b, ((u : α → ℝ) a)) = ∑ a : α, (u : α → ℝ) a := by
    simpa using
      (Finset.sum_fiberwise (s := (Finset.univ : Finset α)) (g := g) (f := fun a => (u : α → ℝ) a))
  have hu_sum : (∑ a : α, (u : α → ℝ) a) = 0 :=
    (tangentSpace.mem_iff (α := α) (u := (u : α → ℝ))).1 u.property
  -- Finish via the membership characterization of `tangentSpace`.
  refine (tangentSpace.mem_iff (α := β) (u := fun b => ∑ a with g a = b, ((u : α → ℝ) a))).2 ?_
  simp [hfib, hu_sum]

@[simp] lemma tangentPushforward_apply (g : α → β) (u : tangentSpace (α := α)) (b : β) :
    (tangentPushforward (α := α) (β := β) g u : β → ℝ) b = ∑ a with g a = b, ((u : α → ℝ) a) :=
  rfl

/-- Monotonicity of the Fisher quadratic form under a surjective map
(finite sufficient statistic). -/
theorem fisherBilin_pushforward_le (g : α → β) (hg : Function.Surjective g)
    (p : Simplex α) (u : tangentSpace (α := α)) :
    fisherBilin (Simplex.pushforward (α := α) (β := β) g hg p)
        (tangentPushforward (α := α) (β := β) g u)
        (tangentPushforward (α := α) (β := β) g u)
      ≤ fisherBilin p u u := by
  classical
  -- Fiberwise, use Titu's lemma / Engel form.
  have hb (b : β) :
      ((∑ a with g a = b, ((u : α → ℝ) a)) ^ 2) / (∑ a with g a = b, p.p a)
        ≤ ∑ a with g a = b, (((u : α → ℝ) a) ^ 2) / p.p a := by
    -- Convert the filtered sums to explicit finset sums over the fiber, then apply the lemma.
    simpa using
      (Finset.sq_sum_div_le_sum_sq_div (s := (Finset.univ.filter fun a : α => g a = b))
        (f := fun a => (u : α → ℝ) a) (g := fun a => p.p a)
        (hg := fun a _ => p.pos a))
  -- Sum the inequalities over `b`.
  have hsum :
      (∑ b : β, ((∑ a with g a = b, ((u : α → ℝ) a)) ^ 2) / (∑ a with g a = b, p.p a))
        ≤ ∑ b : β, ∑ a with g a = b, (((u : α → ℝ) a) ^ 2) / p.p a := by
    simpa using (Finset.sum_le_sum fun b _ => hb b)
  -- Collapse the right-hand side back to a total sum over `a`.
  have hfib_sq :
      (∑ b : β, ∑ a with g a = b, (((u : α → ℝ) a) ^ 2) / p.p a)
        = ∑ a : α, (((u : α → ℝ) a) ^ 2) / p.p a := by
    simpa using
      (Finset.sum_fiberwise (s := (Finset.univ : Finset α)) (g := g)
        (f := fun a => (((u : α → ℝ) a) ^ 2) / p.p a))
  -- Rewrite both sides as Fisher forms.
  -- LHS: Fisher on β after pushforward.
  have hL :
      fisherBilin (Simplex.pushforward (α := α) (β := β) g hg p)
          (tangentPushforward (α := α) (β := β) g u)
          (tangentPushforward (α := α) (β := β) g u)
        = ∑ b : β, ((∑ a with g a = b, ((u : α → ℝ) a)) ^ 2) / (∑ a with g a = b, p.p a) := by
    -- Expand, then use the pushforward definitions.
    simp [fisherBilin.apply, Simplex.pushforward_apply, tangentPushforward_apply, pow_two]
  have hR :
      fisherBilin p u u = ∑ a : α, (((u : α → ℝ) a) ^ 2) / p.p a := by
    simp [fisherBilin.apply, pow_two]
  -- Assemble.
  simp_all
end LeanPool.CencovPetz
