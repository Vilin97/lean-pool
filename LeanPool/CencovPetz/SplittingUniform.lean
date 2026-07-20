/-
Copyright (c) 2026 Adam Benenson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Benenson
-/
import LeanPool.CencovPetz.Splitting
import LeanPool.CencovPetz.UniformSimplex


/-!
# `CencovPetz.SplittingUniform`

If a simplex point `p` has coordinates proportional to a fiber-multiplicity function `m : α → ℕ`,
then the fiberwise splitting Markov morphism `α → Σ a, Fin (m a)` pushes `p` forward to the
uniform distribution on the split target.

This is one of the standard reduction steps in finite Čencov/Chentsov uniqueness arguments.

## Main result

- `CencovPetz.MarkovMorphism.split_pushforward_eq_uniform_of_apply_eq_div_card`
-/

namespace LeanPool.CencovPetz
open scoped BigOperators

universe u

namespace Simplex

variable {α : Type u} [Fintype α]

/-- A simplex point whose coordinates are proportional to a natural multiplicity function.

Such points become uniform after applying the fiberwise splitting Markov morphism
`α → Σ a, Fin (m a)`. This is the standard “rational-point” reduction step in finite Čencov/Chentsov
arguments.
-/
def IsSplitRepresentable (p : Simplex α) : Prop :=
  ∃ m : α → ℕ,
    (∀ a, 0 < m a) ∧
      ∀ a,
        p.p a = (m a : ℝ) / (Fintype.card (MarkovMorphism.SplitTarget (α := α) m) : ℝ)

end Simplex

namespace MarkovMorphism

variable {α : Type u} [Fintype α] [Nonempty α]

lemma split_pushforward_eq_uniform_of_apply_eq_div_card (m : α → ℕ) (hm : ∀ a, 0 < m a)
    (p : Simplex α)
    (hp : ∀ a, p.p a = (m a : ℝ) / (Fintype.card (SplitTarget (α := α) m) : ℝ)) :
    letI : Nonempty (SplitTarget (α := α) m) := by
      classical
      rcases (inferInstance : Nonempty α) with ⟨a0⟩
      exact ⟨⟨a0, ⟨0, hm a0⟩⟩⟩
    (split (α := α) m hm).pushforward p = Simplex.uniform (α := SplitTarget (α := α) m) := by
  classical
  ext b
  rcases b with ⟨a, i⟩
  have hm0 : (m a : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt (hm a))
  rw [split_pushforward_apply (α := α) (m := m) (hm := hm) (p := p) (a := a) (i := i)]
  simp [Simplex.uniform_apply, hp a, hm0, div_eq_mul_inv, mul_comm]

end MarkovMorphism
end LeanPool.CencovPetz
