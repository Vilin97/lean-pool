/-
Copyright (c) 2026 Adam Benenson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Benenson
-/
import LeanPool.CencovPetz.MarkovMorphism


/-!
# `CencovPetz.Splitting`

Fiberwise splitting (dependent replication) Markov morphisms in the finite/discrete setting.

Given a finite type `α` and a multiplicity function `m : α → ℕ` with `0 < m a` for all `a`,
we define:

- a **split** Markov morphism `α → Σ a, Fin (m a)` sending `a` to the uniform distribution on
  its fiber, and
- a **merge** (coarsening) Markov morphism `Σ a, Fin (m a) → α` forgetting the fiber index.

These are left inverses on simplex points and tangent vectors, and are standard tools in finite
Čencov/Chentsov uniqueness proofs.
-/

namespace LeanPool.CencovPetz
open scoped BigOperators

universe u

namespace MarkovMorphism

variable {α : Type u} [Fintype α]

/-- The target type for a fiberwise split: `Σ a, Fin (m a)`. -/
abbrev SplitTarget (m : α → ℕ) : Type u :=
  Sigma fun a : α => Fin (m a)

variable (m : α → ℕ) (hm : ∀ a, 0 < m a)

/-- Fiberwise split: send `a` to the uniform distribution on the fiber `Fin (m a)`. -/
noncomputable def split : MarkovMorphism α (SplitTarget (α := α) m) := by
  classical
  refine
    { K := fun a b => if b.1 = a then (1 : ℝ) / (m a : ℝ) else 0
      nonneg := ?_
      row_sum_eq_one := ?_
      col_pos := ?_ }
  · intro a b
    by_cases h : b.1 = a <;> simp [h]
  · intro a
    have hm_ne : (m a : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt (hm a))
    -- Expand the sigma-sum, discard the non-matching fibers, and sum the constant on `Fin (m a)`.
    calc
      (∑ b : SplitTarget (α := α) m, (if b.1 = a then (1 : ℝ) / (m a : ℝ) else 0))
          = ∑ x : α, ∑ _i : Fin (m x), if x = a then (1 : ℝ) / (m a : ℝ) else 0 := by
              simpa [SplitTarget] using
                (Fintype.sum_sigma (f := fun b : SplitTarget (α := α) m =>
                  if b.1 = a then (1 : ℝ) / (m a : ℝ) else 0))
      _ = ∑ _i : Fin (m a), (1 : ℝ) / (m a : ℝ) := by
            -- Only the fiber over `a` contributes.
            simp [eq_comm]
      _ = (m a : ℝ) * ((1 : ℝ) / (m a : ℝ)) := by
            simp_all
      _ = 1 := by
            -- Cancel `m a`.
            field_simp [hm_ne]
  · intro b
    refine ⟨b.1, ?_⟩
    simp_all

/-- Fiberwise merge: forget the fiber index. -/
noncomputable def merge : MarkovMorphism (SplitTarget (α := α) m) α := by
  classical
  refine
    { K := fun b a => if b.1 = a then (1 : ℝ) else 0
      nonneg := ?_
      row_sum_eq_one := ?_
      col_pos := ?_ }
  · intro b a
    by_cases h : b.1 = a <;> simp [h]
  · intro b
    -- Exactly one `a` matches `b.1`.
    simp
  · intro a
    refine ⟨⟨a, ⟨0, hm a⟩⟩, by simp⟩

lemma split_pushforward_apply (p : Simplex α) (a : α) (i : Fin (m a)) :
    ((split (α := α) m hm).pushforward p).p ⟨a, i⟩ = p.p a / (m a : ℝ) := by
  classical
  simp [MarkovMorphism.pushforward_apply, split, mul_ite, div_eq_mul_inv, eq_comm]

lemma split_tangentPushforward_apply (u : tangentSpace (α := α)) (a : α) (i : Fin (m a)) :
    (((split (α := α) m hm).tangentPushforward u : SplitTarget (α := α) m → ℝ) ⟨a, i⟩)
      = (u : α → ℝ) a / (m a : ℝ) := by
  classical
  simp [MarkovMorphism.tangentPushforward_apply, split, mul_ite, div_eq_mul_inv, eq_comm]

lemma merge_pushforward_split (p : Simplex α) :
    (merge (α := α) m hm).pushforward ((split (α := α) m hm).pushforward p) = p := by
  classical
  ext a
  have hm_ne : (m a : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt (hm a))
  -- Expand `merge` pushforward, rewrite the sigma-sum, and evaluate the resulting constant sum.
  calc
    ((merge (α := α) m hm).pushforward ((split (α := α) m hm).pushforward p)).p a
        = ∑ b : SplitTarget (α := α) m,
            ((split (α := α) m hm).pushforward p).p b * if b.1 = a then (1 : ℝ) else 0 := by
              simp [MarkovMorphism.pushforward_apply, merge]
    _ = ∑ x : α, ∑ i : Fin (m x),
            ((split (α := α) m hm).pushforward p).p ⟨x, i⟩ * if x = a then (1 : ℝ) else 0 := by
          simpa [SplitTarget] using
            (Fintype.sum_sigma (f := fun b : SplitTarget (α := α) m =>
              ((split (α := α) m hm).pushforward p).p b * if b.1 = a then (1 : ℝ) else 0))
    _ = ∑ x : α, if x = a
          then ∑ i : Fin (m x),
            ((split (α := α) m hm).pushforward p).p ⟨x, i⟩
          else 0 := by
          simp_all
    _ = ∑ i : Fin (m a), ((split (α := α) m hm).pushforward p).p ⟨a, i⟩ := by
          -- Only the `x = a` term survives.
          simp [eq_comm]
    _ = ∑ _i : Fin (m a), p.p a / (m a : ℝ) := by
          simp only [split_pushforward_apply]
    _ = p.p a := by
          -- `m a` copies, each `p(a)/m(a)`.
          have :
              (∑ _i : Fin (m a), p.p a / (m a : ℝ)) =
                (m a : ℝ) * (p.p a / (m a : ℝ)) := by
            classical
            simp [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
          -- Cancel `m a`.
          calc
            (∑ _i : Fin (m a), p.p a / (m a : ℝ))
                = (m a : ℝ) * (p.p a / (m a : ℝ)) := this
            _ = p.p a := by
                  field_simp [hm_ne]

lemma merge_tangentPushforward_split (u : tangentSpace (α := α)) :
    (merge (α := α) m hm).tangentPushforward ((split (α := α) m hm).tangentPushforward u) = u := by
  classical
  ext a
  have hm_ne : (m a : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt (hm a))
  calc
    ((merge (α := α) m hm).tangentPushforward
        ((split (α := α) m hm).tangentPushforward u) :
        α → ℝ) a
        = ∑ b : SplitTarget (α := α) m,
            (((split (α := α) m hm).tangentPushforward u : SplitTarget (α := α) m → ℝ) b) *
              if b.1 = a then (1 : ℝ) else 0 := by
              simp [MarkovMorphism.tangentPushforward_apply, merge]
    _ = ∑ x : α, ∑ i : Fin (m x),
            (((split (α := α) m hm).tangentPushforward u : SplitTarget (α := α) m → ℝ) ⟨x, i⟩) *
              if x = a then (1 : ℝ) else 0 := by
          simpa [SplitTarget] using
            (Fintype.sum_sigma (f := fun b : SplitTarget (α := α) m =>
              (((split (α := α) m hm).tangentPushforward u : SplitTarget (α := α) m → ℝ) b) *
                if b.1 = a then (1 : ℝ) else 0))
    _ = ∑ x : α, if x = a
          then ∑ i : Fin (m x),
            (((split (α := α) m hm).tangentPushforward u :
              SplitTarget (α := α) m → ℝ) ⟨x, i⟩)
          else 0 := by
          simp_all
    _ = ∑ i : Fin (m a),
          ((split (α := α) m hm).tangentPushforward u :
            SplitTarget (α := α) m → ℝ) ⟨a, i⟩ := by
          simp [eq_comm]
    _ = ∑ _i : Fin (m a), (u : α → ℝ) a / (m a : ℝ) := by
          simp only [split_tangentPushforward_apply]
    _ = (u : α → ℝ) a := by
          have :
              (∑ _i : Fin (m a), (u : α → ℝ) a / (m a : ℝ)) =
                (m a : ℝ) * ((u : α → ℝ) a / (m a : ℝ)) := by
            classical
            simp [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
          calc
            (∑ _i : Fin (m a), (u : α → ℝ) a / (m a : ℝ))
                = (m a : ℝ) * ((u : α → ℝ) a / (m a : ℝ)) := this
            _ = (u : α → ℝ) a := by
                  field_simp [hm_ne]

end MarkovMorphism
end LeanPool.CencovPetz
