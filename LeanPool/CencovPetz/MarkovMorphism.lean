/-
Copyright (c) 2026 Adam Benenson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Benenson
-/
import LeanPool.CencovPetz.Simplex


/-!
# `CencovPetz.MarkovMorphism`

Finite/discrete Markov morphisms (row-stochastic matrices) and monotonicity of the Fisher
quadratic form.

This is the “general Markov morphism” version of the deterministic sufficient-statistic result in
`CencovPetz.SufficientStatistic`. It provides the main finite-data-processing inequality
needed for the Čencov/Chentsov uniqueness story.

## Main definitions

- `CencovPetz.MarkovMorphism α β`: a row-stochastic matrix `K : α → β → ℝ` together with a
  mild positivity condition ensuring it maps the **open** simplex to the open simplex.
- `CencovPetz.MarkovMorphism.pushforward`: pushforward of a `Simplex α` along `K`.
- `CencovPetz.MarkovMorphism.tangentPushforward`: pushforward of tangent vectors.

## Main result

- `CencovPetz.fisherBilin_pushforward_le_of_markovMorphism`: Fisher monotonicity under a
  Markov morphism.
-/

namespace LeanPool.CencovPetz
open scoped BigOperators

variable {α β : Type*} [Fintype α] [Fintype β]

/-- A finite Markov morphism `α → β`, presented as a row-stochastic matrix.

We additionally assume every output coordinate is reachable with positive probability from some
input (`col_pos`). This ensures the pushforward of a strictly positive distribution is again
strictly positive, so we stay on the **open** simplex where the Fisher metric is nondegenerate.
-/
structure MarkovMorphism (α β : Type*) [Fintype α] [Fintype β] : Type _ where
  /-- Transition weights `K a b`. -/
  K : α → β → ℝ
  /-- Nonnegativity. -/
  nonneg : ∀ a b, 0 ≤ K a b
  /-- Each row sums to `1`. -/
  row_sum_eq_one : ∀ a, (∑ b, K a b) = 1
  /-- Each column has a strictly positive entry (so the open simplex maps to the open simplex). -/
  col_pos : ∀ b, ∃ a, 0 < K a b

namespace MarkovMorphism

variable (κ : MarkovMorphism α β)

/-- The deterministic Markov morphism induced by a surjective map `g : α → β`:
`K a b = 1` if `g a = b`, else `0`. -/
noncomputable def deterministic (g : α → β) (hg : Function.Surjective g) : MarkovMorphism α β := by
  classical
  refine
    { K := fun a b => if g a = b then (1 : ℝ) else 0
      nonneg := ?_
      row_sum_eq_one := ?_
      col_pos := ?_ }
  · intro a b
    by_cases h : g a = b <;> simp [h]
  · intro a
    simp
  · intro b
    rcases hg b with ⟨a0, rfl⟩
    refine ⟨a0, ?_⟩
    simp

/-- Pushforward of a distribution `p` along a Markov morphism `κ`. -/
noncomputable def pushforward (p : Simplex α) : Simplex β := by
  classical
  refine
    { p := fun b => ∑ a, p.p a * κ.K a b
      pos := ?_
      sum_eq_one := ?_ }
  · intro b
    rcases κ.col_pos b with ⟨a0, ha0⟩
    have h_nonneg : ∀ a : α, 0 ≤ p.p a * κ.K a b :=
      fun a => mul_nonneg (p.pos a).le (κ.nonneg a b)
    have h_pos : 0 < ∑ a : α, p.p a * κ.K a b := by
      -- Use that one term is strictly positive.
      refine Finset.sum_pos' (s := (Finset.univ : Finset α))
        (f := fun a => p.p a * κ.K a b) (h := fun a _ => h_nonneg a) ?_
      refine ⟨a0, by simp, mul_pos (p.pos a0) ha0⟩
    simpa using h_pos
  · -- `∑_b ∑_a p(a) K(a,b) = ∑_a p(a) (∑_b K(a,b)) = ∑_a p(a)`.
    have hcomm :
        (∑ b : β, ∑ a : α, p.p a * κ.K a b) =
          ∑ a : α, ∑ b : β, p.p a * κ.K a b := by
      simpa using
        (Finset.sum_comm (s := (Finset.univ : Finset β)) (t := (Finset.univ : Finset α))
          (f := fun b a => p.p a * κ.K a b))
    calc
      (∑ b : β, ∑ a : α, p.p a * κ.K a b)
          = ∑ a : α, ∑ b : β, p.p a * κ.K a b := hcomm
      _ = ∑ a : α, p.p a * (∑ b : β, κ.K a b) := by
            refine Finset.sum_congr rfl (fun a _ => ?_)
            simp [Finset.mul_sum]
      _ = ∑ a : α, p.p a := by simp [κ.row_sum_eq_one]
      _ = 1 := p.sum_eq_one

/-- Pushforward of a tangent vector along a Markov morphism. -/
noncomputable def tangentPushforward (u : tangentSpace (α := α)) : tangentSpace (α := β) := by
  classical
  refine ⟨fun b => ∑ a : α, ((u : α → ℝ) a) * κ.K a b, ?_⟩
  -- Prove the pushed-forward vector has total sum `0`.
  have hcomm :
      (∑ b : β, ∑ a : α, ((u : α → ℝ) a) * κ.K a b) =
        ∑ a : α, ∑ b : β, ((u : α → ℝ) a) * κ.K a b := by
    simpa using
      (Finset.sum_comm (s := (Finset.univ : Finset β)) (t := (Finset.univ : Finset α))
        (f := fun b a => ((u : α → ℝ) a) * κ.K a b))
  have hu_sum : (∑ a : α, (u : α → ℝ) a) = 0 :=
    (tangentSpace.mem_iff (α := α) (u := (u : α → ℝ))).1 u.property
  refine (tangentSpace.mem_iff (α := β) (u := fun b => ∑ a : α, ((u : α → ℝ) a) * κ.K a b)).2 ?_
  calc
    (∑ b : β, (∑ a : α, ((u : α → ℝ) a) * κ.K a b))
        = ∑ a : α, ∑ b : β, ((u : α → ℝ) a) * κ.K a b := hcomm
    _ = ∑ a : α, (u : α → ℝ) a * (∑ b : β, κ.K a b) := by
          refine Finset.sum_congr rfl (fun a _ => ?_)
          simp [Finset.mul_sum]
    _ = ∑ a : α, (u : α → ℝ) a := by simp [κ.row_sum_eq_one]
    _ = 0 := hu_sum

@[simp] lemma pushforward_apply (p : Simplex α) (b : β) :
    (κ.pushforward p).p b = ∑ a : α, p.p a * κ.K a b :=
  rfl

@[simp] lemma tangentPushforward_apply (u : tangentSpace (α := α)) (b : β) :
    (κ.tangentPushforward u : β → ℝ) b = ∑ a : α, ((u : α → ℝ) a) * κ.K a b :=
  rfl

/-- `tangentPushforward` packaged as a linear map. -/
noncomputable def tangentPushforwardLinear : tangentSpace (α := α) →ₗ[ℝ] tangentSpace (α := β) := by
  classical
  refine
    { toFun := κ.tangentPushforward
      map_add' := ?_
      map_smul' := ?_ }
  · intro u v
    ext b
    simp [MarkovMorphism.tangentPushforward_apply, Pi.add_apply, add_mul, Finset.sum_add_distrib]
  · intro c u
    ext b
    simp [MarkovMorphism.tangentPushforward_apply, Pi.smul_apply, smul_eq_mul,
      mul_assoc, Finset.mul_sum]

@[simp] lemma tangentPushforwardLinear_apply (u : tangentSpace (α := α)) :
    κ.tangentPushforwardLinear u = κ.tangentPushforward u :=
  rfl

/-- Pushforward along a deterministic morphism is fiberwise summation. -/
lemma deterministic_pushforward_apply [DecidableEq β] (g : α → β) (hg : Function.Surjective g)
    (p : Simplex α) (b : β) :
    ((deterministic (α := α) (β := β) g hg).pushforward p).p b = ∑ a with g a = b, p.p a := by
  classical
  -- Expand the deterministic kernel, then convert an `if`-sum to a filtered sum.
  have :
      (∑ a : α, if g a = b then p.p a else 0) = ∑ a with g a = b, p.p a := by
    simpa using
      (Finset.sum_filter (s := (Finset.univ : Finset α)) (p := fun a : α => g a = b)
        (f := fun a => p.p a)).symm
  simp [deterministic, pushforward, mul_ite, this]

/-- Tangent pushforward along a deterministic morphism is fiberwise summation. -/
lemma deterministic_tangentPushforward_apply [DecidableEq β]
    (g : α → β) (hg : Function.Surjective g)
    (u : tangentSpace (α := α)) (b : β) :
    ((deterministic (α := α) (β := β) g hg).tangentPushforward u : β → ℝ) b =
      ∑ a with g a = b, ((u : α → ℝ) a) := by
  classical
  -- Expand the deterministic kernel, then convert an `if`-sum to a filtered sum.
  have :
      (∑ a : α, if g a = b then (u : α → ℝ) a else 0) = ∑ a with g a = b, (u : α → ℝ) a := by
    simpa using
      (Finset.sum_filter (s := (Finset.univ : Finset α)) (p := fun a : α => g a = b)
        (f := fun a => (u : α → ℝ) a)).symm
  simp [deterministic, tangentPushforward, mul_ite, this]

end MarkovMorphism

/-- Fisher monotonicity under a finite Markov morphism. -/
theorem fisherBilin_pushforward_le_of_markovMorphism (κ : MarkovMorphism α β)
    (p : Simplex α) (u : tangentSpace (α := α)) :
    fisherBilin (κ.pushforward p) (κ.tangentPushforward u) (κ.tangentPushforward u) ≤
      fisherBilin p u u := by
  classical
  -- Expand both sides.
  simp only [fisherBilin.apply, MarkovMorphism.pushforward_apply,
    MarkovMorphism.tangentPushforward_apply]
  -- It suffices to prove the inequality termwise in `b` and sum.
  have hb (b : β) :
      ((∑ a : α, (u : α → ℝ) a * κ.K a b) * ∑ a : α, (u : α → ℝ) a * κ.K a b) /
            (∑ a : α, p.p a * κ.K a b)
        ≤ ∑ a : α, (((u : α → ℝ) a) * (u : α → ℝ) a) / p.p a * κ.K a b := by
    -- Cauchy–Schwarz in “Engel form” on the finite index set `α`.
    have hf (a : α) : 0 ≤ (((u : α → ℝ) a) ^ 2) / p.p a * κ.K a b := by
      have hp_pos : 0 < p.p a := p.pos a
      have : 0 ≤ (((u : α → ℝ) a) ^ 2) / p.p a :=
        div_nonneg (sq_nonneg _) (le_of_lt hp_pos)
      exact mul_nonneg this (κ.nonneg a b)
    have hg (a : α) : 0 ≤ p.p a * κ.K a b :=
      mul_nonneg (p.pos a).le (κ.nonneg a b)
    have ht (a : α) :
        (((u : α → ℝ) a) * κ.K a b) ^ 2 =
          ((((u : α → ℝ) a) ^ 2) / p.p a * κ.K a b) * (p.p a * κ.K a b) := by
      -- Expand and cancel `p.p a`.
      have hp_ne : p.p a ≠ 0 := ne_of_gt (p.pos a)
      -- `^2` is `pow_two`.
      -- We keep the proof `simp`-driven (upstream-friendly).
      simp [pow_two, div_eq_mul_inv, hp_ne, mul_assoc, mul_left_comm, mul_comm]
    have hcs :
        (∑ a : α, (u : α → ℝ) a * κ.K a b) ^ 2
          ≤ (∑ a : α, (((u : α → ℝ) a) ^ 2) / p.p a * κ.K a b) * (∑ a : α, p.p a * κ.K a b) := by
      -- Use the finset lemma on `Finset.univ`.
      simpa using
        (Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul (s := (Finset.univ : Finset α))
          (r := fun a => (u : α → ℝ) a * κ.K a b)
          (f := fun a => (((u : α → ℝ) a) ^ 2) / p.p a * κ.K a b)
          (g := fun a => p.p a * κ.K a b)
          (fun a _ => hf a) (fun a _ => hg a) (fun a _ => le_of_eq (ht a)))
    have hden_pos : 0 < ∑ a : α, p.p a * κ.K a b := by
      rcases κ.col_pos b with ⟨a0, ha0⟩
      have h_nonneg' : ∀ a : α, 0 ≤ p.p a * κ.K a b := hg
      -- One term is positive.
      refine Finset.sum_pos' (s := (Finset.univ : Finset α))
        (f := fun a => p.p a * κ.K a b) (h := fun a _ => h_nonneg' a) ?_
      exact ⟨a0, by simp, mul_pos (p.pos a0) ha0⟩
    -- Divide the Cauchy–Schwarz inequality by the (positive) denominator.
    have hdiv :
        ((∑ a : α, (u : α → ℝ) a * κ.K a b) ^ 2) / (∑ a : α, p.p a * κ.K a b)
          ≤ ∑ a : α, (((u : α → ℝ) a) ^ 2) / p.p a * κ.K a b :=
      (div_le_iff₀ hden_pos).2 (by simpa [mul_assoc] using hcs)
    -- Rewrite `x^2` as `x*x` and align `u^2` with `u*u`.
    simpa [pow_two, mul_assoc, mul_left_comm, mul_comm] using hdiv
  -- Sum over `b`.
  have hsum :
      (∑ b : β,
            ((∑ a : α, (u : α → ℝ) a * κ.K a b) * ∑ a : α, (u : α → ℝ) a * κ.K a b) /
              (∑ a : α, p.p a * κ.K a b))
        ≤ ∑ b : β, ∑ a : α, (((u : α → ℝ) a) * (u : α → ℝ) a) / p.p a * κ.K a b := by
    simpa using (Finset.sum_le_sum fun b _ => hb b)
  -- Swap sums on the right and use row-stochasticity.
  have hcomm :
      (∑ b : β, ∑ a : α, (((u : α → ℝ) a) * (u : α → ℝ) a) / p.p a * κ.K a b)
        = ∑ a : α, ∑ b : β, (((u : α → ℝ) a) * (u : α → ℝ) a) / p.p a * κ.K a b := by
    simpa using
      (Finset.sum_comm (s := (Finset.univ : Finset β)) (t := (Finset.univ : Finset α))
        (f := fun b a => (((u : α → ℝ) a) * (u : α → ℝ) a) / p.p a * κ.K a b))
  calc
    (∑ b : β,
          ((∑ a : α, (u : α → ℝ) a * κ.K a b) * ∑ a : α, (u : α → ℝ) a * κ.K a b) /
            (∑ a : α, p.p a * κ.K a b))
        ≤ ∑ b : β, ∑ a : α, (((u : α → ℝ) a) * (u : α → ℝ) a) / p.p a * κ.K a b := hsum
    _ = ∑ a : α, ∑ b : β, (((u : α → ℝ) a) * (u : α → ℝ) a) / p.p a * κ.K a b := hcomm
    _ = ∑ a : α, (((u : α → ℝ) a) * (u : α → ℝ) a) / p.p a := by
          -- Pull the `a`-dependent coefficient out and use `∑_b K(a,b) = 1`.
          refine Finset.sum_congr rfl (fun a _ => ?_)
          have :
              (∑ b : β, (((u : α → ℝ) a) * (u : α → ℝ) a) / p.p a * κ.K a b)
                = (((u : α → ℝ) a) * (u : α → ℝ) a) / p.p a * (∑ b : β, κ.K a b) := by
            -- `∑ (f b * c) = (∑ f b) * c`.
            simpa [mul_assoc, mul_left_comm, mul_comm] using
              (Finset.sum_mul (s := (Finset.univ : Finset β)) (f := fun b => κ.K a b)
                (a := (((u : α → ℝ) a) * (u : α → ℝ) a) / p.p a)).symm
          simp [this, κ.row_sum_eq_one a]
    _ = ∑ a : α, ((u : α → ℝ) a * (u : α → ℝ) a) / p.p a := rfl
end LeanPool.CencovPetz
