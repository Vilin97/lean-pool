/-
Copyright (c) 2026 Adam Benenson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Benenson
-/
import LeanPool.CencovPetz.RationalPoint
import LeanPool.CencovPetz.SimplexTopology
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Algebra.Order.Ring.Star


/-!
# `CencovPetz.RationalDensity`

Density of common-denominator (“rational”) points in the finite open simplex.

This is the final topological input for the finite Čencov/Chentsov argument: once the metric
identity is proved on the dense family of rational points, continuity hypotheses extend it to all
simplex points.

## Main result

- `CencovPetz.Simplex.dense_setOf_isRational`
-/

namespace LeanPool.CencovPetz
open scoped BigOperators

namespace Simplex

open Filter Topology

variable {α : Type*} [Fintype α]

noncomputable section

private def approxWeight (p : Simplex α) (n : ℕ) (a : α) : ℕ :=
  Nat.floor (p.p a * (n + 1)) + 1

private def approxDenom (p : Simplex α) (n : ℕ) : ℕ :=
  ∑ a : α, approxWeight (p := p) n a

private lemma approxWeight_pos (p : Simplex α) (n : ℕ) (a : α) :
    0 < approxWeight (p := p) n a := by
  simp [approxWeight]

variable [Nonempty α]

private lemma approxDenom_pos (p : Simplex α) (n : ℕ) :
    0 < approxDenom (p := p) n := by
  classical
  have : 0 < ∑ a : α, approxWeight (p := p) n a := by
    simpa using
      (Finset.sum_pos (s := (Finset.univ : Finset α))
        (f := fun a => approxWeight (p := p) n a)
        (by intro a ha; exact approxWeight_pos (p := p) n a)
        (Finset.univ_nonempty))
  simpa [approxDenom] using this

private def approx (p : Simplex α) (n : ℕ) : Simplex α where
  p := fun a => (approxWeight (p := p) n a : ℝ) / (approxDenom (p := p) n : ℝ)
  pos := by
    intro a
    have hw : 0 < (approxWeight (p := p) n a : ℝ) := by
      exact_mod_cast approxWeight_pos (p := p) n a
    have hD : 0 < (approxDenom (p := p) n : ℝ) := by
      exact_mod_cast approxDenom_pos (p := p) n
    exact div_pos hw hD
  sum_eq_one := by
    classical
    let D : ℕ := approxDenom (p := p) n
    have hDpos : 0 < D := by
      simpa [D] using approxDenom_pos (p := p) n
    have hDne : (D : ℝ) ≠ 0 := by
      exact_mod_cast (Nat.ne_of_gt hDpos)
    calc
      (∑ a : α, (approxWeight (p := p) n a : ℝ) / (D : ℝ))
          = (∑ a : α, (approxWeight (p := p) n a : ℝ)) / (D : ℝ) := by
              simp [div_eq_mul_inv, Finset.sum_mul]
      _ = (D : ℝ) / (D : ℝ) := by
            simp [D, approxDenom]
      _ = 1 := by
            field_simp [hDne]

private lemma approx_isRational (p : Simplex α) (n : ℕ) :
    IsRational (α := α) (approx (p := p) n) := by
  classical
  refine ⟨approxWeight (p := p) n, ?_, ?_⟩
  · intro a
    exact approxWeight_pos (p := p) n a
  · intro a
    simp [approx, approxDenom]

omit [Nonempty α] in
private lemma approxWeight_lower (p : Simplex α) (n : ℕ) (a : α) :
    p.p a * (n + 1 : ℝ) ≤ (approxWeight (p := p) n a : ℝ) := by
  have :
      p.p a * (n + 1 : ℝ) < (Nat.floor (p.p a * (n + 1 : ℝ)) : ℝ) + 1 :=
    Nat.lt_floor_add_one (p.p a * (n + 1 : ℝ))
  simpa [approxWeight, Nat.cast_add] using le_of_lt this

omit [Nonempty α] in
private lemma approxWeight_upper (p : Simplex α) (n : ℕ) (a : α) :
    (approxWeight (p := p) n a : ℝ) ≤ p.p a * (n + 1 : ℝ) + 1 := by
  have h0 : 0 ≤ p.p a * (n + 1 : ℝ) := by
    have hp : 0 ≤ p.p a := le_of_lt (p.pos a)
    have hn : 0 ≤ (n + 1 : ℝ) := by exact_mod_cast (Nat.zero_le (n + 1))
    exact mul_nonneg hp hn
  have hf : (Nat.floor (p.p a * (n + 1 : ℝ)) : ℝ) ≤ p.p a * (n + 1 : ℝ) :=
    Nat.floor_le h0
  have : (Nat.floor (p.p a * (n + 1 : ℝ)) : ℝ) + 1 ≤ p.p a * (n + 1 : ℝ) + 1 := by
    linarith
  simpa [approxWeight, Nat.cast_add] using this

omit [Nonempty α] in
private lemma approxDenom_lower (p : Simplex α) (n : ℕ) :
    (n + 1 : ℝ) ≤ (approxDenom (p := p) n : ℝ) := by
  classical
  have hsum :
      (∑ a : α, p.p a * (n + 1 : ℝ)) ≤ ∑ a : α, (approxWeight (p := p) n a : ℝ) := by
    simpa using
      (Finset.sum_le_sum (s := (Finset.univ : Finset α))
        (fun a ha => approxWeight_lower (p := p) n a))
  have hleft : (∑ a : α, p.p a * (n + 1 : ℝ)) = (n + 1 : ℝ) := by
    have : (∑ a : α, p.p a * (n + 1 : ℝ)) = (∑ a : α, p.p a) * (n + 1 : ℝ) := by
      simpa using
        (Finset.sum_mul (s := (Finset.univ : Finset α))
          (f := fun a => p.p a) (a := (n + 1 : ℝ))).symm
    simp [this, p.sum_eq_one]
  have hright : (∑ a : α, (approxWeight (p := p) n a : ℝ)) = (approxDenom (p := p) n : ℝ) := by
    simp [approxDenom]
  simpa [hleft, hright] using hsum

omit [Nonempty α] in
private lemma approxDenom_upper (p : Simplex α) (n : ℕ) :
    (approxDenom (p := p) n : ℝ) ≤ (n + 1 : ℝ) + Fintype.card α := by
  classical
  have hsum :
      (∑ a : α, (approxWeight (p := p) n a : ℝ)) ≤ ∑ a : α, (p.p a * (n + 1 : ℝ) + 1) := by
    simpa using
      (Finset.sum_le_sum (s := (Finset.univ : Finset α))
        (fun a ha => approxWeight_upper (p := p) n a))
  have hright : (∑ a : α, (p.p a * (n + 1 : ℝ) + 1)) = (n + 1 : ℝ) + Fintype.card α := by
    have :
        (∑ a : α, (p.p a * (n + 1 : ℝ) + 1)) =
          (∑ a : α, p.p a * (n + 1 : ℝ)) + (∑ a : α, (1 : ℝ)) := by
      simp [Finset.sum_add_distrib]
    have hsum1 : (∑ a : α, p.p a * (n + 1 : ℝ)) = (n + 1 : ℝ) := by
      have : (∑ a : α, p.p a * (n + 1 : ℝ)) = (∑ a : α, p.p a) * (n + 1 : ℝ) := by
        simpa using
          (Finset.sum_mul (s := (Finset.univ : Finset α))
            (f := fun a => p.p a) (a := (n + 1 : ℝ))).symm
      simp [this, p.sum_eq_one]
    simp_all
  have hleft : (∑ a : α, (approxWeight (p := p) n a : ℝ)) = (approxDenom (p := p) n : ℝ) := by
    simp [approxDenom]
  simpa [hleft, hright] using hsum

private lemma approx_coord_lower (p : Simplex α) (n : ℕ) (a : α) :
    p.p a * (n + 1 : ℝ) / ((n + 1 : ℝ) + Fintype.card α)
      ≤ (approx (p := p) n).p a := by
  have hDpos : 0 < (approxDenom (p := p) n : ℝ) := by
    exact_mod_cast approxDenom_pos (p := p) n
  have hDn :
      (approxDenom (p := p) n : ℝ) ≤ (n + 1 : ℝ) + Fintype.card α :=
    approxDenom_upper (p := p) n
  have hx0 : 0 ≤ p.p a * (n + 1 : ℝ) := by
    have hp : 0 ≤ p.p a := le_of_lt (p.pos a)
    have hn : 0 ≤ (n + 1 : ℝ) := by exact_mod_cast (Nat.zero_le (n + 1))
    exact mul_nonneg hp hn
  have h1 :
      p.p a * (n + 1 : ℝ) / ((n + 1 : ℝ) + Fintype.card α)
        ≤ p.p a * (n + 1 : ℝ) / (approxDenom (p := p) n : ℝ) :=
    div_le_div_of_nonneg_left hx0 hDpos hDn
  have h2 :
      p.p a * (n + 1 : ℝ) / (approxDenom (p := p) n : ℝ)
        ≤ (approxWeight (p := p) n a : ℝ) / (approxDenom (p := p) n : ℝ) :=
    div_le_div_of_nonneg_right (approxWeight_lower (p := p) n a) (le_of_lt hDpos)
  simpa [approx, approxDenom] using le_trans h1 h2

private lemma approx_coord_upper (p : Simplex α) (n : ℕ) (a : α) :
    (approx (p := p) n).p a ≤ p.p a + 1 / (n + 1 : ℝ) := by
  have hDpos : 0 < (approxDenom (p := p) n : ℝ) := by
    exact_mod_cast approxDenom_pos (p := p) n
  have hNpos : 0 < (n + 1 : ℝ) := by exact_mod_cast Nat.succ_pos n
  have hND : (n + 1 : ℝ) ≤ (approxDenom (p := p) n : ℝ) :=
    approxDenom_lower (p := p) n
  have hw0 : 0 ≤ (approxWeight (p := p) n a : ℝ) := by
    exact_mod_cast (Nat.zero_le (approxWeight (p := p) n a))
  have h1 :
      (approxWeight (p := p) n a : ℝ) / (approxDenom (p := p) n : ℝ)
        ≤ (approxWeight (p := p) n a : ℝ) / (n + 1 : ℝ) :=
    div_le_div_of_nonneg_left hw0 hNpos hND
  have h2 :
      (approxWeight (p := p) n a : ℝ) / (n + 1 : ℝ)
        ≤ (p.p a * (n + 1 : ℝ) + 1) / (n + 1 : ℝ) :=
    div_le_div_of_nonneg_right (approxWeight_upper (p := p) n a) (le_of_lt hNpos)
  have h3 : (p.p a * (n + 1 : ℝ) + 1) / (n + 1 : ℝ) = p.p a + 1 / (n + 1 : ℝ) := by
    have hn : (n + 1 : ℝ) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero n
    calc
      (p.p a * (n + 1 : ℝ) + 1) / (n + 1 : ℝ)
          = (p.p a * (n + 1 : ℝ)) / (n + 1 : ℝ) + 1 / (n + 1 : ℝ) := by
              simp [add_div]
      _ = p.p a + 1 / (n + 1 : ℝ) := by
              simp [hn]
  simpa [approx, approxDenom, h3] using le_trans (le_trans h1 h2) (le_of_eq h3)

private lemma tendsto_approx_coord (p : Simplex α) (a : α) :
    Filter.Tendsto (fun n : ℕ => (approx (p := p) n).p a) Filter.atTop (𝓝 (p.p a)) := by
  classical
  -- Lower function tends to `p(a)`.
  have hLower :
      Filter.Tendsto
          (fun n : ℕ =>
            p.p a * (n + 1 : ℝ) / ((n + 1 : ℝ) + Fintype.card α))
          Filter.atTop (𝓝 (p.p a)) := by
    let f : ℕ → ℝ := fun n : ℕ => (n : ℝ) / (n + (Fintype.card α : ℝ))
    have hbase : Filter.Tendsto f Filter.atTop (𝓝 (1 : ℝ)) := by
      simpa [f] using (tendsto_natCast_div_add_atTop (𝕜 := ℝ) (Fintype.card α : ℝ))
    have hshift : Filter.Tendsto (fun n : ℕ => f (n + 1)) Filter.atTop (𝓝 (1 : ℝ)) :=
      (tendsto_add_atTop_iff_nat 1).2 hbase
    have hmul :
        Filter.Tendsto (fun n : ℕ => p.p a * f (n + 1)) Filter.atTop (𝓝 (p.p a * (1 : ℝ))) :=
      (tendsto_const_nhds.mul hshift)
    have hrewrite :
        (fun n : ℕ => p.p a * f (n + 1)) =
          fun n : ℕ => p.p a * (n + 1 : ℝ) / ((n + 1 : ℝ) + Fintype.card α) := by
      funext n
      simp [f, mul_div_assoc, add_comm, add_left_comm]
    simpa [hrewrite] using hmul
  -- Upper function tends to `p(a)`.
  have hUpper :
      Filter.Tendsto (fun n : ℕ => p.p a + 1 / (n + 1 : ℝ)) Filter.atTop (𝓝 (p.p a)) := by
    have h1 : Filter.Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 1)) Filter.atTop (𝓝 (0 : ℝ)) := by
      simpa using (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
    have h2 :
        Filter.Tendsto (fun n : ℕ => p.p a + 1 / ((n : ℝ) + 1)) Filter.atTop (𝓝 (p.p a + 0)) :=
      (tendsto_const_nhds.add h1)
    simpa [Nat.cast_add, add_assoc, add_comm, add_left_comm] using h2
  refine
    tendsto_of_tendsto_of_tendsto_of_le_of_le hLower hUpper
      (fun n => approx_coord_lower (p := p) n a) (fun n => approx_coord_upper (p := p) n a)

private lemma tendsto_approx_p (p : Simplex α) :
    Filter.Tendsto (fun n : ℕ => (approx (p := p) n).p) Filter.atTop (𝓝 p.p) := by
  -- Reduce to coordinates.
  rw [tendsto_pi_nhds]
  intro a
  exact tendsto_approx_coord (p := p) a

private lemma tendsto_approx (p : Simplex α) :
    Filter.Tendsto (fun n : ℕ => approx (p := p) n) Filter.atTop (𝓝 p) := by
  -- Unfold the induced topology on `Simplex α`.
  -- `nhds_induced` turns the goal into convergence of coordinates.
  rw [nhds_induced]
  exact Filter.map_le_iff_le_comap.mp
    (by
      change Filter.map (fun n : ℕ => (approx (p := p) n).p) Filter.atTop ≤ 𝓝 p.p
      exact tendsto_approx_p (p := p))

lemma dense_setOf_isRational : Dense {p : Simplex α | IsRational (α := α) p} := by
  classical
  intro p
  refine mem_closure_of_tendsto (tendsto_approx (p := p)) ?_
  refine (Filter.Eventually.of_forall ?_)
  intro n
  exact approx_isRational (p := p) n

end

end Simplex
end LeanPool.CencovPetz
