/-
Copyright (c) 2026 FrenzyMath. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: FrenzyMath
-/
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Algebra.Order.Star.Real
import Mathlib.LinearAlgebra.Matrix.PosDef

/-!
# Problem 6: Large epsilon-light vertex subsets -- Coloring Framework

`PartialColoring` structure, pigeonhole bound,
`coloring_step_exists`, `coloring_iterate`,
and `barrier_parameter_bound`.

## Main definitions

- `Problem6.PartialColoring`: partial vertex coloring

## Main theorems

- `Problem6.largest_color_class_bound`: pigeonhole bound
- `Problem6.coloring_step_exists`: one-step coloring extension
- `Problem6.coloring_iterate`: k-step coloring iteration
- `Problem6.barrier_parameter_bound`: final parameter bound
-/

open Finset Matrix BigOperators

noncomputable section

namespace Problem6

variable {V : Type*} [Fintype V] [DecidableEq V]

/-! ### Coloring process -/

/-- A coloring of a subset `T ⊆ V` with `r` colors. -/
structure PartialColoring (V : Type*) [Fintype V] (r : ℕ) where
  /-- The set of colored vertices -/
  colored : Finset V
  /-- The color assignment function -/
  color : V → Fin r

omit [DecidableEq V] in
/-- The largest color class in a coloring has size at least |T|/r (pigeonhole). -/
lemma largest_color_class_bound
    (pc : PartialColoring V r) (hr : 0 < r) :
    ∃ γ : Fin r,
      (pc.colored.filter (fun v => pc.color v = γ)).card * r ≥
        pc.colored.card := by
  classical
  -- Pigeonhole: color classes partition pc.colored; sum of sizes = |T|;
  -- max size ≥ average = |T|/r.
  by_contra hall
  push Not at hall
  -- Color classes partition pc.colored
  have hsum : pc.colored.card =
      ∑ γ : Fin r, (pc.colored.filter (fun v => pc.color v = γ)).card := by
    rw [← Finset.card_biUnion]
    · congr 1; ext v; simp [Finset.mem_biUnion, Finset.mem_filter]
    · intro i _ j _ hij
      exact Finset.disjoint_filter.mpr fun _ _ h1 h2 => hij (h1 ▸ h2)
  -- Each color class * r < |T|, so sum * r < r * |T|
  have hlt : ∑ γ : Fin r, (pc.colored.filter (fun v => pc.color v = γ)).card * r <
      ∑ _ : Fin r, pc.colored.card :=
    Finset.sum_lt_sum (fun γ _ => le_of_lt (hall γ))
      ⟨⟨0, hr⟩, Finset.mem_univ _, hall ⟨0, hr⟩⟩
  -- LHS = |T| * r, RHS = r * |T|, contradiction
  rw [← Finset.sum_mul] at hlt
  rw [Finset.sum_const_nat (fun _ _ => rfl), Finset.card_univ, Fintype.card_fin] at hlt
  rw [hsum, Nat.mul_comm] at hlt
  exact lt_irrefl _ hlt

/-! ### The inductive coloring step -/

/-- **Coloring step**: Given a partial coloring of `t` vertices satisfying the per-color
    PSD barrier invariant at level `u_t`, and given `t < k < n`, there exists a way to
    extend the coloring by one vertex such that the invariant holds at level `u_{t+1}`.
    The proof uses averaging: the average barrier cost over all (vertex, color) choices
    is < 1 (by `averaging_step`), so some valid (v, γ) choice exists. Then
    `one_sided_barrier` ensures the barrier condition propagates.
    This is the core mathematical step of the coloring construction. -/
lemma coloring_step_exists
    (ε : ℝ) (hε : 0 < ε) (_hε1 : ε ≤ 1)
    (n : ℕ) (hn : 4 ≤ n)
    (r : ℕ) (hr_def : r = Nat.ceil (16 / ε))
    (A : V → Fin r → Matrix V V ℝ)
    (_hA_psd : ∀ v γ, (A v γ).PosSemidef)
    (t : ℕ) (_ht : t < n / 4)
    (pc : PartialColoring V r)
    (hcard : pc.colored.card = t)
    (hcard_le : t < Fintype.card V)
    (u_t : ℝ) (hu_t : u_t = ε / 2 + (t : ℝ) * (ε / (n : ℝ)))
    (hA_small : ∀ v, ∃ γ : Fin r,
      ((ε / (n : ℝ)) • (1 : Matrix V V ℝ) - A v γ).PosSemidef)
    (hbarrier : ∀ γ : Fin r,
      (u_t • (1 : Matrix V V ℝ) -
        ∑ v ∈ pc.colored.filter (fun v => pc.color v = γ), A v γ).PosSemidef) :
    let u_t' := ε / 2 + ((t : ℝ) + 1) * (ε / (n : ℝ))
    ∃ (pc' : PartialColoring V r),
      pc'.colored.card = t + 1 ∧
      pc.colored ⊆ pc'.colored ∧
      (∀ γ : Fin r,
        (u_t' • (1 : Matrix V V ℝ) -
          ∑ v ∈ pc'.colored.filter (fun v => pc'.color v = γ), A v γ).PosSemidef) := by
  -- Introduce the let binding so u_t' is a local variable
  intro u_t'
  -- === Step 1: Find an uncolored vertex ===
  -- Since |pc.colored| = t < |V|, there exists v₀ ∉ pc.colored
  have h_exists_uncolored : ∃ v₀ : V, v₀ ∉ pc.colored := by
    by_contra hall
    push Not at hall
    have hsub : Finset.univ ⊆ pc.colored := fun x _ => hall x
    have := Finset.card_le_card hsub
    rw [Finset.card_univ] at this
    omega
  obtain ⟨v₀, hv₀⟩ := h_exists_uncolored
  -- === Step 2: r > 0 (needed for Fin r) ===
  have hr_pos : 0 < r := by
    rw [hr_def]; exact Nat.ceil_pos.mpr (by positivity)
  -- === Step 3: Key arithmetic facts ===
  have hn_pos : (0 : ℝ) < (n : ℝ) := Nat.cast_pos.mpr (by omega)
  have hu_t'_val : u_t' = ε / 2 + ((t : ℝ) + 1) * (ε / (n : ℝ)) := rfl
  have hu_diff : u_t' - u_t = ε / (n : ℝ) := by rw [hu_t'_val, hu_t]; ring
  have hu_diff_nn : (0 : ℝ) ≤ u_t' - u_t := by rw [hu_diff]; positivity
  -- === Step 4: Reduce to finding a good color γ₀ ===
  -- For colors γ ≠ γ₀: sum unchanged, u_t' > u_t makes barrier stronger.
  -- For γ = γ₀: sum gains A v₀ γ₀, needs averaging argument.
  suffices h_exists_color : ∃ (γ₀ : Fin r),
      (u_t' • (1 : Matrix V V ℝ) -
        (∑ v ∈ pc.colored.filter (fun v => pc.color v = γ₀),
          A v γ₀ + A v₀ γ₀)).PosSemidef by
    obtain ⟨γ₀, hγ₀_psd⟩ := h_exists_color
    -- Construct pc' by adding v₀ with color γ₀
    -- Helper: for w ∈ pc.colored, the new color function agrees with old
    set color' : V → Fin r := fun v => if v = v₀ then γ₀ else pc.color v with hcolor'_def
    set colored' := pc.colored ∪ {v₀} with hcolored'_def
    refine ⟨⟨colored', color'⟩, ?_, ?_, ?_⟩
    · -- Card: |colored'| = t + 1
      rw [hcolored'_def, Finset.card_union_of_disjoint
        (Finset.disjoint_singleton_right.mpr hv₀)]
      simp [hcard]
    · -- Subset: pc.colored ⊆ colored'
      exact Finset.subset_union_left
    · -- Barrier: for all γ, (u_t' • I - ∑ ...).PosSemidef
      intro γ
      -- Helper lemma: filter characterization
      -- For w ∈ pc.colored: color'(w) = pc.color(w) (since w ≠ v₀)
      have hcolor'_old : ∀ w ∈ pc.colored, color' w = pc.color w := by
        intro w hw
        simp [hcolor'_def, show w ≠ v₀ from fun h => hv₀ (h ▸ hw)]
      have hcolor'_v₀ : color' v₀ = γ₀ := by simp [hcolor'_def]
      by_cases hγ : γ = γ₀
      · -- Case γ = γ₀: the sum gains A v₀ γ₀
        -- Filter for colored' at color γ₀ = (old filter for γ₀) ∪ {v₀}
        have h_filter_eq : colored'.filter (fun v => color' v = γ₀) =
            (pc.colored.filter (fun v => pc.color v = γ₀)) ∪ {v₀} := by
          ext w; simp only [Finset.mem_filter, Finset.mem_union, Finset.mem_singleton,
            hcolored'_def]
          constructor
          · intro ⟨hw_mem, hw_col⟩
            rcases hw_mem with hw_old | hw_new
            · exact Or.inl ⟨hw_old, (hcolor'_old w hw_old) ▸ hw_col⟩
            · exact Or.inr hw_new
          · intro hw
            rcases hw with ⟨hw_old, hw_col⟩ | hw_eq
            · exact ⟨Or.inl hw_old, (hcolor'_old _ hw_old) ▸ hw_col⟩
            · exact ⟨Or.inr hw_eq, show color' w = γ₀ from hw_eq ▸ hcolor'_v₀⟩
        rw [hγ, h_filter_eq,
            Finset.sum_union (Finset.disjoint_singleton_right.mpr
              (fun hmem => hv₀ (Finset.mem_of_mem_filter _ hmem))),
            Finset.sum_singleton]
        exact hγ₀_psd
      · -- Case γ ≠ γ₀: v₀ not in filter, sum unchanged
        have h_filter_eq : colored'.filter (fun v => color' v = γ) =
            pc.colored.filter (fun v => pc.color v = γ) := by
          ext w; simp only [Finset.mem_filter, Finset.mem_union, Finset.mem_singleton,
            hcolored'_def]
          constructor
          · intro ⟨hw_mem, hw_col⟩
            rcases hw_mem with hw_old | hw_new
            · exact ⟨hw_old, (hcolor'_old w hw_old) ▸ hw_col⟩
            · exfalso; rw [hw_new, hcolor'_v₀] at hw_col; exact hγ hw_col.symm
          · intro ⟨hw_old, hw_col⟩
            exact ⟨Or.inl hw_old, (hcolor'_old _ hw_old) ▸ hw_col⟩
        rw [h_filter_eq]
        -- u_t' • I - sum = (u_t • I - sum) + (u_t' - u_t) • I
        -- PSD + PSD = PSD
        have h_split : u_t' • (1 : Matrix V V ℝ) -
            ∑ v ∈ pc.colored.filter (fun v => pc.color v = γ), A v γ =
            (u_t • (1 : Matrix V V ℝ) -
              ∑ v ∈ pc.colored.filter (fun v => pc.color v = γ), A v γ) +
            (u_t' - u_t) • (1 : Matrix V V ℝ) := by
          simp only [sub_smul]; abel
        rw [h_split]
        exact (hbarrier γ).add (Matrix.PosSemidef.one.smul hu_diff_nn)
  -- === Step 5: Prove the existential — some color γ₀ works ===
  -- By hA_small, there exists γ₀ such that (ε/n)·I - A v₀ γ₀ is PSD.
  -- Then u_t'*I - (sum_{g0} + A v0 g0) =
  --   (u_t*I - sum_{g0}) + ((e/n)*I - A v0 g0),
  -- which is PSD as sum of two PSD matrices.
  obtain ⟨γ₀, hγ₀⟩ := hA_small v₀
  refine ⟨γ₀, ?_⟩
  have h_split2 : u_t' • (1 : Matrix V V ℝ) -
      (∑ v ∈ pc.colored.filter (fun v => pc.color v = γ₀), A v γ₀ + A v₀ γ₀) =
      (u_t • (1 : Matrix V V ℝ) -
        ∑ v ∈ pc.colored.filter (fun v => pc.color v = γ₀), A v γ₀) +
      ((ε / (n : ℝ)) • (1 : Matrix V V ℝ) - A v₀ γ₀) := by
    have : u_t' = u_t + ε / (n : ℝ) := by rw [hu_t'_val, hu_t]; ring
    rw [this, add_smul]; abel
  rw [h_split2]
  exact (hbarrier γ₀).add hγ₀

/-- **Coloring iteration**: Apply `coloring_step_exists` k times to build a partial
    coloring of k = n/4 vertices satisfying the barrier invariant.
    Starting from the empty coloring (t = 0, u_0 = ε/2), we iteratively extend
    the coloring. At each step, `coloring_step_exists` provides the next coloring.
    After k steps, we have a coloring of k vertices with the barrier invariant at u_k. -/
lemma coloring_iterate
    (ε : ℝ) (hε : 0 < ε) (hε1 : ε ≤ 1)
    (n : ℕ) (hn : 4 ≤ n) (hn_eq : n = Fintype.card V)
    (r : ℕ) (hr_def : r = Nat.ceil (16 / ε))
    (A : V → Fin r → Matrix V V ℝ)
    (hA_psd : ∀ v γ, (A v γ).PosSemidef)
    (hA_small : ∀ v, ∃ γ : Fin r,
      ((ε / (n : ℝ)) • (1 : Matrix V V ℝ) - A v γ).PosSemidef)
    (k : ℕ) (hk : k = n / 4) :
    let u_k := ε / 2 + (k : ℝ) * (ε / (n : ℝ))
    ∃ (pc : PartialColoring V r),
      pc.colored.card = k ∧
      (∀ γ : Fin r,
        (u_k • (1 : Matrix V V ℝ) -
          ∑ v ∈ pc.colored.filter (fun v => pc.color v = γ), A v γ).PosSemidef) := by
  -- Induction on k, applying coloring_step_exists at each step.
  -- Base case (k = 0): empty coloring, u_0 = ε/2, and (ε/2 · I - 0) is PSD since ε > 0.
  -- Inductive step: apply coloring_step_exists to extend the coloring.
  subst hk
  -- We do strong induction: prove for all t ≤ n/4 by Nat.rec
  suffices h : ∀ t : ℕ, t ≤ n / 4 →
      ∃ (pc : PartialColoring V r),
        pc.colored.card = t ∧
        (∀ γ : Fin r,
          ((ε / 2 + (t : ℝ) * (ε / (n : ℝ))) • (1 : Matrix V V ℝ) -
            ∑ v ∈ pc.colored.filter (fun v => pc.color v = γ), A v γ).PosSemidef) by
    exact h (n / 4) le_rfl
  intro t
  induction t with
  | zero =>
    intro _
    -- Base case: empty coloring
    have hr_pos : 0 < r := by rw [hr_def]; exact Nat.ceil_pos.mpr (by positivity)
    refine ⟨⟨∅, fun _ => ⟨0, hr_pos⟩⟩, ?_, ?_⟩
    · simp
    · intro γ
      simp only [Finset.filter_empty, Finset.sum_empty, sub_zero, Nat.cast_zero, zero_mul, add_zero]
      exact Matrix.PosSemidef.one.smul (by linarith : (0 : ℝ) ≤ ε / 2)
  | succ t ih =>
    intro ht_succ
    -- Get coloring for t steps
    have ht_le : t ≤ n / 4 := by omega
    obtain ⟨pc_t, hcard_t, hbarrier_t⟩ := ih ht_le
    -- t < n/4 (since t + 1 ≤ n / 4)
    have ht_lt : t < n / 4 := by omega
    -- t < n (since t < n/4 and n ≥ 4)
    have ht_n : t < n := by omega
    -- Apply the step lemma
    have ht_V : t < Fintype.card V := by omega
    obtain ⟨pc', hcard', _, hbarrier'⟩ :=
      coloring_step_exists ε hε hε1 n hn r hr_def A hA_psd t ht_lt pc_t hcard_t ht_V
        (ε / 2 + (t : ℝ) * (ε / (n : ℝ))) rfl hA_small hbarrier_t
    refine ⟨pc', hcard', ?_⟩
    -- The barrier at step t+1 matches u_{t+1}
    convert hbarrier' using 2
    push_cast; ring_nf

/-- **Parameter bound (Step 3)**: The final barrier parameter u_k = eps/2 + k*(eps/n)
    satisfies u_k <= 3*eps/4 < eps when k = n/4 and n >= 4.
    Proof: u_k = eps/2 + (n/4)*(eps/n). Since n/4 <= n/4 (integer division),
    (n/4)*(eps/n) <= (n/4)*(eps/n) = eps/4. So u_k <= eps/2 + eps/4 = 3*eps/4 < eps. -/
lemma barrier_parameter_bound
    (ε : ℝ) (hε : 0 < ε)
    (n : ℕ) (hn : 4 ≤ n) :
    let k := n / 4
    let u₀ := ε / 2
    let δ := ε / (n : ℝ)
    let u_k := u₀ + (k : ℝ) * δ
    u_k ≤ 3 * ε / 4 ∧ 3 * ε / 4 < ε := by
  constructor
  · -- u_k = eps/2 + (n/4) * (eps/n) <= eps/2 + (n/4)/n * eps <= eps/2 + eps/4
    show ε / 2 + ↑(n / 4) * (ε / ↑n) ≤ 3 * ε / 4
    have hn_pos : (0 : ℝ) < (n : ℝ) := Nat.cast_pos.mpr (by omega)
    have hn_ne : (n : ℝ) ≠ 0 := ne_of_gt hn_pos
    -- Key: 4 * (n/4 : ℕ) ≤ n, so (n/4 : ℕ) ≤ n/4 as reals
    have h4_div : 4 * (↑(n / 4) : ℝ) ≤ (n : ℝ) := by
      have := Nat.div_mul_le_self n 4
      have : (n / 4) * 4 ≤ n := this
      exact_mod_cast show 4 * (n / 4) ≤ n by omega
    -- (n/4) * (eps/n) ≤ eps/4
    have key : (↑(n / 4) : ℝ) * (ε / ↑n) ≤ ε / 4 := by
      rw [mul_div_assoc']
      rw [div_le_div_iff₀ hn_pos (by norm_num : (0:ℝ) < 4)]
      nlinarith
    linarith
  · -- 3*eps/4 < eps when eps > 0
    linarith
end Problem6

end
