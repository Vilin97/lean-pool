/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import LeanPool.Shannon1948Formalization.Entropy.Approx

/-!
# Shannon.Entropy.Final

Final theorem layer.

Combines the rational characterization and continuity extension to prove:
- natural-log uniqueness (`entropyNat_unique`);
- base-parametric uniqueness (`entropyBase_unique`).
-/
namespace LeanPool.Shannon1948Formalization

noncomputable section
open Filter
open scoped Topology

/-! ## Final Characterization Theorems -/

/-! ### Theorem Index

- `entropyNat_unique`
- `entropyBase_unique`
-/

/--
Uniqueness in natural-log units:
every `H` satisfying the condition bundle agrees with Shannon entropy up to the
positive multiplicative scale factor `K H`.
-/
theorem entropyNat_unique
    (H : {α : Type} → [Fintype α] → ProbDist α → ℝ)
    (hH : ShannonEntropyAxioms H)
    {α : Type} [Fintype α]
    (p : ProbDist α) :
    H p = -K H * ∑ a, p a * Real.log (p a) := by
  have hseq : ∀ N : ℕ, H (approxProb p N) = K H * entropyNat (approxProb p N) := fun N => by
    simpa [entropyNat, mul_assoc, mul_left_comm, mul_comm] using entropyNat_approxProb H hH p N
  have hleft : Tendsto (fun N : ℕ => H (approxProb p N)) atTop (𝓝 (H p)) :=
    (hH.continuous (α := α)).continuousAt.tendsto.comp (tendsto_approxProb p)
  have hright :
      Tendsto (fun N : ℕ => K H * entropyNat (approxProb p N)) atTop (𝓝 (K H * entropyNat p)) :=
    (continuous_const.mul continuous_entropyNat).continuousAt.tendsto.comp (tendsto_approxProb p)
  have hright' : Tendsto (fun N : ℕ => H (approxProb p N)) atTop (𝓝 (K H * entropyNat p)) := by
    simpa only [hseq] using hright
  simpa [entropyNat, mul_assoc, mul_left_comm, mul_comm] using tendsto_nhds_unique hleft hright'

/--
Base-parametric uniqueness:
for each base `b > 1`, there is a positive scale factor `Kb` with
`H p = -Kb * ∑ p_i log_b p_i`.
-/
theorem entropyBase_unique
    (H : {α : Type} → [Fintype α] → ProbDist α → ℝ)
    (hH : ShannonEntropyAxioms H)
    (b : ℝ)
    (hb : 1 < b) :
    ∃ Kb : ℝ, 0 < Kb ∧
      ∀ {α : Type} [Fintype α] (p : ProbDist α),
        H p = -Kb * ∑ a, p a * Real.logb b (p a) := by
  have hb_pos : 0 < b := lt_trans (by norm_num) hb
  have hlogb_ne : Real.log b ≠ 0 := Real.log_ne_zero_of_pos_of_ne_one hb_pos (ne_of_gt hb)
  refine ⟨K H * Real.log b, mul_pos (K_pos H hH) (Real.log_pos hb), fun {α} _ p => ?_⟩
  have hsum : (∑ a, p a * Real.log (p a)) = Real.log b * (∑ a, p a * Real.logb b (p a)) := by
    simp_rw [Finset.mul_sum]
    congr 1
    ext a
    simp only [Real.logb, mul_div_assoc']
    field_simp [hlogb_ne]
  rw [entropyNat_unique H hH p, hsum]
  ring


end

end LeanPool.Shannon1948Formalization
