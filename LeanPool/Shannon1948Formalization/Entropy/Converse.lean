/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import LeanPool.Shannon1948Formalization.Entropy.Gibbs

/-!
# Shannon.Entropy.Converse

The converse direction: `entropyNat` satisfies `ShannonEntropyAxioms`.

Combined with the characterization theorems in `Final.lean`, this gives a true
"if and only if": a functional `H` satisfies the Shannon conditions iff it is a
positive multiple of `entropyNat`.

## Main results

- `entropyNat_relabelInvariant`: relabeling outcomes preserves entropy
- `entropyNat_grouping`: two-stage decomposition identity
- `entropyNat_shannonAxioms`: `ShannonEntropyAxioms entropyNat`
-/
namespace LeanPool.Shannon1948Formalization

noncomputable section
open Finset Real

/-! ## Relabel invariance -/

/-- Entropy is invariant under relabeling outcomes by an equivalence. -/
theorem entropyNat_relabelInvariant
    {α β : Type} [Fintype α] [Fintype β]
    (e : α ≃ β) (p : ProbDist α) :
    entropyNat (relabelProb e p) = entropyNat p := by
  unfold entropyNat relabelProb
  simp only [neg_inj]
  exact e.symm.sum_comp (fun a => p a * log (p a))

/-! ## Uniform monotonicity -/

/-- Entropy on uniform distributions is strictly monotone in alphabet size. -/
theorem entropyNat_uniformMonotone :
    StrictMono fun n : ℕ+ => entropyNat (uniformPNat n) := by
  intro m n hmn
  simp only [entropyNat_uniformPNat]
  exact Real.log_lt_log (by exact_mod_cast m.2) (by exact_mod_cast hmn)

/-! ## Grouping -/

/-- Two-stage decomposition: `H(compose p q) = H(p) + ∑ a, p(a) * H(q a)`. -/
theorem entropyNat_grouping
    {α : Type} [Fintype α]
    {β : α → Type} [∀ a, Fintype (β a)]
    (p : ProbDist α) (q : (a : α) → ProbDist (β a)) :
    entropyNat (composeProb p q) = entropyNat p + ∑ a, p a * entropyNat (q a) := by
  unfold entropyNat
  simp_rw [show ∀ x : Sigma β, (composeProb p q) x = p x.1 * q x.1 x.2 from fun _ => rfl]
  rw [show -∑ x : Sigma β, p x.1 * q x.1 x.2 * log (p x.1 * q x.1 x.2) =
      -(∑ a, ∑ b, p a * q a b * log (p a * q a b)) by
    simp [Fintype.sum_sigma]]
  have key : ∀ a, ∑ b, p a * q a b * log (p a * q a b) =
      p a * log (p a) + p a * ∑ b, q a b * log (q a b) := fun a => by
    by_cases hpa : p a = 0
    · simp [hpa]
    · have hpa_pos : 0 < p a := lt_of_le_of_ne (prob_nonneg p a) (Ne.symm hpa)
      have split : ∀ b, p a * q a b * log (p a * q a b) =
          q a b * (p a * log (p a)) + p a * (q a b * log (q a b)) := fun b => by
        by_cases hqb : q a b = 0
        · simp [hqb]
        · rw [Real.log_mul (ne_of_gt hpa_pos)
            (ne_of_gt (lt_of_le_of_ne (prob_nonneg (q a) b) (Ne.symm hqb)))]
          ring
      simp_rw [split, Finset.sum_add_distrib, ← Finset.sum_mul, ← Finset.mul_sum,
        prob_sum_eq_one (q a), one_mul]
  simp_rw [key, Finset.sum_add_distrib]
  simp_rw [mul_neg, Finset.sum_neg_distrib]
  linarith

/-! ## Main theorem -/

/-- `entropyNat` satisfies the Shannon entropy conditions.

This is the converse of the characterization: the characterization shows any `H`
satisfying the conditions must be a positive multiple of `entropyNat`; this theorem
shows `entropyNat` itself satisfies the conditions, proving the specification is
consistent and completing the "if and only if". -/
theorem entropyNat_shannonAxioms : ShannonEntropyAxioms (fun {α} [Fintype α] => entropyNat) where
  continuous := continuous_entropyNat
  uniformMonotone := entropyNat_uniformMonotone
  relabelInvariant := entropyNat_relabelInvariant
  grouping := entropyNat_grouping

end

end LeanPool.Shannon1948Formalization
