/-
Copyright (c) 2026 Anastasios Fragkos. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anastasios Fragkos
-/
module


public import LeanPool.QuadraticCarleson.QuadraticCarleson.KrauseLaceyActiveOverlapPruning

/-!
# The source-size active overlap cutoff and its prefix estimate

The concrete cutoff `(s+1)(1+2^s)` has size `O((s+1)2^s)` and logarithm
at most `2s+1`. The pruned actual prefix estimate is unconditional. The
exceptional-set result retained from the previous module is first-moment
decay, not the stronger exponential tail needed to finish the source proof.
-/

@[expose] public section

open Function MeasureTheory Set
open scoped ENNReal

namespace QuadraticCarleson
namespace KrauseLaceyBadScale


/-- A literal natural-number cutoff of the paper's required asymptotic size. -/
def activeOverlapCutoff (s : ℕ) : ℕ := (s + 1) * (1 + 2 ^ s)

theorem activeOverlapCutoff_le (s : ℕ) :
    activeOverlapCutoff s ≤ 2 * (s + 1) * 2 ^ s := by
  have hpow : 1 ≤ (2 : ℕ) ^ s := Nat.one_le_pow s 2 (by omega)
  unfold activeOverlapCutoff
  nlinarith

theorem activeOverlapCutoff_le_pow (s : ℕ) :
    activeOverlapCutoff s ≤ 2 ^ (2 * s + 1) := by
  have hs : s + 1 ≤ (2 : ℕ) ^ s := by
    induction s with
    | zero => norm_num
    | succ n ih => rw [pow_succ]; omega
  have ht : 1 + (2 : ℕ) ^ s ≤ 2 ^ (s + 1) := by
    rw [pow_succ]
    have := Nat.one_le_pow s 2 (by omega)
    omega
  calc
    _ ≤ (2 : ℕ) ^ s * 2 ^ (s + 1) := Nat.mul_le_mul hs ht
    _ = _ := by rw [← pow_add]; congr 1; omega

theorem log2_activeOverlapCutoff_le (s : ℕ) :
    Nat.log2 (activeOverlapCutoff s) ≤ 2 * s + 1 := by
  have h := Nat.log_mono_right (b := 2) (activeOverlapCutoff_le_pow s)
  simpa only [Nat.log2_eq_log_two, Nat.log_pow (by norm_num : 1 < (2 : ℕ))] using h

/-- At the concrete source-size cutoff, the actual pruned maximal prefix
has an explicit linear-in-`s` logarithmic factor. No packing or overlap
estimate is supplied as a hypothesis. -/
theorem eLpNorm_paperPrunedActivePrefixMaximal_le
    {S : Finset RealInterval} {f : ℝ → ℂ} (hf : Integrable f)
    (I₀ : RealInterval) (k₀ : ℤ) (s : ℕ) (hk₀ : 3 ≤ k₀)
    (scale : RealInterval → ℤ)
    (hlam : Set.Pairwise (↑S : Set RealInterval) fun J K ↦
      J.carrier ⊆ K.carrier ∨ K.carrier ⊆ J.carrier ∨ Disjoint J.carrier K.carrier)
    (hparent : HasDyadicParents S I₀) (hsub : ∀ K ∈ S, K.carrier ⊆ I₀.carrier)
    (N : Finset RealInterval) (hN : N ⊆ nonstandardIntervals S f I₀ k₀ s scale) (L : ℕ) :
    eLpNorm (badSubcollectionPrefixMaximal S f I₀ k₀ s scale
      (overlapPrunedFamily (activeBadIntervals S f I₀ k₀ s scale N) (activeOverlapCutoff s)) L)
      2 volume ≤ ENNReal.ofReal ((2 * (s : ℝ) + 2) *
        Real.sqrt (nonstandardSignedEnergyBudget f I₀ s)) := by
  apply (eLpNorm_prunedActivePrefixMaximal_le hf I₀ k₀ s hk₀ (by omega) scale
    hlam hparent hsub N hN L (activeOverlapCutoff s)).trans
  apply ENNReal.ofReal_le_ofReal
  apply mul_le_mul_of_nonneg_right _ (Real.sqrt_nonneg _)
  have h := log2_activeOverlapCutoff_le s
  have hr : (Nat.log2 (activeOverlapCutoff s) : ℝ) ≤ 2 * (s : ℝ) + 1 := by exact_mod_cast h
  linarith


end KrauseLaceyBadScale
end QuadraticCarleson
