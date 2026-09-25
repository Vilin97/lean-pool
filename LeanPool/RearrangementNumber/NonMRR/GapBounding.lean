/-
Copyright (c) 2026 Vinicius de Oliveira Rodrigues. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vinicius de Oliveira Rodrigues
-/
module

/-
Copyright (c) 2026 Vinicius de Oliveira Rodrigues.
Released under Apache 2.0 license as described in the file LICENSE.
-/

public import LeanPool.RearrangementNumber.NonMRR.PermutationBounds

/-!
# Unbounded families of interval gaps

An eventually unbounded family gives, without increasing its cardinality, a
family of increasing sequences whose successive gaps escape any prescribed
function. This is the bounding-number ingredient in the category reduction.
-/

@[expose] public section

open Filter Finset Cardinal

namespace NonMRR

/-- A monotone pointwise majorant of an arbitrary function. -/
def monotoneMajorant (f : ℕ → ℕ) (n : ℕ) : ℕ :=
  max (n + 1) ((range (n + 1)).sup f)

theorem le_monotoneMajorant (f : ℕ → ℕ) (n : ℕ) : f n ≤ monotoneMajorant f n :=
  (le_sup (f := f) (mem_range.mpr (Nat.lt_succ_self n))).trans (le_max_right _ _)

theorem monotone_monotoneMajorant (f : ℕ → ℕ) : Monotone (monotoneMajorant f) := by
  intro m n hmn
  exact max_le_max (Nat.add_le_add_right hmn 1)
    (Finset.sup_mono (range_mono (Nat.add_le_add_right hmn 1)))

/-- Locate an integer between consecutive terms of an increasing sequence starting at zero. -/
theorem exists_between_consecutive {t : ℕ → ℕ} (ht : StrictMono t) (hzero : t 0 = 0)
    (n : ℕ) : ∃ k, t k ≤ n ∧ n < t (k + 1) := by
  induction n with
  | zero => exact ⟨0, hzero.le, by simpa only [hzero] using ht (Nat.zero_lt_succ 0)⟩
  | succ n ih =>
    obtain ⟨k, hkn, hnk⟩ := ih
    by_cases h : n + 1 < t (k + 1)
    · exact ⟨k, hkn.trans (Nat.le_succ n), h⟩
    · have heq : t (k + 1) = n + 1 := by omega
      exact ⟨k + 1, heq.le, by simpa only [heq] using ht (Nat.lt_succ_self (k + 1))⟩

/-- Tame successive gaps force eventual domination of the original function. -/
theorem eventuallyLE_of_tame_gaps (f h : ℕ → ℕ)
    (htame : ∀ᶠ k in atTop,
      spacedSequence (monotoneMajorant f) (k + 1) ≤
        h (spacedSequence (monotoneMajorant f) k)) :
    EventuallyLE f (monotoneMajorant h ∘ monotoneMajorant h) := by
  let t := spacedSequence (monotoneMajorant f)
  let H := monotoneMajorant h
  have ht : StrictMono t := spacedSequence_strictMono _
  have hH : Monotone H := monotone_monotoneMajorant _
  obtain ⟨N, hN⟩ := eventually_atTop.mp htame
  filter_upwards [eventually_ge_atTop (t N)] with n hn
  obtain ⟨k, hkn, hnk⟩ := exists_between_consecutive ht rfl n
  have hNk : N ≤ k := by
    by_contra h
    have hkN : k + 1 ≤ N := by omega
    have := ht.monotone hkN
    omega
  have hstep (j : ℕ) : monotoneMajorant f (t j) ≤ t (j + 1) := le_max_right _ _
  change f n ≤ H (H n)
  calc
    f n ≤ monotoneMajorant f n := le_monotoneMajorant f n
    _ ≤ monotoneMajorant f (t (k + 1)) := monotone_monotoneMajorant f hnk.le
    _ ≤ t (k + 1 + 1) := hstep (k + 1)
    _ ≤ h (t (k + 1)) := hN (k + 1) (by omega)
    _ ≤ H (t (k + 1)) := le_monotoneMajorant _ _
    _ ≤ H (h (t k)) := hH (hN k hNk)
    _ ≤ H (H (t k)) := hH (le_monotoneMajorant _ _)
    _ ≤ H (H n) := hH (hH hkn)

/-- There is a family of increasing sequences of size at most `b` whose gaps
escape every natural-valued function infinitely often. -/
theorem exists_gap_unbounded_family :
    ∃ B : Set (ℕ → ℕ), #B ≤ boundingNumber ∧
      (∀ t ∈ B, StrictMono t) ∧
      ∀ h : ℕ → ℕ, ∃ t ∈ B, ∃ᶠ k in atTop, h (t k) < t (k + 1) := by
  obtain ⟨G, hG, hcard⟩ := boundingRelation.exists_dominating_of_norm
  let Φ : (ℕ → ℕ) → (ℕ → ℕ) := fun f ↦ spacedSequence (monotoneMajorant f)
  refine ⟨Φ '' G, ?_, ?_, ?_⟩
  · exact Cardinal.mk_image_le.trans_eq hcard
  · rintro t ⟨f, hf, rfl⟩
    exact spacedSequence_strictMono _
  · intro h
    obtain ⟨f, hf, hescape⟩ := hG (monotoneMajorant h ∘ monotoneMajorant h)
    refine ⟨Φ f, Set.mem_image_of_mem _ hf, ?_⟩
    by_contra hnot
    have htame : ∀ᶠ k in atTop, Φ f (k + 1) ≤ h (Φ f k) := by
      simpa only [Filter.not_frequently, not_lt] using hnot
    exact (frequentlyLT_iff_not_eventuallyLE _ _).mp hescape
      (eventuallyLE_of_tame_gaps f h htame)

end NonMRR

/- Adapted for Lean Pool: module imports and compatibility with its pinned toolchain. -/
