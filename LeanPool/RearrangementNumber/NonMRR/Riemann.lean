/-
Copyright (c) 2026 Vinicius de Oliveira Rodrigues. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vinicius de Oliveira Rodrigues
-/
/-
Copyright (c) 2026 Vinicius de Oliveira Rodrigues.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import LeanPool.RearrangementNumber.NonMRR.Series
import Mathlib.Topology.Algebra.InfiniteSum.Real
import Mathlib.Topology.Baire.CompleteMetrizable
import Mathlib.Logic.Equiv.Fintype
import Mathlib.Data.Finset.Sort
import Mathlib.Tactic

open Filter Finset Set Topology
open scoped BigOperators Classical

namespace NonMRR

/-- A real family with bounded sums on all finite subsets is absolutely summable. -/
theorem summable_abs_of_bounded_finite_sums (a : ℕ → ℝ) (c : ℝ)
    (h : ∀ s : Finset ℕ, |∑ i ∈ s, a i| ≤ c) : Summable (fun i => |a i|) := by
  have hpos (b : ℕ → ℝ) (hb : ∀ s : Finset ℕ, |∑ i ∈ s, b i| ≤ c) :
      Summable (fun i => max (b i) 0) := by
    apply summable_of_sum_le (fun _ => le_max_right _ _) (c := c)
    intro s
    have heq : ∑ i ∈ s, max (b i) 0 = ∑ i ∈ s.filter (fun i => 0 ≤ b i), b i := by
      rw [sum_filter]
      apply sum_congr rfl
      intro i _hi
      split_ifs with hi
      · exact max_eq_left hi
      · exact max_eq_right (le_of_not_ge hi)
    change (∑ i ∈ s, max (b i) 0) ≤ c
    rw [heq]
    exact (le_abs_self _).trans (hb _)
  have hp := hpos a h
  have hn := hpos (fun i => -a i) (fun s => by simpa using h s)
  convert hp.add hn using 1
  ext i
  by_cases hi : 0 ≤ a i
  · simp [abs_of_nonneg hi, max_eq_left hi, max_eq_right (neg_nonpos.mpr hi)]
  · have hi' : a i ≤ 0 := le_of_not_ge hi
    simp [abs_of_nonpos hi', max_eq_right hi', max_eq_left (neg_nonneg.mpr hi')]

/-- Nonabsolute summability forces arbitrarily large finite sums. -/
theorem exists_large_finite_sum (a : ℕ → ℝ) (ha : ¬ Summable (fun i => |a i|)) (c : ℝ) :
    ∃ s : Finset ℕ, c < |∑ i ∈ s, a i| := by
  by_contra h
  push Not at h
  exact ha (summable_abs_of_bounded_finite_sums a c h)

/-- The same unboundedness holds after excluding any prescribed finite set. -/
theorem exists_large_finite_sum_disjoint (a : ℕ → ℝ)
    (ha : ¬ Summable (fun i => |a i|)) (F : Finset ℕ) (c : ℝ) :
    ∃ s : Finset ℕ, Disjoint s F ∧ c < |∑ i ∈ s, a i| := by
  obtain ⟨s, hs⟩ := exists_large_finite_sum a ha (c + ∑ i ∈ F, |a i|)
  refine ⟨s \ F, sdiff_disjoint, ?_⟩
  have htriangle : |∑ i ∈ s, a i| ≤ |∑ i ∈ s \ F, a i| + ∑ i ∈ F, |a i| := by
    have heq := sum_sdiff (show s ∩ F ⊆ s from inter_subset_left) (f := a)
    have heq' : (∑ i ∈ s \ F, a i) + ∑ i ∈ s ∩ F, a i = ∑ i ∈ s, a i := by
      simpa using heq
    rw [← heq']
    apply (abs_add_le _ _).trans
    apply add_le_add le_rfl
    exact (abs_sum_le_sum_abs _ _).trans
      (sum_le_sum_of_subset_of_nonneg inter_subset_right (fun _ _ _ => abs_nonneg _))
  linarith

/-- Extend any finite initial segment of an injection to a permutation having
an arbitrarily large partial sum. -/
theorem exists_perm_large_partialSum (a : ℕ → ℝ)
    (ha : ¬ Summable (fun i => |a i|)) (f : ℕ → ℕ) (hf : Function.Injective f)
    (N : ℕ) (c : ℝ) :
    ∃ π : Equiv.Perm ℕ, (∀ i < N, π i = f i) ∧
      ∃ M, c < |partialSum (a ∘ π) M| := by
  classical
  obtain ⟨s, hs, hlarge⟩ := exists_large_finite_sum_disjoint a ha
    ((range N).image f) (c + |∑ i ∈ range N, a (f i)|)
  let e : Fin s.card ≃ s := (s.orderIsoOfFin rfl).toEquiv
  let b : Fin (N + s.card) → ℕ :=
    Fin.addCases (fun i : Fin N => f i.val) (fun i : Fin s.card => (e i).val)
  have hb : Function.Injective b := by
    intro i j
    refine Fin.addCases (fun i => ?_) (fun i => ?_) i <;>
      refine Fin.addCases (fun j => ?_) (fun j => ?_) j <;>
      intro h <;> simp only [b, Fin.addCases_left, Fin.addCases_right] at h
    · congr 1
      exact Fin.ext (hf h)
    · exfalso
      exact (disjoint_left.mp hs) (e j).property
        (mem_image.mpr ⟨i.val, mem_range.mpr i.is_lt, h⟩)
    · exfalso
      exact (disjoint_left.mp hs) (e i).property
        (mem_image.mpr ⟨j.val, mem_range.mpr j.is_lt, h.symm⟩)
    · congr 1
      exact e.injective (Subtype.ext h)
  obtain ⟨π, hπ⟩ := Equiv.Perm.exists_extending_pair
    (fun i : Fin (N + s.card) => i.val) b Fin.val_injective hb
  refine ⟨π, ?_, N + s.card, ?_⟩
  · intro i hi
    simpa only [b, Fin.addCases_left, Fin.val_castAdd] using hπ (Fin.castAdd s.card ⟨i, hi⟩)
  · have heq : partialSum (a ∘ π) (N + s.card) =
        (∑ i ∈ range N, a (f i)) + ∑ i ∈ s, a i := by
      rw [partialSum, ← Fin.sum_univ_eq_sum_range]
      simp only [Function.comp_apply, hπ]
      rw [Fin.sum_univ_add]
      simp only [b, Fin.addCases_left, Fin.addCases_right]
      rw [Fin.sum_univ_eq_sum_range (fun i => a (f i)) N]
      congr 1
      exact (Equiv.sum_comp e (fun i : s => a i)).trans (sum_attach s a)
    rw [heq]
    have htri := abs_add_le (-(∑ i ∈ range N, a (f i)))
      ((∑ i ∈ range N, a (f i)) + ∑ i ∈ s, a i)
    simp only [neg_add_cancel_left, abs_neg] at htri
    linarith

abbrev InjectionSpace := {f : ℕ → ℕ // Function.Injective f}

theorem isClosed_injections : IsClosed {f : ℕ → ℕ | Function.Injective f} := by
  have heq : {f : ℕ → ℕ | Function.Injective f} =
      ⋂ i : ℕ, ⋂ j : ℕ, ⋂ (_ : i ≠ j), {f : ℕ → ℕ | f i ≠ f j} := by
    ext f
    simp only [mem_setOf_eq, mem_iInter]
    constructor
    · exact fun hf i j hij => fun h => hij (hf h)
    · intro h i j hij
      by_contra hne
      exact h i j hne hij
  rw [heq]
  apply isClosed_iInter
  intro i
  apply isClosed_iInter
  intro j
  apply isClosed_iInter
  intro _
  have hdisc : IsClosed ({p : ℕ × ℕ | p.1 ≠ p.2} : Set (ℕ × ℕ)) := isClosed_discrete _
  exact hdisc.preimage
    (show Continuous (fun f : ℕ → ℕ => (f i, f j)) from
      (continuous_apply i).prodMk (continuous_apply j))

instance : TopologicalSpace.IsCompletelyMetrizableSpace InjectionSpace :=
  isClosed_injections.isCompletelyMetrizableSpace

instance : Nonempty InjectionSpace := ⟨⟨id, Function.injective_id⟩⟩

/-- A useful density criterion for the closed space of injections. -/
theorem dense_injections_of_extension (P : Set InjectionSpace)
    (h : ∀ f : InjectionSpace, ∀ N : ℕ,
      ∃ g ∈ P, ∀ i < N, g.val i = f.val i) : Dense P := by
  apply dense_iff_inter_open.mpr
  intro O hO hOne
  obtain ⟨f, hf⟩ := hOne
  obtain ⟨U, hU, rfl⟩ := isOpen_induced_iff.mp hO
  obtain ⟨I, u, hu, hsub⟩ := isOpen_pi_iff.mp hU f.val hf
  obtain ⟨g, hg, hgf⟩ := h f (I.sup id + 1)
  refine ⟨g, hsub ?_, hg⟩
  intro i hi
  rw [hgf i (Nat.lt_succ_of_le (le_sup (f := id) hi))]
  exact (hu i hi).2

end NonMRR

/- Adapted for Lean Pool: module imports and compatibility with its pinned toolchain. -/
