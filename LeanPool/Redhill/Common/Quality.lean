/-
Copyright (c) 2026 Jeremy Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Tan
-/

import Mathlib.Algebra.EuclideanDomain.Int
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.RingTheory.PrincipalIdealDomain
import Mathlib.RingTheory.Radical.Basic
import LeanPool.Redhill.Common.MaxAbs

/-!
# Qualities of tuples and sets of tuples
-/


open Finset Real ENNReal

variable {n : ℕ}

open UniqueFactorizationMonoid in
/-- The quality of a single tuple.
This depends on Lean defining `log -x = log x` for all real `x`. -/
noncomputable def tupleQuality (a : Fin n → ℤ) : ℝ≥0∞ :=
  .ofReal (log (maxAbs a) / log (radical (∏ i, a i) : ℤ))

/-- The quality of a set of tuples, defined as the infimum of those numbers where
only finitely many tuples in the set have a strictly higher quality. -/
noncomputable def quality (A : Set (Fin n → ℤ)) : ℝ≥0∞ :=
  sInf {q | {a ∈ A | q < tupleQuality a}.Finite}

variable {A B : Set (Fin n → ℤ)} {q : ℝ≥0∞}

lemma quality_mono (h : A ⊆ B) : quality A ≤ quality B :=
  sInf_le_sInf fun _ mq ↦ mq.subset fun _ ma ↦ ⟨h ma.1, ma.2⟩

lemma quality_le_of_finite (hq : {a ∈ A | q < tupleQuality a}.Finite) : quality A ≤ q :=
  sInf_le hq

lemma quality_finite (hA : A.Finite) : quality A = 0 := by
  rw [← nonpos_iff_eq_zero]
  exact quality_le_of_finite (hA.sep _)

lemma quality_empty : quality (n := n) ∅ = 0 :=
  quality_finite Set.finite_empty

lemma quality_union_finite (h : B.Finite) : quality (A ∪ B) = quality A := by
  refine le_antisymm (sInf_le_sInf fun q mq ↦ ?_) (quality_mono Set.subset_union_left)
  simp only [Set.mem_setOf, Set.mem_union, Set.sep_union, Set.finite_union] at mq ⊢
  refine ⟨mq, h.subset (Set.sep_subset ..)⟩

open Filter in
lemma quality_ge_of_liminf (f : ℕ → Fin n → ℤ) (s : Set ℕ)
    (infs : s.Infinite) (injs : s.InjOn f) (ms : ∀ i ∈ s, f i ∈ A)
    (qf : q ≤ liminf (tupleQuality ∘ f) atTop) : q ≤ quality A := by
  rw [quality, le_sInf_iff]
  intro k lk
  contrapose! lk
  rw [le_liminf_iff] at qf
  specialize qf _ lk
  rw [eventually_atTop] at qf
  obtain ⟨N₀, hN₀⟩ := qf
  have key : {i | N₀ ≤ i ∧ i ∈ s}.Infinite := by
    convert infs.sdiff (Set.finite_lt_nat N₀) using 1
    ext
    simp [and_comm]
  refine key.image (injs.mono fun _ m ↦ m.2) |>.mono fun a ma ↦ ?_
  obtain ⟨i, li, rfl⟩ := ma
  exact ⟨ms _ li.2, hN₀ _ li.1⟩

open Filter in
/-- A specialisation of `quality_ge_of_liminf` to `s = univ`. -/
lemma quality_ge_of_liminf_univ (f : ℕ ↪ Fin n → ℤ) (ms : ∀ i, f i ∈ A)
    (qf : q ≤ liminf (tupleQuality ∘ f) atTop) : q ≤ quality A :=
  quality_ge_of_liminf _ _ Set.infinite_univ (Set.injOn_univ.mpr f.injective) (by simpa using ms) qf
