/-
Copyright (c) 2026 Juliane Trianon Fraga and Vinicius de Oliveira Rodrigues. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juliane Trianon Fraga, Vinicius de Oliveira Rodrigues
-/

import LeanPool.Wallace.SeparationInterface
import Mathlib.Data.Nat.Nth

/-!
# Excluding nontrivial convergent sequences

The separating package constructed for the Wallace semigroup has a stronger consequence than
point separation.  Every injective sequence has a genuine subsequence which converges, along a
free ultrafilter, to a nonzero basis vector.  In a Hausdorff topological group this rules out
convergence of the original injective sequence: after translation by its alleged limit, the
same subsequence would converge to zero along the free ultrafilter.

This observation avoids any separate oscillating-marker construction.
-/

open Filter Set Topology

universe u

namespace Wallace

noncomputable section

/-- Every injective sequence has a strictly reindexed subsequence with a nonzero limit along a
free ultrafilter. -/
def HasNonzeroLimitProperty
    (G : Type u) [TopologicalSpace G] [Zero G] : Prop :=
  ∀ s : ℕ → G, Function.Injective s →
    ∃ (φ : ℕ → ℕ) (x : G) (p : Ultrafilter ℕ),
      StrictMono φ ∧ x ≠ 0 ∧ (p : Filter ℕ) ≤ cofinite ∧
        Tendsto (s ∘ φ) p (nhds x)

/-- A separation package has the nonzero ultrafilter-limit property: its prescribed limit is
the fresh basis vector attached to the code of the sequence. -/
theorem SeparationPackage.hasNonzeroLimitProperty
    {I : Type u} (C : SeparationPackage I) :
    @HasNonzeroLimitProperty (I →₀ ℤ) C.initialTopology _ := by
  intro s hs
  let encoded : InjectiveSequence' (I →₀ ℤ) := ⟨s, hs⟩
  let c : C.Code := C.codeEquiv.symm encoded
  have hcoded : (C.codeEquiv c).1 = s := by
    exact congrArg Subtype.val (C.codeEquiv.apply_symm_apply encoded)
  refine ⟨C.subsequence c, Finsupp.single (C.codeIndex c) 1, C.ultrafilter c,
    C.subsequence_strictMono c, ?_, C.ultrafilter_free c, ?_⟩
  · exact Finsupp.single_ne_zero.mpr one_ne_zero
  · change Tendsto (fun n ↦ s (C.subsequence c n)) (C.ultrafilter c) _
    rw [← hcoded]
    exact C.prepared_tendsto_basis c

/-- In a Hausdorff topological group, the nonzero ultrafilter-limit property prevents every
injective sequence from converging. -/
theorem no_injective_sequence_converges_of_nonzeroLimitProperty
    {G : Type u} [TopologicalSpace G] [AddGroup G]
    [IsTopologicalAddGroup G] [T2Space G]
    (hlimits : HasNonzeroLimitProperty G) :
    ∀ s : ℕ → G, Function.Injective s →
      ¬ ∃ x : G, Tendsto s atTop (nhds x) := by
  intro s hs
  rintro ⟨x, hsx⟩
  let t : ℕ → G := fun n ↦ s n - x
  have htinj : Function.Injective t := by
    intro m n hmn
    have h := congrArg (fun z : G ↦ z + x) hmn
    apply hs
    simpa [t] using h
  obtain ⟨φ, y, p, hφ, hy, hfree, hpy⟩ := hlimits t htinj
  have ht0 : Tendsto t atTop (nhds 0) := by
    simpa [t] using hsx.sub
      (tendsto_const_nhds : Tendsto (fun _ : ℕ ↦ x) atTop (nhds x))
  have hsub0 : Tendsto (t ∘ φ) atTop (nhds 0) :=
    ht0.comp hφ.tendsto_atTop
  have hfree' : (p : Filter ℕ) ≤ atTop := by
    simpa only [Nat.cofinite_eq_atTop] using hfree
  have hp0 : Tendsto (t ∘ φ) p (nhds 0) := hsub0.mono_left hfree'
  exact hy (tendsto_nhds_unique hpy hp0)

/-- The nonzero limits supplied by a separation package rule out convergence of every injective
sequence in its initial topology. -/
theorem SeparationPackage.no_injective_sequence_converges
    {I : Type u} (C : SeparationPackage I) :
    ∀ s : ℕ → (I →₀ ℤ), Function.Injective s →
      ¬ ∃ x : I →₀ ℤ,
        Tendsto s atTop (@nhds (I →₀ ℤ) C.initialTopology x) := by
  letI : TopologicalSpace (I →₀ ℤ) := C.initialTopology
  letI : IsTopologicalAddGroup (I →₀ ℤ) := C.initial_isTopologicalAddGroup
  letI : T2Space (I →₀ ℤ) := C.initial_t2Space
  exact no_injective_sequence_converges_of_nonzeroLimitProperty
    C.hasNonzeroLimitProperty

/-- Any sequence with infinite range has a strictly reindexed injective subsequence. -/
theorem exists_injective_subsequence_of_infinite_range
    {X : Type u} {s : ℕ → X} (hinf : (Set.range s).Infinite) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ Function.Injective (s ∘ φ) := by
  let e : ℕ ↪ Set.range s := hinf.natEmbedding
  let pick : ℕ → ℕ := fun n ↦ Classical.choose (e n).property
  have hpick : ∀ n, s (pick n) = e n := fun n ↦ Classical.choose_spec (e n).property
  have hpickinj : Function.Injective pick := by
    intro m n hmn
    apply e.injective
    apply Subtype.val_injective
    rw [← hpick m, ← hpick n, hmn]
  have hrange : (Set.range pick).Infinite := Set.infinite_range_of_injective hpickinj
  let φ : ℕ → ℕ := Nat.nth (fun k ↦ k ∈ Set.range pick)
  have hφ : StrictMono φ := Nat.nth_strictMono hrange
  refine ⟨φ, hφ, ?_⟩
  intro m n hmn
  have hm : φ m ∈ Set.range pick := Nat.nth_mem_of_infinite hrange m
  have hn : φ n ∈ Set.range pick := Nat.nth_mem_of_infinite hrange n
  obtain ⟨i, hi⟩ := hm
  obtain ⟨j, hj⟩ := hn
  have heij : e i = e j := by
    apply Subtype.val_injective
    rw [← hpick i, ← hpick j, hi, hj]
    exact hmn
  have hij : i = j := e.injective heij
  apply hφ.injective
  rw [← hi, ← hj, hij]

/-- In a T1 space where no injective sequence converges, every convergent sequence is eventually
equal to its limit. -/
theorem eventually_eq_limit_of_no_injective_sequence_converges
    {X : Type u} [TopologicalSpace X] [T1Space X]
    (hno : ∀ s : ℕ → X, Function.Injective s →
      ¬ ∃ x : X, Tendsto s atTop (nhds x))
    {s : ℕ → X} {x : X} (hs : Tendsto s atTop (nhds x)) :
    ∀ᶠ n in atTop, s n = x := by
  by_cases hfinite : (Set.range s).Finite
  · let A : Set X := Set.range s \ {x}
    have hA : A.Finite := hfinite.diff
    have hAc : IsClosed A := hA.isClosed
    have hxA : x ∈ Aᶜ := by simp [A]
    have hnhds : Aᶜ ∈ nhds x := hAc.isOpen_compl.mem_nhds hxA
    filter_upwards [hs.eventually hnhds] with n hn
    have hrange : s n ∈ Set.range s := Set.mem_range_self n
    by_contra hne
    exact hn ⟨hrange, by simpa using hne⟩
  · have hinf : (Set.range s).Infinite := hfinite
    obtain ⟨φ, hφ, hinj⟩ := exists_injective_subsequence_of_infinite_range hinf
    exact ((hno (s ∘ φ) hinj) ⟨x, hs.comp hφ.tendsto_atTop⟩).elim

/-- Consequently every convergent sequence in the initial topology of a separation package is
eventually constant at its limit. -/
theorem SeparationPackage.every_convergent_sequence_eventually_constant
    {I : Type u} (C : SeparationPackage I)
    {s : ℕ → (I →₀ ℤ)} {x : I →₀ ℤ}
    (hs : Tendsto s atTop (@nhds (I →₀ ℤ) C.initialTopology x)) :
    ∀ᶠ n in atTop, s n = x := by
  letI : TopologicalSpace (I →₀ ℤ) := C.initialTopology
  letI : IsTopologicalAddGroup (I →₀ ℤ) := C.initial_isTopologicalAddGroup
  letI : T2Space (I →₀ ℤ) := C.initial_t2Space
  exact eventually_eq_limit_of_no_injective_sequence_converges
    C.no_injective_sequence_converges hs

end

end Wallace
