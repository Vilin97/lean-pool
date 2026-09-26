/-
Copyright (c) 2026 Xiaoyu Li, Andi Han, Jiaojiao Jiang, Junbin Gao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xiaoyu Li, Andi Han, Jiaojiao Jiang, Junbin Gao
-/
module

public import LeanPool.LanguageGeneration.FiniteWitness.Width.TwoCore
public import LeanPool.LanguageGeneration.FiniteWitness.Width.Transport
public import Mathlib.Order.Filter.AtTopBot.Basic

/-!
# Witness-size divergence in the two-core family
-/

public section

namespace GenLimit.FiniteWitness.TwoCore

/-- The natural-number indices of the right-copy elements in a sample. -/
noncomputable def rightPart (S : Finset Point) : Finset ℕ := Anchored.rightTail 0 S
/-- The natural-number indices of the left-copy elements in a sample. -/
noncomputable def leftPart (S : Finset Point) : Finset ℕ :=
  S.preimage Sum.inl (fun _ _ _ _ h => Sum.inl.inj h)

@[simp] theorem mem_rightPart (S : Finset Point) (n : ℕ) :
    n ∈ rightPart S ↔ Sum.inr n ∈ S := by simp [rightPart]
@[simp] theorem mem_leftPart (S : Finset Point) (n : ℕ) :
    n ∈ leftPart S ↔ Sum.inl n ∈ S := Finset.mem_preimage

/-- A full right copy together with the first n points of the left copy. -/
def rightChain (n : ℕ) : Set Point := rightTarget ↑(Finset.range n)
/-- A full left copy together with the first n points of the right copy. -/
def leftChain (n : ℕ) : Set Point := leftTarget ↑(Finset.range n)

/-- The common right part of the active targets that contain the entire left copy. -/
def leftCore (T : Set Point → Finset Point) (S : Finset Point) : Set ℕ :=
  {n | ∀ D, leftTarget D ∈ active family T S → n ∈ D}

theorem leftCore_infinite {T : Set Point → Finset Point} (hT : Valid family T)
    {S : Finset Point} {n : ℕ} (hK : rightChain n ∈ active family T S) :
    (leftCore T S).Infinite := by
  have hJ := hT.2 S ⟨_, hK⟩
  have hfin : {m | Sum.inl m ∈ activeCore family T S}.Finite := by
    apply (Finset.range n).finite_toSet.subset
    intro m hm
    exact hm _ hK
  apply (Anchored.right_part_infinite hJ hfin).mono
  intro m hm D hD
  exact hm _ hD

/-- No infinite subsequence of this specified chain has bounded right-part witnesses. -/
theorem bounded_indices_finite {T : Set Point → Finset Point} (hT : Valid family T)
    (d : ℕ) : {n | (rightPart (T (rightChain n))).card ≤ d}.Finite := by
  classical
  by_contra hi
  let I := {n | (rightPart (T (rightChain n))).card ≤ d}
  have hI : I.Infinite := hi
  let e := hI.natEmbedding I
  let f : ℕ → ℕ := fun n => (e n).val
  have hf : Function.Injective f := Subtype.val_injective.comp e.injective
  let U := fun n => rightPart (T (rightChain (f n)))
  obtain ⟨D, hcap, havoid⟩ := bounded_capture_indexed d U
    (fun n => (e n).property) (leftCore T)
  let L := leftTarget D
  let b := (T L).sup (Sum.elim id id)
  obtain ⟨_, ⟨n, hncap, rfl⟩, hbn⟩ := (hcap.image hf.injOn).exists_gt b
  let K := rightChain (f n)
  have hLK : (↑(T L) : Set Point) ⊆ K := by
    rintro (m | m) hm
    · have hmb : m ≤ b := Finset.le_sup (f := Sum.elim id id) hm
      exact Finset.mem_range.mpr (by omega)
    · trivial
  have hKL : (↑(T K) : Set Point) ⊆ L := by
    rintro (m | m) hm
    · trivial
    · exact hncap ((mem_rightPart _ _).mpr hm)
  let S := T L ∪ T K
  have hLa : L ∈ active family T S := by
    refine ⟨left_mem D, Finset.subset_union_left, ?_⟩
    intro x hx
    rcases Finset.mem_union.mp hx with hx | hx
    · exact hT.1 _ (left_mem D) hx
    · exact hKL hx
  have hKa : K ∈ active family T S := by
    refine ⟨right_mem _, Finset.subset_union_right, ?_⟩
    intro x hx
    rcases Finset.mem_union.mp hx with hx | hx
    · exact hLK hx
    · exact hT.1 _ (right_mem _) hx
  exact havoid S (leftCore_infinite hT hKa) (fun x hx => hx D hLa)

theorem right_witness_divergence {T : Set Point → Finset Point} (hT : Valid family T) :
    ∀ d, ∃ N, ∀ n ≥ N, d ≤ (rightPart (T (rightChain n))).card := by
  intro d
  obtain ⟨N, hN⟩ := (bounded_indices_finite hT d).bddAbove
  refine ⟨N + 1, ?_⟩
  intro n hn
  by_contra hh
  have hsmall : (rightPart (T (rightChain n))).card ≤ d := by omega
  have := hN hsmall
  omega

theorem right_witness_tendsto {T : Set Point → Finset Point} (hT : Valid family T) :
    Filter.Tendsto (fun n => (rightPart (T (rightChain n))).card) Filter.atTop Filter.atTop :=
  Filter.tendsto_atTop_atTop.mpr (right_witness_divergence hT)

@[simp] theorem swap_family : transportClass (Equiv.sumComm ℕ ℕ) family = family := by
  ext L
  change ((∀ n, Sum.inr n ∈ L) ∨ (∀ n, Sum.inl n ∈ L)) ↔
    ((∀ n, Sum.inl n ∈ L) ∨ (∀ n, Sum.inr n ∈ L))
  exact or_comm

theorem swap_rightChain (n : ℕ) :
    (Equiv.sumComm ℕ ℕ) ⁻¹' rightChain n = leftChain n := by
  ext x
  cases x <;> rfl

theorem swap_rightPart (T : Set Point → Finset Point) (n : ℕ) :
    rightPart (transportAssignment (Equiv.sumComm ℕ ℕ) T (rightChain n)) =
      leftPart (T (leftChain n)) := by
  classical
  ext m
  simp only [mem_rightPart, mem_leftPart, transportAssignment, swap_rightChain]
  simp

theorem left_witness_divergence {T : Set Point → Finset Point} (hT : Valid family T) :
    ∀ d, ∃ N, ∀ n ≥ N, d ≤ (leftPart (T (leftChain n))).card := by
  have ht : Valid family (transportAssignment (Equiv.sumComm ℕ ℕ) T) := by
    simpa using hT.transport (Equiv.sumComm ℕ ℕ)
  simpa only [swap_rightPart] using right_witness_divergence ht

theorem left_witness_tendsto {T : Set Point → Finset Point} (hT : Valid family T) :
    Filter.Tendsto (fun n => (leftPart (T (leftChain n))).card) Filter.atTop Filter.atTop :=
  Filter.tendsto_atTop_atTop.mpr (left_witness_divergence hT)

end GenLimit.FiniteWitness.TwoCore
