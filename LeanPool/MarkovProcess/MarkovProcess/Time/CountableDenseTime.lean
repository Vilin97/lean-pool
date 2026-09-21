/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
import Mathlib.Data.NNRat.Defs
import Mathlib.Basic.NNReal.Defs
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Data.Rat.Encodable
import Mathlib.Basic.Denumerable
import Mathlib.MeasureTheory.MeasurableSpace.Embedding

/-!
# Countable dense time indices

This file gives finite prefixes and measurable path reindexings for an arbitrary enumeration of
a countably infinite type. The fixed enumeration of nonnegative rational times below is arbitrary,
not increasing. No probability law, projective limit, stochastic process, continuity, or path
regularity is constructed here.
-/

noncomputable section PortComputability

namespace MarkovProcess

section

namespace CountableEnumeration

variable {D : Type*}

/-- The first `n` values of an enumeration. -/
def «prefix» (e : ℕ ≃ D) (n : ℕ) : Finset D :=
  Finset.map e.toEmbedding (Finset.range n)

@[simp]
theorem mem_prefix_iff (e : ℕ ≃ D) (n : ℕ) (d : D) :
    d ∈ «prefix» e n ↔ e.symm d < n := by
  simp only [«prefix», Finset.mem_map, Finset.mem_range]
  constructor
  · rintro ⟨k, hk, hkd⟩
    rw [← hkd]
    change e.symm (e k) < n
    rw [e.symm_apply_apply]
    exact hk
  · intro hd
    exact ⟨e.symm d, hd, e.apply_symm_apply d⟩

@[simp]
theorem prefix_zero (e : ℕ ≃ D) : «prefix» e 0 = ∅ := by
  rw [«prefix», Finset.range_zero, Finset.map_empty]

@[simp]
theorem prefix_succ (e : ℕ ≃ D) (n : ℕ) :
    «prefix» e (n + 1) =
      Finset.cons (e n) («prefix» e n) (by
        rw [mem_prefix_iff, e.symm_apply_apply]
        exact Nat.lt_irrefl n) := by
  ext d
  rw [mem_prefix_iff, Finset.mem_cons, mem_prefix_iff, Nat.lt_succ_iff]
  constructor
  · intro h
    obtain h | h := h.eq_or_lt
    · left
      apply e.symm.injective
      simpa only [e.symm_apply_apply] using h
    · exact Or.inr h
  · rintro (rfl | h)
    · rw [e.symm_apply_apply]
    · exact h.le

theorem prefix_mono (e : ℕ ≃ D) : Monotone («prefix» e) := by
  intro m n hmn d
  simp only [mem_prefix_iff]
  exact fun hd ↦ hd.trans_le hmn

@[simp]
theorem card_prefix (e : ℕ ≃ D) (n : ℕ) : («prefix» e n).card = n := by
  rw [«prefix», Finset.card_map, Finset.card_range]

theorem mem_prefix_self (e : ℕ ≃ D) (d : D) : d ∈ «prefix» e (e.symm d + 1) := by
  rw [mem_prefix_iff]
  exact Nat.lt_succ_self _

theorem exists_mem_prefix (e : ℕ ≃ D) (d : D) : ∃ n, d ∈ «prefix» e n :=
  ⟨e.symm d + 1, mem_prefix_self e d⟩

/-- The enumeration equivalence between `Fin n` and its first `n` values. -/
noncomputable def finEquivPrefix (e : ℕ ≃ D) (n : ℕ) : Fin n ≃ «prefix» e n :=
  Equiv.ofBijective
    (fun i ↦ ⟨e i, by rw [mem_prefix_iff]; simpa only [e.symm_apply_apply] using i.isLt⟩)
    ⟨fun _ _ h ↦ Fin.ext (e.injective (congrArg Subtype.val h)), fun d ↦ by
      refine ⟨⟨e.symm d, ?_⟩, ?_⟩
      · exact (mem_prefix_iff e n d).mp d.property
      · apply Subtype.ext
        exact e.apply_symm_apply d⟩

/-- Measurable reindexing between an ordered prefix path and an enumeration-prefix path. -/
noncomputable def measurableEquivFinPrefix (e : ℕ ≃ D) (n : ℕ) (α : Type*)
    [MeasurableSpace α] : (Fin n → α) ≃ᵐ («prefix» e n → α) :=
  MeasurableEquiv.piCongrLeft (fun _ : «prefix» e n ↦ α) (finEquivPrefix e n)

/-- Measurable reindexing between paths on `ℕ` and paths on the enumerated type. -/
def measurableEquivPath (e : ℕ ≃ D) (α : Type*) [MeasurableSpace α] :
    (ℕ → α) ≃ᵐ (D → α) :=
  MeasurableEquiv.piCongrLeft (fun _ : D ↦ α) e

end CountableEnumeration

/-- The countable dense carrier of nonnegative rational times. -/
abbrev DenseTime := NNRat

namespace DenseTime

/-- The order embedding of nonnegative rational times into nonnegative real times. -/
noncomputable def castOrderEmbedding : DenseTime ↪o NNReal :=
  NNRat.castOrderEmbedding

/-- Between two distinct nonnegative real times lies a nonnegative rational time. -/
theorem exists_cast_btwn {a b : NNReal} (hab : a < b) :
    ∃ q : DenseTime, a < castOrderEmbedding q ∧ castOrderEmbedding q < b := by
  obtain ⟨q, hq, haq, hqb⟩ := (NNReal.lt_iff_exists_rat_btwn a b).mp hab
  have hcast : NNRat.cast (K := NNReal) ⟨q, hq⟩ = Real.toNNReal q := by
    apply NNReal.eq
    rw [Real.coe_toNNReal _ (Rat.cast_nonneg.mpr hq)]
    norm_cast
  have hcoe : castOrderEmbedding ⟨q, hq⟩ = NNRat.cast (K := NNReal) ⟨q, hq⟩ := rfl
  refine ⟨⟨q, hq⟩, ?_, ?_⟩
  · rw [hcoe, hcast]
    exact haq
  · rw [hcoe, hcast]
    exact hqb

private instance : Infinite DenseTime :=
  Infinite.of_injective (fun n : ℕ ↦ (n : DenseTime)) Nat.cast_injective

private instance : Countable DenseTime where
  exists_injective_nat' :=
    ⟨fun q ↦ Encodable.encode (q : ℚ), fun _ _ h ↦
      NNRat.ext (Encodable.encode_injective h)⟩

/-- A fixed arbitrary enumeration of nonnegative rational times. It is not order-preserving. -/
noncomputable def enumeration : ℕ ≃ DenseTime :=
  nonempty_equiv_of_countable.some

end DenseTime
end
end MarkovProcess

end PortComputability
