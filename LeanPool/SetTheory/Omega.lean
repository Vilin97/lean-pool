/-
Copyright (c) 2026 Shuhao Song. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shuhao Song
-/
import LeanPool.SetTheory.Ordinals

/-!
# The first infinite ordinal in models of ZF

This module develops the theory of `ω` and the natural numbers inside a von Neumann model
of ZF, providing the infinitary tools needed for the Kunen inconsistency argument.
-/

noncomputable section

open SetTheory Ordinal Cardinal ZFSet Function

variable {M M₀} [ZFStructure M] [ZFStructure M₀]
    [hM : IsVonNeumann M] [hM₀ : IsVonNeumannWithOmega M₀]

/-- The `toZFSet` declaration. -/
def Set.toZFSet {A : ZFSet} (B : Set A) : ZFSet :=
  ZFSet.sep (fun x => ∃ hx : x ∈ A, ⟨x, hx⟩ ∈ B) A

@[simp] lemma Set.mem_toZFSet {A : ZFSet} (B : Set A) (x : ZFSet) :
    x ∈ B.toZFSet ↔ ∃ hx : x ∈ A, ⟨x, hx⟩ ∈ B := by
  simp [Set.toZFSet]

namespace SetTheory

/-- The `IsWellFoundedRevMem` declaration. -/
@[realize] def IsWellFoundedRevMem (x : M) := ∀ S ∈ 𝓟 x, S ≠ ∅ → ∃ y ∈ S, ∀ z ∈ S, y ∉ z
/-- The `MemOmega` declaration. -/
@[realize] def MemOmega (x : M) := IsOrdinal x ∧ IsWellFoundedRevMem x
@[toV_simps] lemma IsWellFoundedRevMem.toV (x : M) :
    IsWellFoundedRevMem ↓x ↔ IsWellFoundedRevMem x := by
  simp only [IsWellFoundedRevMem, toV_simps, empty.toV (M := M)]

@[toZFSet_simps] lemma forall_set {x : ZFSet} {p : Set x → Prop} :
    (∀ y : Set x, p y) ↔ (∀ y ⊆ x, p {z : x | z.1 ∈ y}) := by
  refine ⟨fun h _ _ => h _, fun h y => ?_⟩
  convert h y.toZFSet ?_
  · ext z
    simp
  · intro z
    simpa using fun hz _ => hz

@[toZFSet_simps] lemma IsWellFoundedRevMem.toZFSet (x : M) :
    IsWellFoundedRevMem x ↔ IsWellFounded ⇓x fun a b => b ∈ a := by
  rw [← IsWellFoundedRevMem.toV]
  simp only [IsWellFoundedRevMem, isWellFounded_iff, WellFounded.wellFounded_iff_has_min,
    powerset.spec, toZFSet_simps, Subtype.forall, Subtype.exists,
    Set.mem_setOf_eq, mem_inside_ZFSet, exists_and_left, exists_prop]
  conv =>
    enter [2, y, hy, ne, 1, z]
    rw [← and_assoc, and_iff_left_of_imp (@hy z)]
    enter [2, u]
    rw [← and_imp, and_iff_right_of_imp (@hy u)]
  congr! 4 with y hy sub
  simp only [ne_eq, ZFSet.ext_iff, notMem_empty, iff_false, not_forall, not_not, Set.Nonempty,
    Set.mem_setOf_eq, Subtype.exists, exists_prop]
  conv =>
    enter [2, 1, z]
    erw [and_iff_right_of_imp (@hy z)]

/-- The `ωₛ` declaration. -/
def ωₛ := Ordinal.toZFSet ω

instance instNatCastM : NatCast M where
  natCast (n : ℕ) := by
    split_vonNeumann hM
    · refine ⟨Ordinal.toZFSet n, ?_⟩
      erw [mem_vonNeumann, rank_toZFSet]
      exact natCast_lt_of_isSuccLimit hμ _
    · exact ↓(Ordinal.toZFSet n)

instance instOfNatM {n} : OfNat M n where
  ofNat := (n : M)

@[toZFSet_simps] lemma NatCast.natCast.toZFSet {n : ℕ} : ⇓(n : M) = Ordinal.toZFSet n := by
  split_vonNeumann hM <;> rfl

lemma ofNat_eq_natCast (n : ℕ) : (OfNat.ofNat n : M) = n := rfl

lemma natCast_zero : (0 : M) = ∅ := by
  simp [toZFSet_simps, ofNat_eq_natCast]

lemma natCast_succ {n : ℕ} : ((n + 1 : ℕ) : M) = succ (n : M) := by
  simp [toZFSet_simps]

lemma toZFSet_nat_mem_ωₛ {n : ℕ} : Ordinal.toZFSet n ∈ ωₛ := by
  simpa only [ωₛ] using toZFSet_mem_toZFSet_iff.mpr <| natCast_lt_omega0 _

lemma eq_natCast_of_mem_ωₛ {α} (hα : α ∈ ωₛ) : ∃ n : ℕ, α = Ordinal.toZFSet n := by
  have ord_α := (isOrdinal_toZFSet _).mem hα
  obtain ⟨α, ⟨_⟩⟩ := isOrdinal_iff_mem_range_toZFSet.mp ord_α
  simpa [ωₛ, toZFSet_mem_toZFSet_iff, lt_omega0, toZFSet_strictMono.injective.eq_iff] using hα

lemma nwf_rev_of_ωₛ_le {α} (hα : ωₛ ≤ α) : ¬IsWellFounded α (fun x y => y ∈ x) := by
  intro ⟨h⟩
  rw [wellFounded_iff_isEmpty_descending_chain] at h
  refine h.false ⟨fun n => ⟨Ordinal.toZFSet n, hα toZFSet_nat_mem_ωₛ⟩, ?_⟩
  simpa only [mem_inside_ZFSet] using fun n => toZFSet_mem_toZFSet_iff.mpr (by simp)

lemma wf_rev_of_lt_ωₛ {α} (hα : α ∈ ωₛ) : IsWellFounded α (fun x y => y ∈ x) := by
  rw [isWellFounded_iff]
  refine @Finite.wellFounded_of_trans_of_irrefl _ ?_  _ ?_ ?_
  · obtain ⟨n, ⟨_⟩⟩ := eq_natCast_of_mem_ωₛ hα
    erw [← mk_lt_aleph0_iff, cardinalMk_coe_sort]
    simp only [card_toZFSet, lift_lt_aleph0, card_lt_aleph0, natCast_lt_omega0]
  · have ord_α := (isOrdinal_toZFSet _).mem hα
    refine ⟨fun x y z hy hz => ?_⟩
    simp only [mem_inside_ZFSet] at *
    exact ord_α.2 hz hy x.2
  · refine ⟨fun x => ?_⟩
    simp [mem_inside_ZFSet, mem_irrefl]

@[toV_simps] lemma MemOmega.toV (n : M) : MemOmega ↓n ↔ MemOmega n := by
  simp only [MemOmega, toV_simps]

@[toZFSet_simps] lemma MemOmega.toZFSet (n : M) : MemOmega n ↔ ⇓n ∈ ωₛ := by
  rw [← MemOmega.toV, MemOmega]
  conv_rhs => rw [← ToZFSet.toZFSet_toV]
  generalize ↓n = n
  refine ⟨fun | ⟨ord, wf_rev⟩ => ?_, fun sub => ?_⟩
  · simp only [toZFSet_simps] at ord wf_rev
    exact (ord.mem_or_subset (isOrdinal_toZFSet _)).resolve_right
      fun sub => nwf_rev_of_ωₛ_le sub wf_rev
  · simpa only [toZFSet_simps]
      using ⟨(isOrdinal_toZFSet _).mem sub, wf_rev_of_lt_ωₛ sub⟩

lemma eq_natCast_of_memOmega {α : M} (hα : MemOmega α) : ∃ n : ℕ, α = n := by
  simp only [toZFSet_simps] at hα ⊢
  exact eq_natCast_of_mem_ωₛ hα

lemma memOmega_natCast {n : ℕ} : MemOmega (n : M) := by
  simp only [toZFSet_simps, toZFSet_nat_mem_ωₛ]

@[realize] lemma ωₘ.eu : IsSet {n : M₀ | MemOmega n} := by
  rw [isSet_iff]
  split_vonNeumann_omega hM₀
  · refine ⟨⟨ωₛ, by simpa [ωₛ, mem_vonNeumann]⟩, ?_⟩
    intro y hy
    rw [Set.mem_setOf_eq, MemOmega.toZFSet] at hy
    rwa [ToZFSet.mem, ToZFSet.toZFSet_vonNeumann]
  · refine ⟨↓ωₛ, ?_⟩
    intro y hy
    rw [Set.mem_setOf_eq, MemOmega.toZFSet] at hy
    rw [ToZFSet.mem, ToZFSet.toV_ZFSet, ToZFSet.toZFSet_V]
    exact hy

@[simp] lemma natCast_mem_ωₘ {n : ℕ} : (n : M₀) ∈ (ωₘ : M₀) := by
  simp only [ωₘ.spec, memOmega_natCast]

@[toV_simps] lemma ωₘ.toV : ωₘ = ↓(ωₘ : M₀) := by
  rw [ωₘ.eq_iff, ToV.forall_mem_toV_iff]
  · simpa only [toV_simps] using ωₘ.spec
  · intro α hα
    simp only [toZFSet_simps] at hα ⊢
    generalize α.val = α at *
    obtain ⟨n, ⟨_⟩⟩ := eq_natCast_of_mem_ωₛ hα
    exact ⟨n, by simp only [toZFSet_simps]⟩

@[toZFSet_simps] lemma ωₘ.toZFSet : ⇓(ωₘ : M₀) = ωₛ := by
  rw [← ToZFSet.toZFSet_toV, ← ωₘ.toV]
  have (x : V) : x ∈ (ωₘ : V) ↔ ⇓x ∈ ωₛ := by rw [ωₘ.spec, MemOmega.toZFSet]
  simpa [ZFSet.ext_iff, toZFSet_simps] using this

@[simp] lemma isOrdinal_ωₘ : IsOrdinal (ωₘ : M₀) := by
  rw [IsOrdinal.toZFSet, ωₘ.toZFSet, ωₛ]
  exact isOrdinal_toZFSet _

/-- The `omegaEquiv` declaration. -/
def omegaEquiv : (ωₘ : M₀) ≃ ℕ :=
  Equiv.symm <| Equiv.ofBijective (fun n => ⟨Nat.cast n, natCast_mem_ωₘ⟩) <| by
    simp only [Bijective, Injective, Surjective, toZFSet_simps, Subtype.forall,
      Subtype.mk.injEq, toZFSet_strictMono.injective.eq_iff]
    refine ⟨fun m n eq => ?_, fun α hα => ?_⟩
    · apply_fun (·.card.toNat) at eq
      simpa using eq
    · replace hα : ⇓α ∈ ωₛ := MemOmega.toZFSet _ |>.mp (ωₘ.spec _ |>.mp hα)
      simpa only [eq_comm] using eq_natCast_of_mem_ωₛ hα

instance {n : ℕ} : OfNat (Ordinals M) n where
  ofNat := ⟨(n : M), memOmega_natCast.1⟩

end SetTheory
