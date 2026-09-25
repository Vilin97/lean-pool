/-
Copyright (c) 2026 Xiaoyu Li, Andi Han, Jiaojiao Jiang, Junbin Gao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xiaoyu Li, Andi Han, Jiaojiao Jiang, Junbin Gao
-/
module

public import LeanPool.LanguageGeneration.FiniteWitness.Width.Divergence
public import LeanPool.LanguageGeneration.FiniteWitness.Width.Singleton
public import Mathlib.Basic.Denumerable

/-!
# Endpoint examples and realization of the entire width range
-/

@[expose] public section

namespace GenLimit.FiniteWitness

variable {α : Type*}

/-- The family of all infinite subsets of a universe. -/
def allInfinite (α : Type*) : Set (Set α) := {L | L.Infinite}
/-- The family of subsets with finite complement. -/
def cofinite (α : Type*) : Set (Set α) := {L | Lᶜ.Finite}

theorem allInfinite_uus : Generic.UUS (allInfinite α) := fun _ h => h

theorem cofinite_uus [Infinite α] : Generic.UUS (cofinite α) :=
  fun _ h => Set.infinite_of_finite_compl h

theorem cofinite_subset_allInfinite [Infinite α] : cofinite α ⊆ allInfinite α := cofinite_uus

theorem cofinite_countable [Countable α] : (cofinite α).Countable := by
  classical
  apply (Set.countable_range (fun S : Finset α => (↑S : Set α)ᶜ)).mono
  intro L hL
  exact ⟨hL.toFinset, congrArg Set.compl hL.coe_toFinset |>.trans (compl_compl L)⟩

theorem cofinite_core_empty : ⋂₀ cofinite α = ∅ := by
  ext x
  simp only [Set.mem_empty_iff_false, iff_false]
  intro hx
  have hL : ({x}ᶜ : Set α) ∈ cofinite α := by simp [cofinite]
  have := hx _ hL
  simp at this

theorem cofinite_width [Countable α] [Infinite α] :
    separationWidth (cofinite α) = finiteValue 1 := by
  apply width_eq_finite_of_bounds
    (countable_hasBoundedWitnesses_one cofinite_countable cofinite_uus)
  intro q hq
  by_contra hn
  have hzero : q = 0 := by omega
  subst q
  have hh := (bounded_zero_iff_core_infinite (cofinite α)).mp hq
  rw [cofinite_core_empty] at hh
  exact hh Set.finite_empty

theorem allInfinite_no_finiteWitnesses [Countable α] [Infinite α] :
    ¬ HasFiniteWitnesses (allInfinite α) := by
  classical
  rintro ⟨T, hT⟩
  let e := (Set.infinite_univ : (Set.univ : Set α).Infinite).natEmbedding Set.univ
  let f : ℕ → α := fun n => (e n).val
  have hf : Function.Injective f := Subtype.val_injective.comp e.injective
  let U : ℕ → Finset α := fun n => {f n}
  obtain ⟨D, hcap, havoid⟩ := bounded_capture_indexed 1 U
    (fun _ => by simp [U]) (activeCore (allInfinite α) T)
  have hD : D.Infinite := by
    apply (hcap.image hf.injOn).mono
    rintro _ ⟨n, hn, rfl⟩
    exact hn (by simp [U])
  have ha : D ∈ active (allInfinite α) T (T D) :=
    ⟨hD, Finset.Subset.refl _, hT.1 D hD⟩
  exact havoid (T D) (hT.2 (T D) ⟨D, ha⟩) (fun x hx => hx D ha)

theorem allInfinite_width [Countable α] [Infinite α] :
    separationWidth (allInfinite α) = ⊤ :=
  (width_eq_top_iff _).mpr allInfinite_no_finiteWitnesses

theorem cofinite_ordinary [Countable α] [Infinite α] :
    Generic.GeneratableInLimit (cofinite α) :=
  countable_ordinary cofinite_countable cofinite_uus

theorem allInfinite_not_ordinary [Countable α] [Infinite α] :
    ¬ Generic.GeneratableInLimit (allInfinite α) := by
  rw [ordinary_iff_finiteWitnesses _ allInfinite_uus]
  exact allInfinite_no_finiteWitnesses

theorem full_range_on_sum (v : SeparationValue) :
    ∃ H : Set (Set TwoCore.Point), Generic.UUS H ∧ separationWidth H = v := by
  induction v using WithTop.recTopCoe with
  | top => exact ⟨allInfinite _, allInfinite_uus, allInfinite_width⟩
  | coe v =>
    induction v using WithTop.recTopCoe with
    | top => exact ⟨TwoCore.family, TwoCore.family_uus, TwoCore.exact_width⟩
    | coe d => exact ⟨Anchored.family (2 * d), Anchored.family_uus _,
        Anchored.realizes_every_finite d⟩

theorem full_range [Countable α] [Infinite α] (v : SeparationValue) :
    ∃ H : Set (Set α), Generic.UUS H ∧ separationWidth H = v := by
  classical
  let e : TwoCore.Point ≃ α := Classical.choice inferInstance
  obtain ⟨H, hH, hw⟩ := full_range_on_sum v
  exact ⟨transportClass e H, uus_transport hH e, (width_transport e H).trans hw⟩

end GenLimit.FiniteWitness
