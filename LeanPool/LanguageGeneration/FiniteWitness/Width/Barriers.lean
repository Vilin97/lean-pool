/-
Copyright (c) 2026 Xiaoyu Li, Andi Han, Jiaojiao Jiang, Junbin Gao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xiaoyu Li, Andi Han, Jiaojiao Jiang, Junbin Gao
-/
module

public import LeanPool.LanguageGeneration.FiniteWitness.Width.Endpoints
public import Mathlib.Tactic.Tauto

/-!
# Obstructions to countable tests and finite observation profiles
-/

@[expose] public section

namespace GenLimit.FiniteWitness

variable {α : Type*}

/-- The dimension is completely arbitrary: no monotonicity or computability assumption. -/
theorem no_countably_supported_dimension [Countable α] [Infinite α] :
    ¬ ∃ D : Set (Set α) → WithTop ℕ,
      (∀ H, Generic.UUS H → (Generic.GeneratableInLimit H ↔ D H < ⊤)) ∧
      (∀ H, Generic.UUS H → D H = ⊤ →
        ∃ K ⊆ H, K.Countable ∧ D K = ⊤) := by
  rintro ⟨D, hchar, hsupp⟩
  have htop : D (allInfinite α) = ⊤ := by
    by_contra hn
    exact allInfinite_not_ordinary ((hchar _ allInfinite_uus).mpr
      (lt_top_iff_ne_top.mpr hn))
  obtain ⟨K, hK, hc, hd⟩ := hsupp _ allInfinite_uus htop
  have hu : Generic.UUS K := fun L hL => hK hL
  have hg := countable_ordinary hc hu
  have hlt := (hchar K hu).mp hg
  simp [hd] at hlt

theorem finite_level_not_countably_determined (d : ℕ) :
    ∃ H : Set (Set TwoCore.Point), Generic.UUS H ∧
      separationWidth H = finiteValue (d + 1) ∧
      ∀ K ⊆ H, K.Countable → separationWidth K ≤ finiteValue 1 := by
  refine ⟨Anchored.family (2 * d + 1), Anchored.family_uus _, ?_, ?_⟩
  · rw [Anchored.exact_width]
    congr 1
    omega
  · intro K hK hc
    exact (width_le_finite_iff K 1).mpr (countable_hasBoundedWitnesses_one hc
      (fun L hL => Anchored.family_uus _ L (hK hL)))

/-- All restrictions of target languages to a fixed finite observation set. -/
def finiteTraces (H : Set (Set α)) (F : Finset α) : Set (Set α) :=
  {E | ∃ L ∈ H, L ∩ (↑F : Set α) = E}

/-- The intersection of all target languages consistent with a finite positive sample. -/
def positiveClosure (H : Set (Set α)) (S : Finset α) : Set α :=
  {x | ∀ L ∈ H, (↑S : Set α) ⊆ L → x ∈ L}

theorem full_finiteTraces_of_cofinite_subset {H : Set (Set α)} (hH : cofinite α ⊆ H)
    (F : Finset α) : finiteTraces H F = Set.powerset (↑F : Set α) := by
  classical
  ext E
  constructor
  · rintro ⟨L, _, rfl⟩
    exact Set.inter_subset_right
  · intro hE
    refine ⟨((↑F : Set α) \ E)ᶜ, hH ?_, ?_⟩
    · change (((↑F : Set α) \ E)ᶜ)ᶜ.Finite
      simpa only [compl_compl] using (F.finite_toSet.sdiff : ((↑F : Set α) \ E).Finite)
    · ext x
      simp only [Set.mem_inter_iff, Set.mem_compl_iff, Set.mem_sdiff]
      have he : x ∈ E → x ∈ (↑F : Set α) := fun hx => hE hx
      tauto

theorem positiveClosure_of_cofinite_subset {H : Set (Set α)} (hH : cofinite α ⊆ H)
    (S : Finset α) : positiveClosure H S = (↑S : Set α) := by
  classical
  ext x
  constructor
  · intro hx
    by_contra hn
    have hL : ({x}ᶜ : Set α) ∈ H := hH (by simp [cofinite])
    have hSL : (↑S : Set α) ⊆ {x}ᶜ := by
      intro y hy he
      have hyx : y = x := he
      subst y
      exact hn hy
    exact hx _ hL hSL rfl
  · intro hx L _ hSL
    exact hSL hx

theorem identical_finite_profiles [Infinite α] :
    (∀ F : Finset α, finiteTraces (cofinite α) F = finiteTraces (allInfinite α) F) ∧
    (∀ S : Finset α, positiveClosure (cofinite α) S = positiveClosure (allInfinite α) S) := by
  constructor
  · intro F
    rw [full_finiteTraces_of_cofinite_subset (Set.Subset.refl _) F,
      full_finiteTraces_of_cofinite_subset cofinite_subset_allInfinite F]
  · intro S
    rw [positiveClosure_of_cofinite_subset (Set.Subset.refl _) S,
      positiveClosure_of_cofinite_subset cofinite_subset_allInfinite S]

theorem profiles_do_not_determine_ordinary [Countable α] [Infinite α] :
    (∀ F : Finset α, finiteTraces (cofinite α) F = finiteTraces (allInfinite α) F) ∧
    (∀ S : Finset α, positiveClosure (cofinite α) S = positiveClosure (allInfinite α) S) ∧
    Generic.GeneratableInLimit (cofinite α) ∧ ¬ Generic.GeneratableInLimit (allInfinite α) :=
  ⟨identical_finite_profiles.1, identical_finite_profiles.2,
    cofinite_ordinary, allInfinite_not_ordinary⟩

end GenLimit.FiniteWitness
