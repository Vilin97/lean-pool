/-
Copyright (c) 2026 Catskills Research Company. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Catskills Research Company
-/

import LeanPool.DomainTheory.Neighborhood.Example62
import LeanPool.DomainTheory.Neighborhood.Example44
import LeanPool.DomainTheory.Neighborhood.Exercise315

/-!
# Example 6.2 (Scott 1981, PRG-19, §6) — `C ≅ {{Λ}} + C + C`

Following Dana Scott, *Lectures on a Mathematical Theory of Computation*, PRG-19
(1981), Lecture VI.
This module formalizes the second domain equation of Example 6.2, for the system
`C` of finite or
infinite binary sequences (Example 4.4):

`C ≅ {{Λ}} + C + C`,

where `{{Λ}} = 𝟙` is the one-point (unit) domain (Exercise 3.15). Presented over
`{0,1}*`,

`C = {Σ*} ∪ {{Λ}} ∪ {0X ∣ X ∈ C} ∪ {1X ∣ X ∈ C}`,

so a neighbourhood of `C` is the master `Σ*` (`= cone []`), the terminator `{Λ} =
{[]}`, a `0`-copy
`0X = embBit false X`, or a `1`-copy `1X = embBit true X`. These four shapes are
exactly those of a
**three-way separated sum** `𝟙 + C + C`: a fresh basepoint, plus one `𝟙`-copy (the
lone `{Λ}`), plus
two `C`-copies.

Crucially this is a genuine *three-way* sum: nesting the binary sum (`𝟙 + (C +
C)`) would introduce a
spurious extra bottom element (the inner sum's basepoint) with no counterpart in
`C`. So we first build
the three-way separated sum `sum3` (mirroring Exercise 3.18), then exhibit the
order-isomorphism
`ccEquiv : |C| ≃o |𝟙 + C + C|`.

All *data* is choice-free (`#print axioms ⊆ {propext, Quot.sound}`).
-/

namespace Domain.Neighborhood

open NeighborhoodSystem ApproximableMap ExampleB Example44 Example62

/-! ## The three-way separated sum `D₀ + D₁ + D₂`.

Tokens are `Option (α ⊕ β ⊕ γ)`: a fresh basepoint `Λ = none` below three disjoint
tagged copies. -/

/-- Left tag `0a = some (inl a)`. -/
def t0 {α β γ : Type*} (a : α) : Option (α ⊕ β ⊕ γ) := some (Sum.inl a)

/-- Middle tag `1b = some (inr (inl b))`. -/
def t1 {α β γ : Type*} (b : β) : Option (α ⊕ β ⊕ γ) := some (Sum.inr (Sum.inl b))

/-- Right tag `2c = some (inr (inr c))`. -/
def t2 {α β γ : Type*} (c : γ) : Option (α ⊕ β ⊕ γ) := some (Sum.inr (Sum.inr c))

/-- The tagged left copy `0X`. -/
def j0 {α β γ : Type*} (X : Set α) : Set (Option (α ⊕ β ⊕ γ)) := {w | ∃ a, w = t0 a ∧ a ∈ X}

/-- The tagged middle copy `1Y`. -/
def j1 {α β γ : Type*} (Y : Set β) : Set (Option (α ⊕ β ⊕ γ)) := {w | ∃ b, w = t1 b ∧ b ∈ Y}

/-- The tagged right copy `2Z`. -/
def j2 {α β γ : Type*} (Z : Set γ) : Set (Option (α ⊕ β ⊕ γ)) := {w | ∃ c, w = t2 c ∧ c ∈ Z}

variable {α β γ : Type*}

@[simp] theorem t0_mem_j0 {X : Set α} {a : α} : (t0 a : Option (α ⊕ β ⊕ γ)) ∈ j0 X ↔ a ∈ X := by
  constructor
  · rintro ⟨a', heq, ha'⟩; simp only [t0, Option.some.injEq, Sum.inl.injEq] at heq; exact heq ▸ ha'
  · intro ha; exact ⟨a, rfl, ha⟩

@[simp] theorem t1_mem_j1 {Y : Set β} {b : β} : (t1 b : Option (α ⊕ β ⊕ γ)) ∈ j1 Y ↔ b ∈ Y := by
  constructor
  · rintro ⟨b', heq, hb'⟩
    simp only [t1, Option.some.injEq, Sum.inr.injEq, Sum.inl.injEq] at heq; exact heq ▸ hb'
  · intro hb; exact ⟨b, rfl, hb⟩

@[simp] theorem t2_mem_j2 {Z : Set γ} {c : γ} : (t2 c : Option (α ⊕ β ⊕ γ)) ∈ j2 Z ↔ c ∈ Z := by
  constructor
  · rintro ⟨c', heq, hc'⟩
    simp only [t2, Option.some.injEq, Sum.inr.injEq] at heq; exact heq ▸ hc'
  · intro hc; exact ⟨c, rfl, hc⟩

@[simp] theorem none_not_mem_j0 {X : Set α} : (none : Option (α ⊕ β ⊕ γ)) ∉ j0 X := by
  rintro ⟨a, heq, -⟩; exact absurd heq (by simp [t0])

@[simp] theorem none_not_mem_j1 {Y : Set β} : (none : Option (α ⊕ β ⊕ γ)) ∉ j1 Y := by
  rintro ⟨b, heq, -⟩; exact absurd heq (by simp [t1])

@[simp] theorem none_not_mem_j2 {Z : Set γ} : (none : Option (α ⊕ β ⊕ γ)) ∉ j2 Z := by
  rintro ⟨c, heq, -⟩; exact absurd heq (by simp [t2])

@[simp] theorem t1_not_mem_j0 {X : Set α} {b : β} : (t1 b : Option (α ⊕ β ⊕ γ)) ∉ j0 X := by
  rintro ⟨a, heq, -⟩; exact absurd heq (by simp [t0, t1])

@[simp] theorem t2_not_mem_j0 {X : Set α} {c : γ} : (t2 c : Option (α ⊕ β ⊕ γ)) ∉ j0 X := by
  rintro ⟨a, heq, -⟩; exact absurd heq (by simp [t0, t2])

@[simp] theorem t0_not_mem_j1 {Y : Set β} {a : α} : (t0 a : Option (α ⊕ β ⊕ γ)) ∉ j1 Y := by
  rintro ⟨b, heq, -⟩; exact absurd heq (by simp [t0, t1])

@[simp] theorem t2_not_mem_j1 {Y : Set β} {c : γ} : (t2 c : Option (α ⊕ β ⊕ γ)) ∉ j1 Y := by
  rintro ⟨b, heq, -⟩; exact absurd heq (by simp [t1, t2])

@[simp] theorem t0_not_mem_j2 {Z : Set γ} {a : α} : (t0 a : Option (α ⊕ β ⊕ γ)) ∉ j2 Z := by
  rintro ⟨c, heq, -⟩; exact absurd heq (by simp [t0, t2])

@[simp] theorem t1_not_mem_j2 {Z : Set γ} {b : β} : (t1 b : Option (α ⊕ β ⊕ γ)) ∉ j2 Z := by
  rintro ⟨c, heq, -⟩; exact absurd heq (by simp [t1, t2])

theorem j0_inter_j0 (X X' : Set α) :
    (j0 X ∩ j0 X' : Set (Option (α ⊕ β ⊕ γ))) = j0 (X ∩ X') := by
  ext w; rcases w with _ | (a | b | c) <;>
    simp [j0, t0, Set.mem_inter_iff]

theorem j1_inter_j1 (Y Y' : Set β) :
    (j1 Y ∩ j1 Y' : Set (Option (α ⊕ β ⊕ γ))) = j1 (Y ∩ Y') := by
  ext w; rcases w with _ | (a | b | c) <;>
    simp [j1, t1, Set.mem_inter_iff]

theorem j2_inter_j2 (Z Z' : Set γ) :
    (j2 Z ∩ j2 Z' : Set (Option (α ⊕ β ⊕ γ))) = j2 (Z ∩ Z') := by
  ext w; rcases w with _ | (a | b | c) <;>
    simp [j2, t2, Set.mem_inter_iff]

theorem j0_inter_j1 (X : Set α) (Y : Set β) :
    (j0 X ∩ j1 Y : Set (Option (α ⊕ β ⊕ γ))) = ∅ := by
  ext w; rcases w with _ | (a | b | c) <;>
    simp [j0, j1, t0, t1, Set.mem_inter_iff]

theorem j0_inter_j2 (X : Set α) (Z : Set γ) :
    (j0 X ∩ j2 Z : Set (Option (α ⊕ β ⊕ γ))) = ∅ := by
  ext w; rcases w with _ | (a | b | c) <;>
    simp [j0, j2, t0, t2, Set.mem_inter_iff]

theorem j1_inter_j2 (Y : Set β) (Z : Set γ) :
    (j1 Y ∩ j2 Z : Set (Option (α ⊕ β ⊕ γ))) = ∅ := by
  ext w; rcases w with _ | (a | b | c) <;>
    simp [j1, j2, t1, t2, Set.mem_inter_iff]

theorem j0_nonempty {X : Set α} (hX : X.Nonempty) : (j0 X : Set (Option (α ⊕ β ⊕ γ))).Nonempty := by
  obtain ⟨a, ha⟩ := hX; exact ⟨t0 a, a, rfl, ha⟩

theorem j1_nonempty {Y : Set β} (hY : Y.Nonempty) : (j1 Y : Set (Option (α ⊕ β ⊕ γ))).Nonempty := by
  obtain ⟨b, hb⟩ := hY; exact ⟨t1 b, b, rfl, hb⟩

theorem j2_nonempty {Z : Set γ} (hZ : Z.Nonempty) : (j2 Z : Set (Option (α ⊕ β ⊕ γ))).Nonempty := by
  obtain ⟨c, hc⟩ := hZ; exact ⟨t2 c, c, rfl, hc⟩

theorem j0_subset_j0 {X X' : Set α} :
    (j0 X : Set (Option (α ⊕ β ⊕ γ))) ⊆ j0 X' ↔ X ⊆ X' := by
  constructor
  · intro h a ha; exact t0_mem_j0.mp (h (t0_mem_j0.mpr ha))
  · rintro h w ⟨a, rfl, ha⟩; exact t0_mem_j0.mpr (h ha)

theorem j1_subset_j1 {Y Y' : Set β} :
    (j1 Y : Set (Option (α ⊕ β ⊕ γ))) ⊆ j1 Y' ↔ Y ⊆ Y' := by
  constructor
  · intro h b hb; exact t1_mem_j1.mp (h (t1_mem_j1.mpr hb))
  · rintro h w ⟨b, rfl, hb⟩; exact t1_mem_j1.mpr (h hb)

theorem j2_subset_j2 {Z Z' : Set γ} :
    (j2 Z : Set (Option (α ⊕ β ⊕ γ))) ⊆ j2 Z' ↔ Z ⊆ Z' := by
  constructor
  · intro h c hc; exact t2_mem_j2.mp (h (t2_mem_j2.mpr hc))
  · rintro h w ⟨c, rfl, hc⟩; exact t2_mem_j2.mpr (h hc)

theorem j0_injective {X X' : Set α}
    (h : (j0 X : Set (Option (α ⊕ β ⊕ γ))) = j0 X') : X = X' :=
  Set.Subset.antisymm (j0_subset_j0.mp h.subset) (j0_subset_j0.mp h.symm.subset)

theorem j1_injective {Y Y' : Set β}
    (h : (j1 Y : Set (Option (α ⊕ β ⊕ γ))) = j1 Y') : Y = Y' :=
  Set.Subset.antisymm (j1_subset_j1.mp h.subset) (j1_subset_j1.mp h.symm.subset)

theorem j2_injective {Z Z' : Set γ}
    (h : (j2 Z : Set (Option (α ⊕ β ⊕ γ))) = j2 Z') : Z = Z' :=
  Set.Subset.antisymm (j2_subset_j2.mp h.subset) (j2_subset_j2.mp h.symm.subset)

variable (V₀ : NeighborhoodSystem α) (V₁ : NeighborhoodSystem β) (V₂ : NeighborhoodSystem γ)

/-- The master neighbourhood of the three-way sum: `{Λ} ∪ 0Δ₀ ∪ 1Δ₁ ∪ 2Δ₂`. -/
def master3 : Set (Option (α ⊕ β ⊕ γ)) :=
  insert none (j0 V₀.master ∪ j1 V₁.master ∪ j2 V₂.master)

variable {V₀ V₁ V₂}

@[simp] theorem none_mem_master3 : (none : Option (α ⊕ β ⊕ γ)) ∈ master3 V₀ V₁ V₂ :=
  Set.mem_insert _ _

theorem j0_subset_master3 {X : Set α} (hX : V₀.mem X) :
    (j0 X : Set (Option (α ⊕ β ⊕ γ))) ⊆ master3 V₀ V₁ V₂ := by
  rintro w ⟨a, rfl, ha⟩
  exact Set.mem_insert_iff.mpr (Or.inr (Set.mem_union_left _
    (Set.mem_union_left _ (t0_mem_j0.mpr (V₀.sub_master hX ha)))))

theorem j1_subset_master3 {Y : Set β} (hY : V₁.mem Y) :
    (j1 Y : Set (Option (α ⊕ β ⊕ γ))) ⊆ master3 V₀ V₁ V₂ := by
  rintro w ⟨b, rfl, hb⟩
  exact Set.mem_insert_iff.mpr (Or.inr (Set.mem_union_left _
    (Set.mem_union_right _ (t1_mem_j1.mpr (V₁.sub_master hY hb)))))

theorem j2_subset_master3 {Z : Set γ} (hZ : V₂.mem Z) :
    (j2 Z : Set (Option (α ⊕ β ⊕ γ))) ⊆ master3 V₀ V₁ V₂ := by
  rintro w ⟨c, rfl, hc⟩
  exact Set.mem_insert_iff.mpr
    (Or.inr (Set.mem_union_right _ (t2_mem_j2.mpr (V₂.sub_master hZ hc))))

theorem master3_inter_j0 {X : Set α} (hX : V₀.mem X) :
    (master3 V₀ V₁ V₂ ∩ j0 X : Set (Option (α ⊕ β ⊕ γ))) = j0 X :=
  Set.inter_eq_right.mpr (j0_subset_master3 hX)

theorem master3_inter_j1 {Y : Set β} (hY : V₁.mem Y) :
    (master3 V₀ V₁ V₂ ∩ j1 Y : Set (Option (α ⊕ β ⊕ γ))) = j1 Y :=
  Set.inter_eq_right.mpr (j1_subset_master3 hY)

theorem master3_inter_j2 {Z : Set γ} (hZ : V₂.mem Z) :
    (master3 V₀ V₁ V₂ ∩ j2 Z : Set (Option (α ⊕ β ⊕ γ))) = j2 Z :=
  Set.inter_eq_right.mpr (j2_subset_master3 hZ)

theorem eq_master3_of_subset {W : Set (Option (α ⊕ β ⊕ γ))}
    (hsub : master3 V₀ V₁ V₂ ⊆ W) (hsub' : W ⊆ master3 V₀ V₁ V₂) : W = master3 V₀ V₁ V₂ :=
  Set.Subset.antisymm hsub' hsub

/-- **Example 6.2 — the three-way separated sum `D₀ + D₁ + D₂`** over `{Λ} ∪ 0Δ₀ ∪
1Δ₁ ∪ 2Δ₂`,
under the standing assumption that no neighbourhood of any factor is empty. -/
def sum3 (V₀ : NeighborhoodSystem α) (V₁ : NeighborhoodSystem β) (V₂ : NeighborhoodSystem γ)
    (h₀ : ∀ X, V₀.mem X → X.Nonempty) (h₁ : ∀ Y, V₁.mem Y → Y.Nonempty)
    (h₂ : ∀ Z, V₂.mem Z → Z.Nonempty) : NeighborhoodSystem (Option (α ⊕ β ⊕ γ)) where
  mem W := W = master3 V₀ V₁ V₂ ∨ (∃ X, V₀.mem X ∧ W = j0 X)
    ∨ (∃ Y, V₁.mem Y ∧ W = j1 Y) ∨ (∃ Z, V₂.mem Z ∧ W = j2 Z)
  master := master3 V₀ V₁ V₂
  master_mem := Or.inl rfl
  sub_master := by
    rintro W (rfl | ⟨X, hX, rfl⟩ | ⟨Y, hY, rfl⟩ | ⟨Z, hZ, rfl⟩)
    · exact subset_rfl
    · exact j0_subset_master3 hX
    · exact j1_subset_master3 hY
    · exact j2_subset_master3 hZ
  inter_mem := by
    have hne : ∀ W, (W = master3 V₀ V₁ V₂ ∨ (∃ X, V₀.mem X ∧ W = j0 X)
        ∨ (∃ Y, V₁.mem Y ∧ W = j1 Y) ∨ (∃ Z, V₂.mem Z ∧ W = j2 Z)) →
        (W : Set (Option (α ⊕ β ⊕ γ))).Nonempty := by
      rintro W (rfl | ⟨X, hX, rfl⟩ | ⟨Y, hY, rfl⟩ | ⟨Z, hZ, rfl⟩)
      · exact ⟨none, none_mem_master3⟩
      · exact j0_nonempty (h₀ X hX)
      · exact j1_nonempty (h₁ Y hY)
      · exact j2_nonempty (h₂ Z hZ)
    rintro W W' Z hW hW' hZ hZsub
    rcases hW with rfl | ⟨X, hX, rfl⟩ | ⟨Y, hY, rfl⟩ | ⟨Zc, hZc, rfl⟩
    · rcases hW' with rfl | ⟨X', hX', rfl⟩ | ⟨Y', hY', rfl⟩ | ⟨Z', hZ', rfl⟩
      · rw [Set.inter_self]; exact Or.inl rfl
      · rw [master3_inter_j0 hX']; exact Or.inr (Or.inl ⟨X', hX', rfl⟩)
      · rw [master3_inter_j1 hY']; exact Or.inr (Or.inr (Or.inl ⟨Y', hY', rfl⟩))
      · rw [master3_inter_j2 hZ']; exact Or.inr (Or.inr (Or.inr ⟨Z', hZ', rfl⟩))
    · rcases hW' with rfl | ⟨X', hX', rfl⟩ | ⟨Y', hY', rfl⟩ | ⟨Z', hZ', rfl⟩
      · rw [Set.inter_comm, master3_inter_j0 hX]; exact Or.inr (Or.inl ⟨X, hX, rfl⟩)
      · rw [j0_inter_j0] at hZsub ⊢
        rcases hZ with rfl | ⟨Z0, hZ0, rfl⟩ | ⟨Z1, hZ1, rfl⟩ | ⟨Z2, hZ2, rfl⟩
        · exact absurd (hZsub none_mem_master3) (by simp)
        · exact Or.inr (Or.inl ⟨X ∩ X', V₀.inter_mem hX hX' hZ0 (j0_subset_j0.mp hZsub), rfl⟩)
        · obtain ⟨b, hb⟩ := h₁ Z1 hZ1; exact absurd (hZsub (t1_mem_j1.mpr hb)) (by simp)
        · obtain ⟨c, hc⟩ := h₂ Z2 hZ2; exact absurd (hZsub (t2_mem_j2.mpr hc)) (by simp)
      · rw [j0_inter_j1] at hZsub ⊢
        obtain ⟨t, ht⟩ := hne Z hZ; exact absurd (hZsub ht) (Set.notMem_empty t)
      · rw [j0_inter_j2] at hZsub ⊢
        obtain ⟨t, ht⟩ := hne Z hZ; exact absurd (hZsub ht) (Set.notMem_empty t)
    · rcases hW' with rfl | ⟨X', hX', rfl⟩ | ⟨Y', hY', rfl⟩ | ⟨Z', hZ', rfl⟩
      · rw [Set.inter_comm, master3_inter_j1 hY]; exact Or.inr (Or.inr (Or.inl ⟨Y, hY, rfl⟩))
      · rw [Set.inter_comm, j0_inter_j1] at hZsub ⊢
        obtain ⟨t, ht⟩ := hne Z hZ; exact absurd (hZsub ht) (Set.notMem_empty t)
      · rw [j1_inter_j1] at hZsub ⊢
        rcases hZ with rfl | ⟨Z0, hZ0, rfl⟩ | ⟨Z1, hZ1, rfl⟩ | ⟨Z2, hZ2, rfl⟩
        · exact absurd (hZsub none_mem_master3) (by simp)
        · obtain ⟨a, ha⟩ := h₀ Z0 hZ0; exact absurd (hZsub (t0_mem_j0.mpr ha)) (by simp)
        · exact Or.inr (Or.inr (Or.inl ⟨Y ∩ Y',
          V₁.inter_mem hY hY' hZ1 (j1_subset_j1.mp hZsub), rfl⟩))
        · obtain ⟨c, hc⟩ := h₂ Z2 hZ2; exact absurd (hZsub (t2_mem_j2.mpr hc)) (by simp)
      · rw [j1_inter_j2] at hZsub ⊢
        obtain ⟨t, ht⟩ := hne Z hZ; exact absurd (hZsub ht) (Set.notMem_empty t)
    · rcases hW' with rfl | ⟨X', hX', rfl⟩ | ⟨Y', hY', rfl⟩ | ⟨Z', hZ', rfl⟩
      · rw [Set.inter_comm, master3_inter_j2 hZc]; exact Or.inr (Or.inr (Or.inr ⟨Zc, hZc, rfl⟩))
      · rw [Set.inter_comm, j0_inter_j2] at hZsub ⊢
        obtain ⟨t, ht⟩ := hne Z hZ; exact absurd (hZsub ht) (Set.notMem_empty t)
      · rw [Set.inter_comm, j1_inter_j2] at hZsub ⊢
        obtain ⟨t, ht⟩ := hne Z hZ; exact absurd (hZsub ht) (Set.notMem_empty t)
      · rw [j2_inter_j2] at hZsub ⊢
        rcases hZ with rfl | ⟨Z0, hZ0, rfl⟩ | ⟨Z1, hZ1, rfl⟩ | ⟨Z2, hZ2, rfl⟩
        · exact absurd (hZsub none_mem_master3) (by simp)
        · obtain ⟨a, ha⟩ := h₀ Z0 hZ0; exact absurd (hZsub (t0_mem_j0.mpr ha)) (by simp)
        · obtain ⟨b, hb⟩ := h₁ Z1 hZ1; exact absurd (hZsub (t1_mem_j1.mpr hb)) (by simp)
        · exact Or.inr (Or.inr (Or.inr ⟨Zc ∩ Z',
          V₂.inter_mem hZc hZ' hZ2 (j2_subset_j2.mp hZsub), rfl⟩))

/-! ## The domain equation `C ≅ 𝟙 + C + C`. -/

namespace Example62C

/-- `𝟙` is positive: its single neighbourhood `univ` (over the inhabited `Unit`)
is nonempty. -/
theorem unitSys_nonempty : ∀ X, unitSys.mem X → X.Nonempty := by
  rintro X rfl; exact Set.univ_nonempty

/-- Scott's standing assumption `∅ ∉ C`: every neighbourhood of `C` is nonempty. -/
theorem C_nonempty : ∀ X, C.mem X → X.Nonempty := by
  rintro X (⟨σ, rfl⟩ | ⟨σ, rfl⟩)
  · exact ⟨σ, List.prefix_rfl⟩
  · exact ⟨σ, rfl⟩

/-- `b{σ} = {bσ}`: prepending a bit to a singleton. -/
theorem embBit_singleton (b : Bool) (σ : Str) : embBit b ({σ} : Set Str) = {(b :: σ : Str)} := by
  rw [embBit_eq_prepend, Example44.prepend_singleton]; rfl

/-- Prepending a bit lands back in `C`. -/
theorem memC_embBit (b : Bool) {X : Set Str} (hX : C.mem X) : C.mem (embBit b X) := by
  rw [embBit_eq_prepend]; exact Example44.memC_prepend [b] hX

/-- **Example 6.2 — the shape of a `C`-neighbourhood.** Every neighbourhood of `C`
is the master
`Σ* = cone []`, the terminator `{Λ} = {[]}`, a `0`-copy `0X` with `X ∈ C`, or a
`1`-copy `1X`. -/
theorem memC_cases {W : Set Str} (hW : C.mem W) :
    W = Set.univ ∨ W = ({[]} : Set Str)
      ∨ (∃ X, C.mem X ∧ W = embBit false X) ∨ (∃ Y, C.mem Y ∧ W = embBit true Y) := by
  rcases hW with ⟨σ, rfl⟩ | ⟨σ, rfl⟩
  · cases σ with
    | nil => exact Or.inl cone_nil
    | cons b σ' => cases b with
      | false =>
        exact Or.inr (Or.inr (Or.inl ⟨cone σ', memC_cone σ', (embBit_cone false σ').symm⟩))
      | true =>
        exact Or.inr (Or.inr (Or.inr ⟨cone σ', memC_cone σ', (embBit_cone true σ').symm⟩))
  · cases σ with
    | nil => exact Or.inr (Or.inl rfl)
    | cons b σ' => cases b with
      | false =>
        exact Or.inr (Or.inr (Or.inl ⟨{σ'}, memC_singleton σ', (embBit_singleton false σ').symm⟩))
      | true =>
        exact Or.inr (Or.inr (Or.inr ⟨{σ'}, memC_singleton σ', (embBit_singleton true σ').symm⟩))

/-- If `bW ∈ C` then `W ∈ C`. -/
theorem memC_embBit_inv {b : Bool} {W : Set Str} (h : C.mem (embBit b W)) : C.mem W := by
  rcases h with ⟨σ, hσ⟩ | ⟨σ, hσ⟩
  · have hmem : σ ∈ embBit b W := hσ ▸ (show σ ∈ cone σ from List.prefix_rfl)
    obtain ⟨w', rfl, -⟩ := hmem
    rw [← embBit_cone] at hσ; rw [embBit_injective hσ]; exact memC_cone w'
  · have hmem : σ ∈ embBit b W := hσ ▸ (Set.mem_singleton_iff.mpr rfl : σ ∈ ({σ} : Set Str))
    obtain ⟨w', rfl, -⟩ := hmem
    rw [← embBit_singleton] at hσ; rw [embBit_injective hσ]; exact memC_singleton w'

theorem singleton_nil_inter_embBit (b : Bool) (X : Set Str) :
    (({[]} : Set Str) ∩ embBit b X) = ∅ := by
  ext w
  simp only [Set.mem_inter_iff, Set.mem_singleton_iff, mem_embBit, Set.mem_empty_iff_false,
    iff_false, not_and]
  rintro rfl ⟨w', heq, -⟩
  exact absurd heq (by simp)

theorem singleton_nil_ne_univ : ({[]} : Set Str) ≠ Set.univ := by
  intro h
  have hmem : ([true] : Str) ∈ ({[]} : Set Str) := h ▸ Set.mem_univ _
  rw [Set.mem_singleton_iff] at hmem; exact absurd hmem (by simp)

theorem singleton_nil_ne_embBit (b : Bool) (X : Set Str) : ({[]} : Set Str) ≠ embBit b X := by
  intro h
  exact nil_not_mem_embBit (h ▸ (Set.mem_singleton_iff.mpr rfl : ([] : Str) ∈ ({[]} : Set Str)))

/-- The right-hand side of the domain equation: the three-way sum `𝟙 + C + C`. -/
abbrev CC : NeighborhoodSystem (Option (Unit ⊕ Str ⊕ Str)) :=
  sum3 unitSys C C unitSys_nonempty C_nonempty C_nonempty

theorem sum3_mem_j1_inv {X : Set Str} (h : CC.mem (j1 X)) : C.mem X := by
  rcases h with h0 | ⟨U, hU, heq⟩ | ⟨Y, hY, heq⟩ | ⟨Z, hZ, heq⟩
  · exact absurd (h0 ▸ none_mem_master3) none_not_mem_j1
  · obtain ⟨a, ha⟩ := unitSys_nonempty U hU; exact absurd (heq ▸ (t0_mem_j0.mpr ha)) t0_not_mem_j1
  · rw [j1_injective heq]; exact hY
  · obtain ⟨c, hc⟩ := C_nonempty Z hZ; exact absurd (heq ▸ (t2_mem_j2.mpr hc)) t2_not_mem_j1

theorem sum3_mem_j2_inv {Y : Set Str} (h : CC.mem (j2 Y)) : C.mem Y := by
  rcases h with h0 | ⟨U, hU, heq⟩ | ⟨Z, hZ, heq⟩ | ⟨Y', hY', heq⟩
  · exact absurd (h0 ▸ none_mem_master3) none_not_mem_j2
  · obtain ⟨a, ha⟩ := unitSys_nonempty U hU; exact absurd (heq ▸ (t0_mem_j0.mpr ha)) t0_not_mem_j2
  · obtain ⟨c, hc⟩ := C_nonempty Z hZ; exact absurd (heq ▸ (t1_mem_j1.mpr hc)) t1_not_mem_j2
  · rw [j2_injective heq]; exact hY'

theorem sum3_mem_nonempty {W : Set (Option (Unit ⊕ Str ⊕ Str))} (h : CC.mem W) : W.Nonempty := by
  rcases h with rfl | ⟨U, hU, rfl⟩ | ⟨Y, hY, rfl⟩ | ⟨Z, hZ, rfl⟩
  · exact ⟨none, none_mem_master3⟩
  · exact j0_nonempty (unitSys_nonempty U hU)
  · exact j1_nonempty (C_nonempty Y hY)
  · exact j2_nonempty (C_nonempty Z hZ)

/-! ### The forward half `toCC : |C| → |𝟙 + C + C|`. -/

/-- **Example 6.2 — forward half of `C ≅ 𝟙 + C + C`.** -/
def toCC (x : C.Element) : CC.Element where
  mem W := W = master3 unitSys C C
    ∨ (W = j0 (Set.univ : Set Unit) ∧ x.mem ({[]} : Set Str))
    ∨ (∃ X, C.mem X ∧ W = j1 X ∧ x.mem (embBit false X))
    ∨ (∃ Y, C.mem Y ∧ W = j2 Y ∧ x.mem (embBit true Y))
  sub := by
    rintro W (rfl | ⟨rfl, -⟩ | ⟨X, hX, rfl, -⟩ | ⟨Y, hY, rfl, -⟩)
    · exact Or.inl rfl
    · exact Or.inr (Or.inl ⟨Set.univ, rfl, rfl⟩)
    · exact Or.inr (Or.inr (Or.inl ⟨X, hX, rfl⟩))
    · exact Or.inr (Or.inr (Or.inr ⟨Y, hY, rfl⟩))
  master_mem := Or.inl rfl
  inter_mem := by
    rintro W W' (rfl | ⟨rfl, hzU⟩ | ⟨X, hX, rfl, hzF⟩ | ⟨Y, hY, rfl, hzT⟩)
      (rfl | ⟨rfl, hzU'⟩ | ⟨X', hX', rfl, hzF'⟩ | ⟨Y', hY', rfl, hzT'⟩)
    · exact Or.inl (by rw [Set.inter_self])
    · exact Or.inr (Or.inl ⟨master3_inter_j0 rfl, hzU'⟩)
    · exact Or.inr (Or.inr (Or.inl ⟨X', hX', master3_inter_j1 hX', hzF'⟩))
    · exact Or.inr (Or.inr (Or.inr ⟨Y', hY', master3_inter_j2 hY', hzT'⟩))
    · exact Or.inr (Or.inl ⟨by rw [Set.inter_comm, master3_inter_j0 rfl], hzU⟩)
    · refine Or.inr (Or.inl ⟨?_, hzU⟩)
      rw [j0_inter_j0, Set.inter_self]
    · exfalso
      have hx := x.inter_mem hzU hzF'
      rw [singleton_nil_inter_embBit] at hx
      obtain ⟨t, ht⟩ := C_nonempty _ (x.sub hx); exact Set.notMem_empty t ht
    · exfalso
      have hx := x.inter_mem hzU hzT'
      rw [singleton_nil_inter_embBit] at hx
      obtain ⟨t, ht⟩ := C_nonempty _ (x.sub hx); exact Set.notMem_empty t ht
    · exact Or.inr (Or.inr (Or.inl ⟨X, hX, by rw [Set.inter_comm, master3_inter_j1 hX], hzF⟩))
    · exfalso
      have hx := x.inter_mem hzF hzU'
      rw [Set.inter_comm, singleton_nil_inter_embBit] at hx
      obtain ⟨t, ht⟩ := C_nonempty _ (x.sub hx); exact Set.notMem_empty t ht
    · refine Or.inr (Or.inr (Or.inl ⟨X ∩ X', ?_, j1_inter_j1 X X', ?_⟩))
      · have hx := x.inter_mem hzF hzF'; rw [embBit_inter] at hx; exact memC_embBit_inv (x.sub hx)
      · have hx := x.inter_mem hzF hzF'; rwa [embBit_inter] at hx
    · exfalso
      have hx := x.inter_mem hzF hzT'
      rw [embBit_inter_ne (show (false : Bool) ≠ true by decide)] at hx
      obtain ⟨t, ht⟩ := C_nonempty _ (x.sub hx); exact Set.notMem_empty t ht
    · exact Or.inr (Or.inr (Or.inr ⟨Y, hY, by rw [Set.inter_comm, master3_inter_j2 hY], hzT⟩))
    · exfalso
      have hx := x.inter_mem hzT hzU'
      rw [Set.inter_comm, singleton_nil_inter_embBit] at hx
      obtain ⟨t, ht⟩ := C_nonempty _ (x.sub hx); exact Set.notMem_empty t ht
    · exfalso
      have hx := x.inter_mem hzT hzF'
      rw [embBit_inter_ne (show (true : Bool) ≠ false by decide)] at hx
      obtain ⟨t, ht⟩ := C_nonempty _ (x.sub hx); exact Set.notMem_empty t ht
    · refine Or.inr (Or.inr (Or.inr ⟨Y ∩ Y', ?_, j2_inter_j2 Y Y', ?_⟩))
      · have hx := x.inter_mem hzT hzT'; rw [embBit_inter] at hx; exact memC_embBit_inv (x.sub hx)
      · have hx := x.inter_mem hzT hzT'; rwa [embBit_inter] at hx
  up_mem := by
    rintro W W' (rfl | ⟨rfl, hzU⟩ | ⟨X, hX, rfl, hzF⟩ | ⟨Y, hY, rfl, hzT⟩) hW' hsub
    · exact Or.inl (eq_master3_of_subset hsub (CC.sub_master hW'))
    · rcases hW' with rfl | ⟨X', hX', rfl⟩ | ⟨Y', hY', rfl⟩ | ⟨Z', hZ', rfl⟩
      · exact Or.inl rfl
      · obtain rfl := hX'; exact Or.inr (Or.inl ⟨rfl, hzU⟩)
      · exact absurd (hsub (t0_mem_j0.mpr (Set.mem_univ ()))) t0_not_mem_j1
      · exact absurd (hsub (t0_mem_j0.mpr (Set.mem_univ ()))) t0_not_mem_j2
    · rcases hW' with rfl | ⟨X', hX', rfl⟩ | ⟨Y', hY', rfl⟩ | ⟨Z', hZ', rfl⟩
      · exact Or.inl rfl
      · obtain ⟨b, hb⟩ := C_nonempty X hX
        exact absurd (hsub (t1_mem_j1.mpr hb)) t1_not_mem_j0
      · refine Or.inr (Or.inr (Or.inl ⟨Y', hY', rfl, ?_⟩))
        exact x.up_mem hzF (memC_embBit false hY') (embBit_subset.mpr (j1_subset_j1.mp hsub))
      · obtain ⟨b, hb⟩ := C_nonempty X hX
        exact absurd (hsub (t1_mem_j1.mpr hb)) t1_not_mem_j2
    · rcases hW' with rfl | ⟨X', hX', rfl⟩ | ⟨Y', hY', rfl⟩ | ⟨Z', hZ', rfl⟩
      · exact Or.inl rfl
      · obtain ⟨c, hc⟩ := C_nonempty Y hY
        exact absurd (hsub (t2_mem_j2.mpr hc)) t2_not_mem_j0
      · obtain ⟨c, hc⟩ := C_nonempty Y hY
        exact absurd (hsub (t2_mem_j2.mpr hc)) t2_not_mem_j1
      · refine Or.inr (Or.inr (Or.inr ⟨Z', hZ', rfl, ?_⟩))
        exact x.up_mem hzT (memC_embBit true hZ') (embBit_subset.mpr (j2_subset_j2.mp hsub))

@[simp] theorem toCC_mem_j0 {x : C.Element} :
    (toCC x).mem (j0 (Set.univ : Set Unit)) ↔ x.mem ({[]} : Set Str) := by
  constructor
  · rintro (h0 | ⟨-, hz⟩ | ⟨X', hX', heq, hz⟩ | ⟨Y', hY', heq, hz⟩)
    · exact absurd (h0 ▸ none_mem_master3) none_not_mem_j0
    · exact hz
    · exact absurd (heq ▸ (t0_mem_j0.mpr (Set.mem_univ ()))) t0_not_mem_j1
    · exact absurd (heq ▸ (t0_mem_j0.mpr (Set.mem_univ ()))) t0_not_mem_j2
  · intro hz; exact Or.inr (Or.inl ⟨rfl, hz⟩)

theorem toCC_mem_j1 {x : C.Element} {X : Set Str} (hX : C.mem X) :
    (toCC x).mem (j1 X) ↔ x.mem (embBit false X) := by
  constructor
  · rintro (h0 | ⟨heq, hz⟩ | ⟨X', hX', heqj, hz⟩ | ⟨Y', hY', heqj, hz⟩)
    · exact absurd (h0 ▸ none_mem_master3) none_not_mem_j1
    · obtain ⟨b, hb⟩ := C_nonempty X hX
      exact absurd (heq ▸ (t1_mem_j1.mpr hb)) t1_not_mem_j0
    · rw [j1_injective heqj]; exact hz
    · obtain ⟨b, hb⟩ := C_nonempty X hX
      exact absurd (heqj ▸ (t1_mem_j1.mpr hb)) t1_not_mem_j2
  · intro hz; exact Or.inr (Or.inr (Or.inl ⟨X, hX, rfl, hz⟩))

theorem toCC_mem_j2 {x : C.Element} {Y : Set Str} (hY : C.mem Y) :
    (toCC x).mem (j2 Y) ↔ x.mem (embBit true Y) := by
  constructor
  · rintro (h0 | ⟨heq, hz⟩ | ⟨X', hX', heqj, hz⟩ | ⟨Y', hY', heqj, hz⟩)
    · exact absurd (h0 ▸ none_mem_master3) none_not_mem_j2
    · obtain ⟨c, hc⟩ := C_nonempty Y hY
      exact absurd (heq ▸ (t2_mem_j2.mpr hc)) t2_not_mem_j0
    · obtain ⟨c, hc⟩ := C_nonempty Y hY
      exact absurd (heqj ▸ (t2_mem_j2.mpr hc)) t2_not_mem_j1
    · rw [j2_injective heqj]; exact hz
  · intro hz; exact Or.inr (Or.inr (Or.inr ⟨Y, hY, rfl, hz⟩))

/-! ### The inverse half `fromCC : |𝟙 + C + C| → |C|`. -/

/-- **Example 6.2 — inverse half of `C ≅ 𝟙 + C + C`.** -/
def fromCC (s : CC.Element) : C.Element where
  mem W := W = Set.univ
    ∨ (W = ({[]} : Set Str) ∧ s.mem (j0 (Set.univ : Set Unit)))
    ∨ (∃ X, C.mem X ∧ W = embBit false X ∧ s.mem (j1 X))
    ∨ (∃ Y, C.mem Y ∧ W = embBit true Y ∧ s.mem (j2 Y))
  sub := by
    rintro W (rfl | ⟨rfl, -⟩ | ⟨X, hX, rfl, -⟩ | ⟨Y, hY, rfl, -⟩)
    · exact Or.inl ⟨[], cone_nil.symm⟩
    · exact memC_singleton []
    · exact memC_embBit false hX
    · exact memC_embBit true hY
  master_mem := Or.inl rfl
  inter_mem := by
    rintro W W' (rfl | ⟨rfl, hsU⟩ | ⟨X, hX, rfl, hsF⟩ | ⟨Y, hY, rfl, hsT⟩)
      (rfl | ⟨rfl, hsU'⟩ | ⟨X', hX', rfl, hsF'⟩ | ⟨Y', hY', rfl, hsT'⟩)
    · exact Or.inl (by rw [Set.inter_self])
    · exact Or.inr (Or.inl ⟨by rw [Set.univ_inter], hsU'⟩)
    · exact Or.inr (Or.inr (Or.inl ⟨X', hX', by rw [Set.univ_inter], hsF'⟩))
    · exact Or.inr (Or.inr (Or.inr ⟨Y', hY', by rw [Set.univ_inter], hsT'⟩))
    · exact Or.inr (Or.inl ⟨by rw [Set.inter_univ], hsU⟩)
    · exact Or.inr (Or.inl ⟨by rw [Set.inter_self], hsU⟩)
    · exfalso
      have hs := s.inter_mem hsU hsF'; rw [j0_inter_j1] at hs
      obtain ⟨t, ht⟩ := sum3_mem_nonempty (s.sub hs); exact Set.notMem_empty t ht
    · exfalso
      have hs := s.inter_mem hsU hsT'; rw [j0_inter_j2] at hs
      obtain ⟨t, ht⟩ := sum3_mem_nonempty (s.sub hs); exact Set.notMem_empty t ht
    · exact Or.inr (Or.inr (Or.inl ⟨X, hX, by rw [Set.inter_univ], hsF⟩))
    · exfalso
      have hs := s.inter_mem hsF hsU'; rw [Set.inter_comm, j0_inter_j1] at hs
      obtain ⟨t, ht⟩ := sum3_mem_nonempty (s.sub hs); exact Set.notMem_empty t ht
    · refine Or.inr (Or.inr (Or.inl ⟨X ∩ X', ?_, embBit_inter false X X', ?_⟩))
      · have hs := s.inter_mem hsF hsF'; rw [j1_inter_j1] at hs
        exact sum3_mem_j1_inv (s.sub hs)
      · have hs := s.inter_mem hsF hsF'; rw [j1_inter_j1] at hs; exact hs
    · exfalso
      have hs := s.inter_mem hsF hsT'; rw [j1_inter_j2] at hs
      obtain ⟨t, ht⟩ := sum3_mem_nonempty (s.sub hs); exact Set.notMem_empty t ht
    · exact Or.inr (Or.inr (Or.inr ⟨Y, hY, by rw [Set.inter_univ], hsT⟩))
    · exfalso
      have hs := s.inter_mem hsT hsU'; rw [Set.inter_comm, j0_inter_j2] at hs
      obtain ⟨t, ht⟩ := sum3_mem_nonempty (s.sub hs); exact Set.notMem_empty t ht
    · exfalso
      have hs := s.inter_mem hsT hsF'; rw [Set.inter_comm, j1_inter_j2] at hs
      obtain ⟨t, ht⟩ := sum3_mem_nonempty (s.sub hs); exact Set.notMem_empty t ht
    · refine Or.inr (Or.inr (Or.inr ⟨Y ∩ Y', ?_, embBit_inter true Y Y', ?_⟩))
      · have hs := s.inter_mem hsT hsT'; rw [j2_inter_j2] at hs
        exact sum3_mem_j2_inv (s.sub hs)
      · have hs := s.inter_mem hsT hsT'; rw [j2_inter_j2] at hs; exact hs
  up_mem := by
    rintro W W' (rfl | ⟨rfl, hsU⟩ | ⟨X, hX, rfl, hsF⟩ | ⟨Y, hY, rfl, hsT⟩) hW' hsub
    · exact Or.inl (Set.univ_subset_iff.mp hsub)
    · rcases memC_cases hW' with rfl | rfl | ⟨X', hX', rfl⟩ | ⟨Y', hY', rfl⟩
      · exact Or.inl rfl
      · exact Or.inr (Or.inl ⟨rfl, hsU⟩)
      · exact absurd (hsub (Set.mem_singleton_iff.mpr rfl)) nil_not_mem_embBit
      · exact absurd (hsub (Set.mem_singleton_iff.mpr rfl)) nil_not_mem_embBit
    · rcases memC_cases hW' with rfl | rfl | ⟨X', hX', rfl⟩ | ⟨Y', hY', rfl⟩
      · exact Or.inl rfl
      · exfalso
        obtain ⟨a, ha⟩ := C_nonempty X hX
        have hm := hsub (⟨a, rfl, ha⟩ : (false :: a) ∈ embBit false X)
        rw [Set.mem_singleton_iff] at hm; exact absurd hm (by simp)
      · refine Or.inr (Or.inr (Or.inl ⟨X', hX', rfl, ?_⟩))
        exact s.up_mem hsF (Or.inr (Or.inr (Or.inl ⟨X', hX', rfl⟩)))
          (j1_subset_j1.mpr (embBit_subset.mp hsub))
      · exfalso
        obtain ⟨a, ha⟩ := C_nonempty X hX
        obtain ⟨w', he, -⟩ := hsub (⟨a, rfl, ha⟩ : (false :: a) ∈ embBit false X)
        rw [List.cons.injEq] at he; exact absurd he.1 (by decide)
    · rcases memC_cases hW' with rfl | rfl | ⟨X', hX', rfl⟩ | ⟨Y', hY', rfl⟩
      · exact Or.inl rfl
      · exfalso
        obtain ⟨a, ha⟩ := C_nonempty Y hY
        have hm := hsub (⟨a, rfl, ha⟩ : (true :: a) ∈ embBit true Y)
        rw [Set.mem_singleton_iff] at hm; exact absurd hm (by simp)
      · exfalso
        obtain ⟨a, ha⟩ := C_nonempty Y hY
        obtain ⟨w', he, -⟩ := hsub (⟨a, rfl, ha⟩ : (true :: a) ∈ embBit true Y)
        rw [List.cons.injEq] at he; exact absurd he.1 (by decide)
      · refine Or.inr (Or.inr (Or.inr ⟨Y', hY', rfl, ?_⟩))
        exact s.up_mem hsT (Or.inr (Or.inr (Or.inr ⟨Y', hY', rfl⟩)))
          (j2_subset_j2.mpr (embBit_subset.mp hsub))

@[simp] theorem fromCC_mem_nil {s : CC.Element} :
    (fromCC s).mem ({[]} : Set Str) ↔ s.mem (j0 (Set.univ : Set Unit)) := by
  constructor
  · rintro (h0 | ⟨-, hs⟩ | ⟨X', hX', heq, hs⟩ | ⟨Y', hY', heq, hs⟩)
    · exact absurd h0 singleton_nil_ne_univ
    · exact hs
    · exact absurd heq (singleton_nil_ne_embBit false X')
    · exact absurd heq (singleton_nil_ne_embBit true Y')
  · intro hs; exact Or.inr (Or.inl ⟨rfl, hs⟩)

theorem fromCC_mem_embF {s : CC.Element} {X : Set Str} (hX : C.mem X) :
    (fromCC s).mem (embBit false X) ↔ s.mem (j1 X) := by
  constructor
  · rintro (h0 | ⟨heq, hs⟩ | ⟨X', hX', heqj, hs⟩ | ⟨Y', hY', heqj, hs⟩)
    · exact absurd h0 (embBit_ne_univ false X)
    · exact absurd heq.symm (singleton_nil_ne_embBit false X)
    · rw [embBit_injective heqj]; exact hs
    · exact absurd heqj (embBit_ne (show (false : Bool) ≠ true by decide) (C_nonempty X hX))
  · intro hs; exact Or.inr (Or.inr (Or.inl ⟨X, hX, rfl, hs⟩))

theorem fromCC_mem_embT {s : CC.Element} {Y : Set Str} (hY : C.mem Y) :
    (fromCC s).mem (embBit true Y) ↔ s.mem (j2 Y) := by
  constructor
  · rintro (h0 | ⟨heq, hs⟩ | ⟨X', hX', heqj, hs⟩ | ⟨Y', hY', heqj, hs⟩)
    · exact absurd h0 (embBit_ne_univ true Y)
    · exact absurd heq.symm (singleton_nil_ne_embBit true Y)
    · exact absurd heqj.symm (embBit_ne (show (false : Bool) ≠ true by decide) (C_nonempty X' hX'))
    · rw [embBit_injective heqj]; exact hs
  · intro hs; exact Or.inr (Or.inr (Or.inr ⟨Y, hY, rfl, hs⟩))

/-! ### The two halves are mutually inverse. -/

theorem fromCC_toCC (x : C.Element) : fromCC (toCC x) = x := by
  apply NeighborhoodSystem.Element.ext
  intro W
  constructor
  · rintro (rfl | ⟨rfl, hs⟩ | ⟨X, hX, rfl, hs⟩ | ⟨Y, hY, rfl, hs⟩)
    · exact x.master_mem
    · exact toCC_mem_j0.mp hs
    · exact (toCC_mem_j1 hX).mp hs
    · exact (toCC_mem_j2 hY).mp hs
  · intro hW
    rcases memC_cases (x.sub hW) with rfl | rfl | ⟨X, hX, rfl⟩ | ⟨Y, hY, rfl⟩
    · exact Or.inl rfl
    · exact Or.inr (Or.inl ⟨rfl, toCC_mem_j0.mpr hW⟩)
    · exact Or.inr (Or.inr (Or.inl ⟨X, hX, rfl, (toCC_mem_j1 hX).mpr hW⟩))
    · exact Or.inr (Or.inr (Or.inr ⟨Y, hY, rfl, (toCC_mem_j2 hY).mpr hW⟩))

theorem toCC_fromCC (s : CC.Element) : toCC (fromCC s) = s := by
  apply NeighborhoodSystem.Element.ext
  intro W
  constructor
  · rintro (rfl | ⟨rfl, hs⟩ | ⟨X, hX, rfl, hs⟩ | ⟨Y, hY, rfl, hs⟩)
    · exact s.master_mem
    · exact fromCC_mem_nil.mp hs
    · exact (fromCC_mem_embF hX).mp hs
    · exact (fromCC_mem_embT hY).mp hs
  · intro hW
    rcases s.sub hW with rfl | ⟨U, hU, rfl⟩ | ⟨X, hX, rfl⟩ | ⟨Y, hY, rfl⟩
    · exact Or.inl rfl
    · obtain rfl := hU
      exact Or.inr (Or.inl ⟨rfl, fromCC_mem_nil.mpr hW⟩)
    · exact Or.inr (Or.inr (Or.inl ⟨X, hX, rfl, (fromCC_mem_embF hX).mpr hW⟩))
    · exact Or.inr (Or.inr (Or.inr ⟨Y, hY, rfl, (fromCC_mem_embT hY).mpr hW⟩))

/-! ### The domain equation `C ≅ 𝟙 + C + C`. -/

/-- **Example 6.2 (Scott 1981, PRG-19) — the isomorphism `|C| ≃o |𝟙 + C + C|`.** -/
def ccEquiv : C.Element ≃o CC.Element where
  toFun := toCC
  invFun := fromCC
  left_inv := fromCC_toCC
  right_inv := toCC_fromCC
  map_rel_iff' := by
    intro x x'
    constructor
    · intro h W hW
      rcases memC_cases (x.sub hW) with rfl | rfl | ⟨A, hA, rfl⟩ | ⟨A, hA, rfl⟩
      · exact x'.master_mem
      · exact toCC_mem_j0.mp (h _ (Or.inr (Or.inl ⟨rfl, hW⟩)))
      · exact (toCC_mem_j1 hA).mp (h _ (Or.inr (Or.inr (Or.inl ⟨A, hA, rfl, hW⟩))))
      · exact (toCC_mem_j2 hA).mp (h _ (Or.inr (Or.inr (Or.inr ⟨A, hA, rfl, hW⟩))))
    · intro h W hW
      rcases hW with rfl | ⟨rfl, hz⟩ | ⟨X, hX, rfl, hz⟩ | ⟨Y, hY, rfl, hz⟩
      · exact Or.inl rfl
      · exact Or.inr (Or.inl ⟨rfl, h _ hz⟩)
      · exact Or.inr (Or.inr (Or.inl ⟨X, hX, rfl, h _ hz⟩))
      · exact Or.inr (Or.inr (Or.inr ⟨Y, hY, rfl, h _ hz⟩))

/-- **Example 6.2 (Scott 1981, PRG-19) — the domain equation `C ≅ {{Λ}} + C +
C`.** Scott's domain
`C` of finite-or-infinite binary sequences is, as a domain, isomorphic to the
three-way separated sum
`𝟙 + C + C`: a sequence is bottom, the finished empty sequence `Λ` (the `𝟙`
summand), or begins with
`0` or `1` (the two `C` summands). -/
theorem C_domain_equation :
    C ≅ᴰ sum3 unitSys C C unitSys_nonempty C_nonempty C_nonempty :=
  ⟨ccEquiv⟩

end Example62C

end Domain.Neighborhood
