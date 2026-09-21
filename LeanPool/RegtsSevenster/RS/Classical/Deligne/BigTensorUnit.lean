/-
Copyright (c) 2026 William Whistler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Whistler
-/

import LeanPool.RegtsSevenster.RS.Classical.Deligne.BigTensor

/-!
# The unit of a big tensor product survives

If the tensor of two nonzero points is nonzero, then a finite
tensor product of algebras with nonvanishing units again has a
nonvanishing unit, by induction on the slots.  The unit of the
whole family is the unit of any finite stage followed by the
stage inclusion, so it survives as soon as the unit of the
ambient category can be tested against the filtered colimit one
stage at a time.
-/

namespace RS

open CategoryTheory MonoidalCategory Limits

local notation "η[" M "]" => MonObj.one (X := M)
local notation "μ[" M "]" => MonObj.mul (X := M)

universe v u

variable {D : Type u}

/-- **The unit of a finite fold survives**: the unit of a tensor
product of monoid objects is the tensor of their units, so it is
nonzero as soon as the binary statement holds. -/
theorem listTensor_one_ne_zero
    [Category.{v} D] [MonoidalCategory D] [BraidedCategory D]
    [Preadditive D] {ι : Type v} (B : ι → D) [∀ i, MonObj (B i)]
    (h1 : 𝟙 (𝟙_ D) ≠ 0)
    (hbin : ∀ {M N : D} (u : 𝟙_ D ⟶ M) (v : 𝟙_ D ⟶ N),
      u ≠ 0 → v ≠ 0 → (u ⊗ₘ v) ≠ 0)
    (hB : ∀ i, η[B i] ≠ 0) :
    ∀ l : List ι, η[listTensor B l] ≠ 0
  | [] => h1
  | i :: l => by
    have hstep : η[listTensor B (i :: l)] =
        (λ_ (𝟙_ D)).inv ≫ (η[B i] ⊗ₘ η[listTensor B l]) := rfl
    rw [hstep]
    intro h0
    refine hbin η[B i] η[listTensor B l] (hB i)
      (listTensor_one_ne_zero B h1 hbin hB l) ?_
    have hcomp := congrArg (fun t => (λ_ (𝟙_ D)).hom ≫ t) h0
    simp only [Iso.hom_inv_id_assoc] at hcomp
    rw [hcomp]
    exact Limits.comp_zero

/-- **The unit of a finite sub-tensor-product survives.** -/
theorem finTensor_one_ne_zero
    [Category.{v} D] [MonoidalCategory D] [BraidedCategory D]
    [Preadditive D] {ι : Type v} (B : ι → D) [∀ i, MonObj (B i)]
    [LinearOrder ι]
    (h1 : 𝟙 (𝟙_ D) ≠ 0)
    (hbin : ∀ {M N : D} (u : 𝟙_ D ⟶ M) (v : 𝟙_ D ⟶ N),
      u ≠ 0 → v ≠ 0 → (u ⊗ₘ v) ≠ 0)
    (hB : ∀ i, η[B i] ≠ 0) (s : Finset ι) :
    η[finTensor B s] ≠ 0 :=
  listTensor_one_ne_zero B h1 hbin hB (s.sort (· ≤ ·))

/-- **The unit of the big tensor product survives**, given that
a point of the colimit vanishes only if it already vanishes at a
later stage. -/
theorem bigTensorUnit_ne_zero
    [Category.{v} D] [MonoidalCategory D] [BraidedCategory D]
    [Preadditive D] {ι : Type v} (B : ι → D) [∀ i, MonObj (B i)]
    [LinearOrder ι] [HasColimitsOfShape (Finset ι) D]
    (h1 : 𝟙 (𝟙_ D) ≠ 0)
    (hbin : ∀ {M N : D} (u : 𝟙_ D ⟶ M) (v : 𝟙_ D ⟶ N),
      u ≠ 0 → v ≠ 0 → (u ⊗ₘ v) ≠ 0)
    (hB : ∀ i, η[B i] ≠ 0)
    (hstage : ∀ (s : Finset ι) (f : 𝟙_ D ⟶ finTensor B s),
      f ≫ bigTensorStage B s = 0 →
      ∃ (t : Finset ι) (h : s ⊆ t), f ≫ finTensorIncl B h = 0) :
    bigTensorUnit B ≠ 0 := by
  intro h0
  obtain ⟨t, h, ht⟩ := hstage ∅ η[finTensor B ∅]
    (by rw [bigTensorUnit_stage]; exact h0)
  refine finTensor_one_ne_zero B h1 hbin hB t ?_
  rw [← (isMonHom_finTensorIncl B h).one_hom]
  exact ht

end RS
