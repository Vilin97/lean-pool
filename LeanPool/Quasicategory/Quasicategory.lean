/-
Copyright (c) 2026 Jack McKoen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jack McKoen
-/
import LeanPool.Quasicategory.Basic
import LeanPool.Quasicategory.Monomorphism
import Mathlib.AlgebraicTopology.SimplicialSet.CategoryWithFibrations

open CategoryTheory Simplicial MorphismProperty

namespace SSet

/-- `01BB` S is a quasicategory iff S ⟶ Δ[0] is an inner fibration -/
lemma quasicategory_iff_from_innerFibration {S : SSet} :
    Quasicategory S ↔ innerFibration (isTerminalZero.from S) := by
  constructor
  · intro h _ _ p ⟨h0, hn⟩
    constructor
    intro f _ _
    obtain ⟨l, hl⟩ := h.hornFilling h0 hn f
    exact ⟨l, hl.symm, isTerminalZero.hom_ext _ _⟩
  · intro h
    constructor
    intro n i σ₀ h0 hn
    have := CommSq.mk (isTerminalZero.hom_ext
      (σ₀ ≫ isTerminalZero.from _) (Λ[n + 2, i].ι ≫ isTerminalZero.from _))
    have lift := ((h _ (.mk h0 hn)).sq_hasLift this).exists_lift.some
    exact ⟨lift.l, lift.fac_left.symm⟩

/-- `007E` quasicategory iff extension property wrt every inner anodyne morphism -/
lemma quasicategory_iff_from_innerAnodyne_rlp {S : SSet} :
    Quasicategory S ↔ innerAnodyne.rlp (isTerminalZero.from S) := by
  rw [quasicategory_iff_from_innerFibration, rlp_llp_rlp]

/-- `01BJ` if Y is a quasicategory and X ⟶ Y is an inner fibration, then X is a quasicategory -/
lemma quasicategory_of_innerFibration {X Y : SSet} (p : X ⟶ Y) (hp : innerFibration p) :
    Quasicategory Y → Quasicategory X := fun h ↦ by
  rw [quasicategory_iff_from_innerFibration] at h ⊢
  apply comp_mem _ p (isTerminalZero.from Y) hp h

/-- `050J` (3) --/
instance quasicategory_of_trivialFibration {X Y : SSet} (p : X ⟶ Y) (hp : trivialFibration p) :
    Quasicategory X → Quasicategory Y := by
  intro h
  constructor
  intro n i σ₀ h0 hn
  rw [trivialFibration_eq_rlp_monomorphisms] at hp
  have : (isInitialEmpty.to X) ≫ p = (isInitialEmpty.to Λ[n + 2, i]) ≫ σ₀ := isInitialEmpty.hom_ext _ _
  have τ₀ := ((hp _ (initial_mono Λ[n + 2, i] isInitialEmpty)).sq_hasLift (CommSq.mk (this))).exists_lift.some
  obtain ⟨τ, hτ⟩ := h.hornFilling h0 hn τ₀.l
  use τ ≫ p
  rw [← Category.assoc, ← hτ, τ₀.fac_right]

namespace modelCategoryQuillen

/-- `050J` (1) -/
instance kanComplex_of_trivialFibration {X Y : SSet}
    (p : X ⟶ Y) (hp : trivialFibration p) :
    KanComplex X → KanComplex Y := by
  intro hX
  dsimp [KanComplex]
  rw [HomotopicalAlgebra.isFibrant_iff Y, modelCategoryQuillen.fibration_iff] --no longer works because Kan complex definition is no longer simple to work with
  rw [trivialFibration_eq_rlp_monomorphisms] at hp
  intro _ _ _ h
  obtain ⟨_, ⟨h, hw⟩⟩ := h
  simp at h
  obtain ⟨n, _, h⟩ := h
  have := h hw
  rw [ofHoms_iff] at this
  obtain ⟨i, hi⟩ := this
  rw [Arrow.hasLiftingProperty_iff, hi, ← Arrow.hasLiftingProperty_iff]
  constructor
  intro σ₀ g sq
  have : (isInitialEmpty.to X) ≫ p = (isInitialEmpty.to Λ[n + 1, i].toSSet) ≫ σ₀ := isInitialEmpty.hom_ext _ _
  have τ₀ := ((hp _ (initial_mono Λ[n + 1, i] isInitialEmpty)).sq_hasLift (CommSq.mk this)).exists_lift.some
  obtain ⟨τ, hτ⟩ := hX.hornFilling τ₀.l
  constructor
  constructor
  exact ⟨τ ≫ p, by rw [← Category.assoc, ← hτ, τ₀.fac_right], Limits.terminal.hom_ext _ _⟩

end modelCategoryQuillen
