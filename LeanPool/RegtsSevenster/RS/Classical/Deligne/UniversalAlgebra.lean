/-
Copyright (c) 2026 William Whistler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Whistler
-/

import LeanPool.RegtsSevenster.RS.Classical.Deligne.CommonAlgebra
import LeanPool.RegtsSevenster.RS.Classical.Deligne.SplitTransport

/-!
# The universal algebra of Deligne 2.11

Choosing, for every object, an algebra over which it becomes a
mixed sum, and for every short exact sequence an algebra over
which it splits, and taking the tensor product of all of them,
gives a single nonzero algebra over which every object is a mixed
sum and every short exact sequence splits.
-/

namespace RS

open CategoryTheory MonoidalCategory Limits

universe v

variable {C : Type v}

/-- **The universal algebra**: one nonzero algebra over which
every object of the family becomes a mixed sum and every chosen
morphism acquires a section. -/
theorem exists_universal_algebra
    [SmallCategory C] [MonoidalCategory C] [Abelian C]
    [CategoryTheory.Linear ℂ C] [MonoidalPreadditive C] [MonoidalLinear ℂ C]
    [RigidCategory C] [SymmetricCategory (Ind C)] [HasCoequalizers (Ind C)]
    [∀ Z : Ind C, PreservesColimitsOfShape WalkingParallelPair (tensorLeft
      Z)] [HasFiniteBiproducts (Ind C)]
    (hu : HasScalarUnit C)
    (L : OddLine (Ind C)) {J K : Type v} (X : J → Ind C)
    (V W : K → Ind C) (g : ∀ k, V k ⟶ W k)
    (hmix : ∀ j, L.LocallyMixed (X j))
    (hsplit : ∀ k, ∃ (A : Ind C) (_ : MonObj A) (_ : IsCommMonObj A),
      MonObj.one (X := A) ≠ 0 ∧
      ∃ s : freeMod A (W k) ⟶ freeMod A (V k),
        s ≫ freeModMap A (g k) = 𝟙 (freeMod A (W k))) :
    ∃ (𝔸 : Ind C) (_ : MonObj 𝔸) (_ : IsCommMonObj 𝔸),
      MonObj.one (X := 𝔸) ≠ 0 ∧
      (∀ j, ∃ p q : ℕ,
        Nonempty (freeMod 𝔸 (X j) ≅ freeMod 𝔸 (L.mix p q))) ∧
      (∀ k, ∃ s : freeMod 𝔸 (W k) ⟶ freeMod 𝔸 (V k),
        s ≫ freeModMap 𝔸 (g k) = 𝟙 (freeMod 𝔸 (W k))) := by
  classical
  choose pm qm Am Amon Acomm Ane Aiso using hmix
  choose Bs Bmon Bcomm Bne Bsec using hsplit
  let : ∀ i : J ⊕ K, MonObj (Sum.elim Am Bs i) := fun i =>
    match i with
    | Sum.inl j => Amon j
    | Sum.inr k => Bmon k
  let : ∀ i : J ⊕ K, IsCommMonObj (Sum.elim Am Bs i) := fun i =>
    match i with
    | Sum.inl j => Acomm j
    | Sum.inr k => Bcomm k
  obtain ⟨𝔸, hmon, hcomm, hne, hmap⟩ :=
    exists_common_algebra hu (Sum.elim Am Bs)
      (fun i => match i with
        | Sum.inl j => Ane j
        | Sum.inr k => Bne k)
  refine ⟨𝔸, hmon, hcomm, hne, ?_, ?_⟩
  · intro j
    obtain ⟨φ, hφ⟩ := hmap (Sum.inl j)
    have : IsMonHom (show Am j ⟶ 𝔸 from φ) := hφ
    exact ⟨pm j, qm j,
      ⟨freeModIsoBaseChange (Am j) 𝔸 (show Am j ⟶ 𝔸 from φ)
        (Aiso j).some⟩⟩
  · intro k
    obtain ⟨φ, hφ⟩ := hmap (Sum.inr k)
    have : IsMonHom (show Bs k ⟶ 𝔸 from φ) := hφ
    obtain ⟨s, hs⟩ := Bsec k
    exact exists_section_baseChange (Bs k) 𝔸
      (show Bs k ⟶ 𝔸 from φ) (g k) s hs

end RS
