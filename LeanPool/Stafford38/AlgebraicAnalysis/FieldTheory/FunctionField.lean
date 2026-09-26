/-
Copyright (c) 2026 Christopher Albert. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Albert
-/

module

public import Mathlib.FieldTheory.IntermediateField.Adjoin.Algebra
public import Mathlib.RingTheory.FiniteType
public import Mathlib.RingTheory.Localization.FractionRing


/-!
# Finitely generated fraction fields

A fraction field of a finitely generated domain is finitely generated as a
field extension.  The conclusion uses `IntermediateField.FG`, rather than
finite type as an algebra: a transcendental fraction field is generally not
finitely generated as an algebra over its ground field.
-/

@[expose] public section

namespace AlgebraicAnalysis.FunctionField

noncomputable section

universe u v w

/-- The fraction field of a finitely generated domain is a finitely generated
field extension of the ground field. -/
theorem top_fg_of_finiteType_fractionRing
    (k : Type u) (A : Type v) (K : Type w)
    [Field k] [CommRing A] [Algebra k A]
    [Field K] [Algebra A K] [IsFractionRing A K]
    [Algebra k K] [IsScalarTower k A K]
    [Algebra.FiniteType k A] :
    (⊤ : IntermediateField k K).FG := by
  classical
  obtain ⟨s, hs⟩ := (Algebra.FiniteType.out (R := k) (A := A))
  let f : A →ₐ[k] K := IsScalarTower.toAlgHom k A K
  let fi : A ↪ K :=
    ⟨f, IsFractionRing.injective A K⟩
  let T : IntermediateField k K :=
    IntermediateField.adjoin k (f '' (s : Set A))
  have hmap : ∀ a : A, f a ∈ T := by
    intro a
    have ha : a ∈ Algebra.adjoin k (s : Set A) := by
      rw [hs]
      trivial
    refine Algebra.adjoin_induction
      (p := fun a _ ↦ f a ∈ T) ?_ ?_ ?_ ?_ ha
    · intro x hx
      exact IntermediateField.subset_adjoin k _ ⟨x, hx, rfl⟩
    · intro x
      simp [f]
    · intro x y _ _ hx hy
      simpa using T.add_mem hx hy
    · intro x y _ _ hx hy
      simpa using T.mul_mem hx hy
  have htop : T = ⊤ := by
    rw [eq_top_iff]
    intro z _
    obtain ⟨a, b, hb, hab⟩ := IsFractionRing.div_surjective (A := A) z
    rw [← hab]
    exact T.div_mem (hmap a) (hmap b)
  refine ⟨s.map fi, ?_⟩
  simpa [T, fi, f, Finset.coe_map] using htop


end

end AlgebraicAnalysis.FunctionField
