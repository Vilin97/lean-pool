/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/
module


public import Mathlib.RepresentationTheory.Invariants
public import Mathlib.FieldTheory.Galois.Basic
/-!
# Invariant units

The actual invariant submodule of the unit representation, together with its
arithmetic identification with the units of the base field.
-/

@[expose] public section

namespace CyclicCohomology

noncomputable section

/-- The actual invariant submodule of the unit representation `Lˣ` under `Gal(L/K)`. -/
def unitsInvariantSubmodule (K L : Type) [Field K] [Field L] [Algebra K L] :
    Submodule ℤ (Additive Lˣ) :=
  (Rep.ofAlgebraAutOnUnits K L).ρ.invariants

private noncomputable def invariantUnitToBaseUnit (K L : Type)
    [Field K] [Field L] [Algebra K L] [IsGalois K L] [FiniteDimensional K L]
    (x : unitsInvariantSubmodule K L) : Kˣ := by
  classical
  let y : Lˣ := Additive.toMul (x : Additive Lˣ)
  have hfixed : ∀ σ : Gal(L/K), σ (y : L) = (y : L) := by
    intro σ
    have h :=
      congrArg (fun z : Additive Lˣ => ((Additive.toMul z : Lˣ) : L)) (x.property σ)
    have hρ :
        (Rep.ofAlgebraAutOnUnits K L).ρ σ (x : Additive Lˣ) =
          Additive.ofMul
            (Units.mapEquiv σ.toMulEquiv (Additive.toMul (x : Additive Lˣ))) :=
      rfl
    rw [hρ] at h
    simpa [y] using h
  have hmem : (y : L) ∈ Set.range (algebraMap K L) :=
    (IsGalois.mem_range_algebraMap_iff_fixed (F := K) (E := L) (y : L)).2 hfixed
  let a : K := Classical.choose hmem
  have ha : algebraMap K L a = (y : L) := Classical.choose_spec hmem
  have ha0 : a ≠ 0 := by
    intro hzero
    exact y.ne_zero (by rw [← ha, hzero, map_zero])
  exact ⟨a, a⁻¹, by simp [ha0], by simp [ha0]⟩

private lemma invariantUnitToBaseUnit_spec (K L : Type)
    [Field K] [Field L] [Algebra K L] [IsGalois K L] [FiniteDimensional K L]
    (x : unitsInvariantSubmodule K L) :
    algebraMap K L (invariantUnitToBaseUnit K L x : K) =
      ((Additive.toMul (x : Additive Lˣ) : Lˣ) : L) := by
  classical
  let y : Lˣ := Additive.toMul (x : Additive Lˣ)
  have hfixed : ∀ σ : Gal(L/K), σ (y : L) = (y : L) := by
    intro σ
    have h :=
      congrArg (fun z : Additive Lˣ => ((Additive.toMul z : Lˣ) : L)) (x.property σ)
    have hρ :
        (Rep.ofAlgebraAutOnUnits K L).ρ σ (x : Additive Lˣ) =
          Additive.ofMul
            (Units.mapEquiv σ.toMulEquiv (Additive.toMul (x : Additive Lˣ))) :=
      rfl
    rw [hρ] at h
    simpa [y] using h
  have hmem : (y : L) ∈ Set.range (algebraMap K L) :=
    (IsGalois.mem_range_algebraMap_iff_fixed (F := K) (E := L) (y : L)).2 hfixed
  change algebraMap K L (Classical.choose hmem) = (y : L)
  exact Classical.choose_spec hmem

private noncomputable def baseUnitToInvariantUnit (K L : Type)
    [Field K] [Field L] [Algebra K L] (x : Kˣ) : unitsInvariantSubmodule K L where
  val := Additive.ofMul (Units.map (algebraMap K L).toMonoidHom x)
  property := by
    intro σ
    change
      Additive.ofMul
          (Units.mapEquiv σ.toMulEquiv (Units.map (algebraMap K L).toMonoidHom x)) =
        Additive.ofMul (Units.map (algebraMap K L).toMonoidHom x)
    apply Additive.ofMul.injective
    ext
    simp

private lemma invariantUnitToBaseUnit_baseUnitToInvariantUnit (K L : Type)
    [Field K] [Field L] [Algebra K L] [IsGalois K L] [FiniteDimensional K L]
    (x : Kˣ) :
    invariantUnitToBaseUnit K L (baseUnitToInvariantUnit K L x) = x := by
  ext
  apply FaithfulSMul.algebraMap_injective K L
  rw [invariantUnitToBaseUnit_spec]
  rfl

private lemma baseUnitToInvariantUnit_invariantUnitToBaseUnit (K L : Type)
    [Field K] [Field L] [Algebra K L] [IsGalois K L] [FiniteDimensional K L]
    (x : unitsInvariantSubmodule K L) :
    baseUnitToInvariantUnit K L (invariantUnitToBaseUnit K L x) = x := by
  apply Subtype.ext
  apply Additive.ofMul.injective
  ext
  exact invariantUnitToBaseUnit_spec K L x

/-- The canonical additive equivalence `(Lˣ)^Gal(L/K) ≃ Kˣ` for finite Galois extensions. -/
noncomputable def invariantsUnitsAddEquivBaseUnits (K L : Type)
    [Field K] [Field L] [Algebra K L] [IsGalois K L] [FiniteDimensional K L] :
    unitsInvariantSubmodule K L ≃+ Additive Kˣ where
  toFun := fun x => Additive.ofMul (invariantUnitToBaseUnit K L x)
  invFun := fun x => baseUnitToInvariantUnit K L (Additive.toMul x)
  left_inv := baseUnitToInvariantUnit_invariantUnitToBaseUnit K L
  right_inv := by
    intro x
    apply Additive.ofMul.injective
    exact invariantUnitToBaseUnit_baseUnitToInvariantUnit K L (Additive.toMul x)
  map_add' := by
    intro x y
    apply Additive.ofMul.injective
    change
      invariantUnitToBaseUnit K L (x + y) =
        invariantUnitToBaseUnit K L x * invariantUnitToBaseUnit K L y
    ext
    apply FaithfulSMul.algebraMap_injective K L
    change
      algebraMap K L (invariantUnitToBaseUnit K L (x + y) : K) =
        algebraMap K L
          ((invariantUnitToBaseUnit K L x : K) *
            (invariantUnitToBaseUnit K L y : K))
    rw [map_mul, invariantUnitToBaseUnit_spec,
      invariantUnitToBaseUnit_spec, invariantUnitToBaseUnit_spec]
    rfl

/-- The canonical linear equivalence `(Lˣ)^Gal(L/K) ≃ Kˣ` for finite Galois extensions. -/
noncomputable def invariantsUnitsEquivBaseUnits (K L : Type)
    [Field K] [Field L] [Algebra K L] [IsGalois K L] [FiniteDimensional K L] :
    unitsInvariantSubmodule K L ≃ₗ[ℤ] Additive Kˣ :=
  (invariantsUnitsAddEquivBaseUnits K L).toIntLinearEquiv

/-- Restricting an invariant unit and re-embedding its value recovers the
underlying extension-field unit. -/
lemma invariantsUnitsAddEquivBaseUnits_spec (K L : Type)
    [Field K] [Field L] [Algebra K L] [IsGalois K L] [FiniteDimensional K L]
    (x : unitsInvariantSubmodule K L) :
    algebraMap K L
        ((Additive.toMul (invariantsUnitsAddEquivBaseUnits K L x) : Kˣ) : K) =
      ((Additive.toMul (x : Additive Lˣ) : Lˣ) : L) := by
  exact invariantUnitToBaseUnit_spec K L x

end
end CyclicCohomology
