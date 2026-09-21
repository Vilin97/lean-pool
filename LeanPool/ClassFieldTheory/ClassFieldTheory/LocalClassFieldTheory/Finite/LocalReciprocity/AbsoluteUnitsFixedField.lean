/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/

import LeanPool.ClassFieldTheory.ValuedFieldTheory.Ramification.GaloisValuation.ClosedFixingSubgroup
import LeanPool.ClassFieldTheory.GaloisCohomology.Kummer.Abstract.KummerDelta
import Mathlib.RepresentationTheory.Rep.Basic

/-! # Absolute Units Fixed Field -/
namespace LocalClassFieldTheory

open RamificationTheory KummerTheory CyclicCohomology

/-!
# Finite local reciprocity: Galois units and fixed fields

For local reciprocity the coefficient module in the abstract class formation is
`A = (K^sep)ˣ`.  This file identifies its subgroup fixed by the actual closed
fixing subgroup of an intermediate field `E` with the image of `Eˣ`.

The result is stated for an arbitrary Galois ambient extension.  In particular
it applies to `SeparableClosure K / K` for every field `K`; no perfectness,
local-field, or finite-dimensional hypothesis is needed.  Using the separable
closure is essential in positive characteristic: the fixed field of
`Aut(K^alg/K)` inside `K^alg` need not be `K` when `K` is imperfect.
-/

noncomputable section

variable (K Ω : Type) [Field K] [Field Ω] [Algebra K Ω]

/-- The actual Galois representation on `Ωˣ`, written additively for the
group-cohomology API. -/
abbrev galoisAmbientUnitsRep : Rep ℤ (Gal(Ω / K)) :=
  Rep.ofAlgebraAutOnUnits K Ω

/-- Inclusion of the units of an intermediate field into the units of the
chosen Galois ambient field, in additive notation. -/
def intermediateFieldUnitsToGaloisAmbient
    (E : IntermediateField K Ω) :
    Additive Eˣ →+ Additive Ωˣ :=
  MonoidHom.toAdditive (Units.map E.val.toRingHom)

/-- States the theorem `intermediateFieldUnitsToGaloisAmbient_apply`. -/
@[simp]
theorem intermediateFieldUnitsToGaloisAmbient_apply
    (E : IntermediateField K Ω) (x : Eˣ) :
    intermediateFieldUnitsToGaloisAmbient K Ω E (Additive.ofMul x) =
      Additive.ofMul (Units.map E.val.toRingHom x) :=
  rfl

variable [IsGalois K Ω]

/-- An ambient unit is fixed by `Gal(Ω/E)` exactly when its underlying
field element belongs to `E`. -/
theorem mem_galoisAmbientUnits_fixed_iff
    (E : IntermediateField K Ω)
    (x : Additive Ωˣ) :
    x ∈ ambientFixedAddSubgroup (galoisAmbientUnitsRep K Ω)
        (closedFixingSubgroup K Ω E) ↔
      ((Additive.toMul x : Ωˣ) : Ω) ∈ E := by
  change
    (show galoisAmbientUnitsRep K Ω from x) ∈
        ambientFixedAddSubgroup (galoisAmbientUnitsRep K Ω)
          (closedFixingSubgroup K Ω E) ↔
      ((Additive.toMul x : Ωˣ) : Ω) ∈ E
  rw [mem_ambientFixedAddSubgroup_iff]
  constructor
  · intro hx
    rw [← InfiniteGalois.fixedField_fixingSubgroup E,
      IntermediateField.mem_fixedField_iff]
    intro σ hσ
    have hσclosed :
        σ ∈ (closedFixingSubgroup K Ω E).toSubgroup := by
      simpa only [closedFixingSubgroup] using hσ
    have hfixed := hx ⟨σ, hσclosed⟩
    have hρ :
        (Rep.ofAlgebraAutOnUnits K Ω).ρ σ x =
          Additive.ofMul
            (Units.mapEquiv σ.toMulEquiv (Additive.toMul x)) :=
      rfl
    rw [hρ] at hfixed
    have hval := congrArg
      (fun z : Additive Ωˣ ↦ ((Additive.toMul z : Ωˣ) : Ω)) hfixed
    convert hval using 1
    rfl
  · intro hx σ
    have hσE : σ.1 ∈ E.fixingSubgroup := by
      simpa only [closedFixingSubgroup] using σ.2
    have hρ :
        (Rep.ofAlgebraAutOnUnits K Ω).ρ
            (σ : Gal(Ω / K)) x =
          Additive.ofMul
            (Units.mapEquiv
              (σ : Gal(Ω / K)).toMulEquiv (Additive.toMul x)) :=
      rfl
    rw [hρ]
    apply Additive.ext
    rw [toMul_ofMul]
    apply Units.ext
    convert (IntermediateField.mem_fixingSubgroup_iff E σ.1).1 hσE _ hx using 1
    rfl

/-- The image of `Eˣ` in `Ωˣ` is precisely the abstract fixed
subgroup `A_E` used in the abstract class-formation framework. -/
theorem intermediateFieldUnitsToGaloisAmbient_range
    (E : IntermediateField K Ω) :
    (intermediateFieldUnitsToGaloisAmbient K Ω E).range =
      ambientFixedAddSubgroup (galoisAmbientUnitsRep K Ω)
        (closedFixingSubgroup K Ω E) := by
  apply AddSubgroup.ext
  intro x
  constructor
  · rintro ⟨y, rfl⟩
    change
      (show galoisAmbientUnitsRep K Ω from
        intermediateFieldUnitsToGaloisAmbient K Ω E y) ∈
        ambientFixedAddSubgroup (galoisAmbientUnitsRep K Ω)
          (closedFixingSubgroup K Ω E)
    apply (mem_galoisAmbientUnits_fixed_iff K Ω E _).2
    rw [← ofMul_toMul y, intermediateFieldUnitsToGaloisAmbient_apply,
      toMul_ofMul, Units.coe_map]
    exact (Additive.toMul y : Eˣ).1.property
  · intro hx
    have hxE :
        ((Additive.toMul x : Ωˣ) : Ω) ∈ E :=
      (mem_galoisAmbientUnits_fixed_iff K Ω E x).1 hx
    let y₀ : E :=
      ⟨((Additive.toMul x : Ωˣ) : Ω), hxE⟩
    have hy₀ : y₀ ≠ 0 := by
      intro h
      have h' :
          ((Additive.toMul x : Ωˣ) : Ω) = 0 :=
        congrArg E.val h
      exact (Additive.toMul x : Ωˣ).ne_zero h'
    let y : Eˣ := Units.mk0 y₀ hy₀
    refine ⟨Additive.ofMul y, ?_⟩
    rw [intermediateFieldUnitsToGaloisAmbient_apply]
    apply Additive.ext
    rw [toMul_ofMul]
    apply Units.ext
    rw [Units.coe_map]
    rfl

/-- Canonical additive equivalence `Eˣ ≃ A_E` for the actual ambient-unit
representation. -/
def intermediateFieldUnitsEquivGaloisFixed
    (E : IntermediateField K Ω) :
    Additive Eˣ ≃+ ambientFixedAddSubgroup (galoisAmbientUnitsRep K Ω)
      (closedFixingSubgroup K Ω E) := by
  let eRange : Additive Eˣ ≃+
      (intermediateFieldUnitsToGaloisAmbient K Ω E).range :=
    AddMonoidHom.ofInjective (by
      intro x y hxy
      apply Additive.toMul.injective
      exact (Units.map_injective E.val.injective) (congrArg Additive.toMul hxy))
  exact eRange.trans
    (AddEquiv.addSubgroupCongr
      (intermediateFieldUnitsToGaloisAmbient_range K Ω E))

/-- States the theorem `intermediateFieldUnitsEquivGaloisFixed_coe`. -/
@[simp]
theorem intermediateFieldUnitsEquivGaloisFixed_coe
    (E : IntermediateField K Ω) (x : Additive Eˣ) :
    (intermediateFieldUnitsEquivGaloisFixed K Ω E x).1 =
        intermediateFieldUnitsToGaloisAmbient K Ω E x :=
  rfl

/-- For an embedded extension `i : L → Ω`, the coefficient group fixed by
`Gal(Ω/i(L))` is canonically the actual unit group `Lˣ`.  This is the form
needed when an abstract finite extension is realized inside a separable
closure. -/
def embeddedFieldUnitsEquivGaloisFixed
    (L : Type) [Field L] [Algebra K L]
    (i : L →ₐ[K] Ω) :
    Additive Lˣ ≃+ ambientFixedAddSubgroup (galoisAmbientUnitsRep K Ω)
      (closedFixingSubgroup K Ω (AlgHom.fieldRange i)) :=
  (MulEquiv.toAdditive
    (Units.mapEquiv (AlgEquiv.ofInjectiveField i).toMulEquiv)).trans
      (intermediateFieldUnitsEquivGaloisFixed K Ω (AlgHom.fieldRange i))

/-- States the theorem `embeddedFieldUnitsEquivGaloisFixed_coe`. -/
@[simp]
theorem embeddedFieldUnitsEquivGaloisFixed_coe
    (L : Type) [Field L] [Algebra K L]
    (i : L →ₐ[K] Ω) (x : Lˣ) :
    (embeddedFieldUnitsEquivGaloisFixed K Ω L i (Additive.ofMul x)).1 =
      Additive.ofMul (Units.map i.toRingHom.toMonoidHom x) :=
  rfl

end
end LocalClassFieldTheory
