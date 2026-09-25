/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/
module


public import LeanPool.ClassFieldTheory.ValuedFieldTheory.LocalField.DiscreteValuationField.RamificationIdeal
public import LeanPool.ClassFieldTheory.ValuedFieldTheory.Valuation.DiscreteValuationField.AddVal
/-!
# Additive valuations in finite complete-DVF extensions

The normalized additive valuation on the target valuation ring restricts to
the ramification index times the normalized additive valuation on the base
valuation ring.  The proof is characteristic-independent and follows from the
ideal identity
`m_K · O_L = m_L ^ e`.
-/

@[expose] public section

noncomputable
section

universe u v w x

namespace LocalFieldTheory.DiscreteValuationField
open ValuationTheory.DiscreteValuationField
namespace ValuedExtension
open ValuationTheory.DiscreteValuationField.ValuedExtension

variable {K : Type u} {L : Type w} [Field K] [Field L]
variable [Algebra K L]
variable (base : CompleteDVF.{u, v} K) (target : CompleteDVF.{w, x} L)
variable [base.valuation.HasExtension target.valuation]

/-- The target normalized additive valuation of an element from the base
valuation ring is its base additive valuation multiplied by the ramification
index.  This includes the zero element, whose additive valuation is `⊤`. -/
theorem addVal_integerMap_eq_ramificationIndex_nsmul
    (a : base.valuationSubring) :
    IsDiscreteValuationRing.addVal target.valuationSubring
        (integerMap base.toDVF target.toDVF a) =
      ramificationIndex base.toDVF target.toDVF •
        IsDiscreteValuationRing.addVal base.valuationSubring a := by
  let e := ramificationIndex base.toDVF target.toDVF
  have he_ne : e ≠ 0 := by
    intro he
    have hle :=
      maximalIdeal_map_integerMap_le base.toDVF target.toDVF
    have hmap :=
      maximalIdeal_map_eq_target_maximalIdeal_pow_ramificationIndex
        base target
    rw [show ramificationIndex base.toDVF target.toDVF = e from rfl,
      he, pow_zero] at hmap
    rw [hmap] at hle
    have hle_top :
        (⊤ : Ideal target.valuationSubring) ≤
          IsLocalRing.maximalIdeal target.valuationSubring := by
      simpa only [Ideal.one_eq_top] using hle
    exact
      (IsLocalRing.maximalIdeal.isMaximal
        target.valuationSubring).ne_top (top_unique hle_top)
  by_cases ha : a = 0
  · subst a
    have he_coe_ne : (e : ℕ∞) ≠ 0 := by
      exact_mod_cast he_ne
    rw [map_zero, IsDiscreteValuationRing.addVal_zero,
      IsDiscreteValuationRing.addVal_zero, nsmul_eq_mul,
      ENat.mul_top he_coe_ne]
  obtain ⟨pi, hpi⟩ :=
    IsDiscreteValuationRing.exists_irreducible base.valuationSubring
  obtain ⟨varpi, hvarpi⟩ :=
    IsDiscreteValuationRing.exists_irreducible target.valuationSubring
  obtain ⟨m, unit, ha_decomp⟩ :=
    IsDiscreteValuationRing.eq_unit_mul_pow_irreducible ha hpi
  have hspan :
      Ideal.span
          ({integerMap base.toDVF target.toDVF pi} :
            Set target.valuationSubring) =
        Ideal.span ({varpi ^ e} : Set target.valuationSubring) := by
    calc
      Ideal.span
          ({integerMap base.toDVF target.toDVF pi} :
            Set target.valuationSubring) =
          Ideal.map (integerMap base.toDVF target.toDVF)
            (Ideal.span ({pi} : Set base.valuationSubring)) := by
              rw [Ideal.map_span, Set.image_singleton]
      _ = Ideal.map (integerMap base.toDVF target.toDVF)
          base.maximalIdeal := by
            rw [show base.maximalIdeal =
                IsLocalRing.maximalIdeal base.valuationSubring from rfl,
              hpi.maximalIdeal_eq]
      _ = target.maximalIdeal ^ e := by
            exact
              maximalIdeal_map_eq_target_maximalIdeal_pow_ramificationIndex
                base target
      _ = Ideal.span ({varpi ^ e} : Set target.valuationSubring) := by
            rw [show target.maximalIdeal =
                IsLocalRing.maximalIdeal target.valuationSubring from rfl,
              hvarpi.maximalIdeal_eq, Ideal.span_singleton_pow]
  have hmap_uniformizer :
      IsDiscreteValuationRing.addVal target.valuationSubring
          (integerMap base.toDVF target.toDVF pi) =
        (e : ℕ∞) := by
    calc
      IsDiscreteValuationRing.addVal target.valuationSubring
          (integerMap base.toDVF target.toDVF pi) =
          IsDiscreteValuationRing.addVal target.valuationSubring
            (varpi ^ e) :=
        (IsDiscreteValuationRing.addVal_eq_iff_associated _ _).2
          (Ideal.span_singleton_eq_span_singleton.mp hspan)
      _ = (e : ℕ∞) := hvarpi.addVal_pow e
  rw [ha_decomp, map_mul, map_pow,
    IsDiscreteValuationRing.addVal_mul,
    IsDiscreteValuationRing.addVal_pow, hmap_uniformizer,
    IsDiscreteValuationRing.addVal_def
      ((unit : base.valuationSubring) * pi ^ m)
      unit hpi m rfl]
  have hmap_unit :
      IsDiscreteValuationRing.addVal target.valuationSubring
          (integerMap base.toDVF target.toDVF
            (unit : base.valuationSubring)) = 0 := by
    exact
      IsDiscreteValuationRing.addVal_eq_zero_iff.mpr
        ((unit.isUnit : IsUnit (unit : base.valuationSubring)).map
          (integerMap base.toDVF target.toDVF))
  rw [hmap_unit, zero_add]
  simp [e, nsmul_eq_mul, mul_comm]

/-- The target additive valuation of the image of a base uniformizer is the
ramification index. -/
theorem addVal_integerMap_eq_ramificationIndex_of_irreducible
    {a : base.valuationSubring} (ha : Irreducible a) :
    IsDiscreteValuationRing.addVal target.valuationSubring
        (integerMap base.toDVF target.toDVF a) =
      (ramificationIndex base.toDVF target.toDVF : ℕ∞) := by
  rw [addVal_integerMap_eq_ramificationIndex_nsmul base target a,
    IsDiscreteValuationRing.addVal_uniformizer ha, nsmul_eq_mul, mul_one]

/-- If a base uniformizer remains a uniformizer after applying the
valuation-ring map, then the relative ramification index is one. -/
theorem ramificationIndex_eq_one_of_integerMap_uniformizer
    (a : base.valuationSubring)
    (ha : base.valuation.IsUniformizer (a : K))
    (hmap :
      target.valuation.IsUniformizer
        ((integerMap base.toDVF target.toDVF a :
          target.valuationSubring) : L)) :
    ramificationIndex base.toDVF target.toDVF = 1 := by
  have haIrreducible : Irreducible a :=
    (IsDiscreteValuationRing.irreducible_iff_uniformizer a).2
      (base.maximalIdeal_eq_span_uniformizer ha)
  have hmapIrreducible :
      Irreducible (integerMap base.toDVF target.toDVF a) :=
    (IsDiscreteValuationRing.irreducible_iff_uniformizer
      (integerMap base.toDVF target.toDVF a)).2
      (target.maximalIdeal_eq_span_uniformizer hmap)
  have hadd :=
    addVal_integerMap_eq_ramificationIndex_nsmul base target a
  rw [IsDiscreteValuationRing.addVal_uniformizer hmapIrreducible,
    IsDiscreteValuationRing.addVal_uniformizer haIrreducible,
    nsmul_eq_mul, mul_one] at hadd
  have hcoe :
      (ramificationIndex base.toDVF target.toDVF : ℕ∞) = 1 :=
    hadd.symm
  exact_mod_cast hcoe

end ValuedExtension
end LocalFieldTheory.DiscreteValuationField

end
