/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/
module


public import LeanPool.ClassFieldTheory.ValuedFieldTheory.Valuation.DiscreteValuationField.Basic

/-! # Valuation Transport -/

@[expose] public section
namespace ValuationTheory

/-!
# Valuation transport along field equivalences

This file records the source facts needed to transport complete-DVF data from
a finite subextension to its image inside a common ambient field.  The
transport is by comapping the valuation along a field equivalence; no
valuation-comparison hypothesis is added.
-/

noncomputable
section

universe u v w

namespace DiscreteValuationField
namespace Valuation

variable {K : Type u} {L : Type w} [Field K] [Field L]
variable {Γ : Type v} [LinearOrderedCommGroupWithZero Γ]

/-- Pulling a valuation back along a field equivalence does not change its
value group. -/
theorem valueGroup_comap_ringEquiv
    (v : _root_.Valuation K Γ) (e : L ≃+* K) :
    MonoidWithZeroHom.valueGroup
        (.ofClass (v.comap (e : L →+* K))) =
      MonoidWithZeroHom.valueGroup (.ofClass v) := by
  ext γ
  constructor
  · intro hγ
    have hval :
        (γ : Γ) ∈ Set.range (v.comap (e : L →+* K)) \ {0} := by
      have himage :
          (γ : Γ) ∈ Units.val '' MonoidWithZeroHom.valueGroup
            (.ofClass (v.comap (e : L →+* K))) :=
        ⟨γ, hγ, rfl⟩
      rw [MonoidWithZeroHom.valueGroup_eq_range] at himage
      simpa only [MonoidWithZeroHom.coe_ofClass] using himage
    rcases hval with ⟨hrange, hne⟩
    rcases hrange with ⟨x, hx⟩
    have hval' : (γ : Γ) ∈ Set.range v \ {0} := by
      exact ⟨⟨e x, by simpa using hx⟩, hne⟩
    have himage :
        (γ : Γ) ∈
          Units.val '' MonoidWithZeroHom.valueGroup (.ofClass v) := by
      rw [MonoidWithZeroHom.valueGroup_eq_range]
      simpa only [MonoidWithZeroHom.coe_ofClass] using hval'
    rcases himage with ⟨δ, hδ, hδγ⟩
    have hδ_eq : δ = γ := Units.ext hδγ
    simpa [hδ_eq] using hδ
  · intro hγ
    have hval : (γ : Γ) ∈ Set.range v \ {0} := by
      have himage :
          (γ : Γ) ∈
            Units.val '' MonoidWithZeroHom.valueGroup (.ofClass v) :=
        ⟨γ, hγ, rfl⟩
      rw [MonoidWithZeroHom.valueGroup_eq_range] at himage
      simpa only [MonoidWithZeroHom.coe_ofClass] using himage
    rcases hval with ⟨hrange, hne⟩
    rcases hrange with ⟨x, hx⟩
    have hval' :
        (γ : Γ) ∈ Set.range (v.comap (e : L →+* K)) \ {0} := by
      exact ⟨⟨e.symm x, by simpa using hx⟩, hne⟩
    have himage :
        (γ : Γ) ∈
          Units.val '' MonoidWithZeroHom.valueGroup
            (.ofClass (v.comap (e : L →+* K))) := by
      rw [MonoidWithZeroHom.valueGroup_eq_range]
      simpa only [MonoidWithZeroHom.coe_ofClass] using hval'
    rcases himage with ⟨δ, hδ, hδγ⟩
    have hδ_eq : δ = γ := Units.ext hδγ
    simpa [hδ_eq] using hδ

/-- Rank-one discreteness is preserved by pulling a valuation back along a
field equivalence. -/
instance isRankOneDiscrete_comap_ringEquiv
    (v : _root_.Valuation K Γ) [v.IsRankOneDiscrete] (e : L ≃+* K) :
    (v.comap (e : L →+* K)).IsRankOneDiscrete where
  exists_generator_lt_one' := by
    rcases _root_.Valuation.IsRankOneDiscrete.exists_generator_lt_one v with
      ⟨γ, hγ, hlt⟩
    refine ⟨γ, ?_, hlt⟩
    simpa [valueGroup_comap_ringEquiv (v := v) e] using hγ

/-- The valuation ring of a comapped valuation is the source valuation ring,
transported through the field equivalence. -/
noncomputable def valuationSubringRingEquivOfComap
    (v : _root_.Valuation K Γ) (e : L ≃+* K) :
    (v.comap (e : L →+* K)).valuationSubring ≃+* v.valuationSubring where
  toFun x := ⟨e (x : L), x.2⟩
  invFun y := ⟨e.symm (y : K), by
    change v (e (e.symm (y : K))) ≤ 1
    rw [e.apply_symm_apply]
    exact y.2⟩
  left_inv x := by
    ext
    simp
  right_inv y := by
    ext
    simp
  map_mul' x y := by
    ext
    simp
  map_add' x y := by
    ext
    simp

/-- The valuation-subring equivalence induced by a comap acts through the ambient ring map. -/
@[simp] theorem valuationSubringRingEquivOfComap_apply
    (v : _root_.Valuation K Γ) (e : L ≃+* K)
    (x : (v.comap (e : L →+* K)).valuationSubring) :
    ((valuationSubringRingEquivOfComap v e x : v.valuationSubring) : K) =
      e (x : L) :=
  rfl

/-- The valuation-ring equivalence attached to a comap carries maximal-ideal
membership exactly. -/
theorem valuationSubringRingEquivOfComap_mem_maximalIdeal_iff
    (v : _root_.Valuation K Γ) (e : L ≃+* K)
    (x : (v.comap (e : L →+* K)).valuationSubring) :
    valuationSubringRingEquivOfComap v e x ∈
        IsLocalRing.maximalIdeal v.valuationSubring ↔
      x ∈ IsLocalRing.maximalIdeal
        (v.comap (e : L →+* K)).valuationSubring := by
  rw [_root_.Valuation.mem_maximalIdeal_iff,
    _root_.Valuation.mem_maximalIdeal_iff]
  rfl

/-- Map form of maximal-ideal preservation for the valuation-ring equivalence
attached to a comap. -/
@[simp] theorem maximalIdeal_map_valuationSubringRingEquivOfComap
    (v : _root_.Valuation K Γ) (e : L ≃+* K) :
    (IsLocalRing.maximalIdeal
        (v.comap (e : L →+* K)).valuationSubring).map
        (valuationSubringRingEquivOfComap v e :
          (v.comap (e : L →+* K)).valuationSubring →+*
            v.valuationSubring) =
      IsLocalRing.maximalIdeal v.valuationSubring := by
  let r := valuationSubringRingEquivOfComap v e
  ext y
  rw [Ideal.mem_map_iff_of_surjective
    (r : (v.comap (e : L →+* K)).valuationSubring →+*
      v.valuationSubring) r.surjective]
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact
      (valuationSubringRingEquivOfComap_mem_maximalIdeal_iff v e x).2 hx
  · intro hy
    refine ⟨r.symm y, ?_, by simp [r]⟩
    exact
      (valuationSubringRingEquivOfComap_mem_maximalIdeal_iff v e
        (r.symm y)).1 (by simpa [r] using hy)

/-- Comap form of maximal-ideal preservation for the valuation-ring
equivalence attached to a comap. -/
@[simp] theorem maximalIdeal_comap_valuationSubringRingEquivOfComap
    (v : _root_.Valuation K Γ) (e : L ≃+* K) :
    (IsLocalRing.maximalIdeal v.valuationSubring).comap
        (valuationSubringRingEquivOfComap v e :
          (v.comap (e : L →+* K)).valuationSubring →+*
            v.valuationSubring) =
      IsLocalRing.maximalIdeal
        (v.comap (e : L →+* K)).valuationSubring := by
  ext x
  exact valuationSubringRingEquivOfComap_mem_maximalIdeal_iff v e x

end Valuation
end DiscreteValuationField

end

end ValuationTheory
