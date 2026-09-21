/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/

import LeanPool.ClassFieldTheory.ValuedFieldTheory.Valuation.DiscreteValuationField.FiniteExtension.Uniqueness
/-!
# Uniformizers detected in an ambient complete discrete valuation field

An embedding into an ambient complete DVF can make a uniformizer easier to
recognize.  For a finite separable extension, uniqueness of the extended
valuation transports that recognition back to the chosen valuation.
-/

namespace ValuationTheory

noncomputable section

universe u v w x y z

namespace DiscreteValuationField
namespace ValuedExtension

variable {K : Type u} {L : Type w} [Field K] [Field L]
variable [Algebra K L] [FiniteDimensional K L] [Algebra.IsSeparable K L]

/-- An embedding into an ambient valued field restricts to valuation rings
whenever the chosen source valuation is equivalent to the pulled-back
ambient valuation. -/
noncomputable def valuationSubringMapOfIsEquivComap
    {M : Type y} [Field M]
    {GammaL : Type x} {GammaM : Type z}
    [LinearOrderedCommGroupWithZero GammaL]
    [LinearOrderedCommGroupWithZero GammaM]
    (vL : _root_.Valuation L GammaL)
    (vM : _root_.Valuation M GammaM)
    (ι : L →+* M)
    (hEquiv : vL.IsEquiv (vM.comap ι)) :
    vL.valuationSubring →+* vM.valuationSubring where
  toFun a :=
    ⟨ι (a : L), by
      have ha :
          vL (a : L) ≤ vL 1 :=
        by
          rw [map_one]
          exact a.property
      have hcomap :=
        (hEquiv.le_iff_le
          (x := (a : L)) (y := (1 : L))).1 ha
      change vM (ι (a : L)) ≤ 1
      simpa only [_root_.Valuation.comap_apply, map_one] using hcomap⟩
  map_one' := by
    apply Subtype.ext
    simp
  map_mul' a b := by
    apply Subtype.ext
    simp
  map_zero' := by
    apply Subtype.ext
    simp
  map_add' a b := by
    apply Subtype.ext
    simp

/-- The valuation-ring map induced by an equivalent ambient pullback acts
through the original field embedding. -/
@[simp]
theorem valuationSubringMapOfIsEquivComap_apply
    {M : Type y} [Field M]
    {GammaL : Type x} {GammaM : Type z}
    [LinearOrderedCommGroupWithZero GammaL]
    [LinearOrderedCommGroupWithZero GammaM]
    (vL : _root_.Valuation L GammaL)
    (vM : _root_.Valuation M GammaM)
    (ι : L →+* M)
    (hEquiv : vL.IsEquiv (vM.comap ι))
    (a : vL.valuationSubring) :
    ((valuationSubringMapOfIsEquivComap vL vM ι hEquiv a :
      vM.valuationSubring) : M) =
      ι (a : L) :=
  rfl

/-- The valuation-ring map induced by an equivalent ambient pullback is a
local homomorphism. -/
theorem valuationSubringMapOfIsEquivComap_isLocalHom
    {M : Type y} [Field M]
    {GammaL : Type x} {GammaM : Type z}
    [LinearOrderedCommGroupWithZero GammaL]
    [LinearOrderedCommGroupWithZero GammaM]
    (vL : _root_.Valuation L GammaL)
    (vM : _root_.Valuation M GammaM)
    (ι : L →+* M)
    (hEquiv : vL.IsEquiv (vM.comap ι)) :
    IsLocalHom
      (valuationSubringMapOfIsEquivComap vL vM ι hEquiv) := by
  let f := valuationSubringMapOfIsEquivComap vL vM ι hEquiv
  apply ((IsLocalRing.local_hom_TFAE f).out 2 1).mp
  rintro _ ⟨a, ha, rfl⟩
  have haVal : vL (a : L) < 1 :=
    (_root_.Valuation.mem_maximalIdeal_iff (v := vL)).1 ha
  have hlt :=
    (hEquiv.lt_iff_lt
      (x := (a : L)) (y := (1 : L))).1
      (by
        rw [map_one]
        exact haVal)
  exact (_root_.Valuation.mem_maximalIdeal_iff (v := vM)).2 <| by
    simpa only [f, valuationSubringMapOfIsEquivComap_apply,
      _root_.Valuation.comap_apply, map_one] using hlt

/-- The induced injection from the chosen residue field into the ambient
residue field. -/
noncomputable def residueFieldMapOfIsEquivComap
    {M : Type y} [Field M]
    {GammaL : Type x} {GammaM : Type z}
    [LinearOrderedCommGroupWithZero GammaL]
    [LinearOrderedCommGroupWithZero GammaM]
    (vL : _root_.Valuation L GammaL)
    (vM : _root_.Valuation M GammaM)
    (ι : L →+* M)
    (hEquiv : vL.IsEquiv (vM.comap ι)) :
    IsLocalRing.ResidueField vL.valuationSubring →+*
      IsLocalRing.ResidueField vM.valuationSubring := by
  letI :
      IsLocalHom
        (valuationSubringMapOfIsEquivComap vL vM ι hEquiv) :=
    valuationSubringMapOfIsEquivComap_isLocalHom vL vM ι hEquiv
  exact
    IsLocalRing.ResidueField.map
      (valuationSubringMapOfIsEquivComap vL vM ι hEquiv)

/-- Reduction modulo the maximal ideal commutes with compatible
automorphisms of the source and ambient valuation rings.  This is the
residue-field naturality needed when a finite valued subfield is realized
inside a larger complete discrete valuation field. -/
theorem residueFieldMapOfIsEquivComap_mapEquiv
    {M : Type y} [Field M]
    {GammaL : Type x} {GammaM : Type z}
    [LinearOrderedCommGroupWithZero GammaL]
    [LinearOrderedCommGroupWithZero GammaM]
    (vL : _root_.Valuation L GammaL)
    (vM : _root_.Valuation M GammaM)
    (ι : L →+* M)
    (hEquiv : vL.IsEquiv (vM.comap ι))
    (σL : vL.valuationSubring ≃+* vL.valuationSubring)
    (σM : vM.valuationSubring ≃+* vM.valuationSubring)
    (hcompat :
      ∀ a : vL.valuationSubring,
        valuationSubringMapOfIsEquivComap vL vM ι hEquiv (σL a) =
          σM
            (valuationSubringMapOfIsEquivComap
              vL vM ι hEquiv a))
    (a : IsLocalRing.ResidueField vL.valuationSubring) :
    residueFieldMapOfIsEquivComap vL vM ι hEquiv
        (IsLocalRing.ResidueField.mapEquiv σL a) =
      IsLocalRing.ResidueField.mapEquiv σM
        (residueFieldMapOfIsEquivComap vL vM ι hEquiv a) := by
  let :
      IsLocalHom
        (valuationSubringMapOfIsEquivComap vL vM ι hEquiv) :=
    valuationSubringMapOfIsEquivComap_isLocalHom vL vM ι hEquiv
  let : IsLocalHom σL.toRingHom :=
    IsLocalHom.of_surjective σL.toRingHom σL.surjective
  let : IsLocalHom σM.toRingHom :=
    IsLocalHom.of_surjective σM.toRingHom σM.surjective
  obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective a
  change
    IsLocalRing.ResidueField.map
        (valuationSubringMapOfIsEquivComap vL vM ι hEquiv)
        (IsLocalRing.ResidueField.map σL.toRingHom
          (IsLocalRing.residue vL.valuationSubring b)) =
      IsLocalRing.ResidueField.map σM.toRingHom
        (IsLocalRing.ResidueField.map
          (valuationSubringMapOfIsEquivComap vL vM ι hEquiv)
          (IsLocalRing.residue vL.valuationSubring b))
  simp only [IsLocalRing.ResidueField.map_residue]
  exact congrArg
    (IsLocalRing.residue vM.valuationSubring)
    (hcompat b)

/-- Let `L / K` be finite separable with a chosen complete discrete valuation
extending the one on `K`.  If a field embedding of `L` into another complete
DVF sends `π` to an ambient uniformizer, and the pulled-back ambient valuation
also extends the base valuation, then `π` is a uniformizer for the chosen
valuation on `L`.

The proof first uses uniqueness of valuation extension to compare the chosen
valuation with the ambient comap valuation.  It then pulls divisibility by the
ambient uniformizer back through the field embedding, proving that `π`
generates the chosen maximal ideal. -/
theorem isUniformizer_of_ambient_image_isUniformizer
    {M : Type y} [Field M]
    (base : CompleteDVF.{u, v} K) (target : CompleteDVF.{w, x} L)
    (ambient : CompleteDVF.{y, z} M)
    [base.valuation.HasExtension target.valuation]
    (ι : L →+* M)
    [base.valuation.HasExtension (ambient.valuation.comap ι)]
    {π : L} (hπ : ambient.valuation.IsUniformizer (ι π)) :
    target.valuation.IsUniformizer π := by
  have hEquiv :
      target.valuation.IsEquiv (ambient.valuation.comap ι) :=
    valuation_isEquiv_of_finite_separable base target
      (ambient.valuation.comap ι)
  have hπ_target_lt : target.valuation π < 1 := by
    have hπ_comap_lt :
        (ambient.valuation.comap ι) π <
          (ambient.valuation.comap ι) 1 := by
      simpa using hπ.val_lt_one
    simpa using
      (hEquiv.lt_iff_lt (x := π) (y := (1 : L))).2 hπ_comap_lt
  let πtarget : target.valuationSubring :=
    ⟨π, hπ_target_lt.le⟩
  have hmaximal :
      target.maximalIdeal =
        Ideal.span ({πtarget} : Set target.valuationSubring) := by
    apply le_antisymm
    · intro a ha
      have ha_target_lt : target.valuation (a : L) < 1 :=
        (_root_.Valuation.mem_maximalIdeal_iff
          (v := target.valuation)).1 ha
      have ha_ambient_lt : ambient.valuation (ι (a : L)) < 1 := by
        have ha_comap_lt :
            (ambient.valuation.comap ι) (a : L) <
              (ambient.valuation.comap ι) 1 :=
          (hEquiv.lt_iff_lt (x := (a : L)) (y := (1 : L))).1
            (by simpa using ha_target_lt)
        simpa using ha_comap_lt
      let aambient : ambient.valuationSubring :=
        ⟨ι (a : L), ha_ambient_lt.le⟩
      let πambient : ambient.valuationSubring :=
        ⟨ι π, hπ.val_lt_one.le⟩
      have ha_ambient_maximal :
          aambient ∈ ambient.maximalIdeal :=
        (_root_.Valuation.mem_maximalIdeal_iff
          (v := ambient.valuation)).2 ha_ambient_lt
      have hπambient :
          ambient.valuation.IsUniformizer (πambient : M) := by
        simpa [πambient] using hπ
      rw [ambient.maximalIdeal_eq_span_uniformizer hπambient,
        Ideal.mem_span_singleton] at ha_ambient_maximal
      obtain ⟨c, hc⟩ := ha_ambient_maximal
      have hc_field :
          ι (a : L) = ι π * (c : M) := by
        simpa [aambient, πambient] using
          congrArg
            (fun t : ambient.valuationSubring => (t : M)) hc
      have hπ_ne : π ≠ 0 := by
        intro hzero
        apply hπ.ne_zero
        simp [hzero]
      have hc_eq :
          (c : M) = ι (π⁻¹ * (a : L)) := by
        apply mul_left_cancel₀ hπ.ne_zero
        calc
          ι π * (c : M) = ι (a : L) := hc_field.symm
          _ = ι (π * (π⁻¹ * (a : L))) := by
            congr 1
            rw [← mul_assoc, mul_inv_cancel₀ hπ_ne, one_mul]
          _ = ι π * ι (π⁻¹ * (a : L)) := by
            rw [map_mul]
      have hquotient_comap :
          (ambient.valuation.comap ι) (π⁻¹ * (a : L)) ≤
            (ambient.valuation.comap ι) 1 := by
        have hquotient_ambient :
            ambient.valuation (ι (π⁻¹ * (a : L))) ≤ 1 := by
          rw [← hc_eq]
          exact c.property
        simpa using hquotient_ambient
      have hquotient_target :
          target.valuation (π⁻¹ * (a : L)) ≤ 1 := by
        have hle :=
          (hEquiv.le_iff_le
            (x := π⁻¹ * (a : L)) (y := (1 : L))).2
            hquotient_comap
        simpa using hle
      let quotient : target.valuationSubring :=
        ⟨π⁻¹ * (a : L), hquotient_target⟩
      rw [Ideal.mem_span_singleton]
      refine ⟨quotient, ?_⟩
      apply Subtype.ext
      change (a : L) = π * (π⁻¹ * (a : L))
      rw [← mul_assoc, mul_inv_cancel₀ hπ_ne, one_mul]
    · rw [Ideal.span_le]
      intro a ha
      have ha_eq : a = πtarget := by
        simpa using ha
      subst a
      exact
        (_root_.Valuation.mem_maximalIdeal_iff
          (v := target.valuation)).2
          (by simpa [πtarget] using hπ_target_lt)
  have hπtarget :
      target.valuation.IsUniformizer (πtarget : L) :=
    target.valuation.isUniformizer_of_maximalIdeal_eq_span hmaximal
  simpa [πtarget] using hπtarget

end ValuedExtension
end DiscreteValuationField
end
end ValuationTheory
