/-
Copyright (c) 2026 Utensil Song, OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Utensil Song, OpenAI
-/
/-

Derived in part from Apache-2.0 `openai/ten-proofs`, `ConnesRigidity.lean` at
94bc0feb6a9ff12c7d31d6de640a725c9d43d2b6, lines 14519-14692.
Modifications: split generic Haar transport into its own module and changed
imports and namespace. Paper: §3. See the upstream PORT_MAP.md.
-/
import LeanPool.ConnesRigidity.Foundation.OperatorAlgebra.CrossedProduct

/-!
The crossed product transport component of the Connes rigidity formalization.
-/

namespace Connes
namespace CrossedProduct

open MeasureTheory
open scoped NNReal ENNReal

noncomputable section

universe u v w

variable {K : Type u} [Group K]
variable {Ω : Type v} [AddCommGroup Ω] [TopologicalSpace Ω] [MeasurableSpace Ω]
variable {Ξ : Type w} [AddCommGroup Ξ] [TopologicalSpace Ξ] [MeasurableSpace Ξ]

/- The fiberwise Haar transport on crossed Hilbert spaces. Paper: §3.
-/
/--
The `crossedHaarHilbertEquiv` construction used in the Connes rigidity formalization.
-/
def crossedHaarHilbertEquiv
    {X : HaarProbabilityAction K Ω}
    {Y : HaarProbabilityAction K Ξ}
    (e : EquivariantHaarEquiv X Y) :
    crossedHilbert X ≃ₗᵢ[ℂ] crossedHilbert Y :=
  crossedFiberwiseEquiv (K := K) (crossedBaseHaarEquiv e)

@[simp] theorem crossedHaarHilbertEquiv_apply
    {X : HaarProbabilityAction K Ω}
    {Y : HaarProbabilityAction K Ξ}
    (e : EquivariantHaarEquiv X Y)
    (ξ : crossedHilbert X) (k : K) :
    crossedHaarHilbertEquiv e ξ k = crossedBaseHaarEquiv e (ξ k) := rfl

/- Constant one is preserved by measure-preserving base transport.
Paper: §3. -/
theorem crossedBaseHaarEquiv_const_one
    {X : HaarProbabilityAction K Ω}
    {Y : HaarProbabilityAction K Ξ}
    (e : EquivariantHaarEquiv X Y) :
    let _ : IsProbabilityMeasure X.measure := X.probability
    let _ : IsProbabilityMeasure Y.measure := Y.probability
    crossedBaseHaarEquiv e (Lp.const 2 X.measure (1 : ℂ)) =
      Lp.const 2 Y.measure (1 : ℂ) := by
  let probabilityX : IsProbabilityMeasure X.measure := X.probability
  let probabilityY : IsProbabilityMeasure Y.measure := Y.probability
  apply Lp.ext
  let hp : MeasurePreserving
      (e.toMeasurableEquiv.symm : Ξ → Ω) Y.measure X.measure :=
    (EquivariantHaarEquiv.symm e).measure_preserving
  have hsource := Lp.coeFn_const (μ := X.measure) (p := 2) (1 : ℂ)
  have hsource' := hp.quasiMeasurePreserving.ae_eq_comp hsource
  filter_upwards [
    Lp.coeFn_compMeasurePreserving (Lp.const 2 X.measure (1 : ℂ)) hp,
    hsource',
    Lp.coeFn_const (μ := Y.measure) (p := 2) (1 : ℂ)]
    with z hcomp hsource' htarget
  change
    (Lp.compMeasurePreserving e.toMeasurableEquiv.symm hp
      (Lp.const 2 X.measure (1 : ℂ))) z =
      Lp.const 2 Y.measure (1 : ℂ) z
  calc
    _ = (Lp.const 2 X.measure (1 : ℂ))
      (e.toMeasurableEquiv.symm z) := hcomp
    _ = 1 := hsource'
    _ = _ := htarget.symm

/- The crossed-product vacuum is invariant under equivariant Haar transport.
Paper: §3. -/
theorem crossedHaarHilbertEquiv_vacuum
    {X : HaarProbabilityAction K Ω}
    {Y : HaarProbabilityAction K Ξ}
    (e : EquivariantHaarEquiv X Y) :
    crossedHaarHilbertEquiv e (crossedVacuum X) = crossedVacuum Y := by
  classical
  let probabilityX : IsProbabilityMeasure X.measure := X.probability
  let probabilityY : IsProbabilityMeasure Y.measure := Y.probability
  apply lp.ext
  funext k
  by_cases hk : k = 1
  · subst k
    simpa only [crossedVacuum, crossedHaarHilbertEquiv_apply, lp.single_apply,
      Pi.single_eq_same, crossedBaseHaarEquiv_apply] using
      crossedBaseHaarEquiv_const_one e
  · simp only [crossedVacuum, crossedHaarHilbertEquiv_apply, lp.single_apply,
      ne_eq, hk, not_false_eq_true, Pi.single_eq_of_ne, map_zero]

/- Base multiplication is transported by the Haar pullback. Paper: §3. -/
theorem crossedBaseHaarEquiv_multiplier_apply
    {X : HaarProbabilityAction K Ω}
    {Y : HaarProbabilityAction K Ξ}
    (e : EquivariantHaarEquiv X Y)
    (f : crossedCoefficient X) (ξ : crossedBaseHilbert X) :
    crossedBaseHaarEquiv e (crossedBaseMultiplier X f ξ) =
      crossedBaseMultiplier Y
        (Lp.compMeasurePreserving e.toMeasurableEquiv.symm
          (EquivariantHaarEquiv.symm e).measure_preserving f)
        (crossedBaseHaarEquiv e ξ) := by
  apply Lp.ext
  let hs : MeasurePreserving
      (e.toMeasurableEquiv.symm : Ξ → Ω) Y.measure X.measure :=
    (EquivariantHaarEquiv.symm e).measure_preserving
  have hleft := Lp.coeFn_compMeasurePreserving
    (crossedBaseMultiplier X f ξ) hs
  have hmul := hs.quasiMeasurePreserving.ae
    (crossedBaseMultiplier_apply_ae X f ξ)
  have hf := Lp.coeFn_compMeasurePreserving f hs
  have hξ := Lp.coeFn_compMeasurePreserving ξ hs
  have hright := crossedBaseMultiplier_apply_ae Y
    (Lp.compMeasurePreserving e.toMeasurableEquiv.symm hs f)
    (crossedBaseHaarEquiv e ξ)
  filter_upwards [hleft, hmul, hf, hξ, hright]
    with z hleft hmul hf hξ hright
  simp only [Function.comp_apply] at hleft hf hξ
  change (Lp.compMeasurePreserving e.toMeasurableEquiv.symm hs
    (crossedBaseMultiplier X f ξ)) z = _
  calc
    _ = (crossedBaseMultiplier X f ξ)
      (e.toMeasurableEquiv.symm z) := hleft
    _ = f (e.toMeasurableEquiv.symm z) *
      ξ (e.toMeasurableEquiv.symm z) := hmul
    _ = (Lp.compMeasurePreserving e.toMeasurableEquiv.symm hs f) z *
      (crossedBaseHaarEquiv e ξ) z := by
        congr 1
        · exact hf.symm
        · exact hξ.symm
    _ = _ := hright.symm

/- Equivariance transports the base action on L². Paper: §3. -/
theorem crossedBaseHaarEquiv_action
    {X : HaarProbabilityAction K Ω}
    {Y : HaarProbabilityAction K Ξ}
    (e : EquivariantHaarEquiv X Y) (k : K) (ξ : crossedBaseHilbert X) :
    crossedBaseHaarEquiv e (crossedActionL2Equiv X k ξ) =
      crossedActionL2Equiv Y k (crossedBaseHaarEquiv e ξ) := by
  let hs : MeasurePreserving
      (e.toMeasurableEquiv.symm : Ξ → Ω) Y.measure X.measure :=
    (EquivariantHaarEquiv.symm e).measure_preserving
  let hX := X.action_preserves_measure k⁻¹
  let hY := Y.action_preserves_measure k⁻¹
  change
    Lp.compMeasurePreserving e.toMeasurableEquiv.symm hs
      (Lp.compMeasurePreserving (X.action k⁻¹) hX ξ) =
      Lp.compMeasurePreserving (Y.action k⁻¹) hY
        (Lp.compMeasurePreserving e.toMeasurableEquiv.symm hs ξ)
  have hleft := Lp.compMeasurePreserving_comp_apply ξ hX hs
  have hright := Lp.compMeasurePreserving_comp_apply ξ hs hY
  have hfun :
      (X.action k⁻¹ : Ω → Ω) ∘
        (e.toMeasurableEquiv.symm : Ξ → Ω) =
      (e.toMeasurableEquiv.symm : Ξ → Ω) ∘
        (Y.action k⁻¹ : Ξ → Ξ) := by
    funext z
    change X.action k⁻¹ (e.toMeasurableEquiv.symm z) =
      e.toMeasurableEquiv.symm (Y.action k⁻¹ z)
    apply e.toMeasurableEquiv.injective
    rw [e.equivariant]
    simp only [map_inv, MeasurableEquiv.apply_symm_apply, Equiv.Perm.coe_inv]
  calc
    _ = Lp.compMeasurePreserving
      ((X.action k⁻¹ : Ω → Ω) ∘
        (e.toMeasurableEquiv.symm : Ξ → Ω))
      (hX.comp hs) ξ := hleft.symm
    _ = Lp.compMeasurePreserving
      ((e.toMeasurableEquiv.symm : Ξ → Ω) ∘
        (Y.action k⁻¹ : Ξ → Ξ))
      (hs.comp hY) ξ := by
        apply Lp.ext
        have hL := Lp.coeFn_compMeasurePreserving ξ (hX.comp hs)
        have hR := Lp.coeFn_compMeasurePreserving ξ (hs.comp hY)
        filter_upwards [hL, hR] with z hzL hzR
        calc
          _ = ξ (((X.action k⁻¹ : Ω → Ω) ∘
            (e.toMeasurableEquiv.symm : Ξ → Ω)) z) := by
              simpa only [Function.comp_apply] using hzL
          _ = ξ (((e.toMeasurableEquiv.symm : Ξ → Ω) ∘
            (Y.action k⁻¹ : Ξ → Ξ)) z) :=
              congrArg ξ (congrFun hfun z)
          _ = _ := by simpa only [Function.comp_apply] using hzR.symm
    _ = _ := hright

/- The crossed-product group unitary is transported by equivariant Haar data.
Paper: §3. -/
theorem crossedHaarHilbertEquiv_group_apply
    {X : HaarProbabilityAction K Ω}
    {Y : HaarProbabilityAction K Ξ}
    (e : EquivariantHaarEquiv X Y) (k : K) (ξ : crossedHilbert X) :
    crossedHaarHilbertEquiv e (crossedGroupUnitary X k ξ) =
      crossedGroupUnitary Y k (crossedHaarHilbertEquiv e ξ) := by
  apply lp.ext
  funext h
  exact crossedBaseHaarEquiv_action e k (ξ (k⁻¹ * h))

/- The transported crossed-product group operator is conjugate to the target.
Paper: §3. -/
theorem crossedHaarHilbertEquiv_group_conj
    {X : HaarProbabilityAction K Ω}
    {Y : HaarProbabilityAction K Ξ}
    (e : EquivariantHaarEquiv X Y) (k : K) :
    (crossedHaarHilbertEquiv e).conjStarAlgEquiv
      (crossedGroupUnitary X k).toContinuousLinearEquiv.toContinuousLinearMap =
        (crossedGroupUnitary Y k).toContinuousLinearEquiv.toContinuousLinearMap := by
  apply ContinuousLinearMap.ext
  intro η
  obtain ⟨ξ, rfl⟩ := (crossedHaarHilbertEquiv e).surjective η
  simpa only [LinearIsometryEquiv.conjStarAlgEquiv_apply_apply,
    LinearIsometryEquiv.symm_apply_apply, ContinuousLinearEquiv.coe_coe,
    LinearIsometryEquiv.coe_toContinuousLinearEquiv] using
    crossedHaarHilbertEquiv_group_apply e k ξ

end
end CrossedProduct
end Connes
