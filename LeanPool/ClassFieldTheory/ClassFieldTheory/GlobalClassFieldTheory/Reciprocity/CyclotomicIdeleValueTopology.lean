/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/

import LeanPool.ClassFieldTheory.ClassFieldTheory.GlobalClassFieldTheory.Reciprocity.CyclotomicIdeleValue
import LeanPool.ClassFieldTheory.ClassFieldTheory.GlobalClassFieldTheory.Reciprocity.CyclotomicNormOneCorrection
import LeanPool.ClassFieldTheory.ClassFieldTheory.AlgebraicNumberTheory.Idele.NormTopology.Continuity
/-!
# Topology of the rational cyclotomic idele value

The rational cyclotomic idele value is constructed multiplicatively in
`CyclotomicIdeleValue`.  For descent to the additive idele class group and
for the valuation package, this file records its genuine continuous additive
form.  Its finite reductions give the open-kernel finite quotients which form
the profinite neighbourhood system used after principal-idèle vanishing has
been proved.
-/

noncomputable section

namespace GlobalClassFieldTheory
namespace Reciprocity

open ClassFormation

/-- The rational cyclotomic idele value in continuous additive notation. -/
noncomputable def rationalCyclotomicZHatIdeleValueContinuousAdd :
    Additive (IdeleGroup ℚ) →ₜ+ ZHat where
  __ :=
    rationalCyclotomicZHatIdeleValue.toMonoidHom.toAdditiveLeft
  continuous_toFun :=
    continuous_toAdd.comp
      (rationalCyclotomicZHatIdeleValue.continuous_toFun.comp
        continuous_toMul)

/-- Evaluation of the continuous additive rational cyclotomic value agrees
with the original multiplicative value. -/
@[simp]
theorem rationalCyclotomicZHatIdeleValueContinuousAdd_apply
    (a : IdeleGroup ℚ) :
    rationalCyclotomicZHatIdeleValueContinuousAdd
        (Additive.ofMul a) =
      Multiplicative.toAdd
        (rationalCyclotomicZHatIdeleValue a) :=
  rfl

/-- The continuous additive rational cyclotomic value has dense image. -/
theorem rationalCyclotomicZHatIdeleValueContinuousAdd_denseRange :
    DenseRange rationalCyclotomicZHatIdeleValueContinuousAdd := by
  have hToAdd :
      Function.Surjective
        (Multiplicative.toAdd :
          Multiplicative ZHat → ZHat) :=
    fun z => ⟨Multiplicative.ofAdd z, rfl⟩
  have hToMul :
      Function.Surjective
        (Additive.toMul :
          Additive (IdeleGroup ℚ) → IdeleGroup ℚ) :=
    fun a => ⟨Additive.ofMul a, rfl⟩
  have hAfterToAdd :
      DenseRange
        (fun a : IdeleGroup ℚ =>
          Multiplicative.toAdd
            (rationalCyclotomicZHatIdeleValue a)) :=
    hToAdd.denseRange.comp
      rationalCyclotomicZHatIdeleValue_denseRange
      continuous_toAdd
  change
    DenseRange
      (fun a : Additive (IdeleGroup ℚ) =>
        Multiplicative.toAdd
          (rationalCyclotomicZHatIdeleValue
            (Additive.toMul a)))
  exact
    hAfterToAdd.comp hToMul.denseRange
      (continuous_toAdd.comp
        rationalCyclotomicZHatIdeleValue.continuous_toFun)

/-- The kernel of the continuous additive rational cyclotomic value is
closed.  This is the Hausdorffness input for its eventual quotient descent. -/
theorem rationalCyclotomicZHatIdeleValueContinuousAdd_isClosed_ker :
    IsClosed
      (((ContinuousAddMonoidHom.toAddMonoidHom
          rationalCyclotomicZHatIdeleValueContinuousAdd).ker :
        AddSubgroup (Additive (IdeleGroup ℚ))) :
        Set (Additive (IdeleGroup ℚ))) := by
  rw [show
    (((ContinuousAddMonoidHom.toAddMonoidHom
        rationalCyclotomicZHatIdeleValueContinuousAdd).ker :
      AddSubgroup (Additive (IdeleGroup ℚ))) :
      Set (Additive (IdeleGroup ℚ))) =
        rationalCyclotomicZHatIdeleValueContinuousAdd ⁻¹'
          ({0} : Set ZHat) by
    ext a
    simp]
  exact
    isClosed_singleton.preimage
      rationalCyclotomicZHatIdeleValueContinuousAdd.continuous_toFun

/-- Reduction of the rational cyclotomic idele value modulo a positive
integer, as an actual continuous additive homomorphism. -/
noncomputable def rationalCyclotomicZHatIdeleValueReduction
    (n : ℕ) (hn : 0 < n) :
    Additive (IdeleGroup ℚ) →ₜ+ ZMod n :=
  (zHatReduction n hn).comp
    rationalCyclotomicZHatIdeleValueContinuousAdd

/-- Evaluation of a finite reduction is reduction of the original
cyclotomic value. -/
@[simp]
theorem rationalCyclotomicZHatIdeleValueReduction_apply
    (n : ℕ) (hn : 0 < n) (a : IdeleGroup ℚ) :
    rationalCyclotomicZHatIdeleValueReduction n hn
        (Additive.ofMul a) =
      zHatReduction n hn
        (Multiplicative.toAdd
          (rationalCyclotomicZHatIdeleValue a)) :=
  rfl

/-- Every residue class modulo a positive integer occurs as a finite
reduction of the rational cyclotomic idele value. -/
theorem rationalCyclotomicZHatIdeleValueReduction_surjective
    (n : ℕ) (hn : 0 < n) :
    Function.Surjective
      (rationalCyclotomicZHatIdeleValueReduction n hn) := by
  have hReductionSurjective :
      Function.Surjective (zHatReduction n hn) := by
    intro z
    obtain ⟨a, rfl⟩ := ZMod.intCast_surjective z
    exact ⟨(a : ZHat), zHatReduction_intCast n hn a⟩
  have hDense :
      DenseRange
        (rationalCyclotomicZHatIdeleValueReduction n hn) := by
    exact
      hReductionSurjective.denseRange.comp
        rationalCyclotomicZHatIdeleValueContinuousAdd_denseRange
        (zHatReduction n hn).continuous_toFun
  intro z
  have hz :
      z ∈ closure
        (Set.range
          (rationalCyclotomicZHatIdeleValueReduction n hn)) :=
    hDense z
  rw [closure_discrete] at hz
  exact hz

/-- The finite reduction kernels are open.  They are the concrete open
congruence subgroups available for the later idele-class quotient map. -/
theorem rationalCyclotomicZHatIdeleValueReduction_isOpen_ker
    (n : ℕ) (hn : 0 < n) :
    IsOpen
      (((ContinuousAddMonoidHom.toAddMonoidHom
          (rationalCyclotomicZHatIdeleValueReduction n hn)).ker :
        AddSubgroup (Additive (IdeleGroup ℚ))) :
        Set (Additive (IdeleGroup ℚ))) := by
  rw [show
    (((ContinuousAddMonoidHom.toAddMonoidHom
        (rationalCyclotomicZHatIdeleValueReduction n hn)).ker :
      AddSubgroup (Additive (IdeleGroup ℚ))) :
      Set (Additive (IdeleGroup ℚ))) =
        rationalCyclotomicZHatIdeleValueReduction n hn ⁻¹'
          ({0} : Set (ZMod n)) by
    ext a
    simp]
  exact
    (isOpen_discrete ({0} : Set (ZMod n))).preimage
      (rationalCyclotomicZHatIdeleValueReduction n hn).continuous_toFun

variable (K : Type) [Field K] [NumberField K]

/-- The unnormalized cyclotomic norm composite, bundled with its actual
continuity.  Continuity here uses the global idele norm rather than a
quotient-level substitute. -/
noncomputable def cyclotomicZHatNormCompositeContinuous :
    Additive (IdeleGroup K) →ₜ+ ZHat where
  __ := cyclotomicZHatNormComposite K
  continuous_toFun := by
    change
      Continuous
        (fun a : Additive (IdeleGroup K) =>
          Multiplicative.toAdd
            (rationalCyclotomicZHatIdeleValue
              (IdeleGroup.norm ℚ K (Additive.toMul a))))
    exact
      continuous_toAdd.comp
        (rationalCyclotomicZHatIdeleValue.continuous_toFun.comp
          ((IdeleGroup.norm_continuous ℚ K).comp
            continuous_toMul))

/-- The continuous norm composite agrees pointwise with the underlying
unnormalized cyclotomic norm composite. -/
@[simp]
theorem cyclotomicZHatNormCompositeContinuous_apply
    (a : IdeleGroup K) :
    cyclotomicZHatNormCompositeContinuous K (Additive.ofMul a) =
      Multiplicative.toAdd
        (rationalCyclotomicZHatIdeleValue
          (IdeleGroup.norm ℚ K a)) :=
  rfl

/-- The unnormalized composite, continuously restricted to its actual
multiple subgroup `f_K ℤ̂`. -/
noncomputable def cyclotomicZHatNormCompositeInMulNatRangeContinuous :
    Additive (IdeleGroup K) →ₜ+
      (zHatMulNat
        (cyclotomicZHatIntersectionDegree K)).toAddMonoidHom.range where
  __ := cyclotomicZHatNormCompositeInMulNatRange K
  continuous_toFun := by
    apply Continuous.subtype_mk
    exact (cyclotomicZHatNormCompositeContinuous K).continuous_toFun

/-- Coercing the continuous range-restricted norm composite recovers the
underlying cyclotomic norm composite. -/
theorem cyclotomicZHatNormCompositeInMulNatRangeContinuous_apply
    (a : Additive (IdeleGroup K)) :
    (cyclotomicZHatNormCompositeInMulNatRangeContinuous K a :
        ZHat) =
      cyclotomicZHatNormComposite K a :=
  rfl

/-- The normalized cyclotomic value on ideles as a genuine continuous
additive homomorphism. -/
noncomputable def normalizedCyclotomicZHatIdeleValueContinuous :
    Additive (IdeleGroup K) →ₜ+ ZHat :=
  (zHatDivide
      (cyclotomicZHatIntersectionDegree K)
      (cyclotomicZHatIntersectionDegree_pos K)).comp
    (cyclotomicZHatNormCompositeInMulNatRangeContinuous K)

/-- The continuous normalized cyclotomic value agrees pointwise with its
underlying additive homomorphism. -/
@[simp]
theorem normalizedCyclotomicZHatIdeleValueContinuous_apply
    (a : Additive (IdeleGroup K)) :
    normalizedCyclotomicZHatIdeleValueContinuous K a =
      normalizedCyclotomicZHatIdeleValue K a :=
  rfl

/-- The normalized cyclotomic value in continuous multiplicative notation.
This is the source homomorphism which descends through the principal-idèle
quotient once the rational principal product formula has been established. -/
noncomputable def normalizedCyclotomicZHatIdeleValueContinuousMul :
    IdeleGroup K →ₜ* Multiplicative ZHat where
  toMonoidHom :=
    AddMonoidHom.toMultiplicativeRight
      (normalizedCyclotomicZHatIdeleValueContinuous K).toAddMonoidHom
  continuous_toFun :=
    continuous_ofAdd.comp
      ((normalizedCyclotomicZHatIdeleValueContinuous K).continuous_toFun.comp
        continuous_toAdd)

/-- The multiplicative continuous normalized value is the multiplicative
form of the underlying additive normalized value. -/
@[simp]
theorem normalizedCyclotomicZHatIdeleValueContinuousMul_apply
    (a : IdeleGroup K) :
    normalizedCyclotomicZHatIdeleValueContinuousMul K a =
      Multiplicative.ofAdd
        (normalizedCyclotomicZHatIdeleValue K
          (Additive.ofMul a)) :=
  rfl

/-- The actual norm-one ideles already have dense normalized cyclotomic
value.  The source reduction uses the positive archimedean correction,
whose cyclotomic value is trivial. -/
theorem normalizedCyclotomicZHatIdeleValue_normOne_denseRange :
    DenseRange
      (fun b : IdeleGroup.normOneSubgroup (K := K) =>
        normalizedCyclotomicZHatIdeleValue K
          (Additive.ofMul (b : IdeleGroup K))) := by
  apply (normalizedCyclotomicZHatIdeleValue_denseRange K).mono
  rintro z ⟨a, rfl⟩
  obtain ⟨b, hb⟩ :=
    exists_normOneIdele_same_normalizedCyclotomicZHatIdeleValue
      K (Additive.toMul a)
  refine ⟨b, ?_⟩
  simpa using hb

end Reciprocity
end GlobalClassFieldTheory
