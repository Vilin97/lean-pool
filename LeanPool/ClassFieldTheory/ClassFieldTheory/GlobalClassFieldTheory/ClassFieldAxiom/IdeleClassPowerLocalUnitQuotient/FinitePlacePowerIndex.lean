/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/

import LeanPool.ClassFieldTheory.ClassFieldTheory.GlobalClassFieldTheory.ClassFieldAxiom.IdeleClassPowerLocalUnitQuotient.LocalResidueArithmetic
import LeanPool.ClassFieldTheory.ClassFieldTheory.AlgebraicNumberTheory.Idele.LocallyCompact
import LeanPool.ClassFieldTheory.ValuedFieldTheory.LocalField.DiscreteValuationField.FieldUnitPowerIndexFormulas
import Mathlib.NumberTheory.NumberField.ProductFormula
/-!
# Finite-place power indices

This file supplies the completion instances and local cardinality formulas used
to evaluate finite-place factors in idele power quotients.
-/

open scoped NumberField NNReal ValuativeRel TensorProduct
open NumberField IsDedekindDomain

noncomputable section

namespace GlobalClassFieldTheory.ClassFieldAxiom

variable {K : Type} [Field K] [NumberField K]

open scoped Classical in
/-- The finite-place local power index in the integral form used before
applying the global product formula.  The two copies of `n` are
respectively the uniformizer direction and the `n`-th roots of unity
already contained in `K`. -/
theorem card_finitePlace_nthPowerQuotient
    (n : ℕ+)
    (hmu : (primitiveRoots (n : ℕ) K).Nonempty)
    (v₀ : HeightOneSpectrum (𝓞 K)) :
    let ν :
        Valuation (v₀.adicCompletion K)
          (WithZero (Multiplicative ℤ)) :=
      Valued.v
    let F :=
      LocalFieldTheory.DiscreteValuationField.LocalField.ofWithZeroValuation ν
    letI :
        LocalFieldTheory.DiscreteValuationField.LocalField.MixedWithZeroValuationContext
          ν :=
      LocalFieldTheory.DiscreteValuationField.LocalField.mixedWithZeroValuationContext ν
    letI :
        Valued (v₀.adicCompletion K)
          (WithZero (Multiplicative ℤ)) :=
      Valued.mk' ν
    let d :=
      Module.finrank ℚ_[F.residueCharacteristic]
        (v₀.adicCompletion K)
    Nat.card
        ((v₀.adicCompletion K)ˣ ⧸
          (powMonoidHom (n : ℕ) :
            (v₀.adicCompletion K)ˣ →*
              (v₀.adicCompletion K)ˣ).range) =
      (n : ℕ) *
        ((n : ℕ) *
          F.residueCharacteristic ^
            (d *
              padicValNat F.residueCharacteristic (n : ℕ))) := by
  let ν :
      Valuation (v₀.adicCompletion K)
        (WithZero (Multiplicative ℤ)) :=
    Valued.v
  let F :=
    LocalFieldTheory.DiscreteValuationField.LocalField.ofWithZeroValuation ν
  let : NeZero (n : ℕ) := ⟨n.ne_zero⟩
  have hν : Function.Surjective ν :=
    v₀.valuedAdicCompletion_surjective K
  let :
      LocalFieldTheory.DiscreteValuationField.LocalField.MixedWithZeroValuationContext
        ν :=
    LocalFieldTheory.DiscreteValuationField.LocalField.mixedWithZeroValuationContext ν
  let :
      Valued (v₀.adicCompletion K)
        (WithZero (Multiplicative ℤ)) :=
    Valued.mk' ν
  let d :=
    Module.finrank ℚ_[F.residueCharacteristic]
      (v₀.adicCompletion K)
  obtain ⟨a, e⟩ :=
    LocalFieldTheory.DiscreteValuationField.LocalField.chosenMixedFirstPrincipalUnitStructureOfWithZeroValuation
      ν hν
  let U :=
    LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup
      F.toCompleteDVF 1
  let A :=
    ZMod (F.residueCharacteristic ^ a) ×
      (Fin d → ℤ_[F.residueCharacteristic])
  let : Finite
      (A ⧸ LocalFieldTheory.nsmulAddSubgroup A (n : ℕ)) := by
    infer_instance
  let emul : U ≃* Multiplicative A := by
    let direct :
        Valued (v₀.adicCompletion K)
          (WithZero (Multiplicative ℤ)) :=
      Valued.mk' ν
    letI : TopologicalSpace (v₀.adicCompletion K) :=
      direct.toTopologicalSpace
    exact e.symm.toMulEquiv
  let : Finite
      (U ⧸
        (powMonoidHom (n : ℕ) : U →* U).range) :=
    LocalFieldTheory.finite_nthPowerQuotient_of_mulEquiv
      U (Multiplicative A) (n : ℕ) emul
  let hex := F.toCompleteDVF.exists_uniformizer
  let π := Classical.choose hex
  have hπ :
      F.toCompleteDVF.valuation.IsUniformizer
        (π : v₀.adicCompletion K) :=
    Classical.choose_spec hex
  let : Finite
      ((v₀.adicCompletion K)ˣ ⧸
        (powMonoidHom (n : ℕ) :
          (v₀.adicCompletion K)ˣ →*
            (v₀.adicCompletion K)ˣ).range) :=
    LocalFieldTheory.DiscreteValuationField.finite_fieldUnits_nthPowerQuotient_of_finite_principalUnits
      F.toCompleteDVF hπ (n : ℕ)
  have hindex :=
    LocalFieldTheory.DiscreteValuationField.LocalField.mixed_fieldIndex
      ν hν (n := (n : ℕ))
  have hroots :
      Nat.card
          ((powMonoidHom (n : ℕ) :
            (v₀.adicCompletion K)ˣ →*
              (v₀.adicCompletion K)ˣ).ker) =
        (n : ℕ) := by
    rw [
      LocalFieldTheory.powMonoidHom_ker_units_eq_rootsOfUnity]
    obtain ⟨ζ, hζ⟩ := hmu
    have hζprim : IsPrimitiveRoot ζ (n : ℕ) :=
      (mem_primitiveRoots n.pos).mp hζ
    exact
      (hζprim.map_of_injective
        (algebraMap K (v₀.adicCompletion K)).injective).card_rootsOfUnity
  simpa only [hroots] using hindex

open scoped Classical in
/-- The residue-characteristic contribution in the finite local
power-index formula.  Keeping this contribution as a named natural
number makes the subsequent product-formula calculation visible. -/
noncomputable def finitePlaceNthPowerDefect
    (n : ℕ+)
    (v₀ : HeightOneSpectrum (𝓞 K)) : ℕ :=
  let ν :
      Valuation (v₀.adicCompletion K)
        (WithZero (Multiplicative ℤ)) :=
    Valued.v
  let F :=
    LocalFieldTheory.DiscreteValuationField.LocalField.ofWithZeroValuation ν
  letI :
      LocalFieldTheory.DiscreteValuationField.LocalField.MixedWithZeroValuationContext
        ν :=
    LocalFieldTheory.DiscreteValuationField.LocalField.mixedWithZeroValuationContext ν
  letI :
      Valued (v₀.adicCompletion K)
        (WithZero (Multiplicative ℤ)) :=
    Valued.mk' ν
  let d :=
    Module.finrank ℚ_[F.residueCharacteristic]
      (v₀.adicCompletion K)
  F.residueCharacteristic ^
    (d * padicValNat F.residueCharacteristic (n : ℕ))

open scoped Classical in
/-- The local defect is the norm of the exact prime-power factor of
the principal ideal `(n)` at `v`. -/
theorem finitePlaceNthPowerDefect_eq_absNorm_maxPowDividing
    (n : ℕ+)
    (v : HeightOneSpectrum (𝓞 K)) :
    finitePlaceNthPowerDefect (K := K) n v =
      Ideal.absNorm
        (v.maxPowDividing
          (Ideal.span {((n : ℕ) : 𝓞 K)})) := by
  let ν :
      Valuation
        (v.adicCompletion K)
        (WithZero (Multiplicative ℤ)) :=
    Valued.v
  let F :=
    LocalFieldTheory.DiscreteValuationField.LocalField.ofWithZeroValuation
      ν
  let :
      LocalFieldTheory.DiscreteValuationField.LocalField.MixedWithZeroValuationContext
        ν :=
    LocalFieldTheory.DiscreteValuationField.LocalField.mixedWithZeroValuationContext
      ν
  let :
      Valued
        (v.adicCompletion K)
        (WithZero (Multiplicative ℤ)) :=
    Valued.mk' ν
  let p := F.residueCharacteristic
  let d :=
    Module.finrank ℚ_[p] (v.adicCompletion K)
  let e :=
    LocalFieldTheory.DiscreteValuationField.LocalField.ramificationIndexOfWithZeroValuation
      ν
  let f :=
    ValuationTheory.DiscreteValuationField.ValuedExtension.residueDegree
      (LocalFieldTheory.DiscreteValuationField.Examples.Qp.padicCompleteDVF p).toDVF
      F.toCompleteDVF.toDVF
  let k := padicValNat p (n : ℕ)
  let x : 𝓞 K := ((n : ℕ) : 𝓞 K)
  have hx : x ≠ 0 := by
    exact Nat.cast_ne_zero.mpr n.ne_zero
  have hI :
      Ideal.span {x} ≠ 0 :=
    Submodule.span_singleton_eq_bot.mp.mt hx
  have hd : d = e * f := by
    simpa [F, p, d, e, f] using
      finrank_qp_eq_ramificationIndex_mul_residueDegree
        ν (v.valuedAdicCompletion_surjective K)
  have hq : Ideal.absNorm v.asIdeal = p ^ f := by
    simpa [ν, F, p, f] using
      absNorm_eq_residueCharacteristic_pow_residueDegree
        (K := K) v
  have hcomp :
      ν ((n : ℕ) : v.adicCompletion K) =
        WithZero.exp
          (-((e : ℤ) * (k : ℤ))) := by
    simpa [F, e, k] using
      LocalFieldTheory.DiscreteValuationField.LocalField.valuation_natCast_eq_exp_neg_ramificationIndex_mul_padicValNat
        ν (n : ℕ) n.ne_zero
  have hval :
      v.intValuation x =
        WithZero.exp
          (-((e : ℤ) * (k : ℤ))) := by
    calc
      v.intValuation x =
          v.valuation K x :=
        (v.valuation_of_algebraMap
          (K := K) x).symm
      _ =
          Valued.v
            (x : v.adicCompletion K) :=
        (HeightOneSpectrum.valuedAdicCompletion_eq_valuation
          (v := v) x).symm
      _ =
          ν ((n : ℕ) : v.adicCompletion K) := by
        apply congrArg ν
        change
          algebraMap K (v.adicCompletion K) (x : K) =
            ((n : ℕ) : v.adicCompletion K)
        simp [x]
      _ = _ := hcomp
  have hexp :
      WithZero.exp
          (-(multiplicity v.asIdeal
            (Ideal.span {x}) : ℤ)) =
        WithZero.exp
          (-((e : ℤ) * (k : ℤ))) := by
    rw [← v.intValuation_eq_exp_neg_multiplicity hx]
    exact hval
  have hmult :
      multiplicity v.asIdeal
          (Ideal.span {x}) =
        e * k := by
    exact_mod_cast
      neg_injective
        (WithZero.exp_injective hexp)
  change
    p ^ (d * k) =
      Ideal.absNorm
        (v.maxPowDividing
          (Ideal.span {x}))
  calc
    p ^ (d * k) =
        p ^ ((e * f) * k) := by
      rw [hd]
    _ = p ^ (f * (e * k)) := by
      congr 1
      ac_rfl
    _ = (p ^ f) ^ (e * k) := by
      rw [pow_mul]
    _ =
        Ideal.absNorm v.asIdeal ^ (e * k) := by
      rw [hq]
    _ =
        Ideal.absNorm
          (v.asIdeal ^ (e * k)) := by
      rw [map_pow]
    _ =
        Ideal.absNorm
          (v.maxPowDividing
            (Ideal.span {x})) := by
      rw [
        HeightOneSpectrum.maxPowDividing_eq_pow_multiplicity
          hI,
        hmult]

open scoped Classical in
/-- The finite local power-index formula with the
residue-characteristic contribution packaged as
`finitePlaceNthPowerDefect`. -/
theorem card_finitePlace_nthPowerQuotient_eq_defect
    (n : ℕ+)
    (hmu : (primitiveRoots (n : ℕ) K).Nonempty)
    (v₀ : HeightOneSpectrum (𝓞 K)) :
    Nat.card
        ((v₀.adicCompletion K)ˣ ⧸
          (powMonoidHom (n : ℕ) :
            (v₀.adicCompletion K)ˣ →*
              (v₀.adicCompletion K)ˣ).range) =
      (n : ℕ) *
        ((n : ℕ) *
          finitePlaceNthPowerDefect (K := K) n v₀) := by
  simpa [finitePlaceNthPowerDefect] using
    card_finitePlace_nthPowerQuotient
      (K := K) n hmu v₀


end GlobalClassFieldTheory.ClassFieldAxiom
