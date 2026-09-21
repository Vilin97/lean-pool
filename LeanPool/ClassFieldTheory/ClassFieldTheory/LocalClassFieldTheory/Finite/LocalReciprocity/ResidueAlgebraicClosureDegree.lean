/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/

import LeanPool.ClassFieldTheory.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.ResidueAbsoluteDegree
import LeanPool.ClassFieldTheory.ValuedFieldTheory.Ramification.GaloisValuation.AbsoluteGalois.InfiniteGaloisCorrespondence

/-! # Residue Algebraic Closure Degree -/
namespace LocalClassFieldTheory

open ClassFormation

/-!
# Finite local reciprocity: degree coordinates on any residue algebraic closure

The residue field obtained from a valuation ring in a separable closure is
not definitionally Mathlib's chosen `AlgebraicClosure`.  The construction of
the degree map must therefore work on any algebraically closed algebraic
extension of the finite residue field.

This file repeats the inverse-limit detection argument in that intrinsic
setting.  The resulting map is the inverse of the canonical arithmetic
Frobenius homomorphism itself; no equivalence with a chosen algebraic closure
and no generator of a finite cyclic group enters its definition.
-/

noncomputable section

universe u v

open CategoryTheory Opposite
open FiniteGaloisIntermediateField ProfiniteGrp
open RamificationTheory.Field.absoluteGaloisGroup
open Polynomial

variable (k : Type u) [Field k] [Fintype k]
variable (Omega : Type v) [Field Omega] [Algebra k Omega]
  [Algebra.IsAlgebraic k Omega] [IsAlgClosed Omega]

private instance finiteResidueBaseRingCharPrime : Fact (ringChar k).Prime :=
  ⟨CharP.char_is_prime k (ringChar k)⟩

private instance residueAlgebraicClosureIsAlgClosure : IsAlgClosure k Omega :=
  ⟨inferInstance, inferInstance⟩

private instance residueAlgebraicClosureIsGalois : IsGalois k Omega := by
  infer_instance

private instance residueAlgebraicClosureGaloisT2 :
    T2Space (Omega ≃ₐ[k] Omega) := by
  infer_instance

/-- Embed the degree-`n` finite extension of `k` into the given residue
algebraic closure.  This choice is used only to prove that all profinite
coordinates are detected. -/
noncomputable def finiteResidueExtensionEmbeddingInto
    (n : ℕ) [NeZero n] :
    FiniteField.Extension k (ringChar k) n →ₐ[k] Omega := by
  letI : Module.IsTorsionFree k Omega :=
    Module.isTorsionFree_iff_algebraMap_injective.mpr
      (algebraMap k Omega).injective
  exact IsAlgClosed.lift (R := k)
    (S := FiniteField.Extension k (ringChar k) n) (M := Omega)

/-- The image of the degree-`n` finite extension in the given residue
algebraic closure. -/
noncomputable def finiteResidueIntermediateFieldIn
    (n : ℕ) [NeZero n] : IntermediateField k Omega :=
  (⊤ : IntermediateField k
      (FiniteField.Extension k (ringChar k) n)).map
    (finiteResidueExtensionEmbeddingInto k Omega n)

/-- The model finite field is canonically isomorphic to its embedded image. -/
noncomputable def finiteResidueExtensionEquivIntermediateIn
    (n : ℕ) [NeZero n] :
    FiniteField.Extension k (ringChar k) n ≃ₐ[k]
      finiteResidueIntermediateFieldIn k Omega n :=
  IntermediateField.topEquiv.symm.trans
    (IntermediateField.equivMap ⊤
      (finiteResidueExtensionEmbeddingInto k Omega n))

/-- An actual degree-`n` finite Galois intermediate field in any residue
algebraic closure. -/
noncomputable def finiteResidueGaloisIntermediateFieldIn
    (n : ℕ) [NeZero n] : FiniteGaloisIntermediateField k Omega where
  toIntermediateField := finiteResidueIntermediateFieldIn k Omega n
  finiteDimensional := Module.Finite.equiv
    (finiteResidueExtensionEquivIntermediateIn k Omega n).toLinearEquiv
  isGalois := IsGalois.of_algEquiv
    (finiteResidueExtensionEquivIntermediateIn k Omega n)

omit [Algebra.IsAlgebraic k Omega] in
/-- States the theorem `finrank_finiteResidueGaloisIntermediateFieldIn`. -/
@[simp]
theorem finrank_finiteResidueGaloisIntermediateFieldIn
    (n : ℕ) [NeZero n] :
    Module.finrank k
        (finiteResidueGaloisIntermediateFieldIn k Omega n) = n := by
  calc
    Module.finrank k
        (finiteResidueGaloisIntermediateFieldIn k Omega n) =
        Module.finrank k
          (FiniteField.Extension k (ringChar k) n) :=
      (finiteResidueExtensionEquivIntermediateIn k Omega n).toLinearEquiv.finrank_eq.symm
    _ = n := FiniteField.finrank_extension k (ringChar k) n

/-- Finite subextensions of every positive degree detect every coordinate of
the canonical Frobenius homomorphism on an arbitrary residue algebraic
closure. -/
theorem residueAbsoluteFrobenius_isAlgClosure_injective :
    Function.Injective (residueAbsoluteFrobenius k Omega) := by
  intro z w hzw
  apply Multiplicative.ext
  apply ZHat.ext
  intro n hn
  let : NeZero n := ⟨Nat.ne_of_gt hn⟩
  let E := finiteResidueGaloisIntermediateFieldIn k Omega n
  have hrestriction := congrArg (AlgEquiv.restrictNormalHom E) hzw
  rw [restrictNormalHom_residueAbsoluteFrobenius (z := z) (E := E),
    restrictNormalHom_residueAbsoluteFrobenius (z := w) (E := E)] at hrestriction
  let : Finite E := Module.finite_of_finite k
  change finiteResidueFrobeniusFromZHat k E z =
    finiteResidueFrobeniusFromZHat k E w at hrestriction
  rw [finiteResidueFrobeniusFromZHat_apply,
    finiteResidueFrobeniusFromZHat_apply] at hrestriction
  have hcoordinate := congrArg Multiplicative.toAdd
    (finiteResidueFrobeniusExponentHom_injective k E hrestriction)
  have hdegree : Module.finrank k E = n := by
    exact finrank_finiteResidueGaloisIntermediateFieldIn
      k Omega n
  simp only [toAdd_ofAdd] at hcoordinate
  change zHatReduction (Module.finrank k E) Module.finrank_pos z.toAdd =
    zHatReduction (Module.finrank k E) Module.finrank_pos w.toAdd at hcoordinate
  have hdiv : n ∣ Module.finrank k E := by simp [hdegree]
  have hcast := congrArg (ZMod.castHom hdiv (ZMod n)) hcoordinate
  rw [zHatReduction_transition hn Module.finrank_pos hdiv z.toAdd,
    zHatReduction_transition hn Module.finrank_pos hdiv w.toAdd] at hcast
  exact hcast

omit [IsAlgClosed Omega] in
/-- In any algebraic closure of a finite field, the fixed points of arithmetic
Frobenius are exactly the base field. -/
theorem mem_range_algebraMap_iff_frobenius_fixed_in
    (x : Omega) :
    x ∈ Set.range (algebraMap k Omega) ↔
      FiniteField.frobeniusAlgEquivOfAlgebraic k Omega x = x := by
  constructor
  · rintro ⟨a, rfl⟩
    simp only [FiniteField.coe_frobeniusAlgEquivOfAlgebraic]
    rw [← map_pow, FiniteField.pow_card]
  · intro hx
    have hxpow : x ^ Fintype.card k = x := by
      simpa only [FiniteField.coe_frobeniusAlgEquivOfAlgebraic] using hx
    let p : k[X] := X ^ Fintype.card k - X
    have hpne : p ≠ 0 :=
      FiniteField.X_pow_card_sub_X_ne_zero k Fintype.one_lt_card
    have hxroot : x ∈ p.rootSet Omega := by
      rw [Polynomial.mem_rootSet_of_ne hpne]
      simp [p, hxpow]
    have hsplits : (p.map (algebraMap k k)).Splits := by
      simpa only [p] using (FiniteField.isSplittingField_sub k k).splits
    have himage := hsplits.image_rootSet (Algebra.ofId k Omega)
    rw [← himage] at hxroot
    rcases hxroot with ⟨a, _ha, hax⟩
    exact ⟨a, hax⟩

/-- The compact image of the intrinsic Frobenius homomorphism. -/
noncomputable def residueAbsoluteFrobeniusRangeIn :
    ClosedSubgroup (Omega ≃ₐ[k] Omega) where
  toSubgroup := (residueAbsoluteFrobenius k Omega).toMonoidHom.range
  isClosed' := by
    change IsClosed (Set.range (residueAbsoluteFrobenius k Omega))
    exact (isCompact_range
      (residueAbsoluteFrobenius k Omega).continuous_toFun).isClosed

/-- The compact Frobenius image fixes precisely the finite base field. -/
theorem fixedField_residueAbsoluteFrobeniusRangeIn :
    IntermediateField.fixedField
        (residueAbsoluteFrobeniusRangeIn k Omega).toSubgroup = ⊥ := by
  apply le_antisymm
  · intro x hx
    have hfrobenius_mem :
        FiniteField.frobeniusAlgEquivOfAlgebraic k Omega ∈
          residueAbsoluteFrobeniusRangeIn k Omega := by
      change FiniteField.frobeniusAlgEquivOfAlgebraic k Omega ∈
        (residueAbsoluteFrobenius k Omega).toMonoidHom.range
      exact ⟨Multiplicative.ofAdd (1 : ZHat),
        residueAbsoluteFrobenius_one k Omega⟩
    rw [IntermediateField.mem_fixedField_iff] at hx
    have hxFrobenius := hx
      (FiniteField.frobeniusAlgEquivOfAlgebraic k Omega)
      hfrobenius_mem
    rw [IntermediateField.mem_bot]
    exact (mem_range_algebraMap_iff_frobenius_fixed_in k Omega x).mpr
      hxFrobenius
  · exact bot_le

/-- The intrinsic Frobenius image is the whole residue absolute Galois group. -/
theorem residueAbsoluteFrobeniusRangeIn_eq_top :
    (residueAbsoluteFrobeniusRangeIn k Omega).toSubgroup = ⊤ := by
  have hfixed := InfiniteGalois.fixingSubgroup_fixedField
    (residueAbsoluteFrobeniusRangeIn k Omega)
  rw [fixedField_residueAbsoluteFrobeniusRangeIn,
    IntermediateField.fixingSubgroup_bot] at hfixed
  exact hfixed.symm

/-- The intrinsic Frobenius homomorphism is surjective. -/
theorem residueAbsoluteFrobenius_isAlgClosure_surjective :
    Function.Surjective (residueAbsoluteFrobenius k Omega) := by
  intro sigma
  have hsigma : sigma ∈
      (residueAbsoluteFrobeniusRangeIn k Omega).toSubgroup := by
    rw [residueAbsoluteFrobeniusRangeIn_eq_top]
    exact Subgroup.mem_top sigma
  exact hsigma

/-- Arithmetic Frobenius gives the canonical topological equivalence between
`ZHatMul` and the Galois group of any algebraic closure of a finite field. -/
noncomputable def residueAbsoluteFrobeniusEquivIn :
    ZHatMul ≃ₜ* (Omega ≃ₐ[k] Omega) where
  toMulEquiv := MulEquiv.ofBijective
    (residueAbsoluteFrobenius k Omega).toMonoidHom
    ⟨residueAbsoluteFrobenius_isAlgClosure_injective k Omega,
      residueAbsoluteFrobenius_isAlgClosure_surjective k Omega⟩
  continuous_toFun := (residueAbsoluteFrobenius k Omega).continuous_toFun
  continuous_invFun :=
    Continuous.continuous_symm_of_equiv_compact_to_t2
      (f := (MulEquiv.ofBijective
        (residueAbsoluteFrobenius k Omega).toMonoidHom
        ⟨residueAbsoluteFrobenius_isAlgClosure_injective k Omega,
          residueAbsoluteFrobenius_isAlgClosure_surjective k Omega⟩).toEquiv)
      (residueAbsoluteFrobenius k Omega).continuous_toFun

/-- **Finite local reciprocity, intrinsic residue degree.**  This is the inverse of
arithmetic Frobenius coordinates on the actual residue algebraic closure. -/
noncomputable def residueAbsoluteDegreeIn :
    (Omega ≃ₐ[k] Omega) →ₜ* ZHatMul :=
  ContinuousMonoidHom.toContinuousMonoidHom
    (residueAbsoluteFrobeniusEquivIn k Omega).symm

/-- Intrinsic residue degree is unchanged by simultaneous semilinear
equivalence of the finite residue base and its algebraic closure.  The
conjugate automorphism is written locally in the statement, so no parallel
restriction or automorphism-conjugation API is introduced. -/
theorem residueAbsoluteDegreeIn_semilinear_conjugation
    {k' : Type u} {Omega' : Type v}
    [Field k'] [Fintype k']
    [Field Omega'] [Algebra k' Omega']
    [Algebra.IsAlgebraic k' Omega'] [IsAlgClosed Omega']
    (tau : k ≃+* k') (e : Omega ≃+* Omega')
    (he : ∀ x : k,
      e (algebraMap k Omega x) = algebraMap k' Omega' (tau x))
    (sigma : Omega ≃ₐ[k] Omega) :
    let sigma' : Omega' ≃ₐ[k'] Omega' :=
      { e.symm.trans (sigma.toRingEquiv.trans e) with
        commutes' := fun x => by
          change e (sigma (e.symm (algebraMap k' Omega' x))) =
            algebraMap k' Omega' x
          have hpre :
              e.symm (algebraMap k' Omega' x) =
                algebraMap k Omega (tau.symm x) := by
            apply e.injective
            rw [e.apply_symm_apply, he, tau.apply_symm_apply]
          rw [hpre, sigma.commutes, he, tau.apply_symm_apply] }
    residueAbsoluteDegreeIn k' Omega' sigma' =
      residueAbsoluteDegreeIn k Omega sigma := by
  let conjugate (g : Omega ≃ₐ[k] Omega) :
      Omega' ≃ₐ[k'] Omega' :=
    AlgEquiv.ofRingEquiv
      (f := e.symm.trans (g.toRingEquiv.trans e)) (fun x => by
        change e (g (e.symm (algebraMap k' Omega' x))) =
          algebraMap k' Omega' x
        have hpre :
            e.symm (algebraMap k' Omega' x) =
              algebraMap k Omega (tau.symm x) := by
          apply e.injective
          rw [e.apply_symm_apply, he, tau.apply_symm_apply]
        rw [hpre, g.commutes, he, tau.apply_symm_apply])
  have conjugate_one : conjugate 1 = 1 := by
    apply AlgEquiv.ext
    intro x
    simp [conjugate]
  have conjugate_mul (g h : Omega ≃ₐ[k] Omega) :
      conjugate (g * h) = conjugate g * conjugate h := by
    apply AlgEquiv.ext
    intro x
    simp [conjugate, AlgEquiv.mul_apply]
  let conjugation :
      (Omega ≃ₐ[k] Omega) →* (Omega' ≃ₐ[k'] Omega') :=
    { toFun := conjugate
      map_one' := conjugate_one
      map_mul' := conjugate_mul }
  let conjugationContinuous :
      (Omega ≃ₐ[k] Omega) →ₜ* (Omega' ≃ₐ[k'] Omega') :=
    { toMonoidHom := conjugation
      continuous_toFun :=
        RamificationTheory.Field.absoluteGaloisGroup.semilinear_conjugation_continuous
          tau e he conjugation (fun _ => rfl) }
  let lhs : ZHatMul →ₜ* (Omega' ≃ₐ[k'] Omega') :=
    conjugationContinuous.comp (residueAbsoluteFrobenius k Omega)
  let rhs : ZHatMul →ₜ* (Omega' ≃ₐ[k'] Omega') :=
    residueAbsoluteFrobenius k' Omega'
  have hgenerator :
      lhs (Multiplicative.ofAdd (1 : ZHat)) =
        rhs (Multiplicative.ofAdd (1 : ZHat)) := by
    change conjugation
        (residueAbsoluteFrobenius k Omega
          (Multiplicative.ofAdd (1 : ZHat))) =
      residueAbsoluteFrobenius k' Omega'
        (Multiplicative.ofAdd (1 : ZHat))
    rw [residueAbsoluteFrobenius_one, residueAbsoluteFrobenius_one]
    apply AlgEquiv.ext
    intro x
    change e ((e.symm x) ^ Fintype.card k) =
      x ^ Fintype.card k'
    rw [map_pow, e.apply_symm_apply,
      Fintype.card_congr tau.toEquiv]
  let iota : Multiplicative ℤ →* ZHatMul :=
    AddMonoidHom.toMultiplicative
      (Int.castRingHom ZHat).toAddMonoidHom
  have hiota : DenseRange iota := by
    have hOfAdd :
        DenseRange (Multiplicative.ofAdd : ZHat → ZHatMul) :=
      (show Function.Surjective
          (Multiplicative.ofAdd : ZHat → ZHatMul) from
        fun x => ⟨Multiplicative.toAdd x, rfl⟩).denseRange
    have hCast :
        DenseRange
          (Multiplicative.ofAdd ∘ fun a : ℤ => (a : ZHat)) :=
      hOfAdd.comp denseRange_intCast_zHat continuous_id
    have hToAdd :
        DenseRange (Multiplicative.toAdd : Multiplicative ℤ → ℤ) :=
      (show Function.Surjective
          (Multiplicative.toAdd : Multiplicative ℤ → ℤ) from
        fun a => ⟨Multiplicative.ofAdd a, rfl⟩).denseRange
    simpa [iota, Function.comp_def] using
      hCast.comp hToAdd continuous_of_discreteTopology
  have hcomp :
      lhs.toMonoidHom.comp iota = rhs.toMonoidHom.comp iota := by
    apply MonoidHom.ext_mint
    simpa [iota] using hgenerator
  have heq (w : ZHatMul) : lhs w = rhs w := by
    have hfun :=
      hiota.equalizer lhs.continuous_toFun rhs.continuous_toFun <| by
        funext n
        exact DFunLike.congr_fun hcomp n
    exact congrFun hfun w
  let z := residueAbsoluteDegreeIn k Omega sigma
  have hz :
      conjugation (residueAbsoluteFrobenius k Omega z) =
        residueAbsoluteFrobenius k' Omega' z := by
    exact heq z
  apply (residueAbsoluteFrobeniusEquivIn k' Omega').injective
  change
    (residueAbsoluteFrobeniusEquivIn k' Omega')
        ((residueAbsoluteFrobeniusEquivIn k' Omega').symm
          (conjugation sigma)) =
      (residueAbsoluteFrobeniusEquivIn k' Omega')
        ((residueAbsoluteFrobeniusEquivIn k Omega).symm sigma)
  rw [(residueAbsoluteFrobeniusEquivIn k' Omega').apply_symm_apply]
  change conjugation sigma =
    residueAbsoluteFrobenius k' Omega' z
  have hsigma :
      sigma = residueAbsoluteFrobenius k Omega z := by
    change sigma =
      (residueAbsoluteFrobeniusEquivIn k Omega)
        ((residueAbsoluteFrobeniusEquivIn k Omega).symm sigma)
    exact
      ((residueAbsoluteFrobeniusEquivIn k Omega).apply_symm_apply sigma).symm
  exact (congrArg conjugation hsigma).trans hz

/-- Arithmetic Frobenius is compatible with changing the finite residue
base from `k` to a finite intermediate field `E`: after forgetting the
`E`-linear structure, the Frobenius coordinate is multiplied by
`[E : k]`. -/
theorem residueAbsoluteFrobenius_restrictScalars
    (E : IntermediateField k Omega) [FiniteDimensional k E]
    (z : ZHatMul) :
    letI : Finite E := Module.finite_of_finite k
    letI : Fintype E := Fintype.ofFinite E
    (residueAbsoluteFrobenius E Omega z).restrictScalars k =
      residueAbsoluteFrobenius k Omega
        (Multiplicative.ofAdd
          ((Module.finrank k E) • z.toAdd)) := by
  let : Finite E := Module.finite_of_finite k
  let : Fintype E := Fintype.ofFinite E
  let scaleHom : ZHatMul →* ZHatMul :=
    AddMonoidHom.toMultiplicative
      (zHatMulNat (Module.finrank k E)).toAddMonoidHom
  let scale : ZHatMul →ₜ* ZHatMul :=
    { toMonoidHom := scaleHom
      continuous_toFun :=
        continuous_ofAdd.comp
          ((zHatMulNat (Module.finrank k E)).continuous_toFun.comp
            continuous_toAdd) }
  let inclusion : (Omega ≃ₐ[E] Omega) →ₜ* (Omega ≃ₐ[k] Omega) :=
    { toMonoidHom := ofIntermediateFieldInExtension E
      continuous_toFun := ofIntermediateFieldInExtension_continuous E }
  let lhs : ZHatMul →ₜ* (Omega ≃ₐ[k] Omega) :=
    inclusion.comp (residueAbsoluteFrobenius E Omega)
  let rhs : ZHatMul →ₜ* (Omega ≃ₐ[k] Omega) :=
    (residueAbsoluteFrobenius k Omega).comp scale
  have hgenerator :
      lhs (Multiplicative.ofAdd (1 : ZHat)) =
        rhs (Multiplicative.ofAdd (1 : ZHat)) := by
    change
      (residueAbsoluteFrobenius E Omega
          (Multiplicative.ofAdd (1 : ZHat))).restrictScalars k =
        residueAbsoluteFrobenius k Omega
          (Multiplicative.ofAdd
            ((Module.finrank k E) • (1 : ZHat)))
    rw [residueAbsoluteFrobenius_one]
    have hscale :
        Multiplicative.ofAdd
            ((Module.finrank k E) • (1 : ZHat)) =
          (Multiplicative.ofAdd (1 : ZHat)) ^ Module.finrank k E := by
      apply Multiplicative.ext
      simp
    rw [hscale, map_pow, residueAbsoluteFrobenius_one]
    apply AlgEquiv.ext
    intro x
    change
      FiniteField.frobeniusAlgEquivOfAlgebraic E Omega x =
        (FiniteField.frobeniusAlgEquivOfAlgebraic k Omega ^
          Module.finrank k E) x
    rw [FiniteField.coe_frobeniusAlgEquivOfAlgebraic,
      AlgEquiv.coe_pow,
      FiniteField.coe_frobeniusAlgEquivOfAlgebraic_iterate,
      Module.card_eq_pow_finrank (K := k) (V := E)]
  let iota : Multiplicative ℤ →* ZHatMul :=
    AddMonoidHom.toMultiplicative
      (Int.castRingHom ZHat).toAddMonoidHom
  have hiota : DenseRange iota := by
    have hOfAdd :
        DenseRange (Multiplicative.ofAdd : ZHat → ZHatMul) :=
      (show Function.Surjective
          (Multiplicative.ofAdd : ZHat → ZHatMul) from
        fun x => ⟨Multiplicative.toAdd x, rfl⟩).denseRange
    have hCast :
        DenseRange
          (Multiplicative.ofAdd ∘ fun a : ℤ => (a : ZHat)) :=
      hOfAdd.comp denseRange_intCast_zHat continuous_id
    have hToAdd :
        DenseRange (Multiplicative.toAdd : Multiplicative ℤ → ℤ) :=
      (show Function.Surjective
          (Multiplicative.toAdd : Multiplicative ℤ → ℤ) from
        fun a => ⟨Multiplicative.ofAdd a, rfl⟩).denseRange
    simpa [iota, Function.comp_def] using
      hCast.comp hToAdd continuous_of_discreteTopology
  have hcomp :
      lhs.toMonoidHom.comp iota = rhs.toMonoidHom.comp iota := by
    apply MonoidHom.ext_mint
    simpa [iota] using hgenerator
  have heq (w : ZHatMul) : lhs w = rhs w := by
    have hfun :=
      hiota.equalizer lhs.continuous_toFun rhs.continuous_toFun <| by
        funext n
        exact DFunLike.congr_fun hcomp n
    exact congrFun hfun w
  exact heq z

/-- The intrinsic absolute residue degree has the corresponding
finite-base-change formula. -/
theorem residueAbsoluteDegreeIn_restrictScalars
    (E : IntermediateField k Omega) [FiniteDimensional k E]
    (sigma : Omega ≃ₐ[E] Omega) :
    letI : Finite E := Module.finite_of_finite k
    letI : Fintype E := Fintype.ofFinite E
    residueAbsoluteDegreeIn k Omega (sigma.restrictScalars k) =
      Multiplicative.ofAdd
        ((Module.finrank k E) •
          (residueAbsoluteDegreeIn E Omega sigma).toAdd) := by
  let : Finite E := Module.finite_of_finite k
  let : Fintype E := Fintype.ofFinite E
  apply (residueAbsoluteFrobeniusEquivIn k Omega).injective
  change
    (residueAbsoluteFrobeniusEquivIn k Omega)
        ((residueAbsoluteFrobeniusEquivIn k Omega).symm
          (sigma.restrictScalars k)) =
      (residueAbsoluteFrobeniusEquivIn k Omega)
        (Multiplicative.ofAdd
          ((Module.finrank k E) •
            ((residueAbsoluteFrobeniusEquivIn E Omega).symm sigma).toAdd))
  rw [(residueAbsoluteFrobeniusEquivIn k Omega).apply_symm_apply]
  change sigma.restrictScalars k =
    residueAbsoluteFrobenius k Omega
      (Multiplicative.ofAdd
        ((Module.finrank k E) •
          ((residueAbsoluteFrobeniusEquivIn E Omega).symm sigma).toAdd))
  rw [← residueAbsoluteFrobenius_restrictScalars]
  exact congrArg (fun g : Omega ≃ₐ[E] Omega => g.restrictScalars k)
    ((residueAbsoluteFrobeniusEquivIn E Omega).apply_symm_apply sigma).symm

/-- The intrinsic degree map sends arithmetic Frobenius to `1`. -/
@[simp]
theorem residueAbsoluteDegreeIn_frobenius :
    residueAbsoluteDegreeIn k Omega
        (FiniteField.frobeniusAlgEquivOfAlgebraic k Omega) =
      Multiplicative.ofAdd (1 : ZHat) := by
  apply (residueAbsoluteFrobeniusEquivIn k Omega).injective
  change (residueAbsoluteFrobeniusEquivIn k Omega)
      ((residueAbsoluteFrobeniusEquivIn k Omega).symm
        (FiniteField.frobeniusAlgEquivOfAlgebraic k Omega)) =
    (residueAbsoluteFrobeniusEquivIn k Omega)
      (Multiplicative.ofAdd (1 : ZHat))
  rw [(residueAbsoluteFrobeniusEquivIn k Omega).apply_symm_apply]
  exact (residueAbsoluteFrobenius_one k Omega).symm

/-- Finite-coordinate compatibility for the intrinsic residue degree. -/
theorem finiteResidueFrobeniusExponentEquiv_symm_restrict_in
    (sigma : Omega ≃ₐ[k] Omega)
    (E : FiniteGaloisIntermediateField k Omega) :
    letI : Finite E := Module.finite_of_finite k
    (finiteResidueFrobeniusExponentEquiv k E).symm
        (AlgEquiv.restrictNormalHom E sigma) =
      Multiplicative.ofAdd
        (zHatReduction (Module.finrank k E) Module.finrank_pos
          (residueAbsoluteDegreeIn k Omega sigma).toAdd) := by
  let : Finite E := Module.finite_of_finite k
  apply (finiteResidueFrobeniusExponentEquiv k E).injective
  rw [(finiteResidueFrobeniusExponentEquiv k E).apply_symm_apply]
  change AlgEquiv.restrictNormalHom E sigma =
    finiteResidueFrobeniusIntermediate k Omega E
      (residueAbsoluteDegreeIn k Omega sigma)
  rw [← restrictNormalHom_residueAbsoluteFrobenius]
  congr 1
  exact ((residueAbsoluteFrobeniusEquivIn k Omega).apply_symm_apply sigma).symm

end
end LocalClassFieldTheory
