/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/
module


public import LeanPool.ClassFieldTheory.ClassFieldTheory.GlobalClassFieldTheory.Reciprocity.PowerResidueReciprocity
/-!
# Rational quadratic reciprocity from global class field theory

The dyadic correction specializes power-residue reciprocity over `ℚ` and
derives Gauss's quadratic reciprocity law.
-/

@[expose] public section

open scoped BigOperators NumberField NumberTheorySymbols ValuativeRel WithZero
open NumberField IsDedekindDomain

noncomputable
section

namespace GlobalClassFieldTheory
namespace Reciprocity

-- Specializing the generic completion construction to `ℚ` must keep the
-- `Algebra.id` owner fixed.  Otherwise the rational-field algebra path is
-- underdetermined during instance synthesis.
open scoped Classical in
/-- The rational scalar action on a finite-place completion, with the identity algebra on the base
field fixed. -/
@[reducible] noncomputable local instance rationalQuadraticCompletionAlgebra
    (v : HeightOneSpectrum (𝓞 ℚ)) :
    Algebra ℚ (HeightOneSpectrum.adicAbv ℚ v).Completion := by
  letI : Algebra ℚ ℚ := Algebra.id ℚ
  let hWith : Algebra ℚ
      (WithAbs (HeightOneSpectrum.adicAbv ℚ v)) :=
    WithAbs.instAlgebra _
  let hUniform : UniformContinuousConstSMul ℚ
      (WithAbs (HeightOneSpectrum.adicAbv ℚ v)) :=
    WithAbs.instUniformContinuousConstSMulReal _
  exact
    @UniformSpace.Completion.algebra
      (WithAbs (HeightOneSpectrum.adicAbv ℚ v)) _ _ _ _
      ℚ _ hWith hUniform

attribute [local instance] rationalQuadraticCompletionAlgebra

open KummerTheory
open AlgebraicNumberTheory.PowerResidueSymbols
open LocalClassFieldTheory.Kummer
open LocalFieldTheory
open LocalFieldTheory.IsNonarchimedeanLocalField

open scoped Classical in
private def rationalQuadraticRootValuePNatMonoidHom :
    rootsOfUnity (((2 : ℕ+) : ℕ)) (𝓞 ℚ) →* ℤ := by
  change rootsOfUnity 2 (𝓞 ℚ) →* ℤ
  exact rationalQuadraticRootValueMonoidHom

/-! ## Dyadic correction and Gauss reciprocity -/

open scoped Classical in
/-- The rational prime above two, used throughout the dyadic specialization. -/
def rationalTwoPrime : Nat.Primes := ⟨2, Nat.prime_two⟩

open scoped Classical in
/-- Identify the completion at the rational prime above two with the corresponding indexed
p-adic field. -/
noncomputable def rationalTwoAdicCompletionToIndexedPadic :
    (RayClass.rationalPrime rationalTwoPrime).adicCompletion ℚ ≃+*
      ℚ_[Rat.HeightOneSpectrum.primesEquiv
        (RayClass.rationalPrime rationalTwoPrime)] :=
  (IsDedekindDomain.HeightOneSpectrum.adicCompletion.equiv ℚ
      (RayClass.rationalPrime rationalTwoPrime)).trans
    ((UniformSpace.Completion.mapRingEquiv
        (WithVal.congr
          (IsDedekindDomain.HeightOneSpectrum.valuation ℚ
            (RayClass.rationalPrime rationalTwoPrime))
          (Rat.padicValuation
            (Rat.HeightOneSpectrum.primesEquiv
              (RayClass.rationalPrime rationalTwoPrime)))
          (RingEquiv.refl ℚ))
        (Rat.HeightOneSpectrum.withValEquiv
          (RayClass.rationalPrime rationalTwoPrime)).continuous
        (Rat.HeightOneSpectrum.withValEquiv
          (RayClass.rationalPrime rationalTwoPrime)).symm.continuous).trans
      Padic.withValRingEquiv)

open scoped Classical in
/-- The absolute-value completion at the rational prime above two is
canonically the usual field of `2`-adic numbers. -/
noncomputable def rationalTwoAdicCompletionEquivPadic :
    (HeightOneSpectrum.adicAbv ℚ
        (RayClass.rationalPrime rationalTwoPrime)).Completion ≃+* ℚ_[2] :=
  (finitePlaceCompletionRingEquiv
      (RayClass.rationalPrime rationalTwoPrime)).trans
    (rationalTwoAdicCompletionToIndexedPadic.trans
      (show
          ℚ_[Rat.HeightOneSpectrum.primesEquiv
              (RayClass.rationalPrime rationalTwoPrime)] ≃+*
            ℚ_[rationalTwoPrime] from
        RingEquiv.cast (R := fun p : Nat.Primes => ℚ_[p.1])
          ((Rat.HeightOneSpectrum.primesEquiv
            (R := 𝓞 ℚ)).apply_symm_apply rationalTwoPrime)))

open scoped Classical in
/-- A natural number in the rational ring of integers. -/
noncomputable def rationalNatInteger (m : ℕ) : 𝓞 ℚ :=
  Rat.ringOfIntegersEquiv.symm (m : ℤ)

open scoped Classical in
@[simp]
theorem rationalNatInteger_equiv (m : ℕ) :
    Rat.ringOfIntegersEquiv (rationalNatInteger m) = (m : ℤ) :=
  Rat.ringOfIntegersEquiv.apply_symm_apply (m : ℤ)

open scoped Classical in
@[simp]
theorem rationalNatInteger_coe (m : ℕ) :
    (rationalNatInteger m : ℚ) = (m : ℚ) := by
  exact Rat.ringOfIntegersEquiv_symm_apply_coe (m : ℤ)

open scoped Classical in
/-- A positive natural number, regarded canonically as a rational field unit. -/
noncomputable def rationalNaturalFieldUnit
    (m : ℕ) (hm : m ≠ 0) : ℚˣ :=
  nonzeroIntegralFieldUnit ℚ (rationalNatInteger m) (by
    intro h
    apply Int.ofNat_ne_zero.mpr hm
    simpa [rationalNatInteger_equiv] using
      congrArg Rat.ringOfIntegersEquiv h)

open scoped Classical in
@[simp]
theorem rationalNaturalFieldUnit_coe
    (m : ℕ) (hm : m ≠ 0) :
    (rationalNaturalFieldUnit m hm : ℚ) = (m : ℚ) := by
  exact rationalNatInteger_coe m

open scoped Classical in
/-- The negative quadratic integral root of unity over `ℚ`. -/
def rationalQuadraticNegOneRoot : rootsOfUnity 2 (𝓞 ℚ) :=
  ⟨-1, by norm_num⟩

open scoped Classical in
@[simp]
theorem rationalQuadraticRootValue_negOneRoot :
    rationalQuadraticRootValue rationalQuadraticNegOneRoot = -1 := by
  simp [rationalQuadraticRootValue, rationalQuadraticNegOneRoot]

open scoped Classical in
/-- For exponent two, the exponent ideal is the rational principal ideal
generated by two. -/
theorem powerResidueExponentIdeal_rational_two :
    powerResidueExponentIdeal ℚ (2 : ℕ+) = rationalPrincipalIdeal 2 := by
  unfold powerResidueExponentIdeal rationalPrincipalIdeal
  congr 2
  apply Rat.ringOfIntegersEquiv.injective
  simp

open scoped Classical in
/-- The only finite exponent place in the rational quadratic specialization
is the prime above two. -/
theorem powerResidueExponentFinitePlaces_rational_two :
    powerResidueExponentFinitePlaces ℚ (2 : ℕ+) =
      {RayClass.rationalPrime rationalTwoPrime} := by
  ext v
  rw [Finset.mem_singleton,
    mem_powerResidueExponentFinitePlaces_iff,
    powerResidueExponentIdeal_rational_two]
  let p : Nat.Primes :=
    Rat.HeightOneSpectrum.primesEquiv (R := 𝓞 ℚ) v
  have hpv : RayClass.rationalPrime p = v :=
    (Rat.HeightOneSpectrum.primesEquiv
      (R := 𝓞 ℚ)).symm_apply_apply v
  constructor
  · intro hvDvd
    have hpDvd : p.1 ∣ 2 := by
      apply (rationalPrime_dvd_rationalPrincipalIdeal_iff p 2).mp
      simpa only [hpv] using hvDvd
    have hpEq : p = rationalTwoPrime := by
      apply Subtype.ext
      exact (Nat.prime_dvd_prime_iff_eq p.2 Nat.prime_two).mp hpDvd
    exact hpv.symm.trans (congrArg RayClass.rationalPrime hpEq)
  · intro hv
    rw [hv]
    apply (rationalPrime_dvd_rationalPrincipalIdeal_iff
      rationalTwoPrime 2).mpr
    change 2 ∣ 2
    exact dvd_rfl

open scoped Classical in
/-- The sign-normalized odd integer used in the dyadic square-class
calculation, regarded as a unit of `ℚ₂`. -/
noncomputable def rationalTwoAdicSignedOddUnit
    (m : ℕ) (hm : Odd m) : ℚ_[2]ˣ :=
  Units.mk0
    ((((-1 : ℤ) ^ (m / 2) * (m : ℤ)) : ℤ) : ℚ_[2]) (by
      exact_mod_cast
        mul_ne_zero (pow_ne_zero _ (by norm_num : (-1 : ℤ) ≠ 0))
          (Int.ofNat_ne_zero.mpr (by
            intro hm0
            subst m
            norm_num at hm)))

open scoped Classical in
@[simp]
theorem rationalTwoAdicSignedOddUnit_coe
    (m : ℕ) (hm : Odd m) :
    (rationalTwoAdicSignedOddUnit m hm : ℚ_[2]) =
      (((-1 : ℤ) ^ (m / 2) * (m : ℤ) : ℤ) : ℚ_[2]) :=
  rfl

open scoped Classical in
/-- A sign-normalized odd rational integer is, in `ℚ₂`, either a square or
five times a square.  This is the exact dyadic square-class input needed for
the quadratic Hilbert correction. -/
theorem rationalTwoAdicSignedOddUnit_squareClass
    (m : ℕ) (hm : Odd m) :
    let five : ℚ_[2]ˣ := Units.mk0 (5 : ℚ_[2]) (by norm_num)
    ∃ r : ℚ_[2]ˣ,
      rationalTwoAdicSignedOddUnit m hm = r ^ 2 ∨
        rationalTwoAdicSignedOddUnit m hm = five * r ^ 2 := by
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let q : ℤ := (-1 : ℤ) ^ (m / 2) * (m : ℤ)
  have hmInt : Odd (m : ℤ) := by exact_mod_cast hm
  have hqData : Odd q ∧ ∃ k : ℤ, q - 1 = 4 * k := by
    have hmMod : m % 4 = 1 ∨ m % 4 = 3 := by
      have hmTwo := Nat.odd_iff.mp hm
      omega
    rcases hmMod with hm1 | hm3
    · have hsign : (-1 : ℤ) ^ (m / 2) = 1 :=
        by
          have hdiv : m / 2 = 2 * (m / 4) := by omega
          rw [hdiv, pow_mul]
          norm_num
      have hmForm : m = 4 * (m / 4) + 1 := by
        have hdiv := Nat.mod_add_div m 4
        omega
      constructor
      · simpa only [q, hsign, one_mul] using hmInt
      · refine ⟨(m / 4 : ℕ), ?_⟩
        simp only [q, hsign, one_mul]
        exact_mod_cast (by omega : (m : ℤ) - 1 = 4 * (m / 4 : ℕ))
    · have hsign : (-1 : ℤ) ^ (m / 2) = -1 :=
        by
          have hdiv : m / 2 = 2 * (m / 4) + 1 := by omega
          rw [hdiv, pow_add, pow_mul]
          norm_num
      have hmForm : m = 4 * (m / 4) + 3 := by
        have hdiv := Nat.mod_add_div m 4
        omega
      constructor
      · simpa only [q, hsign, neg_one_mul] using hmInt.neg
      · refine ⟨-((m / 4 : ℤ) + 1), ?_⟩
        simp only [q, hsign, neg_one_mul]
        omega
  have hqCoprime : IsCoprime q (2 : ℤ) := by
    obtain ⟨k, hk⟩ := hqData.2
    refine ⟨1, -2 * k, ?_⟩
    omega
  have hqPadicUnit : IsUnit (q : ℤ_[2]) := by
    rw [PadicInt.isUnit_iff, PadicInt.norm_intCast_eq_one_iff]
    exact hqCoprime
  let qZ : ℤ_[2]ˣ := hqPadicUnit.unit
  let F :=
    LocalFieldTheory.DiscreteValuationField.Examples.Qp.padicCompleteDVF 2
  let eO : ℤ_[2] ≃+* F.valuationSubring :=
    LocalFieldTheory.DiscreteValuationField.Examples.Qp.padicIntEquivValuationSubring 2
  let qO : F.valuationSubringˣ := Units.mapEquiv eO.toMulEquiv qZ
  have hqMaximal :
      (q : ℤ_[2]) - 1 ∈ IsLocalRing.maximalIdeal ℤ_[2] ^ 2 := by
    rw [PadicInt.maximalIdeal_eq_span_p, Ideal.span_singleton_pow,
      Ideal.mem_span_singleton]
    obtain ⟨k, hk⟩ := hqData.2
    refine ⟨(k : ℤ_[2]), ?_⟩
    calc
      (q : ℤ_[2]) - 1 = ((q - 1 : ℤ) : ℤ_[2]) := by norm_num
      _ = ((4 * k : ℤ) : ℤ_[2]) := by rw [hk]
      _ = (2 : ℤ_[2]) ^ 2 * (k : ℤ_[2]) := by norm_num
  have hqO2 :
      qO ∈ LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup F 2 := by
    rw [LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.mem_iff]
    have hqOVal : (qO : F.valuationSubring) = eO (q : ℤ_[2]) := by
      simp [qO, qZ]
    rw [hqOVal, ← map_one eO, ← map_sub]
    exact
      (ValuationTheory.ringEquiv_mem_maximalIdeal_pow_iff
        eO 2 ((q : ℤ_[2]) - 1)).2 hqMaximal
  let u : LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup F 2 :=
    ⟨qO, hqO2⟩
  obtain ⟨rD, hrD⟩ :=
    LocalClassFieldTheory.padicDVR_U2_square_class u
  let toField : F.valuationSubringˣ →* ℚ_[2]ˣ :=
    Units.map F.valuation.valuationSubring.subtype.toMonoidHom
  let r : ℚ_[2]ˣ := toField (rD : F.valuationSubringˣ)
  let five : ℚ_[2]ˣ := Units.mk0 (5 : ℚ_[2]) (by norm_num)
  have hbase : toField qO = rationalTwoAdicSignedOddUnit m hm := by
    apply Units.ext
    dsimp [toField, qO, qZ, eO, F, q]
    rfl
  have hfive :
      toField
          ((LocalClassFieldTheory.padicDVRFive :
              LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup F 2) :
            F.valuationSubringˣ) =
        five := by
    apply Units.ext
    dsimp [toField, five, F]
    exact LocalClassFieldTheory.padicDVR_five_val
  refine ⟨r, ?_⟩
  rcases hrD with hrD | hrD
  · left
    calc
      rationalTwoAdicSignedOddUnit m hm = toField qO := hbase.symm
      _ = toField ((rD : F.valuationSubringˣ) ^ 2) :=
        congrArg toField hrD
      _ = r ^ 2 := by rw [map_pow]
  · right
    calc
      rationalTwoAdicSignedOddUnit m hm = toField qO := hbase.symm
      _ = toField
          ((LocalClassFieldTheory.padicDVRFive :
              LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup F 2) *
            (rD : F.valuationSubringˣ) ^ 2) :=
        congrArg toField hrD
      _ = five * r ^ 2 := by rw [map_mul, map_pow, hfive]

open scoped Classical in
/-- Pull the signed odd square-class decomposition back from `ℚ₂` to the
canonical absolute-value completion used by global Hilbert symbols. -/
theorem rationalTwoAdicOddUnit_squareClass
    (m : ℕ) (hm : Odd m) :
    let v₂ := RayClass.rationalPrime rationalTwoPrime
    let C := (HeightOneSpectrum.adicAbv ℚ v₂).Completion
    let aC := finitePlaceHilbertCompletionUnit ℚ v₂
      (rationalNaturalFieldUnit m (by
        intro hm0
        subst m
        norm_num at hm))
    let fiveC : Cˣ := Units.mk0 (5 : C)
      (finitePlaceHilbert_natCast_ne_zero ℚ (5 : ℕ+) (by norm_num) v₂)
    ∃ r : Cˣ,
      aC = (-1 : Cˣ) ^ (m / 2) * r ^ 2 ∨
        aC = (-1 : Cˣ) ^ (m / 2) * (fiveC * r ^ 2) := by
  dsimp only
  let v₂ := RayClass.rationalPrime rationalTwoPrime
  let C := (HeightOneSpectrum.adicAbv ℚ v₂).Completion
  let e : C ≃+* ℚ_[2] := rationalTwoAdicCompletionEquivPadic
  have hm0 : m ≠ 0 := by
    intro hm0
    subst m
    norm_num at hm
  let aC : Cˣ := finitePlaceHilbertCompletionUnit ℚ v₂
    (rationalNaturalFieldUnit m hm0)
  have haC :
      (aC : (HeightOneSpectrum.adicAbv ℚ v₂).Completion) =
        (m : (HeightOneSpectrum.adicAbv ℚ v₂).Completion) := by
    simp only [aC, C, finitePlaceHilbertCompletionUnit, Units.coe_map,
      rationalNaturalFieldUnit_coe]
    exact map_natCast
      (algebraMap ℚ (HeightOneSpectrum.adicAbv ℚ v₂).Completion) m
  let fiveC : Cˣ := Units.mk0 (5 : C)
    (finitePlaceHilbert_natCast_ne_zero ℚ (5 : ℕ+) (by norm_num) v₂)
  let fiveQ : ℚ_[2]ˣ := Units.mk0 (5 : ℚ_[2]) (by norm_num)
  obtain ⟨rQ, hrQ⟩ :=
    rationalTwoAdicSignedOddUnit_squareClass m hm
  let rC : Cˣ := Units.map e.symm.toMonoidHom rQ
  have hsigned :
      Units.map e.symm.toMonoidHom
          (rationalTwoAdicSignedOddUnit m hm) =
        (-1 : Cˣ) ^ (m / 2) * aC := by
    apply Units.ext
    simp only [Units.coe_map, Units.val_mul, Units.val_pow_eq_pow_val,
      rationalTwoAdicSignedOddUnit_coe]
    rw [haC]
    change
      e.symm ((((-1 : ℤ) ^ (m / 2) * (m : ℤ) : ℤ) : ℚ_[2])) =
        (-1 : (HeightOneSpectrum.adicAbv ℚ v₂).Completion) ^ (m / 2) *
          (m : (HeightOneSpectrum.adicAbv ℚ v₂).Completion)
    calc
      e.symm ((((-1 : ℤ) ^ (m / 2) * (m : ℤ) : ℤ) : ℚ_[2])) =
          (((-1 : ℤ) ^ (m / 2) * (m : ℤ) : ℤ) :
            (HeightOneSpectrum.adicAbv ℚ v₂).Completion) :=
        map_intCast e.symm.toRingHom _
      _ = (-1 : (HeightOneSpectrum.adicAbv ℚ v₂).Completion) ^ (m / 2) *
          (m : (HeightOneSpectrum.adicAbv ℚ v₂).Completion) := by norm_num
  have hqSq : (((-1 : Cˣ) ^ (m / 2)) ^ 2) = 1 := by
    calc
      (((-1 : Cˣ) ^ (m / 2)) ^ 2) = ((-1 : Cˣ) ^ 2) ^ (m / 2) := by
        rw [← pow_mul, Nat.mul_comm, pow_mul]
      _ = 1 := by rw [neg_one_sq, one_pow]
  refine ⟨rC, ?_⟩
  rcases hrQ with hrQ | hrQ
  · left
    have hmapped := congrArg
      (Units.map e.symm.toMonoidHom) hrQ
    have hsignedEq :
        (-1 : Cˣ) ^ (m / 2) * aC = rC ^ 2 := by
      simpa only [hsigned, map_pow, rC] using hmapped
    calc
      aC = 1 * aC := (one_mul aC).symm
      _ = (((-1 : Cˣ) ^ (m / 2)) ^ 2) * aC := by rw [hqSq]
      _ = (-1 : Cˣ) ^ (m / 2) *
          (((-1 : Cˣ) ^ (m / 2)) * aC) := by
        rw [pow_two, mul_assoc]
      _ = (-1 : Cˣ) ^ (m / 2) * rC ^ 2 := by rw [hsignedEq]
  · right
    have hmapped := congrArg
      (Units.map e.symm.toMonoidHom) hrQ
    have hfiveMapped :
        Units.map e.symm.toMonoidHom fiveQ = fiveC := by
      apply Units.ext
      change e.symm (5 : ℚ_[2]) = (5 : C)
      simpa using map_natCast e.symm 5
    have hsignedEq :
        (-1 : Cˣ) ^ (m / 2) * aC = fiveC * rC ^ 2 := by
      simpa only [hsigned, map_mul, map_pow, hfiveMapped, rC, fiveQ]
        using hmapped
    calc
      aC = 1 * aC := (one_mul aC).symm
      _ = (((-1 : Cˣ) ^ (m / 2)) ^ 2) * aC := by rw [hqSq]
      _ = (-1 : Cˣ) ^ (m / 2) *
          (((-1 : Cˣ) ^ (m / 2)) * aC) := by
        rw [pow_two, mul_assoc]
      _ = (-1 : Cˣ) ^ (m / 2) * (fiveC * rC ^ 2) :=
        congrArg (fun z => (-1 : Cˣ) ^ (m / 2) * z) hsignedEq

open scoped Classical in
private theorem localHilbertSymbol_pow_left
    (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    (n : ℕ+) (hnF : ((n : ℕ) : F) ≠ 0)
    (hmu : (primitiveRoots (n : ℕ) F).Nonempty)
    (x y : Fˣ) (e : ℕ) :
    localHilbertSymbol F n hnF hmu (x ^ e) y =
      localHilbertSymbol F n hnF hmu x y ^ e := by
  change
    localHilbertSymbolHom F n hnF hmu y (x ^ e) =
      localHilbertSymbolHom F n hnF hmu y x ^ e
  exact map_pow (localHilbertSymbolHom F n hnF hmu y) x e

open scoped Classical in
private theorem localHilbertSymbol_pow_right
    (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    (n : ℕ+) (hnF : ((n : ℕ) : F) ≠ 0)
    (hmu : (primitiveRoots (n : ℕ) F).Nonempty)
    (x y : Fˣ) (e : ℕ) :
    localHilbertSymbol F n hnF hmu x (y ^ e) =
      localHilbertSymbol F n hnF hmu x y ^ e := by
  rw [localHilbertSymbol_skew,
    localHilbertSymbol_pow_left,
    ← inv_pow, ← localHilbertSymbol_skew]

open scoped Classical in
private theorem localHilbertSymbol_mul_left
    (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    (n : ℕ+) (hnF : ((n : ℕ) : F) ≠ 0)
    (hmu : (primitiveRoots (n : ℕ) F).Nonempty)
    (x y z : Fˣ) :
    localHilbertSymbol F n hnF hmu (x * y) z =
      localHilbertSymbol F n hnF hmu x z *
        localHilbertSymbol F n hnF hmu y z := by
  change
    localHilbertSymbolHom F n hnF hmu z (x * y) =
      localHilbertSymbolHom F n hnF hmu z x *
        localHilbertSymbolHom F n hnF hmu z y
  exact map_mul (localHilbertSymbolHom F n hnF hmu z) x y

open scoped Classical in
private theorem localHilbertSymbol_pow_pow
    (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    (n : ℕ+) (hnF : ((n : ℕ) : F) ≠ 0)
    (hmu : (primitiveRoots (n : ℕ) F).Nonempty)
    (x y : Fˣ) (a b : ℕ) :
    localHilbertSymbol F n hnF hmu (x ^ a) (y ^ b) =
      localHilbertSymbol F n hnF hmu x y ^ (a * b) := by
  rw [localHilbertSymbol_pow_left, localHilbertSymbol_pow_right,
    ← pow_mul, Nat.mul_comm]

open scoped Classical in
private theorem localQuadraticHilbertSymbol_square_left_eq_one
    (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    (h2F : ((((2 : ℕ+) : ℕ)) : F) ≠ 0)
    (hmu : (primitiveRoots (((2 : ℕ+) : ℕ)) F).Nonempty)
    (x y : Fˣ) :
    localHilbertSymbol F (2 : ℕ+) h2F hmu (x ^ 2) y = 1 := by
  rw [localHilbertSymbol_pow_left]
  apply Subtype.ext
  exact (localHilbertSymbol F (2 : ℕ+) h2F hmu x y).2

open scoped Classical in
private theorem localQuadraticHilbertSymbol_square_right_eq_one
    (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    (h2F : ((((2 : ℕ+) : ℕ)) : F) ≠ 0)
    (hmu : (primitiveRoots (((2 : ℕ+) : ℕ)) F).Nonempty)
    (x y : Fˣ) :
    localHilbertSymbol F (2 : ℕ+) h2F hmu x (y ^ 2) = 1 := by
  rw [localHilbertSymbol_pow_right]
  apply Subtype.ext
  exact (localHilbertSymbol F (2 : ℕ+) h2F hmu x y).2

open scoped Classical in
private theorem localQuadraticHilbertSymbol_value_sq_eq_one
    (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    (h2F : ((((2 : ℕ+) : ℕ)) : F) ≠ 0)
    (hmu : (primitiveRoots (((2 : ℕ+) : ℕ)) F).Nonempty)
    (x y : Fˣ) :
    localHilbertSymbol F (2 : ℕ+) h2F hmu x y ^ 2 = 1 := by
  apply Subtype.ext
  exact (localHilbertSymbol F (2 : ℕ+) h2F hmu x y).2

open scoped Classical in
private theorem localQuadraticHilbertSymbol_squareClass_formula
    (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    (h2F : ((((2 : ℕ+) : ℕ)) : F) ≠ 0)
    (hmu : (primitiveRoots (((2 : ℕ+) : ℕ)) F).Nonempty)
    (q five a b r s : Fˣ) (ka kb : ℕ)
    (negRoot : nthRootsSubgroup F (((2 : ℕ+) : ℕ)))
    (hqq : localHilbertSymbol F (2 : ℕ+) h2F hmu q q = negRoot)
    (hqfive :
      localHilbertSymbol F (2 : ℕ+) h2F hmu q five = 1)
    (hfivefive :
      localHilbertSymbol F (2 : ℕ+) h2F hmu five five = 1)
    (ha : a = q ^ ka * r ^ 2 ∨
      a = q ^ ka * (five * r ^ 2))
    (hb : b = q ^ kb * s ^ 2 ∨
      b = q ^ kb * (five * s ^ 2)) :
    localHilbertSymbol F (2 : ℕ+) h2F hmu a b =
      negRoot ^ (ka * kb) := by
  have hfiveq :
      localHilbertSymbol F (2 : ℕ+) h2F hmu five q = 1 := by
    rw [localHilbertSymbol_skew, hqfive, inv_one]
  rcases ha with ha | ha <;> rcases hb with hb | hb
  all_goals subst a; subst b
  all_goals
    simp only [localHilbertSymbol_mul_left,
      localHilbertSymbol_mul_right,
      localHilbertSymbol_pow_left,
      localHilbertSymbol_pow_right,
      localQuadraticHilbertSymbol_value_sq_eq_one,
      hqq, hqfive, hfiveq, hfivefive,
      one_pow, mul_one, one_mul]
  all_goals
    have hsquare
        (x : nthRootsSubgroup F (((2 : ℕ+) : ℕ))) : x ^ 2 = 1 := by
      apply Subtype.ext
      change x.1 ^ 2 = 1
      exact x.2
    rw [hsquare, mul_one]
    exact (pow_mul negRoot ka kb).symm

open scoped Classical in
/-- The dyadic quadratic Hilbert symbol of `-1` and `5` is trivial. -/
theorem rationalTwoAdicHilbert_negOne_five_eq_one :
    let v₂ := RayClass.rationalPrime rationalTwoPrime
    let C := (HeightOneSpectrum.adicAbv ℚ v₂).Completion
    letI : ValuativeRel C :=
      finitePlaceLocalArtinCompletionValuativeRel v₂
    letI : IsNonarchimedeanLocalField C :=
      finitePlaceLocalArtinCompletionIsNonarchimedeanLocalField v₂
    localHilbertSymbol C (2 : ℕ+)
        (finitePlaceHilbert_natCast_ne_zero ℚ (2 : ℕ+)
          (by norm_num) v₂)
        (finitePlaceHilbert_primitiveRoots_nonempty ℚ (2 : ℕ+)
          rationalQuadraticPrimitiveRoots_nonempty v₂)
        (-1 : Cˣ) (Units.mk0 (5 : C)
          (finitePlaceHilbert_natCast_ne_zero ℚ (5 : ℕ+)
            (by norm_num) v₂)) = 1 := by
  dsimp only
  let v₂ := RayClass.rationalPrime rationalTwoPrime
  let C := (HeightOneSpectrum.adicAbv ℚ v₂).Completion
  let : ValuativeRel C :=
    finitePlaceLocalArtinCompletionValuativeRel v₂
  let : IsNonarchimedeanLocalField C :=
    finitePlaceLocalArtinCompletionIsNonarchimedeanLocalField v₂
  let h2C := finitePlaceHilbert_natCast_ne_zero ℚ (2 : ℕ+)
    (by norm_num) v₂
  let hmuC := finitePlaceHilbert_primitiveRoots_nonempty ℚ (2 : ℕ+)
    rationalQuadraticPrimitiveRoots_nonempty v₂
  let two : Cˣ := Units.mk0 (2 : C)
    (finitePlaceHilbert_natCast_ne_zero ℚ (2 : ℕ+) (by norm_num) v₂)
  let negFour : Cˣ := Units.mk0 (-4 : C)
    (neg_ne_zero.mpr
      (finitePlaceHilbert_natCast_ne_zero ℚ (4 : ℕ+) (by norm_num) v₂))
  let five : Cˣ := Units.mk0 (5 : C)
    (finitePlaceHilbert_natCast_ne_zero ℚ (5 : ℕ+) (by norm_num) v₂)
  have hnegFour : negFour = (-1 : Cˣ) * two ^ 2 := by
    apply Units.ext
    change
      (-4 : (HeightOneSpectrum.adicAbv ℚ v₂).Completion) =
        (-1 : (HeightOneSpectrum.adicAbv ℚ v₂).Completion) *
          (2 : (HeightOneSpectrum.adicAbv ℚ v₂).Completion) ^ 2
    norm_num
  have hstein :
      localHilbertSymbol C (2 : ℕ+) h2C hmuC negFour five = 1 := by
    have hcomp : 1 - (negFour : C) ≠ 0 := by
      have hval : 1 - (negFour : C) = (5 : C) := by
        dsimp only [negFour]
        change
          1 - (-4 : (HeightOneSpectrum.adicAbv ℚ v₂).Completion) = 5
        norm_num
      rw [hval]
      exact finitePlaceHilbert_natCast_ne_zero ℚ (5 : ℕ+)
        (by norm_num) v₂
    have hs := localHilbertSymbol_steinberg C (2 : ℕ+) h2C hmuC negFour hcomp
    have hfiveComp : five = Units.mk0 (1 - (negFour : C)) hcomp := by
      apply Units.ext
      dsimp only [negFour, five]
      change
        (5 : (HeightOneSpectrum.adicAbv ℚ v₂).Completion) = 1 - (-4)
      norm_num
    rw [hfiveComp]
    exact hs
  rw [hnegFour] at hstein
  change
    localHilbertSymbolHom C (2 : ℕ+) h2C hmuC five
        ((-1 : Cˣ) * two ^ 2) = 1 at hstein
  rw [map_mul] at hstein
  change
    localHilbertSymbol C (2 : ℕ+) h2C hmuC (-1 : Cˣ) five *
        localHilbertSymbol C (2 : ℕ+) h2C hmuC (two ^ 2) five = 1
      at hstein
  rw [localQuadraticHilbertSymbol_square_left_eq_one, mul_one] at hstein
  exact hstein

open scoped Classical in
/-- The dyadic quadratic Hilbert symbol of `5` with itself is trivial. -/
theorem rationalTwoAdicHilbert_five_five_eq_one :
    let v₂ := RayClass.rationalPrime rationalTwoPrime
    let C := (HeightOneSpectrum.adicAbv ℚ v₂).Completion
    letI : ValuativeRel C :=
      finitePlaceLocalArtinCompletionValuativeRel v₂
    letI : IsNonarchimedeanLocalField C :=
      finitePlaceLocalArtinCompletionIsNonarchimedeanLocalField v₂
    localHilbertSymbol C (2 : ℕ+)
        (finitePlaceHilbert_natCast_ne_zero ℚ (2 : ℕ+)
          (by norm_num) v₂)
        (finitePlaceHilbert_primitiveRoots_nonempty ℚ (2 : ℕ+)
          rationalQuadraticPrimitiveRoots_nonempty v₂)
        (Units.mk0 (5 : C)
          (finitePlaceHilbert_natCast_ne_zero ℚ (5 : ℕ+)
            (by norm_num) v₂))
        (Units.mk0 (5 : C)
          (finitePlaceHilbert_natCast_ne_zero ℚ (5 : ℕ+)
            (by norm_num) v₂)) = 1 := by
  dsimp only
  let v₂ := RayClass.rationalPrime rationalTwoPrime
  let C := (HeightOneSpectrum.adicAbv ℚ v₂).Completion
  let : ValuativeRel C :=
    finitePlaceLocalArtinCompletionValuativeRel v₂
  let : IsNonarchimedeanLocalField C :=
    finitePlaceLocalArtinCompletionIsNonarchimedeanLocalField v₂
  let h2C := finitePlaceHilbert_natCast_ne_zero ℚ (2 : ℕ+)
    (by norm_num) v₂
  let hmuC := finitePlaceHilbert_primitiveRoots_nonempty ℚ (2 : ℕ+)
    rationalQuadraticPrimitiveRoots_nonempty v₂
  let five : Cˣ := Units.mk0 (5 : C)
    (finitePlaceHilbert_natCast_ne_zero ℚ (5 : ℕ+) (by norm_num) v₂)
  have hneg :
      localHilbertSymbol C (2 : ℕ+) h2C hmuC five (-five) = 1 :=
    localHilbertSymbol_neg_self C (2 : ℕ+) h2C hmuC five
  have hdecomp : -five = (-1 : Cˣ) * five := by
    apply Units.ext
    change
      -(5 : (HeightOneSpectrum.adicAbv ℚ v₂).Completion) =
        (-1 : (HeightOneSpectrum.adicAbv ℚ v₂).Completion) * 5
    ring
  rw [hdecomp, localHilbertSymbol_mul_right] at hneg
  have hskew :
      localHilbertSymbol C (2 : ℕ+) h2C hmuC five (-1 : Cˣ) = 1 := by
    rw [localHilbertSymbol_skew,
      rationalTwoAdicHilbert_negOne_five_eq_one, inv_one]
  rw [hskew, one_mul] at hneg
  exact hneg

open scoped Classical in
/-- The rational global field unit represented by `-1`. -/
def rationalQuadraticNegOneFieldUnit : ℚˣ :=
  nonzeroIntegralFieldUnit ℚ (-1 : 𝓞 ℚ) (by norm_num)

open scoped Classical in
@[simp]
theorem rationalQuadraticNegOneFieldUnit_coe :
    (rationalQuadraticNegOneFieldUnit : ℚ) = -1 :=
  rfl

open scoped Classical in
private theorem rationalQuadraticNegOne_not_mem
    (v : HeightOneSpectrum (𝓞 ℚ)) :
    (-1 : 𝓞 ℚ) ∉ v.asIdeal := by
  intro hneg
  have hone : (1 : 𝓞 ℚ) ∈ v.asIdeal := by
    simpa only [neg_neg] using v.asIdeal.neg_mem hneg
  exact v.isPrime.ne_top ((Ideal.eq_top_iff_one v.asIdeal).mpr hone)

open scoped Classical in
private theorem rationalFinitePlaceHilbert_negOne_negOne_eq_one_of_ne_two
    (v : HeightOneSpectrum (𝓞 ℚ))
    (hv : v ≠ RayClass.rationalPrime rationalTwoPrime) :
    finitePlaceHilbertSymbol ℚ (2 : ℕ+) (by norm_num)
        rationalQuadraticPrimitiveRoots_nonempty v
        rationalQuadraticNegOneFieldUnit
        rationalQuadraticNegOneFieldUnit = 1 := by
  apply finitePlaceHilbertSymbol_integral_units_eq_one
      ℚ (2 : ℕ+) (by norm_num)
        rationalQuadraticPrimitiveRoots_nonempty v
  · rw [powerResidueExponentFinitePlaces_rational_two]
    simpa only [Finset.mem_singleton]
  · exact rationalQuadraticNegOne_not_mem v
  · exact rationalQuadraticNegOne_not_mem v

open scoped Classical in
/-- The finite-place Hilbert factor of `(-1,-1)` at the prime above two is
the negative quadratic root.  The proof uses the global product formula;
all odd finite factors are trivial and the unique real factor is `-1`. -/
theorem rationalFinitePlaceHilbert_negOne_negOne_eq_negOne :
    finitePlaceHilbertSymbol ℚ (2 : ℕ+) (by norm_num)
        rationalQuadraticPrimitiveRoots_nonempty
        (RayClass.rationalPrime rationalTwoPrime)
        rationalQuadraticNegOneFieldUnit
        rationalQuadraticNegOneFieldUnit =
      integralRootsOfUnityToNthRoots ℚ 2
        rationalQuadraticNegOneRoot := by
  let negRoot : nthRootsSubgroup ℚ (((2 : ℕ+) : ℕ)) :=
    integralRootsOfUnityToNthRoots ℚ (((2 : ℕ+) : ℕ))
      rationalQuadraticNegOneRoot
  have hinfinite :
      (∏ v : InfinitePlace ℚ,
        infinitePlaceHilbertSymbol ℚ (2 : ℕ+)
          v rationalQuadraticNegOneFieldUnit
            rationalQuadraticNegOneFieldUnit) = negRoot := by
    rw [Fintype.prod_unique,
      show (default : InfinitePlace ℚ) = Rat.infinitePlace by
        exact Subsingleton.elim _ _]
    apply Subtype.ext
    have hreal := infinitePlaceHilbertSymbol_real_apply
      ℚ (2 : ℕ+) Rat.infinitePlace
        rationalQuadraticNegOneFieldUnit rationalQuadraticNegOneFieldUnit
          rfl Rat.isReal_infinitePlace
    have hneg :
        InfinitePlace.embedding_of_isReal Rat.isReal_infinitePlace
          (rationalQuadraticNegOneFieldUnit : ℚ) < 0 := by
      rw [rationalQuadraticNegOneFieldUnit_coe, map_neg, map_one]
      norm_num
    rw [ite_eq_left ⟨hneg, hneg⟩] at hreal
    have hreal' :
        (infinitePlaceHilbertSymbol ℚ (2 : ℕ+) Rat.infinitePlace
          rationalQuadraticNegOneFieldUnit
            rationalQuadraticNegOneFieldUnit).1 = (-1 : ℚˣ) := by
      simpa [rationalQuadraticNegOneFieldUnit] using hreal
    have hnegRootVal : negRoot.1 = (-1 : ℚˣ) := by
      apply Units.ext
      change algebraMap (𝓞 ℚ) ℚ (-1 : 𝓞 ℚ) = (-1 : ℚ)
      rw [map_neg, map_one]
    exact hreal'.trans hnegRootVal.symm
  have hfinite :
      (∏ᶠ v : HeightOneSpectrum (𝓞 ℚ),
        finitePlaceHilbertSymbol ℚ (2 : ℕ+) (by norm_num)
          rationalQuadraticPrimitiveRoots_nonempty v
          rationalQuadraticNegOneFieldUnit
          rationalQuadraticNegOneFieldUnit) =
        finitePlaceHilbertSymbol ℚ (2 : ℕ+) (by norm_num)
          rationalQuadraticPrimitiveRoots_nonempty
          (RayClass.rationalPrime rationalTwoPrime)
          rationalQuadraticNegOneFieldUnit
          rationalQuadraticNegOneFieldUnit := by
    apply finprod_eq_single
    intro v hv
    exact
      rationalFinitePlaceHilbert_negOne_negOne_eq_one_of_ne_two v hv
  have hproduct := hilbertSymbol_allPlaces_product_eq_one
    ℚ (2 : ℕ+) (by norm_num)
      rationalQuadraticPrimitiveRoots_nonempty
        rationalQuadraticNegOneFieldUnit
          rationalQuadraticNegOneFieldUnit
  rw [hinfinite, hfinite] at hproduct
  have hnegRootSquare : negRoot * negRoot = 1 := by
    have hroot : negRoot.1 ^ (((2 : ℕ+) : ℕ)) = (1 : ℚˣ) :=
      (KummerTheory.mem_nthRootsSubgroup_iff ℚ).mp negRoot.2
    change negRoot.1 ^ 2 = (1 : ℚˣ) at hroot
    apply Subtype.ext
    change negRoot.1 * negRoot.1 = (1 : ℚˣ)
    simpa only [pow_two] using hroot
  let twoFactor :=
    finitePlaceHilbertSymbol ℚ (2 : ℕ+) (by norm_num)
      rationalQuadraticPrimitiveRoots_nonempty
      (RayClass.rationalPrime rationalTwoPrime)
      rationalQuadraticNegOneFieldUnit rationalQuadraticNegOneFieldUnit
  change twoFactor = negRoot
  calc
    twoFactor = 1 * twoFactor := (one_mul twoFactor).symm
    _ = (negRoot * negRoot) * twoFactor := by rw [hnegRootSquare]
    _ = negRoot * (negRoot * twoFactor) := mul_assoc _ _ _
    _ = negRoot := by rw [hproduct, mul_one]

open scoped Classical in
/-- In the canonical dyadic completion, the local quadratic Hilbert symbol
of `(-1,-1)` is `-1`. -/
theorem rationalTwoAdicHilbert_negOne_negOne_eq_negOne :
    let v₂ := RayClass.rationalPrime rationalTwoPrime
    let C := (HeightOneSpectrum.adicAbv ℚ v₂).Completion
    letI : ValuativeRel C :=
      finitePlaceLocalArtinCompletionValuativeRel v₂
    letI : IsNonarchimedeanLocalField C :=
      finitePlaceLocalArtinCompletionIsNonarchimedeanLocalField v₂
    localHilbertSymbol C (2 : ℕ+)
        (finitePlaceHilbert_natCast_ne_zero ℚ (2 : ℕ+)
          (by norm_num) v₂)
        (finitePlaceHilbert_primitiveRoots_nonempty ℚ (2 : ℕ+)
          rationalQuadraticPrimitiveRoots_nonempty v₂)
        (-1 : Cˣ) (-1 : Cˣ) =
      (⟨(-1 : Cˣ), by
        apply (KummerTheory.mem_nthRootsSubgroup_iff C).mpr
        change
          ((-1 : (HeightOneSpectrum.adicAbv ℚ
            (RayClass.rationalPrime rationalTwoPrime)).Completionˣ)) ^ 2 = 1
        norm_num⟩ : nthRootsSubgroup C 2) := by
  dsimp only
  let v₂ := RayClass.rationalPrime rationalTwoPrime
  let C := (HeightOneSpectrum.adicAbv ℚ v₂).Completion
  let : ValuativeRel C :=
    finitePlaceLocalArtinCompletionValuativeRel v₂
  let : IsNonarchimedeanLocalField C :=
    finitePlaceLocalArtinCompletionIsNonarchimedeanLocalField v₂
  let hn : ((((2 : ℕ+) : ℕ)) : ℚ) ≠ 0 := by norm_num
  have hmap := finitePlaceHilbertSymbol_map_eq_localHilbertSymbol
    ℚ (2 : ℕ+) hn rationalQuadraticPrimitiveRoots_nonempty
      (RayClass.rationalPrime rationalTwoPrime)
        rationalQuadraticNegOneFieldUnit rationalQuadraticNegOneFieldUnit
  rw [rationalFinitePlaceHilbert_negOne_negOne_eq_negOne] at hmap
  have hmappedNeg :
      nthRootsSubgroupMap ℚ
        (HeightOneSpectrum.adicAbv ℚ
          (RayClass.rationalPrime rationalTwoPrime)).Completion 2
          (integralRootsOfUnityToNthRoots ℚ 2
            rationalQuadraticNegOneRoot) =
        (⟨(-1 : (HeightOneSpectrum.adicAbv ℚ
          (RayClass.rationalPrime rationalTwoPrime)).Completionˣ), by
            apply (KummerTheory.mem_nthRootsSubgroup_iff _).mpr
            norm_num⟩ : nthRootsSubgroup _ 2) := by
    apply Subtype.ext
    apply Units.ext
    change
      algebraMap ℚ (HeightOneSpectrum.adicAbv ℚ
        (RayClass.rationalPrime rationalTwoPrime)).Completion (-1) = -1
    rw [map_neg, map_one]
  have hnegC :
      finitePlaceHilbertCompletionUnit ℚ
          (RayClass.rationalPrime rationalTwoPrime)
            rationalQuadraticNegOneFieldUnit =
        (-1 : (HeightOneSpectrum.adicAbv ℚ
          (RayClass.rationalPrime rationalTwoPrime)).Completionˣ) := by
    apply Units.ext
    change
      algebraMap ℚ (HeightOneSpectrum.adicAbv ℚ
        (RayClass.rationalPrime rationalTwoPrime)).Completion (-1) = -1
    rw [map_neg, map_one]
  have hresult := hmap.symm.trans hmappedNeg
  unfold finitePlaceLocalHilbertSymbol at hresult
  rw [hnegC] at hresult
  exact hresult

open scoped Classical in
/-- Explicit dyadic quadratic Hilbert-symbol formula for positive odd
rational integers. -/
theorem rationalTwoAdicHilbert_odd_eq_classicalSign
    (a b : ℕ) (ha : Odd a) (hb : Odd b) :
    let v₂ := RayClass.rationalPrime rationalTwoPrime
    let C := (HeightOneSpectrum.adicAbv ℚ v₂).Completion
    letI : ValuativeRel C :=
      finitePlaceLocalArtinCompletionValuativeRel v₂
    letI : IsNonarchimedeanLocalField C :=
      finitePlaceLocalArtinCompletionIsNonarchimedeanLocalField v₂
    localHilbertSymbol C (2 : ℕ+)
        (finitePlaceHilbert_natCast_ne_zero ℚ (2 : ℕ+)
          (by norm_num) v₂)
        (finitePlaceHilbert_primitiveRoots_nonempty ℚ (2 : ℕ+)
          rationalQuadraticPrimitiveRoots_nonempty v₂)
        (finitePlaceHilbertCompletionUnit ℚ v₂
          (rationalNaturalFieldUnit a (by
            intro ha0
            subst a
            norm_num at ha)))
        (finitePlaceHilbertCompletionUnit ℚ v₂
          (rationalNaturalFieldUnit b (by
            intro hb0
            subst b
            norm_num at hb))) =
      (⟨(-1 : Cˣ), by
        apply (KummerTheory.mem_nthRootsSubgroup_iff C).mpr
        change
          (-1 : (HeightOneSpectrum.adicAbv ℚ
            (RayClass.rationalPrime rationalTwoPrime)).Completionˣ) ^ 2 = 1
        norm_num⟩ : nthRootsSubgroup C 2) ^
        (a / 2 * (b / 2)) := by
  dsimp only
  let v₂ := RayClass.rationalPrime rationalTwoPrime
  let C := (HeightOneSpectrum.adicAbv ℚ v₂).Completion
  let : ValuativeRel C :=
    finitePlaceLocalArtinCompletionValuativeRel v₂
  let : IsNonarchimedeanLocalField C :=
    finitePlaceLocalArtinCompletionIsNonarchimedeanLocalField v₂
  let h2C := finitePlaceHilbert_natCast_ne_zero ℚ (2 : ℕ+)
    (by norm_num) v₂
  let hmuC := finitePlaceHilbert_primitiveRoots_nonempty ℚ (2 : ℕ+)
    rationalQuadraticPrimitiveRoots_nonempty v₂
  have ha0 : a ≠ 0 := by
    intro ha0
    subst a
    norm_num at ha
  have hb0 : b ≠ 0 := by
    intro hb0
    subst b
    norm_num at hb
  let aC := finitePlaceHilbertCompletionUnit ℚ v₂
    (rationalNaturalFieldUnit a ha0)
  let bC := finitePlaceHilbertCompletionUnit ℚ v₂
    (rationalNaturalFieldUnit b hb0)
  let fiveC : Cˣ := Units.mk0 (5 : C)
    (finitePlaceHilbert_natCast_ne_zero ℚ (5 : ℕ+) (by norm_num) v₂)
  let negRootC : nthRootsSubgroup C 2 := ⟨(-1 : Cˣ), by
    apply (KummerTheory.mem_nthRootsSubgroup_iff C).mpr
    change
      (-1 : (HeightOneSpectrum.adicAbv ℚ v₂).Completionˣ) ^ 2 = 1
    norm_num⟩
  obtain ⟨r, hr⟩ := rationalTwoAdicOddUnit_squareClass a ha
  obtain ⟨s, hs⟩ := rationalTwoAdicOddUnit_squareClass b hb
  exact localQuadraticHilbertSymbol_squareClass_formula
    C h2C hmuC (-1 : Cˣ) fiveC aC bC r s
      (a / 2) (b / 2) negRootC
      rationalTwoAdicHilbert_negOne_negOne_eq_negOne
      rationalTwoAdicHilbert_negOne_five_eq_one
      rationalTwoAdicHilbert_five_five_eq_one hr hs

open scoped Classical in
/-- The global finite-place Hilbert factor at two is the classical quadratic
sign for positive odd rational integers. -/
theorem rationalFinitePlaceHilbert_odd_eq_classicalSign
    (a b : ℕ) (ha : Odd a) (hb : Odd b) :
    finitePlaceHilbertSymbol ℚ (2 : ℕ+) (by norm_num)
        rationalQuadraticPrimitiveRoots_nonempty
        (RayClass.rationalPrime rationalTwoPrime)
        (rationalNaturalFieldUnit a (by
          intro ha0
          subst a
          norm_num at ha))
        (rationalNaturalFieldUnit b (by
          intro hb0
          subst b
          norm_num at hb)) =
      integralRootsOfUnityToNthRoots ℚ 2
        (rationalQuadraticNegOneRoot ^ (a / 2 * (b / 2))) := by
  have ha0 : a ≠ 0 := by
    intro ha0
    subst a
    norm_num at ha
  have hb0 : b ≠ 0 := by
    intro hb0
    subst b
    norm_num at hb
  let hn : ((2 : ℕ) : ℚ) ≠ 0 := by norm_num
  let v₂ := RayClass.rationalPrime rationalTwoPrime
  change finitePlaceHilbertSymbol ℚ (2 : ℕ+) hn
      rationalQuadraticPrimitiveRoots_nonempty v₂
      (rationalNaturalFieldUnit a ha0)
      (rationalNaturalFieldUnit b hb0) = _
  apply nthRootsSubgroupMap_injective ℚ
    (HeightOneSpectrum.adicAbv ℚ v₂).Completion 2
  have hmap := finitePlaceHilbertSymbol_map_eq_localHilbertSymbol
    ℚ (2 : ℕ+) hn rationalQuadraticPrimitiveRoots_nonempty v₂
      (rationalNaturalFieldUnit a ha0) (rationalNaturalFieldUnit b hb0)
  have hlocal := rationalTwoAdicHilbert_odd_eq_classicalSign a b ha hb
  dsimp only at hlocal
  have hrootMap :
      nthRootsSubgroupMap ℚ
          (HeightOneSpectrum.adicAbv ℚ v₂).Completion 2
          (integralRootsOfUnityToNthRoots ℚ 2
            (rationalQuadraticNegOneRoot ^ (a / 2 * (b / 2)))) =
        (⟨(-1 : (HeightOneSpectrum.adicAbv ℚ v₂).Completionˣ), by
            apply (KummerTheory.mem_nthRootsSubgroup_iff _).mpr
            norm_num⟩ : nthRootsSubgroup _ 2) ^
          (a / 2 * (b / 2)) := by
    apply Subtype.ext
    change
      Units.map (algebraMap ℚ
        (HeightOneSpectrum.adicAbv ℚ v₂).Completion).toMonoidHom
          (Units.map (algebraMap (𝓞 ℚ) ℚ).toMonoidHom
            ((-1 : (𝓞 ℚ)ˣ) ^ (a / 2 * (b / 2)))) =
        (-1 : (HeightOneSpectrum.adicAbv ℚ v₂).Completionˣ) ^
          (a / 2 * (b / 2))
    rw [map_pow, map_pow]
    congr 1
    apply Units.ext
    simp
  have hlocal' :
      finitePlaceLocalHilbertSymbol ℚ (2 : ℕ+) hn
          rationalQuadraticPrimitiveRoots_nonempty v₂
          (rationalNaturalFieldUnit a ha0)
          (rationalNaturalFieldUnit b hb0) =
        (⟨(-1 : (HeightOneSpectrum.adicAbv ℚ v₂).Completionˣ), by
            apply (KummerTheory.mem_nthRootsSubgroup_iff _).mpr
            norm_num⟩ : nthRootsSubgroup _ 2) ^
          (a / 2 * (b / 2)) := by
    unfold finitePlaceLocalHilbertSymbol
    exact hlocal
  exact hmap.trans (hlocal'.trans hrootMap.symm)

open scoped Classical in
private theorem rationalInfinitePlaceHilbert_natural_eq_one
    (a b : ℕ) (ha : a ≠ 0) (hb : b ≠ 0)
    (v : InfinitePlace ℚ) :
    infinitePlaceHilbertSymbol ℚ (2 : ℕ+) v
        (rationalNaturalFieldUnit a ha)
        (rationalNaturalFieldUnit b hb) = 1 := by
  have hv : v = Rat.infinitePlace := Subsingleton.elim _ _
  subst v
  have haPos :
      0 < InfinitePlace.embedding_of_isReal Rat.isReal_infinitePlace
        (rationalNaturalFieldUnit a ha : ℚ) := by
    rw [rationalNaturalFieldUnit_coe]
    simpa only [map_natCast] using
      (Nat.cast_pos.mpr (Nat.pos_of_ne_zero ha) : (0 : ℝ) < (a : ℝ))
  apply Subtype.ext
  have hreal := infinitePlaceHilbertSymbol_real_apply
    ℚ (2 : ℕ+) Rat.infinitePlace
      (rationalNaturalFieldUnit a ha) (rationalNaturalFieldUnit b hb)
        rfl Rat.isReal_infinitePlace
  have hnot :
      ¬(InfinitePlace.embedding_of_isReal Rat.isReal_infinitePlace
          (rationalNaturalFieldUnit a ha : ℚ) < 0 ∧
        InfinitePlace.embedding_of_isReal Rat.isReal_infinitePlace
          (rationalNaturalFieldUnit b hb : ℚ) < 0) :=
    fun h => (not_lt_of_ge haPos.le) h.1
  rw [ite_eq_right hnot] at hreal
  exact hreal

open scoped Classical in
/-- Evaluation of the complete rational quadratic bad-place correction.
For positive odd inputs the infinite factor is trivial, and the sole finite
bad place is `2`, whose wild Hilbert symbol gives the classical sign. -/
theorem rationalQuadraticBadPlaceCorrection_eq_classicalSign
    (a b : ℕ) (ha : Odd a) (hb : Odd b) :
    powerResidueBadPlaceCorrection ℚ (2 : ℕ+) (by norm_num)
        rationalQuadraticPrimitiveRoots_nonempty
        (rationalNaturalFieldUnit a (by
          intro ha0
          subst a
          norm_num at ha))
        (rationalNaturalFieldUnit b (by
          intro hb0
          subst b
          norm_num at hb)) =
      integralRootsOfUnityToNthRoots ℚ 2
        (rationalQuadraticNegOneRoot ^ (a / 2 * (b / 2))) := by
  have ha0 : a ≠ 0 := by
    intro ha0
    subst a
    norm_num at ha
  have hb0 : b ≠ 0 := by
    intro hb0
    subst b
    norm_num at hb
  let hn : ((((2 : ℕ+) : ℕ)) : ℚ) ≠ 0 := by norm_num
  change powerResidueBadPlaceCorrection ℚ (2 : ℕ+) hn
      rationalQuadraticPrimitiveRoots_nonempty
      (rationalNaturalFieldUnit a ha0)
      (rationalNaturalFieldUnit b hb0) = _
  unfold powerResidueBadPlaceCorrection
  have hinfinite :
      (∏ v : InfinitePlace ℚ,
        infinitePlaceHilbertSymbol ℚ (2 : ℕ+) v
          (rationalNaturalFieldUnit a ha0)
          (rationalNaturalFieldUnit b hb0)) = 1 := by
    apply Finset.prod_eq_one
    intro v _
    exact rationalInfinitePlaceHilbert_natural_eq_one a b ha0 hb0 v
  rw [hinfinite, one_mul,
    powerResidueExponentFinitePlaces_rational_two,
    Finset.prod_singleton,
    rationalFinitePlaceHilbert_odd_eq_classicalSign a b ha hb]

open scoped Classical in
/-- Every prime divisor of an odd rational principal ideal is away from the
quadratic exponent place. -/
theorem rationalPrincipalIdeal_primeDivisors_away_from_two
    (m : ℕ) (hm : Odd m)
    (P : HeightOneSpectrum (𝓞 ℚ))
    (hP : P.asIdeal ∣ rationalPrincipalIdeal m) :
    P ∉ powerResidueExponentFinitePlaces ℚ (2 : ℕ+) := by
  rw [powerResidueExponentFinitePlaces_rational_two,
    Finset.mem_singleton]
  intro hPtwo
  subst P
  have htwoDvd : 2 ∣ m :=
    (rationalPrime_dvd_rationalPrincipalIdeal_iff
      rationalTwoPrime m).mp hP
  exact hm.not_two_dvd_nat htwoDvd

open scoped Classical in
/-- Gauss reciprocity derived from the global power-residue reciprocity
theorem, including the explicitly evaluated dyadic correction.  The proof
does not invoke the pre-existing quadratic-reciprocity theorem. -/
theorem gaussReciprocity_nat_from_powerResidueReciprocity
    {a b : ℕ} (ha : Odd a) (hb : Odd b) (hab : a.Coprime b) :
    J((a : ℤ) | b) * J((b : ℤ) | a) =
      (-1 : ℤ) ^ (a / 2 * (b / 2)) := by
  have ha0 : a ≠ 0 := by
    intro ha0
    subst a
    norm_num at ha
  have hb0 : b ≠ 0 := by
    intro hb0
    subst b
    norm_num at hb
  let aO : 𝓞 ℚ := rationalNatInteger a
  let bO : 𝓞 ℚ := rationalNatInteger b
  have haO0 : aO ≠ 0 := by
    intro h
    exact (Int.ofNat_ne_zero.mpr ha0) (by
      simpa [aO] using congrArg Rat.ringOfIntegersEquiv h)
  have hbO0 : bO ≠ 0 := by
    intro h
    exact (Int.ofNat_ne_zero.mpr hb0) (by
      simpa [bO] using congrArg Rat.ringOfIntegersEquiv h)
  have hspanA : Ideal.span {aO} = rationalPrincipalIdeal a := rfl
  have hspanB : Ideal.span {bO} = rationalPrincipalIdeal b := rfl
  have haB :
      ∀ P : HeightOneSpectrum (𝓞 ℚ),
        P.asIdeal ∣ Ideal.span {bO} → aO ∉ P.asIdeal := by
    intro P hP
    apply rationalPrincipalIdeal_numerator_not_mem_of_coprime aO b
    · simpa [aO] using hab
    · simpa only [hspanB] using hP
  have hbA :
      ∀ P : HeightOneSpectrum (𝓞 ℚ),
        P.asIdeal ∣ Ideal.span {aO} → bO ∉ P.asIdeal := by
    intro P hP
    apply rationalPrincipalIdeal_numerator_not_mem_of_coprime bO a
    · simpa [bO, Nat.coprime_comm] using hab
    · simpa only [hspanA] using hP
  have hrec :=
    idealPowerResidueSymbol_reciprocity_with_bad_place_correction
      ℚ (2 : ℕ+) (by norm_num)
        rationalQuadraticPrimitiveRoots_nonempty
        aO bO haO0 hbO0
        (fun P hP => by
          apply rationalPrincipalIdeal_absNorm_coprime_two_of_odd a ha P
          simpa only [hspanA] using hP)
        (fun P hP => by
          apply rationalPrincipalIdeal_absNorm_coprime_two_of_odd b hb P
          simpa only [hspanB] using hP)
        haB hbA
        (fun P hP =>
          rationalPrincipalIdeal_primeDivisors_away_from_two a ha P
            (by simpa only [hspanA] using hP))
        (fun P hP =>
          rationalPrincipalIdeal_primeDivisors_away_from_two b hb P
            (by simpa only [hspanB] using hP))
  let symbolAB :=
    idealPowerResidueSymbol ℚ (rationalPrincipalIdeal b)
      (rationalPrincipalIdeal_ne_zero b hb0)
      (2 : ℕ+) rationalQuadraticPrimitiveRoots_nonempty aO
      (rationalPrincipalIdeal_absNorm_coprime_two_of_odd b hb)
      (rationalPrincipalIdeal_numerator_not_mem_of_coprime aO b
        (by simpa [aO] using hab))
  let symbolBA :=
    idealPowerResidueSymbol ℚ (rationalPrincipalIdeal a)
      (rationalPrincipalIdeal_ne_zero a ha0)
      (2 : ℕ+) rationalQuadraticPrimitiveRoots_nonempty bO
      (rationalPrincipalIdeal_absNorm_coprime_two_of_odd a ha)
      (rationalPrincipalIdeal_numerator_not_mem_of_coprime bO a
        (by simpa [bO, Nat.coprime_comm] using hab))
  let negPow : rootsOfUnity (((2 : ℕ+) : ℕ)) (𝓞 ℚ) :=
    rationalQuadraticNegOneRoot ^ (a / 2 * (b / 2))
  have hcorrection :
      powerResidueBadPlaceCorrection ℚ (2 : ℕ+) (by norm_num)
          rationalQuadraticPrimitiveRoots_nonempty
          (nonzeroIntegralFieldUnit ℚ aO haO0)
          (nonzeroIntegralFieldUnit ℚ bO hbO0) =
        integralRootsOfUnityToNthRoots ℚ (((2 : ℕ+) : ℕ)) negPow := by
    have hc := rationalQuadraticBadPlaceCorrection_eq_classicalSign a b ha hb
    unfold rationalNaturalFieldUnit at hc
    change
      powerResidueBadPlaceCorrection ℚ (2 : ℕ+) (by norm_num)
          rationalQuadraticPrimitiveRoots_nonempty
          (nonzeroIntegralFieldUnit ℚ aO haO0)
          (nonzeroIntegralFieldUnit ℚ bO hbO0) = _
    exact hc
  have hnegInv :
      (integralRootsOfUnityToNthRoots ℚ (((2 : ℕ+) : ℕ)) negPow)⁻¹ =
        integralRootsOfUnityToNthRoots ℚ (((2 : ℕ+) : ℕ)) negPow := by
    apply inv_eq_of_mul_eq_one_right
    have hroot :
        (integralRootsOfUnityToNthRoots ℚ (((2 : ℕ+) : ℕ)) negPow).1 ^
            (((2 : ℕ+) : ℕ)) = (1 : ℚˣ) :=
      (KummerTheory.mem_nthRootsSubgroup_iff ℚ).mp
        (integralRootsOfUnityToNthRoots ℚ (((2 : ℕ+) : ℕ)) negPow).2
    change
      integralRootsOfUnityToNthRoots ℚ (((2 : ℕ+) : ℕ)) negPow *
          integralRootsOfUnityToNthRoots ℚ (((2 : ℕ+) : ℕ)) negPow = 1
    apply Subtype.ext
    change
      (integralRootsOfUnityToNthRoots ℚ (((2 : ℕ+) : ℕ)) negPow).1 *
          (integralRootsOfUnityToNthRoots ℚ (((2 : ℕ+) : ℕ)) negPow).1 =
        (1 : ℚˣ)
    change
      (integralRootsOfUnityToNthRoots ℚ (((2 : ℕ+) : ℕ)) negPow).1 ^ 2 =
        (1 : ℚˣ) at hroot
    simpa only [pow_two] using hroot
  have hroot : symbolAB = negPow * symbolBA := by
    apply integralRootsOfUnityToNthRoots_injective ℚ (((2 : ℕ+) : ℕ))
    rw [map_mul]
    calc
      integralRootsOfUnityToNthRoots ℚ (((2 : ℕ+) : ℕ)) symbolAB =
          (powerResidueBadPlaceCorrection ℚ (2 : ℕ+) (by norm_num)
            rationalQuadraticPrimitiveRoots_nonempty
            (nonzeroIntegralFieldUnit ℚ aO haO0)
            (nonzeroIntegralFieldUnit ℚ bO hbO0))⁻¹ *
              integralRootsOfUnityToNthRoots ℚ (((2 : ℕ+) : ℕ)) symbolBA := by
        simpa only [hspanA, hspanB, symbolAB, symbolBA] using hrec
      _ = integralRootsOfUnityToNthRoots ℚ (((2 : ℕ+) : ℕ)) negPow *
          integralRootsOfUnityToNthRoots ℚ (((2 : ℕ+) : ℕ)) symbolBA := by
        rw [hcorrection, hnegInv]
  have hvalue := congrArg rationalQuadraticRootValuePNatMonoidHom hroot
  have hAB : rationalQuadraticRootValue symbolAB = J((a : ℤ) | b) := by
    simpa only [symbolAB, aO, rationalNatInteger_equiv] using
      rationalIdealPowerResidueSymbol_two_eq_jacobiSym
        aO b hb0 hb (by simpa [aO] using hab)
  have hBA : rationalQuadraticRootValue symbolBA = J((b : ℤ) | a) := by
    simpa only [symbolBA, bO, rationalNatInteger_equiv] using
      rationalIdealPowerResidueSymbol_two_eq_jacobiSym
        bO a ha0 ha (by simpa [bO, Nat.coprime_comm] using hab)
  have hnegValue :
      rationalQuadraticRootValue negPow =
        (-1 : ℤ) ^ (a / 2 * (b / 2)) := by
    change rationalQuadraticRootValueMonoidHom
      (rationalQuadraticNegOneRoot ^ (a / 2 * (b / 2))) = _
    rw [map_pow, rationalQuadraticRootValueMonoidHom_apply,
      rationalQuadraticRootValue_negOneRoot]
  have hlinear :
      J((a : ℤ) | b) =
        (-1 : ℤ) ^ (a / 2 * (b / 2)) * J((b : ℤ) | a) := by
    unfold rationalQuadraticRootValuePNatMonoidHom at hvalue
    rw [map_mul] at hvalue
    change
      rationalQuadraticRootValue symbolAB =
        rationalQuadraticRootValue negPow *
          rationalQuadraticRootValue symbolBA at hvalue
    rw [hAB, hBA, hnegValue] at hvalue
    exact hvalue
  have hsq : J((b : ℤ) | a) ^ 2 = 1 := by
    apply jacobiSym.sq_one
    simpa [Int.gcd_eq_natAbs] using hab.symm.gcd_eq_one
  calc
    J((a : ℤ) | b) * J((b : ℤ) | a) =
        ((-1 : ℤ) ^ (a / 2 * (b / 2)) * J((b : ℤ) | a)) *
          J((b : ℤ) | a) := by rw [hlinear]
    _ = (-1 : ℤ) ^ (a / 2 * (b / 2)) *
        J((b : ℤ) | a) ^ 2 := by ring
    _ = (-1 : ℤ) ^ (a / 2 * (b / 2)) := by rw [hsq, mul_one]

open scoped Classical in
/-- The CFT-derived theorem agrees propositionally with the existing library
statement.  This comparison is the only place where the pre-existing theorem
is mentioned. -/
theorem gaussReciprocity_nat_from_powerResidueReciprocity_eq_mathlib
    {a b : ℕ} (ha : Odd a) (hb : Odd b) (hab : a.Coprime b) :
    gaussReciprocity_nat_from_powerResidueReciprocity ha hb hab =
      AlgebraicNumberTheory.PowerResidueSymbols.gaussReciprocity_nat
        ha hb hab := by
  apply Subsingleton.elim

end Reciprocity
end GlobalClassFieldTheory
