/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/
module


public import LeanPool.ClassFieldTheory.ClassFieldTheory.AlgebraicNumberTheory.Idele.Basic
public import Mathlib.RingTheory.DedekindDomain.Factorization
public import Mathlib.RingTheory.ClassGroup.Basic
/-!
# The ideal attached to an idele

This file formalizes the ideal map from ideles. Its construction
is explicit: local discrete valuations form a finitely supported integer
vector, and unique factorization of fractional ideals identifies that vector
with a nonzero fractional ideal.  We prove both stages surjective and identify
the kernel with the ideles integral at every finite place.
-/

@[expose] public section

open scoped NumberField RestrictedProduct WithZero
open NumberField IsDedekindDomain

noncomputable
section


variable {K : Type*} [Field K] [NumberField K]

namespace FiniteIdeleGroup

/-- The exponent of a local multiplicative element, normalized so that a
uniformizer has exponent one. -/
def localOrder (v : HeightOneSpectrum (𝓞 K)) :
    (v.adicCompletion K)ˣ →* Multiplicative ℤ :=
  MonoidHom.mk'
    (fun x => Multiplicative.ofAdd (-WithZero.log (Valued.v (x : v.adicCompletion K))))
    fun x y => by
      apply Multiplicative.ext
      simp [WithZero.log_mul, add_comm]

@[simp]
theorem localOrder_apply (v : HeightOneSpectrum (𝓞 K))
    (x : (v.adicCompletion K)ˣ) :
    (localOrder v x).toAdd =
      -WithZero.log (Valued.v (x : v.adicCompletion K)) :=
  rfl

theorem localOrder_eq_zero_iff (v : HeightOneSpectrum (𝓞 K))
    (x : (v.adicCompletion K)ˣ) :
    (localOrder v x).toAdd = 0 ↔
      x ∈ (v.adicCompletionIntegers K).units := by
  rw [localOrder_apply]
  rw [HeightOneSpectrum.adicCompletionIntegers.mem_units_iff_valued_eq_one]
  change -WithZero.log (Valued.v (x : v.adicCompletion K)) = 0 ↔
    Valued.v (x : v.adicCompletion K) = 1
  rw [neg_eq_zero]
  let z : ℤᵐ⁰ := Valued.v (x : v.adicCompletion K)
  have hz : z ≠ 0 := by
    dsimp [z]
    simp
  constructor
  · intro h
    have h' :
        WithZero.logEquiv (Units.mk0 z hz) =
          WithZero.logEquiv (1 : (ℤᵐ⁰)ˣ) := by
      simpa [WithZero.logEquiv_apply] using h
    have hu := (WithZero.logEquiv (G := ℤ)).injective h'
    simpa [z] using congrArg Units.val hu
  · intro h
    rw [h]
    rfl

/-- The set of finite places where a finite idele is not an integral unit is
finite. -/
theorem finite_nonLocalUnits (a : FiniteIdeleGroup K) :
    {v : HeightOneSpectrum (𝓞 K) |
      a v ∉ (v.adicCompletionIntegers K).units}.Finite :=
  Filter.eventually_cofinite.mp a.2

/-- The finitely supported family of normalized local orders of a finite
idele. -/
def valuationVectorAdd (a : FiniteIdeleGroup K) :
    HeightOneSpectrum (𝓞 K) →₀ ℤ :=
  Finsupp.onFinset (finite_nonLocalUnits a).toFinset
    (fun v => (localOrder v (a v)).toAdd) (fun v hv => by
      rw [Set.Finite.mem_toFinset]
      intro hmem
      exact hv ((localOrder_eq_zero_iff v (a v)).2 hmem))

@[simp]
theorem valuationVectorAdd_apply (a : FiniteIdeleGroup K)
    (v : HeightOneSpectrum (𝓞 K)) :
    valuationVectorAdd a v = (localOrder v (a v)).toAdd :=
  rfl

/-- The finite valuation vector is a homomorphism from finite ideles to the
free abelian group on finite places. -/
def valuationVector :
    FiniteIdeleGroup K →* Multiplicative
      (HeightOneSpectrum (𝓞 K) →₀ ℤ) :=
  MonoidHom.mk' (fun a => Multiplicative.ofAdd (valuationVectorAdd a))
    fun a b => by
      apply Multiplicative.ext
      ext v
      exact congrArg Multiplicative.toAdd
        (map_mul (localOrder v) (a v) (b v))

@[simp]
theorem valuationVector_apply (a : FiniteIdeleGroup K)
    (v : HeightOneSpectrum (𝓞 K)) :
    (valuationVector a).toAdd v =
      (localOrder v (a v)).toAdd :=
  rfl

/-- A chosen local element of prescribed normalized order. -/
def chosenLocalOrderSection (v : HeightOneSpectrum (𝓞 K)) (n : ℤ) :
    (v.adicCompletion K)ˣ :=
  let x := Classical.choose
    (HeightOneSpectrum.valuedAdicCompletion_surjective K v
      (WithZero.exp (-n)))
  Units.mk0 x (by
    intro hx
    have hval := Classical.choose_spec
      (HeightOneSpectrum.valuedAdicCompletion_surjective K v
        (WithZero.exp (-n)))
    change Valued.v x = WithZero.exp (-n) at hval
    rw [hx, map_zero] at hval
    exact WithZero.exp_ne_zero hval.symm)

theorem localOrder_chosenLocalOrderSection
    (v : HeightOneSpectrum (𝓞 K)) (n : ℤ) :
    (localOrder v (chosenLocalOrderSection v n)).toAdd = n := by
  rw [localOrder_apply]
  change -WithZero.log
    (Valued.v (Classical.choose
      (HeightOneSpectrum.valuedAdicCompletion_surjective K v
        (WithZero.exp (-n))))) = n
  rw [Classical.choose_spec
    (HeightOneSpectrum.valuedAdicCompletion_surjective K v
      (WithZero.exp (-n)))]
  simp

/-- A finite idele with a prescribed finitely supported valuation vector. -/
def valuationVectorSection
    (e : HeightOneSpectrum (𝓞 K) →₀ ℤ) :
    FiniteIdeleGroup K :=
  ⟨fun v => chosenLocalOrderSection v (e v), by
    filter_upwards [e.support.eventually_cofinite_notMem] with v hv
    apply (localOrder_eq_zero_iff v _).1
    rw [localOrder_chosenLocalOrderSection, Finsupp.notMem_support_iff.mp hv]⟩

@[simp]
theorem valuationVector_valuationVectorSection
    (e : HeightOneSpectrum (𝓞 K) →₀ ℤ) :
    valuationVector (valuationVectorSection e) =
      Multiplicative.ofAdd e := by
  apply Multiplicative.ext
  ext v
  rw [valuationVector_apply]
  change (localOrder v (chosenLocalOrderSection v (e v))).toAdd = e v
  rw [localOrder_chosenLocalOrderSection]

theorem valuationVector_surjective :
    Function.Surjective (valuationVector (K := K)) := by
  intro e
  refine ⟨valuationVectorSection e.toAdd, ?_⟩
  exact valuationVector_valuationVectorSection e.toAdd

end FiniteIdeleGroup

/-- The group of nonzero fractional ideals of a number field. -/
abbrev FractionalIdealGroup (K : Type*) [Field K] :=
  (FractionalIdeal (nonZeroDivisors (𝓞 K)) K)ˣ

namespace FractionalIdealGroup

/-- The fractional ideal represented by a finite prime. -/
def prime (v : HeightOneSpectrum (𝓞 K)) :
    FractionalIdealGroup K :=
  Units.mk0 (v.asIdeal : FractionalIdeal (nonZeroDivisors (𝓞 K)) K)
    (FractionalIdeal.coeIdeal_ne_zero.mpr v.ne_bot)

/-- The homomorphism sending an integer exponent to the corresponding
power of a finite prime. -/
def primePowerHom (v : HeightOneSpectrum (𝓞 K)) :
    Multiplicative ℤ →* FractionalIdealGroup K :=
  MonoidHom.mk' (fun n => prime v ^ n.toAdd) fun m n => by
    simp [zpow_add]

/-- Reconstruct a fractional ideal from its finitely supported vector
of prime exponents. -/
def factorization :
    Multiplicative (HeightOneSpectrum (𝓞 K) →₀ ℤ) →*
      FractionalIdealGroup K :=
  MonoidHom.mk' (fun exps =>
      exps.toAdd.prod fun v n => primePowerHom v (Multiplicative.ofAdd n))
    fun a b => by
      exact Finsupp.prod_hom_add_index (fun v => primePowerHom v)

@[simp]
theorem factorization_val (exps :
    Multiplicative (HeightOneSpectrum (𝓞 K) →₀ ℤ)) :
    ((factorization exps : FractionalIdealGroup K) :
      FractionalIdeal (nonZeroDivisors (𝓞 K)) K) =
      exps.toAdd.prod fun v n =>
        (v.asIdeal : FractionalIdeal (nonZeroDivisors (𝓞 K)) K) ^ n := by
  classical
  simp [factorization, primePowerHom, prime, Finsupp.prod]

theorem finite_count_support (I : FractionalIdealGroup K) :
    {v : HeightOneSpectrum (𝓞 K) |
      FractionalIdeal.count K v
        (I : FractionalIdeal (nonZeroDivisors (𝓞 K)) K) ≠ 0}.Finite :=
  Filter.eventually_cofinite.mp
    (FractionalIdeal.finite_factors
      (I : FractionalIdeal (nonZeroDivisors (𝓞 K)) K))

/-- The finitely supported vector of prime exponents of a nonzero
fractional ideal. -/
def countVector (I : FractionalIdealGroup K) :
    HeightOneSpectrum (𝓞 K) →₀ ℤ :=
  Finsupp.onFinset (finite_count_support I).toFinset
    (fun v => FractionalIdeal.count K v
      (I : FractionalIdeal (nonZeroDivisors (𝓞 K)) K))
    (fun v hv => by
      rw [Set.Finite.mem_toFinset]
      exact hv)

@[simp]
theorem countVector_apply (I : FractionalIdealGroup K)
    (v : HeightOneSpectrum (𝓞 K)) :
    countVector I v =
      FractionalIdeal.count K v
        (I : FractionalIdeal (nonZeroDivisors (𝓞 K)) K) :=
  rfl

theorem count_factorization (exps :
    Multiplicative (HeightOneSpectrum (𝓞 K) →₀ ℤ))
    (v : HeightOneSpectrum (𝓞 K)) :
    FractionalIdeal.count K v
      ((factorization exps : FractionalIdealGroup K) :
        FractionalIdeal (nonZeroDivisors (𝓞 K)) K) =
      exps.toAdd v := by
  rw [factorization_val]
  exact FractionalIdeal.count_finsuppProd K v exps.toAdd

theorem ext_count {I J : FractionalIdealGroup K}
    (h : ∀ v : HeightOneSpectrum (𝓞 K),
      FractionalIdeal.count K v
        (I : FractionalIdeal (nonZeroDivisors (𝓞 K)) K) =
      FractionalIdeal.count K v
        (J : FractionalIdeal (nonZeroDivisors (𝓞 K)) K)) :
    I = J := by
  apply Units.ext
  rw [← FractionalIdeal.finprod_heightOneSpectrum_factorization'
      K (Units.ne_zero I),
    ← FractionalIdeal.finprod_heightOneSpectrum_factorization'
      K (Units.ne_zero J)]
  exact finprod_congr fun v => congrArg
    (fun n : ℤ =>
      (v.asIdeal : FractionalIdeal (nonZeroDivisors (𝓞 K)) K) ^ n) (h v)

theorem factorization_injective :
    Function.Injective (factorization (K := K)) := by
  intro a b hab
  apply Multiplicative.ext
  ext v
  rw [← count_factorization a v, ← count_factorization b v, hab]

theorem factorization_surjective :
    Function.Surjective (factorization (K := K)) := by
  intro I
  refine ⟨Multiplicative.ofAdd (countVector I), ?_⟩
  apply ext_count
  intro v
  rw [count_factorization]
  change countVector I v =
    FractionalIdeal.count K v
      (I : FractionalIdeal (nonZeroDivisors (𝓞 K)) K)
  exact countVector_apply I v

/-- Multiplicative unique factorization of nonzero fractional ideals by
finite primes. -/
def factorizationEquiv :
    Multiplicative (HeightOneSpectrum (𝓞 K) →₀ ℤ) ≃*
      FractionalIdealGroup K :=
  MulEquiv.ofBijective (factorization (K := K))
    ⟨factorization_injective, factorization_surjective⟩

end FractionalIdealGroup

namespace FiniteIdeleGroup

/-- The fractional ideal attached to a finite idele. -/
def fractionalIdeal :
    FiniteIdeleGroup K →* FractionalIdealGroup K :=
  (FractionalIdealGroup.factorizationEquiv (K := K)).toMonoidHom.comp
    (valuationVector (K := K))

theorem fractionalIdeal_surjective :
    Function.Surjective (fractionalIdeal (K := K)) :=
  (FractionalIdealGroup.factorizationEquiv (K := K)).surjective.comp
    valuationVector_surjective

/-- Finite ideles integral at every finite place. -/
def integralSubgroup : Subgroup (FiniteIdeleGroup K) where
  carrier := {a | ∀ v : HeightOneSpectrum (𝓞 K),
    a v ∈ (v.adicCompletionIntegers K).units}
  one_mem' v := (v.adicCompletionIntegers K).units.one_mem
  mul_mem' ha hb v :=
    (v.adicCompletionIntegers K).units.mul_mem (ha v) (hb v)
  inv_mem' ha v :=
    (v.adicCompletionIntegers K).units.inv_mem (ha v)

@[simp]
theorem mem_integralSubgroup_iff (a : FiniteIdeleGroup K) :
    a ∈ integralSubgroup ↔
      ∀ v : HeightOneSpectrum (𝓞 K),
        a v ∈ (v.adicCompletionIntegers K).units :=
  Iff.rfl

theorem fractionalIdeal_ker :
    (fractionalIdeal (K := K)).ker = integralSubgroup := by
  ext a
  constructor
  · intro ha v
    have hv :
        valuationVector a =
          (1 : Multiplicative
            (HeightOneSpectrum (𝓞 K) →₀ ℤ)) := by
      apply (FractionalIdealGroup.factorizationEquiv
        (K := K)).injective
      simpa [fractionalIdeal] using ha
    apply (localOrder_eq_zero_iff v (a v)).1
    rw [← valuationVector_apply a v, hv]
    rfl
  · intro ha
    have hv :
        valuationVector a =
          (1 : Multiplicative
            (HeightOneSpectrum (𝓞 K) →₀ ℤ)) := by
      apply Multiplicative.ext
      ext v
      rw [valuationVector_apply]
      exact (localOrder_eq_zero_iff v (a v)).2 (ha v)
    simp [fractionalIdeal, hv]

/-- The ideal group as the quotient of finite ideles by the everywhere
integral finite ideles. -/
def quotientIntegralEquiv :
    FiniteIdeleGroup K ⧸ integralSubgroup ≃*
      FractionalIdealGroup K := by
  rw [← fractionalIdeal_ker]
  exact QuotientGroup.quotientKerEquivOfSurjective
    fractionalIdeal fractionalIdeal_surjective

end FiniteIdeleGroup

namespace IdeleGroup

/-- The fractional ideal attached to an idele. The archimedean components
do not contribute. -/
def fractionalIdeal :
    IdeleGroup K →* FractionalIdealGroup K :=
  (FiniteIdeleGroup.fractionalIdeal (K := K)).comp
    (MonoidHom.snd _ _)

theorem fractionalIdeal_surjective :
    Function.Surjective (fractionalIdeal (K := K)) := by
  intro I
  obtain ⟨a, rfl⟩ :=
    FiniteIdeleGroup.fractionalIdeal_surjective (K := K) I
  exact ⟨(1, a), rfl⟩

/-- Ideles integral at every finite place; this is the subgroup
`I_K^{S∞}`. -/
def integralAtFinitePlaces : Subgroup (IdeleGroup K) :=
  Subgroup.comap (MonoidHom.snd _ _)
    (FiniteIdeleGroup.integralSubgroup (K := K))

theorem fractionalIdeal_ker :
    (fractionalIdeal (K := K)).ker = integralAtFinitePlaces := by
  ext a
  change FiniteIdeleGroup.fractionalIdeal a.2 = 1 ↔
    a.2 ∈ FiniteIdeleGroup.integralSubgroup
  rw [← MonoidHom.mem_ker,
    FiniteIdeleGroup.fractionalIdeal_ker]

/-- The ideal group as the quotient of all ideles by those integral at
every finite place. -/
def quotientIntegralEquiv :
    IdeleGroup K ⧸ integralAtFinitePlaces ≃*
      FractionalIdealGroup K := by
  rw [← fractionalIdeal_ker]
  exact QuotientGroup.quotientKerEquivOfSurjective
    fractionalIdeal fractionalIdeal_surjective

/-- The canonical surjection from ideles to the ordinary ideal class
group. -/
def idealClass :
    IdeleGroup K →* ClassGroup (𝓞 K) :=
  (ClassGroup.mk K).comp (fractionalIdeal (K := K))

theorem idealClass_surjective :
    Function.Surjective (idealClass (K := K)) := by
  intro c
  induction c using ClassGroup.induction (R := 𝓞 K) K with
  | h I =>
      obtain ⟨a, ha⟩ := fractionalIdeal_surjective (K := K) I
      exact ⟨a, by simp [idealClass, ha]⟩

/-- A quotient form of the ideal-class map. The following results identify
this kernel with `I_K^{S∞} Kˣ`. -/
def quotientIdealClassKernelEquiv :
    IdeleGroup K ⧸ (idealClass (K := K)).ker ≃*
      ClassGroup (𝓞 K) :=
  QuotientGroup.quotientKerEquivOfSurjective
    idealClass idealClass_surjective

end IdeleGroup
