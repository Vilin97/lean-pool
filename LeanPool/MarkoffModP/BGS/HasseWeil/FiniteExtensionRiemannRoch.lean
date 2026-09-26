/-
Copyright (c) 2026 Yuma Mizuno. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuma Mizuno
-/
module


public import LeanPool.MarkoffModP.BGS.HasseWeil.FiniteExtensionDivisorClassRecurrence
public import LeanPool.MarkoffModP.RiemannRoch.CoordinateFree.RiemannRoch

/-!
# Riemann--Roch for the exhaustive finite-extension place model

This file identifies the exhaustive finite and infinite places used by the BGS
function-field development with the two-chart place model of the vendored
Riemann--Roch library.  The identification transports residue degrees,
divisors, divisor degree, normalized valuations, and Riemann spaces.  It then
applies the axiom-clean Riemann--Roch theorem to discharge the eventual uniform
Riemann formula required by the divisor-class recurrence.

The only non-definitional chart issue is at infinity: the two developments
construct the same valuation subring using different `DecidableEq` instances.
We therefore record the identity-on-elements ring equivalence explicitly and
transport the integral closure and its height-one primes across it.
-/

@[expose] public section

namespace BGS.HasseWeil

open BGS.CorvajaZannier
open IsDedekindDomain Multiplicative WithZero
open scoped Polynomial

noncomputable section

variable (K : Type*) [Field K] [Fintype K] [DecidableEq K]
  [DecidableEq (RatFunc K)]
variable (L : Type*) [Field L] [Algebra (RatFunc K) L]
  [FiniteDimensional (RatFunc K) L]
  [Algebra.IsSeparable (RatFunc K) L]

local instance riemannRochConstantAlgebra : Algebra K L :=
  RingHom.toAlgebra ((algebraMap (RatFunc K) L).comp
    (algebraMap K (RatFunc K)))

local instance riemannRochConstantRatFuncTower : IsScalarTower K (RatFunc K) L :=
  IsScalarTower.of_algebraMap_eq' rfl

local instance (priority := 10) riemannRochPolynomialAlgebra : Algebra K[X] L :=
  RingHom.toAlgebra ((algebraMap (RatFunc K) L).comp
    (algebraMap K[X] (RatFunc K)))

local instance riemannRochPolynomialRatFuncTower :
    IsScalarTower K[X] (RatFunc K) L :=
  IsScalarTower.of_algebraMap_eq' rfl

local instance riemannRochConstantPolynomialTower : IsScalarTower K K[X] L :=
  IsScalarTower.of_algebraMap_eq' rfl

local instance riemannRochInfinityBaseConstantAlgebra :
    Algebra K (RatFuncInfinityIntegers K) :=
  (ratFuncInfinityConstantRingHom K).toAlgebra

local instance riemannRochInfinityClosureModuleFinite :
    Module.Finite (RatFuncInfinityIntegers K)
      (RatFuncInfinityIntegralClosure K L) :=
  IsIntegralClosure.finite (RatFuncInfinityIntegers K) (RatFunc K) L
    (RatFuncInfinityIntegralClosure K L)

local instance riemannRochInfinityClosureIsIntegral :
    Algebra.IsIntegral (RatFuncInfinityIntegers K)
      (RatFuncInfinityIntegralClosure K L) :=
  IsIntegralClosure.isIntegral_algebra (RatFuncInfinityIntegers K) L

local instance riemannRochInfinityBaseTorsionFreeTop :
    Module.IsTorsionFree (RatFuncInfinityIntegers K) L :=
  Module.IsTorsionFree.trans_faithfulSMul
    (RatFuncInfinityIntegers K) (RatFunc K) L

local instance riemannRochInfinityClosureIsTorsionFree :
    Module.IsTorsionFree (RatFuncInfinityIntegers K)
      (RatFuncInfinityIntegralClosure K L) :=
  IsIntegralClosure.isTorsionFree (RatFuncInfinityIntegers K) L

local instance riemannRochInfinityClosureIsDedekind :
    IsDedekindDomain (RatFuncInfinityIntegralClosure K L) :=
  IsIntegralClosure.isDedekindDomain
    (RatFuncInfinityIntegers K) (RatFunc K) L
    (RatFuncInfinityIntegralClosure K L)

local instance riemannRochInfinityClosureIsFractionRing :
    IsFractionRing (RatFuncInfinityIntegralClosure K L) L :=
  IsIntegralClosure.isFractionRing_of_finite_extension
    (RatFuncInfinityIntegers K) (RatFunc K) L
    (RatFuncInfinityIntegralClosure K L)

local instance riemannRochInfinityClosureConstantAlgebra :
    Algebra K (RatFuncInfinityIntegralClosure K L) :=
  RingHom.toAlgebra
    ((algebraMap (RatFuncInfinityIntegers K)
      (RatFuncInfinityIntegralClosure K L)).comp
      (algebraMap K (RatFuncInfinityIntegers K)))

local instance riemannRochInfinityClosureConstantTower :
    IsScalarTower K (RatFuncInfinityIntegers K)
      (RatFuncInfinityIntegralClosure K L) :=
  IsScalarTower.of_algebraMap_eq' rfl

/-- The BGS and Riemann--Roch infinity valuation subrings are the same
subring of `RatFunc K`; this equivalence makes the harmless instance-level
difference explicit. -/
def finiteExtensionInfinityBaseRingEquiv :
    RatFuncInfinityIntegers K ≃+*
      FunctionField.Chart.inftyValuationSubring K where
  toFun x := ⟨x.1, by
    have hx := x.2
    unfold RatFuncInfinityIntegers at hx
    rw [Valuation.mem_integer_iff] at hx
    rw [Valuation.mem_valuationSubring_iff]
    have hdec : (inferInstance : DecidableEq (RatFunc K)) =
        Classical.decEq (RatFunc K) := Subsingleton.elim _ _
    cases hdec
    exact hx⟩
  invFun x := ⟨x.1, by
    have hx := x.2
    unfold FunctionField.Chart.inftyValuationSubring at hx
    rw [Valuation.mem_valuationSubring_iff] at hx
    unfold RatFuncInfinityIntegers
    rw [Valuation.mem_integer_iff]
    have hdec : (inferInstance : DecidableEq (RatFunc K)) =
        Classical.decEq (RatFunc K) := Subsingleton.elim _ _
    cases hdec
    exact hx⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_mul' _ _ := rfl
  map_add' _ _ := rfl

omit [Fintype K] [DecidableEq K] in
@[simp]
theorem finiteExtensionInfinityBaseRingEquiv_apply_coe
    (x : RatFuncInfinityIntegers K) :
    ((finiteExtensionInfinityBaseRingEquiv K x :
      FunctionField.Chart.inftyValuationSubring K) : RatFunc K) = x :=
  rfl

omit [Fintype K] [DecidableEq K] [FiniteDimensional (RatFunc K) L]
  [Algebra.IsSeparable (RatFunc K) L] in
private theorem isIntegral_infinityBase_iff (x : L) :
    IsIntegral (RatFuncInfinityIntegers K) x ↔
      IsIntegral (FunctionField.Chart.inftyValuationSubring K) x := by
  let e := finiteExtensionInfinityBaseRingEquiv K
  have hforward :
      (algebraMap (FunctionField.Chart.inftyValuationSubring K) L).comp
          e.toRingHom =
        algebraMap (RatFuncInfinityIntegers K) L := by
    ext a
    rfl
  have hbackward :
      (algebraMap (RatFuncInfinityIntegers K) L).comp
          e.symm.toRingHom =
        algebraMap (FunctionField.Chart.inftyValuationSubring K) L := by
    ext a
    rfl
  constructor
  · intro hx
    have hx' :
        ((algebraMap (FunctionField.Chart.inftyValuationSubring K) L).comp
          e.toRingHom).IsIntegralElem x := by
      rw [hforward]
      exact hx
    exact hx'.of_comp
  · intro hx
    have hx' :
        ((algebraMap (RatFuncInfinityIntegers K) L).comp
          e.symm.toRingHom).IsIntegralElem x := by
      rw [hbackward]
      exact hx
    exact hx'.of_comp

/-- Identity-on-`L` equivalence between the two infinity integral closures. -/
def finiteExtensionInfinityIntegralClosureRingEquiv :
    RatFuncInfinityIntegralClosure K L ≃+*
      FunctionField.Chart.infiniteIntegers K L where
  toFun x := ⟨x.1, by exact (isIntegral_infinityBase_iff K L x.1).mp x.2⟩
  invFun x := ⟨x.1, by exact (isIntegral_infinityBase_iff K L x.1).mpr x.2⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_mul' _ _ := rfl
  map_add' _ _ := rfl

omit [Fintype K] [DecidableEq K] [FiniteDimensional (RatFunc K) L]
  [Algebra.IsSeparable (RatFunc K) L] in
@[simp]
theorem finiteExtensionInfinityIntegralClosureRingEquiv_apply_coe
    (x : RatFuncInfinityIntegralClosure K L) :
    ((finiteExtensionInfinityIntegralClosureRingEquiv K L x :
      FunctionField.Chart.infiniteIntegers K L) : L) = x :=
  rfl

/-- Constant-field-linear form of the infinity integral-closure equivalence. -/
def finiteExtensionInfinityIntegralClosureAlgEquiv :
    RatFuncInfinityIntegralClosure K L ≃ₐ[K]
      FunctionField.Chart.infiniteIntegers K L where
  __ := finiteExtensionInfinityIntegralClosureRingEquiv K L
  commutes' c := by
    apply Subtype.ext
    rfl

/-- Places above the BGS infinity place are exactly the height-one primes of
the BGS infinity integral closure. -/
def finiteExtensionInfinityPrimesOverEquivHeightOne :
    FiniteExtensionInfinityPlace K L ≃
      HeightOneSpectrum (RatFuncInfinityIntegralClosure K L) where
  toFun P := primeOverHeightOne (ratFuncInfinityPlace K) P
  invFun q := ⟨q.asIdeal, q.isPrime, ⟨by
    let A := RatFuncInfinityIntegers K
    let : q.asIdeal.IsMaximal := q.isPrime.isMaximal q.ne_bot
    have hq : q.asIdeal.under A = IsLocalRing.maximalIdeal A :=
      IsLocalRing.eq_maximalIdeal (Ideal.IsMaximal.under A q.asIdeal)
    have hp : (ratFuncInfinityPlace K).asIdeal =
        IsLocalRing.maximalIdeal A :=
      IsLocalRing.eq_maximalIdeal
        ((ratFuncInfinityPlace K).isPrime.isMaximal
          (ratFuncInfinityPlace K).ne_bot)
    exact (hq.trans hp.symm).symm⟩⟩
  left_inv P := by
    apply Subtype.ext
    rfl
  right_inv q := by
    apply HeightOneSpectrum.ext
    rfl

/-- Infinity places in the exhaustive BGS model and in the Riemann--Roch chart. -/
def finiteExtensionInfinityPlaceEquivChart :
    FiniteExtensionInfinityPlace K L ≃
      HeightOneSpectrum (FunctionField.Chart.infiniteIntegers K L) :=
  (finiteExtensionInfinityPrimesOverEquivHeightOne K L).trans
    (HeightOneSpectrum.equivOfRingEquiv
      (finiteExtensionInfinityIntegralClosureRingEquiv K L))

/-- Equivalence from the exhaustive BGS place type to the Riemann--Roch
two-chart place type. -/
def finiteExtensionPlaceEquivChart :
    FiniteExtensionPlace K L ≃ FunctionField.Chart.PlaceA K L :=
  Equiv.sumCongr (Equiv.refl _)
    (finiteExtensionInfinityPlaceEquivChart K L)

noncomputable def finiteExtensionFiniteQuotientResidueAlgEquiv
    (q : FiniteExtensionFinitePlace K L) :
    (RatFuncFiniteIntegralClosure K L ⧸ q.asIdeal) ≃ₐ[K]
      q.asIdeal.ResidueField := by
  letI : q.asIdeal.IsMaximal := q.isPrime.isMaximal q.ne_bot
  exact AlgEquiv.ofBijective
    (IsScalarTower.toAlgHom K
      (RatFuncFiniteIntegralClosure K L ⧸ q.asIdeal)
      q.asIdeal.ResidueField)
    (Ideal.bijective_algebraMap_quotient_residueField q.asIdeal)

noncomputable def finiteExtensionInfinityQuotientResidueAlgEquiv
    (q : HeightOneSpectrum (FunctionField.Chart.infiniteIntegers K L)) :
    (FunctionField.Chart.infiniteIntegers K L ⧸ q.asIdeal) ≃ₐ[K]
      q.asIdeal.ResidueField := by
  letI : q.asIdeal.IsMaximal := q.isPrime.isMaximal q.ne_bot
  exact AlgEquiv.ofBijective
    (IsScalarTower.toAlgHom K
      (FunctionField.Chart.infiniteIntegers K L ⧸ q.asIdeal)
      q.asIdeal.ResidueField)
    (Ideal.bijective_algebraMap_quotient_residueField q.asIdeal)

noncomputable def finiteExtensionInfinityResidueAlgEquiv
    (P : FiniteExtensionInfinityPlace K L) :
    P.1.ResidueField ≃ₐ[K]
      (finiteExtensionInfinityPlaceEquivChart K L P).asIdeal.ResidueField := by
  let e := finiteExtensionInfinityIntegralClosureAlgEquiv K L
  apply Ideal.residueFieldAlgEquiv P.1
    (finiteExtensionInfinityPlaceEquivChart K L P).asIdeal e
  change P.1 = (P.1.comap e.symm).comap e
  exact (Ideal.comap_of_equiv e.toRingEquiv).symm

omit [Fintype K] in
/-- The exhaustive place degree agrees with the Riemann--Roch chart degree. -/
theorem finiteExtensionPlaceDegree_eq_chart
    (v : FiniteExtensionPlace K L) :
    finiteExtensionPlaceDegree K L v =
      FunctionField.Chart.placeDegree K L
        (finiteExtensionPlaceEquivChart K L v) := by
  rcases v with q | P
  · rw [finiteExtensionFinitePlace_degree_eq_finrank_residueField K L q]
    change Module.finrank K q.asIdeal.ResidueField =
      Module.finrank K (RatFuncFiniteIntegralClosure K L ⧸ q.asIdeal)
    exact (finiteExtensionFiniteQuotientResidueAlgEquiv K L q).toLinearEquiv.finrank_eq.symm
  · rw [finiteExtensionInfinityPlace_degree_eq_finrank_residueField K L P]
    let q := finiteExtensionInfinityPlaceEquivChart K L P
    change Module.finrank K P.1.ResidueField =
      Module.finrank K (FunctionField.Chart.infiniteIntegers K L ⧸ q.asIdeal)
    exact (finiteExtensionInfinityResidueAlgEquiv K L P).toLinearEquiv.finrank_eq.trans
      (finiteExtensionInfinityQuotientResidueAlgEquiv K L q).toLinearEquiv.finrank_eq.symm

private theorem heightOneValuation_le_one_of_ringEquiv_of_asIdeal
    {R S F : Type*} [CommRing R] [CommRing S] [Field F]
    [Algebra R F] [Algebra S F] [IsFractionRing R F] [IsFractionRing S F]
    [IsDedekindDomain R] [IsDedekindDomain S]
    (e : R ≃+* S)
    (halg : ∀ r : R, algebraMap S F (e r) = algebraMap R F r)
    (q : HeightOneSpectrum R) (q' : HeightOneSpectrum S)
    (hideal : q'.asIdeal = q.asIdeal.comap e.symm)
    (x : F) (hx : q.valuation F x ≤ 1) : q'.valuation F x ≤ 1 := by
  obtain ⟨n, d, hnd⟩ := q.exists_primeCompl_mul_eq_of_integer x hx
  have hd' : e d.1 ∉ q'.asIdeal := by
    intro hmem
    have hd : (d.1 : R) ∉ q.asIdeal := d.2
    apply hd
    rw [hideal] at hmem
    change e.symm (e d.1) ∈ q.asIdeal at hmem
    simpa using hmem
  have hnd' :
      x * algebraMap S F (e d.1) = algebraMap S F (e n) := by
    simpa only [halg] using hnd
  have hval := congrArg (q'.valuation F) hnd'
  rw [map_mul, q'.valuation_eq_one_iff_notMem (K := F).2 hd'] at hval
  simp only [mul_one] at hval
  rw [hval]
  exact q'.valuation_le_one (K := F) (e n)

private theorem heightOneValuation_isEquiv_of_ringEquiv_of_asIdeal
    {R S F : Type*} [CommRing R] [CommRing S] [Field F]
    [Algebra R F] [Algebra S F] [IsFractionRing R F] [IsFractionRing S F]
    [IsDedekindDomain R] [IsDedekindDomain S]
    (e : R ≃+* S)
    (halg : ∀ r : R, algebraMap S F (e r) = algebraMap R F r)
    (q : HeightOneSpectrum R) (q' : HeightOneSpectrum S)
    (hideal : q'.asIdeal = q.asIdeal.comap e.symm) :
    (q.valuation F).IsEquiv (q'.valuation F) := by
  apply Valuation.isEquiv_of_val_le_one
  intro x
  constructor
  · exact heightOneValuation_le_one_of_ringEquiv_of_asIdeal
      e halg q q' hideal x
  · intro hx
    have halg' : ∀ s : S,
        algebraMap R F (e.symm s) = algebraMap S F s := by
      intro s
      rw [← halg (e.symm s), e.apply_symm_apply]
    have hideal' : q.asIdeal = q'.asIdeal.comap e := by
      ext r
      rw [Ideal.mem_comap, hideal, Ideal.mem_comap]
      simp
    exact heightOneValuation_le_one_of_ringEquiv_of_asIdeal
      e.symm halg' q' q hideal' x hx

private theorem valuation_eq_of_isEquiv_of_surjective
    {F : Type*} [Field F] (v w : Valuation F ℤᵐ⁰)
    (hvw : v.IsEquiv w) (hv : Function.Surjective v)
    (hw : Function.Surjective w) : v = w := by
  obtain ⟨π, hvπ⟩ := hv (WithZero.exp (-1 : ℤ))
  have hπ : π ≠ 0 := by
    apply (Valuation.ne_zero_iff v).mp
    rw [hvπ]
    exact WithZero.exp_ne_zero
  have hwπ0 : w π ≠ 0 :=
    (hvw.eq_zero.ne).mp ((Valuation.ne_zero_iff v).2 hπ)
  let m : ℤ := -WithZero.log (w π)
  have hmpos : 0 < m := by
    have hvπlt : v π < 1 := by
      rw [hvπ, ← WithZero.exp_zero, WithZero.exp_lt_exp]
      omega
    have hwπlt : w π < 1 := hvw.lt_one_iff_lt_one.mp hvπlt
    have hlog : WithZero.log (w π) < 0 := by
      rw [← WithZero.log_one]
      exact (WithZero.log_lt_log hwπ0 one_ne_zero).2 hwπlt
    dsimp only [m]
    omega
  have hformula (x : F) (hx : x ≠ 0) :
      w x = WithZero.exp (m * WithZero.log (v x)) := by
    have hvx0 : v x ≠ 0 := (Valuation.ne_zero_iff v).2 hx
    let n : ℤ := WithZero.log (v x)
    have hvpow : v (π ^ (-n)) = v x := by
      rw [map_zpow₀, hvπ, ← WithZero.exp_zsmul]
      rw [← WithZero.exp_log hvx0]
      congr 1
      dsimp only [n]
      simp
    have hwpow : w (π ^ (-n)) = w x := hvw.eq_iff.mp hvpow
    calc
      w x = w (π ^ (-n)) := hwpow.symm
      _ = (w π) ^ (-n) := by rw [map_zpow₀]
      _ = WithZero.exp ((-n) • WithZero.log (w π)) := by
        rw [WithZero.exp_zsmul, WithZero.exp_log hwπ0]
      _ = WithZero.exp (m * WithZero.log (v x)) := by
        congr 1
        dsimp only [m, n]
        ring
  obtain ⟨y, hwy⟩ := hw (WithZero.exp (1 : ℤ))
  have hy : y ≠ 0 := by
    apply (Valuation.ne_zero_iff w).mp
    rw [hwy]
    exact WithZero.exp_ne_zero
  have hm : m * WithZero.log (v y) = 1 := by
    apply WithZero.exp_injective
    rw [← hformula y hy, hwy]
  have hm1 : m = 1 := by
    rcases Int.mul_eq_one_iff_eq_one_or_neg_one.mp hm with h | h
    · exact h.1
    · omega
  ext x
  by_cases hx : x = 0
  · subst x
    simp
  · rw [hformula x hx, hm1, one_mul,
      WithZero.exp_log ((Valuation.ne_zero_iff v).2 hx)]

omit [Fintype K] [DecidableEq K] in
/-- The normalized infinity valuation is unchanged by the identity-on-`L`
integral-closure transport. -/
theorem finiteExtensionInfinityPlaceValuation_eq_chart
    (P : FiniteExtensionInfinityPlace K L) :
    (primeOverHeightOne (ratFuncInfinityPlace K) P).valuation L =
      (finiteExtensionInfinityPlaceEquivChart K L P).valuation L := by
  let q := primeOverHeightOne
    (R := RatFuncInfinityIntegers K)
    (S := RatFuncInfinityIntegralClosure K L)
    (ratFuncInfinityPlace K) P
  let e := finiteExtensionInfinityIntegralClosureRingEquiv K L
  let q' := finiteExtensionInfinityPlaceEquivChart K L P
  have hideal : q'.asIdeal = q.asIdeal.comap e.symm := by
    rfl
  have hequiv : (q.valuation L).IsEquiv (q'.valuation L) :=
    heightOneValuation_isEquiv_of_ringEquiv_of_asIdeal
      e (fun _ => rfl) q q' hideal
  change q.valuation L = q'.valuation L
  exact valuation_eq_of_isEquiv_of_surjective
    (q.valuation L) (q'.valuation L) hequiv
    (show Function.Surjective (q.valuation L) from
      HeightOneSpectrum.valuation_surjective (K := L) q)
    (show Function.Surjective (q'.valuation L) from
      HeightOneSpectrum.valuation_surjective (K := L) q')

/-- The normalized valuation attached to an exhaustive BGS place. -/
def finiteExtensionPlaceValuation :
    FiniteExtensionPlace K L → Valuation L ℤᵐ⁰
  | .inl q => q.valuation L
  | .inr P =>
      (primeOverHeightOne (ratFuncInfinityPlace K) P).valuation L

omit [Fintype K] [DecidableEq K] in
/-- Every exhaustive BGS place carries exactly the normalized valuation of
its corresponding Riemann--Roch chart place. -/
theorem finiteExtensionPlaceValuation_eq_chart
    (v : FiniteExtensionPlace K L) :
    finiteExtensionPlaceValuation K L v =
      FunctionField.Chart.placeValuation K L
        (finiteExtensionPlaceEquivChart K L v) := by
  rcases v with q | P
  · rfl
  · exact finiteExtensionInfinityPlaceValuation_eq_chart K L P

/-- Transport of exhaustive divisors to the two-chart Riemann--Roch model. -/
def finiteExtensionDivisorEquivChart :
    FiniteExtensionDivisor K L ≃+
      FunctionField.Chart.DivisorA K L :=
  Finsupp.domCongr (finiteExtensionPlaceEquivChart K L)

omit [Fintype K] in
/-- Divisor degree is preserved by the exhaustive-place/chart equivalence. -/
theorem finiteExtensionDivisorDegree_eq_chart
    (D : FiniteExtensionDivisor K L) :
    finiteExtensionDivisorDegree K L D =
      FunctionField.Chart.deg K L
        (finiteExtensionDivisorEquivChart K L D) := by
  classical
  induction D using Finsupp.induction with
  | zero =>
      simp [finiteExtensionDivisorDegree, FunctionField.Chart.deg,
        finiteExtensionDivisorEquivChart]
  | single_add v n D hv hn ih =>
      rw [map_add, finiteExtensionDivisorDegree_add,
        FunctionField.Chart.deg_add, ih]
      congr 1
      simp [finiteExtensionDivisorDegree, FunctionField.Chart.deg,
        finiteExtensionDivisorEquivChart, Finsupp.domCongr_apply,
        Finsupp.equivMapDomain_single,
        finiteExtensionPlaceDegree_eq_chart]

omit [Fintype K] in
/-- The valuation of a nonzero function is the exponential of the negative
coefficient of its exhaustive principal divisor. -/
theorem finiteExtensionPlaceValuation_eq_exp_neg_principalDivisor
    (x : L) (hx : x ≠ 0) (v : FiniteExtensionPlace K L) :
    finiteExtensionPlaceValuation K L v x =
      WithZero.exp (-(finiteExtensionPrincipalDivisor K L x v)) := by
  rcases v with q | P
  · change q.valuation L x = _
    rw [finiteExtensionPrincipalDivisor_inl_eq_finitePlaceOrder,
      valuation_eq_exp_neg_finitePlaceOrder q x hx]
  · change (primeOverHeightOne (ratFuncInfinityPlace K) P).valuation L x = _
    rw [finiteExtensionPrincipalDivisor_inr_eq_infinityPlaceOrder,
      valuation_eq_exp_neg_finitePlaceOrder
        (primeOverHeightOne (ratFuncInfinityPlace K) P) x hx]

/-- The BGS all-place Riemann space is the Riemann--Roch chart space after
transporting its divisor. -/
theorem finiteExtensionRiemannSpace_eq_chart
    (D : FiniteExtensionDivisor K L) :
    finiteExtensionRiemannSpace K L D =
      FunctionField.Chart.RRspace K L
        (finiteExtensionDivisorEquivChart K L D) := by
  classical
  ext x
  rw [mem_finiteExtensionRiemannSpace,
    FunctionField.Chart.mem_RRspace_iff]
  constructor
  · rintro (rfl | ⟨hx, horders⟩)
    · intro w
      rw [Valuation.map_zero]
      exact zero_le
    · intro w
      let v := (finiteExtensionPlaceEquivChart K L).symm w
      have horder := horders v
      have hInt :
          -(finiteExtensionPrincipalDivisor K L x v) ≤ D v := by
        omega
      have hExp :
          WithZero.exp (-(finiteExtensionPrincipalDivisor K L x v)) ≤
            WithZero.exp (D v) :=
        WithZero.exp_le_exp.mpr hInt
      have hprincipal : finiteExtensionPlaceValuation K L v x =
          WithZero.exp (-(finiteExtensionPrincipalDivisor K L x v)) :=
        finiteExtensionPlaceValuation_eq_exp_neg_principalDivisor
          K L x hx v
      have hplace : finiteExtensionPlaceValuation K L v x =
          FunctionField.Chart.placeValuation K L
            (finiteExtensionPlaceEquivChart K L v) x := by
        exact congrArg (fun u : Valuation L ℤᵐ⁰ => u x)
          (finiteExtensionPlaceValuation_eq_chart K L v)
      have hvw : finiteExtensionPlaceEquivChart K L v = w :=
        (finiteExtensionPlaceEquivChart K L).apply_symm_apply w
      calc
        FunctionField.Chart.placeValuation K L w x =
            FunctionField.Chart.placeValuation K L
              (finiteExtensionPlaceEquivChart K L v) x := by rw [hvw]
        _ = finiteExtensionPlaceValuation K L v x := hplace.symm
        _ = WithZero.exp (-(finiteExtensionPrincipalDivisor K L x v)) :=
            hprincipal
        _ ≤ WithZero.exp (D v) := hExp
        _ = WithZero.exp ((finiteExtensionDivisorEquivChart K L D) w) := by
            simp [finiteExtensionDivisorEquivChart, Finsupp.domCongr_apply, v]
  · intro hxchart
    by_cases hx : x = 0
    · exact Or.inl hx
    · refine Or.inr ⟨hx, ?_⟩
      intro v
      have hchart := hxchart (finiteExtensionPlaceEquivChart K L v)
      have hprincipal : finiteExtensionPlaceValuation K L v x =
          WithZero.exp (-(finiteExtensionPrincipalDivisor K L x v)) :=
        finiteExtensionPlaceValuation_eq_exp_neg_principalDivisor
          K L x hx v
      have hplace : finiteExtensionPlaceValuation K L v x =
          FunctionField.Chart.placeValuation K L
            (finiteExtensionPlaceEquivChart K L v) x := by
        exact congrArg (fun u : Valuation L ℤᵐ⁰ => u x)
          (finiteExtensionPlaceValuation_eq_chart K L v)
      have hExp :
          WithZero.exp (-(finiteExtensionPrincipalDivisor K L x v)) ≤
            WithZero.exp (D v) := by
        calc
          WithZero.exp (-(finiteExtensionPrincipalDivisor K L x v)) =
              finiteExtensionPlaceValuation K L v x :=
              hprincipal.symm
          _ = FunctionField.Chart.placeValuation K L
                (finiteExtensionPlaceEquivChart K L v) x := hplace
          _ ≤ WithZero.exp
                ((finiteExtensionDivisorEquivChart K L D)
                  (finiteExtensionPlaceEquivChart K L v)) := hchart
          _ = WithZero.exp (D v) := by
              simp [finiteExtensionDivisorEquivChart, Finsupp.domCongr_apply]
      have hInt := WithZero.exp_le_exp.mp hExp
      omega

/-- Riemann--Roch supplies the uniform eventual formula with genus `g` and
threshold `2g` once the chosen finite constant field is full in `L`. -/
theorem hasFiniteExtensionUniformEventualRiemannFormula_of_fullConstantField
    [FunctionField.IsFullConstantField K L] :
    HasFiniteExtensionUniformEventualRiemannFormula K L
      (FunctionField.Chart.genus K L)
      (2 * FunctionField.Chart.genus K L) := by
  refine ⟨by omega, ?_⟩
  intro D n hn hdegree
  let Dchart := finiteExtensionDivisorEquivChart K L D
  have hspace : finiteExtensionRiemannSpace K L D =
      FunctionField.Chart.RRspace K L Dchart :=
    finiteExtensionRiemannSpace_eq_chart K L D
  have hdegreeChart : FunctionField.Chart.deg K L Dchart = (n : ℤ) := by
    rw [← finiteExtensionDivisorDegree_eq_chart K L D]
    exact hdegree
  constructor
  · rw [hspace]
    exact FunctionField.Chart.finiteDimensional_RRspace K L Dchart
  · rw [hspace]
    change FunctionField.Chart.ell K L Dchart =
      n + 1 - FunctionField.Chart.genus K L
    obtain ⟨W, hW⟩ := FunctionField.Chart.exists_isCanonical K L
    have hnZ : (2 : ℤ) * (FunctionField.Chart.genus K L : ℤ) ≤
        (n : ℤ) := by
      exact_mod_cast hn
    have hlarge : FunctionField.Chart.deg K L Dchart ≥
        2 * (FunctionField.Chart.genus K L : ℤ) - 1 := by
      rw [hdegreeChart]
      omega
    have hRR := FunctionField.Chart.ell_eq_of_deg_ge
      K L hW Dchart hlarge
    rw [hdegreeChart] at hRR
    have hgn : FunctionField.Chart.genus K L ≤ n := by omega
    omega

/-- If the algebraic closure of the finite constant field inside `L` is
exactly the constants, the uniform eventual Riemann formula holds for a
canonical genus and threshold. -/
theorem exists_hasFiniteExtensionUniformEventualRiemannFormula_of_constants
    (hconstants : algebraicClosure K L = ⊥) :
    ∃ genus threshold,
      HasFiniteExtensionUniformEventualRiemannFormula
        K L genus threshold := by
  let : FunctionField.IsFullConstantField K L :=
    (FunctionField.isFullConstantField_iff_algebraicClosure_eq_bot K L).2
      hconstants
  exact ⟨FunctionField.Chart.genus K L,
    2 * FunctionField.Chart.genus K L,
    hasFiniteExtensionUniformEventualRiemannFormula_of_fullConstantField K L⟩

end

end BGS.HasseWeil
