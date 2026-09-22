/-
Copyright (c) 2026 Yuma Mizuno. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuma Mizuno
-/

import LeanPool.MarkoffModP.BGS.CorvajaZannier.PlaneCurveInfinityDifferentBound

/-!
# The degree of the different at infinity

Bound the different at infinity using a primitive element, its discriminant, and the normalized
reciprocal polynomial.
-/

open Polynomial

namespace BGS.CorvajaZannier

noncomputable section

theorem discr_powerBasis_eq_minpoly_discr
    {K L : Type*} [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [Algebra.IsSeparable K L]
    (pb : PowerBasis K L) :
    Algebra.discr K pb.basis = (minpoly K pb.gen).discr := by
  let E := AlgebraicClosure L
  let := fun a b : E => Classical.propDecidable (Eq a b)
  let f := minpoly K pb.gen
  have hfmonic : f.Monic := minpoly.monic pb.isIntegral_gen
  have hfne : f ≠ 0 := hfmonic.ne_zero
  have hfpos : 0 < f.degree := by
    rw [← natDegree_pos_iff_degree_pos]
    change 0 < (minpoly K pb.gen).natDegree
    rw [pb.natDegree_minpoly]
    rw [← pb.finrank]
    exact Module.finrank_pos_iff.mpr inferInstance
  have hsep : f.Separable := Algebra.IsSeparable.isSeparable K pb.gen
  have hsplit : (f.map (algebraMap K E)).Splits := IsAlgClosed.splits _
  have hrootsNodup : (f.aroots E).Nodup :=
    nodup_roots (show (f.map (algebraMap K E)).Separable from hsep.map)
  apply (algebraMap K E).injective
  rw [Algebra.discr_powerBasis_eq_norm]
  rw [map_mul, map_pow, map_neg, map_one,
    Algebra.norm_eq_prod_embeddings K E]
  have hprod :
      (∏ σ : L →ₐ[K] E, σ (aeval pb.gen f.derivative)) =
        ((f.aroots E).map
          ((f.derivative.map (algebraMap K E)).eval)).prod := by
    let e : (L →ₐ[K] E) ≃ {x : E // x ∈ f.aroots E} := by
      simpa [f] using
        (pb.liftEquiv' : (L →ₐ[K] E) ≃
          {x : E // x ∈ (minpoly K pb.gen).aroots E})
    calc
      _ = ∏ x : {x : E // x ∈ f.aroots E},
          (f.derivative.map (algebraMap K E)).eval x.1 := by
        apply Fintype.prod_equiv e
        intro σ
        have he : (e σ).1 = σ pb.gen := by
          simp [e, f]
        rw [he, ← aeval_algHom_apply, ← eval_map_algebraMap]
      _ = _ := by
        rw [Finset.prod_mem_multiset, Finset.prod_eq_multiset_prod,
          Multiset.toFinset_val, Multiset.dedup_eq_self.mpr hrootsNodup]
        intro x
        rfl
  rw [hprod]
  have hres := resultant_deriv (f := f) hfpos
  have hresMap :
      (f.map (algebraMap K E)).resultant
          (f.derivative.map (algebraMap K E)) f.natDegree
            (f.natDegree - 1) =
        (algebraMap K E)
          ((-1) ^ (f.natDegree * (f.natDegree - 1) / 2) *
            f.leadingCoeff * f.discr) := by
    rw [resultant_map_map]
    exact congrArg (algebraMap K E) hres
  have hfmapDegree : (f.map (algebraMap K E)).natDegree = f.natDegree :=
    natDegree_map_eq_of_injective (algebraMap K E).injective f
  have hresEval :
      (f.map (algebraMap K E)).resultant
          (f.derivative.map (algebraMap K E)) f.natDegree
            (f.natDegree - 1) =
        (f.map (algebraMap K E)).leadingCoeff ^ (f.natDegree - 1) *
          (((f.map (algebraMap K E)).roots).map
            ((f.derivative.map (algebraMap K E)).eval)).prod := by
    convert resultant_eq_prod_eval
      (f.map (algebraMap K E))
      (f.derivative.map (algebraMap K E))
      (f.natDegree - 1)
      (natDegree_map_le.trans (natDegree_derivative_le f)) hsplit using 1
    rw [hfmapDegree]
  rw [hresEval,
    leadingCoeff_map_of_injective (algebraMap K E).injective,
    hfmonic.leadingCoeff, map_one, one_pow, one_mul] at hresMap
  simp only [map_mul, map_pow, map_neg, map_one] at hresMap
  have hdegree : f.natDegree = Module.finrank K L := by
    calc
      f.natDegree = pb.dim := by simp [f, pb.natDegree_minpoly]
      _ = Module.finrank K L := pb.finrank.symm
  rw [hdegree] at hresMap
  change ((f.aroots E).map
      ((f.derivative.map (algebraMap K E)).eval)).prod = _ at hresMap
  rw [hresMap]
  let N := Module.finrank K L * (Module.finrank K L - 1) / 2
  have hsign : ((-1 : E) ^ N) * ((-1 : E) ^ N) = 1 := by
    rw [← pow_add, show N + N = 2 * N by omega, pow_mul]
    norm_num
  dsimp only [N, f] at hsign ⊢
  rw [mul_one, ← mul_assoc, hsign, one_mul]

open scoped nonZeroDivisors
open IsDedekindDomain Multiplicative WithZero

section

variable (K : Type*) [Field K] [DecidableEq K] [DecidableEq (RatFunc K)]
variable (L : Type*) [Field L] [Algebra (RatFunc K) L]
  [FiniteDimensional (RatFunc K) L]
  [Algebra.IsSeparable (RatFunc K) L]

local instance infinityDifferentIntegralClosureModuleFinite :
    Module.Finite (RatFuncInfinityIntegers K)
      (RatFuncInfinityIntegralClosure K L) :=
  IsIntegralClosure.finite (RatFuncInfinityIntegers K) (RatFunc K) L
    (RatFuncInfinityIntegralClosure K L)

local instance infinityDifferentIntegralClosureIsIntegral :
    Algebra.IsIntegral (RatFuncInfinityIntegers K)
      (RatFuncInfinityIntegralClosure K L) :=
  IsIntegralClosure.isIntegral_algebra (RatFuncInfinityIntegers K) L

local instance infinityDifferentTopIsTorsionFree :
    Module.IsTorsionFree (RatFuncInfinityIntegers K) L :=
  Module.IsTorsionFree.trans_faithfulSMul
    (RatFuncInfinityIntegers K) (RatFunc K) L

local instance infinityDifferentIntegralClosureIsTorsionFree :
    Module.IsTorsionFree (RatFuncInfinityIntegers K)
      (RatFuncInfinityIntegralClosure K L) :=
  IsIntegralClosure.isTorsionFree (RatFuncInfinityIntegers K) L

local instance infinityDifferentIntegralClosureIsDedekindDomain :
    IsDedekindDomain (RatFuncInfinityIntegralClosure K L) :=
  IsIntegralClosure.isDedekindDomain
    (RatFuncInfinityIntegers K) (RatFunc K) L
      (RatFuncInfinityIntegralClosure K L)

local instance infinityDifferentIntegralClosureIsFractionRing :
    IsFractionRing (RatFuncInfinityIntegralClosure K L) L :=
  IsIntegralClosure.isFractionRing_of_finite_extension
    (RatFuncInfinityIntegers K) (RatFunc K) L
      (RatFuncInfinityIntegralClosure K L)

local instance infinityDifferentPlaceFintype :
    Fintype ((ratFuncInfinityPlace K).asIdeal.primesOver
      (RatFuncInfinityIntegralClosure K L)) :=
  Set.Finite.fintype
    (IsDedekindDomain.primesOver_finite
      (ratFuncInfinityPlace K).asIdeal
      (RatFuncInfinityIntegralClosure K L))

/-- The residue-degree-weighted multiplicity of the different above the
infinity place of `K(X)`. -/
def infinityDifferentDegree : ℕ :=
  ∑ P : (ratFuncInfinityPlace K).asIdeal.primesOver
      (RatFuncInfinityIntegralClosure K L),
    P.1.inertiaDeg (RatFuncInfinityIntegers K) *
      multiplicity P.1
        (differentIdeal (RatFuncInfinityIntegers K)
          (RatFuncInfinityIntegralClosure K L))

omit [DecidableEq K] in
theorem ratFuncInfinityIntegralClosureFractionRingEquiv_valuation
    (q : HeightOneSpectrum (RatFuncInfinityIntegralClosure K L))
    (x : FractionRing (RatFuncInfinityIntegralClosure K L)) :
    q.valuation L
        (ratFuncInfinityIntegralClosureFractionRingEquiv K L x) =
      q.valuation (FractionRing (RatFuncInfinityIntegralClosure K L)) x := by
  obtain ⟨a, b, hb, rfl⟩ :=
    IsFractionRing.div_surjective
      (RatFuncInfinityIntegralClosure K L) x
  rw [map_div₀,
    (ratFuncInfinityIntegralClosureFractionRingEquiv K L).commutes a,
    (ratFuncInfinityIntegralClosureFractionRingEquiv K L).commutes b,
    Valuation.map_div, Valuation.map_div,
    q.valuation_of_algebraMap, q.valuation_of_algebraMap,
    q.valuation_of_algebraMap, q.valuation_of_algebraMap]

omit [DecidableEq K] in
theorem ratFuncInfinityIntegralClosureFractionRingEquiv_order_eq
    (q : HeightOneSpectrum (RatFuncInfinityIntegralClosure K L))
    (x : FractionRing (RatFuncInfinityIntegralClosure K L)) (hx : x ≠ 0) :
    finitePlaceOrder q x =
      finitePlaceOrder q
        (ratFuncInfinityIntegralClosureFractionRingEquiv K L x) := by
  let e := ratFuncInfinityIntegralClosureFractionRingEquiv K L
  have hcanon := valuation_eq_exp_neg_finitePlaceOrder q x hx
  have he_ne : e x ≠ 0 := by simpa using e.injective.ne hx
  have hactual := valuation_eq_exp_neg_finitePlaceOrder q (e x) he_ne
  have hval :=
    ratFuncInfinityIntegralClosureFractionRingEquiv_valuation K L q x
  have hexp : exp (-finitePlaceOrder q x) =
      exp (-finitePlaceOrder q (e x)) := by
    rw [← hcanon, ← hactual]
    exact hval.symm
  rw [exp_inj] at hexp
  change finitePlaceOrder q x = finitePlaceOrder q (e x)
  omega

omit [DecidableEq K] in
/-- The different contribution above infinity is bounded by the infinity
order of the discriminant of any integral primitive-element equation having
a unit value at a center.  The inverse translate of the primitive element is
integral and realizes the complementary reciprocal-discriminant estimate. -/
theorem infinityDifferentDegree_le_discriminantOrder_of_primitiveElement
    (G : (RatFuncInfinityIntegers K)[X])
    (c : RatFuncInfinityIntegers K) (u : (RatFuncInfinityIntegers K)ˣ)
    (v : L)
    (hu : G.eval c = u)
    (hvc : v ≠ algebraMap (RatFuncInfinityIntegers K) L c)
    (hv : aeval v G = 0)
    (hprimitive : Algebra.adjoin (RatFunc K) {v} = ⊤)
    (hdegree : G.natDegree = Module.finrank (RatFunc K) L)
    (hGdiscr : G.discr ≠ 0) :
    (infinityDifferentDegree K L : ℤ) ≤
      ratFuncInfinityOrder
        (algebraMap (RatFuncInfinityIntegers K) (RatFunc K) G.discr) := by
  let A := RatFuncInfinityIntegers K
  let B := RatFuncInfinityIntegralClosure K L
  have hzIntegral : IsIntegral A
      ((v - algebraMap A L c)⁻¹) :=
    isIntegral_inv_sub_of_eval_eq_unit G c u v hu hvc hv
  let z : B := IsIntegralClosure.mk' B
    ((v - algebraMap A L c)⁻¹) hzIntegral
  have hzMap : algebraMap B L z =
      (v - algebraMap A L c)⁻¹ := by
    simp [z]
  have hzPrimitive : Algebra.adjoin (RatFunc K)
      {algebraMap B L z} = ⊤ := by
    rw [hzMap]
    simpa only [IsScalarTower.algebraMap_apply A (RatFunc K) L] using
      (adjoin_inv_sub_eq_top_of_adjoin_eq_top
        (algebraMap A (RatFunc K) c) v hprimitive)
  let d : B := aeval z (derivative (minpoly A z))
  have hd : d ≠ 0 := by
    simpa [d] using minpolyDerivative_ne_zero
      (A := A) (K := RatFunc K) (L := L) z
  let dL : L := algebraMap B L d
  have hdL : dL ≠ 0 := by
    exact (IsFractionRing.injective B L).ne hd
  have hrepr :
      (ratFuncInfinityIntegralClosureFractionRingEquiv K L).symm dL =
        algebraMap B (FractionRing B) d := by
    apply (ratFuncInfinityIntegralClosureFractionRingEquiv K L).injective
    rw [(ratFuncInfinityIntegralClosureFractionRingEquiv K L).apply_symm_apply]
    exact (ratFuncInfinityIntegralClosureFractionRingEquiv K L).commutes d |>.symm
  have hpoint : ∀ P : (ratFuncInfinityPlace K).asIdeal.primesOver B,
      ((P.1.inertiaDeg A *
        multiplicity P.1 (differentIdeal A B) : ℕ) : ℤ) ≤
        (P.1.inertiaDeg A : ℤ) *
          finitePlaceOrder
            (primeOverHeightOne (ratFuncInfinityPlace K) P)
            ((ratFuncInfinityIntegralClosureFractionRingEquiv K L).symm dL) := by
    intro P
    have hmul := differentIdeal_multiplicity_le_finitePlaceOrder_minpolyDerivative
      (A := A) (K := RatFunc K) (L := L) (B := B)
      z hzPrimitive (primeOverHeightOne (ratFuncInfinityPlace K) P)
    change (multiplicity P.1 (differentIdeal A B) : ℤ) ≤
      finitePlaceOrder (primeOverHeightOne (ratFuncInfinityPlace K) P)
        (algebraMap B L d) at hmul
    have horder :
        finitePlaceOrder (primeOverHeightOne (ratFuncInfinityPlace K) P)
            (algebraMap B L d) =
          finitePlaceOrder (primeOverHeightOne (ratFuncInfinityPlace K) P)
            ((ratFuncInfinityIntegralClosureFractionRingEquiv K L).symm dL) := by
      rw [hrepr]
      have hne : algebraMap B (FractionRing B) d ≠ 0 :=
        by
          have hinj : Function.Injective
              (algebraMap B (FractionRing B)) :=
            IsFractionRing.injective B (FractionRing B)
          intro hzero
          apply hd
          apply hinj
          rw [hzero, map_zero]
      have heq := ratFuncInfinityIntegralClosureFractionRingEquiv_order_eq
        K L (primeOverHeightOne (ratFuncInfinityPlace K) P)
          (algebraMap B (FractionRing B) d) hne
      calc
        finitePlaceOrder (primeOverHeightOne (ratFuncInfinityPlace K) P)
            (algebraMap B L d) =
          finitePlaceOrder (primeOverHeightOne (ratFuncInfinityPlace K) P)
            (ratFuncInfinityIntegralClosureFractionRingEquiv K L
              (algebraMap B (FractionRing B) d)) := by
                rw [(ratFuncInfinityIntegralClosureFractionRingEquiv K L).commutes d]
        _ = finitePlaceOrder
            (primeOverHeightOne (ratFuncInfinityPlace K) P)
            (algebraMap B (FractionRing B) d) := heq.symm
    rw [horder] at hmul
    simpa only [Nat.cast_mul] using
      mul_le_mul_of_nonneg_left hmul (Int.natCast_nonneg _)
  have hsum : (infinityDifferentDegree K L : ℤ) ≤
      ∑ P : (ratFuncInfinityPlace K).asIdeal.primesOver B,
        (P.1.inertiaDeg A : ℤ) *
          finitePlaceOrder
            (primeOverHeightOne (ratFuncInfinityPlace K) P)
            ((ratFuncInfinityIntegralClosureFractionRingEquiv K L).symm dL) := by
    rw [infinityDifferentDegree, Nat.cast_sum]
    exact Finset.sum_le_sum fun P _ => hpoint P
  rw [primesAboveInfinity_weightedOrder_eq_normInfinityOrder K L dL hdL] at hsum
  let pb : PowerBasis (RatFunc K) L :=
    PowerBasis.ofAdjoinEqTop'
      (Algebra.IsIntegral.isIntegral (algebraMap B L z)) hzPrimitive
  have hdiscNorm := discr_powerBasisOfPrimitiveElement_eq_norm_minpolyDerivative
    (A := A) (K := RatFunc K) (L := L) (B := B) z hzPrimitive
  have hpb : Algebra.discr (RatFunc K) pb.basis =
      (minpoly (RatFunc K) (algebraMap B L z)).discr :=
    by
      have hpbg : pb.gen = algebraMap B L z := by simp [pb]
      simpa only [hpbg] using discr_powerBasis_eq_minpoly_discr pb
  change Algebra.discr (RatFunc K) pb.basis =
      (-1) ^ (Module.finrank (RatFunc K) L *
        (Module.finrank (RatFunc K) L - 1) / 2) *
          Algebra.norm (RatFunc K) dL at hdiscNorm
  rw [hpb] at hdiscNorm
  have hnormOrder :
      ratFuncInfinityOrder (Algebra.norm (RatFunc K) dL) =
        ratFuncInfinityOrder
          (minpoly (RatFunc K) (algebraMap B L z)).discr := by
    have hsign :
        (-1 : RatFunc K) ^ (Module.finrank (RatFunc K) L *
          (Module.finrank (RatFunc K) L - 1) / 2) ≠ 0 := by simp
    have hnorm : Algebra.norm (RatFunc K) dL ≠ 0 :=
      Algebra.norm_ne_zero_iff.mpr hdL
    have hdegreeEq := congrArg RatFunc.intDegree hdiscNorm
    rw [RatFunc.intDegree_mul hsign hnorm] at hdegreeEq
    have hsignDegree : RatFunc.intDegree
        ((-1 : RatFunc K) ^ (Module.finrank (RatFunc K) L *
          (Module.finrank (RatFunc K) L - 1) / 2)) = 0 := by
      induction (Module.finrank (RatFunc K) L *
          (Module.finrank (RatFunc K) L - 1) / 2) with
      | zero => simp
      | succ n ih =>
          rw [pow_succ, RatFunc.intDegree_mul (pow_ne_zero n (by simp)) (by simp), ih]
          simp
    rw [hsignDegree, zero_add] at hdegreeEq
    exact congrArg Neg.neg hdegreeEq |>.symm
  rw [hnormOrder] at hsum
  have htop := finitePlaceOrderTop_minpoly_inv_sub_discr
    (A := A) (K := RatFunc K) (L := L)
    (ratFuncInfinityPlace K) G c u v hu hvc hv hprimitive hdegree
  rw [← hzMap] at htop
  have hminNe : (minpoly (RatFunc K) (algebraMap B L z)).discr ≠ 0 := by
    intro hzero
    rw [hzero] at hdiscNorm
    exact (mul_ne_zero (by simp) (Algebra.norm_ne_zero_iff.mpr hdL)) hdiscNorm.symm
  have hmapNe : algebraMap A (RatFunc K) G.discr ≠ 0 :=
    (IsFractionRing.injective A (RatFunc K)).ne hGdiscr
  rw [finitePlaceOrderTop_eq_coe _ _ hminNe,
    finitePlaceOrderTop_eq_coe _ _ hmapNe] at htop
  have horderEq : ratFuncInfinityOrder
      (minpoly (RatFunc K) (algebraMap B L z)).discr =
        ratFuncInfinityOrder (algebraMap A (RatFunc K) G.discr) := by
    have hfinite : finitePlaceOrder (ratFuncInfinityPlace K)
        (minpoly (RatFunc K) (algebraMap B L z)).discr =
          finitePlaceOrder (ratFuncInfinityPlace K)
            (algebraMap A (RatFunc K) G.discr) := by
      exact_mod_cast htop
    simpa only [ratFuncInfinityPlace_order_eq K _ hminNe,
      ratFuncInfinityPlace_order_eq K _ hmapNe] using hfinite
  exact hsum.trans_eq horderEq

end

end

end BGS.CorvajaZannier

namespace BGS.CorvajaZannier

open scoped Polynomial
open Multiplicative WithZero Polynomial

variable (K : Type*) [Field K] [DecidableEq K] [DecidableEq (RatFunc K)]

theorem infinityNormalizedCoefficient_isUnit_of_natDegree_eq
    (a : ℕ) (P : K[X]) (hP : P ≠ 0) (hdegree : P.natDegree = a) :
    IsUnit (infinityNormalizedCoefficient K a P hdegree.le) := by
  rw [Valuation.Integers.isUnit_iff_valuation_eq_one
    (Valuation.integer.integers (RatFunc.inftyValuation K))]
  change RatFunc.inftyValuation K
      ((RatFunc.X⁻¹) ^ a * algebraMap K[X] (RatFunc K) P) = 1
  have hXinv : RatFunc.X⁻¹ ≠ (0 : RatFunc K) :=
    inv_ne_zero RatFunc.X_ne_zero
  have hleft : (RatFunc.X⁻¹) ^ a ≠ (0 : RatFunc K) :=
    pow_ne_zero _ hXinv
  have hright : algebraMap K[X] (RatFunc K) P ≠ 0 :=
    RatFunc.algebraMap_ne_zero hP
  have hpow : ((((RatFunc.X : RatFunc K)⁻¹) ^ a) : RatFunc K).intDegree =
      (a : ℤ) * ((RatFunc.X : RatFunc K)⁻¹).intDegree := by
    clear hdegree hleft
    induction a with
    | zero => simp
    | succ n ih =>
        rw [pow_succ, RatFunc.intDegree_mul
          (pow_ne_zero n hXinv) hXinv, ih]
        push_cast
        ring
  rw [RatFunc.inftyValuation_apply,
    RatFunc.inftyValuation_of_nonzero (F := K) (mul_ne_zero hleft hright),
    RatFunc.intDegree_mul hleft hright,
    hpow,
    RatFunc.intDegree_inv, RatFunc.intDegree_X,
    RatFunc.intDegree_polynomial, hdegree]
  simp

theorem infinityNormalizedIntegralPolynomial_isPrimitive
    (a : ℕ) (F : K[X][X])
    (hcoeff : ∀ i, (F.coeff i).natDegree ≤ a)
    (i : ℕ) (hFi : F.coeff i ≠ 0)
    (hi : (F.coeff i).natDegree = a) :
    (infinityNormalizedIntegralPolynomial K a F hcoeff).IsPrimitive := by
  rw [Polynomial.isPrimitive_iff_contentIdeal_eq_top]
  let G := infinityNormalizedIntegralPolynomial K a F hcoeff
  have hcoeffG : G.coeff i =
      infinityNormalizedCoefficient K a (F.coeff i) (hcoeff i) := by
    simp only [G, infinityNormalizedIntegralPolynomial, coeff_sum,
      coeff_monomial]
    simp [Polynomial.sum, hFi]
  apply G.contentIdeal.eq_top_of_isUnit_mem (G.coeff_mem_contentIdeal i)
  rw [hcoeffG]
  exact infinityNormalizedCoefficient_isUnit_of_natDegree_eq
    K a (F.coeff i) hFi hi

end BGS.CorvajaZannier
