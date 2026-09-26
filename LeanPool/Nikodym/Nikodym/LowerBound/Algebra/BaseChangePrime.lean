/-
Copyright (c) 2026 Shengtong Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shengtong Zhang
-/
module


public import LeanPool.Nikodym.Nikodym.LowerBound.Algebra.CoefficientProjection
public import LeanPool.Nikodym.Nikodym.LowerBound.Algebra.Dimension

/-!
# Base change of polynomial ideals: quotient dimension and primality

This file implements the base-change items **TR3** and **TR4** of the algebra backend design
(`docs/algebra_backend_design.md`, node TR). Throughout, `K ⊆ K'` is a field extension,
`P := MvPolynomial (Fin d) K`, `P' := MvPolynomial (Fin d) K'` and
`ι := MvPolynomial.map (algebraMap K K') : P →+* P'`.

## Main declarations

* `Nikodym.LowerBound.quotDim_map`: **TR3**, `quotDim (I.map ι) = quotDim I` for every ideal `I`
  and every field extension `K ⊆ K'`. A Noether normalization
  `g : MvPolynomial (Fin s) K →ₐ[K] P ⧸ I` (Mathlib's
  `exists_integral_inj_algHom_of_quotient`, valid for every proper ideal) is base changed to
  `g' : MvPolynomial (Fin s) K' →ₐ[K'] P' ⧸ I.map ι`; `g'` is still integral (the monic
  witnesses are transported along the induced map of quotients) and still injective (via the
  coefficient projections `coeffProj` along `K`-linear functionals `K' → K`), so
  both quotients have Krull dimension `s` by `ringKrullDim_eq_of_isIntegral`.
* `Nikodym.LowerBound.isPrime_map_ratFunc`: **TR4**, for `K' = RatFunc K` the extension of a
  prime ideal is prime. Through `MvPolynomial (Fin d) K[X] ≃ (MvPolynomial (Fin d) K)[X]` the
  extension to `K[X]` is prime (`Ideal.isPrime_map_C_of_isPrime`), and `MvPolynomial (Fin d)
  (RatFunc K)` is the localization of `MvPolynomial (Fin d) K[X]` at the nonzero constants
  (`MvPolynomial.isLocalization`), which avoid the extended ideal, so
  `IsLocalization.isPrime_of_isPrime_disjoint` applies.
* `Nikodym.LowerBound.infinite_ratFunc`: `RatFunc K` is infinite.

The coefficient projections are shared with the Hilbert base-change proofs through
`Algebra/CoefficientProjection.lean` (TR0/TR1).
-/

@[expose] public section

namespace Nikodym.LowerBound

variable {K K' : Type*} [Field K] [Field K'] [Algebra K K'] {d : ℕ}

/-- Use the specified algebra scalar action without searching quotient module structures. -/
noncomputable local instance baseChangePolynomialQuotientSMul {k : ℕ}
    (J : Ideal (MvPolynomial (Fin k) K)) (S : Type*) [CommSemiring S]
    [Algebra S (MvPolynomial (Fin k) K ⧸ J)] :
    SMul S (MvPolynomial (Fin k) K ⧸ J) := Algebra.toSMul

/-- Use the given algebra action directly on a polynomial quotient. -/
noncomputable local instance baseChangePolynomialQuotientModule
    {k : ℕ} (J : Ideal (MvPolynomial (Fin k) K))
    (S : Type*) [CommSemiring S] [Algebra S (MvPolynomial (Fin k) K ⧸ J)] :
    Module S (MvPolynomial (Fin k) K ⧸ J) := Algebra.toModule

namespace BaseChangePrime

variable {σ : Type*}

variable {τ : Type*}

/-- Blueprint TR3, auxiliary: evaluation commutes with base change. -/
private theorem aeval_map_eq_map_aeval (y : τ → MvPolynomial σ K) (r : MvPolynomial τ K) :
    MvPolynomial.aeval (fun i ↦ MvPolynomial.map (algebraMap K K') (y i))
        (MvPolynomial.map (algebraMap K K') r) =
      MvPolynomial.map (algebraMap K K') (MvPolynomial.aeval y r) := by
  induction r using MvPolynomial.induction_on with
  | C c =>
    simp only [MvPolynomial.map_C, MvPolynomial.aeval_C, MvPolynomial.algebraMap_eq]
  | add p q hp hq =>
    simp only [map_add, hp, hq]
  | mul_X p j hp =>
    simp only [map_mul, MvPolynomial.map_X, MvPolynomial.aeval_X, hp]

/-- Blueprint TR3, auxiliary: `coeffProj` commutes with evaluation at base-changed points. -/
private theorem coeffProj_aeval_map (π : K' →ₗ[K] K) (y : τ → MvPolynomial σ K)
    (q : MvPolynomial τ K') :
    coeffProj π (MvPolynomial.aeval (fun i ↦ MvPolynomial.map (algebraMap K K') (y i)) q) =
      MvPolynomial.aeval y (coeffProj π q) := by
  induction q using MvPolynomial.induction_on' with
  | monomial u c =>
    have h : (MvPolynomial.monomial u c : MvPolynomial τ K') =
        MvPolynomial.map (algebraMap K K') (MvPolynomial.monomial u 1) * MvPolynomial.C c := by
      rw [MvPolynomial.map_monomial, map_one, mul_comm, MvPolynomial.C_mul_monomial, mul_one]
    rw [h, coeffProj_map_mul, coeffProj_C, map_mul (MvPolynomial.aeval y),
      map_mul (MvPolynomial.aeval (fun i ↦ MvPolynomial.map (algebraMap K K') (y i))),
      MvPolynomial.aeval_C,
      MvPolynomial.aeval_C, aeval_map_eq_map_aeval, MvPolynomial.algebraMap_eq,
      MvPolynomial.algebraMap_eq, coeffProj_map_mul, coeffProj_C]
  | add p q hp hq =>
    simp only [map_add, hp, hq]

end BaseChangePrime

open BaseChangePrime in
/-- Blueprint TR3: **base change preserves the quotient dimension.** For every ideal `I` of
`P = MvPolynomial (Fin d) K` and every field extension `K ⊆ K'`,
`quotDim (I.map ι) = quotDim I` where `ι = MvPolynomial.map (algebraMap K K')`. -/
theorem quotDim_map (I : Ideal (MvPolynomial (Fin d) K)) :
    quotDim (I.map (MvPolynomial.map (algebraMap K K'))) = quotDim I := by
  by_cases hI : I = ⊤
  · subst hI
    rw [Ideal.map_top, quotDim_top, quotDim_top]
  set ι : MvPolynomial (Fin d) K →+* MvPolynomial (Fin d) K' :=
    MvPolynomial.map (algebraMap K K') with hι
  obtain ⟨s, -, g, hginj, hgint⟩ := exists_integral_inj_algHom_of_quotient I hI
  -- the dimension of `P ⧸ I` is `s`
  have hdimI : ringKrullDim (MvPolynomial (Fin d) K ⧸ I) = s := by
    let : Algebra (MvPolynomial (Fin s) K) (MvPolynomial (Fin d) K ⧸ I) := g.toRingHom.toAlgebra
    have : Algebra.IsIntegral (MvPolynomial (Fin s) K) (MvPolynomial (Fin d) K ⧸ I) :=
      ⟨hgint⟩
    have : FaithfulSMul (MvPolynomial (Fin s) K) (MvPolynomial (Fin d) K ⧸ I) :=
      (faithfulSMul_iff_algebraMap_injective _ _).mpr hginj
    rw [ringKrullDim_eq_of_isIntegral (R := MvPolynomial (Fin s) K),
      ringKrullDim_mvPolynomial_fin_eq]
  -- lift the parameters to `P`
  choose y hy using fun i ↦ Ideal.Quotient.mk_surjective (g (MvPolynomial.X i))
  set G : MvPolynomial (Fin s) K →ₐ[K] MvPolynomial (Fin d) K := MvPolynomial.aeval y with hG
  have hgG : ∀ r, g r = Ideal.Quotient.mk I (G r) := by
    intro r
    have h : g = (Ideal.Quotient.mkₐ K I).comp G :=
      MvPolynomial.algHom_ext fun i ↦ by simp [hG, hy]
    rw [h]
    rfl
  -- the base-changed normalization
  set G' : MvPolynomial (Fin s) K' →ₐ[K'] MvPolynomial (Fin d) K' :=
    MvPolynomial.aeval (fun i ↦ ι (y i)) with hG'
  set g' : MvPolynomial (Fin s) K' →ₐ[K'] MvPolynomial (Fin d) K' ⧸ I.map ι :=
    (Ideal.Quotient.mkₐ K' (I.map ι)).comp G' with hg'
  have hG'G : ∀ r, G' (MvPolynomial.map (algebraMap K K') r) = ι (G r) := fun r ↦
    aeval_map_eq_map_aeval y r
  -- `g'` is injective
  have hg'inj : Function.Injective g' := by
    rw [injective_iff_map_eq_zero]
    intro q hq
    have hq' : G' q ∈ I.map ι := Ideal.Quotient.eq_zero_iff_mem.mp hq
    have key : ∀ π : K' →ₗ[K] K, coeffProj π q = 0 := by
      intro π
      apply hginj
      rw [map_zero, hgG, ← coeffProj_aeval_map, Ideal.Quotient.eq_zero_iff_mem]
      exact coeffProj_mem_of_mem_map π I hq'
    let b := Module.Basis.ofVectorSpace K K'
    ext m
    rw [AddMonoidAlgebra.coeff_zero, Finsupp.zero_apply]
    refine b.ext_elem_iff.mpr fun j ↦ ?_
    rw [map_zero, Finsupp.zero_apply, ← b.coord_apply, ← coeff_coeffProj, key,
      AddMonoidAlgebra.coeff_zero, Finsupp.zero_apply]
  -- `g'` is integral
  have hg'int :
      (g' : MvPolynomial (Fin s) K' →+* MvPolynomial (Fin d) K' ⧸ I.map ι).IsIntegral := by
    let : Algebra (MvPolynomial (Fin s) K') (MvPolynomial (Fin d) K' ⧸ I.map ι) :=
      g'.toRingHom.toAlgebra
    let : Algebra (MvPolynomial (Fin s) K) (MvPolynomial (Fin d) K ⧸ I) := g.toRingHom.toAlgebra
    let ψ : MvPolynomial (Fin d) K ⧸ I →+* MvPolynomial (Fin d) K' ⧸ I.map ι :=
      Ideal.quotientMap (I.map ι) ι Ideal.le_comap_map
    have hcomp : (algebraMap (MvPolynomial (Fin s) K') (MvPolynomial (Fin d) K' ⧸ I.map ι)).comp
        (MvPolynomial.map (algebraMap K K')) =
          ψ.comp (algebraMap (MvPolynomial (Fin s) K) (MvPolynomial (Fin d) K ⧸ I)) := by
      refine RingHom.ext fun r ↦ ?_
      change g' (MvPolynomial.map (algebraMap K K') r) = ψ (g r)
      rw [hgG, Ideal.quotientMap_mk, hg', AlgHom.comp_apply, hG'G]
      rfl
    have hX : ∀ j, IsIntegral (MvPolynomial (Fin s) K')
        (Ideal.Quotient.mk (I.map ι) (MvPolynomial.X j)) := fun j ↦ by
      have h := IsIntegral.map_of_comp_eq _ ψ hcomp
        (hgint (Ideal.Quotient.mk I (MvPolynomial.X j)))
      have hXj : ι (MvPolynomial.X j) = MvPolynomial.X j := MvPolynomial.map_X _ _
      rwa [Ideal.quotientMap_mk, hXj] at h
    intro x
    obtain ⟨f, rfl⟩ := Ideal.Quotient.mk_surjective x
    change IsIntegral (MvPolynomial (Fin s) K') _
    induction f using MvPolynomial.induction_on with
    | C c =>
      have h : Ideal.Quotient.mk (I.map ι) (MvPolynomial.C c) =
          algebraMap (MvPolynomial (Fin s) K') (MvPolynomial (Fin d) K' ⧸ I.map ι)
            (MvPolynomial.C c) := by
        change _ = g' (MvPolynomial.C c)
        rw [hg', AlgHom.comp_apply, hG', MvPolynomial.aeval_C, MvPolynomial.algebraMap_eq]
        rfl
      rw [h]
      exact isIntegral_algebraMap
    | add p q hp hq =>
      rw [map_add]
      exact hp.add hq
    | mul_X p j hp =>
      rw [map_mul]
      exact hp.mul (hX j)
  -- the dimension of `P' ⧸ I.map ι` is `s`
  have hdim' : ringKrullDim (MvPolynomial (Fin d) K' ⧸ I.map ι) = s := by
    let : Algebra (MvPolynomial (Fin s) K') (MvPolynomial (Fin d) K' ⧸ I.map ι) :=
      g'.toRingHom.toAlgebra
    have : Algebra.IsIntegral (MvPolynomial (Fin s) K') (MvPolynomial (Fin d) K' ⧸ I.map ι) :=
      ⟨hg'int⟩
    have : FaithfulSMul (MvPolynomial (Fin s) K') (MvPolynomial (Fin d) K' ⧸ I.map ι) :=
      (faithfulSMul_iff_algebraMap_injective _ _).mpr hg'inj
    rw [ringKrullDim_eq_of_isIntegral (R := MvPolynomial (Fin s) K'),
      ringKrullDim_mvPolynomial_fin_eq]
  rw [quotDim_of_ringKrullDim_eq hdim', quotDim_of_ringKrullDim_eq hdimI]

/-! ### Primality under `K → RatFunc K` -/

section RatFunc

open Polynomial

/-- Blueprint TR7: `RatFunc K` is infinite (it contains `K[X]`). -/
instance infinite_ratFunc : Infinite (RatFunc K) :=
  Infinite.of_injective (algebraMap K[X] (RatFunc K)) (IsFractionRing.injective _ _)

attribute [local instance] MvPolynomial.algebraMvPolynomial

/-- Blueprint TR4: **primes stay prime under the purely transcendental extension
`K ⊆ RatFunc K`.** -/
theorem isPrime_map_ratFunc (I : Ideal (MvPolynomial (Fin d) K)) [hI : I.IsPrime] :
    (I.map (MvPolynomial.map (algebraMap K (RatFunc K)))).IsPrime := by
  -- the identification `MvPolynomial (Fin d) K[X] ≃ (MvPolynomial (Fin d) K)[X]`
  let e : MvPolynomial (Fin d) K[X] ≃+* Polynomial (MvPolynomial (Fin d) K) :=
    ((MvPolynomial.optionEquivRight K (Fin d)).symm.trans
      (MvPolynomial.optionEquivLeft K (Fin d))).toRingEquiv
  have he : ∀ f : MvPolynomial (Fin d) K,
      e (MvPolynomial.map (Polynomial.C : K →+* K[X]) f) = Polynomial.C f := by
    intro f
    have h : (e : MvPolynomial (Fin d) K[X] →+* Polynomial (MvPolynomial (Fin d) K)).comp
        (MvPolynomial.map (Polynomial.C : K →+* K[X])) =
          (Polynomial.C : MvPolynomial (Fin d) K →+* Polynomial (MvPolynomial (Fin d) K)) := by
      refine MvPolynomial.ringHom_ext (fun c ↦ ?_) (fun i ↦ ?_)
      · simp only [RingHom.comp_apply, MvPolynomial.map_C, RingEquiv.coe_toRingHom, e,
          AlgEquiv.coe_ringEquiv, AlgEquiv.trans_apply,
          ← MvPolynomial.optionEquivRight_C, AlgEquiv.symm_apply_apply,
          MvPolynomial.optionEquivLeft_C]
      · simp only [RingHom.comp_apply, MvPolynomial.map_X, RingEquiv.coe_toRingHom, e,
          AlgEquiv.coe_ringEquiv, AlgEquiv.trans_apply,
          ← MvPolynomial.optionEquivRight_X_some, AlgEquiv.symm_apply_apply,
          MvPolynomial.optionEquivLeft_X_some]
    exact congrArg (fun φ ↦ φ f) h
  have heC : ∀ c : K[X], e (MvPolynomial.C c) = c.map MvPolynomial.C := by
    intro c
    have h : (e : MvPolynomial (Fin d) K[X] →+* Polynomial (MvPolynomial (Fin d) K)).comp
        (MvPolynomial.C : K[X] →+* MvPolynomial (Fin d) K[X]) =
          Polynomial.mapRingHom (MvPolynomial.C : K →+* MvPolynomial (Fin d) K) := by
      refine Polynomial.ringHom_ext (fun a ↦ ?_) ?_
      · simp only [RingHom.comp_apply, Polynomial.coe_mapRingHom, Polynomial.map_C,
          RingEquiv.coe_toRingHom, e, AlgEquiv.coe_ringEquiv,
          AlgEquiv.trans_apply, ← MvPolynomial.optionEquivRight_C, AlgEquiv.symm_apply_apply,
          MvPolynomial.optionEquivLeft_C]
      · simp only [RingHom.comp_apply, Polynomial.coe_mapRingHom, Polynomial.map_X,
          RingEquiv.coe_toRingHom, e, AlgEquiv.coe_ringEquiv,
          AlgEquiv.trans_apply, ← MvPolynomial.optionEquivRight_X_none, AlgEquiv.symm_apply_apply,
          MvPolynomial.optionEquivLeft_X_none]
    exact congrArg (fun φ ↦ φ c) h
  -- the extension of `I` to `K[X]` is prime
  set J : Ideal (MvPolynomial (Fin d) K[X]) :=
    I.map (MvPolynomial.map (Polynomial.C : K →+* K[X])) with hJdef
  have hJ : J = (I.map (Polynomial.C : MvPolynomial (Fin d) K →+* _)).comap e := by
    rw [← Ideal.map_symm, ← Ideal.map_coe e.symm, Ideal.map_map, hJdef]
    congr 1
    refine RingHom.ext fun f ↦ ?_
    rw [RingHom.comp_apply, RingEquiv.coe_toRingHom, eq_comm, RingEquiv.symm_apply_eq, he]
  have : (I.map (Polynomial.C : MvPolynomial (Fin d) K →+* _)).IsPrime :=
    Ideal.isPrime_map_C_of_isPrime
  have hJprime : J.IsPrime := hJ ▸ Ideal.comap_isPrime e _
  -- nonzero constants of `K[X]` avoid `J`
  have hdisj : Disjoint ((((nonZeroDivisors K[X]).map
      (MvPolynomial.C : K[X] →+* MvPolynomial (Fin d) K[X])) : Submonoid _) : Set _)
      (J : Set (MvPolynomial (Fin d) K[X])) := by
    rw [Set.disjoint_left]
    rintro x ⟨c, hc, rfl⟩ hx
    have hc0 : c ≠ 0 := nonZeroDivisors.ne_zero hc
    rw [SetLike.mem_coe, hJ, Ideal.mem_comap, heC, Ideal.mem_map_C_iff] at hx
    have hlc := hx c.natDegree
    rw [Polynomial.coeff_map, ← Polynomial.leadingCoeff] at hlc
    apply hI.ne_top
    rw [Ideal.eq_top_iff_one]
    have h1 : (1 : MvPolynomial (Fin d) K) =
        MvPolynomial.C (c.leadingCoeff⁻¹) * MvPolynomial.C c.leadingCoeff := by
      rw [← MvPolynomial.C_mul, inv_mul_cancel₀ (Polynomial.leadingCoeff_ne_zero.mpr hc0),
        MvPolynomial.C_1]
    rw [h1]
    exact I.mul_mem_left _ hlc
  -- localize
  have h := IsLocalization.isPrime_of_isPrime_disjoint
    ((nonZeroDivisors K[X]).map (MvPolynomial.C : K[X] →+* MvPolynomial (Fin d) K[X]))
    (MvPolynomial (Fin d) (RatFunc K)) J hJprime hdisj
  have hcomp : (MvPolynomial.map (algebraMap K[X] (RatFunc K))).comp
      (MvPolynomial.map (Polynomial.C : K →+* K[X])) =
        (MvPolynomial.map (algebraMap K (RatFunc K)) :
          MvPolynomial (Fin d) K →+* MvPolynomial (Fin d) (RatFunc K)) := by
    refine RingHom.ext fun f ↦ ?_
    rw [RingHom.comp_apply, MvPolynomial.map_map, IsScalarTower.algebraMap_eq K K[X] (RatFunc K),
      Polynomial.algebraMap_eq]
  rwa [MvPolynomial.algebraMap_def, hJdef, Ideal.map_map, hcomp] at h

end RatFunc

end Nikodym.LowerBound

/- Adapted for Lean Pool: module imports and compatibility with its pinned toolchain. -/
