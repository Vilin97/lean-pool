/-
Copyright (c) 2026 Shengtong Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shengtong Zhang
-/

import LeanPool.Nikodym.Nikodym.LowerBound.Algebra.NormalizationSetting

/-!
# Homogeneity of the norm (node A07′)

This file implements node **A07′** of the algebra backend (`docs/algebra_backend_design.md`).

## Part 1: the scaling automorphisms

For a unit `u` of the coefficient ring, `scaleEquiv u : MvPolynomial σ K ≃ₐ[K] MvPolynomial σ K`
is the substitution `X i ↦ C u * X i`. It multiplies a form of degree `t` by `u ^ t`
(`scaleEquiv_apply_isHomogeneous`), and over an infinite field this characterizes forms
(`isHomogeneous_of_forall_scaleEquiv_eq`). It preserves homogeneous ideals
(`scaleEquiv_map_eq_of_isHomogeneous`).

## Part 2: the norm in the shared setting of `NormalizationSetting.lean`

With `Q := MvPolynomial (Fin n) K`, `J` a homogeneous prime, `R := Q ⧸ J`, linear forms
`y : Fin s → Q`, `S := MvPolynomial (Fin s) K` acting on `R` through `[Algebra S R]` and
`halg : algebraMap S R = (aeval (mk J ∘ y)).toRingHom`, and the fraction fields related by
instance arguments `[Algebra (FractionRing S) (FractionRing R)]` and
`[IsScalarTower S (FractionRing S) (FractionRing R)]` (e.g. from `FractionRing.liftAlgebra`):

* `finite_fractionRing_of_pow_idealOfVars_le`: `FractionRing R` is finite-dimensional over
  `FractionRing S` when `𝔪ₙ ^ N ≤ J ⊔ span (range y)`;
* `norm_mem_range_algebraMap`: the norm of (the image of) an element of `R` lies in `S`;
* `norm_isHomogeneous`: the norm of a homogeneous element of degree `t` is a form of degree
  `t * Module.finrank (FractionRing S) (FractionRing R)`; the proof uses the induced scaling
  automorphisms `scaleQuotEquiv` of `R` and `scaleEquiv` of `S`, extended to the fraction fields
  by `IsFractionRing.ringEquivOfRingEquiv`, and `Algebra.norm_eq_of_equiv_equiv`.
-/

namespace Nikodym.LowerBound

open MvPolynomial

attribute [local instance] MvPolynomial.gradedAlgebra
attribute [local instance] normalizationPolynomialQuotientSMul normalizationPolynomialQuotientModule

/-! ### Part 1: the scaling automorphism `X i ↦ u * X i` -/

/-- The quotient action is the multiplicative action supplied by its algebra structure. -/
noncomputable local instance gradedNormQuotientMulAction {K : Type*} [Field K] {k : ℕ}
    (J : Ideal (MvPolynomial (Fin k) K)) (S : Type*) [CommSemiring S]
    [Algebra S (MvPolynomial (Fin k) K ⧸ J)] :
    MulAction S (MvPolynomial (Fin k) K ⧸ J) :=
  (Algebra.toModule : Module S (MvPolynomial (Fin k) K ⧸ J)).toMulAction

/-- Use the algebra's scalar action directly in the normalization construction. -/
noncomputable local instance gradedNormAlgebraSMul {K : Type*} [Field K] {k : ℕ}
    (J : Ideal (MvPolynomial (Fin k) K)) (S : Type*) [CommSemiring S]
    [Algebra S (FractionRing (MvPolynomial (Fin k) K ⧸ J))] :
    SMul S (FractionRing (MvPolynomial (Fin k) K ⧸ J)) := Algebra.toSMul

/-- Use the algebra's module structure directly in the normalization construction. -/
noncomputable local instance gradedNormAlgebraModule {K : Type*} [Field K] {k : ℕ}
    (J : Ideal (MvPolynomial (Fin k) K)) (S : Type*) [CommSemiring S]
    [Algebra S (FractionRing (MvPolynomial (Fin k) K ⧸ J))] :
    Module S (FractionRing (MvPolynomial (Fin k) K ⧸ J)) := Algebra.toModule

section ScaleEquiv

variable {K : Type*} [CommSemiring K] {σ : Type*}

/-- Node A07′: the scaling automorphism `X i ↦ C u * X i` of `MvPolynomial σ K`, for a unit `u`. -/
noncomputable def scaleEquiv (u : Kˣ) : MvPolynomial σ K ≃ₐ[K] MvPolynomial σ K :=
  AlgEquiv.ofAlgHom (aeval fun i ↦ C (u : K) * X i) (aeval fun i ↦ C ((u⁻¹ : Kˣ) : K) * X i)
    (by ext i; simp [algebraMap_eq, ← mul_assoc, ← C_mul])
    (by ext i; simp [algebraMap_eq, ← mul_assoc, ← C_mul])

variable (u : Kˣ)

/-- Node A07′: `scaleEquiv u = aeval (C u * X i)`. -/
theorem scaleEquiv_apply (F : MvPolynomial σ K) :
    scaleEquiv u F = aeval (fun i ↦ C (u : K) * X i) F :=
  rfl

/-- Node A07′: the inverse of `scaleEquiv u` is `scaleEquiv u⁻¹`. -/
theorem scaleEquiv_symm_apply (F : MvPolynomial σ K) :
    (scaleEquiv u).symm F = scaleEquiv u⁻¹ F :=
  rfl

/-- Node A07′: `scaleEquiv u (X i) = C u * X i`. -/
@[simp]
theorem scaleEquiv_X (i : σ) : scaleEquiv u (X i) = C (u : K) * X i :=
  aeval_X _ i

/-- Node A07′: `scaleEquiv u` fixes constants. -/
@[simp]
theorem scaleEquiv_C (a : K) : scaleEquiv u (C a : MvPolynomial σ K) = C a := by
  rw [scaleEquiv_apply, aeval_C, algebraMap_eq]

/-- Node A07′: `scaleEquiv u` multiplies the monomial `X ^ α` by `u ^ |α|`. -/
theorem scaleEquiv_monomial (α : σ →₀ ℕ) (a : K) :
    scaleEquiv u (monomial α a) = monomial α ((u : K) ^ α.degree * a) := by
  rw [scaleEquiv_apply, aeval_monomial, algebraMap_eq, Finsupp.prod, Finsupp.degree_apply]
  simp_rw [mul_pow, ← C_pow, Finset.prod_mul_distrib, ← map_prod, Finset.prod_pow_eq_pow_sum]
  rw [← C_mul_monomial, monomial_eq, Finsupp.prod, mul_left_comm]

/-- Node A07′: the coefficients of `scaleEquiv u F`. -/
theorem coeff_scaleEquiv (F : MvPolynomial σ K) (α : σ →₀ ℕ) :
    (scaleEquiv u F).coeff α = (u : K) ^ α.degree * F.coeff α := by
  classical
  conv_lhs => rw [F.as_sum, map_sum]
  simp_rw [scaleEquiv_monomial, coeff_sum, coeff_monomial]
  rw [Finset.sum_ite_eq', ← mul_ite_zero]
  split_ifs with h
  · rfl
  · rw [notMem_support_iff.mp h, mul_zero]

/-- Node A07′: `scaleEquiv u` multiplies a form of degree `t` by `u ^ t`. -/
theorem scaleEquiv_apply_isHomogeneous {F : MvPolynomial σ K} {t : ℕ} (hF : F.IsHomogeneous t) :
    scaleEquiv u F = C ((u : K) ^ t) * F := by
  ext α
  rw [coeff_scaleEquiv, coeff_C_mul]
  by_cases h : F.coeff α = 0
  · rw [h, mul_zero, mul_zero]
  · have hα : α.degree = t := by
      rw [Finsupp.degree_eq_weight_one]
      exact hF h
    rw [hα]

/-- Node A07′: `scaleEquiv u` maps a homogeneous ideal onto itself (one inclusion). -/
theorem scaleEquiv_mem_of_mem {J : Ideal (MvPolynomial σ K)}
    (hJ : J.IsHomogeneous (homogeneousSubmodule σ K)) {G : MvPolynomial σ K} (hG : G ∈ J) :
    scaleEquiv u G ∈ J := by
  rw [← sum_homogeneousComponent G, map_sum]
  refine Ideal.sum_mem _ fun i _ ↦ ?_
  rw [scaleEquiv_apply_isHomogeneous u (homogeneousComponent_isHomogeneous i G)]
  exact J.mul_mem_left _ (homogeneousComponent_mem_of_mem hJ hG i)

/-- Node A07′: `scaleEquiv u` maps a homogeneous ideal onto itself. -/
theorem scaleEquiv_map_eq_of_isHomogeneous {J : Ideal (MvPolynomial σ K)}
    (hJ : J.IsHomogeneous (homogeneousSubmodule σ K)) :
    J.map (scaleEquiv (σ := σ) u : MvPolynomial σ K →+* MvPolynomial σ K) = J := by
  refine le_antisymm (Ideal.map_le_iff_le_comap.mpr fun G hG ↦ ?_) fun G hG ↦ ?_
  · exact scaleEquiv_mem_of_mem u hJ hG
  · have h := Ideal.mem_map_of_mem (scaleEquiv (σ := σ) u : MvPolynomial σ K →+* MvPolynomial σ K)
      (scaleEquiv_mem_of_mem u⁻¹ hJ hG)
    rwa [RingHom.coe_coe, ← scaleEquiv_symm_apply, AlgEquiv.apply_symm_apply] at h

end ScaleEquiv

section ScaleEquivField

variable {K : Type*} [Field K] {σ : Type*}

/-- Node A07′: **over an infinite field, a polynomial multiplied by `u ^ e` under every scaling
`scaleEquiv u` is a form of degree `e`.** For a monomial `α` of degree `j ≠ e` with nonzero
coefficient `c`, comparing coefficients gives `u ^ j * c = u ^ e * c` for all `u ≠ 0`, so the
nonzero polynomial `X ^ j - X ^ e ∈ K[X]` has infinitely many roots. -/
theorem isHomogeneous_of_forall_scaleEquiv_eq [Infinite K] {F : MvPolynomial σ K} {e : ℕ}
    (h : ∀ u : Kˣ, scaleEquiv u F = C ((u : K) ^ e) * F) : F.IsHomogeneous e := by
  intro α hα
  suffices key : α.degree = e by
    rw [Finsupp.degree_eq_weight_one] at key
    exact key
  by_contra hne
  have hcoeff : ∀ u : Kˣ, (u : K) ^ α.degree = (u : K) ^ e := fun u ↦ by
    have := congrArg (fun p : MvPolynomial σ K => p.coeff α) (h u)
    rw [coeff_scaleEquiv, coeff_C_mul] at this
    exact mul_right_cancel₀ hα this
  set p : Polynomial K := Polynomial.X ^ α.degree - Polynomial.X ^ e with hp
  have hp0 : p ≠ 0 := fun h0 ↦ by
    have := congrArg (Polynomial.coeff · α.degree) h0
    simp only [hp, Polynomial.coeff_sub, Polynomial.coeff_X_pow, ite_true, Polynomial.coeff_zero,
      ite_eq_right hne, sub_zero] at this
    exact one_ne_zero this
  refine hp0 (Polynomial.eq_zero_of_infinite_isRoot p ?_)
  refine Set.Infinite.mono ?_ ((Set.finite_singleton (0 : K)).infinite_compl)
  intro x hx
  have hx0 : x ≠ 0 := hx
  simp only [Set.mem_ofPred_eq, hp, Polynomial.IsRoot, Polynomial.eval_sub, Polynomial.eval_pow,
    Polynomial.eval_X]
  have hx' := hcoeff (Units.mk0 x hx0)
  rw [Units.val_mk0] at hx'
  rw [hx', sub_self]

end ScaleEquivField

/-! ### Part 2: the norm in the shared setting -/

section Norm

variable {K : Type*} [Field K] {n s : ℕ} {J : Ideal (MvPolynomial (Fin n) K)}
  {y : Fin s → MvPolynomial (Fin n) K}

/-- Node A07′: the scaling automorphism `σ_u` of `R = Q ⧸ J` induced by `scaleEquiv u` on `Q`, for
a homogeneous ideal `J`. -/
noncomputable def scaleQuotEquiv (hJh : J.IsHomogeneous (homogeneousSubmodule (Fin n) K)) (u : Kˣ) :
    (MvPolynomial (Fin n) K ⧸ J) ≃ₐ[K] MvPolynomial (Fin n) K ⧸ J :=
  Ideal.quotientEquivAlg J J (scaleEquiv u) (scaleEquiv_map_eq_of_isHomogeneous u hJh).symm

/-- Node A07′: `σ_u (mk G) = mk (scaleEquiv u G)`. -/
theorem scaleQuotEquiv_mk (hJh : J.IsHomogeneous (homogeneousSubmodule (Fin n) K)) (u : Kˣ)
    (G : MvPolynomial (Fin n) K) :
    scaleQuotEquiv hJh u (Ideal.Quotient.mk J G) = Ideal.Quotient.mk J (scaleEquiv u G) :=
  rfl

/-- Node A07′: in the shared setting, `algebraMap S R (C a) = mk J (C a)`. -/
theorem algebraMap_C_eq_mk [Algebra (MvPolynomial (Fin s) K) (MvPolynomial (Fin n) K ⧸ J)]
    (halg : algebraMap (MvPolynomial (Fin s) K) (MvPolynomial (Fin n) K ⧸ J) =
      (MvPolynomial.aeval fun i ↦ Ideal.Quotient.mk J (y i)).toRingHom) (a : K) :
    algebraMap (MvPolynomial (Fin s) K) (MvPolynomial (Fin n) K ⧸ J) (C a) =
      Ideal.Quotient.mk J (C a) := by
  rw [halg, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, aeval_C, ← Ideal.Quotient.mk_algebraMap,
    MvPolynomial.algebraMap_eq]

/-- Node A07′: **`σ_u` is compatible with the scaling `τ_u := scaleEquiv u` of `S`:**
`σ_u (algebraMap S R a) = algebraMap S R (τ_u a)`, since the `y i` are linear forms. -/
theorem scaleQuotEquiv_algebraMap (hJh : J.IsHomogeneous (homogeneousSubmodule (Fin n) K))
    (hy : ∀ i, (y i).IsHomogeneous 1)
    [Algebra (MvPolynomial (Fin s) K) (MvPolynomial (Fin n) K ⧸ J)]
    (halg : algebraMap (MvPolynomial (Fin s) K) (MvPolynomial (Fin n) K ⧸ J) =
      (MvPolynomial.aeval fun i ↦ Ideal.Quotient.mk J (y i)).toRingHom) (u : Kˣ)
    (a : MvPolynomial (Fin s) K) :
    scaleQuotEquiv hJh u (algebraMap (MvPolynomial (Fin s) K) (MvPolynomial (Fin n) K ⧸ J) a) =
      algebraMap (MvPolynomial (Fin s) K) (MvPolynomial (Fin n) K ⧸ J) (scaleEquiv u a) := by
  rw [halg, AlgHom.toRingHom_eq_coe, RingHom.coe_coe]
  have key : (scaleQuotEquiv hJh u).toAlgHom.comp
        (MvPolynomial.aeval fun i ↦ Ideal.Quotient.mk J (y i)) =
      (MvPolynomial.aeval fun i ↦ Ideal.Quotient.mk J (y i)).comp (scaleEquiv u).toAlgHom := by
    apply MvPolynomial.algHom_ext
    intro i
    simp only [AlgHom.comp_apply, AlgEquiv.coe_toAlgHom, aeval_X, scaleEquiv_X, map_mul,
      scaleQuotEquiv_mk, scaleEquiv_apply_isHomogeneous u (hy i), pow_one, aeval_C,
      ← Ideal.Quotient.mk_algebraMap, MvPolynomial.algebraMap_eq]
  exact AlgHom.congr_fun key a

-- synthesizing `Module (MvPolynomial (Fin s) K) (MvPolynomial (Fin n) K ⧸ J)` from the `Algebra`
-- instance first explores `Submodule.Quotient.module'` and needs about `40000` heartbeats
/-- Node A07′: **the fraction field of `R` is finite-dimensional over the fraction field of `S`.**
`R` is a finite `S`-module (A02.h), and a finite `S`-spanning set of `R` spans `Frac R` over
`Frac S` because `R` is algebraic over `S`. -/
theorem finite_fractionRing_of_pow_idealOfVars_le
    (hJh : J.IsHomogeneous (homogeneousSubmodule (Fin n) K)) (hy : ∀ i, (y i).IsHomogeneous 1)
    {N : ℕ} (hN : idealOfVars (Fin n) K ^ N ≤ J ⊔ Ideal.span (Set.range y)) [J.IsPrime]
    [Algebra (MvPolynomial (Fin s) K) (MvPolynomial (Fin n) K ⧸ J)]
    (halg : algebraMap (MvPolynomial (Fin s) K) (MvPolynomial (Fin n) K ⧸ J) =
      (MvPolynomial.aeval fun i ↦ Ideal.Quotient.mk J (y i)).toRingHom)
    [Algebra (FractionRing (MvPolynomial (Fin s) K)) (FractionRing (MvPolynomial (Fin n) K ⧸ J))]
    [IsScalarTower (MvPolynomial (Fin s) K) (FractionRing (MvPolynomial (Fin s) K))
      (FractionRing (MvPolynomial (Fin n) K ⧸ J))] :
    Module.Finite (FractionRing (MvPolynomial (Fin s) K))
      (FractionRing (MvPolynomial (Fin n) K ⧸ J)) := by
  have hfin : Module.Finite (MvPolynomial (Fin s) K) (MvPolynomial (Fin n) K ⧸ J) :=
    finite_of_pow_idealOfVars_le' hJh hy hN halg
  have : Algebra.IsIntegral (MvPolynomial (Fin s) K) (MvPolynomial (Fin n) K ⧸ J) :=
    Algebra.IsIntegral.of_finite _ _
  obtain ⟨b, hb⟩ := hfin.fg_top
  have inj : Function.Injective
      (algebraMap (MvPolynomial (Fin s) K) (FractionRing (MvPolynomial (Fin n) K ⧸ J))) := by
    rw [IsScalarTower.algebraMap_eq (MvPolynomial (Fin s) K) (FractionRing (MvPolynomial (Fin s) K))
      (FractionRing (MvPolynomial (Fin n) K ⧸ J))]
    exact (algebraMap (FractionRing (MvPolynomial (Fin s) K))
      (FractionRing (MvPolynomial (Fin n) K ⧸ J))).injective.comp (IsFractionRing.injective _ _)
  have key := IsFractionRing.ideal_span_singleton_map_subset (MvPolynomial (Fin s) K)
    (K := FractionRing (MvPolynomial (Fin s) K)) (L := FractionRing (MvPolynomial (Fin n) K ⧸ J))
    (a := (1 : MvPolynomial (Fin n) K ⧸ J)) (b := (b : Set (MvPolynomial (Fin n) K ⧸ J))) inj
    (by rw [hb]; exact fun x _ ↦ Submodule.mem_top)
  classical
  refine ⟨⟨b.image (algebraMap _ _), ?_⟩⟩
  rw [Finset.coe_image, eq_top_iff]
  intro x _
  apply key
  rw [map_one, Ideal.span_singleton_one]
  exact Submodule.mem_top

-- synthesizing `Module (MvPolynomial (Fin s) K) (MvPolynomial (Fin n) K ⧸ J)` from the `Algebra`
-- instance first explores `Submodule.Quotient.module'` and needs about `40000` heartbeats
/-- Node A07′: **the norm of an element of `R` lies in `S`.** `F` is integral over `S` (`R` is a
finite `S`-module by A02.h), hence so is its norm, and `S = MvPolynomial (Fin s) K` is integrally
closed. -/
theorem norm_mem_range_algebraMap
    (hJh : J.IsHomogeneous (homogeneousSubmodule (Fin n) K)) (hy : ∀ i, (y i).IsHomogeneous 1)
    {N : ℕ} (hN : idealOfVars (Fin n) K ^ N ≤ J ⊔ Ideal.span (Set.range y)) [J.IsPrime]
    [Algebra (MvPolynomial (Fin s) K) (MvPolynomial (Fin n) K ⧸ J)]
    (halg : algebraMap (MvPolynomial (Fin s) K) (MvPolynomial (Fin n) K ⧸ J) =
      (MvPolynomial.aeval fun i ↦ Ideal.Quotient.mk J (y i)).toRingHom)
    [Algebra (FractionRing (MvPolynomial (Fin s) K)) (FractionRing (MvPolynomial (Fin n) K ⧸ J))]
    [IsScalarTower (MvPolynomial (Fin s) K) (FractionRing (MvPolynomial (Fin s) K))
      (FractionRing (MvPolynomial (Fin n) K ⧸ J))]
    (F : MvPolynomial (Fin n) K ⧸ J) :
    ∃ c : MvPolynomial (Fin s) K,
      algebraMap (MvPolynomial (Fin s) K) (FractionRing (MvPolynomial (Fin s) K)) c =
        Algebra.norm (FractionRing (MvPolynomial (Fin s) K))
          (algebraMap (MvPolynomial (Fin n) K ⧸ J)
            (FractionRing (MvPolynomial (Fin n) K ⧸ J)) F) := by
  have : Module.Finite (MvPolynomial (Fin s) K) (MvPolynomial (Fin n) K ⧸ J) :=
    finite_of_pow_idealOfVars_le' hJh hy hN halg
  have hF : IsIntegral (MvPolynomial (Fin s) K)
      (algebraMap (MvPolynomial (Fin n) K ⧸ J) (FractionRing (MvPolynomial (Fin n) K ⧸ J)) F) :=
    (IsIntegral.of_finite (MvPolynomial (Fin s) K) F).map
      (IsScalarTower.toAlgHom (MvPolynomial (Fin s) K) (MvPolynomial (Fin n) K ⧸ J)
        (FractionRing (MvPolynomial (Fin n) K ⧸ J)))
  exact IsIntegrallyClosed.isIntegral_iff.mp
    (Algebra.isIntegral_norm (FractionRing (MvPolynomial (Fin s) K)) hF)

-- synthesizing `Module (MvPolynomial (Fin s) K) (MvPolynomial (Fin n) K ⧸ J)` from the `Algebra`
-- instance first explores `Submodule.Quotient.module'` and needs about `40000` heartbeats
/-- Node A07′: **the norm of a homogeneous element of degree `t` is a form of degree
`t * [Frac R : Frac S]`.** The scaling automorphisms `σ_u` of `R` and `τ_u` of `S` extend to the
fraction fields compatibly with `algebraMap (Frac S) (Frac R)`, so
`τ_u (N F) = N (σ_u F) = N (u ^ t • F) = u ^ (t Δ) N F`; conclude with
`isHomogeneous_of_forall_scaleEquiv_eq`. -/
theorem norm_isHomogeneous [Infinite K]
    (hJh : J.IsHomogeneous (homogeneousSubmodule (Fin n) K)) (hy : ∀ i, (y i).IsHomogeneous 1)
    [Algebra (MvPolynomial (Fin s) K) (MvPolynomial (Fin n) K ⧸ J)]
    (halg : algebraMap (MvPolynomial (Fin s) K) (MvPolynomial (Fin n) K ⧸ J) =
      (MvPolynomial.aeval fun i ↦ Ideal.Quotient.mk J (y i)).toRingHom)
    [Algebra (FractionRing (MvPolynomial (Fin s) K)) (FractionRing (MvPolynomial (Fin n) K ⧸ J))]
    [IsScalarTower (MvPolynomial (Fin s) K) (FractionRing (MvPolynomial (Fin s) K))
      (FractionRing (MvPolynomial (Fin n) K ⧸ J))]
    {F : MvPolynomial (Fin n) K ⧸ J} {t : ℕ} (hF : IsHomogeneousElem J F t)
    {c : MvPolynomial (Fin s) K}
    (hc : algebraMap (MvPolynomial (Fin s) K) (FractionRing (MvPolynomial (Fin s) K)) c =
      Algebra.norm (FractionRing (MvPolynomial (Fin s) K))
        (algebraMap (MvPolynomial (Fin n) K ⧸ J) (FractionRing (MvPolynomial (Fin n) K ⧸ J)) F)) :
    c.IsHomogeneous (t * Module.finrank (FractionRing (MvPolynomial (Fin s) K))
      (FractionRing (MvPolynomial (Fin n) K ⧸ J))) := by
  obtain ⟨G, hG, rfl⟩ := hF
  apply isHomogeneous_of_forall_scaleEquiv_eq
  intro u
  apply IsFractionRing.injective (MvPolynomial (Fin s) K) (FractionRing (MvPolynomial (Fin s) K))
  -- the scaling automorphisms of the fraction fields
  let τ : FractionRing (MvPolynomial (Fin s) K) ≃+* FractionRing (MvPolynomial (Fin s) K) :=
    IsFractionRing.ringEquivOfRingEquiv (scaleEquiv (σ := Fin s) u).toRingEquiv
  let σ : FractionRing (MvPolynomial (Fin n) K ⧸ J) ≃+* FractionRing (MvPolynomial (Fin n) K ⧸ J) :=
    IsFractionRing.ringEquivOfRingEquiv (scaleQuotEquiv hJh u).toRingEquiv
  have hτ : ∀ a : MvPolynomial (Fin s) K, τ (algebraMap _ _ a) = algebraMap _ _ (scaleEquiv u a) :=
    fun a ↦ IsFractionRing.ringEquivOfRingEquiv_algebraMap _ a
  have hσ : ∀ r : MvPolynomial (Fin n) K ⧸ J,
      σ (algebraMap _ _ r) = algebraMap _ _ (scaleQuotEquiv hJh u r) :=
    fun r ↦ IsFractionRing.ringEquivOfRingEquiv_algebraMap _ r
  -- compatibility with `algebraMap (Frac S) (Frac R)`
  have he : (algebraMap (FractionRing (MvPolynomial (Fin s) K))
        (FractionRing (MvPolynomial (Fin n) K ⧸ J))).comp (τ : _ →+* _) =
      (σ : _ →+* _).comp (algebraMap (FractionRing (MvPolynomial (Fin s) K))
        (FractionRing (MvPolynomial (Fin n) K ⧸ J))) := by
    apply IsLocalization.ringHom_ext (nonZeroDivisors (MvPolynomial (Fin s) K))
    refine RingHom.ext fun a ↦ ?_
    simp only [RingHom.comp_apply, RingHom.coe_coe]
    rw [hτ, ← IsScalarTower.algebraMap_apply (MvPolynomial (Fin s) K)
        (FractionRing (MvPolynomial (Fin s) K)) (FractionRing (MvPolynomial (Fin n) K ⧸ J)),
      ← IsScalarTower.algebraMap_apply (MvPolynomial (Fin s) K)
        (FractionRing (MvPolynomial (Fin s) K)) (FractionRing (MvPolynomial (Fin n) K ⧸ J)),
      IsScalarTower.algebraMap_apply (MvPolynomial (Fin s) K) (MvPolynomial (Fin n) K ⧸ J)
        (FractionRing (MvPolynomial (Fin n) K ⧸ J)),
      IsScalarTower.algebraMap_apply (MvPolynomial (Fin s) K) (MvPolynomial (Fin n) K ⧸ J)
        (FractionRing (MvPolynomial (Fin n) K ⧸ J)),
      hσ, scaleQuotEquiv_algebraMap hJh hy halg]
  -- `σ_u F = u ^ t • F`
  have hx : σ (algebraMap _ _ (Ideal.Quotient.mk J G)) =
      algebraMap (FractionRing (MvPolynomial (Fin s) K)) (FractionRing (MvPolynomial (Fin n) K ⧸ J))
        (algebraMap _ _ (C ((u : K) ^ t) : MvPolynomial (Fin s) K)) *
        algebraMap _ _ (Ideal.Quotient.mk J G) := by
    rw [hσ, scaleQuotEquiv_mk, scaleEquiv_apply_isHomogeneous u hG, map_mul, map_mul,
      ← algebraMap_C_eq_mk halg,
      ← IsScalarTower.algebraMap_apply (MvPolynomial (Fin s) K) (MvPolynomial (Fin n) K ⧸ J),
      IsScalarTower.algebraMap_apply (MvPolynomial (Fin s) K)
        (FractionRing (MvPolynomial (Fin s) K))]
  have hnorm := Algebra.norm_eq_of_equiv_equiv τ σ he (algebraMap _ _ (Ideal.Quotient.mk J G))
  rw [eq_comm, RingEquiv.symm_apply_eq, hx, map_mul, Algebra.norm_algebraMap, ← hc, hτ, ← map_pow,
    ← map_mul] at hnorm
  rw [← hnorm, ← C_pow, ← pow_mul]

end Norm

end Nikodym.LowerBound

/- Adapted for Lean Pool: module imports and compatibility with its pinned toolchain. -/
