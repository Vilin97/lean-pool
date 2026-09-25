/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/
module


public import LeanPool.ClassFieldTheory.ClassFieldTheory.AlgebraicNumberTheory.Idele.ClassGroup.Core
public import LeanPool.ClassFieldTheory.ClassFieldTheory.AlgebraicNumberTheory.Idele.NormCore
public import Mathlib.RingTheory.FractionalIdeal.Norm
/-!
# The product formula for principal ideles

This file proves that the absolute idele norm is trivial on the diagonal
copy of `Kˣ`, and hence descends to the idele class group.
-/

@[expose] public section

open scoped NumberField RestrictedProduct NNReal WithZero
open NumberField IsDedekindDomain

noncomputable section


variable {K : Type*} [Field K] [NumberField K]

namespace InfiniteIdeleGroup

/-- The archimedean norm of a principal idele is the absolute field norm. -/
theorem archimedeanNorm_principalIdele (x : Kˣ) :
    ((archimedeanNorm
        (IdeleGroup.principalIdele K x).1 : ℝ≥0ˣ) : ℝ≥0) =
      ⟨|(Algebra.norm ℚ) (x : K)|, abs_nonneg _⟩ := by
  rw [archimedeanNorm_apply]
  simp only [Units.coe_prod, Units.val_pow_eq_pow_val,
    nnnormUnitHom_val]
  apply NNReal.eq
  simp only [NNReal.coe_prod, NNReal.coe_pow, coe_nnnorm]
  change (∏ w : InfinitePlace K,
      ‖((InfiniteIdeleGroup.component w
        (IdeleGroup.principalIdele K x).1 : w.Completionˣ) :
          w.Completion)‖ ^ w.mult) =
      |((Algebra.norm ℚ) (x : K) : ℝ)|
  simp_rw [show ∀ w : InfinitePlace K,
      ((InfiniteIdeleGroup.component w
        (IdeleGroup.principalIdele K x).1 : w.Completionˣ) :
          w.Completion) = (x : K) by
    intro w
    exact IdeleGroup.infiniteComponent_principalIdele x w]
  have hnorm (w : InfinitePlace K) :
      ‖((x : K) : w.Completion)‖ = w (x : K) := by
    change ‖(((WithAbs.equiv w.1).symm (x : K) :
      WithAbs w.1) : w.Completion)‖ = w (x : K)
    rw [InfinitePlace.Completion.norm_coe,
      (WithAbs.equiv w.1).apply_symm_apply]
  simp_rw [hnorm]
  have hproduct :=
    NumberField.prod_abs_eq_one (Units.ne_zero x)
  have hfinite :=
    FinitePlace.prod_eq_inv_abs_norm (Units.ne_zero x)
  rw [hfinite] at hproduct
  have hnorm_ne_zero :
      (Algebra.norm ℚ) (x : K) ≠ 0 :=
    Algebra.norm_ne_zero_iff.mpr (Units.ne_zero x)
  have habs_ne_zero :
      (|(Algebra.norm ℚ) (x : K)| : ℚ) ≠ 0 :=
    abs_ne_zero.mpr hnorm_ne_zero
  have hcast_ne_zero :
      ((|(Algebra.norm ℚ) (x : K)| : ℚ) : ℝ) ≠ 0 := by
    exact_mod_cast habs_ne_zero
  have hproduct' :
      (∏ w : InfinitePlace K, w (x : K) ^ w.mult) *
        ((|(Algebra.norm ℚ) (x : K)| : ℚ) : ℝ)⁻¹ = 1 := by
    simpa only [Rat.cast_inv] using hproduct
  have hresult :=
    (mul_inv_eq_one₀ hcast_ne_zero).mp hproduct'
  simpa only [Rat.cast_abs] using hresult

end InfiniteIdeleGroup

namespace FractionalIdealGroup

/-- The positive absolute norm of a nonzero fractional ideal. -/
def absoluteNorm :
    FractionalIdealGroup K →* ℝ≥0ˣ where
  toFun I :=
    Units.mk0
      ⟨(FractionalIdeal.absNorm
          (I : FractionalIdeal (nonZeroDivisors (𝓞 K)) K) : ℝ),
        Rat.cast_nonneg.mpr
          (FractionalIdeal.absNorm_nonneg
            (I : FractionalIdeal (nonZeroDivisors (𝓞 K)) K))⟩
      (by
        intro h
        have hr := congrArg (fun z : ℝ≥0 => z.1) h
        change
          ((FractionalIdeal.absNorm
            (I : FractionalIdeal
              (nonZeroDivisors (𝓞 K)) K) : ℚ) : ℝ) = 0 at hr
        have hq : FractionalIdeal.absNorm
            (I : FractionalIdeal
              (nonZeroDivisors (𝓞 K)) K) = 0 := by
          exact_mod_cast hr
        exact Units.ne_zero I
          (FractionalIdeal.absNorm_eq_zero_iff.mp hq))
  map_one' := by
    apply Units.ext
    apply NNReal.eq
    change
      ((FractionalIdeal.absNorm
        (1 : FractionalIdeal
          (nonZeroDivisors (𝓞 K)) K) : ℚ) : ℝ) = 1
    rw [FractionalIdeal.absNorm_one]
    norm_num
  map_mul' I J := by
    apply Units.ext
    change
      (⟨(FractionalIdeal.absNorm
          ((I * J : FractionalIdealGroup K) :
            FractionalIdeal (nonZeroDivisors (𝓞 K)) K) : ℝ),
        Rat.cast_nonneg.mpr
          (FractionalIdeal.absNorm_nonneg
            ((I * J : FractionalIdealGroup K) :
              FractionalIdeal (nonZeroDivisors (𝓞 K)) K))⟩ : ℝ≥0) =
      ⟨(FractionalIdeal.absNorm
          (I : FractionalIdeal
            (nonZeroDivisors (𝓞 K)) K) : ℝ),
        Rat.cast_nonneg.mpr
          (FractionalIdeal.absNorm_nonneg
            (I : FractionalIdeal
              (nonZeroDivisors (𝓞 K)) K))⟩ *
      ⟨(FractionalIdeal.absNorm
          (J : FractionalIdeal
            (nonZeroDivisors (𝓞 K)) K) : ℝ),
        Rat.cast_nonneg.mpr
          (FractionalIdeal.absNorm_nonneg
            (J : FractionalIdeal
              (nonZeroDivisors (𝓞 K)) K))⟩
    apply NNReal.eq
    change
      ((FractionalIdeal.absNorm
        ((I * J : FractionalIdealGroup K) :
          FractionalIdeal (nonZeroDivisors (𝓞 K)) K) : ℚ) : ℝ) =
      ((FractionalIdeal.absNorm
        (I : FractionalIdeal
          (nonZeroDivisors (𝓞 K)) K) : ℚ) : ℝ) *
      ((FractionalIdeal.absNorm
        (J : FractionalIdeal
          (nonZeroDivisors (𝓞 K)) K) : ℚ) : ℝ)
    norm_cast
    simpa only [Units.val_mul] using
      (map_mul FractionalIdeal.absNorm
        (I : FractionalIdeal (nonZeroDivisors (𝓞 K)) K)
        (J : FractionalIdeal (nonZeroDivisors (𝓞 K)) K))

@[simp]
theorem absoluteNorm_prime (v : HeightOneSpectrum (𝓞 K)) :
    absoluteNorm (prime v) = FiniteIdeleGroup.primeNorm v := by
  apply Units.ext
  apply NNReal.eq
  change
    ((FractionalIdeal.absNorm
      (v.asIdeal :
        FractionalIdeal (nonZeroDivisors (𝓞 K)) K) : ℚ) : ℝ) =
      (v.asIdeal.absNorm : ℝ)
  rw [FractionalIdeal.coeIdeal_absNorm]
  norm_cast

/-- The explicit prime-factor norm commutes with the factorization of a
fractional ideal. -/
theorem absoluteNorm_factorization
    (e : Multiplicative
      (HeightOneSpectrum (𝓞 K) →₀ ℤ)) :
    absoluteNorm (factorization e) =
      FiniteIdeleGroup.divisorNorm e := by
  change absoluteNorm
      (e.toAdd.prod fun v n => primePowerHom v
        (Multiplicative.ofAdd n)) =
    e.toAdd.prod fun v n =>
      FiniteIdeleGroup.primeNormPowerHom v
        (Multiplicative.ofAdd n)
  rw [map_finsuppProd]
  apply Finsupp.prod_congr
  intro v hv
  change absoluteNorm (prime v ^ e.toAdd v) =
    FiniteIdeleGroup.primeNorm v ^ e.toAdd v
  rw [map_zpow, absoluteNorm_prime]

/-- The norm of the principal fractional ideal `(x)` is the absolute field
norm of `x`. -/
theorem absoluteNorm_toPrincipalIdeal (x : Kˣ) :
    ((absoluteNorm
      (toPrincipalIdeal (𝓞 K) K x) : ℝ≥0ˣ) : ℝ≥0) =
      ⟨|((Algebra.norm ℚ) (x : K) : ℝ)|, abs_nonneg _⟩ := by
  apply NNReal.eq
  change
    ((FractionalIdeal.absNorm
      ((toPrincipalIdeal (𝓞 K) K x :
        FractionalIdealGroup K) :
        FractionalIdeal (nonZeroDivisors (𝓞 K)) K) : ℚ) : ℝ) =
      |((Algebra.norm ℚ) (x : K) : ℝ)|
  rw [coe_toPrincipalIdeal,
    FractionalIdeal.absNorm_span_singleton, Rat.cast_abs]

end FractionalIdealGroup

namespace FiniteIdeleGroup

/-- The finite idele norm is the absolute norm of its associated fractional
ideal. -/
theorem absoluteNorm_eq_fractionalIdealAbsoluteNorm
    (a : FiniteIdeleGroup K) :
    absoluteNorm a =
      FractionalIdealGroup.absoluteNorm (fractionalIdeal a) := by
  change divisorNorm (valuationVector a) =
    FractionalIdealGroup.absoluteNorm
      (FractionalIdealGroup.factorization (valuationVector a))
  exact (FractionalIdealGroup.absoluteNorm_factorization
    (valuationVector a)).symm

/-- The finite norm of a principal idele is the absolute field norm. -/
theorem absoluteNorm_principalIdele (x : Kˣ) :
    ((absoluteNorm
      (IdeleGroup.principalIdele K x).2 : ℝ≥0ˣ) : ℝ≥0) =
      ⟨|((Algebra.norm ℚ) (x : K) : ℝ)|, abs_nonneg _⟩ := by
  rw [absoluteNorm_eq_fractionalIdealAbsoluteNorm]
  have h :
      fractionalIdeal (IdeleGroup.principalIdele K x).2 =
        toPrincipalIdeal (𝓞 K) K x :=
    IdeleGroup.fractionalIdeal_principalIdele x
  rw [h, FractionalIdealGroup.absoluteNorm_toPrincipalIdeal]

end FiniteIdeleGroup

namespace IdeleGroup

/-- The finite and archimedean norm factors agree on a principal idele. -/
theorem finite_absoluteNorm_eq_archimedeanNorm_principalIdele
    (x : Kˣ) :
    FiniteIdeleGroup.absoluteNorm (principalIdele K x).2 =
      InfiniteIdeleGroup.archimedeanNorm
        (principalIdele K x).1 := by
  apply Units.ext
  exact (FiniteIdeleGroup.absoluteNorm_principalIdele x).trans
    (InfiniteIdeleGroup.archimedeanNorm_principalIdele x).symm

/-- The number-field product formula in idelic form: every principal idele
has global absolute norm one. -/
theorem absoluteNorm_principalIdele (x : Kˣ) :
    absoluteNorm (principalIdele K x) = 1 := by
  rw [absoluteNorm_apply,
    finite_absoluteNorm_eq_archimedeanNorm_principalIdele]
  exact mul_inv_cancel _

/-- Principal ideles lie in the norm-one subgroup. -/
theorem principalSubgroup_le_normOneSubgroup :
    principalSubgroup K ≤ normOneSubgroup (K := K) := by
  rintro a ⟨x, rfl⟩
  exact absoluteNorm_principalIdele x

end IdeleGroup

namespace IdeleClassGroup

/-- The absolute idele norm descended through `C_K = I_K / Kˣ`. -/
def absoluteNorm :
    IdeleClassGroup K →* ℝ≥0ˣ :=
  QuotientGroup.lift (IdeleGroup.principalSubgroup K)
    (IdeleGroup.absoluteNorm (K := K))
    (IdeleGroup.principalSubgroup_le_normOneSubgroup (K := K))

theorem absoluteNorm_mk (a : IdeleGroup K) :
    absoluteNorm
      (QuotientGroup.mk' (IdeleGroup.principalSubgroup K) a) =
        IdeleGroup.absoluteNorm a :=
  QuotientGroup.lift_mk _ _ _

/-- The norm-one idele classes. -/
def normOneSubgroup : Subgroup (IdeleClassGroup K) :=
  (absoluteNorm (K := K)).ker

/-- Pulling the norm-one idele classes back to the idele group recovers
exactly the norm-one ideles. -/
theorem comap_normOneSubgroup :
    Subgroup.comap
      (QuotientGroup.mk' (IdeleGroup.principalSubgroup K))
      (normOneSubgroup (K := K)) =
        IdeleGroup.normOneSubgroup (K := K) := by
  ext a
  change absoluteNorm
      (QuotientGroup.mk' (IdeleGroup.principalSubgroup K) a) = 1 ↔
    IdeleGroup.absoluteNorm a = 1
  rw [absoluteNorm_mk]

theorem mk_mem_normOneSubgroup_iff (a : IdeleGroup K) :
    QuotientGroup.mk' (IdeleGroup.principalSubgroup K) a ∈
        normOneSubgroup (K := K) ↔
      a ∈ IdeleGroup.normOneSubgroup (K := K) := by
  change absoluteNorm
      (QuotientGroup.mk' (IdeleGroup.principalSubgroup K) a) = 1 ↔
    IdeleGroup.absoluteNorm a = 1
  rw [absoluteNorm_mk]

end IdeleClassGroup
