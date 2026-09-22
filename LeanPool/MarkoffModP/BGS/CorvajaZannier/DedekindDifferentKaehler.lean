/-
Copyright (c) 2026 Yuma Mizuno. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuma Mizuno
-/

import Mathlib.RingTheory.DedekindDomain.Different
import Mathlib.RingTheory.Kaehler.Basic
import Mathlib.RingTheory.TensorProduct.Maps
import Mathlib.LinearAlgebra.TensorProduct.Basis

/-!
# The trace different annihilates Kähler differentials

For a finite free extension `B / A` of integrally closed domains whose
fraction-field extension is separable, this file proves

`differentIdeal A B ≤ Module.annihilator B Ω[B⁄A]`.

The proof clears denominators in the trace-dual separability element.  If
`b₁, ..., bₙ` is an integral basis with trace-dual basis `b₁ˇ, ..., bₙˇ`
and `d` lies in the different, then every `d bᵢˇ` is integral.  Thus

`e_d = ∑ i, bᵢ ⊗ d bᵢˇ`

lies in `B ⊗[A] B`, has product `d`, and is killed by the kernel of the
multiplication map.  It follows that multiplication by `d` sends this kernel
into its square, hence kills its cotangent module `I / I² = Ω[B⁄A]`.
-/

open scoped BigOperators TensorProduct
open Polynomial Module

namespace BGS.CorvajaZannier

noncomputable section

section TraceSeparabilityElement

variable {K L ι : Type*} [Field K] [Field L] [Algebra K L]
  [FiniteDimensional K L] [Algebra.IsSeparable K L]
  [Fintype ι] [DecidableEq ι]

/-- The separability element attached to a basis and its trace-dual basis. -/
def traceSeparabilityElement (b : Basis ι K L) : L ⊗[K] L :=
  ∑ i, b i ⊗ₜ[K] b.traceDual i

private lemma traceDual_mul_eq_sum_repr (b : Basis ι K L) (x : L) (j : ι) :
    x * b.traceDual j = ∑ i, b.repr (x * b i) j • b.traceDual i := by
  rw [← b.traceDual.sum_repr (x * b.traceDual j)]
  apply Finset.sum_congr rfl
  intro i hi
  congr 1
  calc
    (b.traceDual).repr (x * b.traceDual j) i =
        Algebra.traceForm K L (x * b.traceDual j) (b i) :=
      b.traceDual_repr_apply _ _
    _ = Algebra.traceForm K L (x * b i) (b.traceDual j) := by
      simp only [Algebra.traceForm_apply]
      congr 1
      ring
    _ = (b.traceDual.traceDual).repr (x * b i) j :=
      ((b.traceDual).traceDual_repr_apply _ _).symm
    _ = b.repr (x * b i) j := by rw [b.traceDual_traceDual]

/-- The trace-dual separability element commutes with the two copies of the
field extension in the tensor product. -/
theorem traceSeparabilityElement_central (b : Basis ι K L) (x : L) :
    (x ⊗ₜ[K] (1 : L)) * traceSeparabilityElement b =
      ((1 : L) ⊗ₜ[K] x) * traceSeparabilityElement b := by
  apply (TensorProduct.equivFinsuppOfBasisLeft b).injective
  ext j
  simp only [traceSeparabilityElement, Finset.mul_sum,
    Algebra.TensorProduct.tmul_mul_tmul, one_mul, map_sum]
  simp only [Finset.sum_apply']
  simp_rw [TensorProduct.equivFinsuppOfBasisLeft_apply_tmul_apply]
  simp only [Basis.repr_self, Finsupp.single_apply, ite_smul, one_smul, zero_smul,
    Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  rw [← traceDual_mul_eq_sum_repr b x j]

/-- Multiplication sends the trace-dual separability element to one. -/
theorem traceSeparabilityElement_mul (b : Basis ι K L) :
    Algebra.TensorProduct.lmul' K (traceSeparabilityElement b) = 1 := by
  apply sub_eq_zero.mp
  apply (traceForm_nondegenerate K L).1
  intro y
  change Algebra.trace K L
    ((Algebra.TensorProduct.lmul' K (traceSeparabilityElement b) - 1) * y) = 0
  rw [sub_mul, one_mul, map_sub, sub_eq_zero, traceSeparabilityElement, map_sum]
  simp only [Algebra.TensorProduct.lmul'_apply_tmul, Finset.sum_mul, map_sum]
  rw [Algebra.trace_eq_matrix_trace b, Matrix.trace]
  apply Finset.sum_congr rfl
  intro i hi
  rw [Matrix.diag_apply, Algebra.leftMulMatrix_eq_repr_mul]
  calc
    Algebra.trace K L (b i * b.traceDual i * y) =
        Algebra.traceForm K L (y * b i) (b.traceDual i) := by
      simp only [Algebra.traceForm_apply]
      congr 1
      ring
    _ = (b.traceDual.traceDual).repr (y * b i) i :=
      ((b.traceDual).traceDual_repr_apply _ _).symm
    _ = b.repr (y * b i) i := by rw [b.traceDual_traceDual]

end TraceSeparabilityElement

section KaehlerFromSeparabilityElement

variable {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]

/-- A denominator-cleared separability element with product `d` proves that
`d` annihilates the relative Kähler differentials. -/
theorem mem_kaehlerAnnihilator_of_separabilityElement
    (d : S) (e : S ⊗[R] S)
    (hcentral : ∀ s : S, (s ⊗ₜ[R] (1 : S)) * e = ((1 : S) ⊗ₜ[R] s) * e)
    (hmul : Algebra.TensorProduct.lmul' R e = d) :
    d ∈ Module.annihilator S Ω[S⁄R] := by
  rw [Module.mem_annihilator]
  intro m
  let I := KaehlerDifferential.ideal R S
  obtain ⟨x, rfl⟩ := Ideal.toCotangent_surjective I m
  suffices d • (I.toCotangent x : I.Cotangent) = 0 by
    exact this
  rw [← smul_one_smul (S ⊗[R] S) d (I.toCotangent x)]
  rw [show d • (1 : S ⊗[R] S) = algebraMap S (S ⊗[R] S) d by
    simp [Algebra.smul_def]]
  rw [← LinearMap.map_smul I.toCotangent]
  apply (Ideal.toCotangent_eq_zero I _).2
  have hxspan : (x : S ⊗[R] S) ∈
      Submodule.span S (Set.range fun s : S ↦
        (1 : S) ⊗ₜ[R] s - s ⊗ₜ[R] (1 : S)) := by
    rw [KaehlerDifferential.submodule_span_range_eq_ideal]
    exact x.2
  have hxe : (x : S ⊗[R] S) * e = 0 := by
    refine Submodule.span_induction ?_ ?_ ?_ ?_ hxspan
    · rintro y ⟨s, rfl⟩
      rw [sub_mul, sub_eq_zero]
      exact (hcentral s).symm
    · rw [zero_mul]
    · intro y z hy hz hye hze
      rw [add_mul, hye, hze, add_zero]
    · intro c y hy hye
      rw [smul_mul_assoc, hye, smul_zero]
  let delta : S ⊗[R] S := d ⊗ₜ[R] (1 : S) - e
  have hdelta : delta ∈ I := by
    change Algebra.TensorProduct.lmul' R delta = 0
    simp [delta, hmul]
  rw [pow_two]
  have hprod : delta * (x : S ⊗[R] S) ∈ I * I :=
    Ideal.mul_mem_mul hdelta x.2
  convert hprod using 1
  · simp only [Submodule.coe_smul, Algebra.smul_def,
      Algebra.TensorProduct.algebraMap_apply]
    dsimp [delta]
    rw [sub_mul, mul_comm e, hxe, sub_zero]

end KaehlerFromSeparabilityElement

section IntegralDifferent

open scoped nonZeroDivisors

variable {A K B L κ : Type*}
  [CommRing A] [Field K] [CommRing B] [Field L]
  [Algebra A K] [Algebra B L] [Algebra A B] [Algebra K L] [Algebra A L]
  [IsScalarTower A K L] [IsScalarTower A B L]
  [IsDomain A] [IsFractionRing A K] [FiniteDimensional K L]
  [Algebra.IsSeparable K L] [IsIntegralClosure B A L]
  [IsIntegrallyClosed A] [IsDedekindDomain B]
  [Module.IsTorsionFree A B]
  [IsLocalization (Algebra.algebraMapSubmonoid B A⁰) L]
  [Fintype κ] [DecidableEq κ]

private lemma exists_integral_traceDual_mul
    (bA : Basis κ A B) (d : B) (hd : d ∈ differentIdeal A B) (i : κ) :
    ∃ c : B, algebraMap B L c = algebraMap B L d *
      (bA.localizationLocalization K A⁰ L).traceDual i := by
  let bK := bA.localizationLocalization K A⁰ L
  have hbspan : (1 : Submodule B L).restrictScalars A =
      Submodule.span A (Set.range bK) := by
    rw [Submodule.one_eq_range]
    exact (bA.localizationLocalization_span K A⁰ L).symm
  have hdual : bK.traceDual i ∈ Submodule.traceDual A K (1 : Submodule B L) := by
    rw [← Submodule.restrictScalars_mem A,
      Submodule.traceDual_span_of_basis A (1 : Submodule B L) bK hbspan]
    exact Submodule.subset_span (Set.mem_range_self i)
  let : IsFractionRing B L :=
    IsIntegralClosure.isFractionRing_of_finite_extension A K L B
  have hd' : algebraMap B L d ∈
      (FractionalIdeal.dual A K (1 : FractionalIdeal B⁰ L))⁻¹ := by
    have h := FractionalIdeal.mem_coeIdeal_of_mem (S := B⁰) (P := L) hd
    rwa [coeIdeal_differentIdeal A K L B] at h
  have hdual' : bK.traceDual i ∈
      FractionalIdeal.dual A K (1 : FractionalIdeal B⁰ L) := by
    change bK.traceDual i ∈
      (FractionalIdeal.dual A K (1 : FractionalIdeal B⁰ L) : Submodule B L)
    rw [FractionalIdeal.coe_dual_one]
    exact hdual
  have hprod : algebraMap B L d * bK.traceDual i ∈
      (1 : FractionalIdeal B⁰ L) :=
    (FractionalIdeal.mem_inv_iff
      (FractionalIdeal.dual_ne_zero A K
        (@one_ne_zero (FractionalIdeal B⁰ L) _ _ _))).mp hd' _ hdual'
  obtain ⟨c, hc⟩ := (FractionalIdeal.mem_one_iff B⁰).mp hprod
  exact ⟨c, hc⟩

end IntegralDifferent

section CanonicalDifferent

open scoped nonZeroDivisors

variable {A B κ : Type*}
  [CommRing A] [CommRing B] [Algebra A B]
  [IsDomain A] [IsIntegrallyClosed A] [IsDedekindDomain B]
  [Module.IsTorsionFree A B] [Module.Finite A B]
  [Algebra (FractionRing A) (FractionRing B)]
  [IsScalarTower A (FractionRing A) (FractionRing B)]
  [Algebra.IsSeparable (FractionRing A) (FractionRing B)]
  [Fintype κ] [DecidableEq κ]

private theorem mem_kaehlerAnnihilator_of_mem_differentIdeal_of_basis
    (bA : Basis κ A B) (d : B) (hd : d ∈ differentIdeal A B) :
    d ∈ Module.annihilator B Ω[B⁄A] := by
  let : IsIntegralClosure B A (FractionRing B) :=
    IsIntegralClosure.of_isIntegrallyClosed B A (FractionRing B)
  let : Algebra.IsAlgebraic (FractionRing A) (FractionRing B) :=
    isAlgebraic_of_isFractionRing A B ..
  let : IsLocalization
      (Algebra.algebraMapSubmonoid B A⁰) (FractionRing B) :=
    IsIntegralClosure.isLocalization A (FractionRing A) (FractionRing B) B
  let : FiniteDimensional (FractionRing A) (FractionRing B) :=
    .of_isLocalization A B A⁰
  let bK := bA.localizationLocalization (FractionRing A) A⁰ (FractionRing B)
  let c : κ → B := fun i ↦
    Classical.choose (exists_integral_traceDual_mul
      (K := FractionRing A) (L := FractionRing B) bA d hd i)
  have hc (i : κ) : algebraMap B (FractionRing B) (c i) =
      algebraMap B (FractionRing B) d * bK.traceDual i := by
    exact Classical.choose_spec (exists_integral_traceDual_mul
      (K := FractionRing A) (L := FractionRing B) bA d hd i)
  let e : B ⊗[A] B := ∑ i, bA i ⊗ₜ[A] c i
  apply mem_kaehlerAnnihilator_of_separabilityElement d e
  · intro x
    apply (TensorProduct.equivFinsuppOfBasisLeft bA).injective
    ext j
    simp only [e, Finset.mul_sum, Algebra.TensorProduct.tmul_mul_tmul,
      one_mul, map_sum, Finset.sum_apply']
    simp_rw [TensorProduct.equivFinsuppOfBasisLeft_apply_tmul_apply]
    simp only [Basis.repr_self, Finsupp.single_apply, ite_smul, one_smul,
      zero_smul, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
    apply FaithfulSMul.algebraMap_injective B (FractionRing B)
    rw [map_sum]
    have htrace := traceDual_mul_eq_sum_repr bK
      (algebraMap B (FractionRing B) x) j
    calc
      ∑ i, algebraMap B (FractionRing B)
          ((bA.repr (x * bA i) j) • c i) =
          algebraMap B (FractionRing B) d *
            ∑ i, bK.repr
                (algebraMap B (FractionRing B) x * bK i) j •
              bK.traceDual i := by
                rw [Finset.mul_sum]
                apply Finset.sum_congr rfl
                intro i hi
                rw [Algebra.smul_def, map_mul, hc]
                have harg : algebraMap B (FractionRing B) x * bK i =
                    algebraMap B (FractionRing B) (x * bA i) := by
                  simp only [bK, Basis.localizationLocalization_apply, map_mul]
                rw [harg]
                simp only [bK, Basis.localizationLocalization_repr_algebraMap]
                simp only [Algebra.smul_def]
                rw [← IsScalarTower.algebraMap_apply A B (FractionRing B),
                  ← IsScalarTower.algebraMap_apply A (FractionRing A)
                    (FractionRing B)]
                ring
      _ = algebraMap B (FractionRing B) d *
          (algebraMap B (FractionRing B) x * bK.traceDual j) := by
            rw [htrace]
      _ = algebraMap B (FractionRing B) x *
          (algebraMap B (FractionRing B) d * bK.traceDual j) := by ring
      _ = algebraMap B (FractionRing B) (x * c j) := by
        rw [map_mul, hc]
  · apply FaithfulSMul.algebraMap_injective B (FractionRing B)
    simp only [e, map_sum, Algebra.TensorProduct.lmul'_apply_tmul,
      map_mul, hc]
    have hsum : ∑ i, bK i * bK.traceDual i = 1 := by
      simpa only [traceSeparabilityElement, map_sum,
        Algebra.TensorProduct.lmul'_apply_tmul] using
        (traceSeparabilityElement_mul
          (K := FractionRing A) (L := FractionRing B) bK)
    calc
      ∑ i, algebraMap B (FractionRing B) (bA i) *
          (algebraMap B (FractionRing B) d * bK.traceDual i) =
          algebraMap B (FractionRing B) d *
            ∑ i, bK i * bK.traceDual i := by
              rw [Finset.mul_sum]
              apply Finset.sum_congr rfl
              intro i hi
              simp only [bK, Basis.localizationLocalization_apply]
              ring
      _ = algebraMap B (FractionRing B) d := by rw [hsum, mul_one]

/-- The trace different is contained in the annihilator of the relative
Kähler differentials. -/
theorem differentIdeal_le_kaehlerDifferentialAnnihilator
    [Module.Free A B] :
    differentIdeal A B ≤ Module.annihilator B Ω[B⁄A] := by
  intro d hd
  let bA := Module.Free.chooseBasis A B
  let := Classical.decEq (Module.Free.ChooseBasisIndex A B)
  exact mem_kaehlerAnnihilator_of_mem_differentIdeal_of_basis bA d hd

/-- In a principal target, a generator of the trace different is also a
Kähler-annihilating scalar.  This applies to a localized DVR whenever the
localized extension is finite free. -/
theorem exists_differentIdeal_generator_mem_kaehlerAnnihilator
    [Module.Free A B] [IsPrincipalIdealRing B] :
    ∃ c : B, Ideal.span {c} = differentIdeal A B ∧
      c ∈ Module.annihilator B Ω[B⁄A] := by
  let c : B := Submodule.IsPrincipal.generator (differentIdeal A B)
  refine ⟨c, Ideal.span_singleton_generator _, ?_⟩
  exact differentIdeal_le_kaehlerDifferentialAnnihilator
    (Submodule.IsPrincipal.generator_mem (differentIdeal A B))

end CanonicalDifferent

end

end BGS.CorvajaZannier
