/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/
module


public import Mathlib.FieldTheory.Galois.Abelian
public import Mathlib.NumberTheory.Cyclotomic.Basic
public import LeanPool.ClassFieldTheory.ClassFieldTheory.AbstractClassFieldTheory.Reciprocity.FiniteAbelianClassification
public import LeanPool.ClassFieldTheory.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.ConcreteReciprocityTransport
public import LeanPool.ClassFieldTheory.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.LocalClassFieldAxiom
public import LeanPool.ClassFieldTheory.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.TopologicalReciprocity
public import LeanPool.ClassFieldTheory.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.StandardOpenSubgroups
public import LeanPool.ClassFieldTheory.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.NormSubgroupFunctoriality
public import LeanPool.ClassFieldTheory.ClassFieldTheory.LocalClassFieldTheory.Finite.Existence.OrderReversal
public import LeanPool.ClassFieldTheory.ClassFieldTheory.LocalClassFieldTheory.Finite.CyclotomicNorm.PrincipalUnits
public import LeanPool.ClassFieldTheory.ClassFieldTheory.LocalClassFieldTheory.Finite.CyclotomicNorm.StandardSubgroup
public import LeanPool.ClassFieldTheory.ClassFieldTheory.LocalClassFieldTheory.Finite.CyclotomicNorm.Unramified
public import LeanPool.ClassFieldTheory.GaloisCohomology.Kummer.Concrete.CyclotomicField
public import LeanPool.ClassFieldTheory.ValuedFieldTheory.Ramification.HilbertRamification.PadicLocalization
/-!
# Local cyclotomic embeddings for the global construction

This module proves local Kronecker--Weber through norm-subgroup order reversal,
then applies it to localizations of finite abelian extensions of `ℚ`.
-/

@[expose] public section

noncomputable section

namespace KroneckerWeber

open LocalFieldTheory RamificationTheory CyclicCohomology KummerTheory
open ClassFormation LocalClassFieldTheory
open LocalFieldTheory.Padic

/-- The ramified cyclotomic branch of local Kronecker–Weber.  When the chosen
prime element `p` is already a norm from `L`, the ramified realization theorem realizes the
principal-unit depth furnished by openness as an actual `p`-power
cyclotomic extension.  Order reversal then embeds `L` into that extension.

The extra norm condition is exactly what excludes the nontrivial unramified
part; the general construction also adjoins roots of
unity of order `p ^ f - 1`. -/
theorem exists_pPowerCyclotomicEmbedding_of_padicPrime_mem_normSubgroup
    (p : ℕ) [Fact p.Prime]
    (L : Type) [Field L] [Algebra ℚ_[p] L]
    [FiniteDimensional ℚ_[p] L] [IsAbelianGalois ℚ_[p] L]
    (hpNorm : padicPrimeUnit p ∈ localNormSubgroup ℚ_[p] L) :
    ∃ n : ℕ, 1 ≤ n ∧
      ∃ ζ : CyclotomicField (p ^ n) ℚ_[p],
        IsPrimitiveRoot ζ (p ^ n) ∧
          Algebra.adjoin ℚ_[p] ({ζ} : Set _) = ⊤ ∧
          Nonempty (L →ₐ[ℚ_[p]] CyclotomicField (p ^ n) ℚ_[p]) := by
  let : IsNonarchimedeanLocalField ℚ_[p] :=
    { toIsValuativeTopology := padicIsValuativeTopology p
      toLocallyCompactSpace := inferInstance
      toIsNontrivial := inferInstance }
  obtain ⟨n, hn, hprincipal⟩ :=
    exists_uniformizerPrincipalSubgroup_one_le_normSubgroup
      ℚ_[p] L (padicPrimeUnit p) hpNorm
  have hpnpos : 0 < p ^ n := pow_pos (Fact.out : Nat.Prime p).pos n
  let : NeZero (p ^ n) := ⟨Nat.ne_of_gt hpnpos⟩
  let C := CyclotomicField (p ^ n) ℚ_[p]
  let : IsCyclotomicExtension {p ^ n} ℚ_[p] C :=
    CyclotomicField.isCyclotomicExtension (p ^ n) ℚ_[p]
  let : FiniteDimensional ℚ_[p] C :=
    IsCyclotomicExtension.finiteDimensional {p ^ n} ℚ_[p] C
  let : IsAbelianGalois ℚ_[p] C :=
    IsCyclotomicExtension.isAbelianGalois {p ^ n} ℚ_[p] C
  obtain ⟨ζ, hζ, hgen⟩ :=
    exists_primitiveRoot_adjoin_eq_top_cyclotomicField ℚ_[p] (p ^ n) hpnpos
  have hnsub : n - 1 + 1 = n := Nat.sub_add_cancel hn
  have hζ' : IsPrimitiveRoot ζ (p ^ (n - 1 + 1)) := by
    simpa [hnsub] using hζ
  have hnorm : localNormSubgroup ℚ_[p] C =
      LocalFieldTheory.uniformizerPrincipalSubgroup ℚ_[p]
        (padicPrimeUnit p) 1 n := by
    simpa [C, hnsub] using
      (localNormSubgroup_eq_uniformizerPrincipalSubgroup_cyclotomicPrimePower
        p (k := n - 1) ζ hζ' hgen)
  have hnorm_le : localNormSubgroup ℚ_[p] C ≤ localNormSubgroup ℚ_[p] L := by
    rw [hnorm]
    exact hprincipal
  exact ⟨n, hn, ζ, hζ, hgen,
    nonempty_algHom_of_normSubgroup_le ℚ_[p] L C hnorm_le⟩

/-- Structured form of local Kronecker--Weber.  The construction uses the
cyclotomic order
`(p ^ f - 1) * p ^ n`; retaining that form makes its unramified and
`p`-primary ramified factors available to the global proof.

Openness supplies positive `f,n` with `⟨p ^ f⟩ Uⁿ ≤ N(Lˣ)`.  The unramified
cyclotomic theorem realizes `⟨p ^ f⟩ U¹` by the extension of order
`p ^ f - 1`, while the ramified cyclotomic theorem realizes `⟨p⟩ Uⁿ` by the
`p ^ n`-cyclotomic extension.  Their
composite sits in the cyclotomic field of order `(p ^ f - 1) * p ^ n`, and
the norm-subgroup order reversal gives the required embedding. -/
theorem exists_structuredLocalCyclotomicEmbedding
    (p : ℕ) [Fact p.Prime]
    (L : Type) [Field L] [Algebra ℚ_[p] L]
    [FiniteDimensional ℚ_[p] L] [IsAbelianGalois ℚ_[p] L] :
    ∃ f n : ℕ, 0 < f ∧ 1 ≤ n ∧
      ∃ ζ : CyclotomicField ((p ^ f - 1) * p ^ n) ℚ_[p],
        IsPrimitiveRoot ζ ((p ^ f - 1) * p ^ n) ∧
          Algebra.adjoin ℚ_[p] ({ζ} : Set _) = ⊤ ∧
          Nonempty
            (L →ₐ[ℚ_[p]]
              CyclotomicField ((p ^ f - 1) * p ^ n) ℚ_[p]) := by
  let : IsNonarchimedeanLocalField ℚ_[p] :=
    { toIsValuativeTopology := padicIsValuativeTopology p
      toLocallyCompactSpace := inferInstance
      toIsNontrivial := inferInstance }
  obtain ⟨f, n, hf, hn, hprincipal⟩ :=
    exists_uniformizerPrincipalSubgroup_le_normSubgroup
      ℚ_[p] L (padicPrimeUnit p)
  have hpf : 1 < p ^ f :=
    one_lt_pow₀ (Fact.out : Nat.Prime p).one_lt hf.ne'
  have huPos : 0 < p ^ f - 1 := Nat.sub_pos_of_lt hpf
  have hrPos : 0 < p ^ n := pow_pos (Fact.out : Nat.Prime p).pos n
  have hmPos : 0 < (p ^ f - 1) * p ^ n := mul_pos huPos hrPos
  let : NeZero (p ^ f - 1) := ⟨huPos.ne'⟩
  let : NeZero (p ^ n) := ⟨hrPos.ne'⟩
  let : NeZero ((p ^ f - 1) * p ^ n) := ⟨hmPos.ne'⟩
  let U := CyclotomicField (p ^ f - 1) ℚ_[p]
  let C := CyclotomicField (p ^ n) ℚ_[p]
  let D := CyclotomicField ((p ^ f - 1) * p ^ n) ℚ_[p]
  let : IsCyclotomicExtension {p ^ f - 1} ℚ_[p] U :=
    CyclotomicField.isCyclotomicExtension (p ^ f - 1) ℚ_[p]
  let : IsCyclotomicExtension {p ^ n} ℚ_[p] C :=
    CyclotomicField.isCyclotomicExtension (p ^ n) ℚ_[p]
  let : IsCyclotomicExtension {(p ^ f - 1) * p ^ n} ℚ_[p] D :=
    CyclotomicField.isCyclotomicExtension ((p ^ f - 1) * p ^ n) ℚ_[p]
  let : FiniteDimensional ℚ_[p] U :=
    IsCyclotomicExtension.finiteDimensional {p ^ f - 1} ℚ_[p] U
  let : FiniteDimensional ℚ_[p] C :=
    IsCyclotomicExtension.finiteDimensional {p ^ n} ℚ_[p] C
  let : FiniteDimensional ℚ_[p] D :=
    IsCyclotomicExtension.finiteDimensional
      {(p ^ f - 1) * p ^ n} ℚ_[p] D
  let : IsAbelianGalois ℚ_[p] U :=
    IsCyclotomicExtension.isAbelianGalois {p ^ f - 1} ℚ_[p] U
  let : IsAbelianGalois ℚ_[p] C :=
    IsCyclotomicExtension.isAbelianGalois {p ^ n} ℚ_[p] C
  let : IsAbelianGalois ℚ_[p] D :=
    IsCyclotomicExtension.isAbelianGalois
      {(p ^ f - 1) * p ^ n} ℚ_[p] D
  obtain ⟨ζU, hζU, hgenU⟩ :=
    exists_primitiveRoot_adjoin_eq_top_cyclotomicField
      ℚ_[p] (p ^ f - 1) huPos
  obtain ⟨ζC, hζC, hgenC⟩ :=
    exists_primitiveRoot_adjoin_eq_top_cyclotomicField
      ℚ_[p] (p ^ n) hrPos
  obtain ⟨ζD, hζD, hgenD⟩ :=
    exists_primitiveRoot_adjoin_eq_top_cyclotomicField
      ℚ_[p] ((p ^ f - 1) * p ^ n) hmPos
  have hnormU : localNormSubgroup ℚ_[p] U =
      unramifiedNormSubgroup ℚ_[p] f :=
    normSubgroup_eq_unramifiedNormSubgroup_padic_prime_pow_sub_one
      p f hf U hζU hgenU
  have hnsub : n - 1 + 1 = n := Nat.sub_add_cancel hn
  have hζC' : IsPrimitiveRoot ζC (p ^ (n - 1 + 1)) := by
    simpa [hnsub] using hζC
  have hnormC : localNormSubgroup ℚ_[p] C =
      LocalFieldTheory.uniformizerPrincipalSubgroup ℚ_[p]
        (padicPrimeUnit p) 1 n := by
    simpa [C, hnsub] using
      (localNormSubgroup_eq_uniformizerPrincipalSubgroup_cyclotomicPrimePower
        p (k := n - 1) ζC hζC' hgenC)
  obtain ⟨iU⟩ := nonempty_algHom_cyclotomicField_of_dvd
    ℚ_[p] (p ^ f - 1) ((p ^ f - 1) * p ^ n)
      huPos hmPos (dvd_mul_right _ _)
  obtain ⟨iC⟩ := nonempty_algHom_cyclotomicField_of_dvd
    ℚ_[p] (p ^ n) ((p ^ f - 1) * p ^ n)
      hrPos hmPos (dvd_mul_left _ _)
  have hnormD_U : localNormSubgroup ℚ_[p] D ≤ localNormSubgroup ℚ_[p] U :=
    LocalFieldTheory.normSubgroup_le_of_algHom ℚ_[p] U D iU
  have hnormD_C : localNormSubgroup ℚ_[p] D ≤ localNormSubgroup ℚ_[p] C :=
    LocalFieldTheory.normSubgroup_le_of_algHom ℚ_[p] C D iC
  have hnormD_inf : localNormSubgroup ℚ_[p] D ≤
      unramifiedNormSubgroup ℚ_[p] f ⊓
        LocalFieldTheory.uniformizerPrincipalSubgroup ℚ_[p]
          (padicPrimeUnit p) 1 n := by
    rw [← hnormU, ← hnormC]
    exact le_inf hnormD_U hnormD_C
  have hnormD_L : localNormSubgroup ℚ_[p] D ≤ localNormSubgroup ℚ_[p] L :=
    (hnormD_inf.trans
      (unramifiedNormSubgroup_inf_padicPrincipalSubgroup_le p f n)).trans
        hprincipal
  exact ⟨f, n, hf, hn, ζD, hζD, hgenD,
    nonempty_algHom_of_normSubgroup_le ℚ_[p] L D hnormD_L⟩

/-- Local Kronecker--Weber: every finite abelian
extension of `ℚ_p` embeds in a cyclotomic extension. -/
theorem exists_localCyclotomicEmbedding
    (p : ℕ) [Fact p.Prime]
    (L : Type) [Field L] [Algebra ℚ_[p] L]
    [FiniteDimensional ℚ_[p] L] [IsAbelianGalois ℚ_[p] L] :
    ∃ m : ℕ, 0 < m ∧
      ∃ ζ : CyclotomicField m ℚ_[p],
        IsPrimitiveRoot ζ m ∧
          Algebra.adjoin ℚ_[p] ({ζ} : Set _) = ⊤ ∧
          Nonempty (L →ₐ[ℚ_[p]] CyclotomicField m ℚ_[p]) := by
  obtain ⟨f, n, hf, _hn, ζ, hζ, hgen, hi⟩ :=
    exists_structuredLocalCyclotomicEmbedding p L
  have hpf : 1 < p ^ f :=
    one_lt_pow₀ (Fact.out : Nat.Prime p).one_lt hf.ne'
  have huPos : 0 < p ^ f - 1 := Nat.sub_pos_of_lt hpf
  have hpPowPos : 0 < p ^ n := pow_pos (Fact.out : Nat.Prime p).pos n
  exact ⟨(p ^ f - 1) * p ^ n, mul_pos huPos hpPowPos,
    ζ, hζ, hgen, hi⟩

end KroneckerWeber

end

noncomputable section

namespace KroneckerWeber

open AlgebraicNumberTheory.Valuations
open HilbertRamification

variable (p : ℕ) [Fact p.Prime]
variable (L : Type) [Field L] [Algebra ℚ L]
  [FiniteDimensional ℚ L] [IsAbelianGalois ℚ L]

/-- The type of actual embeddings of the localization at `w`
into the `m`-th cyclotomic extension of `ℚ_p`.  Naming this type exposes an
embedding as a genuine theorem input while keeping all transported algebra
instances internal. -/
noncomputable def globalPadicLocalizationCyclotomicAlgHom
    (w : AbsoluteValueExtension (Rat.AbsoluteValue.padic p) L)
    (m : ℕ) : Type := by
  let vK := Rat.AbsoluteValue.padic p
  letI hK := AbsoluteValue.extensionCompletionAlgebra (K := ℚ) w.1
  letI : SMul ℚ w.1.Completion := hK.toSMul
  letI := AbsoluteValue.completionAlgebra vK w.1 w.2
  let E := AbsoluteValue.algebraicLocalization vK w.1 w.2
  letI hE : Field E := inferInstance
  letI hBaseE : Algebra vK.Completion E := inferInstance
  let e := padicAbsoluteValueCompletionRingEquiv p
  letI : Algebra ℚ_[p] E :=
    @transportedAlgebraAlongRingEquiv vK.Completion ℚ_[p] E _ _
      (@CommRing.toCommSemiring E hE.toCommRing) hBaseE e
  exact E →ₐ[ℚ_[p]] CyclotomicField m ℚ_[p]

/-- Structured version of the local cyclotomic-embedding assertion.  It
retains the prime-to-`p` unramified order `p ^ f - 1` and the ramified order
`p ^ n` from the local cyclotomic construction. -/
noncomputable def globalPadicLocalizationStructuredCyclotomicEmbeddingProperty
    (w : AbsoluteValueExtension (Rat.AbsoluteValue.padic p) L) : Prop := by
  let vK := Rat.AbsoluteValue.padic p
  letI hK := AbsoluteValue.extensionCompletionAlgebra (K := ℚ) w.1
  letI : SMul ℚ w.1.Completion := hK.toSMul
  letI := AbsoluteValue.completionAlgebra vK w.1 w.2
  let E := AbsoluteValue.algebraicLocalization vK w.1 w.2
  letI hE : Field E := inferInstance
  letI hBaseE : Algebra vK.Completion E := inferInstance
  let e := padicAbsoluteValueCompletionRingEquiv p
  letI hQpE : Algebra ℚ_[p] E :=
    @transportedAlgebraAlongRingEquiv vK.Completion ℚ_[p] E _ _
      (@CommRing.toCommSemiring E hE.toCommRing) hBaseE e
  exact ∃ f n : ℕ, 0 < f ∧ 1 ≤ n ∧
    Nonempty
      (E →ₐ[ℚ_[p]]
        CyclotomicField ((p ^ f - 1) * p ^ n) ℚ_[p])

/-- The local completion of a finite abelian extension of `ℚ`, transported
to the concrete base `ℚ_[p]`, embeds in a cyclotomic extension.

This is the local cyclotomic input to the global construction.  It
does not yet assert that the local embeddings for the finitely many ramified
primes glue into one global cyclotomic field. -/
theorem globalPadicLocalization_structuredCyclotomicEmbedding
    (w : AbsoluteValueExtension (Rat.AbsoluteValue.padic p) L) :
    globalPadicLocalizationStructuredCyclotomicEmbeddingProperty p L w := by
  let vK := Rat.AbsoluteValue.padic p
  let hK := AbsoluteValue.extensionCompletionAlgebra (K := ℚ) w.1
  let : SMul ℚ w.1.Completion := hK.toSMul
  let := AbsoluteValue.completionAlgebra vK w.1 w.2
  let E := AbsoluteValue.algebraicLocalization vK w.1 w.2
  let hE : Field E := inferInstance
  let hBaseE : Algebra vK.Completion E := inferInstance
  let e := padicAbsoluteValueCompletionRingEquiv p
  let hQpE : Algebra ℚ_[p] E :=
    @transportedAlgebraAlongRingEquiv vK.Completion ℚ_[p] E _ _
      (@CommRing.toCommSemiring E hE.toCommRing) hBaseE e
  change ∃ f n : ℕ, 0 < f ∧ 1 ≤ n ∧
    Nonempty
      (E →ₐ[ℚ_[p]]
        CyclotomicField ((p ^ f - 1) * p ^ n) ℚ_[p])
  let : Module.Finite vK.Completion E :=
    globalPadicLocalizationModuleFinite p L w
  let : IsAbelianGalois vK.Completion E :=
    globalPadicLocalization_isAbelianGalois p L w
  let : Algebra ℚ_[p] vK.Completion := e.symm.toRingHom.toAlgebra
  let : IsScalarTower ℚ_[p] vK.Completion E :=
    IsScalarTower.of_algebraMap_eq' (by
      ext x
      exact transportedAlgebraAlongRingEquiv_algebraMap e x)
  let : Module.Finite ℚ_[p] vK.Completion :=
    FiniteDimensional.of_surjective
      (Algebra.linearMap ℚ_[p] vK.Completion) e.symm.surjective
  let : Module.Finite ℚ_[p] E :=
    Module.Finite.trans vK.Completion E
  let : IsGalois ℚ_[p] E := by
    apply IsGalois.of_equiv_equiv
      (F := vK.Completion) (E := E) (M := ℚ_[p]) (N := E)
      (f := e) (g := RingEquiv.refl E)
    apply RingHom.ext
    intro x
    simp only [RingHom.comp_apply]
    change
      (@algebraMap ℚ_[p] E _ hE.toSemiring
        hQpE) (e x) =
      (@algebraMap vK.Completion E _
        hE.toSemiring hBaseE) x
    change
      (@algebraMap vK.Completion E _
        hE.toSemiring hBaseE) (e.symm (e x)) =
      (@algebraMap vK.Completion E _
        hE.toSemiring hBaseE) x
    rw [e.symm_apply_apply]
  let liftToCompletedBase :
      (E ≃ₐ[ℚ_[p]] E) → (E ≃ₐ[vK.Completion] E) := fun σ ↦
    { __ := σ.toRingEquiv
      commutes' := fun x ↦ by
        obtain ⟨q, rfl⟩ := e.symm.surjective x
        change
          σ (@algebraMap ℚ_[p] E _ hE.toSemiring hQpE q) =
            @algebraMap ℚ_[p] E _ hE.toSemiring hQpE q
        exact σ.commutes q }
  let : IsAbelianGalois ℚ_[p] E :=
    { is_comm.comm := fun σ τ ↦
        AlgEquiv.ext fun x ↦ by
          have h := DFunLike.congr_fun
            ((inferInstance :
              IsMulCommutative
                (E ≃ₐ[vK.Completion] E)).is_comm.comm
                  (liftToCompletedBase σ) (liftToCompletedBase τ)) x
          simpa [liftToCompletedBase] using h }
  obtain ⟨f, n, hf, hn, _ζ, _hζ, _hadjoin, hEmbedding⟩ :=
    exists_structuredLocalCyclotomicEmbedding p E
  exact ⟨f, n, hf, hn, hEmbedding⟩

end KroneckerWeber
