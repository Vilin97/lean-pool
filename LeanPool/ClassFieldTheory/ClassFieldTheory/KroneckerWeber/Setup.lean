/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/

import LeanPool.ClassFieldTheory.ValuedFieldTheory.Valuation.AbsoluteValue.AlgebraicLocalization
import Mathlib.FieldTheory.Galois.GaloisClosure
import Mathlib.NumberTheory.NumberField.Cyclotomic.Basic
import Mathlib.NumberTheory.Padics.HeightOneSpectrum
import LeanPool.ClassFieldTheory.ClassFieldTheory.AlgebraicNumberTheory.FiniteAbelianCompositum
import LeanPool.ClassFieldTheory.ClassFieldTheory.AlgebraicNumberTheory.Ramification.FiniteRamifiedPrimes
import LeanPool.ClassFieldTheory.ClassFieldTheory.KroneckerWeber.LocalCyclotomicEmbedding
import LeanPool.ClassFieldTheory.ValuedFieldTheory.Ramification.HilbertRamification.Dedekind.Basic
/-!
# Setup for the global Kronecker--Weber theorem

This file begins the global Kronecker–Weber construction.
Two finite abelian extensions, embedded in one separable closure, have a
finite abelian compositum.  In particular this applies to the given number
field and a cyclotomic field.  The remaining arithmetic step is to choose the
cyclotomic order from the local data and prove that the compositum has no
larger degree than the cyclotomic subfield.
-/

noncomputable section

namespace KroneckerWeber

open AlgebraicNumberTheory
open HilbertRamification
open HilbertRamification.Dedekind
open scoped IsMulCommutative NumberField

section GlobalConductorCandidate

open AlgebraicNumberTheory.Valuations

variable (L : Type) [Field L]
variable [hNF : NumberField L] [hLab : IsAbelianGalois ℚ L]

include hNF in
/-- The finite set `S` of ramified rational primes,
primes.  A prime belongs to this finset precisely when some height-one prime
of `𝓞 L` above it is ramified. -/
noncomputable def kroneckerWeberRamifiedPrimes : Finset Nat.Primes := by
  let S : Set (IsDedekindDomain.HeightOneSpectrum ℤ) :=
    {v | ∃ w : IsDedekindDomain.HeightOneSpectrum (𝓞 L),
      w.asIdeal.LiesOver v.asIdeal ∧
        ¬ Algebra.IsUnramifiedAt ℤ w.asIdeal}
  have hS : S.Finite :=
    AlgebraicNumberTheory.Ramification.finite_ramified_base_heightOne_primes ℤ (𝓞 L)
  exact hS.toFinset.image Rat.HeightOneSpectrum.primesEquiv

omit hLab in
/-- Membership in the finite ramified-prime set, stated in
height-one-prime language. -/
theorem mem_kroneckerWeberRamifiedPrimes_iff
    (p : Nat.Primes) :
    p ∈ kroneckerWeberRamifiedPrimes (L := L) ↔
      ∃ w : IsDedekindDomain.HeightOneSpectrum (𝓞 L),
        (w.asIdeal : Ideal (𝓞 L)).LiesOver
          ((Rat.HeightOneSpectrum.primesEquiv.symm p).asIdeal : Ideal ℤ) ∧
        ¬ Algebra.IsUnramifiedAt ℤ w.asIdeal := by
  classical
  simp only [kroneckerWeberRamifiedPrimes, Finset.mem_image,
    Set.Finite.mem_toFinset, Set.mem_ofPred_eq]
  constructor
  · rintro ⟨v, hv, rfl⟩
    simpa using hv
  · intro hp
    exact ⟨Rat.HeightOneSpectrum.primesEquiv.symm p, hp,
      Rat.HeightOneSpectrum.primesEquiv.apply_symm_apply p⟩

include hLab in
/-- A chosen extension to `L` of the rational `p`-adic absolute value,
constructed by pulling the absolute value on an algebraic closure of the
completion back along a chosen embedding. -/
noncomputable def kroneckerWeberPadicExtension
    (p : ℕ) [Fact p.Prime] :
  AbsoluteValueExtension (Rat.AbsoluteValue.padic p) L := by
  let vK := Rat.AbsoluteValue.padic p
  letI : Algebra ℚ ℚ := Algebra.id ℚ
  let hWith : Algebra ℚ (WithAbs vK) :=
    WithAbs.instAlgebra _
  let hUniform : UniformContinuousConstSMul ℚ (WithAbs vK) :=
    WithAbs.instUniformContinuousConstSMulReal _
  let hBase : Algebra ℚ vK.Completion :=
    @UniformSpace.Completion.algebra
      (WithAbs vK) _ _ _ _ ℚ _ hWith hUniform
  let hClosure : Algebra ℚ
      (absoluteValueExtension_algebraicCompletionClosure vK) :=
    @AlgebraicClosure.instAlgebra vK.Completion _ ℚ _ hBase
  let : Algebra ℚ vK.Completion := hBase
  let : Algebra ℚ
      (absoluteValueExtension_algebraicCompletionClosure vK) :=
    hClosure
  exact pullbackAbsoluteValueExtension
    vK
    (padicAbsoluteValue_isNontrivial p)
    IsSepClosed.lift

include L hNF hLab in
/-- The concrete local embedding assertion attached to fixed structured
parameters `f` and `n`.  Its named form hides the localization
instances while retaining the actual embedding needed for the ramification
estimate in the global argument. -/
noncomputable def kroneckerWeberLocalCyclotomicEmbeddingProperty
    (p : Nat.Primes) (f n : ℕ) : Prop := by
  letI : Fact p.1.Prime := ⟨p.2⟩
  let w := kroneckerWeberPadicExtension (L := L) p.1
  let vK := Rat.AbsoluteValue.padic p.1
  letI hK := AbsoluteValue.extensionCompletionAlgebra (K := ℚ) w.1
  letI : SMul ℚ w.1.Completion := hK.toSMul
  letI := AbsoluteValue.completionAlgebra vK w.1 w.2
  let E := AbsoluteValue.algebraicLocalization vK w.1 w.2
  letI hE : Field E := inferInstance
  letI hBaseE : Algebra vK.Completion E := inferInstance
  let e := padicAbsoluteValueCompletionRingEquiv p.1
  letI hQpE : Algebra ℚ_[p.1] E :=
    @transportedAlgebraAlongRingEquiv vK.Completion ℚ_[p.1] E _ _
      (@CommRing.toCommSemiring E hE.toCommRing) hBaseE e
  exact Nonempty
    (E →ₐ[ℚ_[p.1]]
      CyclotomicField ((p.1 ^ f - 1) * p.1 ^ n) ℚ_[p.1])

/-- The synchronized local data chosen from structured local
Kronecker--Weber.  In particular, the ramification exponent below and the
embedding used to bound it come from one and the same witness. -/
structure KroneckerWeberLocalCyclotomicData (p : Nat.Primes) where
  /-- The unramified-degree parameter in the local cyclotomic order. -/
  unramifiedDegree : ℕ
  /-- The exponent of the `p`-power factor in the local cyclotomic order. -/
  ramificationExponent : ℕ
  /-- Positivity of the chosen unramified-degree parameter. -/
  unramifiedDegree_pos : 0 < unramifiedDegree
  /-- Positivity of the chosen ramification exponent. -/
  ramificationExponent_pos : 1 ≤ ramificationExponent
  /-- The structured local embedding associated with the two chosen parameters. -/
  embedding : kroneckerWeberLocalCyclotomicEmbeddingProperty
    (L := L) p unramifiedDegree ramificationExponent

include L hNF hLab in
/-- A chosen structured local cyclotomic witness at `p`. -/
noncomputable def kroneckerWeberLocalCyclotomicData
    (p : Nat.Primes) :
    KroneckerWeberLocalCyclotomicData (L := L) p := by
  letI : Fact p.1.Prime := ⟨p.2⟩
  let w := kroneckerWeberPadicExtension (L := L) p.1
  have h := globalPadicLocalization_structuredCyclotomicEmbedding p.1 L w
  dsimp only
    [globalPadicLocalizationStructuredCyclotomicEmbeddingProperty] at h
  let f := Classical.choose h
  let hf := Classical.choose_spec h
  let n := Classical.choose hf
  let hn := Classical.choose_spec hf
  refine ⟨f, n, hn.1, hn.2.1, ?_⟩
  simpa only [kroneckerWeberLocalCyclotomicEmbeddingProperty] using hn.2.2

include L hNF hLab in
/-- The prime-to-`p` residue degree in the chosen structured local
cyclotomic witness. -/
noncomputable def kroneckerWeberLocalUnramifiedDegree
    (p : Nat.Primes) : ℕ :=
  (kroneckerWeberLocalCyclotomicData (L := L) p).unramifiedDegree

include L hNF hLab in
/-- The `p`-power exponent supplied by the structured local
Kronecker--Weber theorem for the chosen completion of `L` at `p`. -/
noncomputable def kroneckerWeberLocalRamificationExponent
    (p : Nat.Primes) : ℕ :=
  (kroneckerWeberLocalCyclotomicData (L := L) p).ramificationExponent

include L hNF in
/-- The chosen prime-to-`p` residue degree is positive. -/
theorem kroneckerWeberLocalUnramifiedDegree_pos
    (p : Nat.Primes) :
    0 < kroneckerWeberLocalUnramifiedDegree (L := L) p :=
  (kroneckerWeberLocalCyclotomicData
    (L := L) p).unramifiedDegree_pos

include L hNF in
/-- The actual local cyclotomic embedding selected together with the two
local exponents. -/
theorem kroneckerWeberLocalCyclotomicEmbedding
    (p : Nat.Primes) :
    kroneckerWeberLocalCyclotomicEmbeddingProperty
      (L := L) p
      (kroneckerWeberLocalUnramifiedDegree (L := L) p)
      (kroneckerWeberLocalRamificationExponent (L := L) p) :=
  (kroneckerWeberLocalCyclotomicData (L := L) p).embedding

include L hNF hLab in
/-- The cyclotomic order `n = ∏_{p ∈ S} p^{e_p}` chosen from the ramification
support. -/
noncomputable def kroneckerWeberConductorCandidate : ℕ :=
  ∏ p ∈ kroneckerWeberRamifiedPrimes (L := L),
    p.1 ^ kroneckerWeberLocalRamificationExponent (L := L) p

include L hNF hLab in
/-- The part of the conductor candidate supported away from `p`. -/
noncomputable def kroneckerWeberConductorCoprimePart
    (p : Nat.Primes) : ℕ :=
  ∏ q ∈ (kroneckerWeberRamifiedPrimes (L := L)).erase p,
    q.1 ^ kroneckerWeberLocalRamificationExponent (L := L) q

include L hNF in
/-- At a ramified prime `p`, the conductor candidate splits into its chosen
`p`-primary order and the product supported at the other ramified primes. -/
theorem kroneckerWeberConductorCandidate_eq_primePower_mul_coprimePart
    (p : Nat.Primes)
    (hp : p ∈ kroneckerWeberRamifiedPrimes (L := L)) :
    kroneckerWeberConductorCandidate (L := L) =
      p.1 ^ kroneckerWeberLocalRamificationExponent (L := L) p *
        kroneckerWeberConductorCoprimePart (L := L) p := by
  classical
  rw [kroneckerWeberConductorCandidate,
    kroneckerWeberConductorCoprimePart]
  exact (Finset.mul_prod_erase _ _ hp).symm

include L hNF in
/-- The complementary factor really is prime to `p`; this is the arithmetic
input which makes it part of the unramified factor in the local cyclotomic
field used in the global construction. -/
theorem kroneckerWeberConductorCoprimePart_coprime
    (p : Nat.Primes) :
    Nat.Coprime p.1
      (kroneckerWeberConductorCoprimePart (L := L) p) := by
  classical
  rw [kroneckerWeberConductorCoprimePart,
    Nat.coprime_prod_right_iff]
  intro q hq
  apply Nat.Coprime.pow_right
  exact (Nat.coprime_primes p.2 q.2).2
    (Subtype.coe_ne_coe.mpr
      (Ne.symm (Finset.ne_of_mem_erase hq)))

include L hNF in
/-- The constructed global cyclotomic order is nonzero. -/
theorem kroneckerWeberConductorCandidate_pos :
    0 < kroneckerWeberConductorCandidate (L := L) := by
  classical
  apply Finset.prod_pos
  intro p hp
  exact pow_pos p.2.pos
    (kroneckerWeberLocalRamificationExponent (L := L) p)

end GlobalConductorCandidate

section GlobalCompositum

open AlgebraicNumberTheory.Valuations

variable (L : Type) [Field L]
variable [hNF : NumberField L] [hLab : IsAbelianGalois ℚ L]

/-- The conductor candidate is nonzero. -/
instance kroneckerWeberConductorCandidate_neZero :
    NeZero (kroneckerWeberConductorCandidate (L := L)) :=
  ⟨(kroneckerWeberConductorCandidate_pos (L := L)).ne'⟩

/-- The cyclotomic field at the conductor candidate is abelian Galois over
the rationals. -/
instance kroneckerWeberCyclotomicField_isAbelianGalois :
    IsAbelianGalois ℚ
      (CyclotomicField (kroneckerWeberConductorCandidate (L := L)) ℚ) :=
  let n := kroneckerWeberConductorCandidate (L := L)
  letI : IsCyclotomicExtension {n} ℚ (CyclotomicField n ℚ) :=
    CyclotomicField.isCyclotomicExtension n ℚ
  IsCyclotomicExtension.isAbelianGalois {n} ℚ _

include L hNF hLab in
/-- The concrete compositum `M = L(μ_n)` in a fixed separable closure of
`ℚ`, for the conductor candidate constructed above. -/
noncomputable def kroneckerWeberCompositumField :
    IntermediateField ℚ (SeparableClosure ℚ) :=
  finiteAbelianCompositumField ℚ L
    (CyclotomicField (kroneckerWeberConductorCandidate (L := L)) ℚ)

/-- The global Kronecker--Weber compositum is finite-dimensional over the
rationals. -/
instance kroneckerWeberCompositumField_finiteDimensional :
    FiniteDimensional ℚ (kroneckerWeberCompositumField L) := by
  change FiniteDimensional ℚ
    (finiteAbelianCompositumField ℚ L
      (CyclotomicField (kroneckerWeberConductorCandidate (L := L)) ℚ))
  infer_instance

/-- The global Kronecker--Weber compositum is abelian Galois over the
rationals. -/
instance kroneckerWeberCompositumField_isAbelianGalois :
    IsAbelianGalois ℚ (kroneckerWeberCompositumField L) := by
  exact finiteAbelianCompositumField_isAbelianGalois ℚ L
    (CyclotomicField (kroneckerWeberConductorCandidate (L := L)) ℚ)

/-- The global Kronecker--Weber compositum is a number field. -/
instance kroneckerWeberCompositumField_numberField :
    NumberField (kroneckerWeberCompositumField L) := ⟨⟩

include L hNF hLab in
/-- The original abelian extension embeds into `M = L(μ_n)`. -/
noncomputable def kroneckerWeberCompositumEmbeddingLeft :
    L →ₐ[ℚ] kroneckerWeberCompositumField L :=
  finiteAbelianCompositumEmbeddingLeft ℚ L
    (CyclotomicField (kroneckerWeberConductorCandidate (L := L)) ℚ)

include L hNF hLab in
/-- The conductor cyclotomic field embeds into `M = L(μ_n)`. -/
noncomputable def kroneckerWeberCompositumEmbeddingRight :
    CyclotomicField (kroneckerWeberConductorCandidate (L := L)) ℚ →ₐ[ℚ]
      kroneckerWeberCompositumField L :=
  finiteAbelianCompositumEmbeddingRight ℚ L
    (CyclotomicField (kroneckerWeberConductorCandidate (L := L)) ℚ)

include L hNF hLab in
/-- The copy of `L` inside the concrete compositum. -/
noncomputable def kroneckerWeberCompositumLeftField :
    IntermediateField ℚ (kroneckerWeberCompositumField L) :=
  (kroneckerWeberCompositumEmbeddingLeft (L := L)).fieldRange

include L hNF hLab in
/-- The chosen copy of `L` in the compositum is canonically isomorphic to
`L`. -/
noncomputable def kroneckerWeberCompositumLeftEquiv :
    L ≃ₐ[ℚ] kroneckerWeberCompositumLeftField (L := L) :=
  AlgEquiv.ofInjectiveField
    (kroneckerWeberCompositumEmbeddingLeft (L := L))

include L hNF hLab in
/-- The elementary lower degree bound for the cyclotomic factor of `M`. -/
theorem kroneckerWeberCyclotomic_finrank_le_compositum :
      Module.finrank ℚ
        (CyclotomicField (kroneckerWeberConductorCandidate (L := L)) ℚ) ≤
      Module.finrank ℚ (kroneckerWeberCompositumField L) :=
  finiteAbelianCompositum_finrank_right_le ℚ L
    (CyclotomicField (kroneckerWeberConductorCandidate (L := L)) ℚ)

include L hNF hLab in
/-- Once the global inertia count supplies the upper degree bound, the
cyclotomic inclusion in `M` is an isomorphism.  This isolates the purely
linear-algebraic final step of the global construction. -/
noncomputable def kroneckerWeberCompositumEquivCyclotomicOfFinrankLe
    (hupper :
      Module.finrank ℚ (kroneckerWeberCompositumField L) ≤
        Nat.totient (kroneckerWeberConductorCandidate (L := L))) :
    kroneckerWeberCompositumField L ≃ₐ[ℚ]
      CyclotomicField (kroneckerWeberConductorCandidate (L := L)) ℚ := by
  let n := kroneckerWeberConductorCandidate (L := L)
  let C := CyclotomicField n ℚ
  let M := kroneckerWeberCompositumField L
  let i : C →ₐ[ℚ] M := kroneckerWeberCompositumEmbeddingRight (L := L)
  letI : IsCyclotomicExtension {n} ℚ C := by
    dsimp only [C]
    exact CyclotomicField.isCyclotomicExtension n ℚ
  have hcyclotomic : Module.finrank ℚ C = Nat.totient n :=
    IsCyclotomicExtension.Rat.finrank n C
  have hCM : Module.finrank ℚ C ≤ Module.finrank ℚ M :=
    kroneckerWeberCyclotomic_finrank_le_compositum (L := L)
  have hMC : Module.finrank ℚ M ≤ Module.finrank ℚ C := by
    rw [hcyclotomic]
    exact hupper
  have hdim : Module.finrank ℚ C = Module.finrank ℚ M :=
    Nat.le_antisymm hCM hMC
  have hiSurjective : Function.Surjective i.toLinearMap :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
      (f := i.toLinearMap) hdim).mp i.injective
  exact (AlgEquiv.ofBijective i ⟨i.injective, hiSurjective⟩).symm

include L hNF hLab in
/-- The promised embedding of `L` into the conductor cyclotomic field,
deduced from the global upper degree bound. -/
noncomputable def kroneckerWeberEmbeddingOfCompositumFinrankLe
    (hupper :
      Module.finrank ℚ (kroneckerWeberCompositumField L) ≤
        Nat.totient (kroneckerWeberConductorCandidate (L := L))) :
    L →ₐ[ℚ]
      CyclotomicField (kroneckerWeberConductorCandidate (L := L)) ℚ :=
  (kroneckerWeberCompositumEquivCyclotomicOfFinrankLe
      (L := L) hupper).toAlgHom.comp
    (kroneckerWeberCompositumEmbeddingLeft (L := L))

include L hNF hLab in
/-- A chosen prime of `M = L(μ_n)` over the rational prime `p`. -/
noncomputable def kroneckerWeberCompositumPrimeAbove
    (p : Nat.Primes) :
    Ideal.primesOver
      ((Rat.HeightOneSpectrum.primesEquiv.symm p).asIdeal : Ideal ℤ)
      (𝓞 (kroneckerWeberCompositumField L)) := by
  letI : ((Rat.HeightOneSpectrum.primesEquiv.symm p).asIdeal :
      Ideal ℤ).IsPrime := by
    infer_instance
  exact Classical.choice (inferInstance : Nonempty
    (Ideal.primesOver
      ((Rat.HeightOneSpectrum.primesEquiv.symm p).asIdeal : Ideal ℤ)
      (𝓞 (kroneckerWeberCompositumField L))))

end GlobalCompositum

end KroneckerWeber

end
