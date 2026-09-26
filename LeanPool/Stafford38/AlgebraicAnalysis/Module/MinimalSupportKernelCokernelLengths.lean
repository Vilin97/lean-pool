/-
Copyright (c) 2026 Christopher Albert. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Albert
-/

module

public import LeanPool.Stafford38.AlgebraicAnalysis.Module.EndomorphismKernelSupportOverBase
public import LeanPool.Stafford38.AlgebraicAnalysis.Module.MinimalPrimeFiniteLengthLocalization
public import Mathlib.RingTheory.Support


/-!
# Finite length of a localized kernel and cokernel

This is the small commutative-algebra adapter needed when the finite module is
over a larger coefficient algebra.  Finiteness over the base is supplied
explicitly; no restriction-of-scalars finiteness of the ambient module is
used.
-/

@[expose] public section

namespace AlgebraicAnalysis

open scoped Pointwise

noncomputable section

private theorem localized_isFiniteLength_of_minimal_support
    {R N : Type*} [CommRing R] [AddCommGroup N] [Module R N]
    [IsNoetherianRing R] [Module.Finite R N]
    (q : PrimeSpectrum R)
    (hqmem : q ∈ Module.support R N)
    (hq : ∀ p ∈ Module.support R N, p.asIdeal ≤ q.asIdeal →
      q.asIdeal ≤ p.asIdeal) :
    IsFiniteLength (Localization q.asIdeal.primeCompl)
      (LocalizedModule q.asIdeal.primeCompl N) := by
  have hqmem' : q ∈ Module.support R N := hqmem
  have hqmem := hqmem'
  have hmin : q.asIdeal ∈ (Module.annihilator R N).minimalPrimes := by
    obtain ⟨p, hp, hpq⟩ :=
      Ideal.exists_minimalPrimes_le
        (Module.mem_support_iff_of_finite.mp hqmem)
    have hpprime : p.IsPrime := hp.1.1
    let p' : PrimeSpectrum R := ⟨p, hpprime⟩
    have hp'supp : p' ∈ Module.support R N :=
      Module.mem_support_iff_of_finite.mpr hp.1.2
    have hqp : q.asIdeal ≤ p := hq p' hp'supp hpq
    have heq : p = q.asIdeal := le_antisymm hpq hqp
    simpa [heq] using hp
  exact MinimalPrimeFiniteLengthLocalization.localizedModule_isFiniteLength
    q.asIdeal hmin

theorem localized_kernel_and_cokernel_isFiniteLength
    {R C E : Type*} [CommRing R] [CommRing C] [Algebra R C]
    [AddCommGroup E] [Module C E] [Module R E] [IsScalarTower R C E]
    [IsNoetherianRing R] [IsNoetherianRing C] [Module.Finite C E]
    (f : Module.End C E)
    [Module.Finite R (LinearMap.ker (f.restrictScalars R))]
    [Module.Finite R (E ⧸ LinearMap.range (f.restrictScalars R))]
    (q : PrimeSpectrum R)
    (hqmem : q ∈ Module.support R (E ⧸ LinearMap.range (f.restrictScalars R)))
    (hq : ∀ p ∈ Module.support R (E ⧸ LinearMap.range (f.restrictScalars R)),
      p.asIdeal ≤ q.asIdeal → q.asIdeal ≤ p.asIdeal) :
    IsFiniteLength (Localization q.asIdeal.primeCompl)
        (LocalizedModule q.asIdeal.primeCompl
          (E ⧸ LinearMap.range (f.restrictScalars R))) ∧
      IsFiniteLength (Localization q.asIdeal.primeCompl)
        (LocalizedModule q.asIdeal.primeCompl
          (LinearMap.ker (f.restrictScalars R))) := by
  have hc := localized_isFiniteLength_of_minimal_support q hqmem hq
  have hksub :=
    endomorphism_kernel_support_subset_cokernel_support_over_base
      (R := R) (C := C) (E := E) f
  by_cases hk : q ∈ Module.support R (LinearMap.ker (f.restrictScalars R))
  · have hqk : ∀ p ∈ Module.support R (LinearMap.ker (f.restrictScalars R)),
        p.asIdeal ≤ q.asIdeal → q.asIdeal ≤ p.asIdeal := by
      intro p hp hpq
      exact hq p (hksub hp) hpq
    exact ⟨hc, localized_isFiniteLength_of_minimal_support q hk hqk⟩
  · have hsub : Subsingleton (LocalizedModule q.asIdeal.primeCompl
        (LinearMap.ker (f.restrictScalars R))) :=
      not_nontrivial_iff_subsingleton.mp (by
        intro h
        exact hk (Module.mem_support_iff.mpr h))
    let := hsub
    exact ⟨hc, IsFiniteLength.of_subsingleton⟩


end
end AlgebraicAnalysis
