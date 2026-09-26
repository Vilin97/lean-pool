/-
Copyright (c) 2026 Christopher Albert. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Albert
-/

module

public import LeanPool.Stafford38.AlgebraicAnalysis.Module.PrincipalKoszulSupportOverBase
public import Mathlib.RingTheory.Support


/-!
# Principal Koszul positivity from minimal support

The support primes used by the strict length argument are produced from the
finite `C`-module itself.  In particular, no finiteness of `E` over the base
ring `R` is needed.
-/

@[expose] public section

namespace AlgebraicAnalysis.PrincipalKoszulMinimalSupportPositivity

open AlgebraicAnalysis.PrincipalKoszulSupportOverBase

noncomputable section

universe u v w

variable {R : Type u} {C : Type v} {E : Type w}
variable [CommRing R] [CommRing C] [Algebra R C]
variable [AddCommGroup E] [Module C E] [Module R E]
variable [IsScalarTower R C E]

/-- Minimal support primes of `E` produce the ordered support pair needed by
the principal Koszul positivity argument. -/
theorem length_cokernel_gt_kernel_of_minimal_support
    [IsNoetherianRing C] [Module.Finite C E]
    (x : C)
    (hmin : ∀ p ∈ (Module.annihilator C E).minimalPrimes,
      x ∉ p)
    (hnonzero : Nontrivial (QuotSMulTop x E))
    (hfinite : IsFiniteLength R
      (LinearMap.ker ((LinearMap.lsmul C E x).restrictScalars R))) :
    Module.length R (E ⧸ LinearMap.range ((LinearMap.lsmul C E x).restrictScalars R)) >
      Module.length R (LinearMap.ker ((LinearMap.lsmul C E x).restrictScalars R)) := by
  have : Nontrivial (QuotSMulTop x E) := hnonzero
  obtain ⟨q, hqquot⟩ := Module.nonempty_support_of_nontrivial
    (R := C) (M := QuotSMulTop x E)
  have hq := hqquot
  rw [Module.support_quotSMulTop] at hq
  have hqE : q ∈ Module.support C E := hq.1
  have han : Module.annihilator C E ≤ q.asIdeal :=
    Module.mem_support_iff_of_finite.mp hqE
  obtain ⟨p, hpmin, hpq⟩ :=
    Ideal.exists_minimalPrimes_le (I := Module.annihilator C E)
      (J := q.asIdeal) han
  let p' : PrimeSpectrum C := ⟨p, hpmin.1.1⟩
  have hp' : p' ∈ Module.support C E :=
    Module.mem_support_iff_of_finite.mpr hpmin.1.2
  have hpq' : p' ≤ q := hpq
  have hxp : x ∉ p'.asIdeal := by
    exact hmin p hpmin
  exact length_cokernel_gt_kernel_of_support_over_base
    x p' q hp' hpq' hxp hqquot hfinite


end
end AlgebraicAnalysis.PrincipalKoszulMinimalSupportPositivity
