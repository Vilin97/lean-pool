/-
Copyright (c) 2026 Christopher Albert. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Albert
-/

module

public import Mathlib.RingTheory.Support
public import Mathlib.RingTheory.Noetherian.Orzech


/-!
# Kernel support is contained in cokernel support

The only input is the Hopfian property of a finite module over a commutative
Noetherian ring.  The proof is deliberately made at a prime, using the
actual `LocalizedModule` support definition.
-/

@[expose] public section

namespace AlgebraicAnalysis

theorem endomorphism_kernel_support_subset_cokernel_support
    {R E : Type*} [CommRing R] [AddCommGroup E] [Module R E]
    [IsNoetherianRing R] [Module.Finite R E] (f : Module.End R E) :
    Module.support R (LinearMap.ker f) ⊆
      Module.support R (E ⧸ LinearMap.range f) := by
  intro p hp
  rw [Module.mem_support_iff'] at hp ⊢
  by_contra h
  have hnot : p ∉ Module.support R (E ⧸ LinearMap.range f) := by
    rw [Module.mem_support_iff']
    exact h
  have h := Module.notMem_support_iff.mp hnot
  have hsurj : Function.Surjective
      (LocalizedModule.map p.asIdeal.primeCompl f) :=
    (LinearMap.localizedMap_surjective_iff_subsingleton_localized_coker
      p.asIdeal.primeCompl f).2 h
  let : IsNoetherian (Localization p.asIdeal.primeCompl)
      (LocalizedModule p.asIdeal.primeCompl E) := by infer_instance
  have hinj : Function.Injective
      (LocalizedModule.map p.asIdeal.primeCompl f) :=
    IsNoetherian.injective_of_surjective_endomorphism _ hsurj
  obtain ⟨x, hx⟩ := hp
  let x' : LocalizedModule p.asIdeal.primeCompl E :=
    LocalizedModule.mk x.1 1
  have hxzero : x' = 0 := by
    apply hinj
    dsimp [x']
    rw [LocalizedModule.map_mk]
    simp [LinearMap.mem_ker.mp x.2]
  have hxzero' :
      IsLocalizedModule.mk' (LocalizedModule.mkLinearMap p.asIdeal.primeCompl E)
        x.1 (1 : p.asIdeal.primeCompl) = 0 := by
    rw [← IsLocalizedModule.mk_eq_mk']
    exact hxzero
  obtain ⟨s, hs⟩ :=
    (IsLocalizedModule.mk'_eq_zero'
      (LocalizedModule.mkLinearMap p.asIdeal.primeCompl E) (1 : p.asIdeal.primeCompl)).mp
      hxzero'
  have hs' : (s.1 : R) • x = 0 := by
    apply Subtype.ext
    exact hs
  exact hx s.1 s.2 hs'

end AlgebraicAnalysis
