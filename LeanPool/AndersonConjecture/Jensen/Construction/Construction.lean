/-
Copyright (c) 2026 FrenzyMath. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: FrenzyMath
-/
module

public import LeanPool.AndersonConjecture.Jensen.Defs
public import Mathlib.RingTheory.Ideal.Height
public import Mathlib.RingTheory.Regular.RegularSequence
import LeanPool.AndersonConjecture.Jensen.Construction.HeitmannProp
import LeanPool.AndersonConjecture.Jensen.Construction.Transfinite
import Mathlib.Analysis.Normed.Group.Basic
import Mathlib.CategoryTheory.Category.Init
import Mathlib.Data.EReal.Operations
import Mathlib.Topology.Algebra.InfiniteSum.Order
import Mathlib.Topology.MetricSpace.Bounded

/-!
# The Main Transfinite Construction

An ordinal-indexed chain of A-extensions whose union satisfies
Heitmann's Proposition 1 (surjectivity onto T/M² and ideal
contraction), yielding a Noetherian local domain with prescribed
completion (Jensen, 2006, Corollary 2.4).
-/

@[expose] public section

universe u

noncomputable section

open Cardinal Ideal

variable {T : Type u} [CommRing T] [IsLocalRing T] [IsNoetherianRing T] [IsDomain T]

/-- Jensen's Corollary 2.4 for P = (0), uncountable version:
Given T a complete local domain with depth ≥ 2, |T/M| = |T|, ℵ₀ < |T|, char 0,
there exists a local UFD A with Â ≅ T and trivial generic formal fiber.

This version uses the cardinal bound `ℵ₀ < #T` instead of countability. -/
private def jensen_construction_p0_uncountable_proof
    [IsAdicComplete (IsLocalRing.maximalIdeal T) T]
    (hdepth : ∃ (a b : T), a ∈ IsLocalRing.maximalIdeal T ∧
      b ∈ IsLocalRing.maximalIdeal T ∧
      RingTheory.Sequence.IsRegular T [a, b])
    (hcard : Cardinal.mk T = Cardinal.mk (IsLocalRing.ResidueField T))
    (hchar : ∀ (n : ℤ), n ≠ 0 → (algebraMap ℤ T n) ≠ 0)
    (hT_aleph0 : Cardinal.aleph0 < Cardinal.mk T)
    (hht : ∀ (P : Ideal T), P.IsPrime → P ≠ IsLocalRing.maximalIdeal T → P.height ≤ 1) : PLift (
    ∃ (A : Type u) (_ : CommRing A) (_ : IsLocalRing A) (_ : IsDomain A)
      (_ : UniqueFactorizationMonoid A) (_ : IsNoetherianRing A),
      Nonempty (AdicCompletion (@IsLocalRing.maximalIdeal A _ _) A ≃+* T) ∧
      @HasTrivialGenericFormalFiber A _ _ ) := ⟨by
  have hM_not_assoc := maximal_not_assoc_of_depth_ge_two hdepth
  have hAss_ht := assoc_height_le_one_of_domain hdepth hht
  -- Run the transfinite construction to obtain A ⊆ T with surjectivity, closure, and prime data
  obtain ⟨A, hA_surj, hA_closed, hA_primes⟩ :=
    transfinite_construction hdepth hcard hchar hM_not_assoc hAss_ht hT_aleph0
  obtain ⟨hA_noeth, φ_equiv, hφ_compat⟩ := heitmann_prop1 A.carrier hA_surj hA_closed
  have hA_tgff : @HasTrivialGenericFormalFiber A.carrier _ _ := by
    intro P hP hP_comap
    by_contra hP_ne
    set Q := P.map φ_equiv.toRingHom
    have : Q.IsPrime := Ideal.map_isPrime_of_equiv φ_equiv
    have hQ_ne : Q ≠ ⊥ :=
      (Ideal.map_eq_bot_iff_of_injective φ_equiv.injective).not.mpr hP_ne
    -- Every nonzero prime of T meets A, so its pullback cannot lie over zero.
    obtain ⟨t, ht_mem, ht_ne⟩ := hA_primes Q inferInstance hQ_ne
    have ht_completion : AdicCompletion.of (IsLocalRing.maximalIdeal A.carrier)
        A.carrier t ∈ P := by
      apply (Ideal.apply_mem_of_equiv_iff (f := φ_equiv)).mp
      rw [hφ_compat]
      exact ht_mem
    have ht_bot : t ∈ (⊥ : Ideal A.carrier) :=
      hP_comap ▸ Ideal.mem_comap.mpr ht_completion
    exact ht_ne (congrArg A.carrier.subtype (Ideal.mem_bot.mp ht_bot))
  exact ⟨↥A.carrier, inferInstance, inferInstance, inferInstance, inferInstance,
    hA_noeth, ⟨φ_equiv⟩, hA_tgff⟩
⟩

theorem jensen_construction_p0_uncountable
    [IsAdicComplete (IsLocalRing.maximalIdeal T) T]
    (hdepth : ∃ (a b : T), a ∈ IsLocalRing.maximalIdeal T ∧
      b ∈ IsLocalRing.maximalIdeal T ∧
      RingTheory.Sequence.IsRegular T [a, b])
    (hcard : Cardinal.mk T = Cardinal.mk (IsLocalRing.ResidueField T))
    (hchar : ∀ (n : ℤ), n ≠ 0 → (algebraMap ℤ T n) ≠ 0)
    (hT_aleph0 : Cardinal.aleph0 < Cardinal.mk T)
    (hht : ∀ (P : Ideal T), P.IsPrime → P ≠ IsLocalRing.maximalIdeal T → P.height ≤ 1) :
    ∃ (A : Type u) (_ : CommRing A) (_ : IsLocalRing A) (_ : IsDomain A)
      (_ : UniqueFactorizationMonoid A) (_ : IsNoetherianRing A),
      Nonempty (AdicCompletion (@IsLocalRing.maximalIdeal A _ _) A ≃+* T) ∧
      @HasTrivialGenericFormalFiber A _ _ := by
  exact
    (jensen_construction_p0_uncountable_proof
      hdepth hcard hchar hT_aleph0 hht
    ).down
end
