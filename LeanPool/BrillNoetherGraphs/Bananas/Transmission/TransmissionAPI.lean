/-
Copyright (c) 2026 Nathan Pflueger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nathan Pflueger
-/
module


public import LeanPool.BrillNoetherGraphs.Bananas.Transmission.TransmissionBasics
public import LeanPool.BrillNoetherGraphs.Bananas.CrossOneOff.AffineInversionFinite
public import LeanPool.BrillNoetherGraphs.Bananas.SameStrand.EndpointInversions
public import LeanPool.BrillNoetherGraphs.Bananas.Basics.BananaGeometry

/-!
# Reusable transmission API checks

This file is deliberately disjoint from `Statements.lean`.  It records the
mechanical consequences of the present contracts, and separates those from
the geometric/non-recurrence input used by the evenly-marked theta theorem.
-/

@[expose] public section

namespace Bananas

open Utilities

/-! ## The present torsion contract is not an exact-order contract

Paper sources: `def-EA` / `def-tauD` and the exact-order implication
`lem:kgtImpliesTorsionOrder`.
-/

/-- A torsion witness propagates to every positive multiple of its period.

This is intentionally stated for the current `TorsionWitness` definition:
it proves that the predicate records an annihilating period, not minimality.
-/
theorem torsionWitness_of_dvd
    {M : TwiceMarked} {k m : ℕ}
    (hk : TorsionWitness M k) (hkm : k ∣ m) (hm : 0 < m) :
    TorsionWitness M m := by
  rcases hk with ⟨hkpos, hkEq⟩
  obtain ⟨q, rfl⟩ := hkm
  have hqpos : 0 < q := by
    by_contra hq
    have : q = 0 := Nat.eq_zero_of_not_pos hq
    subst q
    simp at hm
  refine ⟨by positivity, ?_⟩
  unfold linearEquiv at hkEq ⊢
  have hmul :
      ((k * q : ℕ) : ℤ) • (oneChip M.u - oneChip M.v) =
        (q : ℤ) • ((k : ℤ) • (oneChip M.u - oneChip M.v)) := by
    push_cast
    rw [smul_smul]
    ring
  rw [hmul]
  simpa [smul_smul] using AddSubgroup.zsmul_mem _ hkEq (q : ℤ)

/-- In particular, the diagonal marking has a witness at every positive
period.  This exposes why distinctness and minimality cannot be inferred
from `TorsionWitness` alone.
-/
theorem torsionWitness_diagonal (G : CFGraph) (u : G.V) {k : ℕ}
    (hk : 0 < k) :
    TorsionWitness (mark G u u) k := by
  refine ⟨hk, ?_⟩
  unfold linearEquiv
  change (0 : CFDiv G) - (k : ℤ) • (oneChip u - oneChip u) ∈
    principalDivisors G
  have hzero : (0 : CFDiv G) - (k : ℤ) •
      (oneChip u - oneChip u) = 0 := by simp
  rw [hzero]
  exact AddSubgroup.zero_mem (principalDivisors G)

/-- `IsTorsionOrder` is the missing minimality wrapper around a witness. -/
theorem isTorsionOrder_iff_minimalWitness
    {M : TwiceMarked} {k : ℕ} :
    IsTorsionOrder M k ↔
      TorsionWitness M k ∧
        ∀ m : ℕ, 0 < m → TorsionWitness M m → k ≤ m := by
  constructor
  · intro h
    exact ⟨h.1, fun m _ hm => h.2 m hm⟩
  · rintro ⟨hk, hmin⟩
    exact ⟨hk, fun m hm => hmin m hm.1 hm⟩

/-! ## Affine transmission consequences -/

/-- The finiteness conjunct in `KGeneralTransmission` is automatic once its
positive witness and affine-period conjunct are available. -/
theorem kInversions_finite_of_torsionWitness_and_isKAffine
    {M : TwiceMarked} {k : ℕ} {τ : ℤ → ℤ}
    (hk : TorsionWitness M k) (hAffine : IsKAffine k τ) :
    (kInversions k τ).Finite := by
  exact kInversions_finite_of_isKAffine hk.1 hAffine

/-- Paper source: `def-tauD` and `def-inv`.

A `KGeneralTransmission` package contains, for every divisor, an affine
transmission permutation with the expected inversion bound.  The finite-set
field is reconstructed from the other fields, so downstream APIs need not
carry it as an independent hypothesis.
-/
theorem KGeneralTransmission.exists_affine_transmission
    {M : TwiceMarked} {k : ℕ}
    (hK : KGeneralTransmission M k) (D : CFDiv M.graph) :
    ∃ τ : ℤ → ℤ,
      IsTransmissionPermutation M D τ ∧ IsKAffine k τ ∧
        kInversionCount k τ ≤ Int.toNat (genus M.graph) := by
  rcases hK with ⟨hk, _hsub, hD⟩
  obtain ⟨τ, hτ, hAffine, _hfinite, hCount⟩ := hD D
  exact ⟨τ, hτ, hAffine, hCount⟩

/-- Paper source: the contract used in `def-EA` and `def-inv`.

Equivalent presentation of the current `KGeneralTransmission` contract
with the automatically generated finiteness conjunct omitted. -/
theorem KGeneralTransmission_iff_without_finiteness
    {M : TwiceMarked} {k : ℕ} :
    KGeneralTransmission M k ↔
      TorsionWitness M k ∧ AllSubmodular M ∧
        ∀ D : CFDiv M.graph, ∃ τ : ℤ → ℤ,
          IsTransmissionPermutation M D τ ∧ IsKAffine k τ ∧
            kInversionCount k τ ≤ Int.toNat (genus M.graph) := by
  constructor
  · intro hK
    rcases hK with ⟨hk, hsub, hAll⟩
    refine ⟨hk, hsub, ?_⟩
    intro D
    obtain ⟨τ, hτ, hAffine, _hfinite, hCount⟩ := hAll D
    exact ⟨τ, hτ, hAffine, hCount⟩
  · rintro ⟨hk, hsub, hAll⟩
    refine ⟨hk, hsub, ?_⟩
    intro D
    obtain ⟨τ, hτ, hAffine, hCount⟩ := hAll D
    exact ⟨τ, hτ, hAffine,
      kInversions_finite_of_torsionWitness_and_isKAffine hk hAffine,
      hCount⟩

/-- On a connected graph, the converse affine construction is available for
each submodular divisor from a torsion witness.  This is the mechanical
transmission step needed before any theta-specific inversion count. -/
theorem exists_affine_transmission_of_allSubmodular
    {M : TwiceMarked} (hconn : _root_.graphConnected M.graph)
    {k : ℕ} (hk : TorsionWitness M k) (hsub : AllSubmodular M)
    (D : CFDiv M.graph) :
    ∃ τ : ℤ → ℤ,
      IsTransmissionPermutation M D τ ∧ IsKAffine k τ ∧
        (kInversions k τ).Finite := by
  have hD : Submodular M D := hsub D
  obtain ⟨τ, hτ, hAffine⟩ :=
    exists_affineTransmissionPermutation_of_submodular M D hconn hD hk
  exact ⟨τ, hτ, hAffine,
    kInversions_finite_of_torsionWitness_and_isKAffine hk hAffine⟩

/-! ## Exact contract boundary -/

/-- The current definition of `KGeneralTransmission` does not by itself
expose an `IsTorsionOrder` result.  This is a deliberately explicit boundary:
the paper's exact-order lemma needs a separate proof using the rank/inversion
count at `D = 0`, not a definitional simplification of this predicate.
-/
theorem KGeneralTransmission.to_torsionWitness
    {M : TwiceMarked} {k : ℕ} :
    KGeneralTransmission M k → TorsionWitness M k := by
  intro hK
  exact hK.1

/-! ## Negative rank-difference obstruction -/

/-- A single negative marked second difference rules out `k`-general
transmission, independently of the period and inversion-count clauses. -/
theorem not_kGeneralTransmission_of_negative_rankDelta
    (M : TwiceMarked) (k : ℕ)
    (hNeg : ∃ D : CFDiv M.graph, rankDelta M D < 0) :
    ¬ KGeneralTransmission M k := by
  intro hK
  obtain ⟨D, hD⟩ := hNeg
  have hNonneg := hK.2.1 D 0 0
  have hNonneg' : 0 ≤ rankDelta M D := by
    simpa [twist] using hNonneg
  exact (not_lt_of_ge hNonneg') hD

end Bananas
