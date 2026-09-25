/-
Copyright (c) 2026 Nathan Pflueger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nathan Pflueger
-/
module


public import LeanPool.BrillNoetherGraphs.Bananas.Examples.MechanicalAPIAudit

/-!
# Bounded mechanical audit: evenly marked theta transmission

This file is intentionally disjoint from `Statements.lean` and all shared
helpers.  It records only reductions that compile from the current API.  In
particular, it is not an attempted proof of the theorem-level gaps.
-/

@[expose] public section

namespace Bananas

open Utilities

/-! ## Exact names exposed by the current library

The following declarations are the complete generic route from a torsion
witness and all-submodularity to affine transmission and finite inversion
support.  Exact torsion for evenly marked theta graphs is now supplied by
`ThetaExactTorsionRelabel`; the generic API supplies no inversion-count bound.
-/

/-! The audit's point is that these API entry points exist with these
shapes.  Stated as anonymous `example`s rather than `#check`s: both are
compile-time checks, but `#check` prints an `info` on every build. -/

example := @torsionWitness_of_dvd
example := @isTorsionOrder_iff_minimalWitness
example := @exists_affine_transmission_of_allSubmodular
example := @kInversions_finite_of_torsionWitness_and_isKAffine
example := @IsKAffine.iterate_nat
example := @IsKAffine.iterate_int
example := @kInversions_finite_of_isKAffine
example := @evenlyMarkedTheta_allSubmodular
example := @evenlyMarkedTheta_affine_existence_audit
example := @evenlyMarkedTheta_kGeneral_of_torsion_and_count

/-! ## Period-two reductions that are available mechanically -/

theorem period_two_first_coordinate
    {τ : ℤ → ℤ} {p : ℤ × ℤ}
    (hp : p ∈ kInversions 2 τ) : p.1 = 0 ∨ p.1 = 1 := by
  rcases hp with ⟨_, _, hp0, hp2⟩
  omega

theorem period_two_value_decomposition
    {τ : ℤ → ℤ} (hτ : IsKAffine 2 τ) (y : ℤ) :
    τ y = τ (y % 2) + (y / 2) * 2 := by
  have hy := IsKAffine.iterate_int hτ (y % 2) (y / 2)
  norm_num at hy
  have hrepr : y = y % 2 + (y / 2) * 2 := by omega
  conv_lhs => rw [hrepr]
  exact hy

theorem period_two_inversion_finiteness
    {M : TwiceMarked} {τ : ℤ → ℤ}
    (hk : TorsionWitness M 2) (hτ : IsKAffine 2 τ) :
    (kInversions 2 τ).Finite := by
  exact kInversions_finite_of_torsionWitness_and_isKAffine hk hτ

/-! ## Reduction of the evenly-marked theorem to the count inequality

Torsion, all-submodularity, existence of an affine transmission permutation,
and finiteness of its inversion set are already unconditional.  Thus the
only theta-specific input still needed is a bound for any affine
transmission permutation produced by the generic API. -/

theorem evenlyMarkedTheta_kGeneral_of_uniform_inversion_bound
    (B : Banana 2) (α β : Fin 3) (i : B.PathPosition α)
    (j : B.PathPosition β)
    (hEven : EvenlyMarkedTheta B α β i j)
    (hBound : ∀ (D : CFDiv B.graph) (τ : ℤ → ℤ),
      IsTransmissionPermutation
          (mark B.graph (strandVertex B α i) (strandVertex B β j)) D τ →
      IsKAffine (B.length α / Nat.gcd (B.length α) i.val) τ →
      kInversionCount (B.length α / Nat.gcd (B.length α) i.val) τ ≤
        Int.toNat (genus B.graph)) :
    KGeneralTransmission
      (mark B.graph (strandVertex B α i) (strandVertex B β j))
      (B.length α / Nat.gcd (B.length α) i.val) := by
  let M := mark B.graph (strandVertex B α i) (strandVertex B β j)
  let k := B.length α / Nat.gcd (B.length α) i.val
  have hk : TorsionWitness M k := by
    dsimp [M, k]
    exact evenlyMarkedTheta_torsion B α β i j hEven
  have hsub : AllSubmodular M := by
    dsimp [M]
    exact evenlyMarkedTheta_allSubmodular B α β i j hEven
  refine ⟨hk, hsub, ?_⟩
  intro D
  obtain ⟨τ, hτ, hAffine, hFinite⟩ :=
    exists_affine_transmission_of_allSubmodular
      (graphConnected B) hk hsub D
  refine ⟨τ, hτ, hAffine, hFinite, ?_⟩
  dsimp [M, k] at hτ hAffine ⊢
  exact hBound D τ hτ hAffine

/-! A witness at period two mechanically propagates to period four; this is
why an exact-order proof must establish minimality separately. -/

theorem period_two_witness_propagates
    {M : TwiceMarked} (hk : TorsionWitness M 2) :
    TorsionWitness M 4 := by
  exact torsionWitness_of_dvd hk (by norm_num) (by norm_num)

/-! The remaining theta-specific ingredient is a genus-sized bound on
`kInversionCount k τ` for every affine transmission permutation.  The exact
torsion witness and its minimality are proved in `ThetaExactTorsionRelabel`;
all-submodularity and affine-transmission existence are already generic.

The paper obtains this bound through its genus-two inversion formula (Lemma
4.10) and nonrecurrence.  Neither has yet been formalized in the current API.
-/

end Bananas
