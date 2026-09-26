/-
Copyright (c) 2026 Nathan Pflueger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nathan Pflueger
-/
module


public import LeanPool.BrillNoetherGraphs.Bananas.SameStrand.EndpointInversions

/-!
# The explicit endpoint transmission block

The endpoint pencil determines a decreasing block in the transmission
permutation.  This is the algebraic input to the endpoint inversion bound.
-/

@[expose] public section

namespace Bananas

open Utilities

theorem exists_endpoint_transmission_block
    {g k : ℕ} (B : Banana g)
    (hsub : AllSubmodular (mark B.graph (leftEndpoint B) (rightEndpoint B)))
    (hk : TorsionWitness (mark B.graph (leftEndpoint B) (rightEndpoint B)) k) :
    ∃ τ : ℤ → ℤ,
      IsTransmissionPermutation
          (mark B.graph (leftEndpoint B) (rightEndpoint B))
          (g • oneChip (rightEndpoint B)) τ ∧
      IsKAffine k τ ∧
      ∀ b : ℕ, b ≤ g → τ b = (g - b : ℕ) := by
  let M := mark B.graph (leftEndpoint B) (rightEndpoint B)
  let D : CFDiv B.graph := g • oneChip (rightEndpoint B)
  obtain ⟨τ, hτ, hAffine⟩ :=
    exists_affineTransmissionPermutation_of_submodular M D (banana_graph_connected B)
      (hsub D) hk
  refine ⟨τ, hτ, hAffine, ?_⟩
  intro b hb
  have hDiv :
      D + ((g - b : ℕ) : ℤ) • oneChip (leftEndpoint B) -
          (b : ℤ) • oneChip (rightEndpoint B) =
        (g - b) • endpointPencilDivisor B := by
    rw [← Nat.cast_smul_eq_nsmul ℤ]
    dsimp [D, endpointPencilDivisor]
    ext x
    simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply]
    have hCast : ((g - b : ℕ) : ℤ) = (g : ℤ) - b := by omega
    rw [hCast]
    ring
  have hDelta := rankDelta_endpointPencil_nsmul_eq_one B (g - b) (by omega)
  have hValue := hτ.2 (g - b) b
  dsimp [M, D] at hValue
  rw [← Nat.cast_sub hb] at hValue
  change (if τ (b : ℤ) = ((g - b : ℕ) : ℤ) then (1 : ℤ) else 0) =
      rankDelta (mark B.graph (leftEndpoint B) (rightEndpoint B))
        (D + ((g - b : ℕ) : ℤ) • oneChip (leftEndpoint B) -
          (b : ℤ) • oneChip (rightEndpoint B)) at hValue
  rw [hDiv] at hValue
  have hValue' : (if τ (b : ℤ) = ((g - b : ℕ) : ℤ) then (1 : ℤ) else 0) = 1 :=
    hValue.trans hDelta
  simpa using hValue'

/-- The decreasing endpoint block forces every affine period to be larger
than the genus.  In particular its `choose (g+1) 2` ordinary inversions lie
in distinct period classes. -/
theorem endpoint_affine_period_gt_genus
    {g k : ℕ} {τ : ℤ → ℤ}
    (hk : 0 < k) (hAffine : IsKAffine k τ)
    (hBlock : ∀ b : ℕ, b ≤ g → τ b = (g - b : ℕ)) :
    g < k := by
  by_contra hNot
  have hkg : k ≤ g := by omega
  have hAtZero := hBlock 0 (by omega)
  have hAtK := hBlock k hkg
  have hPeriod := hAffine 0
  norm_num at hPeriod
  norm_num at hAtZero hAtK
  rw [hAtZero, hAtK] at hPeriod
  have hkInt : (0 : ℤ) < k := by exact_mod_cast hk
  omega

end Bananas
