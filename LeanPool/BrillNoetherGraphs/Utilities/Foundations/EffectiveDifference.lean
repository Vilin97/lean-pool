/-
Copyright (c) 2026 Nathan Pflueger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nathan Pflueger
-/
module


public import LeanPool.BrillNoetherGraphs.Utilities.Foundations.RiemannRochWinnable

/-!
# The effective-difference lemma

For a connected graph of genus `g ≥ 2`, every degree-zero divisor class `γ` is
the difference `F - E` of two effective divisors `E, F` of degree `g - 1`.

Equivalently, the two effective loci satisfy
`W_{g-1} ∩ (W_{g-1} - γ) ≠ ∅` in the finite graph Jacobian.  The formulation
below is purely in terms of divisors and linear equivalence.

## Proof sketch

Write `K` for `canonicalDivisor G` and `g` for `genus G`.

1. `rank G γ ≥ -1` always, and `g ≥ 2` forces `-1 ≥ 1 - g`, so
   `rank G γ ≥ 1 - g`.  Since `deg γ = 0 = (g - 1) + (1 - g)`, Riemann--Roch
   (`rank_ge_iff_exists_effective_canonical_complement`) turns this rank bound
   into an effective representative `M` of `K - γ`; `deg M = 2g - 2`.
2. Split `M` into effective `E, F*` with `deg E = deg F* = g - 1`
   (`effective_divisor_decomposition`, already in `ChipFiringWithLean.Basic`).
3. `F*` is effective, hence winnable, so by the degree-`(g-1)` self-duality
   (`degree_genus_sub_one_winnable_iff_complement_winnable`) its canonical
   complement `K - F*` is winnable too; let `F` be an effective representative.
4. `F - E ~ (K - F*) - E = K - (E + F*) = K - M ~ K - (K - γ) = γ`.
-/

public section

namespace Utilities

/-- **Effective-difference lemma.** On a connected graph `G` of genus `g ≥ 2`,
every degree-zero divisor class `γ` is the difference `F - E` of two effective
divisors `E, F` of degree `g - 1`. -/
theorem exists_effective_difference_of_deg_zero
    {G : CFGraph} (hG : graphConnected G) (hg : CFGraph.genus G ≥ 2)
    (γ : CFDiv G) (hγ : CFDiv.degree γ = 0) :
    ∃ E F : CFDiv G,
      effective E ∧ effective F ∧
      CFDiv.degree E = CFGraph.genus G - 1 ∧ CFDiv.degree F = CFGraph.genus G - 1 ∧
      linearEquiv G (F - E) γ := by
  -- Step 1: an effective representative `M` of `K - γ`, of degree `2g - 2`.
  have hRankGamma : rank G γ ≥ 1 - CFGraph.genus G := by
    have h1 := rank_geq_neg_one G γ
    omega
  have hDegGamma : CFDiv.degree γ = CFGraph.genus G - 1 + (1 - CFGraph.genus G) := by omega
  obtain ⟨M, hMEff, hMEquiv⟩ :=
    (rank_ge_iff_exists_effective_canonical_complement hG γ (1 - CFGraph.genus G)
      hDegGamma).mp hRankGamma
  have hMDeg : CFDiv.degree M = 2 * CFGraph.genus G - 2 := by
    have hEq := linear_equiv_preserves_deg G (canonicalDivisor G - γ) M hMEquiv
    rw [CFDiv.degree.map_sub, degree_of_canonical_divisor, hγ] at hEq
    omega
  -- Step 2: split `M` into effective `E, F*` of degree `g - 1` each.
  have hd : ((CFGraph.genus G - 1).toNat : ℤ) = CFGraph.genus G - 1 :=
    Int.toNat_of_nonneg (by omega)
  obtain ⟨E, Fstar, hEEff, hFstarEff, hEDeg, hFstarDeg, hMSplit⟩ :=
    effective_divisor_decomposition G M (CFGraph.genus G - 1).toNat (CFGraph.genus G - 1).toNat
      hMEff (by rw [hMDeg, hd]; ring)
  have hEDeg' : CFDiv.degree E = CFGraph.genus G - 1 := hEDeg.trans hd
  have hFstarDeg' : CFDiv.degree Fstar = CFGraph.genus G - 1 := hFstarDeg.trans hd
  -- Step 3: `F*` is effective, hence winnable; by degree-`(g-1)` self-duality
  -- its canonical complement `K - F*` is winnable too.  Let `F` be an
  -- effective representative of it.
  have hFstarWinnable : winnable G Fstar := winnable_of_effective G Fstar hFstarEff
  have hFwinnable : winnable G (canonicalDivisor G - Fstar) :=
    (degree_genus_sub_one_winnable_iff_complement_winnable hG Fstar hFstarDeg').mp
      hFstarWinnable
  obtain ⟨F, hFEff, hFEquiv⟩ :=
    (winnable_iff_exists_effective G (canonicalDivisor G - Fstar)).mp hFwinnable
  have hFDeg : CFDiv.degree F = CFGraph.genus G - 1 := by
    have hEq := linear_equiv_preserves_deg G (canonicalDivisor G - Fstar) F hFEquiv
    rw [CFDiv.degree.map_sub, degree_of_canonical_divisor, hFstarDeg'] at hEq
    omega
  -- Step 4: `F - E = K - (E + F*) = K - M ~ K - (K - γ) = γ`.
  refine ⟨E, F, hEEff, hFEff, hEDeg', hFDeg, ?_⟩
  unfold linearEquiv at hMEquiv hFEquiv ⊢
  have hDifference :
      γ - (F - E) =
        (M - (canonicalDivisor G - γ)) - (F - (canonicalDivisor G - Fstar)) := by
    rw [hMSplit]; abel
  rw [hDifference]
  simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using
    AddSubgroup.add_mem (principalDivisors G) hMEquiv
      (AddSubgroup.neg_mem (principalDivisors G) hFEquiv)

end Utilities
