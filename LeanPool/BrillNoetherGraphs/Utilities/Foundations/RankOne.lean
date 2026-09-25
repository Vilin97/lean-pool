/-
Copyright (c) 2026 Nathan Pflueger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nathan Pflueger
-/
module


public import LeanPool.BrillNoetherGraphs.Utilities.Foundations.Parameters

/-!
# Rank-one certificates

Rank at least one can be checked one vertex at a time. This module packages
that reduction independently of the edge-addition machinery and gives a
certificate interface suited to explicit chip-firing arguments.
-/

@[expose] public section

namespace Utilities

/-- An effective divisor of degree one consists of a single chip. -/
theorem effective_degree_one_eq_one_chip
    {G : CFGraph} (E : CFDiv G) (hEffective : effective E)
    (hDegree : deg E = 1) :
    ∃ v : G.V, E = oneChip v := by
  have hPositive : ∃ v : G.V, E v ≥ 1 := by
    by_contra h
    have hDivisorZero : E = 0 := by
      funext v
      have hv : ¬ E v ≥ 1 := fun hv => h ⟨v, hv⟩
      have hvEffective := hEffective v
      simp only [Pi.zero_apply]
      omega
    have hZero : deg E = 0 := by simp [hDivisorZero]
    omega
  obtain ⟨v, hv⟩ := hPositive
  have hSubEffective : effective (E - oneChip v) := by
    intro w
    by_cases hw : w = v
    · subst w
      simp [oneChip, hv]
    · simpa [oneChip, hw] using hEffective w
  have hSubDegree : deg (E - oneChip v) = 0 := by
    rw [deg.map_sub, deg_one_chip, hDegree]
    norm_num
  have hSubZero := eff_degree_zero (E - oneChip v) hSubEffective hSubDegree
  exact ⟨v, sub_eq_zero.mp hSubZero⟩

/-- Rank at least one can be tested by subtracting one chip at each vertex. -/
theorem rank_ge_one_iff_winnable_sub_one_chip
    (G : CFGraph) (D : CFDiv G) :
    rank G D ≥ 1 ↔ ∀ v : G.V, winnable G (D - oneChip v) := by
  rw [← rank_geq_iff]
  constructor
  · intro hRank v
    exact hRank (oneChip v) ⟨eff_one_chip v, deg_one_chip v⟩
  · intro hVertex E hE
    obtain ⟨v, rfl⟩ :=
      effective_degree_one_eq_one_chip E hE.1 hE.2
    exact hVertex v

/-- Effective representatives for all one-chip subtractions certify rank at
least one. The representatives may be different at different vertices. -/
theorem rank_ge_one_of_vertex_certificates
    (G : CFGraph) (D : CFDiv G)
    (hCertificates : ∀ v : G.V,
      ∃ E : CFDiv G,
        effective E ∧ linearEquiv G (D - oneChip v) E) :
    rank G D ≥ 1 := by
  rw [rank_ge_one_iff_winnable_sub_one_chip]
  intro v
  rw [winnable_iff_exists_effective]
  exact hCertificates v

/-- Explicit firing scripts producing effective representatives for all
one-chip subtractions certify rank at least one. -/
theorem rank_ge_one_of_firing_certificates
    (G : CFGraph) (D : CFDiv G)
    (hCertificates : ∀ v : G.V,
      ∃ (E : CFDiv G) (σ : firingScript G),
        effective E ∧ E = D - oneChip v + prin G σ) :
    rank G D ≥ 1 := by
  apply rank_ge_one_of_vertex_certificates G D
  intro v
  obtain ⟨E, σ, hEffective, hE⟩ := hCertificates v
  refine ⟨E, hEffective, ?_⟩
  apply (principal_iff_eq_prin G (E - (D - oneChip v))).mpr
  refine ⟨σ, ?_⟩
  rw [hE]
  abel

/-- A divisor of the requested degree, together with explicit vertexwise
firing certificates, is a rank-one Brill--Noether witness. -/
theorem BNExists_rank_one_of_firing_certificates
    (G : CFGraph) (D : CFDiv G) {d : ℤ} (hDegree : deg D = d)
    (hCertificates : ∀ v : G.V,
      ∃ (E : CFDiv G) (σ : firingScript G),
        effective E ∧ E = D - oneChip v + prin G σ) :
    BNExists G 1 d := by
  exact ⟨D, hDegree,
    rank_ge_one_of_firing_certificates G D hCertificates⟩

end Utilities
