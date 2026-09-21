/-
Copyright (c) 2026 Nathan Pflueger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nathan Pflueger
-/

import LeanPool.BrillNoetherGraphs.Bananas.Theta.ThetaNonrecurrence
import LeanPool.BrillNoetherGraphs.Bananas.Transmission.TransmissionAPI
import LeanPool.BrillNoetherGraphs.Utilities.Transmission.Transmission

/-!
# Bridging the banana transmission vocabulary to `AspPerm`

`Bananas/` models a transmission permutation as a raw function `ℤ → ℤ`
(`IsTransmissionPermutation`, `IsKAffine`, `kInversions`), because that is the
shape the paper's Definition 2.11 writes down and the shape the inversion
counting arguments use.  `Utilities` models the same notion over the
`demazure` dependency's `AspPerm`, via `Utilities.SatisfiesTransmission`
(an inequality against the slipface `τ.s`).

This file supplies the adapter between those two formulations.  Nothing here
is banana-specific: it holds for any connected `CFGraph` with two marks.

## What is proved

`exists_aspPerm_rank_eq_of_isTransmissionPermutation` is the substantive half.
Given a raw transmission permutation `τ` for `D`, it produces the `AspPerm`
`σ` with `σ.func = τ` and the *equality*

  `rank G (D + a • u - b • v) = σ.s (a + 1) b - 1`

at every lattice point.  `TransmissionInequality` is the `≥` weakening of this.

The degree normalization `deg D = genus G + σ.χ`, the other conjunct of
`SatisfiesTransmission`, looks like an extra side condition but is automatic:
`AspPerm.s_eq` at the origin gives `χ(σ) = σ.s 0 0 - (σ⁻¹).s 0 0`, the two
counting lemmas of `ThetaNonrecurrence` identify those with `rank (D - u) + 1`
and `rank (K - (D - u)) + 1`, and Riemann-Roch turns the difference into
`deg (D - u) - g + 1 = deg D - g`.  So
`satisfiesTransmission_of_isTransmissionPermutation` is unconditional and
constructs a `SatisfiesTransmission` witness directly.
-/

namespace Bananas

open Utilities

open Utilities Utilities.Certificate

/-- The `AspPerm` underlying a raw transmission permutation, together with the
exact marked rank formula it computes.

This is the translation lemma between the two transmission formalisms.  The
`AspPerm` is the one whose slipface is the marked rank surface of `D - u`, and
`σ.s (a + 1) b` is exactly `rank (D + a·u - b·v) + 1`. -/
theorem exists_aspPerm_rank_eq_of_isTransmissionPermutation
    {G : CFGraph} (u v : G.V) (hconn : _root_.graph_connected G)
    (D : CFDiv G) (τ : ℤ → ℤ)
    (hτ : IsTransmissionPermutation (mark G u v) D τ) :
    ∃ σ : AspPerm, σ.func = τ ∧
      ∀ a b : ℤ,
        rank G (D + a • one_chip u - b • one_chip v) = σ.s (a + 1) b - 1 := by
  obtain ⟨σ, hσFunc, _hσSlip⟩ :=
    transmissionPermutation_rankSlipFace (mark G u v) D hconn τ hτ
  refine ⟨σ, hσFunc, ?_⟩
  intro a b
  -- State both sides at `G`, `u`, `v` rather than at `(mark G u v).graph`
  -- etc.  The projections are defeq, and `G` is a variable here, so the
  -- coercion is a cheap projection-of-constructor step; leaving the
  -- projections in place would instead leave `omega` with atoms that do not
  -- match syntactically.
  have hSE : rank G (D + a • one_chip u - b • one_chip v) + 1 =
      ((southeast_set τ (a + 1) b).ncard : ℤ) :=
    transmission_rank_eq_southeast_ncard (mark G u v) D hconn τ hτ a b
  have hs : σ.s (a + 1) b = ((southeast_set τ (a + 1) b).ncard : ℤ) := by
    rw [AspPerm.s_eq_ncard, hσFunc]
  omega

/-- Every raw transmission permutation yields the transmission inequalities of
`Utilities.Transmission` for the corresponding `AspPerm`, on any test set.

Unlike `satisfiesTransmission_of_isTransmissionPermutation` this needs no
degree hypothesis, because `SatisfiesTransmissionOn` carries none. -/
theorem satisfiesTransmissionOn_of_isTransmissionPermutation
    {G : CFGraph} (u v : G.V) (hconn : _root_.graph_connected G)
    (D : CFDiv G) (τ : ℤ → ℤ)
    (hτ : IsTransmissionPermutation (mark G u v) D τ)
    (S : Set (ℤ × ℤ)) :
    ∃ σ : AspPerm, σ.func = τ ∧ SatisfiesTransmissionOn G u v σ D S := by
  obtain ⟨σ, hσFunc, hRank⟩ :=
    exists_aspPerm_rank_eq_of_isTransmissionPermutation u v hconn D τ hτ
  refine ⟨σ, hσFunc, ?_⟩
  intro p _
  have := hRank p.1 p.2
  unfold TransmissionInequality
  omega

/-- The degree normalization is automatic.

`SatisfiesTransmission` requires `deg D = g + χ(σ)`, which looks like an extra
side condition.  It is not: for the `AspPerm` attached to a transmission
permutation of `D` it follows from Riemann-Roch.  Evaluating
`AspPerm.s_eq` at `(0,0)` gives
`χ(σ) = σ.s 0 0 - (σ⁻¹).s 0 0`, and the two counting lemmas identify those
with `rank (D - u) + 1` and `rank (K - (D - u)) + 1`, so
`χ(σ) = rank (D - u) - rank (K - (D - u)) = deg (D - u) - g + 1 = deg D - g`. -/
theorem degree_eq_genus_add_chi_of_isTransmissionPermutation
    {G : CFGraph} (u v : G.V) (hconn : _root_.graph_connected G)
    (D : CFDiv G) (τ : ℤ → ℤ)
    (hτ : IsTransmissionPermutation (mark G u v) D τ)
    (σ : AspPerm) (hσFunc : σ.func = τ) :
    deg D = (genus G : ℤ) + σ.χ := by
  -- `χ` at the origin, in terms of the two counting sets.
  have hχ : σ.χ = σ.s 0 0 - (σ⁻¹).s 0 0 := by
    have := σ.s_eq 0 0
    omega
  have hSE : σ.s 0 0 = ((southeast_set τ 0 0).ncard : ℤ) := by
    rw [AspPerm.s_eq_ncard, hσFunc]
  have hNW : (σ⁻¹).s 0 0 = ((northwest_set τ 0 0).ncard : ℤ) := by
    rw [AspPerm.s'_eq_ncard, hσFunc]
  -- The two counting lemmas at `(a, b) = (-1, 0)`.
  have hRankSE : rank G (D - one_chip u) + 1 =
      ((southeast_set τ 0 0).ncard : ℤ) := by
    have h : rank G (D + (-1 : ℤ) • one_chip u - (0 : ℤ) • one_chip v) + 1 =
        ((southeast_set τ ((-1 : ℤ) + 1) 0).ncard : ℤ) :=
      transmission_rank_eq_southeast_ncard (mark G u v) D hconn τ hτ (-1) 0
    have hDiv : D + (-1 : ℤ) • one_chip u - (0 : ℤ) • one_chip v =
        D - one_chip u := by
      rw [neg_one_zsmul, zero_zsmul]
      abel
    rw [hDiv] at h
    simpa using h
  have hRankNW : rank G (canonical_divisor G - (D - one_chip u)) + 1 =
      ((northwest_set τ 0 0).ncard : ℤ) := by
    have h : rank G (canonical_divisor G - D - (-1 : ℤ) • one_chip u +
          (0 : ℤ) • one_chip v) + 1 =
        ((northwest_set τ ((-1 : ℤ) + 1) 0).ncard : ℤ) :=
      transmission_complement_rank_eq_northwest_ncard (mark G u v) D
        hconn τ hτ (-1) 0
    have hDiv : canonical_divisor G - D - (-1 : ℤ) • one_chip u +
        (0 : ℤ) • one_chip v = canonical_divisor G - (D - one_chip u) := by
      rw [neg_one_zsmul, zero_zsmul]
      abel
    rw [hDiv] at h
    simpa using h
  have hRR := riemann_roch_for_graphs hconn (D - one_chip u)
  have hDeg : deg (D - one_chip u) = deg D - 1 := by
    rw [deg.map_sub, deg_one_chip]
  omega

/-- The full bridge, unconditionally: a raw transmission permutation for `D`
gives an `AspPerm` satisfying `Utilities.SatisfiesTransmission` for `D`.

This gives a direct construction of a `SatisfiesTransmission` witness. -/
theorem satisfiesTransmission_of_isTransmissionPermutation
    {G : CFGraph} (u v : G.V) (hconn : _root_.graph_connected G)
    (D : CFDiv G) (τ : ℤ → ℤ)
    (hτ : IsTransmissionPermutation (mark G u v) D τ) :
    ∃ σ : AspPerm, σ.func = τ ∧ SatisfiesTransmission G u v σ D := by
  obtain ⟨σ, hσFunc, hRank⟩ :=
    exists_aspPerm_rank_eq_of_isTransmissionPermutation u v hconn D τ hτ
  refine ⟨σ, hσFunc,
    degree_eq_genus_add_chi_of_isTransmissionPermutation u v hconn D τ hτ σ
      hσFunc, ?_⟩
  intro a b
  have := hRank a b
  unfold TransmissionInequality
  omega

/-- Specialization to a banana graph: all-submodularity and a torsion witness
already produce a raw transmission permutation for every divisor
(`exists_affine_transmission_of_allSubmodular`), so they produce a full
`AspPerm`-level transmission witness for every divisor too.

This is the form in which the Section 4 banana results — for instance
`evenlyMarkedTheta_kGeneral`, whose `KGeneralTransmission` conclusion contains
exactly this data — become usable by the `AspPerm`/wedge machinery. -/
theorem exists_aspPerm_satisfiesTransmission_of_allSubmodular
    {g k : ℕ} (B : Banana g) (u v : B.graph.V)
    (hk : TorsionWitness (mark B.graph u v) k)
    (hsub : AllSubmodular (mark B.graph u v))
    (D : CFDiv B.graph) :
    ∃ σ : AspPerm, IsKAffine k σ.func ∧
      SatisfiesTransmission B.graph u v σ D := by
  obtain ⟨τ, hτ, hAffine, _hFinite⟩ :=
    exists_affine_transmission_of_allSubmodular
      (banana_graph_connected B) hk hsub D
  obtain ⟨σ, hσFunc, hSat⟩ :=
    satisfiesTransmission_of_isTransmissionPermutation u v
      (banana_graph_connected B) D τ hτ
  exact ⟨σ, by rw [hσFunc]; exact hAffine, hSat⟩

end Bananas
