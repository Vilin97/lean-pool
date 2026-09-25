/-
Copyright (c) 2026 Nathan Pflueger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nathan Pflueger
-/
module


public import LeanPool.BrillNoetherGraphs.LowGenus.GenusFiveTwoPoleData
public import LeanPool.BrillNoetherGraphs.Utilities.Subdivision.CanonicalDivisor
public import LeanPool.BrillNoetherGraphs.Utilities.Subdivision.SubdivisionCoreSupport
public import LeanPool.BrillNoetherGraphs.Utilities.Subdivision.TwoPoleSubdivisionGluing

/-!
# One canonical construction for six positive genus-five rows

Two connected leafless genus-two factors carry effective canonical pencils.
The three-case connector lemma reaches the four attachment vertices, and
all other core vertices already carry chips. The finite data choose each
connector in turn; no length chamber or graph-isomorphism certificate is used.

The theorem here concerns positive subdivisions. `GenusFiveTwoPoleClosed`
extends the same weights to contraction faces by discrete specialization.
-/

@[expose] public section

namespace AtanasovRanganathan.GenusFiveTwoPole

open Utilities Utilities.Certificate
open Utilities.Certificate.TwoPoleSubdivision
open Utilities.Subdivision.SubdivisionCoreSupport
open GenusFiveCoreAtlas GenusFiveTwoPoleData

/-- The fixed core-supported sum of the two local canonical divisors has
rank at least one when every unsupported core vertex is an attachment
vertex in one of the two displayed connector orders. -/
theorem rank_ge_one_of_twoPoleData {n p : ℕ}
    (s : SubdivisionGraph.Spec n p) (hConnected : graphConnected s.graph)
    (weight : Fin n → ℤ) (hNonnegative : ∀ v, 0 ≤ weight v)
    (data : Fin 2 → Data s.core 4 5 4 5)
    (hLeftConnected : ∀ i, (data i).leftCore.Connected)
    (hRightConnected : ∀ i, (data i).rightCore.Connected)
    (hLeftLeafless : ∀ i v, 2 ≤ (data i).leftCore.incidenceDegree v)
    (hRightLeafless : ∀ i v, 2 ≤ (data i).rightCore.incidenceDegree v)
    (hWeightLeft : ∀ i a,
      weight ((data i).vertices (.inl a)) =
        ((data i).leftCore.incidenceDegree a : ℤ) - 2)
    (hWeightRight : ∀ i b,
      weight ((data i).vertices (.inr b)) =
        ((data i).rightCore.incidenceDegree b : ℤ) - 2)
    (hCover : ∀ v, 1 ≤ weight v ∨ ∃ i : Fin 2,
      v = (data i).vertices (.inl ((data i).leftPole 0)) ∨
      v = (data i).vertices (.inr ((data i).rightPole 0))) :
    rank s.graph (coreDivisor s weight) ≥ 1 := by
  let D := coreDivisor s weight
  have hDEffective : effective D := coreDivisor_effective s weight hNonnegative
  have hReaches : ∀ vertex : Fin n,
      StrongSeparator.Reaches s.graph D (s.coreVertex vertex) := by
    intro vertex
    rcases hCover vertex with hChip | ⟨i, hPole⟩
    · exact StrongSeparator.reaches_of_effective_representative
        (linearEquiv.refl s.graph D) hDEffective hChip
    · let d := data i
      let J := d.scriptGluing s
      let CA := canonicalDivisor (d.leftSpec s).graph
      let CB := canonicalDivisor (d.rightSpec s).graph
      obtain ⟨hCA, _, hRankA⟩ := (d.leftSpec s).effective_canonical_pencil
        ((d.leftSpec s).graph_connected_of_coreConnected (hLeftConnected i))
        (by decide) (hLeftLeafless i)
      obtain ⟨hCB, _, hRankB⟩ := (d.rightSpec s).effective_canonical_pencil
        ((d.rightSpec s).graph_connected_of_coreConnected (hRightConnected i))
        (by decide) (hRightLeafless i)
      have hDA : ∀ a, D (J.left a) = CA a := by
        intro a
        rcases a with a | ⟨e, k⟩
        · change weight (d.vertices (.inl a)) =
            canonicalDivisor (d.leftSpec s).graph ((d.leftSpec s).coreVertex a)
          rw [(d.leftSpec s).canonical_divisor_coreVertex]
          exact hWeightLeft i a
        · change 0 = canonicalDivisor (d.leftSpec s).graph
            ((d.leftSpec s).interiorVertex e k)
          rw [(d.leftSpec s).canonical_divisor_interiorVertex]
      have hDB : ∀ b, D (J.right b) = CB b := by
        intro b
        rcases b with b | ⟨e, k⟩
        · change weight (d.vertices (.inr b)) =
            canonicalDivisor (d.rightSpec s).graph ((d.rightSpec s).coreVertex b)
          rw [(d.rightSpec s).canonical_divisor_coreVertex]
          exact hWeightRight i b
        · change 0 = canonicalDivisor (d.rightSpec s).graph
            ((d.rightSpec s).interiorVertex e k)
          rw [(d.rightSpec s).canonical_divisor_interiorVertex]
      have hWinA := (rank_ge_one_iff_winnable_sub_one_chip _ _).mp hRankA
        (d.leftPoles s).first
      have hWinB := (rank_ge_one_iff_winnable_sub_one_chip _ _).mp hRankB
        (d.rightPoles s).first
      rcases hPole with hPole | hPole
      · subst vertex
        exact J.winnable_sub_left_first D CA CB hDA hDB
          (fun z _ _ => hDEffective z) hCA hCB hWinA hWinB
      · subst vertex
        exact J.winnable_sub_right_first D CA CB hDA hDB
          (fun z _ _ => hDEffective z) hCA hCB hWinA hWinB

  apply StrongSeparator.rank_ge_one_of_strongSeparatorCertificate hConnected
    (ExplicitPotential.Certificate.coreVertices_nonempty s)
    s.coreVertices_strongSeparatorCertificate
  intro vertex hVertex
  obtain ⟨anchor, _hAnchor, rfl⟩ := Finset.mem_image.mp hVertex
  exact hReaches anchor

/-- Package the fixed canonical divisor as the existing degree-four
Brill–Noether existence statement. -/
theorem bnExists_of_twoPoleData {n p : ℕ}
    (s : SubdivisionGraph.Spec n p) (hConnected : graphConnected s.graph)
    (weight : Fin n → ℤ) (hNonnegative : ∀ v, 0 ≤ weight v)
    (hDegree : ∑ v : Fin n, weight v = 4)
    (data : Fin 2 → Data s.core 4 5 4 5)
    (hLeftConnected : ∀ i, (data i).leftCore.Connected)
    (hRightConnected : ∀ i, (data i).rightCore.Connected)
    (hLeftLeafless : ∀ i v, 2 ≤ (data i).leftCore.incidenceDegree v)
    (hRightLeafless : ∀ i v, 2 ≤ (data i).rightCore.incidenceDegree v)
    (hWeightLeft : ∀ i a,
      weight ((data i).vertices (.inl a)) =
        ((data i).leftCore.incidenceDegree a : ℤ) - 2)
    (hWeightRight : ∀ i b,
      weight ((data i).vertices (.inr b)) =
        ((data i).rightCore.incidenceDegree b : ℤ) - 2)
    (hCover : ∀ v, 1 ≤ weight v ∨ ∃ i : Fin 2,
      v = (data i).vertices (.inl ((data i).leftPole 0)) ∨
      v = (data i).vertices (.inr ((data i).rightPole 0))) :
    BNExists s.graph 1 4 := by
  refine ⟨coreDivisor s weight, ?_, ?_⟩
  · simpa only [deg_coreDivisor] using hDegree
  · exact rank_ge_one_of_twoPoleData s hConnected weight hNonnegative data
      hLeftConnected hRightConnected hLeftLeafless hRightLeafless
      hWeightLeft hWeightRight hCover

/-- The displayed fixed canonical weights have rank at least one on every
positive subdivision of row 01. -/
theorem row01_rank_positive (s : SubdivisionGraph.Spec 8 12)
    (hCore : s.core = row01Core) :
    rank s.graph (coreDivisor s row01Weight) ≥ 1 := by
  cases s with
  | mk core length hn hl hp =>
    dsimp at hCore
    subst core
    apply rank_ge_one_of_twoPoleData _
      (SubdivisionGraph.Spec.graph_connected_of_coreConnected _ row01_connected)
      row01Weight row01_weight_nonneg row01
      row01_left_connected row01_right_connected
      row01_left_degree_ge_two row01_right_degree_ge_two
      row01_weight_left row01_weight_right row01_coverage

/-- The displayed fixed canonical weights have rank at least one on every
positive subdivision of row 02. -/
theorem row02_rank_positive (s : SubdivisionGraph.Spec 8 12)
    (hCore : s.core = row02Core) :
    rank s.graph (coreDivisor s row02Weight) ≥ 1 := by
  cases s with
  | mk core length hn hl hp =>
    dsimp at hCore
    subst core
    apply rank_ge_one_of_twoPoleData _
      (SubdivisionGraph.Spec.graph_connected_of_coreConnected _ row02_connected)
      row02Weight row02_weight_nonneg row02
      row02_left_connected row02_right_connected
      row02_left_degree_ge_two row02_right_degree_ge_two
      row02_weight_left row02_weight_right row02_coverage

/-- The displayed fixed canonical weights have rank at least one on every
positive subdivision of row 03. -/
theorem row03_rank_positive (s : SubdivisionGraph.Spec 8 12)
    (hCore : s.core = row03Core) :
    rank s.graph (coreDivisor s row03Weight) ≥ 1 := by
  cases s with
  | mk core length hn hl hp =>
    dsimp at hCore
    subst core
    apply rank_ge_one_of_twoPoleData _
      (SubdivisionGraph.Spec.graph_connected_of_coreConnected _ row03_connected)
      row03Weight row03_weight_nonneg row03
      row03_left_connected row03_right_connected
      row03_left_degree_ge_two row03_right_degree_ge_two
      row03_weight_left row03_weight_right row03_coverage

/-- The displayed fixed canonical weights have rank at least one on every
positive subdivision of row 04. -/
theorem row04_rank_positive (s : SubdivisionGraph.Spec 8 12)
    (hCore : s.core = row04Core) :
    rank s.graph (coreDivisor s row04Weight) ≥ 1 := by
  cases s with
  | mk core length hn hl hp =>
    dsimp at hCore
    subst core
    apply rank_ge_one_of_twoPoleData _
      (SubdivisionGraph.Spec.graph_connected_of_coreConnected _ row04_connected)
      row04Weight row04_weight_nonneg row04
      row04_left_connected row04_right_connected
      row04_left_degree_ge_two row04_right_degree_ge_two
      row04_weight_left row04_weight_right row04_coverage

/-- The displayed fixed canonical weights have rank at least one on every
positive subdivision of row 07. -/
theorem row07_rank_positive (s : SubdivisionGraph.Spec 8 12)
    (hCore : s.core = row07Core) :
    rank s.graph (coreDivisor s row07Weight) ≥ 1 := by
  cases s with
  | mk core length hn hl hp =>
    dsimp at hCore
    subst core
    apply rank_ge_one_of_twoPoleData _
      (SubdivisionGraph.Spec.graph_connected_of_coreConnected _ row07_connected)
      row07Weight row07_weight_nonneg row07
      row07_left_connected row07_right_connected
      row07_left_degree_ge_two row07_right_degree_ge_two
      row07_weight_left row07_weight_right row07_coverage

/-- The displayed fixed canonical weights have rank at least one on every
positive subdivision of row 13. -/
theorem row13_rank_positive (s : SubdivisionGraph.Spec 8 12)
    (hCore : s.core = row13Core) :
    rank s.graph (coreDivisor s row13Weight) ≥ 1 := by
  cases s with
  | mk core length hn hl hp =>
    dsimp at hCore
    subst core
    apply rank_ge_one_of_twoPoleData _
      (SubdivisionGraph.Spec.graph_connected_of_coreConnected _ row13_connected)
      row13Weight row13_weight_nonneg row13
      row13_left_connected row13_right_connected
      row13_left_degree_ge_two row13_right_degree_ge_two
      row13_weight_left row13_weight_right row13_coverage

/-- The shared canonical construction on every positive subdivision of row 01. -/
theorem row01_bnExists_positive (s : SubdivisionGraph.Spec 8 12)
    (hCore : s.core = row01Core) : BNExists s.graph 1 4 := by
  refine ⟨coreDivisor s row01Weight, ?_, row01_rank_positive s hCore⟩
  simpa only [deg_coreDivisor] using row01_weight_sum

/-- The shared canonical construction on every positive subdivision of row 02. -/
theorem row02_bnExists_positive (s : SubdivisionGraph.Spec 8 12)
    (hCore : s.core = row02Core) : BNExists s.graph 1 4 := by
  refine ⟨coreDivisor s row02Weight, ?_, row02_rank_positive s hCore⟩
  simpa only [deg_coreDivisor] using row02_weight_sum

/-- The shared canonical construction on every positive subdivision of row 03. -/
theorem row03_bnExists_positive (s : SubdivisionGraph.Spec 8 12)
    (hCore : s.core = row03Core) : BNExists s.graph 1 4 := by
  refine ⟨coreDivisor s row03Weight, ?_, row03_rank_positive s hCore⟩
  simpa only [deg_coreDivisor] using row03_weight_sum

/-- The shared canonical construction on every positive subdivision of row 04. -/
theorem row04_bnExists_positive (s : SubdivisionGraph.Spec 8 12)
    (hCore : s.core = row04Core) : BNExists s.graph 1 4 := by
  refine ⟨coreDivisor s row04Weight, ?_, row04_rank_positive s hCore⟩
  simpa only [deg_coreDivisor] using row04_weight_sum

/-- The shared canonical construction on every positive subdivision of row 07. -/
theorem row07_bnExists_positive (s : SubdivisionGraph.Spec 8 12)
    (hCore : s.core = row07Core) : BNExists s.graph 1 4 := by
  refine ⟨coreDivisor s row07Weight, ?_, row07_rank_positive s hCore⟩
  simpa only [deg_coreDivisor] using row07_weight_sum

/-- The shared canonical construction on every positive subdivision of row 13. -/
theorem row13_bnExists_positive (s : SubdivisionGraph.Spec 8 12)
    (hCore : s.core = row13Core) : BNExists s.graph 1 4 := by
  refine ⟨coreDivisor s row13Weight, ?_, row13_rank_positive s hCore⟩
  simpa only [deg_coreDivisor] using row13_weight_sum

end AtanasovRanganathan.GenusFiveTwoPole
