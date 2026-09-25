/-
Copyright (c) 2026 Nathan Pflueger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nathan Pflueger
-/
module


public import LeanPool.BrillNoetherGraphs.Bananas.Transmission.CycleTorsionOrder
public import LeanPool.BrillNoetherGraphs.Bananas.Theta.EvenlyMarkedThetaKGeneral
public import LeanPool.BrillNoetherGraphs.Bananas.Sections.SectionSixChainConclusion

/-!
# Example 1.15: an explicit genus-eight Brill--Noether general chain

The five factors, in the order the paper lists them:

* the cycle `B_{3,1}` (torsion order `k = 4`);
* the evenly marked theta graph `θ_{4,1,4}`, marked at `(x_1, z_1)`
  (`k = 4`);
* the cycle `B_{3,2}` (`k = 5`);
* the evenly marked theta graph `θ_{5,2,10}`, marked at `(x_2, z_4)`
  (`k = 5`);
* the evenly marked theta graph `θ_{6,2,3}`, marked at `(x_4, z_2)`
  (`k = 3`).

Each factor's `k`-general transmission comes from `cycle_kGeneralTransmission`
(Example 1.11, `Bananas/CycleTorsionOrder.lean`) or
`evenlyMarkedTheta_kGeneral` (`Bananas/EvenlyMarkedThetaKGeneral.lean`). The
genera are `1, 2, 1, 2, 2`, summing to the paper's genus `8`, and the minimum
prefix/suffix budget of Corollary 6.16(2) checks out by direct computation:
`min(1,8) < 4`, `min(3,7) < 4`, `min(4,5) < 5`, `min(6,4) < 5`,
`min(8,2) < 3`. (`FORMALIZATION_NOTES.md` records that the paper's own displayed torsion
orders `4,5,5,5,3` disagree with its per-factor computations `4,4,5,5,3`;
the `k`-values used here are the correct per-factor ones, and the conclusion
is unaffected either way.) -/

@[expose] public section

namespace Bananas

open Utilities
open Utilities.Certificate SubdivisionGraph
open Utilities.Certificate.SubdivisionGraph.Spec

/-! ## The five factors -/

/-- The cycle `B_{3,1}`. -/
def bngB31 : Banana 1 := bananaOfLengths 1 ![3, 1] (by decide)

/-- The theta graph `θ_{4,1,4}`. -/
def bngTheta414 : Banana 2 := bananaOfLengths 2 ![4, 1, 4] (by decide)

/-- The cycle `B_{3,2}`. -/
def bngB32 : Banana 1 := bananaOfLengths 1 ![3, 2] (by decide)

/-- The theta graph `θ_{5,2,10}`. -/
def bngTheta5210 : Banana 2 := bananaOfLengths 2 ![5, 2, 10] (by decide)

/-- The theta graph `θ_{6,2,3}`. -/
def bngTheta623 : Banana 2 := bananaOfLengths 2 ![6, 2, 3] (by decide)

/-- `x_1` on `θ_{4,1,4}`: strand `0` (the `n_0`-strand), position `1`. -/
def bngX1 : bngTheta414.PathPosition (0 : Fin 3) := ⟨1, by decide⟩

/-- `z_1` on `θ_{4,1,4}`: strand `2` (the `n_2`-strand), position `1`. -/
def bngZ1 : bngTheta414.PathPosition (2 : Fin 3) := ⟨1, by decide⟩

/-- `x_2` on `θ_{5,2,10}`. -/
def bngX2 : bngTheta5210.PathPosition (0 : Fin 3) := ⟨2, by decide⟩

/-- `z_4` on `θ_{5,2,10}`. -/
def bngZ4 : bngTheta5210.PathPosition (2 : Fin 3) := ⟨4, by decide⟩

/-- `x_4` on `θ_{6,2,3}`. -/
def bngX4 : bngTheta623.PathPosition (0 : Fin 3) := ⟨4, by decide⟩

/-- `z_2` on `θ_{6,2,3}`. -/
def bngZ2 : bngTheta623.PathPosition (2 : Fin 3) := ⟨2, by decide⟩

theorem bngEvenlyMarked414 : EvenlyMarkedTheta bngTheta414 0 2 bngX1 bngZ1 :=
  ⟨by decide, by decide, by decide, by decide, by decide, by decide⟩

theorem bngEvenlyMarked5210 : EvenlyMarkedTheta bngTheta5210 0 2 bngX2 bngZ4 :=
  ⟨by decide, by decide, by decide, by decide, by decide, by decide⟩

theorem bngEvenlyMarked623 : EvenlyMarkedTheta bngTheta623 0 2 bngX4 bngZ2 :=
  ⟨by decide, by decide, by decide, by decide, by decide, by decide⟩

/-- Factor 1: the cycle `B_{3,1}`, torsion order `4`. -/
noncomputable def bngF1 : KGeneralChainFactor where
  marked := ⟨bngB31.graph, leftEndpoint bngB31, rightEndpoint bngB31⟩
  period := 4
  connected := banana_graph_connected bngB31
  kGeneral := by
    have hk : (bngB31.length 0 + bngB31.length 1) /
        Nat.gcd (bngB31.length 0) (bngB31.length 1) = 4 := by decide
    exact hk ▸ cycle_kGeneralTransmission bngB31

/-- Factor 2: the theta graph `θ_{4,1,4}`, marked at `(x_1, z_1)`, torsion
order `4`. -/
noncomputable def bngF2 : KGeneralChainFactor where
  marked := ⟨bngTheta414.graph, strandVertex bngTheta414 0 bngX1,
    strandVertex bngTheta414 2 bngZ1⟩
  period := 4
  connected := banana_graph_connected bngTheta414
  kGeneral := by
    have hk : bngTheta414.length 0 / Nat.gcd (bngTheta414.length 0) bngX1.val
        = 4 := by decide
    exact hk ▸ evenlyMarkedTheta_kGeneral bngTheta414 0 2 bngX1 bngZ1
      bngEvenlyMarked414

/-- Factor 3: the cycle `B_{3,2}`, torsion order `5`. -/
noncomputable def bngF3 : KGeneralChainFactor where
  marked := ⟨bngB32.graph, leftEndpoint bngB32, rightEndpoint bngB32⟩
  period := 5
  connected := banana_graph_connected bngB32
  kGeneral := by
    have hk : (bngB32.length 0 + bngB32.length 1) /
        Nat.gcd (bngB32.length 0) (bngB32.length 1) = 5 := by decide
    exact hk ▸ cycle_kGeneralTransmission bngB32

/-- Factor 4: the theta graph `θ_{5,2,10}`, marked at `(x_2, z_4)`, torsion
order `5`. -/
noncomputable def bngF4 : KGeneralChainFactor where
  marked := ⟨bngTheta5210.graph, strandVertex bngTheta5210 0 bngX2,
    strandVertex bngTheta5210 2 bngZ4⟩
  period := 5
  connected := banana_graph_connected bngTheta5210
  kGeneral := by
    have hk : bngTheta5210.length 0 / Nat.gcd (bngTheta5210.length 0) bngX2.val
        = 5 := by decide
    exact hk ▸ evenlyMarkedTheta_kGeneral bngTheta5210 0 2 bngX2 bngZ4
      bngEvenlyMarked5210

/-- Factor 5: the theta graph `θ_{6,2,3}`, marked at `(x_4, z_2)`, torsion
order `3`. -/
noncomputable def bngF5 : KGeneralChainFactor where
  marked := ⟨bngTheta623.graph, strandVertex bngTheta623 0 bngX4,
    strandVertex bngTheta623 2 bngZ2⟩
  period := 3
  connected := banana_graph_connected bngTheta623
  kGeneral := by
    have hk : bngTheta623.length 0 / Nat.gcd (bngTheta623.length 0) bngX4.val
        = 3 := by decide
    exact hk ▸ evenlyMarkedTheta_kGeneral bngTheta623 0 2 bngX4 bngZ2
      bngEvenlyMarked623

/-- The genus of each factor, read off `Spec.genus_graph`. -/
theorem bngF1_genus : genus bngF1.marked.graph = 1 := bngB31.genus_graph
theorem bngF2_genus : genus bngF2.marked.graph = 2 := bngTheta414.genus_graph
theorem bngF3_genus : genus bngF3.marked.graph = 1 := bngB32.genus_graph
theorem bngF4_genus : genus bngF4.marked.graph = 2 := bngTheta5210.genus_graph
theorem bngF5_genus : genus bngF5.marked.graph = 2 := bngTheta623.genus_graph

theorem bngChainMinBudget :
    ChainMinBudget [bngF1, bngF2, bngF3, bngF4, bngF5] := by
  intro i hi
  simp only [List.length_cons, List.length_nil] at hi
  interval_cases i <;>
    simp [chainFactorGenus, List.take, List.drop,
      bngF1, bngF2, bngF3, bngF4, bngF5]

/-- **Example 1.15** (`eg:bng`): the iterated vertex gluing of the five
factors — cycle `B_{3,1}`, evenly marked `θ_{4,1,4}` at `(x_1,z_1)`, cycle
`B_{3,2}`, evenly marked `θ_{5,2,10}` at `(x_2,z_4)`, evenly marked
`θ_{6,2,3}` at `(x_4,z_2)` — is a genus-eight Brill--Noether general graph. -/
theorem exampleBng_brillNoetherGeneral :
    BrillNoetherGeneral
      (bngF1.marked.chain
        ([bngF2, bngF3, bngF4, bngF5].map KGeneralChainFactor.marked)).graph :=
  brillNoetherGeneral_mixedTorsionChain_of_minBudget bngF1
    [bngF2, bngF3, bngF4, bngF5] bngChainMinBudget

theorem exampleBng_genus :
    genus (bngF1.marked.chain
        ([bngF2, bngF3, bngF4, bngF5].map KGeneralChainFactor.marked)).graph
      = 8 := by
  rw [MarkedGraph.genus_chain]
  simp [bngF1_genus, bngF2_genus, bngF3_genus, bngF4_genus, bngF5_genus]

end Bananas
