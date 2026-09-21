/-
Copyright (c) 2026 Nathan Pflueger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nathan Pflueger
-/

import LeanPool.BrillNoetherGraphs.LowGenus.AtanasovRanganathanProgram
import LeanPool.BrillNoetherGraphs.Utilities.Segments.AtanasovRanganathanConfigurations
import LeanPool.BrillNoetherGraphs.Utilities.Subdivision.ContractionForestCensusGeneral
import LeanPool.BrillNoetherGraphs.Utilities.Subdivision.ClosedFaceCensus
import LeanPool.BrillNoetherGraphs.Utilities.Subdivision.DegenerateSpec

/-!
# Genus-five Atanasov--Ranganathan configuration infrastructure

The eleven local pictures in Proposition 5.1 are not themselves the final
divisors.  For a fixed subdivision, a construction chooses an effective
degree-four divisor and, at every vertex outside its support, identifies one
of the eleven pictures and supplies the corresponding integral Dhar move.

This file packages exactly that checked output.  It deliberately does not
formalize the informal burning-subgraph notation `G_v`: the load-bearing data
is the firing script and effective residual, which is both unambiguous and
what the rank proof actually consumes.
-/

namespace AtanasovRanganathan.Configurations

open Utilities

open Certificate
open Certificate.ExplicitPotential
open Certificate.SubdivisionGraph
open Certificate.DegenerateSpec
open Utilities.Certificate.ContractionForestCensusGeneral

variable {G : CFGraph}

/-! ## Four-chip bookkeeping -/

/-- The degree-four divisor used by the genus-five pictures.  Repeated chip
positions are allowed, as required by AR's seventh family. -/
def fourChipDivisor (first second third fourth : G.V) : CFDiv G :=
  one_chip first + one_chip second + one_chip third + one_chip fourth

theorem fourChipDivisor_effective (first second third fourth : G.V) :
    effective (fourChipDivisor first second third fourth) := by
  exact (Eff G).add_mem
    ((Eff G).add_mem
      ((Eff G).add_mem (eff_one_chip first) (eff_one_chip second))
      (eff_one_chip third))
    (eff_one_chip fourth)

@[simp] theorem deg_fourChipDivisor (first second third fourth : G.V) :
    deg (fourChipDivisor first second third fourth) = 4 := by
  simp [fourChipDivisor, deg.map_add, deg_one_chip]

theorem fourChipDivisor_has_chip_first (first second third fourth : G.V) :
    1 ≤ fourChipDivisor first second third fourth first := by
  simp only [fourChipDivisor, Pi.add_apply, one_chip, ↓reduceIte]
  omega

theorem fourChipDivisor_has_chip_second (first second third fourth : G.V) :
    1 ≤ fourChipDivisor first second third fourth second := by
  simp only [fourChipDivisor, Pi.add_apply, one_chip, ↓reduceIte]
  omega

theorem fourChipDivisor_has_chip_third (first second third fourth : G.V) :
    1 ≤ fourChipDivisor first second third fourth third := by
  simp only [fourChipDivisor, Pi.add_apply, one_chip, ↓reduceIte]
  omega

theorem fourChipDivisor_has_chip_fourth (first second third fourth : G.V) :
    1 ≤ fourChipDivisor first second third fourth fourth := by
  simp only [fourChipDivisor, Pi.add_apply, one_chip, ↓reduceIte, le_add_iff_nonneg_left]
  omega

/-! ## The eleven local pictures -/

/-- Names for the eleven local configurations in Proposition 5.1, in TikZ
reading order.  Keeping the tag in construction data makes later audits say
which AR picture is being invoked at each off-support vertex. -/
inductive GenusFiveConfigurationKind where
  | first
  | second
  | third
  | fourth
  | fifth
  | sixth
  | seventh
  | eighth
  | ninth
  | tenth
  | eleventh
  deriving DecidableEq, Repr

namespace GenusFiveConfigurationKind

/-- The first six pictures form the top row of AR's figure. -/
def isTopRow : GenusFiveConfigurationKind → Bool
  | first | second | third | fourth | fifth | sixth => true
  | seventh | eighth | ninth | tenth | eleventh => false

end GenusFiveConfigurationKind

/-! ## Checked output of one global construction -/

/-- A degree-four pencil proved by AR-style local Dhar calculations.

The configuration tag is documentary; soundness comes from the accompanying
`DharMove`, whose firing script and effective residual are kernel checked. -/
structure DegreeFourDharPencil (G : CFGraph) where
  divisor : CFDiv G
  divisor_effective : effective divisor
  divisor_degree : deg divisor = 4
  move_off_support : ∀ vertex : G.V, divisor vertex = 0 →
    GenusFiveConfigurationKind × DharMove G divisor vertex

namespace DegreeFourDharPencil

/-- Package any effective degree-four rank-one divisor as an AR pencil.

The row constructions are easiest to read when they prove rank semantically
(for example by a separator argument).  The diagnostic `DharMove` fields do
not add a mathematical hypothesis: rank one says that `D - [v]` is winnable
at every vertex, and the definitions of winnability and principality expose
an effective representative and an integral firing script. -/
noncomputable def ofEffectiveRankOne (D : CFDiv G)
    (hEffective : effective D) (hDegree : deg D = 4)
    (hRank : rank G D ≥ 1) : DegreeFourDharPencil G where
  divisor := D
  divisor_effective := hEffective
  divisor_degree := hDegree
  move_off_support := by
    intro vertex _hZero
    have hWinnable :=
      (rank_ge_one_iff_winnable_sub_one_chip G D).mp hRank vertex
    let representative := Classical.choose hWinnable
    have hRepresentative := (Classical.choose_spec hWinnable).1
    have hLinear := (Classical.choose_spec hWinnable).2
    change effective representative at hRepresentative
    change linear_equiv G (D - one_chip vertex) representative at hLinear
    unfold linear_equiv at hLinear
    have hPrincipal :=
      (principal_iff_eq_prin G (representative - (D - one_chip vertex))).mp
        hLinear
    let script := Classical.choose hPrincipal
    have hScript := Classical.choose_spec hPrincipal
    refine ⟨.second, DharMove.ofScript script ?_⟩
    have hEq : D - one_chip vertex + prin G script = representative := by
      rw [← hScript]
      abel
    simpa only [hEq] using hRepresentative

/-- Package an abstract Brill--Noether existence witness as an AR pencil.

`BNExists` does not require its displayed divisor to be effective.  Rank at
least one nevertheless makes that divisor winnable, hence linearly equivalent
to an effective divisor of the same degree and rank.  This adapter is useful
for finite cone covers: each cone may use a different explicit certificate,
while the row interface still asks for the diagnostic `DharMove` package. -/
theorem nonempty_ofBNExists (existence : BNExists G 1 4) :
    Nonempty (DegreeFourDharPencil G) := by
  obtain ⟨D, hDegree, hRank⟩ := existence
  have hRankNonnegative : rank_geq G D 0 :=
    (rank_geq_iff G D 0).mpr (le_trans (by norm_num) hRank)
  have hWinnable : winnable G D :=
    (rank_nonneg_iff_winnable G D).mp hRankNonnegative
  obtain ⟨E, hEffective, hLinear⟩ :=
    (winnable_iff_exists_effective G D).mp hWinnable
  refine ⟨ofEffectiveRankOne E hEffective ?_ ?_⟩
  · exact (linear_equiv_preserves_deg G D E hLinear).symm.trans hDegree
  · rw [← rank_eq_of_linear_equiv G hLinear]
    exact hRank
theorem rank_ge_one (pencil : DegreeFourDharPencil G) :
    rank G pencil.divisor ≥ 1 := by
  apply rank_ge_one_of_dharMoves_off_support
    pencil.divisor pencil.divisor_effective
  intro vertex hZero
  exact (pencil.move_off_support vertex hZero).2

theorem bnExists (pencil : DegreeFourDharPencil G) : BNExists G 1 4 :=
  ⟨pencil.divisor, pencil.divisor_degree, pencil.rank_ge_one⟩

end DegreeFourDharPencil

/-- Uniform checked construction over every positive integral subdivision of
a fixed ordered core. -/
def PositiveSubdivisionDharConstruction {n p : ℕ}
    (core : Certificate.ExplicitPotential.Core n p)
    (core_nonempty : 0 < n)
    (core_loopless : ∀ edge : Fin p, core.tail edge ≠ core.head edge) : Prop :=
  ∀ (length : Fin p → ℕ) (length_pos : ∀ edge, 0 < length edge),
    Nonempty (DegreeFourDharPencil
      (Spec.ofCore core core_nonempty core_loopless length length_pos).graph)

/-- Forgetting the diagnostic configuration tags and explicit scripts gives
the finite-boundary pencil statement used by the global AR reduction. -/
theorem PositiveSubdivisionDharConstruction.toPositiveSubdivisionPencil
    {n p : ℕ} {core : Certificate.ExplicitPotential.Core n p}
    {core_nonempty : 0 < n}
    {core_loopless : ∀ edge : Fin p, core.tail edge ≠ core.head edge}
    (construction : PositiveSubdivisionDharConstruction
      core core_nonempty core_loopless) :
    PositiveSubdivisionPencil core core_nonempty core_loopless 4 := by
  intro length length_pos
  obtain ⟨pencil⟩ := construction length length_pos
  exact pencil.bnExists

/-! ## Closed-orthant constructions -/

/-- The zero-length slots of a closed length vector. -/
def zeroSlots {p : ℕ} (length : Fin p → ℕ) : Finset (Fin p) :=
  Finset.univ.filter (fun e => length e = 0)

@[simp] theorem mem_zeroSlots {p : ℕ} (length : Fin p → ℕ) (e : Fin p) :
    e ∈ zeroSlots length ↔ length e = 0 := by
  simp [zeroSlots]

/-- The canonical degenerate subdivision of a fixed core at a forest face.

The representative map is the union-find quotient generated by the
zero-length slots.  This is the public, unmarked counterpart of the private
row-authoring `censusSpec`; unlike a bare `DegSpec`, it cannot contain an
artificial identification unrelated to a vanishing slot. -/
def faceSpec {n p : ℕ} (core : Certificate.ExplicitPotential.Core n p)
    (core_nonempty : 0 < n) (length : Fin p → ℕ)
    (forest : IsForest core (zeroSlots length))
    (not_loopy : ¬ IsLoopy core (zeroSlots length)) :
    DegSpec n p where
  core := core
  length := length
  core_nonempty := core_nonempty
  rep := compFold core (zeroSlots length)
  rep_idem := compFold_idem core (zeroSlots length)
  rep_zero := fun e he =>
    compFold_tail_eq_head_of_mem core ((mem_zeroSlots length e).mpr he)
  rep_loopless := fun e he =>
    rep_loopless_of_not_isLoopy core not_loopy e (by simp [zeroSlots]; omega)
  forest := forest_image_add_card_eq core forest

/-- The AR-facing closed subdivision is the generic public census
subdivision.  Keeping this equality named lets structural and generated
closed-row proofs share one certificate layer without conversion boilerplate.
-/
theorem faceSpec_eq_censusSpec {n p : ℕ}
    (core : Certificate.ExplicitPotential.Core n p) (core_nonempty : 0 < n)
    (length : Fin p → ℕ)
    (forest : IsForest core (zeroSlots length))
    (not_loopy : ¬ IsLoopy core (zeroSlots length)) :
    faceSpec core core_nonempty length forest not_loopy =
      Utilities.Certificate.ClosedFaceCensus.censusSpec
        core core_nonempty length forest not_loopy := by
  apply Utilities.Certificate.ClosedFaceCensus.degSpec_ext <;> rfl

/-- A single AR construction valid on the whole genus-preserving closed
orthant of a fixed core.  This is now the primary hard-row obligation.

The only face hypotheses are the two intrinsic graph checks: the zero set is
a forest and its contraction creates no surviving loop.  Consequently one
proof covers the positive subdivision and every honest nonloopy forest face,
with no arbitrary representative map in the authoring interface. -/
def ClosedSubdivisionDharConstruction {n p : ℕ}
    (core : Certificate.ExplicitPotential.Core n p)
    (core_nonempty : 0 < n) : Prop :=
  ∀ (length : Fin p → ℕ)
    (forest : IsForest core (zeroSlots length))
    (not_loopy : ¬ IsLoopy core (zeroSlots length)),
    Nonempty (DegreeFourDharPencil
      (faceSpec core core_nonempty length forest not_loopy).graph)

/-- The interior of a closed construction is the original positive-length
AR pencil.  This is the labor-saving direction: every row is authored closed,
while its existing public `PositiveSubdivisionPencil` theorem is recovered
without row-specific endpoint or contraction arguments. -/
theorem ClosedSubdivisionDharConstruction.toPositiveSubdivisionPencil
    {n p : ℕ} {core : Certificate.ExplicitPotential.Core n p}
    {core_nonempty : 0 < n}
    (core_loopless : ∀ edge : Fin p, core.tail edge ≠ core.head edge)
    (construction : ClosedSubdivisionDharConstruction core core_nonempty) :
    PositiveSubdivisionPencil core core_nonempty core_loopless 4 := by
  intro length length_pos
  have hZeroSlots : zeroSlots length = ∅ := by
    ext e
    simp only [mem_zeroSlots]
    constructor
    · intro hZero
      have := length_pos e
      omega
    · intro hEmpty
      simp at hEmpty
  have forest : IsForest core (zeroSlots length) := by
    rw [hZeroSlots]
    simp [IsForest, compFold, edgeList, foldRep]
  have not_loopy : ¬ IsLoopy core (zeroSlots length) := by
    rw [hZeroSlots]
    rintro ⟨e, _, he⟩
    exact core_loopless e (by simpa using he)
  let d := faceSpec core core_nonempty length forest not_loopy
  obtain ⟨pencil⟩ := construction length forest not_loopy
  have hPositive : BNExists (d.toSpec length_pos).graph 1 4 :=
    (d.bnExists_toSpec_iff length_pos 1 4).mpr pencil.bnExists
  have hToSpec : d.toSpec length_pos =
      Spec.ofCore core core_nonempty core_loopless length length_pos := by
    unfold d faceSpec DegSpec.toSpec Spec.ofCore
    rfl
  rw [hToSpec] at hPositive
  exact hPositive

end AtanasovRanganathan.Configurations
