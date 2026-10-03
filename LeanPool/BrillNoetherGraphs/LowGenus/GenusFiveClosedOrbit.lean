/-
Copyright (c) 2026 Nathan Pflueger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nathan Pflueger
-/
module


public import LeanPool.BrillNoetherGraphs.LowGenus.GenusFiveConfigurations
public import LeanPool.BrillNoetherGraphs.LowGenus.GenusFiveCoreAtlas
public import LeanPool.BrillNoetherGraphs.Utilities.Subdivision.ClosedCoreSymmetry
public import LeanPool.BrillNoetherGraphs.Utilities.Subdivision.DegenerateSubdivisionIso

/-!
# Core automorphisms on the closed genus-five orthant

`CoreSymmetry` transports *positive* subdivisions of a fixed ordered core.
The Atanasov--Ranganathan row obligation `ClosedSubdivisionDharConstruction`
is stated on the whole closed orthant, where zero slots have already
identified core vertices, so a row proof needs the closed-face counterpart:
a core automorphism must also act on the canonical forest contraction
`faceSpec`.

That is what this module supplies.  The proofs deliberately use reachability
rather than the literal output of `compFold`: canonical union-find
representatives need not commute definitionally with a vertex permutation,
but their fibres do.  Everything below is the public restatement, at
`faceSpec`, of the shared transport `Utilities.Certificate.ClosedCoreSymmetry`.

The payoff for a row author is `closedConstruction_of_chamber`: prove the row
on any chamber `P` of length space, exhibit for each nonloopy forest face one
symmetry moving it into `P`, and the whole closed orthant follows.  Neither
the forest hypothesis nor the looplessness hypothesis has to be re-proved at
the moved face -- `isForest_iff` and `isLoopy_iff` transport them.
-/

public section

namespace AtanasovRanganathan.ClosedOrbit

open Utilities

open Certificate
open Certificate.ExplicitPotential
open Certificate.DegenerateSpec
open Utilities.Certificate.ContractionForestCensusGeneral
open Utilities.Certificate.CoreOrbitReduction
open Configurations

variable {n p : ℕ} {core : ExplicitPotential.Core n p}
variable (symmetry : CoreSymmetry core) (length : Fin p → ℕ)

/-- The length vector obtained by moving `length` along the symmetry's slot
permutation.  A row proof works at `targetLength` and concludes at
`length`. -/
abbrev targetLength : Fin p → ℕ := symmetry.reindexLength length

/-! ## The zero set moves along the slot permutation -/

theorem zero_mem_map (e : Fin p) :
    symmetry.slotPerm e ∈ zeroSlots (targetLength symmetry length) ↔
      e ∈ zeroSlots length := by
  simp [mem_zeroSlots]

/-! ## Adjacency and reachability in the contracted core -/

theorem adj_map {u v : Fin n} :
    AdjInList core (edgeList (zeroSlots length)) u v →
      AdjInList core (edgeList (zeroSlots (targetLength symmetry length)))
        (symmetry.vertexPerm u) (symmetry.vertexPerm v) :=
  Utilities.Certificate.ClosedCoreSymmetry.adj_map symmetry length

theorem adj_map_iff {u v : Fin n} :
    AdjInList core (edgeList (zeroSlots (targetLength symmetry length)))
        (symmetry.vertexPerm u) (symmetry.vertexPerm v) ↔
      AdjInList core (edgeList (zeroSlots length)) u v :=
  Utilities.Certificate.ClosedCoreSymmetry.adj_map_iff symmetry length

theorem reach_map_iff (u v : Fin n) :
    ReachIn core (zeroSlots (targetLength symmetry length))
        (symmetry.vertexPerm u) (symmetry.vertexPerm v) ↔
      ReachIn core (zeroSlots length) u v :=
  Utilities.Certificate.ClosedCoreSymmetry.reach_map_iff symmetry length u v

/-- **The fibre statement.**  Canonical union-find representatives do not
commute definitionally with a vertex permutation, but their fibres do: two
core vertices are identified at `length` exactly when their images are
identified at `targetLength`. -/
theorem rep_eq_iff (u v : Fin n) :
    compFold core (zeroSlots (targetLength symmetry length)) (symmetry.vertexPerm u) =
        compFold core (zeroSlots (targetLength symmetry length)) (symmetry.vertexPerm v) ↔
      compFold core (zeroSlots length) u = compFold core (zeroSlots length) v :=
  Utilities.Certificate.ClosedCoreSymmetry.rep_eq_iff symmetry length u v

/-- The induced bijection of contracted classes.  It is built from the fibre
statement by `Equiv.ofBijective`, never by claiming that `compFold` commutes
with `vertexPerm`. -/
noncomputable def classEquiv :
    {v : Fin n // compFold core (zeroSlots length) v = v} ≃
      {v : Fin n // compFold core (zeroSlots (targetLength symmetry length)) v = v} :=
  Utilities.Certificate.ClosedCoreSymmetry.classEquiv symmetry length

/-! ## The two face hypotheses transport -/

/-- Genus preservation is a symmetry-invariant property of a face. -/
theorem isForest_iff :
    IsForest core (zeroSlots (targetLength symmetry length)) ↔
      IsForest core (zeroSlots length) :=
  Utilities.Certificate.ClosedCoreSymmetry.isForest_iff symmetry length

/-- Surviving loops are a symmetry-invariant property of a face. -/
theorem isLoopy_iff :
    IsLoopy core (zeroSlots (targetLength symmetry length)) ↔
      IsLoopy core (zeroSlots length) :=
  Utilities.Certificate.ClosedCoreSymmetry.isLoopy_iff symmetry length

/-- The transported forest hypothesis. -/
theorem forest_target (forest : IsForest core (zeroSlots length)) :
    IsForest core (zeroSlots (targetLength symmetry length)) :=
  (isForest_iff symmetry length).2 forest

/-- The transported looplessness hypothesis. -/
theorem not_loopy_target (not_loopy : ¬ IsLoopy core (zeroSlots length)) :
    ¬ IsLoopy core (zeroSlots (targetLength symmetry length)) :=
  fun h => not_loopy ((isLoopy_iff symmetry length).1 h)

/-! ## Existence transports across the closed face -/

/-- **The closed-face relabeling induced by a core symmetry.**

`bnExists_iff` used to build this datum inline.  Naming it is what lets a
*per-vertex* statement — `StrongSeparator.Reaches` at one contracted core
class — be transported as well as a whole-graph one; see
`AtanasovRanganathan.Guarding.faceGuard_map`. The shared closed-core transport
supplies the relabeling and its vertex action. -/
noncomputable def relabeling (core_nonempty : 0 < n)
    (forest : IsForest core (zeroSlots length))
    (not_loopy : ¬ IsLoopy core (zeroSlots length)) :
    (faceSpec core core_nonempty length forest not_loopy).Relabeling
      (faceSpec core core_nonempty (targetLength symmetry length)
        (forest_target symmetry length forest)
        (not_loopy_target symmetry length not_loopy)) :=
  Utilities.Certificate.ClosedCoreSymmetry.relabeling symmetry length core_nonempty forest not_loopy

/-- The relabeling sends a contracted core class to the class of its image
under the symmetry's vertex permutation. -/
theorem vertexEquiv_relabeling_coreVertex (core_nonempty : 0 < n)
    (forest : IsForest core (zeroSlots length))
    (not_loopy : ¬ IsLoopy core (zeroSlots length)) (u : Fin n) :
    DegSpec.Relabeling.vertexEquiv _ _
        (relabeling symmetry length core_nonempty forest not_loopy)
        ((faceSpec core core_nonempty length forest not_loopy).coreVertex u) =
      (faceSpec core core_nonempty (targetLength symmetry length)
          (forest_target symmetry length forest)
          (not_loopy_target symmetry length not_loopy)).coreVertex
        (symmetry.vertexPerm u) := by
  rw [DegSpec.Relabeling.vertexEquiv_coreVertex]
  unfold DegSpec.coreVertex
  congr 1
  apply Subtype.ext
  exact (rep_eq_iff symmetry length
    ((faceSpec core core_nonempty length forest not_loopy).rep u) u).2
    ((faceSpec core core_nonempty length forest not_loopy).rep_idem u)

/-- **The closed-face transport.**  The canonical forest contraction at
`targetLength` and the one at `length` carry exactly the same Brill--Noether
existence statements. -/
theorem bnExists_iff (core_nonempty : 0 < n)
    (forest : IsForest core (zeroSlots length))
    (not_loopy : ¬ IsLoopy core (zeroSlots length)) (rank degree : ℤ) :
    BNExists
        (faceSpec core core_nonempty (targetLength symmetry length)
          (forest_target symmetry length forest)
          (not_loopy_target symmetry length not_loopy)).graph rank degree ↔
      BNExists (faceSpec core core_nonempty length forest not_loopy).graph rank degree :=
  DegSpec.Relabeling.bnExists_iff _ _
    (relabeling symmetry length core_nonempty forest not_loopy) rank degree

/-- The AR pencil form of the transport: a pencil at the moved face gives a
pencil at the original face. -/
theorem nonempty_pencil_of_target (core_nonempty : 0 < n)
    (forest : IsForest core (zeroSlots length))
    (not_loopy : ¬ IsLoopy core (zeroSlots length))
    (pencil : Nonempty (Configurations.DegreeFourDharPencil
      (faceSpec core core_nonempty (targetLength symmetry length)
        (forest_target symmetry length forest)
        (not_loopy_target symmetry length not_loopy)).graph)) :
    Nonempty (Configurations.DegreeFourDharPencil
      (faceSpec core core_nonempty length forest not_loopy).graph) := by
  obtain ⟨pencil⟩ := pencil
  refine Configurations.DegreeFourDharPencil.nonempty_ofBNExists ?_
  exact (bnExists_iff symmetry length core_nonempty forest not_loopy 1 4).1
    pencil.bnExists

/-! ## The row-authoring interface -/

/-- **The consumer corollary.**  A row is closed on the whole nonloopy forest
orthant as soon as

* `chamber`: it is proved on some chamber `P` of length space, and
* `covers`: every nonloopy forest face is carried into `P` by *some* core
  symmetry.

Both face hypotheses at the moved length vector are supplied by this lemma,
so `chamber` may assume them freely; and `covers` may pick a different
symmetry for each face, typically by `by_cases` on the chamber inequalities
with `CoreSymmetry.refl` and `CoreSymmetry.trans` composites as the
witnesses. -/
theorem closedConstruction_of_chamber {n p : ℕ} (core : ExplicitPotential.Core n p)
    (core_nonempty : 0 < n) (P : (Fin p → ℕ) → Prop)
    (covers : ∀ length : Fin p → ℕ,
      IsForest core (zeroSlots length) → ¬ IsLoopy core (zeroSlots length) →
      ∃ g : CoreSymmetry core, P (g.reindexLength length))
    (chamber : ∀ (length : Fin p → ℕ)
      (forest : IsForest core (zeroSlots length))
      (not_loopy : ¬ IsLoopy core (zeroSlots length)), P length →
      Nonempty (Configurations.DegreeFourDharPencil
        (faceSpec core core_nonempty length forest not_loopy).graph)) :
    Configurations.ClosedSubdivisionDharConstruction core core_nonempty := by
  intro length forest not_loopy
  obtain ⟨g, hP⟩ := covers length forest not_loopy
  exact nonempty_pencil_of_target g length core_nonempty forest not_loopy
    (chamber (targetLength g length) (forest_target g length forest)
      (not_loopy_target g length not_loopy) hP)

/-- The same statement with the symmetries supplied as an explicit list, the
shape generated orbit tables use. -/
theorem closedConstruction_of_orbit {n p : ℕ} (core : ExplicitPotential.Core n p)
    (core_nonempty : 0 < n) (P : (Fin p → ℕ) → Prop)
    (symmetries : List (CoreSymmetry core))
    (covers : ∀ length : Fin p → ℕ,
      IsForest core (zeroSlots length) → ¬ IsLoopy core (zeroSlots length) →
      ∃ g ∈ symmetries, P (g.reindexLength length))
    (chamber : ∀ (length : Fin p → ℕ)
      (forest : IsForest core (zeroSlots length))
      (not_loopy : ¬ IsLoopy core (zeroSlots length)), P length →
      Nonempty (Configurations.DegreeFourDharPencil
        (faceSpec core core_nonempty length forest not_loopy).graph)) :
    Configurations.ClosedSubdivisionDharConstruction core core_nonempty :=
  closedConstruction_of_chamber core core_nonempty P
    (fun length forest not_loopy => by
      obtain ⟨g, -, hP⟩ := covers length forest not_loopy
      exact ⟨g, hP⟩)
    chamber

/-! ## Smoke test: a nontrivial symmetry of the row-11 cube core

`row11Core` is the three-cube `Q₃` (outer square `0,1,3,2`, inner square
`4,5,7,6`, four rungs).  The antipodal map exchanging the two squares is a
core automorphism reversing exactly the four rung slots; both endpoint laws
are kernel-checked.  This is the shape a row author writes. -/

section RowElevenExample

open GenusFiveCoreAtlas

/-- The antipodal automorphism of the cube `row11Core`: `v ↦ v + 4`.  It
exchanges the two squares slotwise and reverses the four rungs. -/
noncomputable def rowElevenAntipode : CoreSymmetry row11Core :=
  CoreSymmetry.ofMaps row11Core
    ![4, 5, 6, 7, 0, 1, 2, 3]
    ![4, 5, 6, 7, 0, 1, 2, 3, 8, 9, 10, 11]
    ![false, false, false, false, false, false, false, false, true, true, true, true]
    (by decide) (by decide) (by decide) (by decide)

/-- Smoke test of the whole row-authoring interface at a concrete core: a
chamber proof `P`, together with the antipodal symmetry as the only orbit
element needed to reach it, closes the row on the entire nonloopy forest
orthant.  Nothing here is row-11 specific except the symmetry itself. -/
example (P : (Fin 12 → ℕ) → Prop)
    (covers : ∀ length : Fin 12 → ℕ,
      P length ∨ P (rowElevenAntipode.reindexLength length))
    (chamber : ∀ (length : Fin 12 → ℕ)
      (forest : IsForest row11Core (zeroSlots length))
      (not_loopy : ¬ IsLoopy row11Core (zeroSlots length)), P length →
      Nonempty (Configurations.DegreeFourDharPencil
        (faceSpec row11Core (by norm_num) length forest not_loopy).graph)) :
    Configurations.ClosedSubdivisionDharConstruction row11Core (by norm_num) :=
  closedConstruction_of_chamber row11Core (by norm_num) P
    (fun length _ _ => (covers length).elim
      (fun hP => ⟨CoreSymmetry.refl row11Core, by simpa using hP⟩)
      (fun hP => ⟨rowElevenAntipode, hP⟩))
    chamber

end RowElevenExample

end AtanasovRanganathan.ClosedOrbit
