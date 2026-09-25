/-
Copyright (c) 2026 Nathan Pflueger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nathan Pflueger
-/
module


public import LeanPool.BrillNoetherGraphs.LowGenus.GenusFiveConfigurations
public import LeanPool.BrillNoetherGraphs.LowGenus.GenusFiveCoreAtlas
public import LeanPool.BrillNoetherGraphs.Utilities.Subdivision.CoreSymmetry
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
`faceSpec`, of the private row-proof transport `RowProof.ClosedAuto`.

The payoff for a row author is `closedConstruction_of_chamber`: prove the row
on any chamber `P` of length space, exhibit for each nonloopy forest face one
symmetry moving it into `P`, and the whole closed orthant follows.  Neither
the forest hypothesis nor the looplessness hypothesis has to be re-proved at
the moved face -- `isForest_iff` and `isLoopy_iff` transport them.
-/

@[expose] public section

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
        (symmetry.vertexPerm u) (symmetry.vertexPerm v) := by
  rintro ⟨e, he, huv⟩
  refine ⟨symmetry.slotPerm e, (mem_edgeList _ _).2 ?_, ?_⟩
  · exact (zero_mem_map symmetry length e).2 ((mem_edgeList _ _).1 he)
  · have ht := symmetry.tail_eq e
    have hh := symmetry.head_eq e
    by_cases hr : symmetry.reversed e
    · simp only [hr, ↓reduceIte] at ht hh
      rcases huv with huv | huv
      · exact Or.inr ⟨hh.trans (congrArg symmetry.vertexPerm huv.1),
          ht.trans (congrArg symmetry.vertexPerm huv.2)⟩
      · exact Or.inl ⟨ht.trans (congrArg symmetry.vertexPerm huv.1),
          hh.trans (congrArg symmetry.vertexPerm huv.2)⟩
    · have hr' : symmetry.reversed e = false := Bool.eq_false_of_not_eq_true hr
      simp only [hr', Bool.false_eq_true, ↓reduceIte] at ht hh
      rcases huv with huv | huv
      · exact Or.inl ⟨ht.trans (congrArg symmetry.vertexPerm huv.1),
          hh.trans (congrArg symmetry.vertexPerm huv.2)⟩
      · exact Or.inr ⟨hh.trans (congrArg symmetry.vertexPerm huv.1),
          ht.trans (congrArg symmetry.vertexPerm huv.2)⟩

theorem adj_map_iff {u v : Fin n} :
    AdjInList core (edgeList (zeroSlots (targetLength symmetry length)))
        (symmetry.vertexPerm u) (symmetry.vertexPerm v) ↔
      AdjInList core (edgeList (zeroSlots length)) u v := by
  constructor
  · rintro ⟨f, hf, huv⟩
    let e := symmetry.slotPerm.symm f
    have hfe : symmetry.slotPerm e = f := symmetry.slotPerm.apply_symm_apply f
    have he : e ∈ zeroSlots length := by
      apply (zero_mem_map symmetry length e).1
      simpa [hfe] using (mem_edgeList _ _).1 hf
    refine ⟨e, (mem_edgeList _ _).2 he, ?_⟩
    have ht := symmetry.tail_eq e
    have hh := symmetry.head_eq e
    rw [hfe] at ht hh
    by_cases hr : symmetry.reversed e
    · simp only [hr, ↓reduceIte] at ht hh
      rcases huv with huv | huv
      · right
        constructor
        · exact symmetry.vertexPerm.injective (huv.1.symm.trans ht) |>.symm
        · exact symmetry.vertexPerm.injective (huv.2.symm.trans hh) |>.symm
      · left
        constructor
        · exact symmetry.vertexPerm.injective (huv.1.symm.trans hh) |>.symm
        · exact symmetry.vertexPerm.injective (huv.2.symm.trans ht) |>.symm
    · have hr' : symmetry.reversed e = false := Bool.eq_false_of_not_eq_true hr
      simp only [hr', Bool.false_eq_true, ↓reduceIte] at ht hh
      rcases huv with huv | huv
      · left
        constructor
        · exact symmetry.vertexPerm.injective (huv.1.symm.trans ht) |>.symm
        · exact symmetry.vertexPerm.injective (huv.2.symm.trans hh) |>.symm
      · right
        constructor
        · exact symmetry.vertexPerm.injective (huv.1.symm.trans hh) |>.symm
        · exact symmetry.vertexPerm.injective (huv.2.symm.trans ht) |>.symm
  · exact adj_map symmetry length

theorem reach_map_iff (u v : Fin n) :
    ReachIn core (zeroSlots (targetLength symmetry length))
        (symmetry.vertexPerm u) (symmetry.vertexPerm v) ↔
      ReachIn core (zeroSlots length) u v := by
  unfold ReachIn ReachInList
  constructor
  · intro h
    simpa [Function.onFun] using Relation.ReflTransGen.lift symmetry.vertexPerm.symm
      (fun a b hab => (adj_map_iff symmetry length
        (u := symmetry.vertexPerm.symm a) (v := symmetry.vertexPerm.symm b)).1
        (by simpa using hab)) (symmetry.vertexPerm u) (symmetry.vertexPerm v) h
  · exact Relation.ReflTransGen.lift symmetry.vertexPerm
      (fun _ _ h => adj_map symmetry length h) u v

/-- **The fibre statement.**  Canonical union-find representatives do not
commute definitionally with a vertex permutation, but their fibres do: two
core vertices are identified at `length` exactly when their images are
identified at `targetLength`. -/
theorem rep_eq_iff (u v : Fin n) :
    compFold core (zeroSlots (targetLength symmetry length)) (symmetry.vertexPerm u) =
        compFold core (zeroSlots (targetLength symmetry length)) (symmetry.vertexPerm v) ↔
      compFold core (zeroSlots length) u = compFold core (zeroSlots length) v := by
  rw [compFold_iff, compFold_iff, reach_map_iff symmetry length]

/-- The induced bijection of contracted classes.  It is built from the fibre
statement by `Equiv.ofBijective`, never by claiming that `compFold` commutes
with `vertexPerm`. -/
noncomputable def classEquiv :
    {v : Fin n // compFold core (zeroSlots length) v = v} ≃
      {v : Fin n // compFold core (zeroSlots (targetLength symmetry length)) v = v} :=
  Equiv.ofBijective
    (fun x => ⟨compFold core (zeroSlots (targetLength symmetry length))
      (symmetry.vertexPerm x.val), compFold_idem _ _ _⟩)
    ⟨by
      intro x y hxy
      apply Subtype.ext
      have hrep := (rep_eq_iff symmetry length x.val y.val).1
        (congrArg Subtype.val hxy)
      simpa [x.property, y.property] using hrep,
     by
      intro y
      let z := symmetry.vertexPerm.symm y.val
      let x : {v : Fin n // compFold core (zeroSlots length) v = v} :=
        ⟨compFold core (zeroSlots length) z, compFold_idem _ _ _⟩
      refine ⟨x, Subtype.ext ?_⟩
      change compFold core (zeroSlots (targetLength symmetry length))
        (symmetry.vertexPerm (compFold core (zeroSlots length) z)) = y.val
      have hreach : ReachIn core (zeroSlots length) (compFold core (zeroSlots length) z) z :=
        (reachIn_equivalence core (zeroSlots length)).symm
          (reachIn_self_compFold core (zeroSlots length) z)
      have htarget := (reach_map_iff symmetry length
        (compFold core (zeroSlots length) z) z).2 hreach
      have hrep := (compFold_iff core _ _ _).2 htarget
      simpa [z, y.property] using hrep⟩

private theorem card_fixed_eq_image (rep : Fin n → Fin n)
    (hidem : ∀ v, rep (rep v) = rep v) :
    Fintype.card {v : Fin n // rep v = v} =
      (Finset.image rep Finset.univ).card := by
  have himage : Finset.image rep Finset.univ =
      Finset.univ.filter (fun v : Fin n => rep v = v) := by
    ext v
    constructor
    · intro hv
      obtain ⟨u, -, hu⟩ := Finset.mem_image.mp hv
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, by rw [← hu, hidem u]⟩
    · intro hv
      exact Finset.mem_image.mpr
        ⟨v, Finset.mem_univ _, (Finset.mem_filter.mp hv).2⟩
  rw [himage, Fintype.card_subtype]

private theorem zero_card_eq :
    (zeroSlots (targetLength symmetry length)).card = (zeroSlots length).card := by
  refine Finset.card_bij (fun e _ => symmetry.slotPerm.symm e) ?_ ?_ ?_
  · intro e he
    have := (zero_mem_map symmetry length (symmetry.slotPerm.symm e)).1
      (by simpa using he)
    simpa using this
  · intro a _ b _ hab
    exact symmetry.slotPerm.symm.injective hab
  · intro e he
    refine ⟨symmetry.slotPerm e, (zero_mem_map symmetry length e).2 he, ?_⟩
    simp

/-! ## The two face hypotheses transport -/

/-- Genus preservation is a symmetry-invariant property of a face. -/
theorem isForest_iff :
    IsForest core (zeroSlots (targetLength symmetry length)) ↔
      IsForest core (zeroSlots length) := by
  unfold IsForest
  have hclass := Fintype.card_congr (classEquiv symmetry length)
  rw [card_fixed_eq_image _ (compFold_idem core (zeroSlots length)),
    card_fixed_eq_image _ (compFold_idem core (zeroSlots (targetLength symmetry length)))]
    at hclass
  rw [zero_card_eq symmetry length, hclass]

/-- Surviving loops are a symmetry-invariant property of a face. -/
theorem isLoopy_iff :
    IsLoopy core (zeroSlots (targetLength symmetry length)) ↔
      IsLoopy core (zeroSlots length) := by
  unfold IsLoopy
  constructor
  · rintro ⟨f, hf, hrep⟩
    let e := symmetry.slotPerm.symm f
    have hfe : symmetry.slotPerm e = f := symmetry.slotPerm.apply_symm_apply f
    have he : e ∉ zeroSlots length := by
      intro he
      have himage := (zero_mem_map symmetry length e).2 he
      rw [hfe] at himage
      exact hf himage
    refine ⟨e, he, ?_⟩
    apply (rep_eq_iff symmetry length (core.tail e) (core.head e)).1
    have ht := symmetry.tail_eq e
    have hh := symmetry.head_eq e
    rw [hfe] at ht hh
    by_cases hr : symmetry.reversed e
    · simp only [hr, ↓reduceIte] at ht hh
      simpa [ht, hh] using hrep.symm
    · have hr' : symmetry.reversed e = false := Bool.eq_false_of_not_eq_true hr
      simp only [hr', Bool.false_eq_true, ↓reduceIte] at ht hh
      simpa [ht, hh] using hrep
  · rintro ⟨e, he, hrep⟩
    refine ⟨symmetry.slotPerm e, ?_, ?_⟩
    · exact fun h => he ((zero_mem_map symmetry length e).1 h)
    · have htarget := (rep_eq_iff symmetry length (core.tail e) (core.head e)).2 hrep
      have ht := symmetry.tail_eq e
      have hh := symmetry.head_eq e
      by_cases hr : symmetry.reversed e
      · simp only [hr, ↓reduceIte] at ht hh
        simpa [ht, hh] using htarget.symm
      · have hr' : symmetry.reversed e = false := Bool.eq_false_of_not_eq_true hr
        simp only [hr', Bool.false_eq_true, ↓reduceIte] at ht hh
        simpa [ht, hh] using htarget

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
`AtanasovRanganathan.Guarding.faceGuard_map`.  The body is the one that was
inside `bnExists_iff`, unchanged. -/
noncomputable def relabeling (core_nonempty : 0 < n)
    (forest : IsForest core (zeroSlots length))
    (not_loopy : ¬ IsLoopy core (zeroSlots length)) :
    (faceSpec core core_nonempty length forest not_loopy).Relabeling
      (faceSpec core core_nonempty (targetLength symmetry length)
        (forest_target symmetry length forest)
        (not_loopy_target symmetry length not_loopy)) :=
  let source := faceSpec core core_nonempty length forest not_loopy
  let target := faceSpec core core_nonempty (targetLength symmetry length)
    (forest_target symmetry length forest) (not_loopy_target symmetry length not_loopy)
  let ce : source.Class ≃ target.Class := classEquiv symmetry length
  have hclass : ∀ u : Fin n,
      ce ⟨source.rep u, source.rep_idem u⟩ =
        ⟨target.rep (symmetry.vertexPerm u), target.rep_idem _⟩ := fun u => by
    apply Subtype.ext
    exact (rep_eq_iff symmetry length (source.rep u) u).2 (source.rep_idem u)
  { classEquiv := ce
    slotEquiv := symmetry.slotPerm
    reversed := symmetry.reversed
    length_eq := fun e => symmetry.reindexLength_compat length e
    tail_eq := fun e => by
      by_cases hr : symmetry.reversed e
      · simp only [ite_eq_left hr]
        rw [hclass]
        apply Subtype.ext
        have ht := symmetry.tail_eq e
        simp only [hr, ↓reduceIte] at ht
        change target.rep (symmetry.vertexPerm (core.head e)) =
          target.rep (core.tail (symmetry.slotPerm e))
        rw [ht]
      · have hr' : symmetry.reversed e = false := Bool.eq_false_of_not_eq_true hr
        simp only [ite_eq_right hr]
        rw [hclass]
        apply Subtype.ext
        have ht := symmetry.tail_eq e
        simp only [hr', Bool.false_eq_true, ↓reduceIte] at ht
        change target.rep (symmetry.vertexPerm (core.tail e)) =
          target.rep (core.tail (symmetry.slotPerm e))
        rw [ht]
    head_eq := fun e => by
      by_cases hr : symmetry.reversed e
      · simp only [ite_eq_left hr]
        rw [hclass]
        apply Subtype.ext
        have hh := symmetry.head_eq e
        simp only [hr, ↓reduceIte] at hh
        change target.rep (symmetry.vertexPerm (core.tail e)) =
          target.rep (core.head (symmetry.slotPerm e))
        rw [hh]
      · have hr' : symmetry.reversed e = false := Bool.eq_false_of_not_eq_true hr
        simp only [ite_eq_right hr]
        rw [hclass]
        apply Subtype.ext
        have hh := symmetry.head_eq e
        simp only [hr', Bool.false_eq_true, ↓reduceIte] at hh
        change target.rep (symmetry.vertexPerm (core.head e)) =
          target.rep (core.head (symmetry.slotPerm e))
        rw [hh] }

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
