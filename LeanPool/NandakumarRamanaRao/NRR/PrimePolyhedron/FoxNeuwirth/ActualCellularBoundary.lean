/-
Copyright (c) 2026 Arseniy Akopyan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arseniy Akopyan
-/

import LeanPool.NandakumarRamanaRao.NRR.PrimePolyhedron.FoxNeuwirth.ModPOrbitCycle
import LeanPool.NandakumarRamanaRao.NRR.PrimePolyhedron.FoxNeuwirth.FiniteAffineZeroCount
/-!
# Actual Fox--Neuwirth top-cell boundary

The orbit coefficient calculation in `ModPOrbitCycle` records the expected binomial answer, but it
is not itself the boundary of a finite chain.  This module defines the genuine finite incidence
sum over all oriented top cells.

For a barred permutation `a`, `topExtensions a` is the finite set of top cells having `a` as a
codimension-one face.  The main reduction proves that the actual boundary coefficient is the
cardinality of this extension set, multiplied by the chosen orientation of `a`.  Consequently the
prime cycle theorem reduces to the concrete shuffle-cardinality statement for codimension-one
cells.
-/

namespace NRR

open scoped BigOperators

variable {p : Nat}

namespace FoxNeuwirth

/-- Top cells containing `a` as a codimension-one face. -/
noncomputable def topExtensions (a : BarredPermutation p) :
    Finset (BarredPermutation.TopCell p) :=
  Finset.univ.filter fun c => a.IsFacet (c : BarredPermutation p)

@[simp] theorem mem_topExtensions_iff
    (a : BarredPermutation p) (c : BarredPermutation.TopCell p) :
    c ∈ topExtensions a ↔ a.IsFacet (c : BarredPermutation p) := by
  simp [topExtensions]

/-- Number of top cells containing a given barred permutation as a facet. -/
noncomputable def topExtensionMultiplicity (a : BarredPermutation p) : Nat :=
  (topExtensions a).card

/-- The actual coefficient of `a` in the boundary of the oriented top-cell sum. -/
noncomputable def actualTopBoundaryCoefficient
    (a : BarredPermutation p) : ZMod p :=
  ∑ c : BarredPermutation.TopCell p,
    (signedIncidence a (c : BarredPermutation p) : ZMod p) *
      orientedTopCoefficient (c : BarredPermutation p)

/-- One top-cell summand is the orientation of the facet when the incidence is present, and zero
otherwise. -/
theorem actualTopBoundary_summand
    (hp : Nat.Prime p) (a : BarredPermutation p)
    (c : BarredPermutation.TopCell p) :
    (signedIncidence a (c : BarredPermutation p) : ZMod p) *
        orientedTopCoefficient (c : BarredPermutation p) =
      if a.IsFacet (c : BarredPermutation p) then
        (a.orientationSign : ZMod p)
      else 0 := by
  by_cases hfacet : a.IsFacet (c : BarredPermutation p)
  · simpa [hfacet] using
      signedIncidence_mul_orientedTopCoefficient hp hfacet c.2
  · simp [hfacet, signedIncidence_of_not_facet]

/-- The genuine boundary coefficient is the extension multiplicity times one common orientation
sign. -/
theorem actualTopBoundaryCoefficient_eq_multiplicity
    (hp : Nat.Prime p) (a : BarredPermutation p) :
    actualTopBoundaryCoefficient a =
      (topExtensionMultiplicity a : ZMod p) *
        (a.orientationSign : ZMod p) := by
  classical
  unfold actualTopBoundaryCoefficient
  calc
    (∑ c : BarredPermutation.TopCell p,
        (signedIncidence a (c : BarredPermutation p) : ZMod p) *
          orientedTopCoefficient (c : BarredPermutation p)) =
        ∑ c : BarredPermutation.TopCell p,
          if a.IsFacet (c : BarredPermutation p) then
            (a.orientationSign : ZMod p)
          else 0 := by
            apply Finset.sum_congr rfl
            intro c hc
            exact actualTopBoundary_summand hp a c
    _ = ∑ c ∈ topExtensions a, (a.orientationSign : ZMod p) := by
          rw [topExtensions, Finset.sum_filter]
    _ = (topExtensionMultiplicity a : ZMod p) *
          (a.orientationSign : ZMod p) := by
          rw [topExtensionMultiplicity, Finset.sum_const, nsmul_eq_mul]

/-- A cell outside codimension one has no top-cell extensions. -/
theorem topExtensions_eq_empty_of_dimension_ne
    (hp : Nat.Prime p) (a : BarredPermutation p)
    (ha : a.dualDimension ≠ p - 2) :
    topExtensions a = ∅ := by
  classical
  ext c
  simp only [mem_topExtensions_iff, Finset.notMem_empty, iff_false]
  intro hfacet
  apply ha
  have htop := BarredPermutation.TopCell.dimension hp c
  have hfac := hfacet.2
  omega

/-- Multiplicity vanishes away from codimension one. -/
theorem topExtensionMultiplicity_eq_zero_of_dimension_ne
    (hp : Nat.Prime p) (a : BarredPermutation p)
    (ha : a.dualDimension ≠ p - 2) :
    topExtensionMultiplicity a = 0 := by
  rw [topExtensionMultiplicity, topExtensions_eq_empty_of_dimension_ne hp a ha]
  simp

/-- A codimension-one cell has exactly one bar. -/
theorem bars_card_eq_one_of_codimOne
    (hp : Nat.Prime p) (a : BarredPermutation p)
    (ha : a.dualDimension = p - 2) :
    a.bars.card = 1 := by
  rw [BarredPermutation.dualDimension_eq a hp.pos] at ha
  have hle := BarredPermutation.bars_card_le a
  have hp2 := hp.two_le
  omega

/-- The unique bar of a codimension-one barred permutation. -/
noncomputable def facetBar
    (hp : Nat.Prime p) (a : BarredPermutation p)
    (ha : a.dualDimension = p - 2) : Fin (p - 1) :=
  Classical.choose (Finset.card_eq_one.mp (bars_card_eq_one_of_codimOne hp a ha))

/-- The bar set of a codimension-one cell is the singleton containing `facetBar`. -/
theorem bars_eq_singleton_facetBar
    (hp : Nat.Prime p) (a : BarredPermutation p)
    (ha : a.dualDimension = p - 2) :
    a.bars = {facetBar hp a ha} :=
  Classical.choose_spec
    (Finset.card_eq_one.mp (bars_card_eq_one_of_codimOne hp a ha))

/-- Size of the first ordered block of a codimension-one cell. -/
noncomputable def facetLeftSize
    (hp : Nat.Prime p) (a : BarredPermutation p)
    (ha : a.dualDimension = p - 2) : Nat :=
  (facetBar hp a ha).1 + 1

@[simp] theorem facetLeftSize_pos
    (hp : Nat.Prime p) (a : BarredPermutation p)
    (ha : a.dualDimension = p - 2) :
    0 < facetLeftSize hp a ha := by
  simp [facetLeftSize]

@[simp] theorem facetLeftSize_lt
    (hp : Nat.Prime p) (a : BarredPermutation p)
    (ha : a.dualDimension = p - 2) :
    facetLeftSize hp a ha < p := by
  unfold facetLeftSize
  have hbar := (facetBar hp a ha).2
  omega

/-- Labels in the first ordered block, expressed directly by their rank before the unique bar. -/
def FirstBlockLabel
    (hp : Nat.Prime p) (a : BarredPermutation p)
    (ha : a.dualDimension = p - 2) :=
  {i : Fin p // (a.rank i).1 < facetLeftSize hp a ha}

noncomputable instance (hp : Nat.Prime p) (a : BarredPermutation p)
    (ha : a.dualDimension = p - 2) : Fintype (FirstBlockLabel hp a ha) := by
  classical
  unfold FirstBlockLabel
  exact Fintype.ofFinite _

/-- The first block has the expected finite cardinality. -/
noncomputable def firstBlockEquivFin
    (hp : Nat.Prime p) (a : BarredPermutation p)
    (ha : a.dualDimension = p - 2) :
    FirstBlockLabel hp a ha ≃ Fin (facetLeftSize hp a ha) where
  toFun i := ⟨(a.rank i.1).1, i.2⟩
  invFun j :=
    ⟨a.rank.symm ⟨j.1, lt_trans j.2 (facetLeftSize_lt hp a ha)⟩, by
      simp⟩
  left_inv i := by
    apply Subtype.ext
    simp
  right_inv j := by
    apply Fin.ext
    simp

@[simp] theorem card_firstBlockLabel
    (hp : Nat.Prime p) (a : BarredPermutation p)
    (ha : a.dualDimension = p - 2) :
    Fintype.card (FirstBlockLabel hp a ha) = facetLeftSize hp a ha := by
  rw [Fintype.card_congr (firstBlockEquivFin hp a ha), Fintype.card_fin]

/-- Top-cell extensions as a finite subtype. -/
def TopExtension (a : BarredPermutation p) :=
  {c : BarredPermutation.TopCell p // a.IsFacet (c : BarredPermutation p)}

noncomputable instance (a : BarredPermutation p) : Fintype (TopExtension a) := by
  classical
  unfold TopExtension
  exact Fintype.ofFinite _
noncomputable instance (a : BarredPermutation p) : DecidableEq (TopExtension a) :=
  Classical.decEq _

@[simp] theorem card_topExtension (a : BarredPermutation p) :
    Fintype.card (TopExtension a) = topExtensionMultiplicity a := by
  classical
  let e : TopExtension a ≃ {c // c ∈ topExtensions a} :=
    { toFun := fun c => ⟨c.1, (mem_topExtensions_iff a c.1).2 c.2⟩
      invFun := fun c => ⟨c.1, (mem_topExtensions_iff a c.1).1 c.2⟩
      left_inv := fun c => by cases c; rfl
      right_inv := fun c => by cases c; rfl }
  rw [topExtensionMultiplicity, Fintype.card_congr e, Fintype.card_coe]

/-- Positions occupied by the first block inside a candidate top-cell order. -/
noncomputable def firstBlockPositions
    (hp : Nat.Prime p) (a : BarredPermutation p)
    (ha : a.dualDimension = p - 2)
    (c : BarredPermutation.TopCell p) : Finset (Fin p) :=
  Finset.univ.image fun i : FirstBlockLabel hp a ha =>
    (c : BarredPermutation p).rank i.1

@[simp] theorem card_firstBlockPositions
    (hp : Nat.Prime p) (a : BarredPermutation p)
    (ha : a.dualDimension = p - 2)
    (c : BarredPermutation.TopCell p) :
    (firstBlockPositions hp a ha c).card = facetLeftSize hp a ha := by
  classical
  unfold firstBlockPositions
  rw [Finset.card_image_of_injective]
  · simp [card_firstBlockLabel hp a ha]
  · intro i j hij
    apply Subtype.ext
    exact (c : BarredPermutation p).rank.injective hij

/-- Canonical map sending a top-cell extension to the positions occupied by the first block. -/
noncomputable def topExtensionToShuffle
    (hp : Nat.Prime p) (a : BarredPermutation p)
    (ha : a.dualDimension = p - 2) :
    TopExtension a → ShuffleIndex p (facetLeftSize hp a ha) :=
  fun c => ⟨firstBlockPositions hp a ha c.1,
    card_firstBlockPositions hp a ha c.1⟩

/-- Exact finite combinatorial statement needed to identify every genuine facet boundary with a
proper shuffle coefficient. -/
def FacetShuffleCardinality (p : Nat) : Prop :=
  ∀ a : BarredPermutation p,
    a.dualDimension = p - 2 →
      ∃ k : Nat, 0 < k ∧ k < p ∧
        topExtensionMultiplicity a = p.choose k

/-- Concrete bijectivity statement for the canonical extension-to-shuffle map. -/
def FacetShuffleBijection (hp : Nat.Prime p) : Prop :=
  ∀ (a : BarredPermutation p) (ha : a.dualDimension = p - 2),
    Function.Bijective (topExtensionToShuffle hp a ha)

/-- The canonical shuffle bijection implies the required cardinality formula. -/
theorem facetShuffleCardinality_of_bijection
    (hp : Nat.Prime p) (H : FacetShuffleBijection hp) :
    FacetShuffleCardinality p := by
  intro a ha
  let k := facetLeftSize hp a ha
  let e : TopExtension a ≃ ShuffleIndex p k :=
    Equiv.ofBijective (topExtensionToShuffle hp a ha) (H a ha)
  refine ⟨k, facetLeftSize_pos hp a ha, facetLeftSize_lt hp a ha, ?_⟩
  calc
    topExtensionMultiplicity a = Fintype.card (TopExtension a) :=
      (card_topExtension a).symm
    _ = Fintype.card (ShuffleIndex p k) := Fintype.card_congr e
    _ = p.choose k := ShuffleIndex.card p k

/-- The shuffle-cardinality theorem implies divisibility of every actual top-extension
multiplicity by the prime. -/
theorem prime_dvd_topExtensionMultiplicity
    (hp : Nat.Prime p) (H : FacetShuffleCardinality p)
    (a : BarredPermutation p) :
    p ∣ topExtensionMultiplicity a := by
  by_cases ha : a.dualDimension = p - 2
  · obtain ⟨k, hk0, hkp, hcard⟩ := H a ha
    rw [hcard]
    exact hp.dvd_choose hkp (by omega) le_rfl
  · rw [topExtensionMultiplicity_eq_zero_of_dimension_ne hp a ha]
    exact dvd_zero p

/-- The shuffle-cardinality theorem proves that the actual oriented top-cell sum has zero boundary
modulo `p`. -/
theorem actualTopBoundaryCoefficient_eq_zero
    (hp : Nat.Prime p) (H : FacetShuffleCardinality p)
    (a : BarredPermutation p) :
    actualTopBoundaryCoefficient a = 0 := by
  rw [actualTopBoundaryCoefficient_eq_multiplicity hp a]
  have hdivInt : (p : Int) ∣ (topExtensionMultiplicity a : Int) := by
    exact_mod_cast prime_dvd_topExtensionMultiplicity hp H a
  have hcast : ((topExtensionMultiplicity a : Int) : ZMod p) = 0 :=
    (ZMod.intCast_zmod_eq_zero_iff_dvd (topExtensionMultiplicity a : Int) p).2 hdivInt
  have hnat : (topExtensionMultiplicity a : ZMod p) = 0 := by
    exact_mod_cast hcast
  simp [hnat]

/-- The genuine finite incidence cycle obtained from the actual top-cell boundary. -/
noncomputable def actualFiniteIncidenceCycle
    (hp : Nat.Prime p) (H : FacetShuffleCardinality p) :
    FiniteIncidenceCycle (ZMod p) where
  TopCell := BarredPermutation.TopCell p
  Facet := BarredPermutation p
  incidence := fun a c =>
    (signedIncidence a (c : BarredPermutation p) : ZMod p)
  coefficient := fun c => orientedTopCoefficient (c : BarredPermutation p)
  boundary_zero := by
    intro a
    simpa [actualTopBoundaryCoefficient] using
      actualTopBoundaryCoefficient_eq_zero hp H a

end FoxNeuwirth

end NRR
