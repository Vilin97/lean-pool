/-
Copyright (c) 2026 Arseniy Akopyan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arseniy Akopyan
-/

import LeanPool.NandakumarRamanaRao.NRR.PrimePolyhedron.FoxNeuwirth.RouteBMixedFaceBadSetMeasurable
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import Mathlib.LinearAlgebra.Dimension.Constructions
/-!
# Route B: full mixed-face bad-set nullity

This is the concrete completion of Step 5.  After the canonical coordinate
split, fix all parameters except the complete `p`-coordinate value at the
selected retained vertex.  Any positive-ray incidence forces that selected
block into the linear span of the diagonal vector and the other `p - 2`
retained vertex blocks.  The span has dimension at most `p - 1` in a
`p`-dimensional real vector space, hence has zero Lebesgue measure.  Fubini and
the measure-preserving coordinate split give nullity of the original complete
bad set, including its existential simplex witness.
-/

namespace NRR

open FoxNeuwirthOrderComplex
open MeasureTheory
open scoped BigOperators

namespace FoxNeuwirthOrderComplex
namespace EquivariantPrismStableRelativeBoundary
namespace ExplicitAffineRelativeCollar
namespace RouteB

open AffinePositiveRayBoundary
open AffinePositiveRayBoundary.VertexMap
open Parameters
open Polynomials
open RelativeGenericity

variable {p N₀ N₁ M L : Nat}
variable (hp : Nat.Prime p)
variable (C : RelativeAffineCellSystem hp N₀ N₁ M L)

namespace MixedFaceCase

/-- Local vertices retained after deleting the two face omissions and the
selected vertex. -/
noncomputable def otherRetainedIndices
    (κ : MixedFaceCase hp C) : Finset (Fin (p + 1)) :=
  (((Finset.univ.erase κ.omitted₀).erase κ.omitted₁).erase κ.retained)

/-- There are exactly `p - 2` other retained vertices. -/
theorem card_otherRetainedIndices
    (κ : MixedFaceCase hp C) :
    (κ.otherRetainedIndices hp C).card = p - 2 := by
  classical
  have h1 : κ.omitted₁ ∈ (Finset.univ.erase κ.omitted₀ : Finset (Fin (p + 1))) := by
    simp [κ.omitted_ne.symm]
  have hr : κ.retained ∈
      ((Finset.univ.erase κ.omitted₀).erase κ.omitted₁ : Finset (Fin (p + 1))) := by
    simp [κ.retained_ne₀, κ.retained_ne₁]
  simp [otherRetainedIndices, Finset.card_erase_of_mem, h1, hr,
     κ.retained_ne₀]; omega

/-- Finite type of the other retained local vertices. -/
abbrev OtherRetainedIndex (κ : MixedFaceCase hp C) :=
  {i : Fin (p + 1) // i ∈ κ.otherRetainedIndices hp C}

/-- The selected block has cardinality `p`. -/
theorem card_selectedVectorParameter
    (κ : MixedFaceCase hp C) :
    Fintype.card (κ.SelectedVectorParameter hp C) = p := by
  simpa using Fintype.card_congr (κ.vectorParameterEquiv hp C).symm

/-- The index type consisting of the diagonal generator and the other retained
vertices has cardinality `p - 1`. -/
theorem card_option_otherRetainedIndex
    (κ : MixedFaceCase hp C) :
    Fintype.card (Option (κ.OtherRetainedIndex hp C)) = p - 1 := by
  classical
  rw [Fintype.card_option, Fintype.card_coe]
  rw [κ.card_otherRetainedIndices hp C]
  have hp2 : 2 ≤ p := hp.two_le
  omega

/-- Reconstruct the complete movable assignment from selected and remaining
blocks. -/
noncomputable def mergedParameters
    (κ : MixedFaceCase hp C)
    (u : κ.SelectedVectorParameter hp C → Real)
    (rest : κ.RemainingMovableParameter hp C → Real) :
    MovableParameterSpace hp C :=
  (κ.parameterSplit hp C).symm (u, rest)

/-- Value of a local vertex, represented in selected-block coordinate order. -/
noncomputable def localVertexBlock
    (base : Assignment hp C) (κ : MixedFaceCase hp C)
    (u : κ.SelectedVectorParameter hp C → Real)
    (rest : κ.RemainingMovableParameter hp C → Real)
    (i : Fin (p + 1)) : κ.SelectedVectorParameter hp C → Real :=
  fun q =>
    assignmentOfMovableParameters hp C base
      (κ.mergedParameters hp C u rest)
      (localParameter hp C κ.cell i ((κ.vectorParameterEquiv hp C).symm q))

/-- At the selected retained vertex, the local vertex block is exactly the
selected coordinate variable. -/
theorem localVertexBlock_retained
    (base : Assignment hp C) (κ : MixedFaceCase hp C)
    (u : κ.SelectedVectorParameter hp C → Real)
    (rest : κ.RemainingMovableParameter hp C → Real) :
    κ.localVertexBlock hp C base u rest κ.retained = u := by
  funext q
  let j : Fin p := (κ.vectorParameterEquiv hp C).symm q
  have hq : κ.vectorParameterEquiv hp C j = q :=
    (κ.vectorParameterEquiv hp C).apply_symm_apply q
  unfold localVertexBlock
  change assignmentOfMovableParameters hp C base
      (κ.mergedParameters hp C u rest)
      (κ.vectorParameter hp C j).1 = u q
  rw [assignmentOfMovableParameters_movable hp C base _
    (κ.vectorParameter hp C j)]
  change (κ.parameterSplit hp C).symm (u, rest)
      (κ.vectorParameter hp C j) = u q
  rw [← κ.vectorParameterEquiv_apply_val hp C j]
  rw [κ.parameterSplit_symm_apply_selected hp C (u, rest)
    (κ.vectorParameterEquiv hp C j), hq]

/-- At every other local vertex, the selected block has no influence. -/
theorem localVertexBlock_eq_zeroSelected_of_ne
    (base : Assignment hp C) (κ : MixedFaceCase hp C)
    (u : κ.SelectedVectorParameter hp C → Real)
    (rest : κ.RemainingMovableParameter hp C → Real)
    (i : Fin (p + 1)) (hi : i ≠ κ.retained) :
    κ.localVertexBlock hp C base u rest i =
      κ.localVertexBlock hp C base 0 rest i := by
  funext q
  let j : Fin p := (κ.vectorParameterEquiv hp C).symm q
  let s : Parameter hp C := localParameter hp C κ.cell i j
  by_cases hs : IsFrozenParameter hp C s
  · change assignmentOfMovableParameters hp C base
        (κ.mergedParameters hp C u rest) s =
      assignmentOfMovableParameters hp C base
        (κ.mergedParameters hp C 0 rest) s
    rw [assignmentOfMovableParameters_frozen hp C base _ hs,
      assignmentOfMovableParameters_frozen hp C base _ hs]
  · let sm : MovableParameter hp C := ⟨s, hs⟩
    have hmovable : ¬ IsFrozenParameter hp C
        (localParameter hp C κ.cell i j) := by
      simpa [s] using hs
    have hnot : ¬ κ.IsSelectedVectorParameter hp C sm := by
      simpa [sm, s] using
        κ.localParameter_not_selected_of_vertex_ne hp C i hi j hmovable
    let sr : κ.RemainingMovableParameter hp C := ⟨sm, hnot⟩
    change assignmentOfMovableParameters hp C base
        (κ.mergedParameters hp C u rest) sm.1 =
      assignmentOfMovableParameters hp C base
        (κ.mergedParameters hp C 0 rest) sm.1
    rw [assignmentOfMovableParameters_movable hp C base _ sm,
      assignmentOfMovableParameters_movable hp C base _ sm]
    change (κ.parameterSplit hp C).symm (u, rest) sr.1 =
      (κ.parameterSplit hp C).symm (0, rest) sr.1
    rw [κ.parameterSplit_symm_apply_remaining hp C (u, rest) sr,
      κ.parameterSplit_symm_apply_remaining hp C (0, rest) sr]

/-- The constant diagonal vector in selected-block coordinates. -/
def diagonalBlock (κ : MixedFaceCase hp C) :
    κ.SelectedVectorParameter hp C → Real :=
  fun _ => 1

/-- The finite generating family for the bad selected-vector fiber. -/
noncomputable def fiberGenerator
    (base : Assignment hp C) (κ : MixedFaceCase hp C)
    (rest : κ.RemainingMovableParameter hp C → Real) :
    Option (κ.OtherRetainedIndex hp C) →
      (κ.SelectedVectorParameter hp C → Real)
  | none => κ.diagonalBlock hp C
  | some i => κ.localVertexBlock hp C base 0 rest i.1

/-- The proper linear subspace containing the complete selected-vector bad
fiber for fixed complementary parameters. -/
noncomputable def badFiberSubmodule
    (base : Assignment hp C) (κ : MixedFaceCase hp C)
    (rest : κ.RemainingMovableParameter hp C → Real) :
    Submodule Real (κ.SelectedVectorParameter hp C → Real) :=
  Submodule.span Real (Set.range (κ.fiberGenerator hp C base rest))

/-- The fiber subspace is proper. -/
theorem badFiberSubmodule_ne_top
    (base : Assignment hp C) (κ : MixedFaceCase hp C)
    (rest : κ.RemainingMovableParameter hp C → Real) :
    κ.badFiberSubmodule hp C base rest ≠ ⊤ := by
  intro htop
  have hle : p ≤ p - 1 := by
    have h := finrank_le_of_span_eq_top
      (R := Real) (v := κ.fiberGenerator hp C base rest)
      (by simpa [badFiberSubmodule] using htop)
    simpa [Module.finrank_pi, κ.card_selectedVectorParameter hp C,
      κ.card_option_otherRetainedIndex hp C] using h
  have hp0 : 0 < p := hp.pos
  omega

/-- Decomposition of a barycentric vector sum after deleting the two zero
weights and isolating the selected retained vertex. -/
theorem weightedSum_eq_selected_add_other
    (κ : MixedFaceCase hp C) (w : StandardSimplex p)
    (V : Fin (p + 1) → (κ.SelectedVectorParameter hp C → Real))
    (h0 : w κ.omitted₀ = 0) (h1 : w κ.omitted₁ = 0) :
    (∑ i : Fin (p + 1), w i • V i) =
      w κ.retained • V κ.retained +
        ∑ i ∈ κ.otherRetainedIndices hp C, w i • V i := by
  classical
  let s0 : Finset (Fin (p + 1)) := Finset.univ.erase κ.omitted₀
  let s1 : Finset (Fin (p + 1)) := s0.erase κ.omitted₁
  have hmem0 : κ.omitted₀ ∈ (Finset.univ : Finset (Fin (p + 1))) :=
    Finset.mem_univ _
  have hmem1 : κ.omitted₁ ∈ s0 := by
    simp [s0, κ.omitted_ne.symm]
  have hmemr : κ.retained ∈ s1 := by
    simp [s1, s0, κ.retained_ne₀, κ.retained_ne₁]
  calc
    (∑ i : Fin (p + 1), w i • V i) =
        ∑ i ∈ s0, w i • V i := by
          calc
        _ = (∑ i ∈ (Finset.univ.erase κ.omitted₀), w i • V i) +
            w κ.omitted₀ • V κ.omitted₀ := by
              symm
              exact Finset.sum_erase_add _ _ hmem0
        _ = _ := by simp [s0, h0]
    _ = ∑ i ∈ s1, w i • V i := by
      calc
        _ = (∑ i ∈ (s0.erase κ.omitted₁), w i • V i) +
            w κ.omitted₁ • V κ.omitted₁ := by
              symm
              exact Finset.sum_erase_add _ _ hmem1
        _ = _ := by simp [s1, h1]
    _ = w κ.retained • V κ.retained +
        ∑ i ∈ κ.otherRetainedIndices hp C, w i • V i := by
      calc
        _ = (∑ i ∈ (s1.erase κ.retained), w i • V i) +
            w κ.retained • V κ.retained := by
              symm
              exact Finset.sum_erase_add _ _ hmemr
        _ = _ := by
          simp [s1, s0, otherRetainedIndices, add_comm]

/-- A complete bad selected-vector fiber is contained in its proper span. -/
theorem selectedFiber_subset_badFiberSubmodule
    (base : Assignment hp C) (κ : MixedFaceCase hp C)
    (rest : κ.RemainingMovableParameter hp C → Real) :
    {u : κ.SelectedVectorParameter hp C → Real |
      κ.mergedParameters hp C u rest ∈ mixedFaceBadSet hp C base κ} ⊆
      κ.badFiberSubmodule hp C base rest := by
  intro u hu
  rcases hu with ⟨w, h0, h1, hret, hdev, hmean⟩
  let S := κ.badFiberSubmodule hp C base rest
  have hdiag : κ.diagonalBlock hp C ∈ S := by
    apply Submodule.subset_span
    exact ⟨none, rfl⟩
  have hother : ∀ i ∈ κ.otherRetainedIndices hp C,
      κ.localVertexBlock hp C base 0 rest i ∈ S := by
    intro i hi
    apply Submodule.subset_span
    exact ⟨some ⟨i, hi⟩, rfl⟩
  have hsumOther :
      (∑ i ∈ κ.otherRetainedIndices hp C,
        w i • κ.localVertexBlock hp C base 0 rest i) ∈ S := by
    apply Submodule.sum_mem
    intro i hi
    exact S.smul_mem (w i) (hother i hi)
  have haffine :
      (∑ i : Fin (p + 1),
        w i • κ.localVertexBlock hp C base u rest i) =
        (mean p
          (affineValue
            (localVertexMap hp C
              (assignmentOfMovableParameters hp C base
                (κ.mergedParameters hp C u rest)) κ.cell) w)) •
          κ.diagonalBlock hp C := by
    funext q
    let j : Fin p := (κ.vectorParameterEquiv hp C).symm q
    have hcoord := coordinate_eq_lastLabel_of_deviation_eq_zero hp
      (affineValue
        (localVertexMap hp C
          (assignmentOfMovableParameters hp C base
            (κ.mergedParameters hp C u rest)) κ.cell) w) hdev j
    have hmeanlast := mean_eq_lastLabel_of_deviation_eq_zero hp
      (affineValue
        (localVertexMap hp C
          (assignmentOfMovableParameters hp C base
            (κ.mergedParameters hp C u rest)) κ.cell) w) hdev
    simp only [Pi.smul_apply, diagonalBlock, smul_eq_mul, mul_one]
    rw [hmeanlast]
    simpa [localVertexBlock, affineValue] using hcoord
  have hdecomp := κ.weightedSum_eq_selected_add_other hp C w
    (κ.localVertexBlock hp C base u rest) h0 h1
  have hotherEq : ∀ i ∈ κ.otherRetainedIndices hp C,
      κ.localVertexBlock hp C base u rest i =
        κ.localVertexBlock hp C base 0 rest i := by
    intro i hi
    have hir : i ≠ κ.retained := by
      exact (Finset.mem_erase.mp hi).1
    exact κ.localVertexBlock_eq_zeroSelected_of_ne hp C base u rest i hir
  have hsumEq :
      (∑ i ∈ κ.otherRetainedIndices hp C,
        w i • κ.localVertexBlock hp C base u rest i) =
      ∑ i ∈ κ.otherRetainedIndices hp C,
        w i • κ.localVertexBlock hp C base 0 rest i := by
    apply Finset.sum_congr rfl
    intro i hi
    rw [hotherEq i hi]
  have hscaled : w κ.retained • u ∈ S := by
    have hrhs :
        (mean p
          (affineValue
            (localVertexMap hp C
              (assignmentOfMovableParameters hp C base
                (κ.mergedParameters hp C u rest)) κ.cell) w)) •
          κ.diagonalBlock hp C -
        ∑ i ∈ κ.otherRetainedIndices hp C,
          w i • κ.localVertexBlock hp C base 0 rest i ∈ S :=
      S.sub_mem (S.smul_mem _ hdiag) hsumOther
    convert hrhs using 1
    rw [← haffine, hdecomp, κ.localVertexBlock_retained hp C base u rest,
      hsumEq]
    abel
  have hretne : w κ.retained ≠ 0 := ne_of_gt hret
  have huEq : u = (w κ.retained)⁻¹ • (w κ.retained • u) := by
    simp [hretne]
  rw [huEq]
  exact S.smul_mem _ hscaled

/-- Each selected-vector fiber has zero volume. -/
theorem volume_selectedFiber_eq_zero
    (base : Assignment hp C) (κ : MixedFaceCase hp C)
    (rest : κ.RemainingMovableParameter hp C → Real) :
    volume {u : κ.SelectedVectorParameter hp C → Real |
      κ.mergedParameters hp C u rest ∈ mixedFaceBadSet hp C base κ} = 0 := by
  apply measure_mono_null
    (κ.selectedFiber_subset_badFiberSubmodule hp C base rest)
  exact MeasureTheory.Measure.addHaar_submodule volume
    (κ.badFiberSubmodule hp C base rest)
    (κ.badFiberSubmodule_ne_top hp C base rest)

end MixedFaceCase

/-- The complete bad set in canonical split coordinates. -/
def splitMixedFaceBadSetCanonical
    (base : Assignment hp C) (κ : MixedFaceCase hp C) :
    Set ((κ.SelectedVectorParameter hp C → Real) ×
      (κ.RemainingMovableParameter hp C → Real)) :=
  (κ.parameterSplit hp C).symm ⁻¹' mixedFaceBadSet hp C base κ

/-- The split bad set is measurable. -/
theorem measurableSet_splitMixedFaceBadSetCanonical
    (base : Assignment hp C) (κ : MixedFaceCase hp C) :
    MeasurableSet (splitMixedFaceBadSetCanonical hp C base κ) := by
  exact (measurableSet_mixedFaceBadSet hp C base κ).preimage
    (κ.parameterSplit hp C).measurable_invFun

/-- Fubini proves nullity in split coordinates. -/
theorem volume_splitMixedFaceBadSetCanonical_eq_zero
    (base : Assignment hp C) (κ : MixedFaceCase hp C) :
    volume (splitMixedFaceBadSetCanonical hp C base κ) = 0 := by
  change ((volume : Measure (κ.SelectedVectorParameter hp C → Real)).prod
    (volume : Measure (κ.RemainingMovableParameter hp C → Real)))
      (splitMixedFaceBadSetCanonical hp C base κ) = 0
  rw [Measure.prod_apply_symm
    (measurableSet_splitMixedFaceBadSetCanonical hp C base κ)]
  have hfiber :
      (fun rest : κ.RemainingMovableParameter hp C → Real =>
        volume ((fun u : κ.SelectedVectorParameter hp C → Real => (u, rest)) ⁻¹'
          splitMixedFaceBadSetCanonical hp C base κ)) = 0 := by
    funext rest
    have hset :
        ((fun u : κ.SelectedVectorParameter hp C → Real => (u, rest)) ⁻¹'
            splitMixedFaceBadSetCanonical hp C base κ) =
          {u : κ.SelectedVectorParameter hp C → Real |
            κ.mergedParameters hp C u rest ∈ mixedFaceBadSet hp C base κ} := by
      ext u
      simp [splitMixedFaceBadSetCanonical, MixedFaceCase.mergedParameters]
    rw [hset]
    exact κ.volume_selectedFiber_eq_zero hp C base rest
  rw [hfiber]
  exact lintegral_zero

/-- Concrete full-set nullity theorem for every mixed-face case. -/
theorem volume_mixedFaceBadSet_eq_zero
    (base : Assignment hp C) (κ : MixedFaceCase hp C) :
    volume (mixedFaceBadSet hp C base κ) = 0 := by
  have htransport :=
    (κ.parameterSplit_measurePreserving hp C).measure_preimage_equiv
      (splitMixedFaceBadSetCanonical hp C base κ)
  have hpreimage :
      (κ.parameterSplit hp C) ⁻¹'
          splitMixedFaceBadSetCanonical hp C base κ =
        mixedFaceBadSet hp C base κ := by
    ext x
    simp [splitMixedFaceBadSetCanonical]
  rw [hpreimage] at htransport
  exact htransport.trans
    (volume_splitMixedFaceBadSetCanonical_eq_zero hp C base κ)

/-- Concrete Step 5 certificate. -/
noncomputable def mixedFaceBadSetNullCertificate
    (base : Assignment hp C) (κ : MixedFaceCase hp C) :
    MixedFaceBadSetNullCertificate hp C base κ :=
  ⟨volume_mixedFaceBadSet_eq_zero hp C base κ⟩

/-- Every positive-volume ball contains a parameter avoiding all mixed-face bad
sets, with no external nullity hypotheses. -/
theorem exists_mem_ball_avoiding_all_mixedFaceBadSets_unconditional
    (base : Assignment hp C)
    (center : MovableParameterSpace hp C) (radius : Real)
    (hball : volume (Metric.ball center radius) ≠ 0) :
    ∃ x ∈ Metric.ball center radius,
      ∀ κ : MixedFaceCase hp C, x ∉ mixedFaceBadSet hp C base κ := by
  apply exists_mem_ball_avoiding_all_mixedFaceBadSets hp C base center radius hball
  exact fun κ => mixedFaceBadSetNullCertificate hp C base κ

end RouteB
end ExplicitAffineRelativeCollar
end EquivariantPrismStableRelativeBoundary
end FoxNeuwirthOrderComplex
end NRR
