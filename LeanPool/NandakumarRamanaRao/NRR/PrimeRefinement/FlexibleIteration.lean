/-
Copyright (c) 2026 Arseniy Akopyan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arseniy Akopyan
-/
module


public import LeanPool.NandakumarRamanaRao.NRR.PrimeRefinement.Iteration
public import LeanPool.NandakumarRamanaRao.NRR.PrimeRefinement.FlexibleCore
/-!
# Model-independent prime-refinement iteration

This module repeats only the recursive constructor and final assembly, allowing each prime step to
carry the compact configuration model supplied by the obstruction proof.
-/

@[expose] public section

open MeasureTheory

namespace NRR

open Geometry

namespace FlexibleIteratedRefinement

/-- Build the full iterated refinement from the model-independent separator theorem. -/
noncomputable def build
    {K : Geometry.ConvexBody Plane}
    (H : FlexiblePrimeRefinementTheorem) :
    (ps : List PrimeFactor) →
    (A : ℝ) → (hA : 0 < A) → (hAK : A ≤ K.area) →
    (φ : NiceMV (BodySpace K (primeDescendArea A ps))) →
    IteratedRefinement ps A hA φ
  | [], A, hA, hAK, φ =>
      { output := φ
        decode := by
          intro C y hy
          exact
            { partition := IndexedConvexPartition.singleton
                (EMP.VariableBody.solidBody hA C)
              leaf := fun _ => C
              piece_eq_leaf := fun _ => rfl
              piece_area_eq := fun _ => rfl
              leaf_zero := fun _ => hy } }
  | p :: ps, A, hA, hAK, φ => by
      have hpA : 0 < A / (p.1 : ℝ) :=
        div_pos hA (by exact_mod_cast p.2.pos)
      have hpOne : (1 : ℝ) ≤ (p.1 : ℝ) := by
        exact_mod_cast p.2.one_le
      have hpAK : A / (p.1 : ℝ) ≤ K.area :=
        (div_le_self (le_of_lt hA) hpOne).trans hAK
      let inner := build H ps (A / (p.1 : ℝ)) hpA hpAK φ
      letI : Nonempty (BodySpace K A) :=
        ⟨BodySpace.parentAt K hAK⟩
      let S := Classical.choice (H p.1 p.2 K A hA inner.output)
      exact
        { output := S.certificate.toNiceMV
          decode := by
            intro C y hy
            have hlift := S.certificate.zero_lifts_to_all_children hy
            let x := hlift.choose
            have hx : ∀ i : Fin p.1,
                inner.output.Zero
                  (EMP.VariableBody.child S.model.sites hA p.2.pos (C, x) i) y := by
              intro i
              change inner.output.Zero
                (EMP.VariableBody.child S.model.sites hA p.2.pos
                  (C, hlift.choose) i) y
              exact hlift.choose_spec i
            let W := EMP.VariableBody.witness
              S.model.sites hA p.2.pos (C, x)
            let R : ∀ i : Fin p.1,
                IteratedPartitionWitness ps (A / (p.1 : ℝ)) hpA φ (W.child i) y :=
              fun i => inner.decode (W.child i) y (by
                simpa [W, EMP.VariableBody.witness] using hx i)
            refine
              { partition :=
                  { piece := fun ij => (R ij.1).partition.piece ij.2
                    subset := by
                      rintro ⟨i, j⟩ z hz
                      apply W.partition.subset i
                      rw [W.piece_eq i]
                      simpa only [EMP.VariableBody.solidBody_carrier] using
                        (R i).partition.subset j hz
                    covers := by
                      intro z hz
                      obtain ⟨i, hi⟩ := Set.mem_iUnion.mp (W.covers hz)
                      have hchild : z ∈
                          (EMP.VariableBody.solidBody hpA (W.child i) : Set Plane) := by
                        simpa only [EMP.VariableBody.solidBody_carrier] using
                          (show z ∈ ((W.child i).body : Set Plane) by
                            rw [← W.piece_eq i]
                            exact hi)
                      obtain ⟨j, hj⟩ :=
                        Set.mem_iUnion.mp ((R i).partition.covers hchild)
                      exact Set.mem_iUnion.mpr ⟨(i, j), hj⟩
                    nullOverlap := by
                      rintro ⟨i, a⟩ ⟨j, b⟩ hij
                      by_cases hfirst : i = j
                      · subst j
                        apply (R i).partition.nullOverlap a b
                        intro hab
                        apply hij
                        exact congrArg (fun t => (i, t)) hab
                      · apply measure_mono_null ?_ (W.nullOverlap i j hfirst)
                        rintro z ⟨hza, hzb⟩
                        constructor
                        · rw [W.piece_eq i]
                          simpa only [EMP.VariableBody.solidBody_carrier] using
                            (R i).partition.subset a hza
                        · rw [W.piece_eq j]
                          simpa only [EMP.VariableBody.solidBody_carrier] using
                            (R j).partition.subset b hzb }
                leaf := fun ij => (R ij.1).leaf ij.2
                piece_eq_leaf := by
                  rintro ⟨i, j⟩
                  exact (R i).piece_eq_leaf j
                piece_area_eq := by
                  rintro ⟨i, j⟩
                  rw [(R i).piece_area_eq j]
                  have hchildArea :
                      (W.child i).body.area = C.body.area / (p.1 : ℝ) := by
                    simpa [W, EMP.VariableBody.witness] using
                      EMP.VariableBody.child_area_eq
                        S.model.sites hA p.2.pos (C, x) i
                  simp [primeDescendArea, hchildArea]
                leaf_zero := by
                  rintro ⟨i, j⟩
                  exact (R i).leaf_zero j }
        }


end FlexibleIteratedRefinement

/-- **Arbitrary-number AAK theorem from the model-independent separator theorem.** -/
theorem exists_fair_partition_of_flexiblePrimeRefinement
    (H : FlexiblePrimeRefinementTheorem)
    (K : Geometry.ConvexBody Plane) (n : ℕ) (hn : 0 < n) :
    ∃ P : ConvexPartition K n, P.IsFair := by
  have hKpos : 0 < K.area := (SolidConvexBody.ofConvexBody K).area_pos
  let ps := bundledPrimeFactors n
  have hn0 : n ≠ 0 := Nat.ne_of_gt hn
  have hprod : primeFactorProduct ps = n := by
    simpa [ps] using primeFactorProduct_bundledPrimeFactors hn0
  have hbase : 0 < primeDescendArea K.area ps :=
    primeDescendArea_pos hKpos ps
  let φ := perimeterNiceMV K (primeDescendArea K.area ps) hbase
  let R := FlexibleIteratedRefinement.build H ps K.area hKpos le_rfl φ
  let C : BodySpace K K.area := BodySpace.full K
  obtain ⟨y, hy⟩ := R.output.exists_zero C
  let W := R.decode C y hy
  have hparent : EMP.VariableBody.solidBody hKpos C = K := by
    simpa [C, EMP.VariableBody.solidBody] using
      BodySpace.toGeometryConvexBody_full K hKpos
  let PI : IndexedConvexPartition K (PrimeRefinementIndex ps) :=
    W.partition.castBody hparent
  have hPIarea : PI.IsEqualArea :=
    (IndexedConvexPartition.castBody_isEqualArea hparent W.partition).2
      W.partition_isEqualArea
  have hPIperimeter : PI.HasEqualPerimeter :=
    (IndexedConvexPartition.castBody_hasEqualPerimeter hparent W.partition).2
      W.partition_hasEqualPerimeter
  rw [← hprod, ← card_primeRefinementIndex ps]
  refine ⟨PI.toConvexPartition, ?_⟩
  exact ⟨PI.toConvexPartition_isEqualArea hPIarea,
    PI.toConvexPartition_hasEqualPerimeter hPIperimeter⟩

/-- Public implication form of the Avvakumov--Akopyan--Karasev theorem.  The conclusion for every
positive number of pieces follows formally from the single prime-refinement separator theorem. -/
theorem avvakumov_akopyan_karasev_flexible
    (H : FlexiblePrimeRefinementTheorem) :
    ∀ (K : Geometry.ConvexBody Plane) (n : ℕ), 0 < n →
      ∃ P : ConvexPartition K n, P.IsFair := by
  intro K n hn
  exact exists_fair_partition_of_flexiblePrimeRefinement H K n hn


end NRR
