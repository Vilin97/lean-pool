/-
Copyright (c) 2026 Dmitrii Zakharov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dmitrii Zakharov
-/
module


public import LeanPool.ErdosGinzburgZiv.EGZ.ConvexFlag.Basic
public import Mathlib.Analysis.LocallyConvex.Separation

/-!
# Weak convex hulls of flag points

This is Definition 3.10 and the elementary closure API around equation
`wcabsorb`.  Proposition 3.11, the finite weak-hull/projection
characterization, is stated as the geometric proof target.
-/

@[expose] public section

namespace EGZ.ConvexFlag

/-- The weak convex hull of `S`: every flag functional defined at `q` has a
defined point of `S` on the same or higher side. -/
def weakConvexHull (F : ConvexFlag) (S : Set F.Point) : Set F.Point :=
  {q | ∀ (xi : F.LinearFunction) (hq : xi.EvaluableAt q),
    ∃ s, s ∈ S ∧ ∃ hs : xi.EvaluableAt s, xi.eval q hq ≤ xi.eval s hs}

theorem mem_weakConvexHull_iff {F : ConvexFlag} {S : Set F.Point} {q : F.Point} :
    q ∈ F.weakConvexHull S ↔
      ∀ (xi : F.LinearFunction) (hq : xi.EvaluableAt q),
        ∃ s, s ∈ S ∧ ∃ hs : xi.EvaluableAt s, xi.eval q hq ≤ xi.eval s hs :=
  Iff.rfl

/-- Weak convex hull is extensive. -/
theorem subset_weakConvexHull (F : ConvexFlag) (S : Set F.Point) :
    S ⊆ F.weakConvexHull S := by
  intro q hq xi hxi
  exact ⟨q, hq, hxi, le_rfl⟩

/-- Monotonicity of weak convex hull. -/
theorem weakConvexHull_mono {F : ConvexFlag} {A B : Set F.Point} (hAB : A ⊆ B) :
    F.weakConvexHull A ⊆ F.weakConvexHull B := by
  intro q hq xi hxi
  obtain ⟨a, ha, hxa, hle⟩ := hq xi hxi
  exact ⟨a, hAB ha, hxa, hle⟩

/-- Absorption, equation `wcabsorb` in the paper. -/
theorem weakConvexHull_absorb {F : ConvexFlag} {A B : Set F.Point}
    (hAB : A ⊆ F.weakConvexHull B) :
    F.weakConvexHull A ⊆ F.weakConvexHull B := by
  intro q hq xi hxi
  obtain ⟨a, ha, hxa, hqa⟩ := hq xi hxi
  obtain ⟨b, hb, hxb, hab⟩ := hAB ha xi hxa
  exact ⟨b, hb, hxb, hqa.trans hab⟩

/-- Weak convex hull is idempotent. -/
theorem weakConvexHull_idempotent (F : ConvexFlag) (S : Set F.Point) :
    F.weakConvexHull (F.weakConvexHull S) = F.weakConvexHull S := by
  apply Set.Subset.antisymm
  · exact weakConvexHull_absorb (fun _ h ↦ h)
  · exact subset_weakConvexHull F _

/-- Evaluation is unchanged by projection.  This packages the cocycle
calculation used throughout the proof of Flag Helly. -/
theorem LinearFunction.eval_eq_of_projection {F : ConvexFlag}
    (xi : F.LinearFunction) (q q' : F.Point)
    (hbase : q'.base ≤ q.base) (hval : q.val = q'.coord hbase)
    (hq : xi.EvaluableAt q) :
    xi.eval q hq = xi.eval q' (hbase.trans hq) := by
  unfold LinearFunction.eval Point.coord
  rw [F.transition_trans hbase hq]
  change xi.toAffine ((F.transition hq).real q.val) =
    xi.toAffine ((F.transition hq).real ((F.transition hbase).real q'.val))
  rw [hval]
  rfl

/-- An affine functional takes a flag-convex combination to the weighted
average of its values on the positive support. -/
theorem ConvexCombination.eval_eq {F : ConvexFlag} {I : Type*} [Fintype I]
    {points : I → F.Point} {weight : I → ℝ} {result : F.Point}
    (c : ConvexCombination points weight result) (xi : F.LinearFunction)
    (hxi : xi.EvaluableAt result) :
    xi.eval result hxi = ∑ i : {i // 0 < weight i},
      weight i * xi.eval (points i) ((c.base_isLUB.1 i i.property).trans hxi) := by
  classical
  let A := {i : I // 0 < weight i}
  let z : A → RealCoord (F.rank xi.base) := fun i ↦
    (points i).coord ((c.base_isLUB.1 i i.property).trans hxi)
  have hs : (∑ i : A, weight i) = 1 := by
    simpa [A] using c.sum_active
  calc
    xi.eval result hxi = xi.toAffine (result.coord hxi) := rfl
    _ = xi.toAffine (∑ i : A, weight i • z i) := by
      rw [c.coord_eq hxi]
    _ = xi.toAffine
        ((Finset.univ : Finset A).affineCombination ℝ z (fun i ↦ weight i)) := by
      rw [Finset.affineCombination_eq_linear_combination _ _ _ (by simpa using hs)]
    _ = (Finset.univ : Finset A).affineCombination ℝ
        (xi.toAffine ∘ z) (fun i ↦ weight i) :=
      (Finset.univ : Finset A).map_affineCombination z (fun i ↦ weight i) hs xi.toAffine
    _ = ∑ i : A, weight i • xi.toAffine (z i) := by
      rw [Finset.affineCombination_eq_linear_combination _ _ _ (by simpa using hs)]
      rfl
    _ = ∑ i : {i // 0 < weight i},
        weight i * xi.eval (points i) ((c.base_isLUB.1 i i.property).trans hxi) := by
      apply Fintype.sum_congr
      intro i
      simp only [smul_eq_mul]
      rfl

/-- Proposition 3.11 (`pf1`): for finite input, weak hull means projection
of an ordinary flag-convex combination. -/
theorem mem_weakConvexHull_iff_exists_projection {F : ConvexFlag}
    {S : Set F.Point} (hS : S.Finite) (q : F.Point) :
    q ∈ F.weakConvexHull S ↔
      ∃ q' ∈ F.convexHull S, q.IsProjectionOf q' := by
  classical
  let T : Set (RealCoord (F.rank q.base)) :=
    {v | ∃ (s : F.Point) (hs : s ∈ S) (hbase : s.base ≤ q.base),
      s.coord hbase = v}
  have hT : T.Finite := by
    let U : Set F.Point := S ∩ {s | s.base ≤ q.base}
    have hU : U.Finite := hS.inter_of_left _
    let f : U → RealCoord (F.rank q.base) := fun s ↦ s.1.coord s.2.2
    have himage : f '' Set.univ = T := by
      ext v
      constructor
      · rintro ⟨s, -, rfl⟩
        exact ⟨s.1, s.2.1, s.2.2, rfl⟩
      · rintro ⟨s, hs, hb, rfl⟩
        exact ⟨⟨s, hs, hb⟩, Set.mem_univ _, rfl⟩
    rw [← himage]
    let : Fintype U := hU.fintype
    exact Set.Finite.image f Set.finite_univ
  constructor
  · intro hq
    have hqT : q.val ∈ _root_.convexHull ℝ T := by
      by_contra hnot
      obtain ⟨f, u, hfT, hfq⟩ := geometric_hahn_banach_closed_point
        (convex_convexHull ℝ T) (hT.isClosed_convexHull ℝ) hnot
      let xi : F.LinearFunction :=
        { base := q.base
          toAffine := f.toLinearMap.toAffineMap }
      obtain ⟨s, hsS, hsxi, hle⟩ := hq xi le_rfl
      have hsT : s.coord hsxi ∈ T := ⟨s, hsS, hsxi, rfl⟩
      have hsep := hfT (s.coord hsxi) (subset_convexHull ℝ T hsT)
      have hle' : f q.val ≤ f (s.coord hsxi) := by
        simpa [xi, LinearFunction.eval] using hle
      linarith
    obtain ⟨ι, hι, weight, z, hnonneg, hsum, hzT, hvalue⟩ :=
      mem_convexHull_iff_exists_fintype.mp hqT
    let : Fintype ι := hι
    let e : Fin (Fintype.card ι) ≃ ι := (Fintype.equivFin ι).symm
    let weight' : Fin (Fintype.card ι) → ℝ := fun i ↦ weight (e i)
    have hzData (i : Fin (Fintype.card ι)) :
        ∃ (s : F.Point) (hs : s ∈ S) (hbase : s.base ≤ q.base),
          s.coord hbase = z (e i) := hzT (e i)
    choose points hpointsS hpointsBase hpointsCoord using hzData
    have hnonneg' : ∀ i, 0 ≤ weight' i := fun i ↦ hnonneg (e i)
    have hsum' : (∑ i, weight' i) = 1 := by
      simpa [weight'] using (e.sum_comp weight).trans hsum
    obtain ⟨q', hc⟩ := exists_convexCombination points weight' hnonneg' hsum'
    have hq'base : q'.base ≤ q.base := by
      apply hc.base_isLUB.2
      intro i hi
      exact hpointsBase i
    have hactive :
        (∑ i : {i // 0 < weight' i}, weight' i • z (e i)) =
          ∑ i, weight' i • z (e i) := by
      have hinactive :
          (∑ i : {i : Fin (Fintype.card ι) // ¬ 0 < weight' i},
              weight' i • z (e i)) = 0 := by
        apply Finset.sum_eq_zero
        intro i _
        have hzero : weight' i = 0 :=
          le_antisymm (le_of_not_gt i.property) (hnonneg' i)
        simp [hzero]
      have hsplit := Fintype.sum_subtype_add_sum_subtype
        (fun i ↦ 0 < weight' i) (fun i ↦ weight' i • z (e i))
      simpa [hinactive] using hsplit
    have hcoord : q'.coord hq'base = q.val := by
      calc
        q'.coord hq'base =
            ∑ i : {i // 0 < weight' i},
              weight' i • (points i).coord
                ((hc.base_isLUB.1 i i.property).trans hq'base) := hc.coord_eq hq'base
        _ = ∑ i : {i // 0 < weight' i}, weight' i • z (e i) := by
          apply Fintype.sum_congr
          intro i
          congr 1
          simpa only using hpointsCoord i
        _ = ∑ i, weight' i • z (e i) := hactive
        _ = ∑ i, weight i • z i := by
          simpa [weight'] using e.sum_comp (fun i ↦ weight i • z i)
        _ = q.val := hvalue
    refine ⟨q', ?_, hq'base, hcoord.symm⟩
    exact ⟨Fintype.card ι, points, weight', hpointsS, hc⟩
  · rintro ⟨q', hq'hull, hproj⟩
    rcases hq'hull with ⟨n, points, weight, hpointsS, hc⟩
    rcases hproj with ⟨hbase, hval⟩
    intro xi hxi
    let A := {i : Fin n // 0 < weight i}
    have hA : Nonempty A := by
      by_contra hnone
      have hzero : ∀ i, weight i = 0 := by
        intro i
        exact le_antisymm
          (le_of_not_gt (fun hi ↦ hnone ⟨⟨i, hi⟩⟩)) (hc.nonnegative i)
      have hsum := hc.sum_eq_one
      simp [hzero] at hsum
    have heval := hc.eval_eq xi (hbase.trans hxi)
    have hprojEval := xi.eval_eq_of_projection q q' hbase hval hxi
    have hexists : ∃ i : A,
        xi.eval q hxi ≤
          xi.eval (points i) ((hc.base_isLUB.1 i i.property).trans (hbase.trans hxi)) := by
      by_contra hnone
      push Not at hnone
      have hlt :
          (∑ i : A, weight i * xi.eval (points i)
              ((hc.base_isLUB.1 i i.property).trans (hbase.trans hxi))) <
            ∑ i : A, weight i * xi.eval q hxi := by
        apply Finset.sum_lt_sum
        · intro i _
          exact (mul_le_mul_of_nonneg_left (le_of_lt (hnone i)) i.property.le)
        · let i : A := Classical.choice hA
          exact ⟨i, Finset.mem_univ i,
            mul_lt_mul_of_pos_left (hnone i) i.property⟩
      have hright : (∑ i : A, weight i * xi.eval q hxi) = xi.eval q hxi := by
        rw [← Finset.sum_mul]
        simp [A, hc.sum_active]
      rw [hright] at hlt
      have hleft :
          (∑ i : A, weight i * xi.eval (points i)
              ((hc.base_isLUB.1 i i.property).trans (hbase.trans hxi))) =
            xi.eval q hxi := heval.symm.trans hprojEval.symm
      rw [hleft] at hlt
      exact (lt_irrefl _ hlt)
    obtain ⟨i, hi⟩ := hexists
    exact ⟨points i, hpointsS i, (hc.base_isLUB.1 i i.property).trans (hbase.trans hxi), hi⟩

/-- No member of `S` lies in the weak hull of the remaining members. -/
def WeaklyConvexPosition (F : ConvexFlag) (S : Set F.Point) : Prop :=
  ∀ q ∈ S, q ∉ F.weakConvexHull (S \ {q})

end EGZ.ConvexFlag
