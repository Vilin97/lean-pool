/-
Copyright (c) 2026 Dmitrii Zakharov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dmitrii Zakharov
-/

import LeanPool.ErdosGinzburgZiv.EGZ.ConvexFlag.WeakHull
import LeanPool.ErdosGinzburgZiv.EGZ.ConvexFlag.ConvexHull
import Mathlib.Data.Fintype.Sigma

/-!
# Helly number of a convex flag

This file formalizes Definition 3.7 and states Theorem 3.13 (Helly's
theorem for convex flags).  The maximum in `hellyConstant` is an actual
bounded maximum: the cutoff is the number of integral points in all fibre
polytopes, which is finite by local finiteness of the fibre lattices.
-/

open scoped BigOperators

namespace EGZ.ConvexFlag

/-- Integral points in one fibre polytope, before attaching the fibre as the
base of a flag point. -/
def IntegralFiber (F : ConvexFlag) (x : F.Node) :=
  {q : RealCoord (F.rank x) //
    q ∈ (F.polytope x).carrier ∧ q ∈ F.lattice x}

noncomputable instance integralFiberFintype (F : ConvexFlag) (x : F.Node) :
    Fintype (IntegralFiber F x) := by
  exact ((F.lattice x).finite_mem_of_isCompact (F.polytope x).isCompact).fintype

/-- A finite code for all integral flag points. -/
def IntegralPointCode (F : ConvexFlag) :=
  Σ x : F.Node, IntegralFiber F x

noncomputable instance integralPointCodeFintype (F : ConvexFlag) :
    Fintype (IntegralPointCode F) := by
  unfold IntegralPointCode
  infer_instance

/-- Integral flag points are equivalent to their base together with their
integral coordinate in that fibre. -/
def integralPointEquiv (F : ConvexFlag) :
    {q : F.Point // q.IsIntegral} ≃ IntegralPointCode F where
  toFun q := ⟨q.1.base, ⟨q.1.val, q.1.val_mem, q.2⟩⟩
  invFun q := ⟨⟨q.1, q.2.1, q.2.2.1⟩, q.2.2.2⟩
  left_inv q := by
    rcases q with ⟨⟨x, q, hq⟩, hi⟩
    rfl
  right_inv q := by
    rcases q with ⟨x, q, hq, hi⟩
    rfl

noncomputable instance integralPointFintype (F : ConvexFlag) :
    Fintype {q : F.Point // q.IsIntegral} :=
  Fintype.ofEquiv (IntegralPointCode F) (integralPointEquiv F).symm

/-- The number of integral points in all fibre polytopes.  This counts the
same real coordinate separately at different bases, as required for flag
points. -/
noncomputable def integralPointCount (F : ConvexFlag) : ℕ :=
  Fintype.card {q : F.Point // q.IsIntegral}

/-- A finite indexed family has the extremal property from Definition 3.7:
its points are pairwise distinct proper integer points, and an integral
convex combination of them must put coefficient one on one of the inputs.

The conclusion is deliberately about the coefficient, rather than merely
about equality of the resulting flag point with an input; these conditions
are not equivalent for flags. -/
structure HellyIndependent {F : ConvexFlag} (Ω : F.ProperPointSet) {n : ℕ}
    (points : Fin n → F.Point) : Prop where
  injective : Function.Injective points
  proper : ∀ i, points i ∈ Ω
  integral : ∀ i, (points i).IsIntegral
  only_trivial : ∀ (weight : Fin n → ℝ) (result : F.Point),
    ConvexCombination points weight result → result.IsIntegral →
      ∃ i, weight i = 1

namespace HellyIndependent

/-- A Helly-independent family cannot have more members than there are
integral flag points. -/
theorem card_le_integralPointCount {F : ConvexFlag} {Ω : F.ProperPointSet}
    {n : ℕ} {points : Fin n → F.Point} (h : HellyIndependent Ω points) :
    n ≤ integralPointCount F := by
  let f : Fin n → {q : F.Point // q.IsIntegral} :=
    fun i ↦ ⟨points i, h.integral i⟩
  have hf : Function.Injective f := by
    intro i j hij
    apply h.injective
    exact congrArg Subtype.val hij
  simpa [integralPointCount] using Fintype.card_le_of_injective f hf

/-- The empty indexed family has the extremal property vacuously: no convex
combination on an empty index type can have total weight one. -/
theorem empty (F : ConvexFlag) (Ω : F.ProperPointSet) :
    HellyIndependent Ω (fun i : Fin 0 ↦ Fin.elim0 i) := by
  refine ⟨fun i ↦ Fin.elim0 i, fun i ↦ Fin.elim0 i,
    fun i ↦ Fin.elim0 i, ?_⟩
  intro weight result hcomb _
  exfalso
  have hzero : (∑ i, weight i) = 0 := by simp
  exact zero_ne_one (hzero ▸ hcomb.sum_eq_one)

/-- Every proper integral singleton is Helly-independent. -/
theorem singleton {F : ConvexFlag} {Ω : F.ProperPointSet} {q : F.Point}
    (hqΩ : q ∈ Ω) (hqint : q.IsIntegral) :
    HellyIndependent Ω (fun _ : Fin 1 ↦ q) := by
  refine ⟨fun _ _ _ ↦ Subsingleton.elim _ _, fun _ ↦ hqΩ,
    fun _ ↦ hqint, ?_⟩
  intro weight result hcomb _
  refine ⟨0, ?_⟩
  simpa using hcomb.sum_eq_one

end HellyIndependent

/-- Definition 3.7: the Helly constant of a convex flag with designated
proper points. -/
noncomputable def hellyConstant {F : ConvexFlag} (Ω : F.ProperPointSet) : ℕ :=
  @Nat.findGreatest
    (fun n ↦ ∃ points : Fin n → F.Point, HellyIndependent Ω points)
    (Classical.decPred _)
    (integralPointCount F)

/-- The defining maximum is attained. -/
theorem hellyConstant_spec {F : ConvexFlag} (Ω : F.ProperPointSet) :
    ∃ points : Fin (hellyConstant Ω) → F.Point,
      HellyIndependent Ω points := by
  classical
  unfold hellyConstant
  exact Nat.findGreatest_spec
    (P := fun n ↦ ∃ points : Fin n → F.Point, HellyIndependent Ω points)
    (n := integralPointCount F) (Nat.zero_le _)
    ⟨fun i : Fin 0 ↦ Fin.elim0 i, HellyIndependent.empty F Ω⟩

/-- Maximality of the Helly constant. -/
theorem HellyIndependent.card_le_hellyConstant {F : ConvexFlag}
    {Ω : F.ProperPointSet} {n : ℕ} {points : Fin n → F.Point}
    (h : HellyIndependent Ω points) : n ≤ hellyConstant Ω := by
  classical
  unfold hellyConstant
  exact Nat.le_findGreatest h.card_le_integralPointCount ⟨points, h⟩

/-- The Helly constant is bounded by the finite population of integral flag
points. -/
theorem hellyConstant_le_integralPointCount {F : ConvexFlag}
    (Ω : F.ProperPointSet) : hellyConstant Ω ≤ integralPointCount F := by
  classical
  unfold hellyConstant
  exact Nat.findGreatest_le _

/-- A proper integral point forces the Helly constant to be positive. -/
theorem hellyConstant_pos {F : ConvexFlag} {Ω : F.ProperPointSet}
    {q : F.Point} (hqΩ : q ∈ Ω) (hqint : q.IsIntegral) :
    0 < hellyConstant Ω := by
  exact (HellyIndependent.singleton hqΩ hqint).card_le_hellyConstant

/-- A proper integral point common to the weak hulls of a family of sets. -/
def HasCommonWeakHullPoint {F : ConvexFlag} (Ω : F.ProperPointSet)
    (ℱ : Set (Set F.Point)) : Prop :=
  ∃ q, q ∈ Ω ∧ q.IsIntegral ∧
    ∀ S ∈ ℱ, q ∈ F.weakConvexHull S

/-- The points of an indexed family other than the point with index `i`. -/
private def deletion {F : ConvexFlag} {I : Type*} (points : I → F.Point) (i : I) :
    Set F.Point :=
  {q | ∃ j, j ≠ i ∧ points j = q}

private theorem mem_weakConvexHull_singleton_of_projection {F : ConvexFlag}
    {q q' : F.Point} (h : q.IsProjectionOf q') :
    q ∈ F.weakConvexHull ({q'} : Set F.Point) := by
  rcases h with ⟨hbase, hval⟩
  intro xi hxi
  refine ⟨q', Set.mem_singleton q', hbase.trans hxi, ?_⟩
  exact le_of_eq (xi.eval_eq_of_projection q q' hbase hval hxi)

private theorem Point.eq_of_projection_of_base_le {F : ConvexFlag}
    {q q' : F.Point} (h : q.IsProjectionOf q') (hle : q.base ≤ q'.base) : q = q' := by
  rcases h with ⟨hge, hval⟩
  have hb : q.base = q'.base := le_antisymm hle hge
  cases q with
  | mk qb qv hqv =>
    cases q' with
    | mk qb' qv' hqv' =>
      dsimp only at hb
      subst qb'
      congr
      simpa only [Point.coord_base] using hval

private theorem ConvexCombination.mem_convexHull_of_active_mem
    {F : ConvexFlag} {I : Type*} [Fintype I]
    {points : I → F.Point} {weight : I → ℝ} {result : F.Point}
    (c : ConvexCombination points weight result) {S : Set F.Point}
    (hS : ∀ i, 0 < weight i → points i ∈ S) : result ∈ F.convexHull S := by
  classical
  let A := {i : I // 0 < weight i}
  let pointA : A → F.Point := fun i ↦ points i
  let weightA : A → ℝ := fun i ↦ weight i
  have hcombA : ConvexCombination pointA weightA result := by
    refine ⟨fun i ↦ i.property.le, c.sum_active, ?_, ?_⟩
    · constructor
      · intro i _
        exact c.base_isLUB.1 i.1 i.2
      · intro x hx
        apply c.base_isLUB.2
        intro i hi
        exact hx ⟨i, hi⟩ hi
    · let e : {i : A // 0 < weightA i} ≃ A :=
        Equiv.subtypeUnivEquiv (fun i : A ↦ i.2)
      have hsum := e.sum_comp (fun i : A ↦
        weight i.1 • (points i.1).coord (c.base_isLUB.1 i.1 i.2))
      rw [c.val_eq]
      simpa only [e, Equiv.subtypeUnivEquiv, Equiv.coe_fn_mk,
        pointA, weightA] using hsum.symm
  let e : Fin (Fintype.card A) ≃ A := (Fintype.equivFin A).symm
  exact ⟨Fintype.card A, pointA ∘ e, weightA ∘ e,
    fun i ↦ hS (e i).1 (e i).2, hcombA.reindex e⟩

private theorem ConvexCombination.coord_eq_of_pos {F : ConvexFlag}
    {I : Type*} [Fintype I] {points : I → F.Point} {weight : I → ℝ}
    {result : F.Point} (c : ConvexCombination points weight result)
    (hpos : ∀ i, 0 < weight i) {y : F.Node} (hy : result.base ≤ y) :
    result.coord hy = ∑ i, weight i • (points i).coord
      ((c.base_isLUB.1 i (hpos i)).trans hy) := by
  classical
  let e : {i : I // 0 < weight i} ≃ I := Equiv.subtypeUnivEquiv hpos
  have hsum := e.sum_comp (fun i : I ↦
    weight i • (points i).coord ((c.base_isLUB.1 i (hpos i)).trans hy))
  rw [c.coord_eq hy]
  simpa only [e, Equiv.subtypeUnivEquiv, Equiv.coe_fn_mk] using hsum

private theorem ConvexCombination.result_eq_of_active_eq {F : ConvexFlag}
    {I : Type*} [Fintype I] {points : I → F.Point} {weight : I → ℝ}
    {result q : F.Point} (c : ConvexCombination points weight result)
    (h : ∀ i, 0 < weight i → points i = q) : result = q := by
  classical
  have hactive : ∃ i, 0 < weight i := by
    by_contra hn
    push Not at hn
    have hz : ∀ i, weight i = 0 := fun i ↦
      le_antisymm (hn i) (c.nonnegative i)
    have hs := c.sum_eq_one
    simp [hz] at hs
  have hrq : result.base ≤ q.base := by
    apply c.base_isLUB.2
    intro i hi
    rw [h i hi]
  have hqr : q.base ≤ result.base := by
    obtain ⟨i, hi⟩ := hactive
    simpa only [h i hi] using c.base_isLUB.1 i hi
  have hb : result.base = q.base := le_antisymm hrq hqr
  cases result with
  | mk rb rv hrmem =>
    cases q with
    | mk qb qv hqmem =>
      dsimp only at hb
      subst qb
      congr
      calc
        rv = ∑ i : {i // 0 < weight i}, weight i •
            (points i).coord (c.base_isLUB.1 i i.property) := c.val_eq
        _ = ∑ i : {i // 0 < weight i}, weight i • qv := by
          apply Fintype.sum_congr
          intro i
          have hp :
              ({ base := rb, val := qv, val_mem := hqmem } : F.Point).IsProjectionOf
                (points i) := by
            rw [h i i.property]
            exact ⟨le_rfl, (Point.coord_base _).symm⟩
          rcases hp with ⟨hib, hiv⟩
          congr 1
          simpa only using hiv.symm
        _ = qv := by rw [← Finset.sum_smul, c.sum_active, one_smul]

private theorem exists_strictSeparator_of_not_mem_weakConvexHull
    {F : ConvexFlag} {S : Set F.Point} {q : F.Point}
    (h : q ∉ F.weakConvexHull S) :
    ∃ (xi : F.LinearFunction) (hq : xi.EvaluableAt q),
      ∀ s ∈ S, ∀ hs : xi.EvaluableAt s, xi.eval s hs < xi.eval q hq := by
  unfold weakConvexHull at h
  simp only [Set.mem_ofPred_eq] at h
  push Not at h
  obtain ⟨xi, hq, hxi⟩ := h
  refine ⟨xi, hq, ?_⟩
  intro s hsS hs
  simpa only using hxi s hsS hs

private theorem LinearFunction.eval_congr_point {F : ConvexFlag}
    (xi : F.LinearFunction) {q q' : F.Point} (hqq' : q = q')
    (hq : xi.EvaluableAt q) (hq' : xi.EvaluableAt q') :
    xi.eval q hq = xi.eval q' hq' := by
  subst q'
  rfl

/-- If a nontrivial convex combination projects to one input, it lies in
the weak hull of all the other inputs.  This is the normalization calculation
in the first paragraph of the flagged Doignon argument. -/
private theorem mem_weakConvexHull_deletion_of_combination_projection
    {F : ConvexFlag} {I : Type*} [Fintype I]
    {points : I → F.Point} {weight : I → ℝ} {result : F.Point}
    (c : ConvexCombination points weight result) (j : I)
    (hjlt : weight j < 1) (hproj : result.IsProjectionOf (points j)) :
    result ∈ F.weakConvexHull (deletion points j) := by
  classical
  by_cases hjzero : weight j = 0
  · let A := {i : I // 0 < weight i}
    let pointA : A → F.Point := fun i ↦ points i
    let weightA : A → ℝ := fun i ↦ weight i
    have hcombA : ConvexCombination pointA weightA result := by
      refine ⟨fun i ↦ i.property.le, c.sum_active, ?_, ?_⟩
      · constructor
        · intro i _
          exact c.base_isLUB.1 i.1 i.2
        · intro x hx
          apply c.base_isLUB.2
          intro i hi
          exact hx ⟨i, hi⟩ hi
      · let e : {i : A // 0 < weightA i} ≃ A :=
          Equiv.subtypeUnivEquiv (fun i : A ↦ i.2)
        have hsum := e.sum_comp (fun i : A ↦
          weight i.1 • (points i.1).coord (c.base_isLUB.1 i.1 i.2))
        rw [c.val_eq]
        simpa only [e, Equiv.subtypeUnivEquiv, Equiv.coe_fn_mk,
          pointA, weightA] using hsum.symm
    have hmemA : ∀ i, pointA i ∈ deletion points j := by
      intro i
      exact ⟨i.1, fun h ↦ by simpa [h, hjzero] using i.2, rfl⟩
    have hhull : result ∈ F.convexHull (deletion points j) := by
      let e : Fin (Fintype.card A) ≃ A := (Fintype.equivFin A).symm
      exact ⟨Fintype.card A, pointA ∘ e, weightA ∘ e,
        fun i ↦ hmemA (e i), hcombA.reindex e⟩
    have hdel : (deletion points j).Finite :=
      (Set.finite_range points).subset (by
        rintro x ⟨i, -, rfl⟩
        exact ⟨i, rfl⟩)
    exact (mem_weakConvexHull_iff_exists_projection hdel result).2
      ⟨result, hhull, le_rfl, (Point.coord_base result).symm⟩
  · have hjpos : 0 < weight j := lt_of_le_of_ne (c.nonnegative j) (Ne.symm hjzero)
    let A := {i : I // 0 < weight i}
    let jj : A := ⟨j, hjpos⟩
    let B := {i : A // i ≠ jj}
    let pointB : B → F.Point := fun i ↦ points i.1.1
    let weightB : B → ℝ := fun i ↦ weight i.1.1 / (1 - weight j)
    have hdenom : 0 < 1 - weight j := sub_pos.mpr hjlt
    have hsumBraw : (∑ i : B, weight i.1.1) = 1 - weight j := by
      have hsub : (∑ i : B, weight i.1.1) =
          ∑ i ∈ (Finset.univ.erase jj : Finset A), weight i.1 := by
        symm
        apply Finset.sum_subtype
        intro i
        simp only [Finset.mem_erase, Finset.mem_univ, and_true]
      have herase := Finset.sum_erase_add (Finset.univ : Finset A)
        (fun i : A ↦ weight i.1) (Finset.mem_univ jj)
      rw [← hsub, c.sum_active] at herase
      simpa only [jj] using (eq_sub_of_add_eq herase)
    have hsumB : (∑ i : B, weightB i) = 1 := by
      simp only [weightB, div_eq_mul_inv]
      rw [← Finset.sum_mul, hsumBraw]
      exact mul_inv_cancel₀ hdenom.ne'
    have hposB : ∀ i, 0 < weightB i := by
      intro i
      exact div_pos i.1.2 hdenom
    obtain ⟨lift, hcomb⟩ := exists_convexCombination pointB weightB
      (fun i ↦ (hposB i).le) hsumB
    have hliftBase : lift.base ≤ result.base := by
      apply hcomb.base_isLUB.2
      intro i _
      exact c.base_isLUB.1 i.1.1 i.1.2
    rcases hproj with ⟨hjbase, hresult⟩
    have hliftCoord : lift.coord hliftBase = result.val := by
      let v : A → RealCoord (F.rank result.base) := fun i ↦
        (points i.1).coord (c.base_isLUB.1 i.1 i.2)
      have hvjj : v jj = result.val := by
        simpa only [v, jj] using hresult.symm
      have hsubVec : (∑ i : B, weight i.1.1 • v i.1) =
          ∑ i ∈ (Finset.univ.erase jj : Finset A), weight i.1 • v i := by
        symm
        apply Finset.sum_subtype
        intro i
        simp only [Finset.mem_erase, Finset.mem_univ, and_true]
      have hsplit := Finset.sum_erase_add (Finset.univ : Finset A)
        (fun i : A ↦ weight i.1 • v i) (Finset.mem_univ jj)
      have horiginal : result.val = ∑ i : A, weight i.1 • v i := by
        simpa only [A, v] using c.val_eq
      have hraw : (∑ i : B, weight i.1.1 • v i.1) =
          (1 - weight j) • result.val := by
        have hsplit' : (∑ i : B, weight i.1.1 • v i.1) + weight jj.1 • v jj =
            ∑ i : A, weight i.1 • v i := by
          rw [hsubVec]
          exact hsplit
        rw [← horiginal, hvjj] at hsplit'
        ext k
        have hk := congrFun hsplit' k
        simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul] at hk ⊢
        linarith
      calc
        lift.coord hliftBase = ∑ i : B, weightB i •
            (pointB i).coord ((hcomb.base_isLUB.1 i (hposB i)).trans hliftBase) :=
          hcomb.coord_eq_of_pos hposB hliftBase
        _ = ∑ i : B, weightB i • v i.1 := by
          apply Fintype.sum_congr
          intro i
          congr 1
        _ = result.val := by
          ext k
          have hrawk := congrFun hraw k
          simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul,
            weightB, div_eq_mul_inv] at hrawk ⊢
          calc
            (∑ x : B, weight x.1.1 * (1 - weight j)⁻¹ * v x.1 k) =
                (∑ x : B, weight x.1.1 * v x.1 k) * (1 - weight j)⁻¹ := by
              rw [Finset.sum_mul]
              apply Finset.sum_congr rfl
              intro i _
              ring
            _ = result.val k := by
              rw [hrawk]
              field_simp
    have hliftHull : lift ∈ F.convexHull (deletion points j) := by
      let e : Fin (Fintype.card B) ≃ B := (Fintype.equivFin B).symm
      refine ⟨Fintype.card B, pointB ∘ e, weightB ∘ e, ?_, hcomb.reindex e⟩
      intro i
      exact ⟨(e i).1.1, fun h ↦ (e i).2 (Subtype.ext h), rfl⟩
    have hdel : (deletion points j).Finite :=
      (Set.finite_range points).subset (by
        rintro x ⟨i, -, rfl⟩
        exact ⟨i, rfl⟩)
    exact (mem_weakConvexHull_iff_exists_projection hdel result).2
      ⟨lift, hliftHull, hliftBase, hliftCoord.symm⟩

/-- The flagged Doignon step used in the proof of Flag Helly. -/
private theorem flaggedDoignon {F : ConvexFlag} (Ω : F.ProperPointSet)
    {I : Type*} [Fintype I] (points : I → F.Point)
    (hinjective : Function.Injective points)
    (hproper : ∀ i, points i ∈ Ω)
    (hintegral : ∀ i, (points i).IsIntegral)
    (hlarge : hellyConstant Ω < Fintype.card I) :
    ∃ q, q ∈ Ω ∧ q.IsIntegral ∧
      ∀ i, q ∈ F.weakConvexHull (deletion points i) := by
  classical
  by_contra hconclusion
  push Not at hconclusion
  let Counterexample : (I → F.Point) → Prop := fun p ↦
    Function.Injective p ∧
    (∀ i, p i ∈ Ω) ∧
    (∀ i, (p i).IsIntegral) ∧
    ∀ q, q ∈ Ω → q.IsIntegral →
      ∃ i, q ∉ F.weakConvexHull (deletion p i)
  have hcounterPoints : Counterexample points :=
    ⟨hinjective, hproper, hintegral, hconclusion⟩
  let hullScore (p : I → F.Point) : ℕ :=
    (Finset.univ.filter fun q : {q : F.Point // q.IsIntegral} ↦
      q.1 ∈ Ω ∧ q.1 ∈ F.weakConvexHull (Set.range p)).card
  let ScoreWitness : ℕ → Prop := fun k ↦
    ∃ p : I → F.Point, Counterexample p ∧ hullScore p = k
  have hScoreWitness : ∃ k, ScoreWitness k :=
    ⟨hullScore points, points, hcounterPoints, rfl⟩
  let minimumScore := Nat.find hScoreWitness
  obtain ⟨p, hp, hscorep⟩ := Nat.find_spec hScoreWitness
  have hminimal {p' : I → F.Point} (hp' : Counterexample p') :
      hullScore p ≤ hullScore p' := by
    calc
      hullScore p = minimumScore := hscorep
      _ ≤ hullScore p' := Nat.find_min' hScoreWitness ⟨p', hp', rfl⟩
  have hweakExtreme (i : I) :
      p i ∉ F.weakConvexHull (deletion p i) := by
    obtain ⟨j, hj⟩ := hp.2.2.2 (p i) (hp.2.1 i) (hp.2.2.1 i)
    have hji : j = i := by
      by_contra hne
      exact hj (subset_weakConvexHull F (deletion p j) ⟨i, Ne.symm hne, rfl⟩)
    simpa only [hji] using hj
  let e : Fin (Fintype.card I) ≃ I := (Fintype.equivFin I).symm
  have hnotIndependent : ¬ HellyIndependent Ω (p ∘ e) := by
    intro h
    have hcard := h.card_le_hellyConstant
    have : Fintype.card I ≤ hellyConstant Ω := by simpa [e] using hcard
    exact (not_le_of_gt hlarge) this
  have hbadCombination :
      ∃ (weight : Fin (Fintype.card I) → ℝ) (r : F.Point),
        ConvexCombination (p ∘ e) weight r ∧ r.IsIntegral ∧
          ¬ ∃ i, weight i = 1 := by
    by_contra hnone
    apply hnotIndependent
    refine ⟨hp.1.comp e.injective, fun i ↦ hp.2.1 (e i),
      fun i ↦ hp.2.2.1 (e i), ?_⟩
    intro weight r hc hrint
    by_contra htrivial
    exact hnone ⟨weight, r, hc, hrint, htrivial⟩
  obtain ⟨weight, r₀, hc₀, hr₀int, hnoOne⟩ := hbadCombination
  let weightI : I → ℝ := weight ∘ e.symm
  have hcI : ConvexCombination p weightI r₀ := by
    simpa only [weightI, Function.comp_apply, Function.comp_def,
      e.apply_symm_apply] using hc₀.reindex e.symm
  have hweightLt (i : I) : weightI i < 1 := by
    have hle : weightI i ≤ ∑ j, weightI j :=
      Finset.single_le_sum (fun j _ ↦ hcI.nonnegative j) (Finset.mem_univ i)
    rw [hcI.sum_eq_one] at hle
    apply lt_of_le_of_ne hle
    intro hi
    apply hnoOne
    exact ⟨e.symm i, by simpa only [weightI, Function.comp_apply] using hi⟩
  have hr₀Ω : r₀ ∈ Ω := by
    apply Ω.convex_closed
    exact ⟨Fintype.card I, p ∘ e, weight,
      fun i ↦ hp.2.1 (e i), hc₀⟩
  have hfiniteRange : (Set.range p).Finite := Set.finite_range p
  have hr₀Hull : r₀ ∈ F.convexHull (Set.range p) :=
    ⟨Fintype.card I, p ∘ e, weight, fun i ↦ ⟨e i, rfl⟩, hc₀⟩
  have hr₀Weak : r₀ ∈ F.weakConvexHull (Set.range p) :=
    (mem_weakConvexHull_iff_exists_projection hfiniteRange r₀).2
      ⟨r₀, hr₀Hull, le_rfl, (Point.coord_base r₀).symm⟩
  have hnoProjection (i : I) : ¬ r₀.IsProjectionOf (p i) := by
    intro hproj
    have hgood : ∀ j, r₀ ∈ F.weakConvexHull (deletion p j) := by
      intro j
      by_cases hji : j = i
      · subst j
        exact mem_weakConvexHull_deletion_of_combination_projection
          hcI i (hweightLt i) hproj
      · have hsingle : r₀ ∈ F.weakConvexHull ({p i} : Set F.Point) :=
          mem_weakConvexHull_singleton_of_projection hproj
        have hsub : ({p i} : Set F.Point) ⊆ deletion p j := by
          intro x hx
          rw [Set.mem_singleton_iff] at hx
          subst x
          exact ⟨i, Ne.symm hji, rfl⟩
        exact weakConvexHull_mono hsub hsingle
    obtain ⟨j, hj⟩ := hp.2.2.2 r₀ hr₀Ω hr₀int
    exact hj (hgood j)
  have hr₀notRange : r₀ ∉ Set.range p := by
    rintro ⟨i, rfl⟩
    exact hnoProjection i ⟨le_rfl, (Point.coord_base (p i)).symm⟩
  let R : Finset {q : F.Point // q.IsIntegral} :=
    Finset.univ.filter fun q ↦
      q.1 ∈ Ω ∧ q.1 ∈ F.weakConvexHull (Set.range p) ∧ q.1 ∉ Set.range p
  have hRnonempty : R.Nonempty := by
    refine ⟨⟨r₀, hr₀int⟩, ?_⟩
    simp only [R, Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨hr₀Ω, hr₀Weak, hr₀notRange⟩
  let deletionCount (q : {q : F.Point // q.IsIntegral}) : ℕ :=
    (Finset.univ.filter fun i ↦ q.1 ∈ F.weakConvexHull (deletion p i)).card
  obtain ⟨r, hrR, hrmax⟩ := R.exists_max_image deletionCount hRnonempty
  have hrData : r.1 ∈ Ω ∧ r.1 ∈ F.weakConvexHull (Set.range p) ∧
      r.1 ∉ Set.range p := by
    simpa only [R, Finset.mem_filter, Finset.mem_univ, true_and] using hrR
  have hrΩ : r.1 ∈ Ω := hrData.1
  have hrWeak : r.1 ∈ F.weakConvexHull (Set.range p) := hrData.2.1
  have hrNotRange : r.1 ∉ Set.range p := hrData.2.2
  by_cases hrProjection : ∃ i, r.1.IsProjectionOf (p i)
  · obtain ⟨i, hri⟩ := hrProjection
    have hrSingleton : r.1 ∈ F.weakConvexHull ({p i} : Set F.Point) :=
      mem_weakConvexHull_singleton_of_projection hri
    have hrOther (k : I) (hki : k ≠ i) :
        r.1 ∈ F.weakConvexHull (deletion p k) := by
      apply weakConvexHull_mono (A := ({p i} : Set F.Point))
        (B := deletion p k) (fun x hx ↦ ?_) hrSingleton
      rw [Set.mem_singleton_iff] at hx
      subst x
      exact ⟨i, Ne.symm hki, rfl⟩
    by_cases hrDelete : r.1 ∈ F.weakConvexHull (deletion p i)
    · have hgood : ∀ k, r.1 ∈ F.weakConvexHull (deletion p k) := by
        intro k
        by_cases hki : k = i
        · simpa only [hki] using hrDelete
        · exact hrOther k hki
      obtain ⟨k, hk⟩ := hp.2.2.2 r.1 hrΩ r.2
      exact hk (hgood k)
    · let p' : I → F.Point := Function.update p i r.1
      have hp'i : p' i = r.1 := by simp [p']
      have hp'ne (k : I) (hki : k ≠ i) : p' k = p k := by simp [p', hki]
      have hdeleteI : deletion p' i = deletion p i := by
        ext x
        constructor
        · rintro ⟨k, hki, rfl⟩
          exact ⟨k, hki, (hp'ne k hki).symm⟩
        · rintro ⟨k, hki, rfl⟩
          exact ⟨k, hki, hp'ne k hki⟩
      have hp'injective : Function.Injective p' := by
        intro a b hab
        by_cases hai : a = i
        · subst a
          by_cases hbi : b = i
          · exact hbi.symm
          · have : r.1 = p b := by simpa [hp'i, hp'ne b hbi] using hab
            exact False.elim (hrNotRange ⟨b, this.symm⟩)
        · by_cases hbi : b = i
          · subst b
            have : p a = r.1 := by simpa [hp'i, hp'ne a hai] using hab
            exact False.elim (hrNotRange ⟨a, this⟩)
          · apply hp.1
            simpa [hp'ne a hai, hp'ne b hbi] using hab
      have hp'proper (k : I) : p' k ∈ Ω := by
        by_cases hki : k = i
        · simpa [hki, hp'i] using hrΩ
        · simpa [hp'ne k hki] using hp.2.1 k
      have hp'integral (k : I) : (p' k).IsIntegral := by
        by_cases hki : k = i
        · simpa [hki, hp'i] using r.2
        · simpa [hp'ne k hki] using hp.2.2.1 k
      have hreplacementSubset (k : I) (hki : k ≠ i) :
          deletion p' k ⊆ F.weakConvexHull (deletion p k) := by
        intro x hx
        obtain ⟨j, hjk, rfl⟩ := hx
        by_cases hji : j = i
        · subst j
          rw [hp'i]
          exact hrOther k hki
        · rw [hp'ne j hji]
          exact subset_weakConvexHull F _ ⟨j, hjk, rfl⟩
      have hp'WeaklyConvex : ∀ k,
          p' k ∉ F.weakConvexHull (deletion p' k) := by
        intro k
        by_cases hki : k = i
        · subst k
          rw [hp'i, hdeleteI]
          exact hrDelete
        · intro hk
          have := weakConvexHull_absorb (hreplacementSubset k hki) hk
          rw [hp'ne k hki] at this
          exact hweakExtreme k this
      have hpiNotNew : p i ∉ F.weakConvexHull (Set.range p') := by
        intro hpi
        obtain ⟨u, huHull, hpiProjection⟩ :=
          (mem_weakConvexHull_iff_exists_projection (Set.finite_range p') (p i)).1 hpi
        rcases huHull with ⟨n, uPoint, uWeight, huPoint, huComb⟩
        by_cases husesR : ∃ a, 0 < uWeight a ∧ uPoint a = r.1
        · obtain ⟨a, ha, har⟩ := husesR
          have hru : r.1.base ≤ u.base := by
            simpa only [har] using huComb.base_isLUB.1 a ha
          rcases hpiProjection with ⟨hupi, -⟩
          have hrpi : r.1.base ≤ (p i).base := hru.trans hupi
          exact hrNotRange ⟨i, (r.1.eq_of_projection_of_base_le hri hrpi).symm⟩
        · push Not at husesR
          have huDelete : u ∈ F.convexHull (deletion p i) := by
            apply huComb.mem_convexHull_of_active_mem
            intro a ha
            obtain ⟨j, hj⟩ := huPoint a
            by_cases hji : j = i
            · subst j
              exact False.elim (husesR a ha (hj.symm.trans hp'i))
            · exact ⟨j, hji, (hp'ne j hji).symm.trans hj⟩
          have hdeleteFinite : (deletion p i).Finite :=
            hfiniteRange.subset (by
              rintro x ⟨j, -, rfl⟩
              exact ⟨j, rfl⟩)
          exact hweakExtreme i
            ((mem_weakConvexHull_iff_exists_projection
              hdeleteFinite (p i)).2 ⟨u, huDelete, hpiProjection⟩)
      have hrangeSubset : Set.range p' ⊆ F.weakConvexHull (Set.range p) := by
        rintro x ⟨k, rfl⟩
        by_cases hki : k = i
        · subst k
          simpa only [hp'i] using hrWeak
        · rw [hp'ne k hki]
          exact subset_weakConvexHull F _ ⟨k, rfl⟩
      have hclosureSubset : F.weakConvexHull (Set.range p') ⊆
          F.weakConvexHull (Set.range p) :=
        weakConvexHull_absorb hrangeSubset
      have hscoreLt : hullScore p' < hullScore p := by
        apply Finset.card_lt_card
        apply Finset.ssubset_iff_subset_ne.mpr
        constructor
        · intro q hq
          simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hq ⊢
          exact ⟨hq.1, hclosureSubset hq.2⟩
        · intro heq
          let qi : {q : F.Point // q.IsIntegral} := ⟨p i, hp.2.2.1 i⟩
          have hold : qi ∈ Finset.univ.filter (fun q : {q : F.Point // q.IsIntegral} ↦
              q.1 ∈ Ω ∧ q.1 ∈ F.weakConvexHull (Set.range p)) := by
            simp only [Finset.mem_filter, Finset.mem_univ, true_and, qi]
            exact ⟨hp.2.1 i, subset_weakConvexHull F _ ⟨i, rfl⟩⟩
          have hnew : qi ∉ Finset.univ.filter (fun q : {q : F.Point // q.IsIntegral} ↦
              q.1 ∈ Ω ∧ q.1 ∈ F.weakConvexHull (Set.range p')) := by
            simp only [Finset.mem_filter, Finset.mem_univ, true_and, qi, not_and]
            exact fun _ ↦ hpiNotNew
          change (Finset.univ.filter fun q : {q : F.Point // q.IsIntegral} ↦
              q.1 ∈ Ω ∧ q.1 ∈ F.weakConvexHull (Set.range p')) =
            (Finset.univ.filter fun q : {q : F.Point // q.IsIntegral} ↦
              q.1 ∈ Ω ∧ q.1 ∈ F.weakConvexHull (Set.range p)) at heq
          rw [← heq] at hold
          exact hnew hold
      have hgoodNew : ∃ q, q ∈ Ω ∧ q.IsIntegral ∧
          ∀ k, q ∈ F.weakConvexHull (deletion p' k) := by
        by_contra hnone
        push Not at hnone
        have hp'counter : Counterexample p' :=
          ⟨hp'injective, hp'proper, hp'integral, hnone⟩
        exact (not_le_of_gt hscoreLt) (hminimal hp'counter)
      obtain ⟨s, hsΩ, hsint, hs⟩ := hgoodNew
      have hsOld : ∀ k, s ∈ F.weakConvexHull (deletion p k) := by
        intro k
        by_cases hki : k = i
        · subst k
          rw [← hdeleteI]
          exact hs i
        · exact weakConvexHull_absorb (hreplacementSubset k hki) (hs k)
      obtain ⟨k, hk⟩ := hp.2.2.2 s hsΩ hsint
      exact hk (hsOld k)
  · have hreplacementSeparation (i : I) :
        p i ∉ F.weakConvexHull (Set.insert r.1 (deletion p i)) := by
      obtain ⟨xi, hpiEval, hsep⟩ :=
        exists_strictSeparator_of_not_mem_weakConvexHull (hweakExtreme i)
      intro hpiReplacement
      obtain ⟨a, ha, haEval, hpia⟩ := hpiReplacement xi hpiEval
      have har : a = r.1 := by
        rcases ha with (rfl | haDelete)
        · rfl
        · have := hsep a haDelete haEval
          linarith
      subst a
      obtain ⟨b, hbRange, hbEval, hrb⟩ := hrWeak xi haEval
      obtain ⟨k, hk⟩ := hbRange
      have hki : k = i := by
        by_contra hne
        have hbDelete : b ∈ deletion p i := ⟨k, hne, hk⟩
        have := hsep b hbDelete hbEval
        linarith
      subst k
      have hbTarget : xi.eval b hbEval = xi.eval (p i) hpiEval :=
        xi.eval_congr_point hk.symm hbEval hpiEval
      have hrTarget : xi.eval r.1 haEval = xi.eval (p i) hpiEval := by
        apply le_antisymm
        · exact hrb.trans_eq hbTarget
        · exact hpia
      obtain ⟨lift, hliftHull, hrLiftProjection⟩ :=
        (mem_weakConvexHull_iff_exists_projection hfiniteRange r.1).1 hrWeak
      rcases hliftHull with ⟨n, liftPoint, liftWeight, hliftPoint, hliftComb⟩
      rcases hrLiftProjection with ⟨hliftBase, hliftVal⟩
      let hliftEval : xi.EvaluableAt lift := hliftBase.trans haEval
      have hliftTarget : xi.eval lift hliftEval = xi.eval (p i) hpiEval := by
        have hprojEval := xi.eval_eq_of_projection r.1 lift hliftBase hliftVal haEval
        exact hprojEval.symm.trans hrTarget
      have hactiveEq (t : Fin n) (ht : 0 < liftWeight t) : liftPoint t = p i := by
        by_contra htne
        let htEval : xi.EvaluableAt (liftPoint t) :=
          (hliftComb.base_isLUB.1 t ht).trans hliftEval
        have htDelete : liftPoint t ∈ deletion p i := by
          obtain ⟨m, hm⟩ := hliftPoint t
          have hmi : m ≠ i := by
            intro hmi
            subst m
            exact htne hm.symm
          exact ⟨m, hmi, hm⟩
        have htStrict := hsep (liftPoint t) htDelete htEval
        have hall (u : {u : Fin n // 0 < liftWeight u}) :
            xi.eval (liftPoint u)
                ((hliftComb.base_isLUB.1 u u.property).trans hliftEval) ≤
              xi.eval (p i) hpiEval := by
          by_cases hui : liftPoint u = p i
          · exact le_of_eq (xi.eval_congr_point hui _ _)
          · exact le_of_lt (hsep (liftPoint u) (by
              obtain ⟨m, hm⟩ := hliftPoint u
              have hmi : m ≠ i := by
                intro hmi
                subst m
                exact hui hm.symm
              exact ⟨m, hmi, hm⟩) _)
        have hsumlt :
            (∑ u : {u : Fin n // 0 < liftWeight u},
              liftWeight u * xi.eval (liftPoint u)
                ((hliftComb.base_isLUB.1 u u.property).trans hliftEval)) <
              ∑ u : {u : Fin n // 0 < liftWeight u},
                liftWeight u * xi.eval (p i) hpiEval := by
          apply Finset.sum_lt_sum
          · intro u _
            exact mul_le_mul_of_nonneg_left (hall u) u.property.le
          · let tt : {u : Fin n // 0 < liftWeight u} := ⟨t, ht⟩
            exact ⟨tt, Finset.mem_univ tt,
              mul_lt_mul_of_pos_left htStrict tt.property⟩
        have hleft :
            (∑ u : {u : Fin n // 0 < liftWeight u},
              liftWeight u * xi.eval (liftPoint u)
                ((hliftComb.base_isLUB.1 u u.property).trans hliftEval)) =
              xi.eval (p i) hpiEval :=
          (hliftComb.eval_eq xi hliftEval).symm.trans hliftTarget
        have hright :
            (∑ u : {u : Fin n // 0 < liftWeight u},
              liftWeight u * xi.eval (p i) hpiEval) =
              xi.eval (p i) hpiEval := by
          rw [← Finset.sum_mul, hliftComb.sum_active, one_mul]
        rw [hleft, hright] at hsumlt
        exact (lt_irrefl _ hsumlt)
      have hliftEq : lift = p i :=
        hliftComb.result_eq_of_active_eq hactiveEq
      apply hrProjection
      refine ⟨i, ?_⟩
      exact Eq.mp (congrArg (fun q : F.Point ↦ r.1.IsProjectionOf q) hliftEq)
        ⟨hliftBase, hliftVal⟩
    obtain ⟨j, hrNotDelete⟩ := hp.2.2.2 r.1 hrΩ r.2
    let p' : I → F.Point := Function.update p j r.1
    have hp'j : p' j = r.1 := by simp [p']
    have hp'ne (k : I) (hkj : k ≠ j) : p' k = p k := by simp [p', hkj]
    have hdeleteJ : deletion p' j = deletion p j := by
      ext x
      constructor
      · rintro ⟨k, hkj, rfl⟩
        exact ⟨k, hkj, (hp'ne k hkj).symm⟩
      · rintro ⟨k, hkj, rfl⟩
        exact ⟨k, hkj, hp'ne k hkj⟩
    have hrange : Set.range p' = Set.insert r.1 (deletion p j) := by
      ext x
      constructor
      · rintro ⟨k, rfl⟩
        by_cases hkj : k = j
        · subst k
          rw [hp'j]
          exact Set.mem_insert _ _
        · exact Set.mem_insert_of_mem _ ⟨k, hkj, (hp'ne k hkj).symm⟩
      · intro hx
        rcases hx with (rfl | hx)
        · exact ⟨j, hp'j⟩
        · obtain ⟨k, hkj, hk⟩ := hx
          exact ⟨k, (hp'ne k hkj).trans hk⟩
    have hp'injective : Function.Injective p' := by
      intro a b hab
      by_cases haj : a = j
      · subst a
        by_cases hbj : b = j
        · exact hbj.symm
        · have : r.1 = p b := by simpa [hp'j, hp'ne b hbj] using hab
          exact False.elim (hrNotRange ⟨b, this.symm⟩)
      · by_cases hbj : b = j
        · subst b
          have : p a = r.1 := by simpa [hp'j, hp'ne a haj] using hab
          exact False.elim (hrNotRange ⟨a, this⟩)
        · apply hp.1
          simpa [hp'ne a haj, hp'ne b hbj] using hab
    have hp'proper (k : I) : p' k ∈ Ω := by
      by_cases hkj : k = j
      · simpa [hkj, hp'j] using hrΩ
      · simpa [hp'ne k hkj] using hp.2.1 k
    have hp'integral (k : I) : (p' k).IsIntegral := by
      by_cases hkj : k = j
      · simpa [hkj, hp'j] using r.2
      · simpa [hp'ne k hkj] using hp.2.2.1 k
    have hp'WeaklyConvex : ∀ k,
        p' k ∉ F.weakConvexHull (deletion p' k) := by
      intro k
      by_cases hkj : k = j
      · subst k
        rw [hp'j, hdeleteJ]
        exact hrNotDelete
      · intro hk
        have hsub : deletion p' k ⊆ Set.insert r.1 (deletion p k) := by
          intro x hx
          obtain ⟨m, hmk, rfl⟩ := hx
          by_cases hmj : m = j
          · subst m
            rw [hp'j]
            exact Set.mem_insert _ _
          · rw [hp'ne m hmj]
            exact Set.mem_insert_of_mem _ ⟨m, hmk, rfl⟩
        have hk' := weakConvexHull_mono hsub hk
        rw [hp'ne k hkj] at hk'
        exact hreplacementSeparation k hk'
    have hpjNotNew : p j ∉ F.weakConvexHull (Set.range p') := by
      rw [hrange]
      exact hreplacementSeparation j
    have hrangeSubset : Set.range p' ⊆ F.weakConvexHull (Set.range p) := by
      rintro x ⟨k, rfl⟩
      by_cases hkj : k = j
      · subst k
        simpa only [hp'j] using hrWeak
      · rw [hp'ne k hkj]
        exact subset_weakConvexHull F _ ⟨k, rfl⟩
    have hclosureSubset : F.weakConvexHull (Set.range p') ⊆
        F.weakConvexHull (Set.range p) :=
      weakConvexHull_absorb hrangeSubset
    have hscoreLt : hullScore p' < hullScore p := by
      apply Finset.card_lt_card
      apply Finset.ssubset_iff_subset_ne.mpr
      constructor
      · intro q hq
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hq ⊢
        exact ⟨hq.1, hclosureSubset hq.2⟩
      · intro heq
        let qj : {q : F.Point // q.IsIntegral} := ⟨p j, hp.2.2.1 j⟩
        have hold : qj ∈ Finset.univ.filter (fun q : {q : F.Point // q.IsIntegral} ↦
            q.1 ∈ Ω ∧ q.1 ∈ F.weakConvexHull (Set.range p)) := by
          simp only [Finset.mem_filter, Finset.mem_univ, true_and, qj]
          exact ⟨hp.2.1 j, subset_weakConvexHull F _ ⟨j, rfl⟩⟩
        have hnew : qj ∉ Finset.univ.filter (fun q : {q : F.Point // q.IsIntegral} ↦
            q.1 ∈ Ω ∧ q.1 ∈ F.weakConvexHull (Set.range p')) := by
          simp only [Finset.mem_filter, Finset.mem_univ, true_and, qj, not_and]
          exact fun _ ↦ hpjNotNew
        change (Finset.univ.filter fun q : {q : F.Point // q.IsIntegral} ↦
            q.1 ∈ Ω ∧ q.1 ∈ F.weakConvexHull (Set.range p')) =
          (Finset.univ.filter fun q : {q : F.Point // q.IsIntegral} ↦
            q.1 ∈ Ω ∧ q.1 ∈ F.weakConvexHull (Set.range p)) at heq
        rw [← heq] at hold
        exact hnew hold
    have hgoodNew : ∃ q, q ∈ Ω ∧ q.IsIntegral ∧
        ∀ k, q ∈ F.weakConvexHull (deletion p' k) := by
      by_contra hnone
      push Not at hnone
      have hp'counter : Counterexample p' :=
        ⟨hp'injective, hp'proper, hp'integral, hnone⟩
      exact (not_le_of_gt hscoreLt) (hminimal hp'counter)
    obtain ⟨s, hsΩ, hsint, hs⟩ := hgoodNew
    have hI : Nonempty I := Fintype.card_pos_iff.mp
      (lt_of_le_of_lt (Nat.zero_le _) hlarge)
    have hsWeakNew : s ∈ F.weakConvexHull (Set.range p') := by
      let k : I := Classical.choice hI
      apply weakConvexHull_mono (A := deletion p' k) (B := Set.range p')
        (fun x hx ↦ ?_) (hs k)
      obtain ⟨m, -, rfl⟩ := hx
      exact ⟨m, rfl⟩
    have hsWeak : s ∈ F.weakConvexHull (Set.range p) :=
      hclosureSubset hsWeakNew
    have hsDeleteJ : s ∈ F.weakConvexHull (deletion p j) := by
      rw [← hdeleteJ]
      exact hs j
    have htransfer (k : I) (hrk : r.1 ∈ F.weakConvexHull (deletion p k))
        (hkj : k ≠ j) : deletion p' k ⊆ F.weakConvexHull (deletion p k) := by
      intro x hx
      obtain ⟨m, hmk, rfl⟩ := hx
      by_cases hmj : m = j
      · subst m
        rw [hp'j]
        exact hrk
      · rw [hp'ne m hmj]
        exact subset_weakConvexHull F _ ⟨m, hmk, rfl⟩
    have hsTransfer (k : I) (hrk : r.1 ∈ F.weakConvexHull (deletion p k)) :
        s ∈ F.weakConvexHull (deletion p k) := by
      have hkj : k ≠ j := by
        intro h
        subst k
        exact hrNotDelete hrk
      exact weakConvexHull_absorb (htransfer k hrk hkj) (hs k)
    have hsNotRange : s ∉ Set.range p := by
      rintro ⟨k, rfl⟩
      by_cases hkj : k = j
      · subst k
        exact hweakExtreme j hsDeleteJ
      · have hpkeq : p k = p' k := (hp'ne k hkj).symm
        have hp'bad : p' k ∈ F.weakConvexHull (deletion p' k) := by
          rw [← hpkeq]
          exact hs k
        exact hp'WeaklyConvex k hp'bad
    let sCode : {q : F.Point // q.IsIntegral} := ⟨s, hsint⟩
    have hsR : sCode ∈ R := by
      simp only [R, Finset.mem_filter, Finset.mem_univ, true_and, sCode]
      exact ⟨hsΩ, hsWeak, hsNotRange⟩
    let Ir : Finset I := Finset.univ.filter fun k ↦
      r.1 ∈ F.weakConvexHull (deletion p k)
    let Is : Finset I := Finset.univ.filter fun k ↦
      s ∈ F.weakConvexHull (deletion p k)
    have hIrIs : Ir ⊆ Is := by
      intro k hk
      simp only [Ir, Is, Finset.mem_filter, Finset.mem_univ, true_and] at hk ⊢
      exact hsTransfer k hk
    have hjIs : j ∈ Is := by
      simp only [Is, Finset.mem_filter, Finset.mem_univ, true_and]
      exact hsDeleteJ
    have hjNotIr : j ∉ Ir := by
      simp only [Ir, Finset.mem_filter, Finset.mem_univ, true_and]
      exact hrNotDelete
    have hIrStrict : Ir ⊂ Is := by
      apply Finset.ssubset_iff_subset_ne.mpr
      refine ⟨hIrIs, ?_⟩
      intro heq
      rw [← heq] at hjIs
      exact hjNotIr hjIs
    have hcountLt : deletionCount r < deletionCount sCode := by
      change Ir.card < Is.card
      exact Finset.card_lt_card hIrStrict
    exact (not_le_of_gt hcountLt) (hrmax sCode hsR)

/-- Finite-family form of Flag Helly.  The proof is the usual Helly
induction once the flagged Doignon step is available. -/
private theorem flagHelly_finset {F : ConvexFlag} (Ω : F.ProperPointSet)
    (hnonempty : ∃ q, q ∈ Ω ∧ q.IsIntegral)
    (ℱ : Set (Set F.Point))
    (_hproper : ∀ S ∈ ℱ, S ⊆ Ω.carrier)
    (hlocal : ∀ G : Finset (Set F.Point),
      (G : Set (Set F.Point)) ⊆ ℱ → G.Nonempty →
      G.card ≤ hellyConstant Ω →
      HasCommonWeakHullPoint Ω (G : Set (Set F.Point)))
    (G : Finset (Set F.Point)) (hG : (G : Set (Set F.Point)) ⊆ ℱ) :
    HasCommonWeakHullPoint Ω (G : Set (Set F.Point)) := by
  classical
  revert hG
  refine Finset.strongInductionOn G ?_
  intro G ih hG
  by_cases hGempty : G = ∅
  · subst G
    obtain ⟨q, hqΩ, hqint⟩ := hnonempty
    exact ⟨q, hqΩ, hqint, by simp⟩
  by_cases hsmall : G.card ≤ hellyConstant Ω
  · exact hlocal G hG (Finset.nonempty_iff_ne_empty.mpr hGempty) hsmall
  have hlarge : hellyConstant Ω < Fintype.card {S // S ∈ G} := by
    simpa using Nat.lt_of_not_ge hsmall
  have hsmaller (S : {S // S ∈ G}) : G.erase S.1 ⊂ G :=
    Finset.erase_ssubset S.2
  have heraseFamily (S : {S // S ∈ G}) :
      ((G.erase S.1 : Finset (Set F.Point)) : Set (Set F.Point)) ⊆ ℱ := by
    intro T hT
    exact hG (Finset.mem_of_mem_erase hT)
  have heraseCommon (S : {S // S ∈ G}) :
      HasCommonWeakHullPoint Ω
        ((G.erase S.1 : Finset (Set F.Point)) : Set (Set F.Point)) :=
    ih (G.erase S.1) (hsmaller S) (heraseFamily S)
  choose q hqΩ hqint hq using heraseCommon
  let points : {S // S ∈ G} → F.Point := fun S ↦ q S
  by_cases hinj : Function.Injective points
  · obtain ⟨r, hrΩ, hrint, hr⟩ :=
      flaggedDoignon Ω points hinj hqΩ hqint hlarge
    refine ⟨r, hrΩ, hrint, ?_⟩
    intro S hS
    let i : {T // T ∈ G} := ⟨S, hS⟩
    have hsub : deletion points i ⊆ F.weakConvexHull S := by
      intro x hx
      obtain ⟨j, hji, rfl⟩ := hx
      exact hq j S (by
        apply Finset.mem_erase.mpr
        exact ⟨fun h ↦ hji (Subtype.ext h.symm), hS⟩)
    exact weakConvexHull_absorb hsub (hr i)
  · obtain ⟨i, j, heq, hij⟩ := Function.not_injective_iff.mp hinj
    have heq' : q i = q j := by simpa only [points] using heq
    refine ⟨points i, hqΩ i, hqint i, ?_⟩
    intro S hS
    by_cases hSi : S = i.1
    · have hmem : S ∈ G.erase j.1 := by
        apply Finset.mem_erase.mpr
        exact ⟨fun h ↦ hij (Subtype.ext (hSi.symm.trans h)), hS⟩
      change q i ∈ F.weakConvexHull S
      rw [heq']
      exact hq j S hmem
    · exact hq i S (Finset.mem_erase.mpr ⟨hSi, hS⟩)

/-- Theorem 3.13 (`Helly`): Helly's theorem for convex flags.

The family may be infinite.  Only nonempty finite subfamilies of cardinality
at most the Helly constant occur in the hypothesis; the separate existence
assumption supplies the conclusion for an empty family. -/
theorem flagHelly {F : ConvexFlag} (Ω : F.ProperPointSet)
    (hnonempty : ∃ q, q ∈ Ω ∧ q.IsIntegral)
    (ℱ : Set (Set F.Point))
    (hproper : ∀ S ∈ ℱ, S ⊆ Ω.carrier)
    (hlocal : ∀ G : Finset (Set F.Point),
      (G : Set (Set F.Point)) ⊆ ℱ → G.Nonempty →
      G.card ≤ hellyConstant Ω →
      HasCommonWeakHullPoint Ω (G : Set (Set F.Point))) :
    HasCommonWeakHullPoint Ω ℱ := by
  classical
  by_contra hfail
  have hmiss : ∀ q : F.Point, q ∈ Ω → q.IsIntegral →
      ∃ S, S ∈ ℱ ∧ q ∉ F.weakConvexHull S := by
    intro q hqΩ hqint
    by_contra hq
    push Not at hq
    exact hfail ⟨q, hqΩ, hqint, hq⟩
  let A := {q : {q : F.Point // q.IsIntegral} // q.1 ∈ Ω}
  let : Fintype A := Fintype.ofFinite A
  have hmissA (q : A) : ∃ S, S ∈ ℱ ∧ q.1.1 ∉ F.weakConvexHull S :=
    hmiss q.1.1 q.2 q.1.2
  choose badSet hbadSetFamily hbadSet using hmissA
  let G : Finset (Set F.Point) := Finset.univ.image badSet
  have hGFamily : (G : Set (Set F.Point)) ⊆ ℱ := by
    intro S hS
    obtain ⟨q, -, rfl⟩ := Finset.mem_image.mp hS
    exact hbadSetFamily q
  obtain ⟨q, hqΩ, hqint, hq⟩ :=
    flagHelly_finset Ω hnonempty ℱ hproper hlocal G hGFamily
  let a : A := ⟨⟨q, hqint⟩, hqΩ⟩
  have hbadMem : badSet a ∈ G :=
    Finset.mem_image.mpr ⟨a, Finset.mem_univ _, rfl⟩
  exact hbadSet a (hq (badSet a) hbadMem)

/-- Numbered alias for Theorem 3.13. -/
alias theorem_3_13 := flagHelly

end EGZ.ConvexFlag
