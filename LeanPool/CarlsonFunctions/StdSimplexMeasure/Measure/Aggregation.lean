/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams.
-/
module

public import LeanPool.CarlsonFunctions.StdSimplexMeasure.Measure.Basic

public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
public import Mathlib.MeasureTheory.Measure.Restrict
public import Mathlib.MeasureTheory.Measure.WithDensity
public import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
public import LeanPool.CarlsonFunctions.StdSimplexMeasure.CoordinateRealization

import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.MeasureTheory.Measure.Dirac
import LeanPool.CarlsonFunctions.StdSimplexMeasure.PositiveSimplex.Aggregation

/-! # Aggregation pushforward of simplex coordinate measure -/

public noncomputable section StdSimplexCoordinateMeasure

namespace MeasureTheory.Measure

variable {ι : Type*} [Fintype ι]

open scoped Classical

/-- Density associated with the cardinalities of the fibers of a coordinate aggregation map. -/
@[expose] def stdSimplexAggregateDensity
    {κ : Type*} [Fintype κ] (f : ι → κ) (v : κ → ℝ) : ENNReal := by
  classical
  exact ∏ k,
      (ENNReal.ofReal (v k)) ^
          (stdSimplexAggregateFiberCard f k - 1) /
        (Nat.factorial
          (stdSimplexAggregateFiberCard f k - 1) : ENNReal)

/-- For a surjective aggregation, the total degree of the aggregation density is the difference
between the dimensions of the source and target affine coordinate spaces. -/
theorem sum_stdSimplexAggregateFiberCard_sub_one
    {κ : Type*} [Fintype κ] {f : ι → κ} (hf : Function.Surjective f) :
    ∑ k, (stdSimplexAggregateFiberCard f k - 1) =
      Fintype.card ι - Fintype.card κ := by
  have hpos : ∀ k, 1 ≤ stdSimplexAggregateFiberCard f k := fun k =>
    stdSimplexAggregateFiberCard_pos hf k
  have hsum : (∑ k, (stdSimplexAggregateFiberCard f k - 1)) + Fintype.card κ =
      Fintype.card ι := by
    rw [← sum_stdSimplexAggregateFiberCard f]
    calc
      (∑ k, (stdSimplexAggregateFiberCard f k - 1)) + Fintype.card κ =
          (∑ k, (stdSimplexAggregateFiberCard f k - 1)) + ∑ _k : κ, 1 := by simp
      _ = ∑ k, ((stdSimplexAggregateFiberCard f k - 1) + 1) :=
        Finset.sum_add_distrib.symm
      _ = ∑ k, stdSimplexAggregateFiberCard f k := by
        apply Finset.sum_congr rfl
        intro k _
        exact Nat.sub_add_cancel (hpos k)
  omega

/-- The aggregation formula when the target has one coordinate. This is the base case for
fiberwise induction on a general surjective aggregation map. -/
theorem map_stdSimplexMeasure_restrict_stdSimplex_aggregate_of_unique
    {κ : Type*} [Fintype κ] [Unique κ] [Nonempty ι]
    (f : ι → κ) :
    Measure.map (stdSimplexAggregate f)
      ((stdSimplexMeasure (ι := ι)).restrict (Convexity.StdSimplex.coordinateSet ℝ ι)) =
    ((stdSimplexMeasure (ι := κ)).restrict (Convexity.StdSimplex.coordinateSet ℝ κ)).withDensity
      (stdSimplexAggregateDensity f) := by
  ext s hs
  rw [Measure.map_apply (by fun_prop) hs]
  rw [withDensity_apply _ hs]
  rw [stdSimplexMeasure_unique (ι := κ)]
  have hconst_mem : (fun _ : κ => (1 : ℝ)) ∈ Convexity.StdSimplex.coordinateSet ℝ κ := by
    simp [Convexity.StdSimplex.coordinateSet]
  rw [MeasureTheory.restrict_dirac' (Convexity.StdSimplex.isClosed_coordinateSet ℝ κ).measurableSet,
    if_pos hconst_mem]
  have hd : Measurable (stdSimplexAggregateDensity f) := by
    unfold stdSimplexAggregateDensity
    fun_prop
  rw [MeasureTheory.setLIntegral_dirac' hd hs]
  by_cases hmem : (fun _ : κ => (1 : ℝ)) ∈ s
  · rw [if_pos hmem]
    have hpre : stdSimplexAggregate f ⁻¹' s ∩ Convexity.StdSimplex.coordinateSet ℝ ι = Convexity.StdSimplex.coordinateSet ℝ ι := by
      ext u
      simp only [Set.mem_inter_iff]
      constructor
      · exact fun h => h.2
      · intro hu
        refine ⟨?_, hu⟩
        have ha := stdSimplexAggregate_mem_stdSimplex (f := f) hu
        have heq : stdSimplexAggregate f u = fun _ : κ => (1 : ℝ) := by
          funext k
          simpa [Convexity.StdSimplex.coordinateSet, Subsingleton.elim k default] using ha.2
        simpa [heq] using hmem
    rw [Measure.restrict_apply (hs.preimage (by fun_prop)), hpre,
      stdSimplexMeasure_stdSimplex]
    simp [stdSimplexAggregateDensity, stdSimplexAggregateFiberCard,
      Subsingleton.elim (f _) default]
  · rw [if_neg hmem]
    have hpre : stdSimplexAggregate f ⁻¹' s ∩ Convexity.StdSimplex.coordinateSet ℝ ι = ∅ := by
      ext u
      simp only [Set.mem_inter_iff, Set.mem_preimage, Set.mem_empty_iff_false]
      constructor
      · rintro ⟨huS, hu⟩
        have ha := stdSimplexAggregate_mem_stdSimplex (f := f) hu
        have heq : stdSimplexAggregate f u = fun _ : κ => (1 : ℝ) := by
          funext k
          simpa [Convexity.StdSimplex.coordinateSet, Subsingleton.elim k default] using ha.2
        exact (hmem (heq ▸ huS)).elim
      · exact False.elim
    rw [Measure.restrict_apply (hs.preimage (by fun_prop)), hpre, measure_empty]

/-- In omitted-coordinate charts, aggregation discards the coordinates in the remainder of
the omitted target fibre and aggregates all complementary coordinates. -/
private theorem stdSimplexAggregate_coordMap_split
    {κ : Type*} [Fintype κ] (f : ι → κ) (k : κ) (i : ι) (hi : f i = k)
    (x : {j : ι // j ≠ i} → ℝ) :
    let p : {j : ι // j ≠ i} → Prop := fun a ↦ f a ≠ k
    let e := MeasurableEquiv.piEquivPiSubtypeProd
      (fun _ : {j : ι // j ≠ i} ↦ ℝ) p
    let f' : {a : {j : ι // j ≠ i} // p a} → {j : κ // j ≠ k} :=
      fun a ↦ ⟨f a, a.property⟩
    stdSimplexAggregate f (stdSimplexCoordMap i x) =
      stdSimplexCoordMap k (FunOnFinite.linearMap ℝ ℝ f' (e x).1) := by
  classical
  dsimp only
  let p : {j : ι // j ≠ i} → Prop := fun a ↦ f a ≠ k
  let e := MeasurableEquiv.piEquivPiSubtypeProd
    (fun _ : {j : ι // j ≠ i} ↦ ℝ) p
  let f' : {a : {j : ι // j ≠ i} // p a} → {j : κ // j ≠ k} :=
    fun a ↦ ⟨f a, a.property⟩
  have hfree (j : κ) (hj : j ≠ k) :
      stdSimplexAggregate f (stdSimplexCoordMap i x) j =
        FunOnFinite.linearMap ℝ ℝ f' (e x).1 ⟨j, hj⟩ := by
    change FunOnFinite.linearMap ℝ ℝ f (stdSimplexCoordMap i x) j = _
    rw [FunOnFinite.linearMap_apply_apply, FunOnFinite.linearMap_apply_apply]
    rw [Finset.sum_subtype (p := fun a : ι ↦ f a = j)
      (Finset.univ.filter fun a : ι ↦ f a = j) (by simp)]
    rw [Finset.sum_subtype
      (p := fun a : {a : {q : ι // q ≠ i} // p a} ↦ f' a = ⟨j, hj⟩)
      (Finset.univ.filter fun a : {a : {q : ι // q ≠ i} // p a} ↦
        f' a = ⟨j, hj⟩) (by simp)]
    let E : {a : ι // f a = j} ≃
        {a : {a : {q : ι // q ≠ i} // p a} // f' a = ⟨j, hj⟩} :=
      { toFun := fun a =>
          ⟨⟨⟨a, fun hai => hj (a.property.symm.trans ((congrArg f hai).trans hi))⟩,
              fun hak => hj (a.property.symm.trans hak)⟩,
            Subtype.ext a.property⟩
        invFun := fun a => ⟨a.1.1.1, congrArg Subtype.val a.property⟩
        left_inv := fun a => by ext; rfl
        right_inv := fun a => by ext; rfl }
    apply Fintype.sum_equiv E
    intro a
    rw [stdSimplexCoordMap_apply_of_ne i a
      (fun hai => hj (a.property.symm.trans ((congrArg f hai).trans hi)))]
    simp [e, p, E]
  funext j
  by_cases hj : j = k
  · subst j
    have hsum_left :
        ∑ j, stdSimplexAggregate f (stdSimplexCoordMap i x) j = 1 := by
      rw [show (∑ j, stdSimplexAggregate f (stdSimplexCoordMap i x) j) =
          ∑ j, ∑ a ∈ Finset.univ.filter (fun a : ι ↦ f a = j),
            stdSimplexCoordMap i x a by
        apply Finset.sum_congr rfl
        intro j _
        change FunOnFinite.linearMap ℝ ℝ f (stdSimplexCoordMap i x) j = _
        rw [FunOnFinite.linearMap_apply_apply]]
      rw [Finset.sum_fiberwise Finset.univ f (stdSimplexCoordMap i x)]
      exact sum_stdSimplexCoordMap i x
    calc
      stdSimplexAggregate f (stdSimplexCoordMap i x) k =
          1 - ∑ q : {j : κ // j ≠ k},
            stdSimplexAggregate f (stdSimplexCoordMap i x) q := by
              rw [← hsum_left, Fintype.sum_eq_add_sum_subtype_ne _ k]
              ring
      _ = 1 - ∑ q : {j : κ // j ≠ k},
          FunOnFinite.linearMap ℝ ℝ f' (e x).1 q := by
            congr 1
            apply Finset.sum_congr rfl
            intro q _
            exact hfree q q.property
      _ = stdSimplexCoordMap k (FunOnFinite.linearMap ℝ ℝ f' (e x).1) k := by
        rw [stdSimplexCoordMap_apply_self]
  · rw [stdSimplexCoordMap_apply_of_ne k j hj]
    exact hfree j hj

/-- In the same omitted-coordinate charts, the standard-simplex aggregation density is the
solid-simplex aggregation density on the complementary fibres times the volume of the
remainder of the omitted fibre. -/
private theorem stdSimplexAggregateDensity_coordMap_split
    {κ : Type*} [Fintype κ] (f : ι → κ) (k : κ) (i : ι) (hi : f i = k)
    (z : {j : κ // j ≠ k} → ℝ) :
    let p : {j : ι // j ≠ i} → Prop := fun a ↦ f a ≠ k
    let f' : {a : {j : ι // j ≠ i} // p a} → {j : κ // j ≠ k} :=
      fun a ↦ ⟨f a, a.property⟩
    let A := {a : {j : ι // j ≠ i} // ¬p a}
    stdSimplexAggregateDensity f (stdSimplexCoordMap k z) =
      (ENNReal.ofReal (1 - ∑ q, z q) ^ Fintype.card A /
        (Nat.factorial (Fintype.card A) : ENNReal)) *
        posSimplexAggregateDensity f' z := by
  classical
  dsimp only
  let p : {j : ι // j ≠ i} → Prop := fun a ↦ f a ≠ k
  let f' : {a : {j : ι // j ≠ i} // p a} → {j : κ // j ≠ k} :=
    fun a ↦ ⟨f a, a.property⟩
  let A := {a : {j : ι // j ≠ i} // ¬p a}
  have hkcard : stdSimplexAggregateFiberCard f k - 1 = Fintype.card A := by
    let E : A ≃ {a : {a : ι // f a = k} // a ≠ ⟨i, hi⟩} :=
      { toFun := fun a =>
          ⟨⟨a.1.1, Classical.not_not.mp a.property⟩,
            fun hai => a.1.property (congrArg Subtype.val hai)⟩
        invFun := fun a =>
          ⟨⟨a.1.1, fun hai => a.property (Subtype.ext hai)⟩,
            fun hne => hne a.1.property⟩
        left_inv := fun a => by ext; rfl
        right_inv := fun a => by ext; rfl }
    unfold stdSimplexAggregateFiberCard
    rw [Fintype.card_congr E]
    rw [Fintype.card_subtype_compl (fun a : {a : ι // f a = k} => a = ⟨i, hi⟩),
      Fintype.card_subtype_eq]
  unfold stdSimplexAggregateDensity posSimplexAggregateDensity
  rw [Fintype.prod_eq_mul_prod_subtype_ne _ k]
  rw [stdSimplexCoordMap_apply_self, hkcard]
  congr 1
  apply Fintype.prod_congr
  intro j
  letI (a : {a : {q : ι // q ≠ i} // p a}) : Decidable (f' a = j) :=
    Classical.propDecidable _
  rw [stdSimplexCoordMap_apply_of_ne k j j.property]
  have hjcard : stdSimplexAggregateFiberCard f j =
      Fintype.card {a : {a : {q : ι // q ≠ i} // p a} // f' a = j} := by
    let E : {a : ι // f a = j} ≃
        {a : {a : {q : ι // q ≠ i} // p a} // f' a = j} :=
      { toFun := fun a =>
          ⟨⟨⟨a, fun hai => j.property
              (a.property.symm.trans ((congrArg f hai).trans hi))⟩,
            fun hak => j.property (a.property.symm.trans hak)⟩,
            Subtype.ext a.property⟩
        invFun := fun a => ⟨a.1.1.1, congrArg Subtype.val a.property⟩
        left_inv := fun a => by ext; rfl
        right_inv := fun a => by ext; rfl }
    unfold stdSimplexAggregateFiberCard
    exact Fintype.card_congr E
  rw [hjcard]

/-- Pushing the restricted simplex measure forward under coordinate aggregation gives the
restricted target simplex measure weighted by the product of the fiber-volume densities.

This is the standard-simplex form of `lintegral_posSimplex_comp_aggregate`. -/
theorem map_stdSimplexMeasure_restrict_stdSimplex_aggregate
    {κ : Type*} [Fintype κ]
    (f : ι → κ) (hf : Function.Surjective f) :
    Measure.map (stdSimplexAggregate f)
      ((stdSimplexMeasure (ι := ι)).restrict (Convexity.StdSimplex.coordinateSet ℝ ι))
      =
    ((stdSimplexMeasure (ι := κ)).restrict (Convexity.StdSimplex.coordinateSet ℝ κ)).withDensity
      (stdSimplexAggregateDensity f) := by
  classical
  cases isEmpty_or_nonempty ι with
  | inl _ =>
      have : IsEmpty κ := ⟨fun k ↦ (hf k).elim fun a _ ↦ isEmptyElim a⟩
      rw [stdSimplexMeasure_empty, stdSimplexMeasure_empty]
      simp
  | inr hι =>
      cases subsingleton_or_nontrivial κ with
      | inl _ =>
          let : Unique κ :=
            { default := f (Classical.choice hι)
              uniq := fun _ ↦ Subsingleton.elim _ _ }
          exact map_stdSimplexMeasure_restrict_stdSimplex_aggregate_of_unique f
      | inr _ =>
          let k : κ := Classical.choice (inferInstance : Nonempty κ)
          obtain ⟨i, hi⟩ := hf k
          let p : {j : ι // j ≠ i} → Prop := fun a ↦ f a ≠ k
          let e := MeasurableEquiv.piEquivPiSubtypeProd
            (fun _ : {j : ι // j ≠ i} ↦ ℝ) p
          let f' : {a : {j : ι // j ≠ i} // p a} → {j : κ // j ≠ k} :=
            fun a ↦ ⟨f a, a.property⟩
          have hf' : Function.Surjective f' := by
            intro j
            obtain ⟨a, ha⟩ := hf j
            have hai : a ≠ i := fun hai => j.property
              (ha.symm.trans ((congrArg f hai).trans hi))
            exact ⟨⟨⟨a, hai⟩, fun hak => j.property (ha.symm.trans hak)⟩,
              Subtype.ext ha⟩
          let A := {a : {j : ι // j ≠ i} // ¬p a}
          let D : ({j : κ // j ≠ k} → ℝ) → ENNReal := fun z ↦
            ENNReal.ofReal (1 - ∑ q, z q) ^ Fintype.card A /
              (Nat.factorial (Fintype.card A) : ENNReal)
          have hsum (u : {a : {j : ι // j ≠ i} // p a} → ℝ) :
              ∑ q, FunOnFinite.linearMap ℝ ℝ f' u q = ∑ a, u a := by
            rw [show (∑ q, FunOnFinite.linearMap ℝ ℝ f' u q) =
                ∑ q, ∑ a ∈ Finset.univ.filter (fun a => f' a = q), u a by
              apply Finset.sum_congr rfl
              intro q _
              rw [FunOnFinite.linearMap_apply_apply]]
            exact Finset.sum_fiberwise Finset.univ f' u
          apply Measure.ext_of_lintegral
          intro g hg
          have hdensity : Measurable (stdSimplexAggregateDensity f) := by
            unfold stdSimplexAggregateDensity
            fun_prop
          have haggregate : Measurable (stdSimplexAggregate (R := ℝ) f) := by
            fun_prop
          have hleft :
              ∫⁻ u, g u ∂Measure.map (stdSimplexAggregate f)
                ((stdSimplexMeasure (ι := ι)).restrict (Convexity.StdSimplex.coordinateSet ℝ ι)) =
              ∫⁻ x in posSimplex {j : ι // j ≠ i} 1,
                g (stdSimplexAggregate f (stdSimplexCoordMap i x)) := by
            rw [lintegral_map hg (by fun_prop),
              stdSimplexMeasure_restrict_stdSimplex i]
            change ∫⁻ a, (g ∘ stdSimplexAggregate f) a
                ∂Measure.map (stdSimplexCoordMap i)
                  (volume.restrict (stdSimplexFreeCoords i)) = _
            rw [lintegral_map (hg.comp haggregate)
              (measurable_stdSimplexCoordMap i)]
            rw [stdSimplexFreeCoords]
            rfl
          have hright :
              ∫⁻ u, g u ∂((stdSimplexMeasure (ι := κ)).restrict
                  (Convexity.StdSimplex.coordinateSet ℝ κ)).withDensity (stdSimplexAggregateDensity f) =
              ∫⁻ z in posSimplex {j : κ // j ≠ k} 1,
                stdSimplexAggregateDensity f (stdSimplexCoordMap k z) *
                  g (stdSimplexCoordMap k z) := by
            rw [lintegral_withDensity_eq_lintegral_mul _ hdensity hg,
              stdSimplexMeasure_restrict_stdSimplex k]
            let Q : (κ → ℝ) → ENNReal := fun u ↦ stdSimplexAggregateDensity f u * g u
            have hQ : Measurable Q := hdensity.mul hg
            change ∫⁻ a, Q a ∂Measure.map (stdSimplexCoordMap k)
                (volume.restrict (stdSimplexFreeCoords k)) = _
            rw [lintegral_map hQ (measurable_stdSimplexCoordMap k)]
            rw [stdSimplexFreeCoords]
            rfl
          rw [hleft, hright]
          let G :
              ({a : {j : ι // j ≠ i} // p a} → ℝ) ×
                (A → ℝ) → ENNReal := fun q ↦
            g (stdSimplexCoordMap k (FunOnFinite.linearMap ℝ ℝ f' q.1))
          have hG : Measurable G := by
            apply hg.comp
            apply (measurable_stdSimplexCoordMap k).comp
            fun_prop
          let H : ({j : κ // j ≠ k} → ℝ) → ENNReal := fun z ↦
            g (stdSimplexCoordMap k z) * D z
          have hH : Measurable H := by
            apply (hg.comp (measurable_stdSimplexCoordMap k)).mul
            unfold D
            fun_prop
          calc
            ∫⁻ x in posSimplex {j : ι // j ≠ i} 1,
                g (stdSimplexAggregate f (stdSimplexCoordMap i x)) =
                ∫⁻ x in posSimplex {j : ι // j ≠ i} 1, G (e x) := by
              apply setLIntegral_congr_fun (measurableSet_posSimplex _ _)
              intro x _
              change g (stdSimplexAggregate f (stdSimplexCoordMap i x)) =
                g (stdSimplexCoordMap k (FunOnFinite.linearMap ℝ ℝ f' (e x).1))
              rw [stdSimplexAggregate_coordMap_split f k i hi x]
            _ = ∫⁻ u in posSimplex {a : {j : ι // j ≠ i} // p a} 1,
                ∫⁻ v in posSimplex A (1 - ∑ a, u a), G (u, v) := by
              simpa only [A] using
                (lintegral_posSimplex_split_pred p 1 G hG)
            _ = ∫⁻ u in posSimplex {a : {j : ι // j ≠ i} // p a} 1,
                H (FunOnFinite.linearMap ℝ ℝ f' u) := by
              apply setLIntegral_congr_fun (measurableSet_posSimplex _ _)
              intro u hu
              have hr : 0 ≤ 1 - ∑ a, u a := sub_nonneg.mpr hu.2
              change (∫⁻ v in posSimplex A (1 - ∑ a, u a), G (u, v)) =
                H (FunOnFinite.linearMap ℝ ℝ f' u)
              rw [show (∫⁻ v in posSimplex A (1 - ∑ a, u a), G (u, v)) =
                  G (u, Classical.arbitrary (A → ℝ)) *
                    volume (posSimplex A (1 - ∑ a, u a)) by
                rw [← setLIntegral_const]]
              rw [volume_posSimplex A _ hr]
              unfold G H D
              rw [hsum]
            _ = ∫⁻ z in posSimplex {j : κ // j ≠ k} 1,
                H z * posSimplexAggregateDensity f' z :=
              lintegral_posSimplex_comp_aggregate f' hf' 1 zero_le_one H hH
            _ = ∫⁻ z in posSimplex {j : κ // j ≠ k} 1,
                stdSimplexAggregateDensity f (stdSimplexCoordMap k z) *
                  g (stdSimplexCoordMap k z) := by
              apply setLIntegral_congr_fun (measurableSet_posSimplex _ _)
              intro z _
              change H z * posSimplexAggregateDensity f' z =
                stdSimplexAggregateDensity f (stdSimplexCoordMap k z) *
                  g (stdSimplexCoordMap k z)
              rw [stdSimplexAggregateDensity_coordMap_split f k i hi z]
              unfold H D
              ac_rfl

end MeasureTheory.Measure

end StdSimplexCoordinateMeasure
