/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

import LeanPool.CoarseGraining.Homogenization.Geometry.OriginCubeBoundaryPush
import LeanPool.CoarseGraining.Homogenization.Geometry.Translation
import Mathlib.Analysis.Normed.Module.Convex
import Mathlib.MeasureTheory.Measure.Typeclasses.Finite
import Mathlib.Topology.MetricSpace.Bounded

/-! # Convex Domain -/

namespace Homogenization

/-!
# Bounded Open Convex Domains

This file bridges the repository's custom bounded-domain predicate
`IsBoundedDomain` with Mathlib's bounded-set API, records the resulting finite
measure consequences for Lebesgue measure, and packages the domain class
`IsOpenBoundedConvexDomain`.

The intended analytic use is to give future Sobolev/Hodge results a stable
geometric target class that already contains the open cubes and metric balls
used downstream.
-/

theorem Bornology.IsBounded.isBoundedDomain {d : ℕ} {U : Set (Vec d)}
    (hU : Bornology.IsBounded U) : IsBoundedDomain U := by
  classical
  by_cases hd : d = 0
  · refine ⟨1, zero_lt_one, ?_⟩
    subst hd
    intro x hx i
    exact Fin.elim0 i
  · have : NeZero d := ⟨hd⟩
    have hcoord :
        ∀ i : Fin d, Bornology.IsBounded (Function.eval i '' U) := fun i => hU.image_eval i
    have hcoord_bound :
        ∀ i : Fin d, ∃ R : ℝ, 0 < R ∧ ∀ y ∈ Function.eval i '' U, ‖y‖ ≤ R := by
      intro i
      rcases isBounded_iff_forall_norm_le.1 (hcoord i) with ⟨R, hR⟩
      refine ⟨max R 1, zero_lt_one.trans_le (le_max_right _ _), ?_⟩
      intro y hy
      exact (hR y hy).trans (le_max_left _ _)
    choose R hRpos hR using hcoord_bound
    let Rmax : ℝ := Finset.univ.sup' Finset.univ_nonempty R
    have hRmax_pos : 0 < Rmax := by
      let i0 : Fin d := 0
      have hi0 : i0 ∈ (Finset.univ : Finset (Fin d)) := by simp
      have hle : R i0 ≤ Rmax :=
        Finset.le_sup' (s := Finset.univ) (f := R) hi0
      exact lt_of_lt_of_le (hRpos i0) hle
    refine ⟨Rmax, hRmax_pos, ?_⟩
    intro x hx i
    have hxi : ‖x i‖ ≤ R i := hR i (x i) ⟨x, hx, rfl⟩
    have hRi : R i ≤ Rmax :=
      Finset.le_sup' (s := Finset.univ) (f := R) (by simp : i ∈ Finset.univ)
    exact by simpa [Real.norm_eq_abs] using hxi.trans hRi

theorem IsBoundedDomain.isBounded {d : ℕ} {U : Set (Vec d)} (hU : IsBoundedDomain U) :
    Bornology.IsBounded U := by
  rcases hU with ⟨R, hRpos, hR⟩
  refine isBounded_iff_forall_norm_le.2 ⟨R, ?_⟩
  intro x hx
  refine (pi_norm_le_iff_of_nonneg (le_of_lt hRpos)).2 ?_
  intro i
  simpa [Real.norm_eq_abs] using hR x hx i

theorem IsBoundedDomain.volume_lt_top {d : ℕ} {U : Set (Vec d)} (hU : IsBoundedDomain U) :
    MeasureTheory.volume U < ⊤ :=
  hU.isBounded.measure_lt_top

theorem IsBoundedDomain.isFiniteMeasure_restrict_volume
    {d : ℕ} {U : Set (Vec d)} (hU : IsBoundedDomain U) :
    MeasureTheory.IsFiniteMeasure (MeasureTheory.volume.restrict U) := by
  let : Fact (MeasureTheory.volume U < ⊤) := ⟨hU.volume_lt_top⟩
  infer_instance

theorem IsBoundedDomain.norm_le_choose
    {d : ℕ} {U : Set (Vec d)} (hU : IsBoundedDomain U) {x : Vec d}
    (hx : x ∈ U) :
    ‖x‖ ≤ Classical.choose hU := by
  have hRpos : 0 < Classical.choose hU := (Classical.choose_spec hU).1
  have hR : ∀ z ∈ U, ∀ i, |z i| ≤ Classical.choose hU := (Classical.choose_spec hU).2
  refine (pi_norm_le_iff_of_nonneg (le_of_lt hRpos)).2 ?_
  intro i
  simpa [Real.norm_eq_abs] using hR x hx i

theorem IsBoundedDomain.norm_sub_le_two_mul_choose
    {d : ℕ} {U : Set (Vec d)} (hU : IsBoundedDomain U) {x y : Vec d}
    (hx : x ∈ U) (hy : y ∈ U) :
    ‖x - y‖ ≤ 2 * Classical.choose hU := by
  calc
    ‖x - y‖ ≤ ‖x‖ + ‖y‖ := norm_sub_le _ _
    _ ≤ Classical.choose hU + Classical.choose hU := by
          exact add_le_add (hU.norm_le_choose hx) (hU.norm_le_choose hy)
    _ = 2 * Classical.choose hU := by ring

theorem IsBoundedDomain.rayParameter_le_two_mul_choose_of_mem_of_norm_eq_one
    {d : ℕ} {U : Set (Vec d)} (hU : IsBoundedDomain U) {x ω : Vec d} {s : ℝ}
    (hx : x ∈ U) (hs : x + s • ω ∈ U) (hs0 : 0 ≤ s) (hω : ‖ω‖ = 1) :
    s ≤ 2 * Classical.choose hU := by
  have hnorm :
      ‖(x + s • ω) - x‖ ≤ 2 * Classical.choose hU :=
    hU.norm_sub_le_two_mul_choose hs hx
  simpa [norm_smul, hω, abs_of_nonneg hs0] using hnorm

/-- Bounded open convex domains in the ambient space `Vec d = Fin d → ℝ`. -/
def IsOpenBoundedConvexDomain {d : ℕ} (U : Set (Vec d)) : Prop :=
  IsOpen U ∧ IsBoundedDomain U ∧ Convex ℝ U

namespace IsOpenBoundedConvexDomain

theorem isOpen {d : ℕ} {U : Set (Vec d)} (hU : IsOpenBoundedConvexDomain U) :
    IsOpen U :=
  hU.1

theorem isBoundedDomain {d : ℕ} {U : Set (Vec d)} (hU : IsOpenBoundedConvexDomain U) :
    IsBoundedDomain U :=
  hU.2.1

theorem convex {d : ℕ} {U : Set (Vec d)} (hU : IsOpenBoundedConvexDomain U) :
    Convex ℝ U :=
  hU.2.2

theorem volume_lt_top {d : ℕ} {U : Set (Vec d)} (hU : IsOpenBoundedConvexDomain U) :
    MeasureTheory.volume U < ⊤ :=
  hU.isBoundedDomain.volume_lt_top

theorem isFiniteMeasure_restrict_volume {d : ℕ} {U : Set (Vec d)}
    (hU : IsOpenBoundedConvexDomain U) :
    MeasureTheory.IsFiniteMeasure (MeasureTheory.volume.restrict U) :=
  hU.isBoundedDomain.isFiniteMeasure_restrict_volume

theorem isSobolevRegularDomain {d : ℕ} {U : Set (Vec d)}
    (hU : IsOpenBoundedConvexDomain U) :
    IsSobolevRegularDomain U :=
  ⟨hU.isOpen.measurableSet, hU.isBoundedDomain⟩

theorem translateSet {d : ℕ} {U : Set (Vec d)}
    (hU : IsOpenBoundedConvexDomain U) (z : Vec d) :
    IsOpenBoundedConvexDomain (translateSet z U) := by
  refine ⟨?_, ?_, ?_⟩
  · have hopen :
        IsOpen ((fun x : Vec d => x - z) ⁻¹' U) :=
      hU.isOpen.preimage (continuous_id.sub continuous_const)
    simpa [preimage_subRight_eq_translateSet] using hopen
  · rcases hU.isBoundedDomain with ⟨R, hRpos, hR⟩
    refine ⟨R + ‖z‖ + 1, ?_, ?_⟩
    · positivity
    · intro x hx i
      have hxpre : x - z ∈ U := (mem_translateSet_iff_sub_mem).1 hx
      have hcoord : |(x - z) i| ≤ R := hR (x - z) hxpre i
      have hzcoord : |z i| ≤ ‖z‖ := by
        simpa [Real.norm_eq_abs] using norm_le_pi_norm z i
      have hxi : x i = (x - z) i + z i := by
        simp
      calc
        |x i| = |(x - z) i + z i| := by rw [hxi]
        _ ≤ |(x - z) i| + |z i| := abs_add_le _ _
        _ ≤ R + ‖z‖ := add_le_add hcoord hzcoord
        _ ≤ R + ‖z‖ + 1 := by linarith
  · have hconv : Convex ℝ ((fun x : Vec d => x + -z) ⁻¹' U) := by
      simpa using hU.convex.translate_preimage_left (-z)
    simpa [preimage_addNeg_eq_translateSet] using hconv

end IsOpenBoundedConvexDomain

namespace IsSobolevRegularDomain

theorem volume_lt_top {d : ℕ} {U : Set (Vec d)} (hU : IsSobolevRegularDomain U) :
    MeasureTheory.volume U < ⊤ :=
  hU.isBoundedDomain.volume_lt_top

theorem isFiniteMeasure_restrict_volume {d : ℕ} {U : Set (Vec d)}
    (hU : IsSobolevRegularDomain U) :
    MeasureTheory.IsFiniteMeasure (MeasureTheory.volume.restrict U) :=
  hU.isBoundedDomain.isFiniteMeasure_restrict_volume

end IsSobolevRegularDomain

theorem isOpenBoundedConvexDomain_ball {d : ℕ} (x : Vec d) {r : ℝ} (_hr : 0 < r) :
    IsOpenBoundedConvexDomain (Metric.ball x r) := by
  refine ⟨Metric.isOpen_ball, ?_, convex_ball x r⟩
  exact Bornology.IsBounded.isBoundedDomain
    (show Bornology.IsBounded (Metric.ball x r) from Metric.isBounded_ball)

theorem isBoundedDomain_openCubeSet {d : ℕ} (Q : TriadicCube d) :
    IsBoundedDomain (openCubeSet Q) := by
  rw [openCubeSet_eq_pi_Ioo]
  exact Bornology.IsBounded.isBoundedDomain <|
    Bornology.IsBounded.pi fun i =>
      show Bornology.IsBounded
        (Set.Ioo
          ((((Q.index i : ℝ) - (1 / 2 : ℝ)) * cubeScaleFactor Q))
          ((((Q.index i : ℝ) + (1 / 2 : ℝ)) * cubeScaleFactor Q))) from
        Metric.isBounded_Ioo _ _

theorem convex_openCubeSet {d : ℕ} (Q : TriadicCube d) :
    Convex ℝ (openCubeSet Q) := by
  rw [openCubeSet_eq_pi_Ioo]
  refine convex_pi ?_
  intro i hi
  exact convex_Ioo _ _

theorem isOpenBoundedConvexDomain_openCubeSet {d : ℕ} (Q : TriadicCube d) :
    IsOpenBoundedConvexDomain (openCubeSet Q) := by
  exact ⟨isOpen_openCubeSet Q, isBoundedDomain_openCubeSet Q, convex_openCubeSet Q⟩

end Homogenization
