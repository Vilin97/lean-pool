/-
Copyright (c) 2024 Sidharth Hariharan and 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI, Sidharth Hariharan, Gareth Ma, Dean Cureton
-/

module

import all LeanPool.SpherePacking.RadialConstruction
public import Mathlib.Analysis.Fourier.Notation
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Analysis.Normed.Lp.MeasurableSpace
public import Mathlib.Data.ENNReal.Basic
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
public import Mathlib.MeasureTheory.Measure.Haar.OfBasis
public import Mathlib.Topology.MetricSpace.Pseudo.Defs
import Mathlib.Algebra.Module.ZLattice.Covolume
import Mathlib.Algebra.Module.ZLattice.Summable
import Mathlib.Algebra.Order.Archimedean.Real.Hom
import Mathlib.Analysis.Fourier.AddCircleMulti
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.RCLike.Inner
import Mathlib.Data.Finset.Functor
import Mathlib.Dynamics.Ergodic.Action.Regular
import Mathlib.LinearAlgebra.BilinearForm.DualLattice
import Mathlib.RingTheory.Coalgebra.CoassocSimps
import Mathlib.Topology.Compactness.Paracompact
import Mathlib.Topology.Connected.Separation
import Mathlib.Topology.Instances.ENat
import Mathlib.Topology.Separation.Lemmas

/-!
# PackingBound

Periodic sphere packings, Poisson summation, and the linear-programming bound.
-/

section


section

open Metric MeasureTheory

variable {r : ℝ} {ι : Type*} [Fintype ι]

private theorem EuclideanSpace.euclidean_ball_volume_positive (x : EuclideanSpace ℝ
  ι) (hr : 0 < r) :
    0 < volume (ball x r) := by
  simpa only  using! measure_ball_pos (μ := volume) x hr

open Classical in
private theorem EuclideanSpace.euclidean_ball_volume_finite
    (x : EuclideanSpace ℝ ι) :
    volume (ball x r) < ⊤ := by
  simpa only  using! measure_ball_lt_top (μ := volume) (x := x) (r := r)

end

section

open MeasureTheory Metric Filter
open Module

open scoped BigOperators ENNReal Pointwise

public
noncomputable instance CohnElkies.numeralTwoAtLeast : Nat.AtLeastTwo 2 := ⟨by decide⟩

/-- Euclidean coordinate space in a finite dimension is finite-dimensional. -/
public
noncomputable instance CohnElkies.euclideanFiniteDimensional (d : ℕ) :
    FiniteDimensional ℝ (EuclideanSpace ℝ (Fin d)) := by
  infer_instance

/-- Euclidean coordinate space carries its standard Borel structure. -/
public
noncomputable instance CohnElkies.euclideanBorelSpace (d : ℕ) :
    BorelSpace (EuclideanSpace ℝ (Fin d)) := by
  infer_instance

section Definitions

/-- A sphere-packing configuration in Euclidean dimension `d`. -/
public
structure SpherePacking (d : ℕ) where
  /-- The set of packing centers. -/
  centers : Set (EuclideanSpace ℝ (Fin d))
  /-- The minimum prescribed distance between distinct centers. -/
  separation : ℝ
  /-- The prescribed separation is positive. -/
  separation_pos : 0 < separation := by positivity
  /-- Distinct centers are separated by at least `separation`. -/
  centers_dist : Pairwise (separation ≤ dist · · : centers → centers → Prop)

private structure PeriodicSpherePacking (d : ℕ) extends SpherePacking d where
  lattice : Submodule ℤ (EuclideanSpace ℝ (Fin d))
  lattice_action : ∀ ⦃x y⦄, x ∈ lattice → y ∈ centers → x + y ∈ centers
  lattice_discrete : DiscreteTopology lattice := by infer_instance
  lattice_isZLattice : IsZLattice ℝ lattice := by infer_instance

variable {d : ℕ}

attribute [instance] PeriodicSpherePacking.lattice_discrete
attribute [instance] PeriodicSpherePacking.lattice_isZLattice

/-- Distinct centers of a packing obey its separation bound. -/
public
theorem SpherePacking.distinct_centers_separation_bound (S : SpherePacking d) (x y :
  EuclideanSpace ℝ (Fin d))
    (hx : x ∈ S.centers) (hy : y ∈ S.centers) (hxy : x ≠ y) :
    S.separation ≤ dist x y := by
  simpa only  using!
    S.centers_dist (Subtype.coe_ne_coe.mp (by simpa only [ne_eq] using! hxy) : (⟨x,
      hx⟩ : S.centers) ≠ ⟨y, hy⟩)

private noncomputable instance PeriodicSpherePacking.instDiscretePackingLattice (S :
  PeriodicSpherePacking d) :
    DiscreteTopology S.lattice :=
  S.lattice_discrete

private noncomputable instance PeriodicSpherePacking.instFullRankPackingLattice (S :
  PeriodicSpherePacking d) :
    IsZLattice ℝ S.lattice :=
  S.lattice_isZLattice

private noncomputable instance SpherePacking.instDiscretePackingCenters (S : SpherePacking d) :
    DiscreteTopology S.centers :=
  DiscreteTopology.of_forall_le_dist S.separation_pos S.centers_dist

private noncomputable instance PeriodicSpherePacking.latticeCenterTranslationAction (S :
  PeriodicSpherePacking d) :
    AddAction S.lattice S.centers := by
  refine
    { vadd := fun x y => ⟨(x : EuclideanSpace ℝ (Fin d)) + y,
        S.lattice_action x.property y.property⟩
      zero_vadd := ?_
      add_vadd := ?_ }
  · intro x y z
    apply Subtype.ext
    exact add_assoc (x : EuclideanSpace ℝ (Fin d)) y z
  · intro y
    apply Subtype.ext
    exact zero_add (y : EuclideanSpace ℝ (Fin d))

@[reducible] private noncomputable def SpherePacking.occupiedBallRegion (S : SpherePacking d) :
    Set (EuclideanSpace ℝ (Fin d)) :=
  ⋃ x : S.centers, ball (x : EuclideanSpace ℝ (Fin d)) (S.separation / 2)

private noncomputable def SpherePacking.densityInsideRadius (S : SpherePacking d) (R : ℝ) :
    ℝ≥0∞ :=
  volume (S.occupiedBallRegion ∩ ball 0 R) / (volume (ball (0 : EuclideanSpace ℝ (Fin d)) R))

private noncomputable def SpherePacking.upperPackingDensity (S : SpherePacking d) : ℝ≥0∞ :=
  limsup S.densityInsideRadius atTop

private theorem PeriodicSpherePacking.integral_basis_spans_packing_lattice
    (S : PeriodicSpherePacking d) {ι : Type*} (b : Basis ι ℤ S.lattice) :
    Submodule.span ℤ (Set.range (b.ofZLatticeBasis ℝ _)) = S.lattice :=
  Basis.ofZLatticeBasis_span ℝ S.lattice b

private theorem PeriodicSpherePacking.mem_integral_basis_span_iff
    (S : PeriodicSpherePacking d) {ι : Type*} (b : Basis ι ℤ S.lattice) (v) :
    v ∈ Submodule.span ℤ (Set.range (b.ofZLatticeBasis ℝ _)) ↔ v ∈ S.lattice :=
  SetLike.ext_iff.mp (S.integral_basis_spans_packing_lattice b) v

end Definitions

section Scaling
variable {d : ℕ}
open Real

/-- Scale every center and the separation of a packing by a positive factor. -/
public
noncomputable def SpherePacking.rescaleConfiguration (S : SpherePacking d) {c : ℝ} (hc :
  0 < c) :
    SpherePacking d := by
  refine
    { centers := (fun x : EuclideanSpace ℝ (Fin d) => c • x) '' S.centers
      separation := c * S.separation
      separation_pos := mul_pos hc S.separation_pos
      centers_dist := ?_ }
  rintro ⟨_, ⟨x, hx, rfl⟩⟩ ⟨_, ⟨y, hy, rfl⟩⟩ hxy
  have hne : x ≠ y := by
    intro h
    apply hxy
    subst y
    rfl
  have hdist := S.distinct_centers_separation_bound x y hx hy hne
  change c * S.separation ≤ dist (c • x) (c • y)
  simpa only [dist_smul₀, norm_eq_abs, abs_of_pos hc] using
    mul_le_mul_of_nonneg_left hdist hc.le

private noncomputable def PeriodicSpherePacking.rescaleConfiguration (S : PeriodicSpherePacking
  d) {c : ℝ}
    (hc : 0 < c) :
    PeriodicSpherePacking d := by
  let scale : EuclideanSpace ℝ (Fin d) →ₗ[ℤ] EuclideanSpace ℝ (Fin d) :=
    (LinearMap.lsmul ℝ (EuclideanSpace ℝ (Fin d)) c).restrictScalars ℤ
  let scaledLattice : Submodule ℤ (EuclideanSpace ℝ (Fin d)) :=
    S.lattice.map scale
  let latticeEquiv : S.lattice ≃ scaledLattice :=
    { toFun := fun x => ⟨c • (x : EuclideanSpace ℝ (Fin d)),
        ⟨x, x.property, rfl⟩⟩
      invFun := fun y => ⟨c⁻¹ • (y : EuclideanSpace ℝ (Fin d)), by
        obtain ⟨x, hx, hxy⟩ := y.property
        change c • x = (y : EuclideanSpace ℝ (Fin d)) at hxy
        rw [← hxy]
        simpa only [smul_smul, ne_eq, hc.ne', not_false_eq_true, inv_mul_cancel₀, one_smul,
          SetLike.mem_coe] using hx⟩
      left_inv := by
        intro x
        apply Subtype.ext
        simp only [smul_smul, ne_eq, hc.ne', not_false_eq_true, inv_mul_cancel₀, one_smul]
      right_inv := by
        intro y
        apply Subtype.ext
        simp only [smul_smul, ne_eq, hc.ne', not_false_eq_true, mul_inv_cancel₀, one_smul] }
  let latticeHomeomorph : S.lattice ≃ₜ scaledLattice :=
    { latticeEquiv with
      continuous_toFun := by
        change Continuous (fun x : S.lattice =>
          (⟨c • (x : EuclideanSpace ℝ (Fin d)), _⟩ : scaledLattice))
        fun_prop
      continuous_invFun := by
        change Continuous (fun y : scaledLattice =>
          (⟨c⁻¹ • (y : EuclideanSpace ℝ (Fin d)), _⟩ : S.lattice))
        fun_prop }
  letI : DiscreteTopology scaledLattice := latticeHomeomorph.discreteTopology
  have scaled_span_top :
      Submodule.span ℝ (scaledLattice : Set (EuclideanSpace ℝ (Fin d))) = ⊤ := by
    have all_scaled_mem : ∀ x : EuclideanSpace ℝ (Fin d),
        c • x ∈ Submodule.span ℝ
          (scaledLattice : Set (EuclideanSpace ℝ (Fin d))) := by
      intro x
      have hx : x ∈ Submodule.span ℝ
          (S.lattice : Set (EuclideanSpace ℝ (Fin d))) := by
        rw [S.lattice_isZLattice.span_top]
        exact Submodule.mem_top
      induction hx using Submodule.span_induction with
      | mem x hx =>
          apply Submodule.subset_span
          exact ⟨x, hx, rfl⟩
      | zero =>
          simp only [smul_zero, zero_mem]
      | add x y hx hy ihx ihy =>
          simpa only [smul_add] using
            (Submodule.add_mem (Submodule.span ℝ
              (scaledLattice : Set (EuclideanSpace ℝ (Fin d)))) ihx ihy)
      | smul a x hx ih =>
          rw [smul_comm c a]
          exact Submodule.smul_mem (Submodule.span ℝ
            (scaledLattice : Set (EuclideanSpace ℝ (Fin d)))) a ih
    apply top_unique
    intro x _
    simpa only [smul_smul, ne_eq, hc.ne', not_false_eq_true, mul_inv_cancel₀,
      one_smul] using all_scaled_mem (c⁻¹ • x)
  letI : IsZLattice ℝ scaledLattice := ⟨scaled_span_top⟩
  refine
    { toSpherePacking := S.toSpherePacking.rescaleConfiguration hc
      lattice := scaledLattice
      lattice_action := ?_
      lattice_discrete := inferInstance
      lattice_isZLattice := inferInstance }
  rintro _ _ ⟨x, hx, rfl⟩ ⟨y, hy, rfl⟩
  refine ⟨x + y, S.lattice_action hx hy, ?_⟩
  change c • (x + y) = c • x + c • y
  exact smul_add c x y

private lemma SpherePacking.rescale_occupied_region {S : SpherePacking d} {c : ℝ} (hc : 0 < c) :
    (S.rescaleConfiguration hc).occupiedBallRegion = c • S.occupiedBallRegion := by
  have hc0 : (c : ℝ) ≠ 0 := hc.ne'
  ext x
  simp only [occupiedBallRegion, rescaleConfiguration, Set.image_smul, mul_div_assoc,
    Set.iUnion_coe_set,
    Set.mem_smul_set, Set.iUnion_exists, Set.biUnion_and', Set.iUnion_iUnion_eq_right,
      Set.mem_iUnion, mem_ball,
    exists_prop, Set.smul_set_iUnion, _root_.smul_ball hc0, norm_eq_abs, abs_of_pos hc]

end Scaling

section Density

variable {d : ℕ} (S : SpherePacking d)

private noncomputable def PeriodicSpherePackingConstant (d : ℕ) : ℝ≥0∞ :=
  ⨆ S : PeriodicSpherePacking d, S.upperPackingDensity

/-- The supremal upper density among sphere packings in dimension `d`. -/
public
noncomputable def SpherePackingConstant (d : ℕ) : ℝ≥0∞ :=
  ⨆ S : SpherePacking d, S.upperPackingDensity

end Density

section DensityLemmas
namespace SpherePacking

private lemma local_density_le_one {d : ℕ} (S : SpherePacking d) (R : ℝ) :
    S.densityInsideRadius R ≤ 1 := by
  simpa only [densityInsideRadius, Set.iUnion_coe_set] using!
    (ENNReal.div_le_of_le_mul (by simpa only [one_mul, OuterMeasure.measureOf_eq_coe,
      Measure.coe_toOuterMeasure] using! volume.mono Set.inter_subset_right))

private lemma upper_packing_density_le_one {d : ℕ} (S : SpherePacking d) : S.upperPackingDensity
  ≤ 1 := by
  rw [upperPackingDensity]
  exact limsup_le_iSup.trans <| iSup_le fun R => local_density_le_one (S := S) R

private lemma rescale_local_packing_density {d : ℕ} (S : SpherePacking d) {c : ℝ} (hc : 0 < c)
    (R : ℝ) :
    (S.rescaleConfiguration hc).densityInsideRadius (c * R) = S.densityInsideRadius R := by
  have hball : ball (0 : EuclideanSpace ℝ (Fin d)) (c * R) = c • ball 0 R := by
    simpa only [smul_zero, Real.norm_eq_abs, abs_of_pos hc] using!
      (smul_ball hc.ne.symm (0 : EuclideanSpace ℝ (Fin d)) R).symm
  rw [densityInsideRadius, rescale_occupied_region, hball, ← Set.smul_set_inter₀ hc.ne.symm]
  rw [Measure.addHaar_smul_of_nonneg _ hc.le,
    Measure.addHaar_smul_of_nonneg _ hc.le]
  rw [ENNReal.mul_div_mul_left, densityInsideRadius]
  · rw [ne_eq, ENNReal.ofReal_eq_zero, not_le, finrank_euclideanSpace_fin]
    positivity
  · apply ENNReal.ofReal_ne_top

@[simp]
private lemma rescale_local_packing_density_radius {d : ℕ} (S : SpherePacking d) {c : ℝ} (hc : 0
  < c)
    (R : ℝ) :
    (S.rescaleConfiguration hc).densityInsideRadius R = S.densityInsideRadius (R / c) := by
  simpa only [mul_div_assoc', ne_eq, hc.ne.symm, not_false_eq_true,
    mul_div_cancel_left₀] using! (rescale_local_packing_density (S := S) hc (R := R / c))

private lemma rescale_upper_packing_density {d : ℕ} (S : SpherePacking d) {c : ℝ} (hc : 0 < c) :
    (S.rescaleConfiguration hc).upperPackingDensity = S.upperPackingDensity := by
  simpa only [upperPackingDensity, map_div_atTop_eq c hc] using!
    (limsup_congr (Eventually.of_forall fun R => rescale_local_packing_density_radius (S := S)
      hc R)).trans
      (Filter.limsup_comp (u := S.densityInsideRadius) (v := fun R => R / c) (f := atTop))

private theorem packing_supremum_eq_unit_separation {d : ℕ} :
    SpherePackingConstant d = ⨆ (S : SpherePacking d) (_ : S.separation = 1),
      S.upperPackingDensity := by
  rw [iSup_subtype', SpherePackingConstant]
  refine le_antisymm (iSup_le ?_) (iSup_le ?_)
  · intro S
    simpa only [rescale_upper_packing_density] using!
      (le_iSup (fun S : { S : SpherePacking d // S.separation = 1 } ↦ S.val.upperPackingDensity)
        ⟨S.rescaleConfiguration (inv_pos.mpr S.separation_pos),
          inv_mul_cancel₀ S.separation_pos.ne.symm⟩)
  · rintro ⟨S, -⟩
    exact le_iSup upperPackingDensity S

end DensityLemmas.SpherePacking
section BasicResults
open scoped ENNReal
open EuclideanSpace

variable {d : ℕ} (S : SpherePacking d)

private lemma nearby_ball_union_subset_clipped_union
    (X : Set (EuclideanSpace ℝ (Fin d))) (r R : ℝ) :
    ⋃ x ∈ X ∩ ball 0 R, ball x r ⊆ (⋃ x ∈ X, ball x r) ∩ ball 0 (R + r) := by
  intro x hx
  simp only [Set.mem_inter_iff, Set.mem_iUnion, mem_ball, exists_prop, dist_zero_right] at hx ⊢
  obtain ⟨y, ⟨hy₁, hy₂⟩⟩ := hx
  use ⟨y, ⟨hy₁.left, hy₂⟩⟩
  exact lt_of_le_of_lt (norm_le_norm_add_norm_sub' x y) (by gcongr <;> tauto)

private lemma clipped_ball_union_subset_nearby_union
    (X : Set (EuclideanSpace ℝ (Fin d))) (r R : ℝ) :
    (⋃ x ∈ X, ball x r) ∩ ball 0 (R - r) ⊆ ⋃ x ∈ X ∩ ball 0 R, ball x r := by
  intro x hx
  simp only [Set.mem_inter_iff, Set.mem_iUnion, mem_ball, exists_prop, dist_zero_right] at hx ⊢
  obtain ⟨⟨y, ⟨hy₁, hy₂⟩⟩, hx⟩ := hx
  use y, ⟨hy₁, ?_⟩, hy₂
  refine lt_of_le_of_lt (norm_le_norm_add_norm_sub x y) ?_
  rw [← sub_add_cancel R r]
  exact add_lt_add hx (by simpa only [dist_eq_norm] using! hy₂)

private theorem SpherePacking.volume_center_ball_union_eq_tsum
    (R : ℝ) {r' : ℝ} (hr' : r' ≤ S.separation / 2) :
    volume (⋃ x : ↑(S.centers ∩ ball 0 R), ball (x : EuclideanSpace ℝ (Fin d)) r')
      = ∑' x : ↑(S.centers ∩ ball 0 R), volume (ball (x : EuclideanSpace ℝ (Fin d)) r') := by
  have : Countable ↑(S.centers ∩ ball 0 R) :=
    Set.Countable.mono Set.inter_subset_left (countable_of_Lindelof_of_discrete (X := S.centers))
  apply measure_iUnion ?_ (fun _ ↦ measurableSet_ball)
  intro ⟨x, hx⟩ ⟨y, hy⟩ h
  apply ball_disjoint_ball
  simp_rw [ne_eq, Subtype.mk.injEq] at h ⊢
  linarith [S.distinct_centers_separation_bound x y hx.left hy.left h]

private theorem SpherePacking.center_count_in_ball_upper_bound (hd : 0 < d) (R : ℝ) :
    (S.centers ∩ ball 0 R).encard ≤
      volume (S.occupiedBallRegion ∩ ball 0 (R + S.separation / 2))
        / volume (ball (0 : EuclideanSpace ℝ (Fin d)) (S.separation / 2)) := by
  have h := volume.mono <|
    nearby_ball_union_subset_clipped_union S.centers (S.separation / 2) R
  change volume _ ≤ volume _ at h
  simp_rw [Set.biUnion_eq_iUnion, S.volume_center_ball_union_eq_tsum R (le_refl _),
    Measure.addHaar_ball_center, ENNReal.tsum_set_const] at h
  have : Nonempty (Fin d) := Fin.pos_iff_nonempty.mp hd
  rwa [← ENNReal.le_div_iff_mul_le] at h <;> left
  · exact (euclidean_ball_volume_positive _ (by linarith [S.separation_pos])).ne.symm
  · exact (euclidean_ball_volume_finite _).ne

private theorem SpherePacking.center_count_in_ball_lower_bound (R : ℝ) :
    (S.centers ∩ ball 0 R).encard ≥
      volume (S.occupiedBallRegion ∩ ball 0 (R - S.separation / 2))
        / volume (ball (0 : EuclideanSpace ℝ (Fin d)) (S.separation / 2)) := by
  have h := volume.mono <|
    clipped_ball_union_subset_nearby_union S.centers (S.separation / 2) R
  change volume _ ≤ volume _ at h
  simp_rw [Set.biUnion_eq_iUnion, S.volume_center_ball_union_eq_tsum _ (le_refl _),
    Measure.addHaar_ball_center, ENNReal.tsum_set_const] at h
  exact ENNReal.div_le_of_le_mul h

private theorem SpherePacking.finite_centers_inside_ball (R : ℝ) :
    Finite ↑(S.centers ∩ ball 0 R) := by
  apply Set.encard_lt_top_iff.mp
  rcases eq_or_ne d 0 with rfl | hd
  · exact Set.encard_lt_top_iff.2 <| Set.Finite.of_subsingleton (S.centers ∩ ball 0 R)
  · have hd' : 0 < d := Nat.pos_of_ne_zero hd
    have : Nonempty (Fin d) := Fin.pos_iff_nonempty.mp hd'
    apply ENat.toENNReal_lt.mp
    refine lt_of_le_of_lt (S.center_count_in_ball_upper_bound hd' R) ?_
    refine ENNReal.div_lt_top
      (ne_of_lt <|
        lt_of_le_of_lt (volume.mono Set.inter_subset_right)
          (EuclideanSpace.euclidean_ball_volume_finite _))
      (euclidean_ball_volume_positive _ (by linarith [S.separation_pos])).ne.symm

private theorem SpherePacking.local_density_lower_bound (hd : 0 < d) (R : ℝ) :
    S.densityInsideRadius R
      ≥ (S.centers ∩ ball 0 (R - S.separation / 2)).encard
        * volume (ball (0 : EuclideanSpace ℝ (Fin d)) (S.separation / 2))
          / volume (ball (0 : EuclideanSpace ℝ (Fin d)) R) := by
  have : Nonempty (Fin d) := Fin.pos_iff_nonempty.mp hd
  rw [densityInsideRadius, occupiedBallRegion]
  apply ENNReal.div_le_div_right
  exact (ENNReal.le_div_iff_mul_le
    (Or.inl (euclidean_ball_volume_positive _ (by linarith [S.separation_pos])).ne.symm)
    (Or.inl (euclidean_ball_volume_finite _).ne)).1 <|
      (by simpa only [Set.iUnion_coe_set,
        sub_add_cancel] using! (S.center_count_in_ball_upper_bound hd (R - S.separation / 2)))

private theorem SpherePacking.local_density_upper_bound (hd : 0 < d) (R : ℝ) :
    S.densityInsideRadius R
      ≤ (S.centers ∩ ball 0 (R + S.separation / 2)).encard
        * volume (ball (0 : EuclideanSpace ℝ (Fin d)) (S.separation / 2))
          / volume (ball (0 : EuclideanSpace ℝ (Fin d)) R) := by
  have : Nonempty (Fin d) := Fin.pos_iff_nonempty.mp hd
  rw [densityInsideRadius, occupiedBallRegion]
  apply ENNReal.div_le_div_right
  exact (ENNReal.div_le_iff_le_mul
    (Or.inl (euclidean_ball_volume_positive _ (by linarith [S.separation_pos])).ne.symm)
    (Or.inl (euclidean_ball_volume_finite _).ne)).1 <|
      (by simpa only [Set.iUnion_coe_set, add_sub_cancel_right,
        ge_iff_le] using! (S.center_count_in_ball_lower_bound (R + S.separation / 2)))

end BasicResults

end

section

private theorem ENat.tsum_constant_eq_card_mul {α : Type*} (c : ENat) :
    ∑' (_ : α), c = ENat.card α * c := by
  classical
  by_cases hα : Finite α
  · let := Fintype.ofFinite α
    simp only [tsum_fintype, Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
      card_eq_coe_fintype_card]
  · let := not_finite_iff_infinite.mp hα
    by_cases hc : c = 0
    · simp only [hc, tsum_zero, card_eq_top_of_infinite, mul_zero]
    · rw [ENat.card_eq_top_of_infinite, ENat.top_mul hc]
      apply HasSum.tsum_eq
      change Filter.Tendsto (fun s : Finset α => ∑ i ∈ s, c)
        Filter.atTop (nhds (⊤ : ENat))
      apply tendsto_order.2
      constructor
      · intro b hb
        have hbtop : b ≠ ⊤ := ne_of_lt hb
        obtain ⟨s, hs⟩ := Finset.exists_card_eq (α := α) (b.toNat + 1)
        apply Filter.eventually_atTop.2
        refine ⟨s, ?_⟩
        intro t hst
        have hcard : s.card ≤ t.card := Finset.card_le_card hst
        have hbc : b < (s.card : ENat) := by
          rw [← ENat.natCast_toNat hbtop, hs]
          exact_mod_cast Nat.lt_succ_self b.toNat
        have hc_one : (1 : ENat) ≤ c := Order.one_le_iff_ne_zero.2 hc
        calc
          b < (s.card : ENat) := hbc
          _ ≤ (t.card : ENat) := by exact_mod_cast hcard
          _ ≤ (t.card : ENat) * c := by
            simpa only [mul_one] using (mul_le_mul_right hc_one (t.card : ENat))
          _ = ∑ i ∈ t, c := by
            simp only [Finset.sum_const, nsmul_eq_mul]
      · intro b hb
        exact (not_lt_of_ge le_top hb).elim

private theorem ENat.tsum_subtype_constant_eq_encard_mul {α : Type*} (s : Set α) (c : ENat) :
    ∑' (_ : s), c = s.encard * c := by
  rw [ENat.tsum_constant_eq_card_mul, Set.encard]

private theorem ENat.tsum_unit_eq_cardinality {α : Type*} : ∑' (_ : α), 1 = ENat.card α := by
  simp only [tsum_constant_eq_card_mul, mul_one]

private theorem ENat.tsum_subtype_unit_eq_encard {α : Type*} (s : Set α) : ∑' (_ : s),
  1 = s.encard := by
  rw [ENat.tsum_unit_eq_cardinality, Set.encard]

end

section

namespace ENat

open Function Set

section tsum

variable {ι : Sort*} {α β : Type*} {f g : α → ℕ∞} {s t : Set α}

private protected theorem hasSum : HasSum f (⨆ s : Finset α, ∑ a ∈ s, f a) :=
  tendsto_atTop_iSup fun _ _ ↦ Finset.sum_le_sum_of_subset

@[simp] private protected theorem summable : Summable f :=
  ENat.hasSum.summable

private protected theorem tsum_reindex_injective_le {φ : α → β} (hφ : Injective φ) (g : β → ℕ∞) :
    ∑' x, g (φ x) ≤ ∑' y, g y :=
  (ENat.summable (f := fun x => g (φ x))).tsum_le_tsum_of_inj φ hφ (fun _ _ ↦ bot_le)
    (fun _ ↦ le_rfl) (ENat.summable (f := g))

private protected theorem tsum_le_reindex_surjection {φ : α → β} (hφ : Surjective φ) (g : β → ℕ∞) :
    ∑' y, g y ≤ ∑' x, g (φ x) :=
  calc ∑' y, g y = ∑' y, g (φ (surjInv hφ y)) := by simp only [surjInv_eq hφ]
    _ ≤ ∑' x, g (φ x) :=
      ENat.tsum_reindex_injective_le (injective_surjInv hφ) _

private protected theorem tsum_reindex_bijection {φ : α → β} (hφ : φ.Bijective) (g : β → ℕ∞) :
    ∑' x, g (φ x) = ∑' y, g y :=
  (ENat.tsum_reindex_injective_le hφ.injective g).antisymm
    (ENat.tsum_le_reindex_surjection hφ.surjective g)

private protected theorem tsum_dependent_subtype_reindex {β : α → Type*} (f : (Σ a, β a) → ℕ∞) :
    ∑' p : Σ a, β a, f p = ∑' (a) (b), f ⟨a, b⟩ :=
  Summable.tsum_sigma' (fun _ ↦ ENat.summable) ENat.summable

variable {ι : Type*}

private theorem tsum_disjoint_subtype_union (f : α → ℕ∞) (t : ι → Set α) (ht : Pairwise
  (Disjoint on t)) :
    ∑' x : ⋃ i, t i, f x = ∑' i, ∑' x : t i, f x :=
  calc ∑' x : ⋃ i, t i, f x = ∑' x : Σ i, t i, f x.2 :=
    (ENat.tsum_reindex_bijection
      (sigmaToiUnion_bijective t (fun _ _ hij ↦ ht hij)) _).symm
    _ = _ := ENat.tsum_dependent_subtype_reindex _

end ENat.tsum
open Function

private theorem Set.encard_disjoint_union_eq_tsum {ι α : Type*} {s : ι → Set α}
    (hs : Set.PairwiseDisjoint Set.univ s) : (⋃ i, s i).encard = ∑' i, (s i).encard := by
  simpa only [ENat.tsum_subtype_unit_eq_encard] using!
    (ENat.tsum_disjoint_subtype_union (f := fun _ : α => (1 : ℕ∞)) (t := s) (by
      simpa only [PairwiseDisjoint, pairwise_univ] using! hs))

end

section

open ZSpan

variable {E ι K : Type*} [NormedField K] [LinearOrder K] [IsStrictOrderedRing K]
  [NormedAddCommGroup E] [NormedSpace K E] (b : Module.Basis ι K E) [FloorRing K] [Fintype ι]

section BasisIndexEquiv

variable {d : ℕ}

namespace ZLattice

private noncomputable def coordinateIndexEquiv (Λ : Submodule ℤ (EuclideanSpace ℝ (Fin d)))
    [DiscreteTopology Λ] [IsZLattice ℝ Λ] :
    (Module.Free.ChooseBasisIndex ℤ Λ) ≃ (Fin d) := by
  let c := EuclideanSpace.equiv (Fin d) ℝ
  let e := c.toLinearEquiv.restrictScalars ℤ
  let L : Submodule ℤ (Fin d → ℝ) := Λ.map e.toLinearMap
  have hmem (x : EuclideanSpace ℝ (Fin d)) : x ∈ Λ ↔ e x ∈ L := by
    constructor
    · intro hx
      exact ⟨x, hx, rfl⟩
    · rintro ⟨y, hy, he⟩
      exact e.injective he ▸ hy
  let h : Λ ≃ₜ L := c.toHomeomorph.subtype (by simpa only
    [ContinuousLinearEquiv.coe_toHomeomorph, LinearEquiv.restrictScalars_apply,
                                                 ContinuousLinearEquiv.coe_toLinearEquiv,
                                                   e] using hmem)
  letI : DiscreteTopology L := h.discreteTopology
  have hset : (L : Set (Fin d → ℝ)) =
      c.toLinearEquiv.toLinearMap '' (Λ : Set (EuclideanSpace ℝ (Fin d))) := by
    ext x
    change (∃ y, y ∈ Λ ∧ e y = x) ↔
      ∃ y, y ∈ Λ ∧ c.toLinearEquiv.toLinearMap y = x
    simp only [LinearEquiv.restrictScalars_apply, ContinuousLinearEquiv.coe_toLinearEquiv,
      LinearEquiv.coe_coe, e]
  letI : IsZLattice ℝ L := ⟨by
    calc
      Submodule.span ℝ (L : Set (Fin d → ℝ)) =
          Submodule.map c.toLinearEquiv.toLinearMap
            (Submodule.span ℝ (Λ : Set (EuclideanSpace ℝ (Fin d)))) := by
              rw [Submodule.map_span]
              rw [hset]
      _ = Submodule.map c.toLinearEquiv.toLinearMap ⊤ := by
            rw [IsZLattice.span_top]
      _ = ⊤ := Submodule.map_eq_top_iff.mpr rfl⟩
  exact (Module.Free.chooseBasis ℤ Λ).indexEquiv
    ((IsZLattice.basis L).map (e.submoduleMap Λ).symm)

end ZLattice

end BasisIndexEquiv

end

section

open scoped ENNReal
open SpherePacking EuclideanSpace MeasureTheory Metric ZSpan Bornology Module

section aux_lemmas

variable {d : ℕ} (S : PeriodicSpherePacking d) (D : Set (EuclideanSpace ℝ (Fin d)))

private lemma bounded_union_of_center_balls (hD_isBounded : IsBounded D) :
    IsBounded (⋃ x ∈ S.centers ∩ D, ball x (S.separation / 2)) := by
  rcases (isBounded_iff_forall_norm_le).1 hD_isBounded with ⟨L, hL⟩
  refine (isBounded_iff_forall_norm_le).2 ⟨L + S.separation / 2, ?_⟩
  intro x hx
  rcases Set.mem_iUnion₂.1 hx with ⟨y, hy, hx⟩
  exact (norm_le_norm_add_norm_sub' x y).trans <|
    add_le_add (hL y hy.2) (le_of_lt (by simpa only [mem_ball, dist_eq_norm] using! hx))

private lemma pairwise_disjoint_center_balls (D : Set (EuclideanSpace ℝ (Fin d))) :
    Set.PairwiseDisjoint (S.centers ∩ D) (fun x ↦ ball x (S.separation / 2)) := by
  intro x hx y hy hxy
  exact ball_disjoint_ball (by simpa only [add_halves] using!
    S.distinct_centers_separation_bound _ _ hx.left hy.left hxy)

private theorem finite_of_bounded_union_with_uniform_volume
    {ι τ : Type*} {s : Set ι} {f : ι → Set (EuclideanSpace ℝ τ)} {c : ℝ≥0∞} (hc : 0 < c)
    [Fintype τ]
    (h_measurable : ∀ x ∈ s, MeasurableSet (f x))
    (h_bounded : IsBounded (⋃ x ∈ s, f x))
    (h_volume : ∀ x ∈ s, c ≤ volume (f x))
    (h_disjoint : s.PairwiseDisjoint f) :
    s.Finite := by
  classical
  have h_finite_volume : volume (⋃ x ∈ s, f x) < ⊤ :=
    h_bounded.measure_lt_top
  by_contra hs
  have : Infinite s := Set.infinite_coe_iff.mpr hs
  let e : ℕ ↪ s := Set.Infinite.natEmbedding s hs
  have h_sum :
      volume (⋃ n : ℕ, f (e n : ι)) =
        ∑' n : ℕ, volume (f (e n : ι)) := by
    apply measure_iUnion
    · intro m n hmn
      apply h_disjoint (e m).property (e n).property
      intro heq
      exact hmn (e.injective (Subtype.ext heq))
    · intro n
      exact h_measurable (e n) (e n).property
  have h_top : ∑' n : ℕ, volume (f (e n : ι)) = ⊤ := by
    apply top_unique
    calc
      (⊤ : ENNReal) = ∑' _ : ℕ, c := by
        simp only [ENNReal.tsum_const, ENat.card_eq_top_of_infinite, ENat.toENNReal_top, ne_eq,
          hc.ne',
          not_false_eq_true, ENNReal.top_mul]
      _ ≤ ∑' n : ℕ, volume (f (e n : ι)) :=
        ENNReal.tsum_le_tsum fun n => h_volume (e n) (e n).property
  have h_subset :
      (⋃ n : ℕ, f (e n : ι)) ⊆ ⋃ x ∈ s, f x := by
    intro x hx
    obtain ⟨n, hn⟩ := Set.mem_iUnion.mp hx
    exact Set.mem_iUnion₂.mpr ⟨e n, (e n).property, hn⟩
  have h_le : (⊤ : ENNReal) ≤ volume (⋃ x ∈ s, f x) := by
    rw [← h_top, ← h_sum]
    exact volume.mono h_subset
  exact (ne_of_lt h_finite_volume) (top_unique h_le)

private lemma finite_centers_in_bounded_region (hD_isBounded : IsBounded D) (hd : 0 < d) :
    Finite ↑(S.centers ∩ D) := by
  have : Nonempty (Fin d) := Fin.pos_iff_nonempty.mp hd
  refine (Set.finite_coe_iff).2 <| finite_of_bounded_union_with_uniform_volume
      (c := volume (ball (0 : EuclideanSpace ℝ (Fin d)) (S.separation / 2)))
      (hc := by
        simpa only  using!
          euclidean_ball_volume_positive (0 : EuclideanSpace ℝ (Fin d)) (by linarith
            [S.separation_pos]))
      (h_measurable := fun _ _ => measurableSet_ball)
      (h_bounded := bounded_union_of_center_balls S D hD_isBounded)
      (h_volume := fun _ _ => by simp only [Measure.addHaar_ball_center, Std.le_refl])
      (h_disjoint := by simpa only  using! pairwise_disjoint_center_balls S D)

private lemma finite_centers_in_fundamental_region {ι : Type*} [Finite ι] (b : Basis ι ℤ S.lattice)
    (hd : 0 < d) :
    Finite ↑(S.centers ∩ fundamentalDomain (b.ofZLatticeBasis ℝ _)) :=
  finite_centers_in_bounded_region S _ (ZSpan.fundamentalDomain_isBounded _) hd

open scoped Pointwise in
private lemma finite_centers_in_translated_fundamental_region
    {ι : Type*} [Finite ι] (b : Basis ι ℤ S.lattice) (hd : 0 < d) (v : EuclideanSpace ℝ (Fin d)) :
    Finite ↑(S.centers ∩ (v +ᵥ fundamentalDomain (b.ofZLatticeBasis ℝ _))) :=
  finite_centers_in_bounded_region S _ ((ZSpan.fundamentalDomain_isBounded _).vadd v) hd

end aux_lemmas

section Pointwise

open scoped Pointwise

variable {d : ℕ}

private lemma translates_disjoint_of_unique_cover {Λ : Submodule ℤ (EuclideanSpace ℝ (Fin d))}
    {D : Set (EuclideanSpace ℝ (Fin d))}
    (hD_unique_covers : ∀ x, ∃! g : Λ, g +ᵥ x ∈ D) {g h : Λ} (hgh : g ≠ h) :
    Disjoint (g +ᵥ D) (h +ᵥ D) := by
  refine Set.disjoint_left.2 (by
    intro x hxg hxh
    exact hgh <| neg_injective <| (hD_unique_covers x).unique
      (by simpa only [Set.mem_vadd_set_iff_neg_vadd_mem] using! hxg)
      (by simpa only [Set.mem_vadd_set_iff_neg_vadd_mem] using! hxh))

end Pointwise

section instances
variable {d : ℕ} (S : PeriodicSpherePacking d)
open scoped Pointwise

private noncomputable def PeriodicSpherePacking.centerOrbitEquivFundamentalRegion
    (D : Set (EuclideanSpace ℝ (Fin d))) (hD_unique_covers : ∀ x, ∃! g : S.lattice, g +ᵥ x ∈ D) :
    Quotient S.latticeCenterTranslationAction.orbitRel ≃ ↑(S.centers ∩ D) := by
  classical
  have h_vadd (g : S.lattice) (x : S.centers) :
      ((g +ᵥ x : S.centers) : EuclideanSpace ℝ (Fin d)) =
        (g : EuclideanSpace ℝ (Fin d)) + x := by
    rfl
  let f : ↑(S.centers ∩ D) → Quotient S.latticeCenterTranslationAction.orbitRel :=
    fun x => Quotient.mk _ (⟨x.1, x.2.1⟩ : S.centers)
  refine (Equiv.ofBijective f ⟨?_, ?_⟩).symm
  · intro x y hxy
    obtain ⟨g, hg⟩ := Quotient.exact hxy
    have hco : (g : EuclideanSpace ℝ (Fin d)) + y.1 = x.1 := by
      simpa only [h_vadd] using congrArg Subtype.val hg
    have hgD : (g : EuclideanSpace ℝ (Fin d)) + y.1 ∈ D :=
      hco.symm ▸ x.2.2
    have hgzero : g = 0 :=
      (hD_unique_covers y.1).unique hgD (by simpa only [zero_vadd] using y.2.2)
    apply Subtype.ext
    simpa only [hgzero, ZeroMemClass.coe_zero, zero_add] using hco.symm
  · intro q
    refine Quotient.inductionOn q ?_
    intro x
    obtain ⟨g, hg, -⟩ := hD_unique_covers (x : EuclideanSpace ℝ (Fin d))
    let y : S.centers := g +ᵥ x
    have hyD : (y : EuclideanSpace ℝ (Fin d)) ∈ D := by
      rw [show (y : EuclideanSpace ℝ (Fin d)) =
        (g : EuclideanSpace ℝ (Fin d)) + x from h_vadd g x]
      exact hg
    refine ⟨⟨y, y.property, hyD⟩, ?_⟩
    apply Quotient.sound
    refine ⟨g, ?_⟩
    apply Subtype.ext
    simp only [y]

private noncomputable def PeriodicSpherePacking.centerOrbitEquivBasisRegion
    {ι : Type*} [Finite ι] (b : Basis ι ℤ S.lattice) :
    Quotient S.latticeCenterTranslationAction.orbitRel ≃ ↑(S.centers ∩ (fundamentalDomain
      (b.ofZLatticeBasis ℝ _))) := by
  refine S.centerOrbitEquivFundamentalRegion _ ?_
  intro x
  obtain ⟨v, ⟨hv, hv'⟩⟩ := exist_unique_vadd_mem_fundamentalDomain (b.ofZLatticeBasis ℝ _) x
  use ⟨v.val, ?_⟩, ?_, ?_
  · apply Set.mem_of_subset_of_mem ?_ v.prop
    rw [← Submodule.coe_toAddSubgroup, Basis.ofZLatticeBasis_span]
    rfl
  · simp only at hv' ⊢
    convert! hv using 1
  · intro s hs
    rw [← hv' ⟨s, ?_⟩ hs]
    apply Set.mem_of_subset_of_mem _ s.prop
    rw [← Submodule.coe_toAddSubgroup, Basis.ofZLatticeBasis_span]
    rfl

private noncomputable def PeriodicSpherePacking.centerOrbitEquivTranslatedBasisRegion
    {ι : Type*} [Finite ι] (b : Basis ι ℤ S.lattice) (v : EuclideanSpace ℝ (Fin d)) :
    Quotient S.latticeCenterTranslationAction.orbitRel ≃
      ↑(S.centers ∩ (v +ᵥ fundamentalDomain (b.ofZLatticeBasis ℝ _))) := by
  refine S.centerOrbitEquivFundamentalRegion _ ?_
  intro x
  obtain ⟨⟨g, hg_lattice⟩, hg, hg'⟩ :=
    exist_unique_vadd_mem_fundamentalDomain (b.ofZLatticeBasis ℝ _) (x - v)
  refine ⟨⟨g, ?_⟩, ?_, ?_⟩
  · apply Set.mem_of_subset_of_mem ?_ hg_lattice
    rw [← Submodule.coe_toAddSubgroup, Basis.ofZLatticeBasis_span]
    rfl
  · change g + x ∈ v +ᵥ fundamentalDomain (b.ofZLatticeBasis ℝ _)
    rw [Set.mem_vadd_set_iff_neg_vadd_mem]
    change -v + (g + x) ∈ fundamentalDomain (b.ofZLatticeBasis ℝ _)
    simp only [(Submodule.span ℤ (Set.range ⇑(b.ofZLatticeBasis ℝ S.lattice))).mk_vadd,
      vadd_eq_add] at hg
    convert hg using 1; abel
  · intro s hs
    apply Subtype.ext
    have hs' : s.val + (x - v) ∈ fundamentalDomain (b.ofZLatticeBasis ℝ _) := by
      rw [Set.mem_vadd_set_iff_neg_vadd_mem] at hs
      change -v + (s.val + x) ∈ fundamentalDomain (b.ofZLatticeBasis ℝ _) at hs
      convert hs using 1; abel
    have heq := hg' ⟨s.val, by
      apply Set.mem_of_subset_of_mem ?_ s.prop
      rw [← Submodule.coe_toAddSubgroup, Basis.ofZLatticeBasis_span]
      rfl⟩ hs'
    have hvals : s.val = g := congrArg
      (fun z : ↥(Submodule.span ℤ (Set.range ⇑(b.ofZLatticeBasis ℝ S.lattice))) =>
        (z : EuclideanSpace ℝ (Fin d))) heq
    exact hvals

private noncomputable instance (S : PeriodicSpherePacking 0) : Finite S.centers := inferInstance

private noncomputable instance PeriodicSpherePacking.finiteCenterTranslationQuotient :
    Finite (Quotient S.latticeCenterTranslationAction.orbitRel) := by
  let b : Basis _ ℤ S.lattice := (ZLattice.module_free ℝ S.lattice).chooseBasis
  by_cases hd : 0 < d
  · have : Finite ↑(S.centers ∩ fundamentalDomain (b.ofZLatticeBasis ℝ _)) :=
      finite_centers_in_fundamental_region S b hd
    exact Finite.of_equiv _ (S.centerOrbitEquivBasisRegion b).symm
  · have : d = 0 := Nat.eq_zero_of_not_pos hd
    subst this
    exact Quotient.finite (AddAction.orbitRel ..)

private noncomputable instance : Fintype (Quotient S.latticeCenterTranslationAction.orbitRel) :=
  Fintype.ofFinite _

end instances

section centerOrbitCardinality

open scoped Pointwise

open Finset Set

variable {d : ℕ} (S : PeriodicSpherePacking d) (D : Set (EuclideanSpace ℝ (Fin d)))

private noncomputable def PeriodicSpherePacking.centerOrbitCardinality : ℕ :=
  Fintype.card (Quotient S.latticeCenterTranslationAction.orbitRel)

private theorem PeriodicSpherePacking.card_centers_in_fundamental_region
    (hD_isBounded : IsBounded D)
    (hD_unique_covers : ∀ x, ∃! g : S.lattice, g +ᵥ x ∈ D)
    (hd : 0 < d) :
    haveI := @Fintype.ofFinite _ <| finite_centers_in_bounded_region S D hD_isBounded hd
    (S.centers ∩ D).toFinset.card = S.centerOrbitCardinality := by
  rw [centerOrbitCardinality]
  convert! Finset.card_eq_of_equiv_fintype ?_
  simpa only [mem_toFinset,
    mem_inter_iff] using! (S.centerOrbitEquivFundamentalRegion D hD_unique_covers).symm

private theorem PeriodicSpherePacking.encard_centers_in_fundamental_region
    (hD_isBounded : IsBounded D)
    (hD_unique_covers : ∀ x, ∃! g : S.lattice, g +ᵥ x ∈ D)
    (hd : 0 < d) :
    (S.centers ∩ D).encard = S.centerOrbitCardinality := by
  rw [← S.card_centers_in_fundamental_region D hD_isBounded hD_unique_covers hd]
  convert! Set.encard_eq_coe_toFinset_card _

private theorem PeriodicSpherePacking.card_centers_in_translated_region (hd : 0 < d)
    {ι : Type*} [Finite ι] (b : Basis ι ℤ S.lattice) (v : EuclideanSpace ℝ (Fin d)) :
    haveI := @Fintype.ofFinite _ <| finite_centers_in_translated_fundamental_region S b hd v
    (S.centers ∩ (v +ᵥ fundamentalDomain (b.ofZLatticeBasis ℝ _))).toFinset.card =
      S.centerOrbitCardinality := by
  rw [centerOrbitCardinality]
  exact card_eq_of_equiv_fintype (by simpa only [mem_toFinset,
    mem_inter_iff] using! (S.centerOrbitEquivTranslatedBasisRegion b v).symm)

private theorem PeriodicSpherePacking.encard_centers_in_translated_region (hd : 0 < d)
    {ι : Type*} [Finite ι] (b : Basis ι ℤ S.lattice) (v : EuclideanSpace ℝ (Fin d)) :
    (S.centers ∩ (v +ᵥ fundamentalDomain (b.ofZLatticeBasis ℝ _))).encard =
      S.centerOrbitCardinality := by
  rw [← S.card_centers_in_translated_region hd b]
  convert! Set.encard_eq_coe_toFinset_card _

end centerOrbitCardinality

section numReps_aux

variable {d : ℕ}

@[reducible] private noncomputable def PeriodicSpherePacking.instFintypeBoundedCenterRepresentatives
  (S : PeriodicSpherePacking d) (hd : 0 < d)
  {D : Set (EuclideanSpace ℝ (Fin d))} (hD_isBounded : IsBounded D) :
  Fintype ↑(S.centers ∩ D) :=
    @Fintype.ofFinite _ <| finite_centers_in_bounded_region S D hD_isBounded hd

private noncomputable def PeriodicSpherePacking.boundedCenterRepresentativeCount
  (S : PeriodicSpherePacking d) (hd : 0 < d)
  {D : Set (EuclideanSpace ℝ (Fin d))} (hD_isBounded : IsBounded D) : ℕ :=
  letI := S.instFintypeBoundedCenterRepresentatives hd hD_isBounded
  Fintype.card ↑(S.centers ∩ D)

private theorem PeriodicSpherePacking.orbit_cardinality_eq_bounded_representatives (S :
  PeriodicSpherePacking d) (hd : 0 < d)
  {D : Set (EuclideanSpace ℝ (Fin d))} (hD_isBounded : IsBounded D)
  (hD_unique_covers : ∀ x, ∃! g : S.lattice, g +ᵥ x ∈ D) :
  S.centerOrbitCardinality = S.boundedCenterRepresentativeCount hd hD_isBounded := by
  simpa only [boundedCenterRepresentativeCount, Set.fintypeCard_eq_ncard, Set.toFinset_card] using!
    (S.card_centers_in_fundamental_region (D := D) hD_isBounded hD_unique_covers hd).symm

end numReps_aux

section theorem_2_3

variable {d : ℕ} (S : PeriodicSpherePacking d) (D : Set (EuclideanSpace ℝ (Fin d)))

open scoped Pointwise

private theorem iUnion_lattice_inter_ball_sub_vadd_fundamentalDomain_subset_ball
    {ι : Type*} (b : Basis ι ℝ (EuclideanSpace ℝ (Fin d)))
    {L : ℝ} (hL : ∀ x ∈ fundamentalDomain b, ‖x‖ ≤ L) (R : ℝ) :
    ⋃ x ∈ ↑S.lattice ∩ ball (0 : EuclideanSpace ℝ (Fin d)) (R - L),
      x +ᵥ (fundamentalDomain b : Set (EuclideanSpace ℝ (Fin d)))
        ⊆ ball 0 R := by
  intro z hz
  rcases Set.mem_iUnion.mp hz with ⟨x, hz⟩
  rcases Set.mem_iUnion.mp hz with ⟨hx, hz⟩
  rw [Set.mem_vadd_set] at hz
  rcases hz with ⟨y, hy, rfl⟩
  have hxnorm : ‖x‖ < R - L := by
    simpa only [mem_ball, dist_zero_right] using hx.2
  have hynorm : ‖y‖ ≤ L := hL y hy
  have hsum : ‖x + y‖ < R :=
    lt_of_le_of_lt (norm_add_le x y) (by linarith)
  simpa only [vadd_eq_add, mem_ball, dist_zero_right, gt_iff_lt] using hsum

private theorem fundamental_region_translates_disjoint
    {ι : Type*} [Finite ι] (b : Basis ι ℤ S.lattice)
    {x y : EuclideanSpace ℝ (Fin d)} (hx : x ∈ S.lattice) (hy : y ∈ S.lattice) (hxy : x ≠ y) :
    Disjoint (x +ᵥ fundamentalDomain (b.ofZLatticeBasis ℝ _))
      (y +ᵥ fundamentalDomain (b.ofZLatticeBasis ℝ _)) := by
  let Λ : Submodule ℤ (EuclideanSpace ℝ (Fin d)) :=
    Submodule.span ℤ (Set.range (b.ofZLatticeBasis ℝ _))
  have hx' : x ∈ Λ := by simpa [Λ, S.integral_basis_spans_packing_lattice] using! hx
  have hy' : y ∈ Λ := by simpa [Λ, S.integral_basis_spans_packing_lattice] using! hy
  have hxy' : (⟨x, hx'⟩ : Λ) ≠ ⟨y,
    hy'⟩ := fun h => hxy (by simpa only  using! congrArg Subtype.val h)
  simpa only  using!
    (translates_disjoint_of_unique_cover (d := d) (Λ := Λ)
      (D := fundamentalDomain (b.ofZLatticeBasis ℝ _))
      (by intro u; simpa only [mem_fundamentalDomain, Set.mem_Ico] using!
        exist_unique_vadd_mem_fundamentalDomain (b.ofZLatticeBasis ℝ _) u) hxy')

private theorem PeriodicSpherePacking.encard_centers_inter_ball_lower_bound
    (hd : 0 < d) {ι : Type*} [Finite ι] (b : Basis ι ℤ S.lattice)
    {L : ℝ} (hL : ∀ x ∈ fundamentalDomain (b.ofZLatticeBasis ℝ _), ‖x‖ ≤ L) (R : ℝ) :
    (↑S.centers ∩ ball 0 R).encard ≥
      S.centerOrbitCardinality • (↑S.lattice ∩ ball (0 : EuclideanSpace ℝ (Fin d)) (R -
        L)).encard := by
  have hsub := Set.inter_subset_inter_right S.centers
    (iUnion_lattice_inter_ball_sub_vadd_fundamentalDomain_subset_ball
      S (b.ofZLatticeBasis ℝ _) hL R)
  rw [Set.biUnion_eq_iUnion, Set.inter_iUnion] at hsub
  have henc := Set.encard_mono hsub
  rw [Set.encard_disjoint_union_eq_tsum] at henc
  · simp_rw [S.encard_centers_in_translated_region hd] at henc
    · convert! henc.ge
      rw [nsmul_eq_mul, ENat.tsum_subtype_constant_eq_encard_mul, mul_comm]
  · intro ⟨x, hx⟩ _ ⟨y, hy⟩ _ hxy
    have hxy' : x ≠ y := fun h => hxy (Subtype.ext h)
    refine Set.disjoint_left.2 fun u hux huy =>
      (Set.disjoint_left.1 (fundamental_region_translates_disjoint (S := S) b hx.left hy.left hxy'))
        hux.right huy.right

private theorem ball_subset_iUnion_lattice_inter_ball_add_vadd_fundamentalDomain
    {ι : Type*} [Finite ι] (b : Basis ι ℤ S.lattice)
    {L : ℝ} (hL : ∀ x ∈ fundamentalDomain (b.ofZLatticeBasis ℝ _), ‖x‖ ≤ L) (R : ℝ) :
    ball 0 R
      ⊆ ⋃ x ∈ ↑S.lattice ∩ ball (0 : EuclideanSpace ℝ (Fin d)) (R + L),
        x +ᵥ (fundamentalDomain (b.ofZLatticeBasis ℝ _) : Set (EuclideanSpace ℝ (Fin d))) := by
  let : Fintype ι := Fintype.ofFinite ι
  intro x hx
  refine Set.mem_iUnion₂.2 ⟨floor (b.ofZLatticeBasis ℝ _) x, ?_, ?_⟩
  · refine ⟨?_, ?_⟩
    · rw [SetLike.mem_coe, ← S.mem_integral_basis_span_iff b]
      exact Submodule.coe_mem _
    · rw [mem_ball_zero_iff] at hx ⊢
      have hfloor : ‖floor (b.ofZLatticeBasis ℝ _) x‖ = ‖x - fract (b.ofZLatticeBasis ℝ _) x‖ := by
        have hfract :
            x - fract (b.ofZLatticeBasis ℝ _) x =
              (floor (b.ofZLatticeBasis ℝ _) x :
                EuclideanSpace ℝ (Fin d)) := by
          simp only [fract, sub_sub_cancel]
        rw [hfract]
        rfl
      refine lt_of_le_of_lt (hfloor.le.trans (norm_sub_le _ _)) ?_
      exact add_lt_add_of_lt_of_le hx (hL _ (fract_mem_fundamentalDomain _ _))
  · rw [Set.mem_vadd_set_iff_neg_vadd_mem, vadd_eq_add, neg_add_eq_sub]
    exact fract_mem_fundamentalDomain (b.ofZLatticeBasis ℝ _) x

private theorem PeriodicSpherePacking.encard_centers_inter_ball_upper_bound
    (hd : 0 < d) {ι : Type*} [Finite ι] (b : Basis ι ℤ S.lattice)
    {L : ℝ} (hL : ∀ x ∈ fundamentalDomain (b.ofZLatticeBasis ℝ _), ‖x‖ ≤ L) (R : ℝ) :
    (↑S.centers ∩ ball 0 R).encard
      ≤ S.centerOrbitCardinality • (↑S.lattice ∩ ball (0 : EuclideanSpace ℝ (Fin d)) (R +
        L)).encard := by
  have hsub := Set.inter_subset_inter_right S.centers
    (ball_subset_iUnion_lattice_inter_ball_add_vadd_fundamentalDomain S b hL R)
  rw [Set.biUnion_eq_iUnion, Set.inter_iUnion] at hsub
  have henc := Set.encard_mono hsub
  rw [Set.encard_disjoint_union_eq_tsum] at henc
  · simp_rw [S.encard_centers_in_translated_region hd] at henc
    · convert! henc
      rw [nsmul_eq_mul, ENat.tsum_subtype_constant_eq_encard_mul, mul_comm]
  · intro ⟨x, hx⟩ _ ⟨y, hy⟩ _ hxy
    have hxy' : x ≠ y := fun h => hxy (Subtype.ext h)
    refine Set.disjoint_left.2 fun u hux huy =>
      (Set.disjoint_left.1 (fundamental_region_translates_disjoint (S := S) b hx.left hy.left hxy'))
        hux.right huy.right

end theorem_2_3

section theorem_2_2

open scoped Pointwise
variable {d : ℕ} (S : PeriodicSpherePacking d)
  {ι : Type*} [Finite ι]
  (D : Set (EuclideanSpace ℝ (Fin d))) {L : ℝ} (R : ℝ)

private theorem lattice_region_is_additive_fundamental_domain
    (hD_unique_covers : ∀ x, ∃! g : S.lattice, g +ᵥ x ∈ D) (hD_measurable : MeasurableSet D) :
    IsAddFundamentalDomain S.lattice D :=
  MeasureTheory.IsAddFundamentalDomain.mk' (μ := volume) hD_measurable.nullMeasurableSet
    hD_unique_covers

private theorem ball_covered_by_nearby_lattice_translates
    (hD_unique_covers : ∀ x, ∃! g : S.lattice, g +ᵥ x ∈ D) (hL : ∀ x ∈ D, ‖x‖ ≤ L) :
    ball 0 (R - L) ⊆ ⋃ x ∈ ↑S.lattice ∩ ball (0 : EuclideanSpace ℝ (Fin d)) R, (x +ᵥ D) := by
  intro x hx
  have hx' : ‖x‖ < R - L := by simpa only [mem_ball, dist_zero_right] using! hx
  rcases hD_unique_covers x with ⟨g, hg, -⟩
  simp_rw [Set.mem_iUnion, exists_prop, Set.mem_inter_iff]
  refine ⟨-g.val, ⟨⟨by simp only [SetLike.mem_coe, neg_mem_iff, SetLike.coe_mem], ?_⟩, ?_⟩⟩
  · have : ‖g.val‖ < R := by
      have htri : ‖g.val‖ ≤ ‖g.val + x‖ + ‖x‖ := by
        simpa only [sub_eq_add_neg, add_assoc, add_neg_cancel,
          add_zero] using! (norm_sub_le (a := g.val + x) (b := x))
      refine lt_of_le_of_lt htri ?_
      calc
        ‖g.val + x‖ + ‖x‖ < L + (R - L) := add_lt_add_of_le_of_lt (hL _ (by simpa only  using!
          hg)) hx'
        _ = R := by abel
    simpa only [mem_ball, dist_zero_right, norm_neg, gt_iff_lt] using! this
  · exact (Set.mem_vadd_set_iff_neg_vadd_mem).2 (by simpa only [neg_neg, vadd_eq_add] using! hg)

private noncomputable instance (E : Type*) [AddCommGroup E] [MeasurableSpace E] [MeasurableAdd
  E] [Module ℤ E] (μ : Measure E) [μ.IsAddLeftInvariant] (s : Submodule ℤ E) :
    VAddInvariantMeasure s E μ where
  measure_preimage_vadd c t ht := by
    simp only [Submodule.vadd_def, vadd_eq_add, measure_preimage_add]

private theorem PeriodicSpherePacking.encard_lattice_inter_ball_ge_volume_ball_sub_div_volume
    (hD_unique_covers : ∀ x, ∃! g : S.lattice, g +ᵥ x ∈ D)
    (hL : ∀ x ∈ D, ‖x‖ ≤ L) :
    (↑S.lattice ∩ ball (0 : EuclideanSpace ℝ (Fin d)) R).encard
      ≥ volume (ball (0 : EuclideanSpace ℝ (Fin d)) (R - L)) / volume D := by
  have hcover := volume.mono
    (ball_covered_by_nearby_lattice_translates (S := S) (D := D) (R := R)
      hD_unique_covers hL)
  rw [Set.biUnion_eq_iUnion] at hcover
  have hcount : Set.Countable
      ((S.lattice : Set (EuclideanSpace ℝ (Fin d))) ∩ ball 0 R) :=
    Set.Countable.mono Set.inter_subset_left
      (countable_of_Lindelof_of_discrete (X := S.lattice))
  let : Countable
      ↑((S.lattice : Set (EuclideanSpace ℝ (Fin d))) ∩ ball 0 R) := hcount
  apply ENNReal.div_le_of_le_mul
  refine hcover.trans ?_
  calc
    volume (⋃ x : ↑((S.lattice : Set (EuclideanSpace ℝ (Fin d))) ∩ ball 0 R),
      (x : EuclideanSpace ℝ (Fin d)) +ᵥ D)
      ≤ ∑' x : ↑((S.lattice : Set (EuclideanSpace ℝ (Fin d))) ∩ ball 0 R),
        volume ((x : EuclideanSpace ℝ (Fin d)) +ᵥ D) := measure_iUnion_le _
    _ = ∑' _ : ↑((S.lattice : Set (EuclideanSpace ℝ (Fin d))) ∩ ball 0 R),
      volume D := by simp_rw [measure_vadd]
    _ = _ := ENNReal.tsum_set_const _ _

private theorem nearby_lattice_translates_subset_expanded_ball (hL : ∀ x ∈ D, ‖x‖ ≤ L) :
    ⋃ x ∈ ↑S.lattice ∩ ball (0 : EuclideanSpace ℝ (Fin d)) R, (x +ᵥ D) ⊆ ball 0 (R + L) := by
  intro x hx
  rw [mem_ball_zero_iff]
  rcases (by simpa only [Set.mem_inter_iff, SetLike.mem_coe, mem_ball, dist_zero_right,
    Set.mem_iUnion, exists_prop] using! hx) with
    ⟨i, ⟨-, hi_ball⟩, hi_mem⟩
  have hi_ball' : ‖i‖ < R := by simpa only  using! hi_ball
  have hi_mem' : ‖-i + x‖ ≤ L := hL _ (Set.mem_vadd_set_iff_neg_vadd_mem.mp hi_mem)
  calc
    _ = ‖i + (-i + x)‖ := by congr; abel
    _ ≤ ‖i‖ + ‖-i + x‖ := norm_add_le _ _
    _ < R + L := add_lt_add_of_lt_of_le hi_ball' hi_mem'

private theorem PeriodicSpherePacking.encard_lattice_inter_ball_le_volume_ball_add_div_volume
    (hD_unique_covers : ∀ x, ∃! g : S.lattice, g +ᵥ x ∈ D) (hD_measurable : MeasurableSet D)
    (hL : ∀ x ∈ D, ‖x‖ ≤ L) (hd : 0 < d) :
    (↑S.lattice ∩ ball (0 : EuclideanSpace ℝ (Fin d)) R).encard
      ≤ volume (ball (0 : EuclideanSpace ℝ (Fin d)) (R + L)) / volume D := by
  classical
  let T : Set (EuclideanSpace ℝ (Fin d)) := ↑S.lattice ∩ ball 0 R
  let : Countable T :=
    Set.Countable.mono Set.inter_subset_left
      (countable_of_Lindelof_of_discrete (X := S.lattice))
  have hfinite : volume D ≠ ⊤ := ne_of_lt <|
    ((Metric.isBounded_closedBall : Bornology.IsBounded
        (Metric.closedBall (0 : EuclideanSpace ℝ (Fin d)) L)).subset
      (fun x hx => by simpa only [mem_closedBall, dist_zero_right] using hL x hx)).measure_lt_top
  let : Nonempty (Fin d) := Fin.pos_iff_nonempty.mp hd
  have hnonzero : volume D ≠ 0 :=
    (lattice_region_is_additive_fundamental_domain S D hD_unique_covers
      hD_measurable).measure_ne_zero
      (fun hv => by
        have hp := euclidean_ball_volume_positive (0 : EuclideanSpace ℝ (Fin d)) (by norm_num :
          (0 : ℝ) < 1)
        simp only [hv, Measure.coe_zero, Pi.zero_apply, lt_self_iff_false] at hp)
  apply (ENNReal.le_div_iff_mul_le (Or.inl hnonzero) (Or.inl hfinite)).2
  calc
    (T.encard : ℝ≥0∞) * volume D =
        ∑' x : T, volume ((x : EuclideanSpace ℝ (Fin d)) +ᵥ D) := by
          simp_rw [measure_vadd]
          exact (ENNReal.tsum_set_const T (volume D)).symm
    _ = volume (⋃ x : T, (x : EuclideanSpace ℝ (Fin d)) +ᵥ D) := by
      symm
      apply measure_iUnion
      · intro x y hxy
        exact translates_disjoint_of_unique_cover (Λ := S.lattice) (D := D)
          hD_unique_covers (g := ⟨x, x.property.1⟩) (h := ⟨y, y.property.1⟩)
          (fun h => hxy (Subtype.ext
            (congrArg (fun z : S.lattice => (z : EuclideanSpace ℝ (Fin d))) h)))
      · intro x
        have hxset : (x : EuclideanSpace ℝ (Fin d)) +ᵥ D =
            (fun z : EuclideanSpace ℝ (Fin d) => -(x : EuclideanSpace ℝ (Fin d)) + z) ⁻¹' D := by
          ext z
          simp only [Set.mem_vadd_set_iff_neg_vadd_mem, Set.mem_preimage, vadd_eq_add]
        rw [hxset]
        exact hD_measurable.preimage
          (measurable_const.add measurable_id :
            Measurable (fun z : EuclideanSpace ℝ (Fin d) => -(x : EuclideanSpace ℝ (Fin d)) + z))
    _ ≤ volume (ball (0 : EuclideanSpace ℝ (Fin d)) (R + L)) := by
      apply volume.mono
      simpa only [Set.iUnion_coe_set, Set.mem_inter_iff, SetLike.mem_coe, mem_ball, dist_zero_right,
        Set.iUnion_subset_iff, and_imp, T] using
        (nearby_lattice_translates_subset_expanded_ball (S := S) (D := D) (R := R) hL)

open ZSpan

variable (b : Basis ι ℤ S.lattice)

private theorem
    PeriodicSpherePacking.encard_lattice_inter_ball_ge_volume_ball_sub_div_volume_fundamentalDomain
    (hL : ∀ x ∈ fundamentalDomain (b.ofZLatticeBasis ℝ _), ‖x‖ ≤ L) :
    (↑S.lattice ∩ ball (0 : EuclideanSpace ℝ (Fin d)) R).encard
      ≥ volume (ball (0 : EuclideanSpace ℝ (Fin d)) (R - L))
        / volume (fundamentalDomain (b.ofZLatticeBasis ℝ _)) := by
  refine S.encard_lattice_inter_ball_ge_volume_ball_sub_div_volume
    _ R ?_ hL
  intro x
  rcases exist_unique_vadd_mem_fundamentalDomain (b.ofZLatticeBasis ℝ _) x with
    ⟨⟨v, hv⟩, hvD, hvuniq⟩
  refine ⟨⟨v, by simpa only [S.integral_basis_spans_packing_lattice] using! hv⟩, hvD, ?_⟩
  rintro ⟨y, hy⟩ hyD
  have := hvuniq ⟨y, by simpa only [S.integral_basis_spans_packing_lattice] using! hy⟩ hyD
  exact Subtype.ext (by simpa only  using! congrArg Subtype.val this)

private theorem
    PeriodicSpherePacking.encard_lattice_inter_ball_le_volume_ball_add_div_volume_fundamentalDomain
    (hL : ∀ x ∈ fundamentalDomain (b.ofZLatticeBasis ℝ _), ‖x‖ ≤ L) (hd : 0 < d) :
    (↑S.lattice ∩ ball (0 : EuclideanSpace ℝ (Fin d)) R).encard
      ≤ volume (ball (0 : EuclideanSpace ℝ (Fin d)) (R + L))
        / volume (fundamentalDomain (b.ofZLatticeBasis ℝ _)) := by
  refine S.encard_lattice_inter_ball_le_volume_ball_add_div_volume
    _ R ?_ (fundamentalDomain_measurableSet _) hL hd
  intro x
  rcases exist_unique_vadd_mem_fundamentalDomain (b.ofZLatticeBasis ℝ _) x with
    ⟨⟨v, hv⟩, hvD, hvuniq⟩
  refine ⟨⟨v, by simpa only [S.integral_basis_spans_packing_lattice] using! hv⟩, hvD, ?_⟩
  rintro ⟨y, hy⟩ hyD
  have := hvuniq ⟨y, by simpa only [S.integral_basis_spans_packing_lattice] using! hy⟩ hyD
  exact Subtype.ext (by simpa only  using! congrArg Subtype.val this)

section finiteDensity_limit

open MeasureTheory Measure Metric ZSpan

variable
  {d : ℕ} {S : PeriodicSpherePacking d}
  {ι : Type*} [Finite ι] (b : Basis ι ℤ S.lattice) {L : ℝ} (R : ℝ)

private theorem finiteDensity_le_numReps_mul_volume_ball_ratio
    (hL : ∀ x ∈ fundamentalDomain (b.ofZLatticeBasis ℝ _), ‖x‖ ≤ L) (hd : 0 < d) :
    S.densityInsideRadius R ≤
      S.centerOrbitCardinality
        * volume (ball (0 : EuclideanSpace ℝ (Fin d)) (S.separation / 2))
          / volume (fundamentalDomain (b.ofZLatticeBasis ℝ _))
            * (volume (ball (0 : EuclideanSpace ℝ (Fin d)) (R + S.separation / 2 + L * 2))
              / volume (ball (0 : EuclideanSpace ℝ (Fin d)) R)) := calc
  _ ≤ (S.centers ∩ ball 0 (R + S.separation / 2)).encard
      * volume (ball (0 : EuclideanSpace ℝ (Fin d)) (S.separation / 2))
        / volume (ball (0 : EuclideanSpace ℝ (Fin d)) R) :=
    S.local_density_upper_bound hd R
  _ ≤ S.centerOrbitCardinality
        • (↑S.lattice ∩ ball (0 : EuclideanSpace ℝ (Fin d)) (R + S.separation / 2 + L)).encard
          * volume (ball (0 : EuclideanSpace ℝ (Fin d)) (S.separation / 2))
            / volume (ball (0 : EuclideanSpace ℝ (Fin d)) R) := by
    gcongr
    simpa only [nsmul_eq_mul, ENat.toENNReal_mul, ENat.toENNReal_coe] using! ENat.toENNReal_le.mpr
      (S.encard_centers_inter_ball_upper_bound hd b hL _)
  _ ≤ S.centerOrbitCardinality
        * (volume (ball (0 : EuclideanSpace ℝ (Fin d)) (R + S.separation / 2 + L + L))
          / volume (fundamentalDomain (b.ofZLatticeBasis ℝ _)))
            * volume (ball (0 : EuclideanSpace ℝ (Fin d)) (S.separation / 2))
              / volume (ball (0 : EuclideanSpace ℝ (Fin d)) R) := by
    rw [nsmul_eq_mul]
    gcongr
    exact S.encard_lattice_inter_ball_le_volume_ball_add_div_volume_fundamentalDomain _ b hL hd
  _ = S.centerOrbitCardinality
        * volume (ball (0 : EuclideanSpace ℝ (Fin d)) (S.separation / 2))
          / volume (fundamentalDomain (b.ofZLatticeBasis ℝ _))
            * (volume (ball (0 : EuclideanSpace ℝ (Fin d)) (R + S.separation / 2 + L * 2))
              / volume (ball (0 : EuclideanSpace ℝ (Fin d)) R)) := by
    rw [← mul_div_assoc, ← mul_div_assoc, mul_two, ← add_assoc, ← ENNReal.mul_div_right_comm,
      ← ENNReal.mul_div_right_comm, mul_assoc, mul_assoc]
    congr 3
    rw [mul_comm]

private theorem finiteDensity_ge_numReps_mul_volume_ball_ratio
    (hL : ∀ x ∈ fundamentalDomain (b.ofZLatticeBasis ℝ _), ‖x‖ ≤ L) (hd : 0 < d) :
    S.densityInsideRadius R ≥
      S.centerOrbitCardinality
        * volume (ball (0 : EuclideanSpace ℝ (Fin d)) (S.separation / 2))
          / volume (fundamentalDomain (b.ofZLatticeBasis ℝ _))
            * (volume (ball (0 : EuclideanSpace ℝ (Fin d)) (R - S.separation / 2 - L * 2))
              / volume (ball (0 : EuclideanSpace ℝ (Fin d)) R)) := by
  calc
    _ ≥ (S.centers ∩ ball 0 (R - S.separation / 2)).encard
        * volume (ball (0 : EuclideanSpace ℝ (Fin d)) (S.separation / 2))
          / volume (ball (0 : EuclideanSpace ℝ (Fin d)) R) :=
      S.local_density_lower_bound hd R
    _ ≥ S.centerOrbitCardinality
        • (↑S.lattice ∩ ball (0 : EuclideanSpace ℝ (Fin d))
          (R - S.separation / 2 - L)).encard
            * volume (ball (0 : EuclideanSpace ℝ (Fin d)) (S.separation / 2))
              / volume (ball (0 : EuclideanSpace ℝ (Fin d)) R) := by
      gcongr
      simpa only [nsmul_eq_mul, ENat.toENNReal_mul, ENat.toENNReal_coe] using ENat.toENNReal_le.mpr
        (S.encard_centers_inter_ball_lower_bound
          hd b hL (R - S.separation / 2))
    _ ≥ S.centerOrbitCardinality
        * (volume (ball (0 : EuclideanSpace ℝ (Fin d))
          (R - S.separation / 2 - L - L))
            / volume (fundamentalDomain (b.ofZLatticeBasis ℝ _)))
              * volume (ball (0 : EuclideanSpace ℝ (Fin d)) (S.separation / 2))
                / volume (ball (0 : EuclideanSpace ℝ (Fin d)) R) := by
      rw [nsmul_eq_mul]
      gcongr
      exact S.encard_lattice_inter_ball_ge_volume_ball_sub_div_volume_fundamentalDomain
        _ b hL
    _ = _ := by
      rw [show R - S.separation / 2 - L - L =
        R - S.separation / 2 - L * 2 by ring]
      simp only [div_eq_mul_inv]
      ac_rfl

open Filter Topology

section VolumeBallRatio

open scoped Topology NNReal
open Asymptotics Filter ENNReal EuclideanSpace

private theorem volume_ball_add_div_volume_ball_add_tendsto_one_of_nonneg
    {d : ℕ} {C C' : ℝ} (hd : 0 < d) (hC : 0 ≤ C) (hC' : 0 ≤ C') :
      Tendsto (fun R ↦ volume (ball (0 : EuclideanSpace ℝ (Fin d)) (R + C))
        / volume (ball (0 : EuclideanSpace ℝ (Fin d)) (R + C'))) atTop (𝓝 1) := by
  have : Nonempty (Fin d) := Fin.pos_iff_nonempty.mp hd
  have hshift : Tendsto (fun R : ℝ => R + C') atTop atTop :=
    tendsto_atTop_add_const_right _ C' tendsto_id
  have herror : Tendsto (fun R : ℝ => (C - C') / (R + C')) atTop (𝓝 0) := by
    simpa only [div_eq_mul_inv, Function.comp_apply, mul_zero] using
      (tendsto_inv_atTop_zero.comp hshift).const_mul (C - C')
  have hratio : Tendsto (fun R : ℝ => (R + C) / (R + C')) atTop (𝓝 1) := by
    have hsum : Tendsto (fun R : ℝ => 1 + (C - C') / (R + C')) atTop (𝓝 1) := by
      simpa only [add_zero] using tendsto_const_nhds.add herror
    apply Tendsto.congr' (f₁ := fun R : ℝ => 1 + (C - C') / (R + C')) ?_ hsum
    filter_upwards [eventually_ge_atTop (1 : ℝ)] with R hR
    have hden : R + C' ≠ 0 := ne_of_gt (by linarith)
    field_simp; ring
  have hpow : Tendsto (fun R : ℝ => ((R + C) / (R + C')) ^ d) atTop (𝓝 1) := by
    simpa only [one_pow] using hratio.pow d
  have henn : Tendsto
      (fun R : ℝ => ENNReal.ofReal (((R + C) / (R + C')) ^ d)) atTop (𝓝 1) := by
    simpa only [ofReal_one] using tendsto_ofReal hpow
  apply Tendsto.congr'
    (f₁ := fun R : ℝ => ENNReal.ofReal (((R + C) / (R + C')) ^ d)) ?_ henn
  filter_upwards [eventually_ge_atTop (1 : ℝ)] with R hR
  symm
  rw [volume_ball, volume_ball, Fintype.card_fin, ← ENNReal.ofReal_pow,
    ← ENNReal.ofReal_mul, ← ENNReal.ofReal_pow, ← ENNReal.ofReal_mul,
    ← ENNReal.ofReal_div_of_pos, mul_div_mul_right, ← div_pow]
  <;> positivity

private theorem Filter.atTop_invariant_under_translation {β : Type*} {f : ℝ → β} (C : ℝ) (α :
  Filter β) :
    Tendsto f atTop α ↔ Tendsto (fun x ↦ f (x + C)) atTop α := by
  have hmap : Filter.map (fun x : ℝ => x + C) atTop = atTop := by
    simpa only  using! (Filter.map_add_atTop_eq (α := ℝ) (k := C))
  constructor <;> intro hf
  · exact tendsto_map'_iff.mp (by simpa only [hmap] using! hf)
  · have : Tendsto f (Filter.map (fun x : ℝ => x + C) atTop) α := tendsto_map'_iff.mpr hf
    simpa only [hmap] using! this

private theorem volume_ball_add_div_volume_ball_add_tendsto_one {d : ℕ} {C C' : ℝ} (hd : 0 < d) :
    Tendsto (fun R ↦ volume (ball (0 : EuclideanSpace ℝ (Fin d)) (R + C))
      / volume (ball (0 : EuclideanSpace ℝ (Fin d)) (R + C'))) atTop (𝓝 1) := by
  have hC₀ : 0 ≤ max (-C) (-C') + C := by linarith [le_max_left (-C) (-C')]
  have hC'₀ : 0 ≤ max (-C) (-C') + C' := by linarith [le_max_right (-C) (-C')]
  refine (Filter.atTop_invariant_under_translation (f := fun R ↦
      volume (ball (0 : EuclideanSpace ℝ (Fin d)) (R + C)) /
        volume (ball (0 : EuclideanSpace ℝ (Fin d)) (R + C'))) (max (-C) (-C')) _).mpr ?_
  simpa only [add_assoc] using!
    volume_ball_add_div_volume_ball_add_tendsto_one_of_nonneg (d := d) (C := max (-C) (-C') + C)
      (C' := max (-C) (-C') + C') hd hC₀ hC'₀

end VolumeBallRatio
end finiteDensity_limit
end theorem_2_2

end

section

open scoped ENNReal
open SpherePacking EuclideanSpace MeasureTheory Metric ZSpan Bornology Module
open Filter
open scoped Pointwise
open scoped Topology

variable {d : ℕ}

section DensityEqFdDensity

variable
  {d : ℕ} {S : PeriodicSpherePacking d}
  {ι : Type*} [Finite ι] (b : Basis ι ℤ S.lattice) {L : ℝ} (R : ℝ)

private lemma PeriodicSpherePacking.local_packing_density_tends_to_formula
    (hL : ∀ x ∈ fundamentalDomain (b.ofZLatticeBasis ℝ _), ‖x‖ ≤ L) (hd : 0 < d) :
    Tendsto S.densityInsideRadius atTop
      (𝓝 (S.centerOrbitCardinality * volume (ball (0 : EuclideanSpace ℝ (Fin d)) (S.separation / 2))
        / volume (fundamentalDomain (b.ofZLatticeBasis ℝ _)))) := by
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le ?_ ?_
      (finiteDensity_ge_numReps_mul_volume_ball_ratio b · hL hd)
      (finiteDensity_le_numReps_mul_volume_ball_ratio b · hL hd)
  · rw [show ∀ a : ENNReal, 𝓝 a = 𝓝 (a * 1) by intro; rw [mul_one]]
    apply ENNReal.Tendsto.const_mul
    · simp_rw [sub_sub, sub_eq_add_neg]
      convert! volume_ball_add_div_volume_ball_add_tendsto_one hd (C := -(S.separation / 2 + L * 2))
      rw [add_zero]
    · left
      exact one_ne_zero
  · rw [show ∀ a : ENNReal, 𝓝 a = 𝓝 (a * 1) by intro; rw [mul_one]]
    apply ENNReal.Tendsto.const_mul
    · simp_rw [add_assoc]
      convert! volume_ball_add_div_volume_ball_add_tendsto_one hd (C := S.separation / 2 + L * 2)
      rw [add_zero]
    · left
      exact one_ne_zero

private theorem PeriodicSpherePacking.density_eq_orbitCard_mul_ballVolume_div_domainVolume
    (hL : ∀ x ∈ fundamentalDomain (b.ofZLatticeBasis ℝ _), ‖x‖ ≤ L) (hd : 0 < d) :
    S.upperPackingDensity
      = S.centerOrbitCardinality * volume (ball (0 : EuclideanSpace ℝ (Fin d)) (S.separation / 2))
        / volume (fundamentalDomain (b.ofZLatticeBasis ℝ _)) :=
  limsSup_eq_of_le_nhds (S.local_packing_density_tends_to_formula b hL hd)

end DensityEqFdDensity

section ConstantEqNormalizedConstant

private theorem periodic_packing_supremum_eq_unit_separation :
    PeriodicSpherePackingConstant d = ⨆ (S : PeriodicSpherePacking d) (_ : S.separation = 1),
    S.upperPackingDensity := by
  rw [iSup_subtype', PeriodicSpherePackingConstant]
  apply le_antisymm
  · apply iSup_le
    intro S
    have h := inv_mul_cancel₀ S.separation_pos.ne.symm
    have := le_iSup (fun x : { x : PeriodicSpherePacking d // x.separation = 1 } ↦
      x.val.upperPackingDensity)
        ⟨S.rescaleConfiguration (inv_pos.mpr S.separation_pos), h⟩
    rw [← rescale_upper_packing_density]
    · exact this
    · rw [inv_pos]
      exact S.separation_pos
  · refine iSup_le ?_
    rintro ⟨S, _⟩
    exact le_iSup (fun S : PeriodicSpherePacking d => S.upperPackingDensity) S

end ConstantEqNormalizedConstant

section Disjoint_Covering_of_Centers

end Disjoint_Covering_of_Centers

section Fundamental_Domains_in_terms_of_Basis

open Submodule

variable (S : PeriodicSpherePacking d) (b : Basis (Fin d) ℤ S.lattice)

private theorem PeriodicSpherePacking.fundamental_region_admits_norm_bound :
  ∃ L : ℝ, ∀ x ∈ fundamentalDomain (b.ofZLatticeBasis ℝ _), ‖x‖ ≤ L :=
  isBounded_iff_forall_norm_le.1 (fundamentalDomain_isBounded (Basis.ofZLatticeBasis ℝ S.lattice b))

private theorem PeriodicSpherePacking.basis_region_translates_cover_uniquely :
   ∀ x, ∃! g : S.lattice, g +ᵥ x ∈ fundamentalDomain (b.ofZLatticeBasis ℝ _) := by
  intro x
  obtain ⟨g, hg, h_unique⟩ :=
    exist_unique_vadd_mem_fundamentalDomain (b.ofZLatticeBasis ℝ _) x
  have hg_lattice : (g : EuclideanSpace ℝ (Fin d)) ∈ S.lattice :=
    (S.mem_integral_basis_span_iff b g).mp g.property
  refine ⟨⟨g, hg_lattice⟩, hg, ?_⟩
  rintro ⟨h, hh⟩ h_mem
  apply Subtype.ext
  exact congrArg
    (fun z : Submodule.span ℤ (Set.range (b.ofZLatticeBasis ℝ _)) =>
      (z : EuclideanSpace ℝ (Fin d)))
    (h_unique ⟨h, (S.mem_integral_basis_span_iff b h).mpr hh⟩ h_mem)

end Fundamental_Domains_in_terms_of_Basis

section Periodic_Density_Formula

private noncomputable def PeriodicSpherePacking.coordinateIndexEquiv
    (P : PeriodicSpherePacking d) : (Module.Free.ChooseBasisIndex ℤ ↥P.lattice) ≃ (Fin d) :=
  ZLattice.coordinateIndexEquiv P.lattice

private noncomputable def PeriodicSpherePacking.canonicalPackingLatticeBasis (S :
  PeriodicSpherePacking d) :
    Basis (Fin d) ℤ ↥S.lattice :=
  ((ZLattice.module_free ℝ S.lattice).chooseBasis).reindex S.coordinateIndexEquiv

@[simp] private theorem PeriodicSpherePacking.density_eq_numReps_mul_volume_ball_div_covolume
  (S : PeriodicSpherePacking d) (hd : 0 < d) : S.upperPackingDensity =
  (ENat.toENNReal (S.centerOrbitCardinality : ENat)) *
  volume (ball (0 : EuclideanSpace ℝ (Fin d)) (S.separation / 2)) /
  Real.toNNReal (ZLattice.covolume S.lattice) := by
  obtain ⟨L, hL⟩ := S.fundamental_region_admits_norm_bound S.canonicalPackingLatticeBasis
  rw [S.density_eq_orbitCard_mul_ballVolume_div_domainVolume
    S.canonicalPackingLatticeBasis hL hd]
  have : Nonempty (Fin d) := Fin.pos_iff_nonempty.mp hd
  have hfinite :
      volume (fundamentalDomain (S.canonicalPackingLatticeBasis.ofZLatticeBasis ℝ _)) ≠ ⊤ :=
    (Bornology.IsBounded.measure_lt_top
      (fundamentalDomain_isBounded (S.canonicalPackingLatticeBasis.ofZLatticeBasis ℝ _))).ne
  have hfund :
      IsAddFundamentalDomain S.lattice
        (fundamentalDomain (S.canonicalPackingLatticeBasis.ofZLatticeBasis ℝ _)) :=
    lattice_region_is_additive_fundamental_domain S _
      (S.basis_region_translates_cover_uniquely S.canonicalPackingLatticeBasis)
      (fundamentalDomain_measurableSet _)
  rw [ZLattice.covolume_eq_measure_fundamentalDomain S.lattice volume hfund]
  have hdenom :
      (↑(Real.toNNReal
        (volume.real (fundamentalDomain
          (S.canonicalPackingLatticeBasis.ofZLatticeBasis ℝ _)))) : ENNReal) =
        volume (fundamentalDomain (S.canonicalPackingLatticeBasis.ofZLatticeBasis ℝ _)) := by
    change ENNReal.ofReal
      (volume (fundamentalDomain
        (S.canonicalPackingLatticeBasis.ofZLatticeBasis ℝ _))).toReal = _
    exact ENNReal.ofReal_toReal hfinite
  rw [hdenom]
  norm_num

end Periodic_Density_Formula

section Empty_Centers

private theorem PeriodicSpherePacking.packing_density_zero_of_empty_centers (S :
  PeriodicSpherePacking d)
    (hd : 0 < d) [instEmpty : IsEmpty S.centers] : S.upperPackingDensity = 0 := by
  rw [S.density_eq_numReps_mul_volume_ball_div_covolume hd]
  let b := S.canonicalPackingLatticeBasis
  let D := fundamentalDomain (Basis.ofZLatticeBasis ℝ S.lattice b)
  have hD_isBounded : IsBounded D :=
    fundamentalDomain_isBounded (Basis.ofZLatticeBasis ℝ S.lattice b)
  have hD_unique_covers : ∀ x, ∃! g : S.lattice, g +ᵥ x ∈ D :=
    S.basis_region_translates_cover_uniquely b
  rw [← S.card_centers_in_fundamental_region D hD_isBounded hD_unique_covers hd]
  simp only [Set.toFinset_card, ENat.toENNReal_coe, ENNReal.div_eq_zero_iff, mul_eq_zero,
    Nat.cast_eq_zero, ENNReal.coe_ne_top, or_false]
  left
  let := @Fintype.ofFinite _ <| finite_centers_in_bounded_region S D hD_isBounded hd
  have : IsEmpty (↥(S.centers ∩ D)) := ⟨fun x => instEmpty.false ⟨x.1, x.2.1⟩⟩
  simp only [Fintype.card_eq_zero]

end Empty_Centers

end

section

open scoped ENNReal
open SpherePacking EuclideanSpace MeasureTheory Metric ZSpan Bornology Module

section PeriodicConstantAux

open MeasureTheory Metric EuclideanSpace
open scoped Pointwise

variable {d : ℕ}

private lemma coordinate_abs_bounded_by_norm (x : EuclideanSpace ℝ (Fin d)) (i : Fin d) : |x i|
  ≤ ‖x‖ := by
  simpa only [inner_single_left, Real.ringHom_apply, one_mul, PiLp.norm_single, norm_one] using!
    abs_real_inner_le_norm (EuclideanSpace.single i (1 : ℝ)) x

private lemma coordinate_difference_small_inside_ball {x y : EuclideanSpace ℝ (Fin d)} {r : ℝ}
  (hy : y ∈ ball x r)
    (i : Fin d) : |y i - x i| < r := by
  have hnorm : ‖y - x‖ < r := by simpa only [mem_ball, dist_eq_norm] using! hy
  exact lt_of_le_of_lt
    (by
      simpa only [PiLp.sub_apply] using!
        coordinate_abs_bounded_by_norm (d := d) (y - x) i)
    hnorm

private lemma metric_ball_subset_axis_cell {x : EuclideanSpace ℝ (Fin d)} {r L : ℝ}
    (hx : ∀ i : Fin d, x i ∈ Set.Icc r (L - r)) :
    ball x r ⊆ {y : EuclideanSpace ℝ (Fin d) | ∀ i : Fin d, y i ∈ Set.Ico (0 : ℝ) L} := by
  intro y hy i
  have hxi := hx i
  have hsub : |y i - x i| < r := coordinate_difference_small_inside_ball (d := d) hy i
  have hy0 : 0 ≤ y i := by
    have hx0 : 0 ≤ x i - r := sub_nonneg.mpr hxi.1
    have : x i - r < y i := by linarith [(abs_lt.mp hsub).1]
    exact hx0.trans (le_of_lt this)
  have hyL : y i < L := by
    have : y i < x i + r := by linarith [(abs_lt.mp hsub).2]
    exact lt_of_lt_of_le this (by linarith [hxi.2])
  exact ⟨hy0, hyL⟩

private lemma center_distance_bound_of_disjoint_regions {x y : EuclideanSpace ℝ (Fin d)} {r : ℝ}
    {A B : Set (EuclideanSpace ℝ (Fin d))}
    (hx : ball x r ⊆ A) (hy : ball y r ⊆ B) (hAB : Disjoint A B) :
    2 * r ≤ dist x y := by
  by_contra hlt
  have hlt' : dist x y < 2 * r := lt_of_not_ge hlt
  let m : EuclideanSpace ℝ (Fin d) := midpoint ℝ x y
  have hhalf : (1 / 2 : ℝ) * dist x y < r := by linarith
  have hmx : m ∈ ball x r := by
    simpa only [mem_ball, dist_comm, dist_left_midpoint,
      Real.norm_ofNat] using! (by simpa only [dist_midpoint_left, Real.norm_ofNat, one_div,
      m] using! hhalf : dist m x < r)
  have hmy : m ∈ ball y r := by
    simpa only [mem_ball, dist_comm, dist_right_midpoint,
      Real.norm_ofNat] using! (by simpa only [dist_comm, dist_right_midpoint, Real.norm_ofNat,
      one_div, m] using! hhalf : dist m y < r)
  exact Set.disjoint_left.1 hAB (hx hmx) (hy hmy)

open scoped Pointwise in
private noncomputable def latticeReplicatedCenters (Λ : Submodule ℤ (EuclideanSpace ℝ (Fin d)))
    (F : Set (EuclideanSpace ℝ (Fin d))) : Set (EuclideanSpace ℝ (Fin d)) :=
  ⋃ g : Λ, g +ᵥ F

private lemma mem_replicated_centers_iff {Λ : Submodule ℤ (EuclideanSpace ℝ (Fin d))}
    {F : Set (EuclideanSpace ℝ (Fin d))} {x : EuclideanSpace ℝ (Fin d)} :
    x ∈ latticeReplicatedCenters (d := d) Λ F ↔ ∃ g : Λ, ∃ f ∈ F, x = g +ᵥ f := by
  simp only [latticeReplicatedCenters, Set.mem_iUnion, Set.mem_vadd_set, eq_comm, Subtype.exists]

private lemma replicated_centers_translation_closed {Λ : Submodule ℤ (EuclideanSpace ℝ (Fin d))}
    {F : Set (EuclideanSpace ℝ (Fin d))} {x y : EuclideanSpace ℝ (Fin d)}
    (hx : x ∈ Λ) (hy : y ∈ latticeReplicatedCenters (d := d) Λ F) :
    x + y ∈ latticeReplicatedCenters (d := d) Λ F := by
  rcases (mem_replicated_centers_iff (d := d) (Λ := Λ) (F := F) (x := y)).1 hy with ⟨g, f, hf, rfl⟩
  refine (mem_replicated_centers_iff (d := d) (Λ := Λ) (F := F)).2 ⟨(⟨x, hx⟩ : Λ) + g, f, hf, ?_⟩
  simp only [Submodule.vadd_def, vadd_eq_add, Submodule.coe_add, add_assoc]

private lemma translated_ball_subset_translated_region {Λ : Submodule ℤ (EuclideanSpace ℝ (Fin d))}
    {D : Set (EuclideanSpace ℝ (Fin d))} {r : ℝ} {g : Λ} {x : EuclideanSpace ℝ (Fin d)}
    (hx : ball x r ⊆ D) :
    ball (g +ᵥ x) r ⊆ g +ᵥ D := by
  intro y hy
  refine Set.mem_vadd_set.2 ⟨(-g : Λ) +ᵥ y, ?_, by simp only [Submodule.vadd_def,
    NegMemClass.coe_neg, vadd_eq_add, add_neg_cancel_left]⟩
  apply hx
  have :
      (- (g : EuclideanSpace ℝ (Fin d))) +ᵥ y ∈
        (- (g : EuclideanSpace ℝ (Fin d))) +ᵥ ball (g +ᵥ x) r :=
    Set.mem_vadd_set.2 ⟨y, by simpa only [Submodule.vadd_def, vadd_eq_add, mem_ball] using! hy, rfl⟩
  simpa only [Submodule.vadd_def, NegMemClass.coe_neg, vadd_eq_add, mem_ball, gt_iff_lt, vadd_ball,
    neg_add_cancel_left] using! this

private noncomputable def replicate_to_periodic_packing
    (S : SpherePacking d)
    (Λ : Submodule ℤ (EuclideanSpace ℝ (Fin d))) [DiscreteTopology Λ] [IsZLattice ℝ Λ]
    (D F : Set (EuclideanSpace ℝ (Fin d)))
    (hD_unique_covers : ∀ x, ∃! g : Λ, g +ᵥ x ∈ D)
    (hF_centers : F ⊆ S.centers)
    (hF_ball : ∀ x ∈ F, ball x (S.separation / 2) ⊆ D) :
    PeriodicSpherePacking d := by
  refine
    { centers := latticeReplicatedCenters (d := d) Λ F
      separation := S.separation
      separation_pos := S.separation_pos
      centers_dist := ?_
      lattice := Λ
      lattice_action := ?_
      lattice_discrete := inferInstance
      lattice_isZLattice := inferInstance }
  · intro a b hab
    change S.separation ≤ dist (a : EuclideanSpace ℝ (Fin d)) (b : EuclideanSpace ℝ (Fin d))
    rcases (mem_replicated_centers_iff (d := d) (Λ := Λ) (F := F)
      (x := (a : EuclideanSpace ℝ (Fin d)))).1
        a.property with ⟨ga, fa, hfa, ha⟩
    rcases (mem_replicated_centers_iff (d := d) (Λ := Λ) (F := F)
      (x := (b : EuclideanSpace ℝ (Fin d)))).1
        b.property with ⟨gb, fb, hfb, hb⟩
    by_cases hgg : ga = gb
    · subst hgg
      have hne : fa ≠ fb := by
        intro h
        apply hab
        apply Subtype.ext
        simp only [ha, h, hb]
      have hdist := S.distinct_centers_separation_bound fa fb (hF_centers hfa) (hF_centers hfb) hne
      have : S.separation ≤ dist (ga +ᵥ fa) (ga +ᵥ fb) := by
        have htrans : dist (ga +ᵥ fa) (ga +ᵥ fb) = dist fa fb :=
          dist_vadd_cancel_left (ga : EuclideanSpace ℝ (Fin d)) fa fb
        simpa only [htrans, ge_iff_le] using! hdist
      simpa only [ha, hb, ge_iff_le] using! this
    · have hballa : ball (ga +ᵥ fa) (S.separation / 2) ⊆ ga +ᵥ D :=
        translated_ball_subset_translated_region (d := d) (Λ := Λ) (D := D) (g := ga) (x := fa)
          (r := S.separation / 2)
          (hF_ball fa hfa)
      have hballb : ball (gb +ᵥ fb) (S.separation / 2) ⊆ gb +ᵥ D :=
        translated_ball_subset_translated_region (d := d) (Λ := Λ) (D := D) (g := gb) (x := fb)
          (r := S.separation / 2)
          (hF_ball fb hfb)
      have hdisj : Disjoint (ga +ᵥ D) (gb +ᵥ D) :=
        translates_disjoint_of_unique_cover (d := d) (Λ := Λ) (D := D) hD_unique_covers hgg
      have : 2 * (S.separation / 2) ≤ dist (ga +ᵥ fa) (gb +ᵥ fb) :=
        center_distance_bound_of_disjoint_regions (d := d) hballa hballb hdisj
      have : S.separation ≤ dist (ga +ᵥ fa) (gb +ᵥ fb) := by
        simpa only [two_mul, add_halves] using! this
      simpa only [ha, hb, ge_iff_le] using! this
  · intro x y hx hy
    exact replicated_centers_translation_closed (d := d) (Λ := Λ) (F := F) hx hy

end PeriodicConstantAux

section PeriodicConstantCube

open scoped Pointwise

variable {d : ℕ}

private noncomputable def axisAlignedCell (L : ℝ) : Set (EuclideanSpace ℝ (Fin d)) :=
  {x | ∀ i : Fin d, x i ∈ Set.Ico (0 : ℝ) L}

private noncomputable def insetAxisAlignedCell (L r : ℝ) : Set (EuclideanSpace ℝ (Fin d)) :=
  {x | ∀ i : Fin d, x i ∈ Set.Icc r (L - r)}

private noncomputable def axisCellBasis (L : ℝ) (hL : 0 < L) :
    Basis (Fin d) ℝ (EuclideanSpace ℝ (Fin d)) :=
  ((EuclideanSpace.basisFun (Fin d) ℝ).toBasis).isUnitSMul
    (fun _ : Fin d ↦ IsUnit.mk0 L (ne_of_gt hL))

private noncomputable def axisCellLattice (L : ℝ) (hL : 0 < L) :
    Submodule ℤ (EuclideanSpace ℝ (Fin d)) :=
  Submodule.span ℤ (Set.range (axisCellBasis (d := d) L hL))

private lemma axis_cell_basis_fundamental_region (L : ℝ) (hL : 0 < L) :
    fundamentalDomain (axisCellBasis (d := d) L hL) = axisAlignedCell (d := d) L := by
  ext x
  simp only [ZSpan.mem_fundamentalDomain, axisAlignedCell, axisCellBasis,
    Module.Basis.repr_isUnitSMul,
    Units.smul_def, Units.val_inv_eq_inv_val, Set.mem_ofPred_eq,
    Set.mem_Ico]
  constructor
  · intro hx i
    specialize hx i
    refine ⟨?_, ?_⟩
    · have : 0 ≤ (L : ℝ) * (L⁻¹ * x.ofLp i) := mul_nonneg (le_of_lt hL) hx.1
      have : 0 ≤ (L * L⁻¹) * x.ofLp i := by simpa only [mul_assoc] using! this
      simpa only [ge_iff_le, mul_inv_cancel₀ (ne_of_gt hL), one_mul] using! this
    · have : (L : ℝ) * (L⁻¹ * x.ofLp i) < (L : ℝ) * 1 := mul_lt_mul_of_pos_left hx.2 hL
      have : (L * L⁻¹) * x.ofLp i < (L : ℝ) * 1 := by simpa only [mul_assoc, mul_one] using! this
      simpa only [gt_iff_lt, mul_inv_cancel₀ (ne_of_gt hL), one_mul, mul_one] using! this
  · intro hx i
    specialize hx i
    have hLinv : 0 < (L⁻¹ : ℝ) := inv_pos.mpr hL
    refine ⟨mul_nonneg (le_of_lt hLinv) hx.1, ?_⟩
    have : (L⁻¹ : ℝ) * x.ofLp i < (L⁻¹ : ℝ) * L := mul_lt_mul_of_pos_left hx.2 hLinv
    simpa only [IsUnit.unit_spec, OrthonormalBasis.coe_toBasis_repr_apply, basisFun_repr,
      smul_eq_mul, gt_iff_lt,
      inv_mul_cancel₀ (ne_of_gt hL)] using! this

private lemma metric_ball_subset_inset_axis_cell {L r : ℝ} {x : EuclideanSpace ℝ (Fin d)}
    (hx : x ∈ insetAxisAlignedCell (d := d) L r) :
    ball x r ⊆ axisAlignedCell (d := d) L := by
  simpa only [axisAlignedCell, Set.mem_Ico] using!
    metric_ball_subset_axis_cell (d := d) (x := x) (r := r) (L := L) hx

private lemma replicated_centers_intersection_of_subset {Λ : Submodule ℤ (EuclideanSpace ℝ (Fin d))}
    {D F : Set (EuclideanSpace ℝ (Fin d))}
    (hF_sub : F ⊆ D) (hD_unique_covers : ∀ x, ∃! g : Λ, g +ᵥ x ∈ D) :
    latticeReplicatedCenters (d := d) Λ F ∩ D = F := by
  ext x
  constructor
  · rintro ⟨hx, hxD⟩
    rcases (mem_replicated_centers_iff (d := d) (Λ := Λ) (F := F)).1 hx with
      ⟨g, f, hf, hxf⟩
    obtain ⟨g₀, hg₀, hunique⟩ := hD_unique_covers f
    have hg : g = g₀ := hunique g (show g +ᵥ f ∈ D from hxf ▸ hxD)
    have hzero : (0 : Λ) = g₀ := hunique 0 (by simpa only [zero_vadd] using hF_sub hf)
    have : g = 0 := hg.trans hzero.symm
    simpa only [hxf, this, zero_vadd] using hf
  · intro hx
    refine ⟨?_, hF_sub hx⟩
    exact (mem_replicated_centers_iff (d := d) (Λ := Λ) (F := F)).2
      ⟨0, x, hx, by simp only [zero_vadd]⟩

end PeriodicConstantCube

section Periodic_Constant_Eq_Constant

open scoped Pointwise

namespace PeriodicConstant

variable {d : ℕ}

private lemma coordinate_preimage_volume (s : Set (Fin d → ℝ)) (hs : MeasurableSet s) :
    volume ((fun x : EuclideanSpace ℝ (Fin d) ↦ x.ofLp) ⁻¹' s) = volume s := by
  simpa only  using! (PiLp.volume_preserving_ofLp (ι := Fin d)).measure_preimage
    hs.nullMeasurableSet

private lemma axis_cell_translates_cover_uniquely (L : ℝ) (hL : 0 < L) :
    ∀ x, ∃! g : axisCellLattice (d := d) L hL, g +ᵥ x ∈ axisAlignedCell (d := d) L := fun x => by
    simpa only [axisCellLattice,
      axis_cell_basis_fundamental_region (d := d) (L := L) (hL := hL)] using!
      exist_unique_vadd_mem_fundamentalDomain (axisCellBasis (d := d) L hL) x

private lemma axis_cell_is_bounded (L : ℝ) (hL : 0 < L) : IsBounded (axisAlignedCell (d := d) L)
  := by
  simpa only [axis_cell_basis_fundamental_region (d := d) (L := L) (hL := hL)] using!
    fundamentalDomain_isBounded (axisCellBasis (d := d) L hL)

private lemma axis_cell_is_measurable (L : ℝ) (hL : 0 < L) :
    MeasurableSet (axisAlignedCell (d := d) L) := by
  simpa only [axis_cell_basis_fundamental_region (d := d) (L := L) (hL := hL)] using!
    fundamentalDomain_measurableSet (axisCellBasis (d := d) L hL)

private lemma axis_cell_eq_coordinate_preimage (L : ℝ) :
    axisAlignedCell (d := d) L =
      (fun x : EuclideanSpace ℝ (Fin d) ↦ x.ofLp) ⁻¹'
        (Set.pi Set.univ fun _ : Fin d ↦ Set.Ico (0 : ℝ) L) := by
  ext x
  simp only [axisAlignedCell, Set.mem_Ico, Set.mem_ofPred_eq, Set.mem_preimage, Set.mem_pi,
    Set.mem_univ,
    forall_const]

private lemma axis_cell_volume_formula (L : ℝ) :
    volume (axisAlignedCell (d := d) L) = (ENNReal.ofReal L) ^ d := by
  have hmeas : MeasurableSet (Set.pi Set.univ fun _ : Fin d ↦ Set.Ico (0 : ℝ) L) := by
    simpa only  using! (MeasurableSet.pi Set.countable_univ fun _ _ ↦ measurableSet_Ico)
  have hpre :
      volume (axisAlignedCell (d := d) L) =
        volume (Set.pi Set.univ fun _ : Fin d ↦ Set.Ico (0 : ℝ) L) := by
    simpa only [axis_cell_eq_coordinate_preimage (d := d) (L := L)] using!
      (coordinate_preimage_volume (d := d) (s := Set.pi Set.univ fun _ : Fin d ↦ Set.Ico (0 : ℝ)
        L) hmeas)
  rw [hpre, volume_pi, Measure.pi_pi]
  simp only [Real.volume_Ico, sub_zero, Finset.prod_const, Finset.card_univ, Fintype.card_fin]

private lemma inset_cell_eq_coordinate_preimage (L r : ℝ) :
    insetAxisAlignedCell (d := d) L r =
      (fun x : EuclideanSpace ℝ (Fin d) ↦ x.ofLp) ⁻¹'
        (Set.pi Set.univ fun _ : Fin d ↦ Set.Icc r (L - r)) := by
  ext x
  simp only [insetAxisAlignedCell, Set.mem_Icc, forall_and, Set.mem_ofPred_eq, Set.pi_univ_Icc,
    Set.mem_preimage,
    Pi.le_def]

private lemma inset_axis_cell_volume_formula (L r : ℝ) :
    volume (insetAxisAlignedCell (d := d) L r) = (ENNReal.ofReal (L - 2 * r)) ^ d := by
  have hmeas : MeasurableSet (Set.pi Set.univ fun _ : Fin d ↦ Set.Icc r (L - r)) := by
    exact MeasurableSet.pi Set.countable_univ fun _ _ ↦ measurableSet_Icc
  have hpre :
      volume (insetAxisAlignedCell (d := d) L r) =
        volume (Set.pi Set.univ fun _ : Fin d ↦ Set.Icc r (L - r)) := by
    simpa only [inset_cell_eq_coordinate_preimage (d := d) (L := L) (r := r),
      Set.pi_univ_Icc] using!
      (coordinate_preimage_volume (d := d) (s := Set.pi Set.univ fun _ : Fin d ↦ Set.Icc r (L - r))
        hmeas)
  rw [hpre, volume_pi, Measure.pi_pi]
  simp only [sub_eq_add_neg, Real.volume_Icc, add_comm, add_left_comm, Finset.prod_const,
    Finset.card_univ,
    Fintype.card_fin, two_mul, neg_add_rev]

private lemma inset_cell_subset_axis_cell {L r : ℝ} (hr : 0 < r) :
    insetAxisAlignedCell (d := d) L r ⊆ axisAlignedCell (d := d) L := by
  intro x hx i
  have hxi := hx i
  exact ⟨(le_of_lt hr).trans hxi.1, hxi.2.trans_lt (sub_lt_self L hr)⟩

end PeriodicConstant

section PeriodicConstantApprox

open scoped Pointwise
open MeasureTheory Metric

namespace PeriodicConstantApprox

variable {d : ℕ}

private lemma translated_axis_cells_cover_uniquely (L : ℝ) (hL : 0 < L)
    (v : axisCellLattice (d := d) L hL) :
    ∀ x, ∃! g : axisCellLattice (d := d) L hL, g +ᵥ x ∈ v +ᵥ axisAlignedCell (d := d) L := by
  intro x
  have hvadd (a : axisCellLattice (d := d) L hL) :
      a +ᵥ x ∈ v +ᵥ axisAlignedCell (d := d) L ↔ (a - v) +ᵥ x ∈ axisAlignedCell (d := d) L := by
    simp only [Submodule.vadd_def, vadd_eq_add, add_comm, Set.mem_vadd_set_iff_neg_vadd_mem,
      add_assoc,
      sub_eq_add_neg, Submodule.coe_add, NegMemClass.coe_neg]
  obtain ⟨g, hg, hguniq⟩ := PeriodicConstant.axis_cell_translates_cover_uniquely (d := d) L hL x
  refine ⟨g + v, (hvadd (a := g + v)).2 (by simpa only [add_sub_cancel_right] using! hg), ?_⟩
  intro a ha
  have ha' : (a - v) +ᵥ x ∈ axisAlignedCell (d := d) L := (hvadd a).1 ha
  have : a - v = g := hguniq _ ha'
  exact (sub_eq_iff_eq_add).1 this

private lemma ball_subset_translated_cell_of_interior {L r : ℝ} (hL : 0 < L)
    {v : axisCellLattice (d := d) L hL} {x : EuclideanSpace ℝ (Fin d)}
    (hx : x ∈ v +ᵥ insetAxisAlignedCell (d := d) L r) :
    ball x r ⊆ v +ᵥ axisAlignedCell (d := d) L := by
  have hx' : (- (v : EuclideanSpace ℝ (Fin d))) +ᵥ x ∈ insetAxisAlignedCell (d := d) L r := by
    simpa only [vadd_eq_add, Set.mem_vadd_set_iff_neg_vadd_mem] using! hx
  have hball : ball ((- (v : EuclideanSpace ℝ (Fin d))) +ᵥ x) r ⊆ axisAlignedCell (d := d) L :=
    metric_ball_subset_inset_axis_cell (d := d) (L := L) (r := r) hx'
  have h :=
    translated_ball_subset_translated_region (d := d) (Λ := axisCellLattice (d := d) L hL) (D :=
      axisAlignedCell (d := d) L)
      (g := v) (x := (- (v : EuclideanSpace ℝ (Fin d))) +ᵥ x) (r := r) hball
  simpa only [Submodule.vadd_def, ge_iff_le, vadd_eq_add, add_comm,
    add_neg_cancel_comm_assoc] using! h

private lemma axis_cell_subset_enclosing_ball (L : ℝ) (hL : 0 < L) :
    ∃ C : ℝ, axisAlignedCell (d := d) L ⊆ ball (0 : EuclideanSpace ℝ (Fin d)) C := by
  simpa only  using! (PeriodicConstant.axis_cell_is_bounded (d := d) L hL).subset_ball 0

private lemma lattice_points_in_ball_finite (L : ℝ) (hL : 0 < L) (R : ℝ) :
    Set.Finite {g : axisCellLattice (d := d) L hL | (g : EuclideanSpace ℝ (Fin d)) ∈ ball 0 R} := by
  let : DiscreteTopology (axisCellLattice (d := d) L hL) := by
    unfold axisCellLattice
    infer_instance
  have hdiscrete := (inferInstance : DiscreteTopology (axisCellLattice (d := d) L hL))
  rw [discreteTopology_iff_isOpen_singleton_zero, Metric.isOpen_singleton_iff] at hdiscrete
  obtain ⟨ε, hε, hεzero⟩ := hdiscrete
  have hzero : ∀ g : axisCellLattice (d := d) L hL, ‖g‖ < ε → g = 0 := by
    intro g hg
    apply hεzero g
    simpa only [dist_zero_right, AddSubgroupClass.coe_norm] using hg
  let P : SpherePacking d :=
    { centers := (axisCellLattice (d := d) L hL : Set (EuclideanSpace ℝ (Fin d)))
      separation := ε
      separation_pos := hε
      centers_dist := by
        intro x y hxy
        by_contra hdist
        have hdist' : dist (x : EuclideanSpace ℝ (Fin d)) y < ε := by
          change ¬ ε ≤ dist (x : EuclideanSpace ℝ (Fin d)) y at hdist
          exact lt_of_not_ge hdist
        let g : axisCellLattice (d := d) L hL :=
          ⟨(x : EuclideanSpace ℝ (Fin d)) - y, sub_mem x.property y.property⟩
        have hg : ‖g‖ < ε := by
          change ‖(x : EuclideanSpace ℝ (Fin d)) - y‖ < ε
          simpa only [dist_eq_norm] using hdist'
        have hgeq : g = 0 := hzero g hg
        apply hxy
        apply Subtype.ext
        exact sub_eq_zero.mp (congrArg (fun z : axisCellLattice (d := d) L hL =>
          (z : EuclideanSpace ℝ (Fin d))) hgeq) }
  have hfinite : Set.Finite (P.centers ∩ ball (0 : EuclideanSpace ℝ (Fin d)) R) :=
    (Set.finite_coe_iff).1 (P.finite_centers_inside_ball R)
  refine (hfinite.preimage (f := fun g : axisCellLattice (d := d) L hL =>
    (g : EuclideanSpace ℝ (Fin d))) Subtype.val_injective.injOn).subset ?_
  intro g hg
  exact ⟨g.property, hg⟩

end PeriodicConstantApprox

end PeriodicConstantApprox

end Periodic_Constant_Eq_Constant

end

section

open scoped ENNReal
open SpherePacking EuclideanSpace MeasureTheory Metric ZSpan Bornology Module
open scoped Pointwise Topology

variable {d : ℕ}

namespace PeriodicConstantApprox

section CoordCubeCover

open Metric

variable (L : ℝ) (hL : 0 < L)

private noncomputable def axisCellCoverIndex (x : EuclideanSpace ℝ (Fin d)) : axisCellLattice (d
  := d) L hL :=
  Classical.choose (PeriodicConstant.axis_cell_translates_cover_uniquely (d := d) L hL x)

private lemma axis_cell_cover_index_mem (x : EuclideanSpace ℝ (Fin d)) :
    axisCellCoverIndex (d := d) L hL x +ᵥ x ∈ axisAlignedCell (d := d) L :=
  (Classical.choose_spec (PeriodicConstant.axis_cell_translates_cover_uniquely (d := d) L hL x)).1

private lemma axis_cell_cover_index_unique (x : EuclideanSpace ℝ (Fin d)) (g : axisCellLattice
  (d := d) L hL)
    (hg : g +ᵥ x ∈ axisAlignedCell (d := d) L) :
    g = axisCellCoverIndex (d := d) L hL x :=
  (Classical.choose_spec (PeriodicConstant.axis_cell_translates_cover_uniquely (d := d) L hL
    x)).2 g hg

private lemma mem_negated_cover_index_cell (x : EuclideanSpace ℝ (Fin d)) :
    x ∈ (-axisCellCoverIndex (d := d) L hL x) +ᵥ axisAlignedCell (d := d) L := by
  simpa only [Set.mem_vadd_set_iff_neg_vadd_mem,
    neg_neg] using! axis_cell_cover_index_mem (d := d) L hL x

private lemma negated_cover_index_mem_enlarged_ball {C R : ℝ}
    (hC : axisAlignedCell (d := d) L ⊆ ball (0 : EuclideanSpace ℝ (Fin d)) C)
    {x : EuclideanSpace ℝ (Fin d)} (hx : x ∈ ball 0 R) :
    ((-axisCellCoverIndex (d := d) L hL x : axisCellLattice (d := d) L hL) :
        EuclideanSpace ℝ (Fin d)) ∈ ball 0 (R + C) := by
  have hx0 : ‖x‖ < R := by simpa only [mem_ball, dist_zero_right] using! hx
  have hxgC : ‖(axisCellCoverIndex (d := d) L hL x : EuclideanSpace ℝ (Fin d)) + x‖ < C := by
    have hmem :
        (axisCellCoverIndex (d := d) L hL x : EuclideanSpace ℝ (Fin d)) + x ∈ axisAlignedCell (d
          := d) L := by
      simpa only [Submodule.vadd_def, vadd_eq_add] using! axis_cell_cover_index_mem (d := d) L hL x
    simpa only [gt_iff_lt, mem_ball, dist_zero_right] using! (hC hmem)
  have htri :
      ‖(axisCellCoverIndex (d := d) L hL x : EuclideanSpace ℝ (Fin d))‖ ≤
        ‖(axisCellCoverIndex (d := d) L hL x : EuclideanSpace ℝ (Fin d)) + x‖ + ‖x‖ := by
    simpa only [add_comm, sub_eq_add_neg, add_assoc, add_neg_cancel_comm_assoc] using!
      (norm_sub_le (a := (axisCellCoverIndex (d := d) L hL x : EuclideanSpace ℝ (Fin d)) + x) (b
        := x))
  have :
      ‖(- (axisCellCoverIndex (d := d) L hL x : EuclideanSpace ℝ (Fin d)))‖ < R + C := by
    have : ‖(axisCellCoverIndex (d := d) L hL x : EuclideanSpace ℝ (Fin d))‖ < C + R := by
      refine lt_of_le_of_lt htri ?_
      simpa only [add_comm] using! add_lt_add hxgC hx0
    simpa only [norm_neg, add_comm, gt_iff_lt] using! this
  simpa only [NegMemClass.coe_neg, mem_ball, dist_zero_right, norm_neg, gt_iff_lt] using! this

private lemma mem_translated_cell_iff_cover_index (g : axisCellLattice (d := d) L hL)
    (x : EuclideanSpace ℝ (Fin d)) :
    x ∈ g +ᵥ axisAlignedCell (d := d) L ↔ g = -axisCellCoverIndex (d := d) L hL x := by
  constructor
  · intro hx
    have : (-g : axisCellLattice (d := d) L hL) = axisCellCoverIndex (d := d) L hL x :=
      axis_cell_cover_index_unique (d := d) L hL x (-g)
        (by simpa only [Set.mem_vadd_set_iff_neg_vadd_mem] using! hx)
    simpa only [neg_neg] using! congrArg (fun t : axisCellLattice (d := d) L hL => -t) this
  · rintro rfl; exact mem_negated_cover_index_cell (d := d) L hL x

end CoordCubeCover

section CoverVolumeBound

open scoped BigOperators

private lemma translated_axis_cell_subset_ball {L : ℝ} (hL : 0 < L) {R C : ℝ}
    (hC : axisAlignedCell (d := d) L ⊆ ball (0 : EuclideanSpace ℝ (Fin d)) C)
    {g : axisCellLattice (d := d) L hL}
    (hg : (g : EuclideanSpace ℝ (Fin d)) ∈ ball 0 (R + C)) :
    g +ᵥ axisAlignedCell (d := d) L ⊆ ball (0 : EuclideanSpace ℝ (Fin d)) (R + (2 * C)) := by
  intro y hy
  rcases hy with ⟨x, hx, rfl⟩
  have hx' : ‖x‖ < C := by
    simpa only [mem_ball, dist_zero_right] using! hC hx
  have hg' : ‖(g : EuclideanSpace ℝ (Fin d))‖ < R + C := by
    simpa only [mem_ball, dist_zero_right] using! hg
  have : ‖(g : EuclideanSpace ℝ (Fin d)) + x‖ < R + (2 * C) := by
    refine (lt_of_le_of_lt (norm_add_le _ _) ?_)
    simpa only [add_comm, two_mul, add_left_comm] using! add_lt_add hg' hx'
  simpa only [vadd_eq_add, mem_ball, dist_zero_right, gt_iff_lt] using! this

private lemma finite_cell_union_subset_enclosing_ball {L : ℝ} (hL : 0 < L) {R C : ℝ}
    (hC : axisAlignedCell (d := d) L ⊆ ball (0 : EuclideanSpace ℝ (Fin d)) C) :
    let htSet :=
      PeriodicConstantApprox.lattice_points_in_ball_finite (d := d) L hL (R + C)
    let t : Finset (axisCellLattice (d := d) L hL) := htSet.toFinset
    (⋃ g ∈ t, g +ᵥ axisAlignedCell (d := d) L) ⊆
      ball (0 : EuclideanSpace ℝ (Fin d)) (R + (2 * C)) := by
  intro htSet t y hy
  rcases Set.mem_iUnion₂.1 hy with ⟨g, hgT, hy'⟩
  have hgBall :
      (g : EuclideanSpace ℝ (Fin d)) ∈ ball (0 : EuclideanSpace ℝ (Fin d)) (R + C) :=
    htSet.mem_toFinset.1 (by simpa only [mem_ball, dist_zero_right, Set.Finite.mem_toFinset,
      Set.mem_ofPred_eq, t] using! hgT)
  exact (translated_axis_cell_subset_ball (d := d) (hL := hL) (R := R) (C := C) hC hgBall) hy'

private lemma lattice_count_mul_cell_volume_le_ball_volume {L : ℝ} (hL : 0 < L)
    {R C : ℝ} (hC : axisAlignedCell (d := d) L ⊆ ball (0 : EuclideanSpace ℝ (Fin d)) C) :
    let htSet :=
      PeriodicConstantApprox.lattice_points_in_ball_finite (d := d) L hL (R + C)
    let t : Finset (axisCellLattice (d := d) L hL) := htSet.toFinset
    (t.card : ℝ≥0∞) * volume (axisAlignedCell (d := d) L) ≤
      volume (ball (0 : EuclideanSpace ℝ (Fin d)) (R + (2 * C))) := by
  intro htSet t
  have hdisj :
      Set.PairwiseDisjoint (↑t : Set (axisCellLattice (d := d) L hL))
        (fun g : axisCellLattice (d := d) L hL => g +ᵥ axisAlignedCell (d := d) L) := by
    intro g _ h _ hgh
    exact translates_disjoint_of_unique_cover (d := d)
      (Λ := axisCellLattice (d := d) L hL) (D := axisAlignedCell (d := d) L)
      (PeriodicConstant.axis_cell_translates_cover_uniquely (d := d) L hL) hgh
  have hmeas :
      ∀ g ∈ t, MeasurableSet (g +ᵥ axisAlignedCell (d := d) L) := by
    intro g _; simpa only  using!
      (MeasurableSet.const_vadd (PeriodicConstant.axis_cell_is_measurable (d := d) L hL) g)
  have hvol_union :
      volume (⋃ g ∈ t, g +ᵥ axisAlignedCell (d := d) L) =
        ∑ g ∈ t, volume (g +ᵥ axisAlignedCell (d := d) L) :=
    measure_biUnion_finset (μ := volume) hdisj hmeas
  have hsub :
      (⋃ g ∈ t, g +ᵥ axisAlignedCell (d := d) L) ⊆
        ball (0 : EuclideanSpace ℝ (Fin d)) (R + (2 * C)) :=
    finite_cell_union_subset_enclosing_ball (d := d) (hL := hL) (R := R) (C := C) hC
  have hle := volume.mono hsub
  simp_all

end CoverVolumeBound

section BoundaryControl

open scoped ENNReal Pointwise BigOperators

private noncomputable def constantCoordinateVector (c : ℝ) : EuclideanSpace ℝ (Fin d) :=
  WithLp.toLp 2 (fun _ : Fin d => c)

private lemma coordinate_abs_lt_of_norm_bound {x : EuclideanSpace ℝ (Fin d)} {r : ℝ} (hx : ‖x‖ < r)
    (i : Fin d) : |x i| < r :=
  lt_of_le_of_lt (coordinate_abs_bounded_by_norm (d := d) x i) hx

private lemma boundary_half_ball_subset_outer_annulus (L : ℝ) :
    ((axisAlignedCell (d := d) L \ insetAxisAlignedCell (d := d) L (1 / 2)) +
        ball (0 : EuclideanSpace ℝ (Fin d)) (1 / 2))
      ⊆ ((constantCoordinateVector (d := d) (- (1 / 2 : ℝ))) +ᵥ insetAxisAlignedCell (d := d) (L
        + 1) 0) \
        insetAxisAlignedCell (d := d) L 1 := by
  intro x hx
  rcases hx with ⟨a, ⟨ha, ha_boundary⟩, b, hb, rfl⟩
  have hb_norm : ‖b‖ < (1 / 2 : ℝ) := by
    simpa only [one_div, mem_ball, dist_zero_right] using hb
  constructor
  · refine Set.mem_vadd_set.2
      ⟨a + b - constantCoordinateVector (d := d) (-(1 / 2 : ℝ)), ?_, ?_⟩
    · intro i
      rcases ha i with ⟨ha_nonneg, ha_lt⟩
      have hbi := coordinate_abs_lt_of_norm_bound (d := d) hb_norm i
      rcases abs_lt.mp hbi with ⟨hb_lower, hb_upper⟩
      change 0 ≤ (a + b - constantCoordinateVector (d := d) (-(1 / 2 : ℝ))) i ∧
        (a + b - constantCoordinateVector (d := d) (-(1 / 2 : ℝ))) i ≤ L + 1 - 0
      simp only [PiLp.sub_apply, PiLp.add_apply, constantCoordinateVector]
      constructor <;> linarith
    · simp only [one_div, vadd_eq_add, add_sub_cancel]
  · intro h_inset
    apply ha_boundary
    intro i
    have hxi := h_inset i
    have hbi := coordinate_abs_lt_of_norm_bound (d := d) hb_norm i
    rcases abs_lt.mp hbi with ⟨hb_lower, hb_upper⟩
    change (1 / 2 : ℝ) ≤ a i ∧ a i ≤ L - 1 / 2
    change 1 ≤ (a + b) i ∧ (a + b) i ≤ L - 1 at hxi
    simp only [PiLp.add_apply] at hxi
    rcases hxi with ⟨hx_lower, hx_upper⟩
    constructor <;> linarith

variable (S : SpherePacking d)

private lemma boundary_count_mul_ball_volume_le_annulus {L : ℝ} (hL : 0 < L)
    (hSsep : S.separation = 1)
    {g : axisCellLattice (d := d) L hL} {s : Finset (EuclideanSpace ℝ (Fin d))}
    (hs_centers : ∀ x ∈ s, x ∈ S.centers)
    (hs_boundary : ∀ x ∈ s,
      x ∈ (g +ᵥ axisAlignedCell (d := d) L) \ (g +ᵥ insetAxisAlignedCell (d := d) L (1 / 2))) :
    (s.card : ℝ≥0∞) * volume (ball (0 : EuclideanSpace ℝ (Fin d)) (2⁻¹ : ℝ)) ≤
      volume (((constantCoordinateVector (d := d) (- (1 / 2 : ℝ))) +ᵥ insetAxisAlignedCell (d :=
        d) (L + 1) 0) \
        insetAxisAlignedCell (d := d) L 1) := by
  classical
  let v : EuclideanSpace ℝ (Fin d) := g
  have hdisj :
      Set.PairwiseDisjoint (↑s : Set (EuclideanSpace ℝ (Fin d)))
        (fun x : EuclideanSpace ℝ (Fin d) => ball (x - v) (1 / 2 : ℝ)) := by
    intro x hx y hy hxy
    apply ball_disjoint_ball
    have hdist :=
      S.distinct_centers_separation_bound x y (hs_centers x hx) (hs_centers y hy) hxy
    rw [hSsep] at hdist
    convert hdist using 1 <;> norm_num [dist_eq_norm, sub_sub_sub_cancel_right]
  have hmeas :
      ∀ x ∈ s, MeasurableSet (ball (x - v) (1 / 2 : ℝ)) := by
    intro x hx
    exact measurableSet_ball
  have hvol_union :
      volume (⋃ x ∈ s, ball (x - v) (1 / 2 : ℝ)) =
        ∑ x ∈ s, volume (ball (x - v) (1 / 2 : ℝ)) :=
    measure_biUnion_finset (μ := volume) hdisj hmeas
  have hsub :
      (⋃ x ∈ s, ball (x - v) (1 / 2 : ℝ)) ⊆
        ((constantCoordinateVector (d := d) (-(1 / 2 : ℝ))) +ᵥ
          insetAxisAlignedCell (d := d) (L + 1) 0) \
          insetAxisAlignedCell (d := d) L 1 := by
    intro y hy
    rcases Set.mem_iUnion₂.mp hy with ⟨x, hx, hy⟩
    apply boundary_half_ball_subset_outer_annulus (d := d) L
    refine Set.mem_add.mpr ⟨x - v, ?_, y - (x - v), ?_, ?_⟩
    · have hboundary := hs_boundary x hx
      constructor
      · have hcell := hboundary.1
        simpa only [sub_eq_add_neg, Submodule.vadd_def, Set.mem_vadd_set_iff_neg_vadd_mem,
          vadd_eq_add,
          add_comm] using hcell
      · intro hinset
        apply hboundary.2
        simpa only [one_div, Submodule.vadd_def, Set.mem_vadd_set_iff_neg_vadd_mem, vadd_eq_add,
          add_comm,
          sub_eq_add_neg] using hinset
    · simpa only [one_div, mem_ball, dist_eq_norm, sub_zero] using hy
    · abel
  calc
    (s.card : ℝ≥0∞) * volume (ball (0 : EuclideanSpace ℝ (Fin d)) (2⁻¹ : ℝ)) =
        volume (⋃ x ∈ s, ball (x - v) (1 / 2 : ℝ)) := by
      rw [hvol_union]
      simp only [Measure.addHaar_ball_center, one_div, Finset.sum_const, nsmul_eq_mul]
    _ ≤ volume (((constantCoordinateVector (d := d) (-(1 / 2 : ℝ))) +ᵥ
          insetAxisAlignedCell (d := d) (L + 1) 0) \
          insetAxisAlignedCell (d := d) L 1) :=
      volume.mono hsub

end BoundaryControl

end PeriodicConstantApprox

namespace SpherePacking

open Filter

variable {d : ℕ}

private lemma frequently_local_density_exceeds_threshold (S : SpherePacking d) {b : ℝ≥0∞}
    (hb : b < S.upperPackingDensity) : ∃ᶠ R in (atTop : Filter ℝ), b < S.densityInsideRadius R := by
  exact frequently_lt_of_lt_limsup (u := S.densityInsideRadius) (b := b)
    (h := by simpa only [upperPackingDensity] using! hb)

private lemma finite_center_ball_intersection_set (S : SpherePacking d) (R : ℝ) :
    (S.centers ∩ ball (0 : EuclideanSpace ℝ (Fin d)) R).Finite := by
  simpa only [Set.finite_coe_iff] using! (SpherePacking.finite_centers_inside_ball (S := S) (R
    := R))

end SpherePacking

namespace PeriodicConstantApprox

open Filter

variable {d : ℕ}

private noncomputable def uniformShellShift (d : ℕ) (c : ℝ) : EuclideanSpace ℝ (Fin d) :=
  WithLp.toLp 2 (fun _ : Fin d => c)

private lemma unit_inset_cell_subset_shifted_shell (L : ℝ) :
    insetAxisAlignedCell (d := d) L 1 ⊆
      (uniformShellShift d (- (1 / 2 : ℝ))) +ᵥ insetAxisAlignedCell (d := d) (L + 1) 0 := by
  intro x hx
  refine (Set.mem_vadd_set_iff_neg_vadd_mem).2 ?_
  have hx' : ∀ i : Fin d, x.ofLp i ∈ Set.Icc (1 : ℝ) (L - 1) := by
    simpa only [Set.mem_Icc, insetAxisAlignedCell, Set.mem_ofPred_eq] using! hx
  simp only [insetAxisAlignedCell, Set.mem_ofPred_eq, uniformShellShift, vadd_eq_add, one_div,
    WithLp.ofLp_add,
    WithLp.ofLp_neg, Pi.add_apply, Pi.neg_apply, neg_neg]
  exact fun i => by
    let hxi := hx' i
    refine ⟨by linarith [hxi.1], by linarith [hxi.2]⟩

private lemma axis_shell_volume_difference (L : ℝ) :
    volume (((uniformShellShift d (- (1 / 2 : ℝ))) +ᵥ insetAxisAlignedCell (d := d) (L + 1) 0) \
        insetAxisAlignedCell (d := d) L 1) =
      volume (insetAxisAlignedCell (d := d) (L + 1) 0) - volume (insetAxisAlignedCell (d := d) L
        1) := by
  have hsub :
      insetAxisAlignedCell (d := d) L 1 ⊆
        (uniformShellShift d (- (1 / 2 : ℝ))) +ᵥ insetAxisAlignedCell (d := d) (L + 1) 0 :=
    unit_inset_cell_subset_shifted_shell (d := d) L
  have hmeas_inner : MeasurableSet (insetAxisAlignedCell (d := d) L 1) := by
    have hmeasPi :
        MeasurableSet (Set.pi Set.univ fun _ : Fin d ↦ Set.Icc (1 : ℝ) (L - 1)) := by
      refine MeasurableSet.pi Set.countable_univ ?_
      intro _ _
      exact measurableSet_Icc
    have hmp : MeasurePreserving (fun x : EuclideanSpace ℝ (Fin d) ↦ x.ofLp) := by
      simpa only  using! (PiLp.volume_preserving_ofLp (ι := Fin d))
    simpa only [PeriodicConstant.inset_cell_eq_coordinate_preimage (d := d) (L := L) (r := (1 : ℝ)),
      Set.pi_univ_Icc] using!
      hmeasPi.preimage hmp.measurable
  have hfin : volume (insetAxisAlignedCell (d := d) L 1) ≠ ∞ := by
    simp only [PeriodicConstant.inset_axis_cell_volume_formula, mul_one, ne_eq,
      ENNReal.pow_eq_top_iff,
      ENNReal.ofReal_ne_top, false_and, not_false_eq_true]
  simpa only [uniformShellShift, one_div, measure_vadd] using!
    (measure_sdiff (μ := volume) hsub hmeas_inner.nullMeasurableSet hfin)

private lemma axis_shell_volume_power_formula (L : ℝ) :
    volume (((uniformShellShift d (- (1 / 2 : ℝ))) +ᵥ insetAxisAlignedCell (d := d) (L + 1) 0) \
        insetAxisAlignedCell (d := d) L 1) =
      (ENNReal.ofReal (L + 1)) ^ d - (ENNReal.ofReal (L - 2)) ^ d := by
  rw [axis_shell_volume_difference (d := d) (L := L)]
  simp only [PeriodicConstant.inset_axis_cell_volume_formula, mul_zero, sub_zero, mul_one]

section BoundaryControlShellVec

open scoped ENNReal Pointwise BigOperators
open SpherePacking EuclideanSpace MeasureTheory Metric

variable {d : ℕ}
variable (S : SpherePacking d)

private lemma boundary_count_mul_ball_volume_le_shell {L : ℝ} (hL : 0 < L)
    (hSsep : S.separation = 1)
    {g : axisCellLattice (d := d) L hL} {s : Finset (EuclideanSpace ℝ (Fin d))}
    (hs_centers : ∀ x ∈ s, x ∈ S.centers)
    (hs_boundary : ∀ x ∈ s,
      x ∈ (g +ᵥ axisAlignedCell (d := d) L) \ (g +ᵥ insetAxisAlignedCell (d := d) L (1 / 2))) :
    (s.card : ℝ≥0∞) * volume (ball (0 : EuclideanSpace ℝ (Fin d)) (2⁻¹ : ℝ)) ≤
      volume (((uniformShellShift d (- (1 / 2 : ℝ))) +ᵥ insetAxisAlignedCell (d := d) (L + 1) 0) \
          insetAxisAlignedCell (d := d) L 1) := by simpa only [uniformShellShift, one_div,
            constantCoordinateVector] using!
    (boundary_count_mul_ball_volume_le_annulus (S := S) hL hSsep hs_centers hs_boundary)

end BoundaryControlShellVec

section CubeLatticeCovolume

open scoped ENNReal
open ZSpan

private lemma axis_lattice_covolume_eq_cell_volume (L : ℝ) (hL : 0 < L) :
    ZLattice.covolume (axisCellLattice (d := d) L hL) volume =
      (volume (axisAlignedCell (d := d) L)).toReal := by
  let : DiscreteTopology (axisCellLattice (d := d) L hL) :=
    ZSpan.instDiscreteTopologySubtypeMemSubmoduleIntSpanRangeCoeBasisRealOfFinite
      (axisCellBasis (d := d) L hL)
  let : IsZLattice ℝ (axisCellLattice (d := d) L hL) :=
    instIsZLatticeRealSpan (axisCellBasis (d := d) L hL)
  have hfund :
      IsAddFundamentalDomain (axisCellLattice (d := d) L hL)
        (fundamentalDomain (axisCellBasis (d := d) L hL)) volume := by
    simpa only [axisCellLattice] using! (ZSpan.isAddFundamentalDomain (axisCellBasis (d := d) L
      hL) volume)
  simpa only [Measure.real, axis_cell_basis_fundamental_region (d := d) (L := L) (hL := hL)] using!
    (ZLattice.covolume_eq_measure_fundamentalDomain (L := axisCellLattice (d := d) L hL)
      (μ := volume) hfund)

private lemma axis_lattice_covolume_toNNReal (L : ℝ) (hL : 0 < L) :
    Real.toNNReal (ZLattice.covolume (axisCellLattice (d := d) L hL) volume) =
      (volume (axisAlignedCell (d := d) L)).toNNReal := by
  simp only [axis_lattice_covolume_eq_cell_volume (d := d) (L := L) hL, ENNReal.toNNReal_toReal_eq]

end CubeLatticeCovolume

section PeriodizeCubeDensity

open scoped ENNReal Pointwise
open SpherePacking EuclideanSpace MeasureTheory Metric Bornology

variable {d : ℕ}

private lemma replicated_cell_packing_density_formula (hd : 0 < d) (S : SpherePacking d) (hSsep
  : S.separation = 1)
    {L : ℝ} (hL : 0 < L) {g : axisCellLattice (d := d) L hL}
    (F : Finset (EuclideanSpace ℝ (Fin d)))
    (hF_centers : ∀ x ∈ F, x ∈ S.centers)
    (hF_inner : ∀ x ∈ F, x ∈ g +ᵥ insetAxisAlignedCell (d := d) L (2⁻¹ : ℝ)) :
    ∃ P : PeriodicSpherePacking d,
      P.separation = 1 ∧
        P.upperPackingDensity =
          (F.card : ℝ≥0∞) *
              volume (ball (0 : EuclideanSpace ℝ (Fin d)) (2⁻¹ : ℝ)) /
            Real.toNNReal (ZLattice.covolume (axisCellLattice (d := d) L hL) volume) := by
  let Λ : Submodule ℤ (EuclideanSpace ℝ (Fin d)) := axisCellLattice (d := d) L hL
  let D : Set (EuclideanSpace ℝ (Fin d)) := g +ᵥ axisAlignedCell (d := d) L
  let Fset : Set (EuclideanSpace ℝ (Fin d)) := (F : Set (EuclideanSpace ℝ (Fin d)))
  let : DiscreteTopology Λ :=
    ZSpan.instDiscreteTopologySubtypeMemSubmoduleIntSpanRangeCoeBasisRealOfFinite
      (axisCellBasis (d := d) L hL)
  let : IsZLattice ℝ Λ :=
    instIsZLatticeRealSpan (axisCellBasis (d := d) L hL)
  let P : PeriodicSpherePacking d :=
    replicate_to_periodic_packing (d := d) S (Λ := Λ) D Fset
      (hD_unique_covers := PeriodicConstantApprox.translated_axis_cells_cover_uniquely (d := d)
        L hL g)
      (hF_centers := by
        assumption)
      (hF_ball := by
        intro x hx
        have hx' : x ∈ F := by simpa only [SetLike.mem_coe, Fset] using! hx
        have hxInner : x ∈ g +ᵥ insetAxisAlignedCell (d := d) L (S.separation / 2) := by
          simpa only [hSsep, one_div] using! (hF_inner x hx')
        exact ball_subset_translated_cell_of_interior hL hxInner)
  have hPsep : P.separation = 1 := by simpa only
  refine ⟨P, hPsep, ?_⟩
  have hD_bounded : IsBounded D := by
    simpa only [Submodule.vadd_def] using!
      (PeriodicConstant.axis_cell_is_bounded (d := d) L hL).vadd (g : EuclideanSpace ℝ (Fin d))
  have hD_unique : ∀ x, ∃! g0 : (axisCellLattice (d := d) L hL), g0 +ᵥ x ∈ D :=
    PeriodicConstantApprox.translated_axis_cells_cover_uniquely (d := d) L hL g
  have hF_sub : Fset ⊆ D := by
    intro x hx
    have hx' : x ∈ F := by simpa only [SetLike.mem_coe] using! hx
    rcases (hF_inner x hx') with ⟨a, ha, rfl⟩
    have ha' : a ∈ axisAlignedCell (d := d) L :=
      PeriodicConstant.inset_cell_subset_axis_cell (d := d) (L := L) (r := (2⁻¹ : ℝ))
        (by norm_num) ha
    exact ⟨a, ha', rfl⟩
  have hcenters_inter :
      P.centers ∩ D = Fset := by
    simpa only [replicate_to_periodic_packing] using!
      (replicated_centers_intersection_of_subset (d := d) (Λ := axisCellLattice (d := d) L hL)
        (D := D)
        (F := Fset) hF_sub hD_unique)
  have hnumReps : P.centerOrbitCardinality = F.card := by
    have h' : (P.centerOrbitCardinality : ENat) = (F.card : ENat) := by
      simpa [hcenters_inter, Fset, Set.encard_coe_eq_coe_finsetCard] using!
        (P.encard_centers_in_fundamental_region (d := d) (D := D) hD_bounded hD_unique hd).symm
    exact_mod_cast h'
  simpa only [hnumReps, ENat.toENNReal_coe, hPsep,
    one_div] using! P.density_eq_numReps_mul_volume_ball_div_covolume (d := d) hd

end PeriodizeCubeDensity

private lemma axis_shell_volume_ratio_tends_zero :
    Tendsto (fun L : ℝ => ((L + 1) ^ d - (L - 2) ^ d) / (L ^ d)) atTop (𝓝 (0 : ℝ)) := by
  have hinv : Tendsto (fun L : ℝ => L⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero
  have hplus : Tendsto (fun L : ℝ => 1 + L⁻¹) atTop (𝓝 (1 : ℝ)) := by
    simpa only [add_zero] using (tendsto_const_nhds.add hinv)
  have hminus : Tendsto (fun L : ℝ => 1 - 2 * L⁻¹) atTop (𝓝 (1 : ℝ)) := by
    simpa only [mul_zero, sub_zero] using (tendsto_const_nhds.sub (tendsto_const_nhds.mul hinv))
  have hlimit : Tendsto (fun L : ℝ => (1 + L⁻¹) ^ d - (1 - 2 * L⁻¹) ^ d)
      atTop (𝓝 (0 : ℝ)) := by
    simpa only [one_pow, sub_self] using (hplus.pow d).sub (hminus.pow d)
  apply hlimit.congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with L hL
  have hplus_eq : 1 + L⁻¹ = (L + 1) / L := by
    field_simp [hL.ne']
  have hminus_eq : 1 - 2 * L⁻¹ = (L - 2) / L := by
    field_simp [hL.ne']
  rw [hplus_eq, hminus_eq, div_pow, div_pow, ← sub_div]

private lemma axis_shell_relative_cell_volume_tends_zero :
    Tendsto
        (fun L : ℝ =>
          volume (((uniformShellShift d (- (1 / 2 : ℝ))) +ᵥ insetAxisAlignedCell (d := d) (L +
            1) 0) \
              insetAxisAlignedCell (d := d) L 1) /
            volume (axisAlignedCell (d := d) L))
        atTop (𝓝 (0 : ℝ≥0∞)) := by
  have hlimit : Tendsto
      (fun L : ℝ => ENNReal.ofReal (((L + 1) ^ d - (L - 2) ^ d) / (L ^ d)))
      atTop (𝓝 (0 : ℝ≥0∞)) := by
    simpa only [Function.comp_def, ENNReal.ofReal_zero] using
      ENNReal.continuous_ofReal.continuousAt.tendsto.comp
        (axis_shell_volume_ratio_tends_zero (d := d))
  refine hlimit.congr' ?_
  filter_upwards [eventually_gt_atTop (2 : ℝ)] with L hL
  have hL0 : 0 < L := by linarith
  have hLplus : 0 ≤ L + 1 := by linarith
  have hLminus : 0 ≤ L - 2 := by linarith
  rw [axis_shell_volume_power_formula, PeriodicConstant.axis_cell_volume_formula,
    ← ENNReal.ofReal_pow hLplus d, ← ENNReal.ofReal_pow hLminus d,
    ← ENNReal.ofReal_pow hL0.le d,
    ← ENNReal.ofReal_sub,
    ← ENNReal.ofReal_div_of_pos (pow_pos hL0 d)]
  exact pow_nonneg hLminus d

end PeriodicConstantApprox

namespace SpherePacking

open Filter
open scoped ENNReal BigOperators

variable {d : ℕ}

private theorem exists_periodic_unit_packing_above_density_threshold (hd : 0 < d)
    (S : SpherePacking d) (hSsep : S.separation = 1) {b : ℝ≥0∞} (hb : b < S.upperPackingDensity) :
    ∃ P : PeriodicSpherePacking d, P.separation = 1 ∧ b < P.upperPackingDensity := by
  classical
  by_contra hnone
  push Not at hnone
  obtain ⟨c, hbc, hc⟩ := exists_between hb
  let cell : ℝ → ℝ≥0∞ := fun L => volume (axisAlignedCell (d := d) L)
  let shell : ℝ → ℝ≥0∞ := fun L =>
    volume (((PeriodicConstantApprox.uniformShellShift d (-(1 / 2 : ℝ))) +ᵥ
      insetAxisAlignedCell (d := d) (L + 1) 0) \
      insetAxisAlignedCell (d := d) L 1)
  have hshell : Tendsto (fun L : ℝ => shell L / cell L) atTop (𝓝 0) := by
    simpa [shell, cell] using
      (PeriodicConstantApprox.axis_shell_relative_cell_volume_tends_zero (d := d))
  have hsmall : ∀ᶠ L : ℝ in atTop, b + shell L / cell L < c := by
    have hlim : Tendsto (fun L : ℝ => b + shell L / cell L) atTop (𝓝 b) := by
      simpa only [add_zero] using tendsto_const_nhds.add hshell
    exact hlim.eventually (Iio_mem_nhds hbc)
  obtain ⟨L, hL, hsmallL⟩ := ((eventually_gt_atTop (0 : ℝ)).and hsmall).exists
  have hcell_top : cell L ≠ ∞ := by
    simp only [PeriodicConstant.axis_cell_volume_formula, ne_eq, ENNReal.pow_eq_top_iff,
      ENNReal.ofReal_ne_top,
      false_and, not_false_eq_true, cell]
  have hcell_zero : cell L ≠ 0 := by
    simp only [PeriodicConstant.axis_cell_volume_formula, ne_eq, pow_eq_zero_iff',
      ENNReal.ofReal_eq_zero,
      not_and, Decidable.not_not, isEmpty_Prop, not_le, hL, IsEmpty.forall_iff, cell]
  have hden :
      (↑(Real.toNNReal (ZLattice.covolume (axisCellLattice (d := d) L hL) volume)) : ℝ≥0∞) =
        cell L := by
    rw [PeriodicConstantApprox.axis_lattice_covolume_toNNReal (d := d) L hL]
    exact ENNReal.coe_toNNReal hcell_top
  obtain ⟨C, hC⟩ := PeriodicConstantApprox.axis_cell_subset_enclosing_ball (d := d) L hL
  let A : ℝ≥0∞ := b + shell L / cell L
  have hAc : A < c := hsmallL
  have hratio : Tendsto (fun R : ℝ => A *
        (volume (ball (0 : EuclideanSpace ℝ (Fin d)) (R + (1 / 2 + 2 * C))) /
          volume (ball (0 : EuclideanSpace ℝ (Fin d)) (R + 0)))) atTop (𝓝 A) := by
    simpa only [one_div, add_zero, mul_one] using
      (ENNReal.Tendsto.const_mul
        (volume_ball_add_div_volume_ball_add_tendsto_one
          (d := d) (C := 1 / 2 + 2 * C) (C' := 0) hd)
        (Or.inl one_ne_zero))
  have hratio_small : ∀ᶠ R : ℝ in atTop, A *
      (volume (ball (0 : EuclideanSpace ℝ (Fin d)) (R + (1 / 2 + 2 * C))) /
        volume (ball (0 : EuclideanSpace ℝ (Fin d)) (R + 0))) < c :=
    hratio.eventually (Iio_mem_nhds hAc)
  obtain ⟨R, hR_density, hR_ratio⟩ :=
    ((S.frequently_local_density_exceeds_threshold hc).and_eventually hratio_small).exists
  let huSet := S.finite_center_ball_intersection_set (R + (1 / 2 : ℝ))
  let u : Finset (EuclideanSpace ℝ (Fin d)) := huSet.toFinset
  let htSet := PeriodicConstantApprox.lattice_points_in_ball_finite (d := d) L hL
    (R + (1 / 2 : ℝ) + C)
  let t : Finset (axisCellLattice (d := d) L hL) := htSet.toFinset
  let index (x : EuclideanSpace ℝ (Fin d)) : axisCellLattice (d := d) L hL :=
    -PeriodicConstantApprox.axisCellCoverIndex (d := d) L hL x
  have hindex : ∀ x ∈ u, index x ∈ t := by
    intro x hx
    have hxball : x ∈ ball (0 : EuclideanSpace ℝ (Fin d)) (R + (1 / 2 : ℝ)) :=
      (huSet.mem_toFinset.mp (by simpa only [one_div, Set.Finite.mem_toFinset,
        Set.mem_inter_iff, mem_ball, dist_zero_right, u] using hx)).2
    apply htSet.mem_toFinset.mpr
    simpa [index, t] using
      (PeriodicConstantApprox.negated_cover_index_mem_enlarged_ball
        (d := d) L hL (C := C) (R := R + (1 / 2 : ℝ)) hC hxball)
  let piece (g : axisCellLattice (d := d) L hL) : Finset (EuclideanSpace ℝ (Fin d)) :=
    u.filter fun x => index x = g
  let inner (g : axisCellLattice (d := d) L hL) : Finset (EuclideanSpace ℝ (Fin d)) :=
    (piece g).filter fun x =>
      x ∈ g +ᵥ insetAxisAlignedCell (d := d) L (2⁻¹ : ℝ)
  let boundary (g : axisCellLattice (d := d) L hL) : Finset (EuclideanSpace ℝ (Fin d)) :=
    (piece g).filter fun x =>
      x ∉ g +ᵥ insetAxisAlignedCell (d := d) L (2⁻¹ : ℝ)
  let V : ℝ≥0∞ := volume (ball (0 : EuclideanSpace ℝ (Fin d)) (2⁻¹ : ℝ))
  have hpiece_center {g : axisCellLattice (d := d) L hL}
      {x : EuclideanSpace ℝ (Fin d)} (hx : x ∈ piece g) : x ∈ S.centers := by
    have hx' : x ∈ u.filter (fun y => index y = g) := by
      simpa only [piece] using hx
    have hxu : x ∈ u := (Finset.mem_filter.mp hx').1
    exact (huSet.mem_toFinset.mp (by simpa only [one_div, Set.Finite.mem_toFinset,
      Set.mem_inter_iff, mem_ball, dist_zero_right, u] using hxu)).1
  have hpiece_cell {g : axisCellLattice (d := d) L hL}
      {x : EuclideanSpace ℝ (Fin d)} (hx : x ∈ piece g) :
      x ∈ g +ᵥ axisAlignedCell (d := d) L := by
    have hx' : x ∈ u.filter (fun y => index y = g) := by
      simpa only [piece] using hx
    have hidx : index x = g := (Finset.mem_filter.mp hx').2
    apply (PeriodicConstantApprox.mem_translated_cell_iff_cover_index (d := d) L hL g x).2
    simpa only  using hidx.symm
  have hinner_bound (g : axisCellLattice (d := d) L hL) :
      ((inner g).card : ℝ≥0∞) * V ≤ b * cell L := by
    obtain ⟨P, hPsep, hPdensity⟩ :=
      PeriodicConstantApprox.replicated_cell_packing_density_formula
        (d := d) hd S hSsep hL (inner g)
        (by
          intro x hx
          exact hpiece_center (Finset.mem_filter.mp (by simpa only [Finset.mem_filter,
            inner] using hx)).1)
        (by
          intro x hx
          exact (Finset.mem_filter.mp (by simpa only [Finset.mem_filter, inner] using hx)).2)
    have hPbound : P.upperPackingDensity ≤ b := hnone P hPsep
    rw [hPdensity, hden] at hPbound
    exact (ENNReal.div_le_iff hcell_zero hcell_top).mp (by simpa only [V] using hPbound)
  have hboundary_bound (g : axisCellLattice (d := d) L hL) :
      ((boundary g).card : ℝ≥0∞) * V ≤ shell L := by
    apply PeriodicConstantApprox.boundary_count_mul_ball_volume_le_shell
      (d := d) S hL hSsep
    · intro x hx
      have hx' : x ∈ (piece g).filter (fun y =>
          y ∉ g +ᵥ insetAxisAlignedCell (d := d) L (2⁻¹ : ℝ)) := by
        simpa only [boundary] using hx
      exact hpiece_center (Finset.mem_filter.mp hx').1
    · intro x hx
      have hx' : x ∈ (piece g).filter (fun y =>
          y ∉ g +ᵥ insetAxisAlignedCell (d := d) L (2⁻¹ : ℝ)) := by
        simpa only [boundary] using hx
      have hx' := Finset.mem_filter.mp hx'
      exact ⟨hpiece_cell hx'.1, by simpa only [one_div] using hx'.2⟩
  have hpiece_bound (g : axisCellLattice (d := d) L hL) :
      ((piece g).card : ℝ≥0∞) * V ≤ A * cell L := by
    have hcard : (inner g).card + (boundary g).card = (piece g).card := by
      simpa only  using
        (Finset.card_filter_add_card_filter_not
          (s := piece g)
          (fun x : EuclideanSpace ℝ (Fin d) =>
            x ∈ g +ᵥ insetAxisAlignedCell (d := d) L (2⁻¹ : ℝ)))
    have hcard' : ((piece g).card : ℝ≥0∞) =
        ((inner g).card : ℝ≥0∞) + (boundary g).card := by
      exact_mod_cast hcard.symm
    calc
      ((piece g).card : ℝ≥0∞) * V =
          ((inner g).card : ℝ≥0∞) * V +
            ((boundary g).card : ℝ≥0∞) * V := by
              rw [hcard', add_mul]
      _ ≤ b * cell L + shell L :=
        add_le_add (hinner_bound g) (hboundary_bound g)
      _ = A * cell L := by
        simp only [add_mul, ENNReal.div_mul_cancel hcell_zero hcell_top, A]
  have hpartition : ∑ g ∈ t, (piece g).card = u.card := by
    simpa only [Finset.filter_eq_self.mpr hindex] using
      (Finset.sum_card_fiberwise_eq_card_filter u t index)
  have hsum_bound :
      (u.card : ℝ≥0∞) * V ≤ (t.card : ℝ≥0∞) * (A * cell L) := by
    have hcast : (u.card : ℝ≥0∞) =
        ∑ g ∈ t, ((piece g).card : ℝ≥0∞) := by
      exact_mod_cast hpartition.symm
    calc
      (u.card : ℝ≥0∞) * V =
          (∑ g ∈ t, ((piece g).card : ℝ≥0∞)) * V := by rw [hcast]
      _ = ∑ g ∈ t, ((piece g).card : ℝ≥0∞) * V := by
        simp_rw [Finset.sum_mul]
      _ ≤ ∑ _g ∈ t, A * cell L :=
        Finset.sum_le_sum fun g _ => hpiece_bound g
      _ = (t.card : ℝ≥0∞) * (A * cell L) := by
        simp only [Finset.sum_const, nsmul_eq_mul]
  have ht_volume : (t.card : ℝ≥0∞) * cell L ≤
      volume (ball (0 : EuclideanSpace ℝ (Fin d))
        ((R + (1 / 2 : ℝ)) + 2 * C)) := by
    simpa [t, htSet, cell] using
      (PeriodicConstantApprox.lattice_count_mul_cell_volume_le_ball_volume
        (d := d) (hL := hL) (R := R + (1 / 2 : ℝ)) (C := C) hC)
  have hcenter_bound : (u.card : ℝ≥0∞) * V ≤
      A * volume (ball (0 : EuclideanSpace ℝ (Fin d))
        (R + (1 / 2 + 2 * C))) := by
    calc
      (u.card : ℝ≥0∞) * V ≤ (t.card : ℝ≥0∞) * (A * cell L) := hsum_bound
      _ = A * ((t.card : ℝ≥0∞) * cell L) := by ac_rfl
      _ ≤ A * volume (ball (0 : EuclideanSpace ℝ (Fin d))
            (R + (1 / 2 + 2 * C))) := by
          gcongr
          simpa only [one_div, add_assoc] using ht_volume
  have hlocal_bound : S.densityInsideRadius R ≤
      (u.card : ℝ≥0∞) * V /
        volume (ball (0 : EuclideanSpace ℝ (Fin d)) R) := by
    have h := S.local_density_upper_bound hd R
    simp only [hSsep, one_div] at h
    have henc :
        (S.centers ∩ ball (0 : EuclideanSpace ℝ (Fin d))
          (R + (2⁻¹ : ℝ))).encard = (u.card : ENat) := by
      simpa [u, huSet, one_div] using huSet.encard_eq_coe_toFinset_card
    rw [henc] at h
    simpa only [ge_iff_le, ENat.toENNReal_coe] using h
  have hfinal : S.densityInsideRadius R ≤ A *
      (volume (ball (0 : EuclideanSpace ℝ (Fin d)) (R + (1 / 2 + 2 * C))) /
        volume (ball (0 : EuclideanSpace ℝ (Fin d)) (R + 0))) := by
    calc
      S.densityInsideRadius R ≤
          (u.card : ℝ≥0∞) * V /
            volume (ball (0 : EuclideanSpace ℝ (Fin d)) R) := hlocal_bound
      _ ≤ (A * volume (ball (0 : EuclideanSpace ℝ (Fin d))
            (R + (1 / 2 + 2 * C)))) /
              volume (ball (0 : EuclideanSpace ℝ (Fin d)) R) := by
          gcongr
      _ = A *
          (volume (ball (0 : EuclideanSpace ℝ (Fin d)) (R + (1 / 2 + 2 * C))) /
            volume (ball (0 : EuclideanSpace ℝ (Fin d)) (R + 0))) := by
          simp only [div_eq_mul_inv, one_mul, mul_assoc, add_zero]
  exact (not_lt_of_ge (le_of_lt (lt_of_le_of_lt hfinal hR_ratio))) hR_density

end SpherePacking

private theorem periodic_packing_supremum_eq_unrestricted (hd : 0 < d) :
    PeriodicSpherePackingConstant d = SpherePackingConstant d := by
  rw [periodic_packing_supremum_eq_unit_separation (d := d),
    SpherePacking.packing_supremum_eq_unit_separation (d := d)]
  apply le_antisymm
  · refine iSup₂_le ?_
    intro P hPsep
    refine
      (le_iSup
          (fun _ : (P.toSpherePacking).separation = 1 ↦ (P.toSpherePacking).upperPackingDensity)
          hPsep).trans ?_
    exact le_iSup (fun S : SpherePacking d ↦ ⨆ (_ : S.separation = 1),
      S.upperPackingDensity) P.toSpherePacking
  · refine iSup₂_le ?_
    intro S hSsep
    refine le_of_forall_lt ?_
    intro a ha
    rcases exists_between ha with ⟨b, hab, hbS⟩
    rcases SpherePacking.exists_periodic_unit_packing_above_density_threshold
      (d := d) hd S hSsep hbS with
      ⟨P, hPsep, hbP⟩
    have hb_lt_sup : b < ⨆ (P : PeriodicSpherePacking d) (_ : P.separation = 1),
      P.upperPackingDensity :=
      lt_of_lt_of_le hbP (le_iSup_of_le P (le_iSup_of_le hPsep le_rfl))
    exact hab.trans hb_lt_sup

end

section

open scoped BigOperators Real
open MeasureTheory

namespace SchwartzMap.UnitAddTorus

private noncomputable def coordinateTorusProjection (n : ℕ) : (Fin n → ℝ) → UnitAddTorus (Fin n) :=
  fun x i => (x i : UnitAddCircle)

@[continuity]
private theorem continuous_coordinate_torus_projection {n : ℕ} : Continuous
  (coordinateTorusProjection n) := by
  simpa only [QuotientAddGroup.coe_mk', Function.comp_apply] using!
    (continuous_pi fun i => (AddCircle.continuous_mk' (p := (1 : ℝ))).comp (continuous_apply i))

private noncomputable def successorCoordinateHomeomorphism (α : Type*) [TopologicalSpace α] (n :
  ℕ) :
    (α × (Fin n → α)) ≃ₜ (Fin n.succ → α) where
  toEquiv := Fin.consEquiv (fun _ ↦ α)
  continuous_toFun := by
    simpa only [Nat.succ_eq_add_one, Fin.consEquiv, Equiv.toFun_as_coe,
      Equiv.coe_fn_mk] using! Continuous.finCons (by fun_prop) (by fun_prop)
  continuous_invFun := by fun_prop

private theorem coordinate_torus_projection_is_open_quotient (n : ℕ) : IsOpenQuotientMap
  (coordinateTorusProjection n) := by
  induction n with
  | zero =>
      have h : coordinateTorusProjection 0 =
          (Homeomorph.homeomorphOfUnique (Fin 0 → ℝ) (UnitAddTorus (Fin 0)) : _ → _) := by
        funext x; exact Subsingleton.elim _ _
      simpa only [h] using!
        (Homeomorph.homeomorphOfUnique (Fin 0 → ℝ) (UnitAddTorus (Fin 0))).isOpenQuotientMap
  | succ n ih =>
      have h₁ : IsOpenQuotientMap (fun x : ℝ => (x : UnitAddCircle)) := by
        simpa only  using!
          (QuotientAddGroup.isOpenQuotientMap_mk (G := ℝ) (N := AddSubgroup.zmultiples (1 : ℝ)))
      let eX := (successorCoordinateHomeomorphism (α := ℝ) n).symm
      let eY := successorCoordinateHomeomorphism (α := UnitAddCircle) n
      have heX : IsOpenQuotientMap (eX : (Fin n.succ → ℝ) → ℝ × (Fin n → ℝ)) :=
        eX.isOpenQuotientMap
      have hprod :
          IsOpenQuotientMap (Prod.map (fun x : ℝ => (x : UnitAddCircle))
            (coordinateTorusProjection n)) :=
        IsOpenQuotientMap.prodMap h₁ (ih)
      have hconj :
          coordinateTorusProjection n.succ =
            (fun x =>
              eY
                (Prod.map (fun x : ℝ => (x : UnitAddCircle)) (coordinateTorusProjection n) (eX
                  x))) := by
        funext x
        ext i
        cases i using Fin.cases with
        | zero => rfl
        | succ i => rfl
      have hhomeoY : IsOpenQuotientMap eY := eY.isOpenQuotientMap
      rw [hconj]
      exact IsOpenQuotientMap.comp hhomeoY
        (IsOpenQuotientMap.comp hprod heX)

private theorem coordinate_torus_projection_measure_preserving (n : ℕ) (t : ℝ) :
    MeasurePreserving (coordinateTorusProjection n)
      (Measure.pi fun _ : Fin n => (volume : Measure ℝ).restrict (Set.Ioc t (t + 1)))
      (volume : Measure (UnitAddTorus (Fin n))) := by
  simpa only  using!
    (MeasureTheory.measurePreserving_pi
      (μ := fun _ : Fin n => (volume : Measure ℝ).restrict (Set.Ioc t (t + 1)))
      (ν := fun _ : Fin n => (volume : Measure UnitAddCircle))
      (hf := fun _ => UnitAddCircle.measurePreserving_mk t))

private theorem restricted_product_volume_eq_product_restriction (n : ℕ) (t : ℝ) :
    (volume : Measure (Fin n → ℝ)).restrict (Set.univ.pi fun _ : Fin n => Set.Ioc t (t + 1)) =
      Measure.pi fun _ : Fin n => (volume : Measure ℝ).restrict (Set.Ioc t (t + 1)) := by
  simpa only  using! (Measure.restrict_pi_pi
    (μ := fun _ : Fin n => (volume : Measure ℝ)) (s := fun _ : Fin n => Set.Ioc t (t + 1)))

private theorem fourier_character_coordinate_projection (n : ℕ) (k : Fin n → ℤ) (x : Fin n → ℝ) :
    UnitAddTorus.mFourier k (coordinateTorusProjection n x) =
      Complex.exp
        (2 * π * Complex.I *
          (∑ i : Fin n, (k i : ℝ) * x i)) := by
  simpa only [UnitAddTorus.mFourier, fourier_apply, ContinuousMap.coe_mk, coordinateTorusProjection,
    fourier_coe_apply', mul_comm, mul_left_comm, Complex.ofReal_one, div_one,
      Complex.ofReal_sum, Complex.ofReal_mul,
    Complex.ofReal_intCast, Finset.mul_sum, mul_assoc] using!
    (Complex.exp_sum (s := (Finset.univ : Finset (Fin n)))
        (f := fun i : Fin n => 2 * π * Complex.I * ((k i : ℝ) * x i))).symm

private theorem fourier_character_coordinate_projection_ofLp (n : ℕ) (k : Fin n → ℤ) (x :
  EuclideanSpace ℝ (Fin n)) :
    UnitAddTorus.mFourier k (coordinateTorusProjection n (WithLp.ofLp x)) =
      Complex.exp
        (2 * π * Complex.I *
          (∑ i : Fin n, (k i : ℝ) * x i)) := by
  simpa only [Complex.ofReal_sum, Complex.ofReal_mul,
    Complex.ofReal_intCast] using! (fourier_character_coordinate_projection (n := n) (k := k) (x
    := WithLp.ofLp x))

private theorem torus_integral_eq_coordinate_cell_integral (n : ℕ) (t : ℝ) (g : UnitAddTorus
  (Fin n) → ℂ)
    (hg : AEStronglyMeasurable g (volume : Measure (UnitAddTorus (Fin n)))) :
    (∫ y : UnitAddTorus (Fin n), g y) =
      ∫ x, g (coordinateTorusProjection n x) ∂(volume : Measure (Fin n → ℝ)).restrict
        (Set.univ.pi fun _ : Fin n => Set.Ioc t (t + 1)) := by
  have hmp := coordinate_torus_projection_measure_preserving n t
  have h1 :
      (∫ y : UnitAddTorus (Fin n), g y) =
        ∫ x, g (coordinateTorusProjection n x) ∂(Measure.pi fun _ : Fin n =>
          (volume : Measure ℝ).restrict (Set.Ioc t (t + 1))) := by
    rw [← hmp.map_eq]
    simpa only  using! (MeasureTheory.integral_map (hφ := hmp.aemeasurable) (f := g)
      (hfm := by simpa only [hmp.map_eq] using! hg))
  simpa only [(restricted_product_volume_eq_product_restriction n t).symm] using! h1

end SchwartzMap.UnitAddTorus

end

section

namespace SpherePacking.ForMathlib.Fourier

open scoped FourierTransform
open MeasureTheory

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V]

private theorem fourier_precompose_linear_equivalence (A : V ≃ₗ[ℝ] V) (f : V → ℂ) (w : V) :
    𝓕 (fun x ↦ f (A x)) w =
      (abs (LinearMap.det (A : V →ₗ[ℝ] V)))⁻¹ •
        𝓕 f (((A.symm : V ≃ₗ[ℝ] V).toLinearMap).adjoint w) := by
  rw [Real.fourier_eq', Real.fourier_eq']
  let B : V →L[ℝ] V := A.toContinuousLinearEquiv.toContinuousLinearMap
  let g : V → ℂ := fun x =>
    Complex.exp
      ((↑(-2 * Real.pi * @inner ℝ V _ x
        (((A.symm : V ≃ₗ[ℝ] V).toLinearMap).adjoint w)) : ℂ) * Complex.I) • f x
  have hinner (x : V) :
      @inner ℝ V _ (A x)
        (((A.symm : V ≃ₗ[ℝ] V).toLinearMap).adjoint w) =
          @inner ℝ V _ x w := by
    rw [LinearMap.adjoint_inner_right]
    simp only [LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply]
  have hchange :
      (∫ x : V, g x) =
        |LinearMap.det (A : V →ₗ[ℝ] V)| • ∫ x : V, g (A x) := by
    have h := MeasureTheory.integral_image_eq_integral_abs_det_fderiv_smul
      (volume : Measure V) (s := Set.univ) (f := fun x : V => A x)
      (f' := fun _ : V => B) MeasurableSet.univ
      (fun x _ => B.hasFDerivAt.hasFDerivWithinAt)
      (Set.injOn_of_injective A.injective) g
    have hdetB : B.det = LinearMap.det (A : V →ₗ[ℝ] V) := by
      rfl
    calc
      (∫ x : V, g x) =
          ∫ x : V, |LinearMap.det (A : V →ₗ[ℝ] V)| • g (A x) := by
        simpa only [Complex.real_smul, Set.image_univ, A.surjective.range_eq,
          Measure.restrict_univ, hdetB] using h
      _ = |LinearMap.det (A : V →ₗ[ℝ] V)| • ∫ x : V, g (A x) :=
        integral_smul _ _
  have hdet : LinearMap.det (A : V →ₗ[ℝ] V) ≠ 0 := by
    intro hzero
    have hcomp := LinearMap.det_comp
      ((A.symm : V ≃ₗ[ℝ] V).toLinearMap) (A : V →ₗ[ℝ] V)
    simp only [LinearEquiv.comp_coe, LinearEquiv.self_trans_symm, LinearEquiv.refl_toLinearMap,
      LinearMap.det_id,
      hzero, mul_zero, one_ne_zero] at hcomp
  change (∫ x : V,
    Complex.exp ((↑(-2 * Real.pi * @inner ℝ V _ x w) : ℂ) * Complex.I) •
      f (A x)) = |LinearMap.det (A : V →ₗ[ℝ] V)|⁻¹ • ∫ x : V, g x
  have hleft :
      (∫ x : V,
        Complex.exp ((↑(-2 * Real.pi * @inner ℝ V _ x w) : ℂ) * Complex.I) •
          f (A x)) = ∫ x : V, g (A x) := by
    congr 1
    funext x
    simp only [neg_mul, Complex.ofReal_neg, Complex.ofReal_mul, Complex.ofReal_ofNat,
      smul_eq_mul, hinner, g]
  rw [hleft]
  calc
    (∫ x : V, g (A x)) =
        |LinearMap.det (A : V →ₗ[ℝ] V)|⁻¹ •
          (|LinearMap.det (A : V →ₗ[ℝ] V)| • ∫ x : V, g (A x)) := by
      rw [← mul_smul, inv_mul_cancel₀ (abs_ne_zero.mpr hdet), one_smul]
    _ = |LinearMap.det (A : V →ₗ[ℝ] V)|⁻¹ • ∫ x : V, g x := by
      rw [hchange]

end SpherePacking.ForMathlib.Fourier

end

section

open scoped BigOperators
open MeasureTheory

namespace SchwartzMap

variable {d : ℕ}
variable (Λ : Submodule ℤ (EuclideanSpace ℝ (Fin d))) [DiscreteTopology Λ] [IsZLattice ℝ Λ]

section StandardLattice

private noncomputable def referenceIntegerLattice (d : ℕ) :
    Submodule ℤ (EuclideanSpace ℝ (Fin d)) :=
  Submodule.span ℤ (Set.range ((EuclideanSpace.basisFun (Fin d) ℝ).toBasis))

namespace referenceIntegerLattice

private noncomputable instance instDiscreteReferenceIntegerLattice : DiscreteTopology
  (referenceIntegerLattice d) := by
  simpa only [referenceIntegerLattice, OrthonormalBasis.coe_toBasis] using!
    (inferInstance :
      DiscreteTopology
        (Submodule.span ℤ (Set.range ((EuclideanSpace.basisFun (Fin d) ℝ).toBasis))))

private noncomputable instance instFullRankPackingLattice : IsZLattice ℝ
  (referenceIntegerLattice d) := by
  simpa only [referenceIntegerLattice, OrthonormalBasis.coe_toBasis] using!
    (inferInstance :
      IsZLattice ℝ
        (Submodule.span ℤ (Set.range ((EuclideanSpace.basisFun (Fin d) ℝ).toBasis))))

end StandardLattice.referenceIntegerLattice

section PoissonSummation

namespace PoissonSummation

namespace Standard

private noncomputable def embeddedIntegerVector (k : Fin d → ℤ) : (EuclideanSpace ℝ (Fin d)) :=
  WithLp.toLp (2 : ENNReal) (fun i : Fin d => (k i : ℝ))

@[simp]
private lemma embedded_integer_vector_coordinate (k : Fin d → ℤ) (i : Fin d) :
    embeddedIntegerVector (d := d) k i = (k i : ℝ) := by
  simp only [embeddedIntegerVector]

private lemma embedded_integer_vector_mem_reference_lattice (k : Fin d → ℤ) :
    embeddedIntegerVector (d := d) k ∈ SchwartzMap.referenceIntegerLattice d := by
  have hsum :
      embeddedIntegerVector (d := d) k =
        ∑ i : Fin d, (k i) • ((EuclideanSpace.basisFun (Fin d) ℝ).toBasis i) := by
    ext j
    simp only [embeddedIntegerVector, OrthonormalBasis.coe_toBasis, EuclideanSpace.basisFun_apply,
      WithLp.ofLp_sum, WithLp.ofLp_smul, PiLp.ofLp_single, zsmul_eq_mul, Finset.sum_apply,
        Pi.mul_apply, Pi.intCast_apply,
      Pi.single_apply, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, ↓reduceIte]
  rw [hsum]
  refine (SchwartzMap.referenceIntegerLattice d).sum_mem ?_
  intro i hi
  refine (SchwartzMap.referenceIntegerLattice d).smul_mem (k i) ?_
  exact Submodule.subset_span ⟨i, rfl⟩

end SchwartzMap.PoissonSummation.PoissonSummation.Standard

namespace SchwartzMap

open TopologicalSpace MeasureTheory

variable {d : ℕ}

namespace PoissonSummation.Standard
open _root_.SchwartzMap.UnitAddTorus

private noncomputable def halfOpenUnitCell : Set (EuclideanSpace ℝ (Fin d)) := {x | ∀ i : Fin d,
  x i ∈ Set.Ioc (0 : ℝ) 1}

private lemma half_open_unit_cell_measurable : MeasurableSet (halfOpenUnitCell (d := d)) := by
  have hset :
      halfOpenUnitCell (d := d) = ⋂ i : Fin d,
        {x : (EuclideanSpace ℝ (Fin d)) | x i ∈ Set.Ioc (0 : ℝ) 1} := by
    ext x
    simp only [halfOpenUnitCell, Set.mem_Ioc, Set.mem_ofPred_eq, Set.mem_iInter]
  have hcoord :
      ∀ i : Fin d, MeasurableSet {x : (EuclideanSpace ℝ (Fin d)) | x i ∈ Set.Ioc (0 : ℝ) 1} := by
    intro i
    have hproj : Measurable fun x : (EuclideanSpace ℝ (Fin d)) => x i := by
      simpa only  using!
        (PiLp.continuous_apply (p := (2 : ENNReal)) (β := fun _ : Fin d => ℝ) i).measurable
    exact hproj measurableSet_Ioc
  simpa only [hset, Set.mem_Ioc] using! MeasurableSet.iInter (ι := Fin d) hcoord

private lemma half_open_unit_cell_null_measurable : NullMeasurableSet (halfOpenUnitCell (d := d)) :=
  (half_open_unit_cell_measurable (d := d)).nullMeasurableSet

private lemma unique_integer_shift_into_half_open_cell (x : (EuclideanSpace ℝ (Fin d))) :
    ∃! n : Fin d → ℤ, x + SchwartzMap.PoissonSummation.Standard.embeddedIntegerVector (d := d) n ∈
      halfOpenUnitCell (d := d) := by
  have hxcoord :
      ∀ i : Fin d, ∃! m : ℤ, (x i : ℝ) + m • (1 : ℝ) ∈ Set.Ioc (0 : ℝ) 1 := by
    intro i
    simpa only [zsmul_eq_mul, mul_one, Set.mem_Ioc, zero_add] using!
      (existsUnique_add_zsmul_mem_Ioc (G := ℝ) (ha := zero_lt_one) (b := (x i : ℝ))
        (c := (0 : ℝ)))
  choose n hn hn_unique using hxcoord
  refine ⟨n, ?_, ?_⟩
  · intro i
    simpa only [PiLp.add_apply, embedded_integer_vector_coordinate, Set.mem_Ioc, zsmul_eq_mul,
      mul_one] using! hn i
  · intro n' hn'
    funext i
    have hcoords : ∀ i : Fin d,
        (x + SchwartzMap.PoissonSummation.Standard.embeddedIntegerVector (d := d) n') i ∈
          Set.Ioc (0 : ℝ) 1 := by
      simpa only [PiLp.add_apply, embedded_integer_vector_coordinate, Set.mem_Ioc, halfOpenUnitCell,
        Set.mem_ofPred_eq] using! hn'
    exact hn_unique i (n' i) (by
      simpa only [zsmul_eq_mul, mul_one, Set.mem_Ioc, PiLp.add_apply,
        embedded_integer_vector_coordinate] using! hcoords i)

private lemma reference_lattice_element_eq_integer_vector (x : (EuclideanSpace ℝ (Fin d)))
    (hx : x ∈ SchwartzMap.referenceIntegerLattice d) :
    ∃ n : Fin d → ℤ, x = SchwartzMap.PoissonSummation.Standard.embeddedIntegerVector (d := d) n
      := by
  let b : OrthonormalBasis (Fin d) ℝ (EuclideanSpace ℝ (Fin d)) := EuclideanSpace.basisFun (Fin d) ℝ
  have hx_span :
      x ∈ Submodule.span ℤ (Set.range fun j : Fin d => (b.toBasis j : (EuclideanSpace ℝ (Fin
        d)))) := by
    simpa only [OrthonormalBasis.coe_toBasis, referenceIntegerLattice] using! hx
  have hx_repr :=
    (Module.Basis.mem_span_iff_repr_mem (R := ℤ) (b := b.toBasis) x).1 hx_span
  choose n hn using hx_repr
  have hn' : ∀ i : Fin d, (n i : ℝ) = x i := by
    intro i
    simpa only [algebraMap_int_eq, eq_intCast, OrthonormalBasis.coe_toBasis_repr_apply,
      EuclideanSpace.basisFun_repr] using! hn i
  refine ⟨n, ?_⟩
  ext i
  simp only [embedded_integer_vector_coordinate, hn' i]

private lemma reference_lattice_dual_self :
    LinearMap.BilinForm.dualSubmodule (B := (innerₗ (EuclideanSpace ℝ (Fin d)) :
      LinearMap.BilinForm ℝ (EuclideanSpace ℝ (Fin d))))
        (SchwartzMap.referenceIntegerLattice d) =
      SchwartzMap.referenceIntegerLattice d := by
  ext x
  constructor
  · intro hx
    have hxcoord : ∀ i : Fin d, ∃ n : ℤ, (n : ℝ) = x i := by
      intro i
      have hinner :
          inner ℝ x (EuclideanSpace.basisFun (Fin d) ℝ i) ∈ (1 : Submodule ℤ ℝ) := by
        simpa only [EuclideanSpace.basisFun_apply, Submodule.mem_one, algebraMap_int_eq, eq_intCast,
          innerₗ_apply_apply] using!
          hx _ (Submodule.subset_span ⟨i, by simp only [OrthonormalBasis.coe_toBasis,
            EuclideanSpace.basisFun_apply]⟩)
      rcases Submodule.mem_one.mp hinner with ⟨n, hn⟩
      exact ⟨n, by simpa only [algebraMap_int_eq, eq_intCast,
        EuclideanSpace.inner_basisFun_real] using! hn⟩
    choose n hn using hxcoord
    have hx' : x = SchwartzMap.PoissonSummation.Standard.embeddedIntegerVector (d := d) n := by
      ext i
      simp only [embedded_integer_vector_coordinate, hn i]
    simpa only [hx'] using!
      SchwartzMap.PoissonSummation.Standard.embedded_integer_vector_mem_reference_lattice (d := d) n
  · intro hx y hy
    rcases reference_lattice_element_eq_integer_vector (d := d) x hx with ⟨n, rfl⟩
    rcases reference_lattice_element_eq_integer_vector (d := d) y hy with ⟨m, rfl⟩
    refine Submodule.mem_one.mpr ⟨∑ i : Fin d, n i * m i, ?_⟩
    simp only [algebraMap_int_eq, map_sum, eq_intCast, Int.cast_mul, embeddedIntegerVector,
      innerₗ_apply_apply,
      PiLp.inner_apply, RCLike.inner_apply, map_intCast, mul_comm]

end SchwartzMap.PoissonSummation.Standard
namespace SchwartzMap

variable {d : ℕ}

namespace PoissonSummation.Standard
open _root_.SchwartzMap.UnitAddTorus

private noncomputable def euclideanTorusProjection : (EuclideanSpace ℝ (Fin d)) → UnitAddTorus
  (Fin d) :=
  fun x => UnitAddTorus.coordinateTorusProjection d ((WithLp.ofLp : (EuclideanSpace ℝ (Fin d)) →
    (Fin d → ℝ)) x)

@[continuity]
private theorem continuous_euclidean_torus_projection : Continuous (euclideanTorusProjection (d
  := d)) := by
  simpa only  using! (UnitAddTorus.continuous_coordinate_torus_projection (n := d)).comp
    (PiLp.continuous_ofLp (p := (2 : ENNReal)) (β := fun _ : Fin d => ℝ))

private theorem euclidean_torus_projection_is_open_quotient : IsOpenQuotientMap
  (euclideanTorusProjection (d := d)) := by
  unfold euclideanTorusProjection
  exact IsOpenQuotientMap.comp (UnitAddTorus.coordinate_torus_projection_is_open_quotient d)
    (PiLp.homeomorph (p := (2 : ENNReal)) (β := fun _ : Fin d => ℝ)).isOpenQuotientMap

@[simp]
private theorem torus_projection_add_integer_vector (x : (EuclideanSpace ℝ (Fin d))) (n : Fin d
  → ℤ) :
    euclideanTorusProjection (d := d) (x +
      SchwartzMap.PoissonSummation.Standard.embeddedIntegerVector (d := d) n) =
      euclideanTorusProjection (d := d) x := by
  ext i
  simp only [euclideanTorusProjection, coordinateTorusProjection, PiLp.add_apply,
    embedded_integer_vector_coordinate, AddSubgroup.intCast_mem_zmultiples_one,
      QuotientAddGroup.mk_add_of_mem]

private theorem equal_torus_projections_differ_by_integer_vector {x y : (EuclideanSpace ℝ (Fin d))}
    (h : euclideanTorusProjection (d := d) x = euclideanTorusProjection (d := d) y) :
    ∃ n : Fin d → ℤ, x - y = SchwartzMap.PoissonSummation.Standard.embeddedIntegerVector (d :=
      d) n := by
  have hcoord : ∀ i : Fin d, ∃ n : ℤ, (n : ℝ) = (x i - y i : ℝ) := by
    intro i
    have hsub : ((x i - y i : ℝ) : AddCircle (1 : ℝ)) = 0 := by
      simpa only [QuotientAddGroup.mk_sub, UnitAddCircle, euclideanTorusProjection,
        coordinateTorusProjection] using!
        sub_eq_zero.2 (congrArg (fun t => t i) h)
    rcases (AddCircle.coe_eq_zero_iff (p := (1 : ℝ)) (x := (x i - y i : ℝ))).1 hsub with ⟨n, hn⟩
    exact ⟨n, by simpa only [zsmul_eq_mul, mul_one] using! hn⟩
  choose n hn using hcoord
  refine ⟨n, ?_⟩
  ext i
  simp only [PiLp.sub_apply, embeddedIntegerVector, hn i]

private theorem half_open_cell_is_fundamental_region :
    MeasureTheory.IsAddFundamentalDomain (SchwartzMap.referenceIntegerLattice d)
      (SchwartzMap.PoissonSummation.Standard.halfOpenUnitCell (d := d)) (volume : Measure
        (EuclideanSpace ℝ (Fin d))) := by
  refine MeasureTheory.IsAddFundamentalDomain.mk'
      (SchwartzMap.PoissonSummation.Standard.half_open_unit_cell_null_measurable (d := d)) ?_
  intro x
  rcases SchwartzMap.PoissonSummation.Standard.unique_integer_shift_into_half_open_cell (d := d)
    x with
    ⟨n, hn, hn_unique⟩
  refine
    ⟨(⟨SchwartzMap.PoissonSummation.Standard.embeddedIntegerVector (d := d) n,
        SchwartzMap.PoissonSummation.Standard.embedded_integer_vector_mem_reference_lattice (d
          := d) n⟩), ?_, ?_⟩
  · simpa only [Submodule.vadd_def, vadd_eq_add, add_comm] using! hn
  · intro ℓ hℓ
    rcases
        SchwartzMap.PoissonSummation.Standard.reference_lattice_element_eq_integer_vector (d := d)
          (ℓ : (EuclideanSpace ℝ (Fin d))) ℓ.property with
      ⟨n', hn'⟩
    have : n' = n := hn_unique n' (by
      simpa only [Submodule.vadd_def, hn', vadd_eq_add, add_comm] using! hℓ)
    apply Subtype.ext
    simp only [hn', this]

private theorem torus_integral_eq_euclidean_cell_integral (g : UnitAddTorus (Fin d) → ℂ)
    (hg : AEStronglyMeasurable g (volume : Measure (UnitAddTorus (Fin d)))) :
    (∫ y : UnitAddTorus (Fin d), g y) =
      ∫ x, g (euclideanTorusProjection (d := d) x) ∂(volume : Measure (EuclideanSpace ℝ (Fin
        d))).restrict
        (SchwartzMap.PoissonSummation.Standard.halfOpenUnitCell (d := d)) := by
  have h1 :
      (∫ y : UnitAddTorus (Fin d), g y) =
        ∫ x, g (UnitAddTorus.coordinateTorusProjection d x) ∂(volume : Measure (Fin d → ℝ)).restrict
          (Set.univ.pi fun _ : Fin d => Set.Ioc (0 : ℝ) (0 + 1)) := by
    simpa only [zero_add] using!
      (UnitAddTorus.torus_integral_eq_coordinate_cell_integral (n := d) (t := (0 : ℝ)) g hg)
  let f : (Fin d → ℝ) ≃ᵐ (EuclideanSpace ℝ (Fin d)) := MeasurableEquiv.toLp 2 (Fin d → ℝ)
  have hmp : MeasurePreserving (⇑f) (volume : Measure (Fin d → ℝ)) (volume : Measure
    (EuclideanSpace ℝ (Fin d))) := by
    simpa only [MeasurableEquiv.coe_toLp] using! (PiLp.volume_preserving_toLp (ι := Fin d))
  have hpre :
      f ⁻¹' (SchwartzMap.PoissonSummation.Standard.halfOpenUnitCell (d := d)) =
        Set.univ.pi fun _ : Fin d => Set.Ioc (0 : ℝ) (0 + 1) := by
    ext x
    simp only [MeasurableEquiv.coe_toLp, halfOpenUnitCell, Set.mem_Ioc, Set.preimage_ofPred_eq,
      Set.mem_ofPred_eq,
      zero_add, Set.mem_pi, Set.mem_univ, forall_const, f]
  have hmpR :
      MeasurePreserving (⇑f)
        ((volume : Measure (Fin d → ℝ)).restrict
          (f ⁻¹' SchwartzMap.PoissonSummation.Standard.halfOpenUnitCell (d := d)))
        ((volume : Measure (EuclideanSpace ℝ (Fin d))).restrict
          (SchwartzMap.PoissonSummation.Standard.halfOpenUnitCell (d := d))) :=
    MeasurePreserving.restrict_preimage hmp
      (SchwartzMap.PoissonSummation.Standard.half_open_unit_cell_measurable (d := d))
  have h2 :
      (∫ x, g (UnitAddTorus.coordinateTorusProjection d x) ∂(volume : Measure (Fin d → ℝ)).restrict
          (Set.univ.pi fun _ : Fin d => Set.Ioc (0 : ℝ) (0 + 1))) =
        ∫ y, g (euclideanTorusProjection (d := d) y) ∂(volume : Measure (EuclideanSpace ℝ (Fin
          d))).restrict
          (SchwartzMap.PoissonSummation.Standard.halfOpenUnitCell (d := d)) := by
    simpa only [zero_add, euclideanTorusProjection, hpre, MeasurableEquiv.toLp_apply] using!
      (MeasurePreserving.integral_comp' hmpR
        (g := fun y : (EuclideanSpace ℝ (Fin d)) => g (UnitAddTorus.coordinateTorusProjection d
          (WithLp.ofLp y))))
  exact h1.trans h2

end SchwartzMap.PoissonSummation.Standard

end

section

open scoped BigOperators FourierTransform
open MeasureTheory

namespace SchwartzMap.PoissonSummation.Standard

variable {d : ℕ}

open _root_.SchwartzMap.UnitAddTorus

private noncomputable def integerVectorLatticeEquiv : (Fin d → ℤ) ≃
  (SchwartzMap.referenceIntegerLattice d) := by
  refine Equiv.ofBijective
    (fun n : Fin d → ℤ =>
      ⟨SchwartzMap.PoissonSummation.Standard.embeddedIntegerVector (d := d) n,
        SchwartzMap.PoissonSummation.Standard.embedded_integer_vector_mem_reference_lattice (d
          := d) n⟩)
    ?_
  refine ⟨?_, ?_⟩
  · intro a b hab
    have hab' :
        SchwartzMap.PoissonSummation.Standard.embeddedIntegerVector (d := d) a =
          SchwartzMap.PoissonSummation.Standard.embeddedIntegerVector (d := d) b := by
      simpa only  using! congrArg Subtype.val hab
    funext i
    have := congrArg (fun x : (EuclideanSpace ℝ (Fin d)) => x i) hab'
    simpa only [embedded_integer_vector_coordinate, Int.cast_inj] using! this
  · intro ℓ
    rcases
        SchwartzMap.PoissonSummation.Standard.reference_lattice_element_eq_integer_vector (d := d)
          (x := (ℓ : (EuclideanSpace ℝ (Fin d)))) ℓ.property with
      ⟨n, hn⟩
    refine ⟨n, ?_⟩
    apply Subtype.ext
    simpa only  using! hn.symm

variable (f : 𝓢(EuclideanSpace ℝ (Fin d), ℂ))

private noncomputable instance instMeasurableReferenceLatticeTranslation :
    MeasurableVAdd (SchwartzMap.referenceIntegerLattice d) (EuclideanSpace ℝ (Fin d)) := by
  refine { measurable_const_vadd := ?_, measurable_vadd_const := ?_ }
  · intro c
    simpa only [Submodule.vadd_def,
      vadd_eq_add] using! (continuous_const.add continuous_id).measurable
  · intro x
    simpa only [Submodule.vadd_def, vadd_eq_add] using!
      (continuous_subtype_val.add continuous_const).measurable

private noncomputable instance instReferenceLatticeTranslationInvariantVolume :
    MeasureTheory.VAddInvariantMeasure (SchwartzMap.referenceIntegerLattice d) (EuclideanSpace ℝ
      (Fin d)) (volume : Measure (EuclideanSpace ℝ (Fin d))) where
  measure_preimage_vadd c s hs := by
    simp only [Submodule.vadd_def, vadd_eq_add, measure_preimage_add]

private noncomputable def latticeTranslatedMap (ℓ : (SchwartzMap.referenceIntegerLattice d)) :
  C((EuclideanSpace ℝ (Fin d)), ℂ) :=
  (⟨(fun x => f x), f.continuous⟩ : C((EuclideanSpace ℝ (Fin d)),
    ℂ)).comp (ContinuousMap.addRight (ℓ : (EuclideanSpace ℝ (Fin d))))

private lemma finite_reference_lattice_points_of_norm_bound (r : ℝ) :
    ( {ℓ : (SchwartzMap.referenceIntegerLattice d) | ‖(ℓ : (EuclideanSpace ℝ (Fin d)))‖ ≤ r} :
      Set _ ).Finite := by
  have : DiscreteTopology (((SchwartzMap.referenceIntegerLattice d)).toAddSubgroup) :=
    (inferInstance : DiscreteTopology (SchwartzMap.referenceIntegerLattice d))
  have hfinE : Set.Finite (Metric.closedBall (0 : (EuclideanSpace ℝ (Fin d))) r ∩
    (((SchwartzMap.referenceIntegerLattice d)).toAddSubgroup : Set (EuclideanSpace ℝ (Fin d)))) :=
    Metric.finite_isBounded_inter_isClosed DiscreteTopology.isDiscrete
      Metric.isBounded_closedBall AddSubgroup.isClosed_of_discrete
  let e : (SchwartzMap.referenceIntegerLattice d) ↪ (EuclideanSpace ℝ (Fin d)) := ⟨fun ℓ => (ℓ :
    (EuclideanSpace ℝ (Fin d))), Subtype.coe_injective⟩
  have hfin_pre : (e ⁻¹' (Metric.closedBall (0 : (EuclideanSpace ℝ (Fin d))) r ∩
    ((SchwartzMap.referenceIntegerLattice d) : Set (EuclideanSpace ℝ (Fin d))))).Finite := by
    simpa only [Set.preimage_inter] using! Set.Finite.preimage_embedding e (by
      simpa only [AddSubgroup.coe_set_mk, Submodule.coe_toAddSubmonoid] using! hfinE)
  have :
      (e ⁻¹' (Metric.closedBall (0 : (EuclideanSpace ℝ (Fin d))) r ∩
        ((SchwartzMap.referenceIntegerLattice d) : Set (EuclideanSpace ℝ (Fin d))))) = {ℓ :
        (SchwartzMap.referenceIntegerLattice d) | ‖(ℓ : (EuclideanSpace ℝ (Fin d)))‖ ≤ r} := by
    ext ℓ
    simp only [Function.Embedding.coeFn_mk, Set.preimage_inter, Set.mem_inter_iff, Set.mem_preimage,
      Metric.mem_closedBall, dist_eq_norm, sub_eq_add_neg, neg_zero, add_zero, Subtype.coe_prop,
        and_true,
      Set.mem_ofPred_eq, e]
  simpa only [this] using! hfin_pre

private lemma summable_restricted_lattice_translate_norms (K : TopologicalSpace.Compacts
  (EuclideanSpace ℝ (Fin d))) :
    Summable (fun ℓ : (SchwartzMap.referenceIntegerLattice d) => ‖(latticeTranslatedMap (d := d)
      f ℓ).restrict K‖) := by
  let k : ℕ := Module.finrank ℤ (SchwartzMap.referenceIntegerLattice d) + 1
  obtain ⟨C, hCpos, hC⟩ := f.decay k 0
  have hC' : ∀ x : (EuclideanSpace ℝ (Fin d)), ‖x‖ ^ k * ‖f x‖ ≤ C := by
    simpa only [norm_iteratedFDeriv_zero] using! hC
  obtain ⟨r, hrK⟩ := K.isCompact.isBounded.subset_closedBall (0 : (EuclideanSpace ℝ (Fin d)))
  let r0 : ℝ := max r 0
  have hrK0 : (K : Set (EuclideanSpace ℝ (Fin d))) ⊆ Metric.closedBall (0 : (EuclideanSpace ℝ
    (Fin d))) r0 := by
    have hr_le : r ≤ r0 := le_max_left r 0
    have hball : Metric.closedBall (0 : (EuclideanSpace ℝ (Fin d))) r ⊆ Metric.closedBall (0 :
      (EuclideanSpace ℝ (Fin d))) r0 :=
      Metric.closedBall_subset_closedBall hr_le
    exact fun x hx => hball (hrK hx)
  let R : ℝ := max (2 * r0) 1
  have hfin :
      ( {ℓ : (SchwartzMap.referenceIntegerLattice d) | ‖(ℓ : (EuclideanSpace ℝ (Fin d)))‖ ≤ R} :
        Set _ ).Finite :=
    finite_reference_lattice_points_of_norm_bound (d := d) (r := R)
  have h_event :
      ∀ᶠ ℓ : (SchwartzMap.referenceIntegerLattice d) in Filter.cofinite,
        ‖(latticeTranslatedMap (d := d) f ℓ).restrict K‖ ≤ (C * (2 ^ k : ℝ)) * (‖(ℓ :
          (EuclideanSpace ℝ (Fin d)))‖⁻¹ ^ k) := by
    filter_upwards [hfin.eventually_cofinite_notMem] with ℓ hℓ
    have hRlt : R < ‖(ℓ : (EuclideanSpace ℝ (Fin d)))‖ := lt_of_not_ge (by simpa only [not_le]
      using! hℓ)
    have hnorm_lt : 2 * r0 < ‖(ℓ : (EuclideanSpace ℝ (Fin d)))‖ := lt_of_le_of_lt (le_max_left _
      _) hRlt
    have hnorm_pos : 0 < ‖(ℓ : (EuclideanSpace ℝ (Fin d)))‖ := lt_trans (by positivity) hRlt
    refine (ContinuousMap.norm_le _ (by positivity)).2 ?_
    rintro ⟨x, hxK⟩
    have hxball : (x : (EuclideanSpace ℝ (Fin d))) ∈ Metric.closedBall (0 : (EuclideanSpace ℝ
      (Fin d))) r0 := hrK0 hxK
    have hxnorm : ‖(x : (EuclideanSpace ℝ (Fin d)))‖ ≤ r0 := by
      simpa only [Metric.mem_closedBall, dist_eq_norm, sub_eq_add_neg, neg_zero,
        add_zero] using! hxball
    have hnorm_ge : (1 / 2 : ℝ) * ‖(ℓ : (EuclideanSpace ℝ (Fin d)))‖ ≤ ‖(x + (ℓ :
      (EuclideanSpace ℝ (Fin d))))‖ := by
      have hsub : ‖(ℓ : (EuclideanSpace ℝ (Fin d)))‖ - ‖(x : (EuclideanSpace ℝ (Fin d)))‖ ≤ ‖(ℓ
        : (EuclideanSpace ℝ (Fin d))) + x‖ := by
        simpa only [add_comm, tsub_le_iff_right, norm_neg,
          sub_neg_eq_add] using! (norm_sub_norm_le (ℓ : (EuclideanSpace ℝ (Fin d))) (-x))
      have hxlt : ‖(x : (EuclideanSpace ℝ (Fin d)))‖ < (1 / 2 : ℝ) * ‖(ℓ : (EuclideanSpace ℝ
        (Fin d)))‖ := by
        grind
      have : (1 / 2 : ℝ) * ‖(ℓ : (EuclideanSpace ℝ (Fin d)))‖ ≤ ‖(ℓ : (EuclideanSpace ℝ (Fin
        d)))‖ - ‖(x : (EuclideanSpace ℝ (Fin d)))‖ := by
        linarith [le_of_lt hxlt]
      have : (1 / 2 : ℝ) * ‖(ℓ : (EuclideanSpace ℝ (Fin d)))‖ ≤ ‖(ℓ : (EuclideanSpace ℝ (Fin
        d))) + x‖ := le_trans this hsub
      simpa only [one_div, ge_iff_le, add_comm] using! this
    have hnorm_xℓ_pos : 0 < ‖(x + (ℓ : (EuclideanSpace ℝ (Fin d))))‖ :=
      (by positivity : 0 < (1 / 2 : ℝ) * ‖(ℓ : (EuclideanSpace ℝ (Fin d)))‖).trans_le hnorm_ge
    have hpow_pos : 0 < ‖(x + (ℓ : (EuclideanSpace ℝ (Fin d))))‖ ^ k := pow_pos hnorm_xℓ_pos _
    have hdiv : ‖f (x + (ℓ : (EuclideanSpace ℝ (Fin d))))‖ ≤ C / (‖(x + (ℓ : (EuclideanSpace ℝ
      (Fin d))))‖ ^ k) :=
      (le_div_iff₀' hpow_pos).2 (hC' (x + (ℓ : (EuclideanSpace ℝ (Fin d)))))
    have hpow_le : C / (‖(x + (ℓ : (EuclideanSpace ℝ (Fin d))))‖ ^ k) ≤ (C * (2 ^ k : ℝ)) * (‖(ℓ
      : (EuclideanSpace ℝ (Fin d)))‖⁻¹ ^ k) := by
      have hpow_ge : ((1 / 2 : ℝ) * ‖(ℓ : (EuclideanSpace ℝ (Fin d)))‖) ^ k ≤ ‖(x + (ℓ :
        (EuclideanSpace ℝ (Fin d))))‖ ^ k :=
        pow_le_pow_left₀ (by positivity) hnorm_ge _
      have hinv :
          (‖(x + (ℓ : (EuclideanSpace ℝ (Fin d))))‖ ^ k)⁻¹ ≤ (2 ^ k : ℝ) * (‖(ℓ :
            (EuclideanSpace ℝ (Fin d)))‖⁻¹ ^ k) := by
        have hapos : 0 < ((1 / 2 : ℝ) * ‖(ℓ : (EuclideanSpace ℝ (Fin d)))‖) ^ k := by
          exact pow_pos (mul_pos (by positivity) hnorm_pos) _
        have :
            (‖(x + (ℓ : (EuclideanSpace ℝ (Fin d))))‖ ^ k)⁻¹ ≤ (((1 / 2 : ℝ) * ‖(ℓ :
              (EuclideanSpace ℝ (Fin d)))‖) ^ k)⁻¹ := by
          simpa only [one_div] using! (one_div_le_one_div_of_le hapos hpow_ge)
        simpa only [inv_pow, ge_iff_le, one_div, mul_pow, mul_inv_rev, inv_inv,
          mul_comm] using! this
      have := mul_le_mul_of_nonneg_left hinv (le_of_lt hCpos)
      simpa only [div_eq_mul_inv, inv_pow, mul_assoc, ge_iff_le] using! this
    have : ‖f (x + (ℓ : (EuclideanSpace ℝ (Fin d))))‖ ≤ (C * (2 ^ k : ℝ)) * (‖(ℓ :
      (EuclideanSpace ℝ (Fin d)))‖⁻¹ ^ k) :=
      le_trans hdiv hpow_le
    simpa only [SetLike.coe_sort_coe, latticeTranslatedMap, inv_pow, ge_iff_le] using! this
  have hsum_pow : Summable (fun ℓ : (SchwartzMap.referenceIntegerLattice d) => (‖(ℓ :
    (EuclideanSpace ℝ (Fin d)))‖⁻¹ ^ k : ℝ)) := by
    simpa only [inv_pow, AddSubgroupClass.coe_norm] using!
      (ZLattice.summable_norm_pow_inv (L := (SchwartzMap.referenceIntegerLattice d)) (n := k)
        (Nat.lt_succ_self _))
  have hsum_bd :
      Summable (fun ℓ : (SchwartzMap.referenceIntegerLattice d) => (C * (2 ^ k : ℝ)) * (‖(ℓ :
        (EuclideanSpace ℝ (Fin d)))‖⁻¹ ^ k)) :=
    hsum_pow.mul_left (C * (2 ^ k : ℝ))
  refine Summable.of_norm_bounded_eventually hsum_bd ?_
  filter_upwards [h_event] with ℓ hℓ
  simpa only [SetLike.coe_sort_coe, norm_norm, inv_pow] using! hℓ

private noncomputable def latticePeriodizedMap : C((EuclideanSpace ℝ (Fin d)), ℂ) :=
  ∑' ℓ : (SchwartzMap.referenceIntegerLattice d), latticeTranslatedMap (d := d) f ℓ

private lemma lattice_periodized_map_apply (x : (EuclideanSpace ℝ (Fin d))) :
    latticePeriodizedMap (d := d) f x = ∑' ℓ : (SchwartzMap.referenceIntegerLattice d),
      f (x + (ℓ : (EuclideanSpace ℝ (Fin d)))) := by
  have hsum := ContinuousMap.summable_of_locally_summable_norm
    (summable_restricted_lattice_translate_norms (d := d) f)
  simpa only [latticePeriodizedMap] using! (ContinuousMap.tsum_apply hsum x).symm

@[simp] private lemma lattice_periodization_translation_invariant (x : (EuclideanSpace ℝ (Fin
  d))) (ℓ₀ : (SchwartzMap.referenceIntegerLattice d)) :
    latticePeriodizedMap (d := d) f (x + ℓ₀) = latticePeriodizedMap (d := d) f x := by
  simpa only [lattice_periodized_map_apply (d := d) f, add_assoc, Equiv.coe_addLeft,
    Submodule.coe_add] using!
    (Equiv.addLeft ℓ₀).tsum_eq fun ℓ => f (x + (ℓ : (EuclideanSpace ℝ (Fin d))))

private noncomputable def euclideanTorusProjectionContinuous : C((EuclideanSpace ℝ (Fin d)),
  UnitAddTorus (Fin d)) :=
  ⟨PoissonSummation.Standard.euclideanTorusProjection (d := d),
    PoissonSummation.Standard.continuous_euclidean_torus_projection (d := d)⟩

private lemma continuous_torus_projection_is_quotient : Topology.IsQuotientMap
  (euclideanTorusProjectionContinuous (d := d)) := by
  let h := PoissonSummation.Standard.euclidean_torus_projection_is_open_quotient (d := d)
  simpa only [euclideanTorusProjectionContinuous, ContinuousMap.coe_mk] using! h.isQuotientMap

private lemma lattice_periodization_factors_through_torus :
    Function.FactorsThrough (latticePeriodizedMap (d := d) f)
      (euclideanTorusProjectionContinuous (d := d)) := by
  intro x y hxy
  rcases PoissonSummation.Standard.equal_torus_projections_differ_by_integer_vector (d := d) (x
    := x) (y := y)
      (by simpa only [euclideanTorusProjectionContinuous,
        ContinuousMap.coe_mk] using! hxy) with ⟨n, hn⟩
  have hx : x = y + SchwartzMap.PoissonSummation.Standard.embeddedIntegerVector (d := d) n := by
    simpa only [sub_eq_add_neg, add_comm, add_left_comm, add_neg_cancel,
      add_zero] using! congrArg (fun t => t + y) hn
  simpa only [hx] using!
    (lattice_periodization_translation_invariant (d := d) (f := f) y
      ⟨SchwartzMap.PoissonSummation.Standard.embeddedIntegerVector (d := d) n,
        SchwartzMap.PoissonSummation.Standard.embedded_integer_vector_mem_reference_lattice (d
          := d) n⟩)

private noncomputable def torusDescendedPeriodization : C(UnitAddTorus (Fin d), ℂ) :=
  Topology.IsQuotientMap.lift
    (hf := continuous_torus_projection_is_quotient (d := d))
    (g := latticePeriodizedMap (d := d) f)
    (lattice_periodization_factors_through_torus (d := d) (f := f))

private lemma torus_descended_periodization_comp_projection (x : (EuclideanSpace ℝ (Fin d))) :
    torusDescendedPeriodization (d := d) f (PoissonSummation.Standard.euclideanTorusProjection
      (d := d) x) =
      latticePeriodizedMap (d := d) f x := by
  have hcomp : (torusDescendedPeriodization (d := d) f).comp (euclideanTorusProjectionContinuous
    (d := d)) = latticePeriodizedMap (d := d) f := by
    simp only [torusDescendedPeriodization, Topology.IsQuotientMap.lift_comp]
  simpa only [euclideanTorusProjectionContinuous, ContinuousMap.comp_apply,
    ContinuousMap.coe_mk] using! congrArg (fun g : C((EuclideanSpace ℝ (Fin d)), ℂ) => g x) hcomp

private lemma negative_fourier_character_projection (n : Fin d → ℤ) (x : (EuclideanSpace ℝ (Fin
  d))) :
    UnitAddTorus.mFourier (-n) (PoissonSummation.Standard.euclideanTorusProjection (d := d) x) =
      (𝐞 (-(inner ℝ x (SchwartzMap.PoissonSummation.Standard.embeddedIntegerVector (d := d) n)))
        : ℂ) := by
  simp only [euclideanTorusProjection, fourier_character_coordinate_projection_ofLp, mul_comm,
    Pi.neg_apply,
    Int.cast_neg, neg_mul, Finset.sum_neg_distrib, Complex.ofReal_neg, Complex.ofReal_sum,
      Complex.ofReal_mul,
    Complex.ofReal_intCast, mul_neg, mul_assoc, embeddedIntegerVector, PiLp.inner_apply,
      RCLike.inner_apply,
    Real.ringHom_apply, Real.fourierChar_apply, Complex.ofReal_ofNat]

@[simp] private lemma embedded_integer_vector_neg (n : Fin d → ℤ) :
    SchwartzMap.PoissonSummation.Standard.embeddedIntegerVector (d := d) (-n) =
      -SchwartzMap.PoissonSummation.Standard.embeddedIntegerVector (d := d) n := by
  ext i
  simp only [embedded_integer_vector_coordinate, Pi.neg_apply, Int.cast_neg, PiLp.neg_apply]

private lemma fourier_character_euclidean_projection (n : Fin d → ℤ) (x : (EuclideanSpace ℝ (Fin
  d))) :
    UnitAddTorus.mFourier n (PoissonSummation.Standard.euclideanTorusProjection (d := d) x) =
      (𝐞 (inner ℝ x (SchwartzMap.PoissonSummation.Standard.embeddedIntegerVector (d := d) n)) :
        ℂ) := by
  simpa only [neg_neg, embedded_integer_vector_neg (d := d) (n := n), inner_neg_right] using!
    (negative_fourier_character_projection (d := d) (n := -n) (x := x))

private lemma fourier_character_projection_exponential (n : Fin d → ℤ) (x : (EuclideanSpace ℝ
  (Fin d))) :
    UnitAddTorus.mFourier n (PoissonSummation.Standard.euclideanTorusProjection (d := d) x) =
      Complex.exp
        (2 * Real.pi * Complex.I *
          ⟪x, SchwartzMap.PoissonSummation.Standard.embeddedIntegerVector (d := d) n⟫_[ℝ]) := by
  have hinner :
      inner ℝ x (SchwartzMap.PoissonSummation.Standard.embeddedIntegerVector (d := d) n) =
        RCLike.wInner (𝕜 := ℝ) 1 x.ofLp
          (SchwartzMap.PoissonSummation.Standard.embeddedIntegerVector (d := d) n).ofLp :=
    RCLike.inner_eq_wInner_one x (embeddedIntegerVector n)
  simpa only [mul_comm, mul_assoc, hinner, Real.fourierChar_apply, Complex.ofReal_mul,
    Complex.ofReal_ofNat] using!
    (fourier_character_euclidean_projection (d := d) (n := n) (x := x))

private lemma negative_character_invariant_under_lattice_shift (n : Fin d → ℤ)
    (ℓ : (SchwartzMap.referenceIntegerLattice d)) (x : (EuclideanSpace ℝ (Fin d))) :
    UnitAddTorus.mFourier (-n) (PoissonSummation.Standard.euclideanTorusProjection (d := d) (x +
      (ℓ : (EuclideanSpace ℝ (Fin d))))) =
      UnitAddTorus.mFourier (-n) (PoissonSummation.Standard.euclideanTorusProjection (d := d) x)
        := by
  rcases
      PoissonSummation.Standard.reference_lattice_element_eq_integer_vector (d := d) (x := (ℓ :
        (EuclideanSpace ℝ (Fin d))))
        ℓ.property with ⟨m, hm⟩
  simp only [hm, torus_projection_add_integer_vector]

private lemma half_open_unit_cell_subset_closed_ball :
    SchwartzMap.PoissonSummation.Standard.halfOpenUnitCell (d := d) ⊆
      Metric.closedBall (0 : (EuclideanSpace ℝ (Fin d))) (Real.sqrt d) := by
  intro x hx
  have hsum : (∑ i : Fin d, ‖x i‖ ^ 2) ≤ (d : ℝ) := by
    have hterm : ∀ i : Fin d, ‖x i‖ ^ 2 ≤ (1 : ℝ) := by
      intro i
      have hi : x i ∈ Set.Ioc (0 : ℝ) 1 := hx i
      have hxle : ‖x i‖ ≤ (1 : ℝ) := by
        have hxnonneg : 0 ≤ x i := le_of_lt hi.1
        simpa only [Real.norm_eq_abs, abs_of_nonneg hxnonneg, ge_iff_le] using! hi.2
      simpa only [Real.norm_eq_abs, pow_two, abs_mul_abs_self, ge_iff_le,
        mul_one] using! mul_le_mul hxle hxle (norm_nonneg _) (by positivity)
    simpa only [Real.norm_eq_abs, sq_abs,
      ge_iff_le] using! (Finset.sum_le_sum fun i _ => hterm i).trans_eq (by simp only
      [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one])
  simpa only [Metric.mem_closedBall, dist_eq_norm, sub_zero, EuclideanSpace.norm_eq,
    Real.norm_eq_abs, sq_abs,
    Nat.cast_nonneg, Real.sqrt_le_sqrt_iff, ge_iff_le] using! (Real.sqrt_le_sqrt hsum)

private lemma half_open_unit_cell_volume_finite :
    (volume : Measure (EuclideanSpace ℝ (Fin d)))
      (SchwartzMap.PoissonSummation.Standard.halfOpenUnitCell (d := d)) < ⊤ := by
  simpa only  using! ((Metric.isBounded_closedBall (x := (0 : (EuclideanSpace ℝ (Fin d)))) (r :=
    Real.sqrt d)).subset
    (half_open_unit_cell_subset_closed_ball (d := d))).measure_lt_top

private lemma fourier_character_translate_integrable_on_cell (n : Fin d → ℤ)
    (ℓ : (SchwartzMap.referenceIntegerLattice d)) :
    IntegrableOn
        (fun x : (EuclideanSpace ℝ (Fin d)) =>
          UnitAddTorus.mFourier (-n) (PoissonSummation.Standard.euclideanTorusProjection (d :=
            d) x) *
            f (x + (ℓ : (EuclideanSpace ℝ (Fin d)))))
        (SchwartzMap.PoissonSummation.Standard.halfOpenUnitCell (d := d)) (volume : Measure
          (EuclideanSpace ℝ (Fin d))) := by
  let K : TopologicalSpace.Compacts (EuclideanSpace ℝ (Fin d)) :=
    ⟨Metric.closedBall (0 : (EuclideanSpace ℝ (Fin d))) (Real.sqrt d),
      isCompact_closedBall (0 : (EuclideanSpace ℝ (Fin d))) (Real.sqrt d)⟩
  have hK : SchwartzMap.PoissonSummation.Standard.halfOpenUnitCell (d := d) ⊆ (K : Set
    (EuclideanSpace ℝ (Fin d))) :=
    (half_open_unit_cell_subset_closed_ball (d := d))
  have hbound :
      ∀ x ∈ SchwartzMap.PoissonSummation.Standard.halfOpenUnitCell (d := d),
        ‖UnitAddTorus.mFourier (-n) (PoissonSummation.Standard.euclideanTorusProjection (d := d)
          x) *
            f (x + (ℓ : (EuclideanSpace ℝ (Fin d))))‖ ≤ ‖(latticeTranslatedMap (d := d) f
              ℓ).restrict K‖ := by
    intro x hx
    have hxK : x ∈ (K : Set (EuclideanSpace ℝ (Fin d))) := hK hx
    have hmFourier :
        ‖UnitAddTorus.mFourier (-n) (PoissonSummation.Standard.euclideanTorusProjection (d := d)
          x)‖ ≤ 1 := by
      simpa only [UnitAddTorus.mFourier_norm (d := Fin d) (n := -n)] using!
        (ContinuousMap.norm_coe_le_norm (UnitAddTorus.mFourier (-n))
          (PoissonSummation.Standard.euclideanTorusProjection (d := d) x))
    have hsup :
        ‖f (x + (ℓ : (EuclideanSpace ℝ (Fin d))))‖ ≤ ‖(latticeTranslatedMap (d := d) f
          ℓ).restrict K‖ := by
      simpa only [SetLike.coe_sort_coe] using!
        (ContinuousMap.norm_coe_le_norm ((latticeTranslatedMap (d := d) f ℓ).restrict K) ⟨x, hxK⟩)
    calc
      ‖UnitAddTorus.mFourier (-n) (PoissonSummation.Standard.euclideanTorusProjection (d := d) x) *
            f (x + (ℓ : (EuclideanSpace ℝ (Fin d))))‖
          = ‖UnitAddTorus.mFourier (-n) (PoissonSummation.Standard.euclideanTorusProjection (d
            := d) x)‖ *
              ‖f (x + (ℓ : (EuclideanSpace ℝ (Fin d))))‖ := by simp only [Complex.norm_mul]
      _ ≤ 1 * ‖f (x + (ℓ : (EuclideanSpace ℝ (Fin d))))‖ := by gcongr
      _ = ‖f (x + (ℓ : (EuclideanSpace ℝ (Fin d))))‖ := by simp only [one_mul]
      _ ≤ ‖(latticeTranslatedMap (d := d) f ℓ).restrict K‖ := hsup
  refine Measure.integrableOn_of_bounded (μ := (volume : Measure (EuclideanSpace ℝ (Fin d))))
      (s := SchwartzMap.PoissonSummation.Standard.halfOpenUnitCell (d := d))
      (s_finite := (half_open_unit_cell_volume_finite (d := d)).ne)
      ?_
      (M := ‖(latticeTranslatedMap (d := d) f ℓ).restrict K‖)
      ?_
  · exact
      (((UnitAddTorus.mFourier (-n)).continuous.comp
            (PoissonSummation.Standard.continuous_euclidean_torus_projection (d := d))).mul
          (f.continuous.comp (continuous_id.add continuous_const))).aestronglyMeasurable
  · exact ae_restrict_of_forall_mem
      (SchwartzMap.PoissonSummation.Standard.half_open_unit_cell_measurable (d := d)) hbound

end SchwartzMap.PoissonSummation.Standard

namespace SchwartzMap.PoissonSummation.Standard

variable {d : ℕ}

open _root_.SchwartzMap.UnitAddTorus

variable (f : 𝓢(EuclideanSpace ℝ (Fin d), ℂ))

private noncomputable def ball : TopologicalSpace.Compacts (EuclideanSpace ℝ (Fin d)) :=
  ⟨Metric.closedBall (0 : (EuclideanSpace ℝ (Fin d))) (Real.sqrt d),
    isCompact_closedBall (0 : (EuclideanSpace ℝ (Fin d))) (Real.sqrt d)⟩

private lemma fourier_weighted_translate_norm_bound (n : Fin d → ℤ) (ℓ :
  (SchwartzMap.referenceIntegerLattice d))
    (x : (EuclideanSpace ℝ (Fin d))) (hx : x ∈
      SchwartzMap.PoissonSummation.Standard.halfOpenUnitCell (d := d)) :
    ‖UnitAddTorus.mFourier (-n) (PoissonSummation.Standard.euclideanTorusProjection (d := d) x) *
          f (x + (ℓ : (EuclideanSpace ℝ (Fin d))))‖ ≤ ‖(latticeTranslatedMap (d := d) f
            ℓ).restrict (ball (d := d))‖ := by
  have hxK : x ∈ (ball (d := d) : Set (EuclideanSpace ℝ (Fin d))) :=
    (half_open_unit_cell_subset_closed_ball (d := d)) hx
  have hmFourier :
      ‖UnitAddTorus.mFourier (-n) (PoissonSummation.Standard.euclideanTorusProjection (d := d)
        x)‖ ≤ 1 := by
    simpa only [UnitAddTorus.mFourier_norm (d := Fin d) (n := -n)] using!
      (ContinuousMap.norm_coe_le_norm (UnitAddTorus.mFourier (-n))
        (PoissonSummation.Standard.euclideanTorusProjection (d := d) x))
  have hsup :
      ‖f (x + (ℓ : (EuclideanSpace ℝ (Fin d))))‖ ≤ ‖(latticeTranslatedMap (d := d) f ℓ).restrict
        (ball (d := d))‖ := by
    simpa only [SetLike.coe_sort_coe] using!
      (ContinuousMap.norm_coe_le_norm ((latticeTranslatedMap (d := d) f ℓ).restrict (ball (d :=
        d))) ⟨x, hxK⟩)
  calc
    ‖UnitAddTorus.mFourier (-n) (PoissonSummation.Standard.euclideanTorusProjection (d := d) x) *
          f (x + (ℓ : (EuclideanSpace ℝ (Fin d))))‖
        = ‖UnitAddTorus.mFourier (-n) (PoissonSummation.Standard.euclideanTorusProjection (d :=
          d) x)‖ *
            ‖f (x + (ℓ : (EuclideanSpace ℝ (Fin d))))‖ := by simp only [Complex.norm_mul]
    _ ≤ 1 * ‖f (x + (ℓ : (EuclideanSpace ℝ (Fin d))))‖ := by gcongr
    _ = ‖f (x + (ℓ : (EuclideanSpace ℝ (Fin d))))‖ := by simp only [one_mul]
    _ ≤ ‖(latticeTranslatedMap (d := d) f ℓ).restrict (ball (d := d))‖ := hsup

private lemma summable_cell_integrals_of_weighted_translates (n : Fin d → ℤ) :
    Summable
        (fun ℓ : (SchwartzMap.referenceIntegerLattice d) =>
          ∫ x in SchwartzMap.PoissonSummation.Standard.halfOpenUnitCell (d := d),
            ‖UnitAddTorus.mFourier (-n) (PoissonSummation.Standard.euclideanTorusProjection (d
              := d) x) *
                f (x + (ℓ : (EuclideanSpace ℝ (Fin d))))‖ ∂(volume : Measure (EuclideanSpace ℝ
                  (Fin d)))) := by
  let s : Set (EuclideanSpace ℝ (Fin d)) :=
    SchwartzMap.PoissonSummation.Standard.halfOpenUnitCell (d := d)
  let μ : Measure (EuclideanSpace ℝ (Fin d)) := (volume : Measure (EuclideanSpace ℝ (Fin
    d))).restrict s
  have : IsFiniteMeasure μ := by
    refine ⟨?_⟩
    simpa only [MeasurableSet.univ, Measure.restrict_apply, Set.univ_inter, μ,
      s] using! (half_open_unit_cell_volume_finite (d := d))
  have hsum_norm :
      Summable (fun ℓ : (SchwartzMap.referenceIntegerLattice d) =>
        μ.real Set.univ * ‖(latticeTranslatedMap (d := d) f ℓ).restrict (ball (d := d))‖) := by
    simpa only [SetLike.coe_sort_coe, mul_comm] using!
      (summable_restricted_lattice_translate_norms (d := d) f (ball (d := d))).mul_left (μ.real
        Set.univ)
  refine Summable.of_nonneg_of_le (fun _ => by positivity) (fun ℓ => ?_) hsum_norm
  have hle_ae :
      (fun x : (EuclideanSpace ℝ (Fin d)) =>
        ‖UnitAddTorus.mFourier (-n) (PoissonSummation.Standard.euclideanTorusProjection (d := d)
          x) *
              f (x + (ℓ : (EuclideanSpace ℝ (Fin d))))‖) ≤ᵐ[μ] fun _ : (EuclideanSpace ℝ (Fin d)) =>
        ‖(latticeTranslatedMap (d := d) f ℓ).restrict (ball (d := d))‖ := by
    refine ae_restrict_of_forall_mem
      (SchwartzMap.PoissonSummation.Standard.half_open_unit_cell_measurable (d := d)) ?_
    intro x hx
    exact fourier_weighted_translate_norm_bound (d := d) (f := f) n ℓ x hx
  have hnonneg :
      (0 : (EuclideanSpace ℝ (Fin d)) → ℝ) ≤ᵐ[μ] fun x : (EuclideanSpace ℝ (Fin d)) =>
        ‖UnitAddTorus.mFourier (-n) (PoissonSummation.Standard.euclideanTorusProjection (d := d)
          x) *
              f (x + (ℓ : (EuclideanSpace ℝ (Fin d))))‖ :=
    ae_of_all _ (fun _ => by positivity)
  have hle' :
      (∫ x, ‖UnitAddTorus.mFourier (-n) (PoissonSummation.Standard.euclideanTorusProjection (d
        := d) x) *
              f (x + (ℓ : (EuclideanSpace ℝ (Fin d))))‖ ∂μ) ≤
        μ.real Set.univ * ‖(latticeTranslatedMap (d := d) f ℓ).restrict (ball (d := d))‖ := by
    have hle :
        (∫ x, ‖UnitAddTorus.mFourier (-n) (PoissonSummation.Standard.euclideanTorusProjection (d
          := d) x) *
                f (x + (ℓ : (EuclideanSpace ℝ (Fin d))))‖ ∂μ) ≤
          ∫ x, ‖(latticeTranslatedMap (d := d) f ℓ).restrict (ball (d := d))‖ ∂μ :=
      integral_mono_of_nonneg hnonneg
        (integrable_const ‖(latticeTranslatedMap (d := d) f ℓ).restrict (ball (d := d))‖) hle_ae
    simpa only [Complex.norm_mul, SetLike.coe_sort_coe, mul_comm, ge_iff_le,
      MeasureTheory.integral_const (μ := μ), smul_eq_mul] using! hle
  simpa only [Complex.norm_mul, MeasurableSet.univ, measureReal_restrict_apply, Set.univ_inter,
    SetLike.coe_sort_coe, mul_comm, ge_iff_le] using! hle'

private lemma fourier_coefficient_torus_periodization (n : Fin d → ℤ) :
    UnitAddTorus.mFourierCoeff (torusDescendedPeriodization (d := d) f) n =
      𝓕 (fun x : (EuclideanSpace ℝ (Fin d)) => f x)
        (SchwartzMap.PoissonSummation.Standard.embeddedIntegerVector (d := d) n) := by
  let χ : (EuclideanSpace ℝ (Fin d)) → ℂ := fun x =>
    UnitAddTorus.mFourier (-n)
      (PoissonSummation.Standard.euclideanTorusProjection (d := d) x)
  let G : (EuclideanSpace ℝ (Fin d)) → ℂ := fun x => χ x * f x
  have hχ_cont : Continuous χ :=
    (UnitAddTorus.mFourier (-n)).continuous.comp
      (PoissonSummation.Standard.continuous_euclidean_torus_projection (d := d))
  have hχ_norm (x : EuclideanSpace ℝ (Fin d)) : ‖χ x‖ ≤ 1 := by
    simpa only [UnitAddTorus.mFourier_norm (d := Fin d) (n := -n)] using!
      (ContinuousMap.norm_coe_le_norm (UnitAddTorus.mFourier (-n))
        (PoissonSummation.Standard.euclideanTorusProjection (d := d) x))
  have hG_int : Integrable G (volume : Measure (EuclideanSpace ℝ (Fin d))) := by
    refine f.integrable.norm.mono' (hχ_cont.mul f.continuous).aestronglyMeasurable ?_
    filter_upwards [] with x
    change ‖χ x * f x‖ ≤ ‖f x‖
    calc
      ‖χ x * f x‖ = ‖χ x‖ * ‖f x‖ := norm_mul _ _
      _ ≤ 1 * ‖f x‖ := by gcongr; exact hχ_norm x
      _ = ‖f x‖ := one_mul _
  have hχ_shift (ℓ : SchwartzMap.referenceIntegerLattice d)
      (x : EuclideanSpace ℝ (Fin d)) : χ (x + (ℓ : EuclideanSpace ℝ (Fin d))) = χ x :=
    negative_character_invariant_under_lattice_shift (d := d) n ℓ x
  have htranslate (ℓ : SchwartzMap.referenceIntegerLattice d) :
      (∫ x in
        (fun y : EuclideanSpace ℝ (Fin d) =>
          (ℓ : EuclideanSpace ℝ (Fin d)) + y) ''
          SchwartzMap.PoissonSummation.Standard.halfOpenUnitCell (d := d), G x) =
        ∫ x in SchwartzMap.PoissonSummation.Standard.halfOpenUnitCell (d := d),
          χ x * f (x + (ℓ : EuclideanSpace ℝ (Fin d))) := by
    let s : Set (EuclideanSpace ℝ (Fin d)) :=
      SchwartzMap.PoissonSummation.Standard.halfOpenUnitCell (d := d)
    let t : Set (EuclideanSpace ℝ (Fin d)) :=
      (fun y : EuclideanSpace ℝ (Fin d) =>
        (ℓ : EuclideanSpace ℝ (Fin d)) + y) '' s
    have hs : MeasurableSet s :=
      SchwartzMap.PoissonSummation.Standard.half_open_unit_cell_measurable (d := d)
    have hls : MeasurableSet t := by
      have hpre :
          t = (fun x : EuclideanSpace ℝ (Fin d) =>
            -(ℓ : EuclideanSpace ℝ (Fin d)) + x) ⁻¹' s := by
        ext x
        simp only [Set.image_add_left, Set.mem_preimage, t]
      rw [hpre]
      exact (continuous_const.add continuous_id).measurable hs
    have hmem (x : EuclideanSpace ℝ (Fin d)) :
        ((ℓ : EuclideanSpace ℝ (Fin d)) + x ∈ t) ↔ x ∈ s := by
      simp only [Set.image_add_left, Set.mem_preimage, neg_add_cancel_left, t]
    calc
      (∫ x in t, G x) = ∫ x, t.indicator G x :=
        (integral_indicator hls).symm
      _ = ∫ x, t.indicator G ((ℓ : EuclideanSpace ℝ (Fin d)) + x) :=
        (integral_add_left_eq_self (t.indicator G)
          (ℓ : EuclideanSpace ℝ (Fin d))).symm
      _ = ∫ x, s.indicator
          (fun x : EuclideanSpace ℝ (Fin d) => G ((ℓ : EuclideanSpace ℝ (Fin d)) + x)) x := by
        apply integral_congr_ae
        filter_upwards [] with x
        by_cases hx : x ∈ s
        · simp only [(hmem x).2 hx, Set.indicator_of_mem, hx]
        · simp only [mt (hmem x).1 hx, not_false_eq_true, Set.indicator_of_notMem, hx]
      _ = ∫ x in s, G ((ℓ : EuclideanSpace ℝ (Fin d)) + x) := integral_indicator hs
      _ = ∫ x in s, χ x * f (x + (ℓ : EuclideanSpace ℝ (Fin d))) := by
        apply integral_congr_ae
        filter_upwards [] with x
        simp only [add_comm, hχ_shift, G]
  have hglobal :
      (∫ x : EuclideanSpace ℝ (Fin d), G x) =
        ∑' ℓ : SchwartzMap.referenceIntegerLattice d,
          ∫ x in SchwartzMap.PoissonSummation.Standard.halfOpenUnitCell (d := d),
            χ x * f (x + (ℓ : EuclideanSpace ℝ (Fin d))) := by
    rw [(half_open_cell_is_fundamental_region (d := d)).integral_eq_tsum G hG_int]
    apply tsum_congr
    intro ℓ
    change (∫ x in
      (fun y : EuclideanSpace ℝ (Fin d) =>
        (ℓ : EuclideanSpace ℝ (Fin d)) + y) ''
        SchwartzMap.PoissonSummation.Standard.halfOpenUnitCell (d := d), G x) = _
    exact htranslate ℓ
  calc
    UnitAddTorus.mFourierCoeff (torusDescendedPeriodization (d := d) f) n =
        ∫ y : UnitAddTorus (Fin d),
          UnitAddTorus.mFourier (-n) y * torusDescendedPeriodization (d := d) f y := by
      rw [UnitAddTorus.mFourierCoeff_eq_integral
        (torusDescendedPeriodization (d := d) f) n (fun _ => 0)]
      have hset :
          {x : Fin d → ℝ | ∀ i, x i ∈ Set.Ioc (0 : ℝ) (0 + 1)} =
            Set.univ.pi (fun _ : Fin d => Set.Ioc (0 : ℝ) (0 + 1)) := by
        ext x
        simp only [zero_add, Set.mem_Ioc, Set.mem_ofPred_eq, Set.mem_pi, Set.mem_univ, forall_const]
      rw [hset]
      simpa only [zero_add, smul_eq_mul] using!
        (UnitAddTorus.torus_integral_eq_coordinate_cell_integral (n := d) (t := 0)
          (fun y : UnitAddTorus (Fin d) =>
            UnitAddTorus.mFourier (-n) y * torusDescendedPeriodization (d := d) f y)
          (((UnitAddTorus.mFourier (-n)).continuous.mul
            (torusDescendedPeriodization (d := d) f).continuous).aestronglyMeasurable)).symm
    _ = ∫ x in SchwartzMap.PoissonSummation.Standard.halfOpenUnitCell (d := d),
          χ x * latticePeriodizedMap (d := d) f x := by
      rw [torus_integral_eq_euclidean_cell_integral
        (fun y : UnitAddTorus (Fin d) =>
          UnitAddTorus.mFourier (-n) y * torusDescendedPeriodization (d := d) f y)
        (((UnitAddTorus.mFourier (-n)).continuous.mul
          (torusDescendedPeriodization (d := d) f).continuous).aestronglyMeasurable)]
      apply integral_congr_ae
      filter_upwards [] with x
      simp only [torus_descended_periodization_comp_projection, χ]
    _ = ∫ x in SchwartzMap.PoissonSummation.Standard.halfOpenUnitCell (d := d),
          ∑' ℓ : SchwartzMap.referenceIntegerLattice d,
            χ x * f (x + (ℓ : EuclideanSpace ℝ (Fin d))) := by
      apply integral_congr_ae
      filter_upwards [] with x
      rw [lattice_periodized_map_apply]
      exact tsum_mul_left.symm
    _ = ∑' ℓ : SchwartzMap.referenceIntegerLattice d,
          ∫ x in SchwartzMap.PoissonSummation.Standard.halfOpenUnitCell (d := d),
            χ x * f (x + (ℓ : EuclideanSpace ℝ (Fin d))) := by
      exact (integral_tsum_of_summable_integral_norm
        (fun ℓ => fourier_character_translate_integrable_on_cell (d := d) f n ℓ)
        (summable_cell_integrals_of_weighted_translates (d := d) f n)).symm
    _ = ∫ x : EuclideanSpace ℝ (Fin d), G x := hglobal.symm
    _ = 𝓕 (fun x : EuclideanSpace ℝ (Fin d) => f x)
          (SchwartzMap.PoissonSummation.Standard.embeddedIntegerVector (d := d) n) := by
      rw [Real.fourier_eq']
      apply integral_congr_ae
      filter_upwards [] with x
      simp only [G, χ, negative_fourier_character_projection,
        Real.fourierChar_apply, smul_eq_mul]
      congr 1
      push_cast
      ring_nf

private lemma summable_fourier_coefficients_torus_periodization :
    Summable (UnitAddTorus.mFourierCoeff (torusDescendedPeriodization (d := d) f)) := by
  have hsum_norm :
      Summable (fun n : Fin d → ℤ =>
        ‖𝓕 (fun x : (EuclideanSpace ℝ (Fin d)) => f x)
          (SchwartzMap.PoissonSummation.Standard.embeddedIntegerVector (d := d) n)‖) := by
    let k : ℕ := d + 1
    have hk : Module.finrank ℤ (SchwartzMap.referenceIntegerLattice d) < k := by
      have hrank : Module.finrank ℤ (SchwartzMap.referenceIntegerLattice d) = d := by
        have h := (ZLattice.rank (K := ℝ) (L := (SchwartzMap.referenceIntegerLattice d)))
        simpa only  using! (h.trans (by simp only [finrank_euclideanSpace, Fintype.card_fin]))
      simp only [hrank, lt_add_iff_pos_right, Order.lt_one_iff, k]
    obtain ⟨C, hCpos, hC⟩ := (FourierTransform.fourierCLE ℂ (SchwartzMap (EuclideanSpace ℝ (Fin
      d)) ℂ) f).decay k 0
    have hC' : ∀ x : (EuclideanSpace ℝ (Fin d)),
      ‖x‖ ^ k * ‖𝓕 (fun y : (EuclideanSpace ℝ (Fin d)) => f y) x‖ ≤ C := by
      simpa only [FourierTransform.fourierCLE_apply, fourier_coe,
        norm_iteratedFDeriv_zero] using! hC
    have hsum_pow :
        Summable (fun ℓ : (SchwartzMap.referenceIntegerLattice d) => (‖(ℓ : (EuclideanSpace ℝ
          (Fin d)))‖⁻¹ ^ k : ℝ)) := by
      simpa only [inv_pow, AddSubgroupClass.coe_norm] using! (ZLattice.summable_norm_pow_inv (L
        := (SchwartzMap.referenceIntegerLattice d)) (n := k) hk)
    have hsum_bd : Summable (fun ℓ : (SchwartzMap.referenceIntegerLattice d) => (C : ℝ) * (‖(ℓ :
      (EuclideanSpace ℝ (Fin d)))‖⁻¹ ^ k)) :=
      hsum_pow.mul_left C
    have hsum_lattice : Summable (fun ℓ : (SchwartzMap.referenceIntegerLattice d) => ‖𝓕 (fun y :
      (EuclideanSpace ℝ (Fin d)) => f y) (ℓ : (EuclideanSpace ℝ (Fin d)))‖) := by
      have hfin : ({ℓ : (SchwartzMap.referenceIntegerLattice d) | ‖(ℓ : (EuclideanSpace ℝ (Fin
        d)))‖ ≤ (1 : ℝ)} : Set _).Finite :=
        finite_reference_lattice_points_of_norm_bound (d := d) 1
      refine Summable.of_norm_bounded_eventually hsum_bd ?_
      filter_upwards [hfin.compl_mem_cofinite] with ℓ hℓ
      have hnorm_gt : (1 : ℝ) < ‖(ℓ : (EuclideanSpace ℝ (Fin d)))‖ := lt_of_not_ge (by simpa
        only [not_le, Set.mem_compl_iff, Set.mem_ofPred_eq] using! hℓ)
      have hnorm_pos : 0 < ‖(ℓ : (EuclideanSpace ℝ (Fin d)))‖ := lt_trans (by positivity) hnorm_gt
      have hpow_pos : 0 < ‖(ℓ : (EuclideanSpace ℝ (Fin d)))‖ ^ k := pow_pos hnorm_pos _
      have hmain := hC' (ℓ : (EuclideanSpace ℝ (Fin d)))
      have : ‖𝓕 (fun y : (EuclideanSpace ℝ (Fin d)) => f y) (ℓ : (EuclideanSpace ℝ (Fin d)))‖ ≤
        C / (‖(ℓ : (EuclideanSpace ℝ (Fin d)))‖ ^ k) :=
        (le_div_iff₀' hpow_pos).2 hmain
      have hdiv :
          ‖𝓕 (fun y : (EuclideanSpace ℝ (Fin d)) => f y) (ℓ : (EuclideanSpace ℝ (Fin d)))‖ ≤ (C
            : ℝ) * (‖(ℓ : (EuclideanSpace ℝ (Fin d)))‖⁻¹ ^ k) := by
        simpa only [inv_pow, div_eq_mul_inv] using! this
      simpa only [norm_norm, inv_pow, ge_iff_le] using! hdiv
    let e := (PoissonSummation.Standard.integerVectorLatticeEquiv (d := d))
    have : Summable (fun n : Fin d → ℤ => ‖𝓕 (fun y : (EuclideanSpace ℝ (Fin d)) => f y) ((e n :
      (SchwartzMap.referenceIntegerLattice d)) : (EuclideanSpace ℝ (Fin d)))‖) := by
      simpa only  using! (Summable.comp_injective hsum_lattice e.injective)
    simpa only  using! this
  refine (Summable.of_norm ?_)
  simpa only [fourier_coefficient_torus_periodization (d := d) (f := f)] using! hsum_norm

private theorem reference_lattice_poisson_formula (v : (EuclideanSpace ℝ (Fin d))) :
    (∑' ℓ : (SchwartzMap.referenceIntegerLattice d), f (v + (ℓ : (EuclideanSpace ℝ (Fin d))))) =
      ∑' n : Fin d → ℤ,
        (𝓕 (fun x : (EuclideanSpace ℝ (Fin d)) => f x)
          (SchwartzMap.PoissonSummation.Standard.embeddedIntegerVector (d := d) n)) *
          Complex.exp
            (2 * Real.pi * Complex.I *
              ⟪v, SchwartzMap.PoissonSummation.Standard.embeddedIntegerVector (d := d) n⟫_[ℝ]) := by
  simpa only [mul_comm, mul_assoc,
    torus_descended_periodization_comp_projection (d := d) (f := f) v,
    lattice_periodized_map_apply (d := d) (f := f),
      fourier_coefficient_torus_periodization (d := d) (f := f),
    fourier_character_projection_exponential (d := d), smul_eq_mul] using!
    (UnitAddTorus.hasSum_mFourier_series_apply_of_summable
        (f := torusDescendedPeriodization (d := d) f)
        (summable_fourier_coefficients_torus_periodization (d := d) (f := f))
        (euclideanTorusProjection (d := d) v)).tsum_eq.symm

end SchwartzMap.PoissonSummation.Standard

end

section

open scoped BigOperators FourierTransform Real

open MeasureTheory Module

namespace SchwartzMap

variable {d : ℕ}

private noncomputable abbrev polarIntegerLattice (L : Submodule ℤ (EuclideanSpace ℝ (Fin d))) :
  Submodule ℤ (EuclideanSpace ℝ (Fin d)) :=
  LinearMap.BilinForm.dualSubmodule (B := (innerₗ (EuclideanSpace ℝ (Fin d)) :
    LinearMap.BilinForm ℝ (EuclideanSpace ℝ (Fin d)))) L

private noncomputable def integralLatticeCoordinateBasis (L : Submodule ℤ (EuclideanSpace ℝ (Fin
  d))) [DiscreteTopology L] [IsZLattice ℝ L] :
    Basis (Fin d) ℤ L := by
  haveI : Module.Free ℤ L := by infer_instance
  haveI : Module.Finite ℤ L := ZLattice.module_finite ℝ L
  let b₀ := Module.Free.chooseBasis ℤ L
  have hfinrank : Module.finrank ℤ L = d := by
    have hE : Module.finrank ℝ (EuclideanSpace ℝ (Fin d)) = d := by
      simp only [finrank_euclideanSpace, Fintype.card_fin]
    exact (ZLattice.rank (K := ℝ) (L := L)).trans hE
  let e : Module.Free.ChooseBasisIndex ℤ L ≃ Fin d :=
    Fintype.equivOfCardEq (by
      simpa only [Fintype.card_fin, hfinrank] using!
        (Module.finrank_eq_card_chooseBasisIndex (R := ℤ) (M := L)).symm)
  exact b₀.reindex e

private noncomputable def realLatticeCoordinateBasis (L : Submodule ℤ (EuclideanSpace ℝ (Fin
  d))) [DiscreteTopology L] [IsZLattice ℝ L] :
    Basis (Fin d) ℝ (EuclideanSpace ℝ (Fin d)) :=
  (integralLatticeCoordinateBasis (d := d) L).ofZLatticeBasis ℝ L

private noncomputable def referenceEuclideanBasis : Basis (Fin d) ℝ (EuclideanSpace ℝ (Fin d)) :=
  (EuclideanSpace.basisFun (Fin d) ℝ).toBasis

private noncomputable def latticeCoordinateEquiv (L : Submodule ℤ (EuclideanSpace ℝ (Fin d)))
  [DiscreteTopology L] [IsZLattice ℝ L] :
    (EuclideanSpace ℝ (Fin d)) ≃ₗ[ℝ] (EuclideanSpace ℝ (Fin d)) :=
  (referenceEuclideanBasis (d := d)).equiv (realLatticeCoordinateBasis (d := d) L) (Equiv.refl
    (Fin d))

@[simp] private lemma lattice_coordinate_equiv_apply_reference_basis (L : Submodule ℤ
  (EuclideanSpace ℝ (Fin d))) [DiscreteTopology L] [IsZLattice ℝ L]
    (i : Fin d) : (latticeCoordinateEquiv (d := d) L) ((referenceEuclideanBasis (d := d)) i) =
      (realLatticeCoordinateBasis (d := d) L) i := by
  simpa only [latticeCoordinateEquiv, referenceEuclideanBasis, realLatticeCoordinateBasis,
    OrthonormalBasis.coe_toBasis, EuclideanSpace.basisFun_apply, Basis.ofZLatticeBasis_apply,
      Equiv.refl_apply] using!
    (Basis.equiv_apply (b := referenceEuclideanBasis (d := d)) (b' := realLatticeCoordinateBasis
      (d := d) L) (e := Equiv.refl _)
      (i := i))

private lemma coordinate_transport_maps_reference_lattice (L : Submodule ℤ (EuclideanSpace ℝ
  (Fin d))) [DiscreteTopology L] [IsZLattice ℝ L] :
    Submodule.map ((latticeCoordinateEquiv (d := d) L).toLinearMap.restrictScalars ℤ)
        (SchwartzMap.referenceIntegerLattice d) = L := by
  have hspan : Submodule.span ℤ (Set.range (realLatticeCoordinateBasis (d := d) L)) = L := by
    simpa only [realLatticeCoordinateBasis] using!
      (Module.Basis.ofZLatticeBasis_span (K := ℝ) (L := L) (b := integralLatticeCoordinateBasis
        (d := d) L))
  have himage :
      (fun a : (EuclideanSpace ℝ (Fin d)) => (latticeCoordinateEquiv (d := d) L) a) ''
        (Set.range (referenceEuclideanBasis (d := d))) =
        Set.range (realLatticeCoordinateBasis (d := d) L) := by
    have hfun : (fun a : (EuclideanSpace ℝ (Fin d)) => (latticeCoordinateEquiv (d := d) L) a) ∘
      referenceEuclideanBasis (d := d) = realLatticeCoordinateBasis (d := d) L := by
      funext i
      simp only [Function.comp, lattice_coordinate_equiv_apply_reference_basis]
    simpa only [hfun] using!
      (Set.range_comp (g := fun a : (EuclideanSpace ℝ (Fin d)) => (latticeCoordinateEquiv (d :=
        d) L) a) (f := referenceEuclideanBasis (d := d))).symm
  calc
    Submodule.map ((latticeCoordinateEquiv (d := d) L).toLinearMap.restrictScalars ℤ)
      (SchwartzMap.referenceIntegerLattice d) =
        Submodule.span ℤ ((fun a : (EuclideanSpace ℝ (Fin d)) => (latticeCoordinateEquiv (d :=
          d) L) a) '' Set.range (referenceEuclideanBasis (d := d))) := by
          simp only [referenceIntegerLattice, OrthonormalBasis.coe_toBasis, Submodule.map_span,
            LinearMap.coe_restrictScalars, LinearEquiv.coe_coe, referenceEuclideanBasis]
    _ = Submodule.span ℤ (Set.range (realLatticeCoordinateBasis (d := d) L)) := by simp only
      [himage]
    _ = L := by simp only [hspan]

section FundamentalDomain

private lemma reference_basis_fundamental_region_volume :
    (volume : Measure (EuclideanSpace ℝ (Fin d))).real
        (ZSpan.fundamentalDomain ((EuclideanSpace.basisFun (Fin d) ℝ).toBasis)) = 1 := by
  have hdomain :
      ZSpan.fundamentalDomain ((EuclideanSpace.basisFun (Fin d) ℝ).toBasis) =
        axisAlignedCell (d := d) 1 := by
    ext x
    simp only [ZSpan.mem_fundamentalDomain, OrthonormalBasis.coe_toBasis_repr_apply,
      EuclideanSpace.basisFun_repr,
      Set.mem_Ico, axisAlignedCell, Set.mem_ofPred_eq]
  rw [Measure.real, hdomain, PeriodicConstant.axis_cell_volume_formula]
  norm_num

end FundamentalDomain

section CovolumeDet

variable (L : Submodule ℤ (EuclideanSpace ℝ (Fin d))) [DiscreteTopology L] [IsZLattice ℝ L]

private lemma lattice_covolume_eq_coordinate_determinant :
    ZLattice.covolume L =
      abs ((LinearMap.det : ((EuclideanSpace ℝ (Fin d)) →ₗ[ℝ] (EuclideanSpace ℝ (Fin d))) →* ℝ)
        ((latticeCoordinateEquiv L).toLinearMap)) := by
  let bZ : Basis (Fin d) ℤ L := integralLatticeCoordinateBasis L
  have hdet :
      (referenceEuclideanBasis (d := d)).det (fun i : Fin d => (bZ i : (EuclideanSpace ℝ (Fin
        d)))) =
        (LinearMap.det : ((EuclideanSpace ℝ (Fin d)) →ₗ[ℝ] (EuclideanSpace ℝ (Fin d))) →* ℝ)
          ((latticeCoordinateEquiv L).toLinearMap) := by
    have hdetA :
        (LinearMap.det : ((EuclideanSpace ℝ (Fin d)) →ₗ[ℝ] (EuclideanSpace ℝ (Fin d))) →* ℝ)
          ((latticeCoordinateEquiv L).toLinearMap) =
          (referenceEuclideanBasis (d := d)).det (realLatticeCoordinateBasis (d := d) L) := by
      simp only [latticeCoordinateEquiv, referenceEuclideanBasis, Basis.det_basis]
    have hr : realLatticeCoordinateBasis (d := d) L = fun i : Fin d => (bZ i : (EuclideanSpace ℝ
      (Fin d))) := by
      funext i
      simp only [realLatticeCoordinateBasis, Basis.ofZLatticeBasis_apply, bZ]
    exact (congrArg ((referenceEuclideanBasis (d := d)).det) hr.symm).trans hdetA.symm
  have hcovol :
      ZLattice.covolume L = |(referenceEuclideanBasis (d := d)).det (fun i : Fin d => (bZ i :
        (EuclideanSpace ℝ (Fin d))))| := by
    simpa only [referenceEuclideanBasis, reference_basis_fundamental_region_volume (d := d),
      mul_one] using!
      (ZLattice.covolume_eq_det_mul_measureReal
        (L := L) (b := bZ) (b₀ := referenceEuclideanBasis (d := d)) (μ := (volume : Measure
          (EuclideanSpace ℝ (Fin d)))))
  simp only [hcovol, hdet]

end CovolumeDet

section PoissonSummationLattices

variable (L : Submodule ℤ (EuclideanSpace ℝ (Fin d))) [DiscreteTopology L] [IsZLattice ℝ L]

private noncomputable def latticeCoordinateTransport : (EuclideanSpace ℝ (Fin d)) ≃ₗ[ℝ]
  (EuclideanSpace ℝ (Fin d)) := latticeCoordinateEquiv (d := d) L

private noncomputable def dualCoordinateTransport : (EuclideanSpace ℝ (Fin d)) →ₗ[ℝ]
  (EuclideanSpace ℝ (Fin d)) := ((latticeCoordinateTransport (d := d) (L :=
  L)).symm.toLinearMap).adjoint

private noncomputable def latticeCoordinateAdjoint : (EuclideanSpace ℝ (Fin d)) →ₗ[ℝ]
  (EuclideanSpace ℝ (Fin d)) := ((latticeCoordinateTransport (d := d) (L := L)).toLinearMap).adjoint

private noncomputable def referenceLatticeCoordinateEquiv : SchwartzMap.referenceIntegerLattice
  d ≃ₗ[ℤ] L :=
  (LinearEquiv.restrictScalars ℤ (latticeCoordinateTransport (d := d) (L := L))).ofSubmodules
    (SchwartzMap.referenceIntegerLattice d) L
    (by
      simpa only [LinearEquiv.restrictScalars_toLinearMap] using!
        (coordinate_transport_maps_reference_lattice (d := d) L))

@[simp]
private lemma reference_lattice_coordinate_equiv_apply (x : SchwartzMap.referenceIntegerLattice d) :
    ((referenceLatticeCoordinateEquiv (d := d) L x : L) : (EuclideanSpace ℝ (Fin d))) =
      (latticeCoordinateTransport (d := d) (L := L)) x := by
  simp only [referenceLatticeCoordinateEquiv, LinearEquiv.ofSubmodules_apply,
    LinearEquiv.restrictScalars_apply]

private lemma dual_transport_comp_coordinate_adjoint :
    (dualCoordinateTransport (d := d) L ∘ₗ latticeCoordinateAdjoint (d := d) L) = (LinearMap.id
      : (EuclideanSpace ℝ (Fin d)) →ₗ[ℝ] (EuclideanSpace ℝ (Fin d))) := by
  let Amap : (EuclideanSpace ℝ (Fin d)) →ₗ[ℝ] (EuclideanSpace ℝ (Fin d)) :=
    (latticeCoordinateTransport (d := d) (L := L)).toLinearMap
  let Bmap : (EuclideanSpace ℝ (Fin d)) →ₗ[ℝ] (EuclideanSpace ℝ (Fin d)) :=
    (latticeCoordinateTransport (d := d) (L := L)).symm.toLinearMap
  have hcomp : Amap ∘ₗ Bmap = (LinearMap.id : (EuclideanSpace ℝ (Fin d)) →ₗ[ℝ] (EuclideanSpace ℝ
    (Fin d))) := by
    ext x
    simp only [LinearEquiv.comp_coe, LinearEquiv.symm_trans_self, LinearEquiv.refl_toLinearMap,
      LinearMap.id_coe,
      id_eq, Amap, Bmap]
  calc
    dualCoordinateTransport (d := d) L ∘ₗ latticeCoordinateAdjoint (d := d) L = Bmap.adjoint ∘ₗ
      Amap.adjoint := by
      simp only [dualCoordinateTransport, latticeCoordinateAdjoint, Bmap, Amap]
    _ = (Amap ∘ₗ Bmap).adjoint := by
      exact (LinearMap.adjoint_comp Amap Bmap).symm
    _ = (LinearMap.id : (EuclideanSpace ℝ (Fin d)) →ₗ[ℝ] (EuclideanSpace ℝ (Fin d))) := by simp
      only [hcomp, LinearMap.IsSymmetric.id, LinearMap.IsSymmetric.adjoint_eq]

private lemma coordinate_adjoint_comp_dual_transport :
    (latticeCoordinateAdjoint (d := d) L ∘ₗ dualCoordinateTransport (d := d) L) = (LinearMap.id
      : (EuclideanSpace ℝ (Fin d)) →ₗ[ℝ] (EuclideanSpace ℝ (Fin d))) := by
  let Amap : (EuclideanSpace ℝ (Fin d)) →ₗ[ℝ] (EuclideanSpace ℝ (Fin d)) :=
    (latticeCoordinateTransport (d := d) (L := L)).toLinearMap
  let Bmap : (EuclideanSpace ℝ (Fin d)) →ₗ[ℝ] (EuclideanSpace ℝ (Fin d)) :=
    (latticeCoordinateTransport (d := d) (L := L)).symm.toLinearMap
  have hcomp : Bmap ∘ₗ Amap = (LinearMap.id : (EuclideanSpace ℝ (Fin d)) →ₗ[ℝ] (EuclideanSpace ℝ
    (Fin d))) := by
    ext x
    simp only [LinearEquiv.comp_coe, LinearEquiv.self_trans_symm, LinearEquiv.refl_toLinearMap,
      LinearMap.id_coe,
      id_eq, Bmap, Amap]
  calc
    latticeCoordinateAdjoint (d := d) L ∘ₗ dualCoordinateTransport (d := d) L = Amap.adjoint ∘ₗ
      Bmap.adjoint := by
      simp only [latticeCoordinateAdjoint, dualCoordinateTransport, Amap, Bmap]
    _ = (Bmap ∘ₗ Amap).adjoint := by
      exact (LinearMap.adjoint_comp Bmap Amap).symm
    _ = (LinearMap.id : (EuclideanSpace ℝ (Fin d)) →ₗ[ℝ] (EuclideanSpace ℝ (Fin d))) := by simp
      only [hcomp, LinearMap.IsSymmetric.id, LinearMap.IsSymmetric.adjoint_eq]

private noncomputable def dualAdjointCoordinateEquiv : (EuclideanSpace ℝ (Fin d)) ≃ₗ[ℝ]
  (EuclideanSpace ℝ (Fin d)) :=
  { toLinearMap := dualCoordinateTransport (d := d) L
    invFun := latticeCoordinateAdjoint (d := d) L
    left_inv := by
      intro x
      have h := coordinate_adjoint_comp_dual_transport (d := d) (L := L)
      simpa only [AddHom.toFun_eq_coe, LinearMap.coe_toAddHom, LinearMap.coe_comp,
        Function.comp_apply,
        LinearMap.id_coe, id_eq] using! congrArg (fun f : (EuclideanSpace ℝ (Fin d)) →ₗ[ℝ]
          (EuclideanSpace ℝ (Fin d)) => f x) h
    right_inv := by
      intro x
      have h := dual_transport_comp_coordinate_adjoint (d := d) (L := L)
      simpa only [AddHom.toFun_eq_coe, LinearMap.coe_toAddHom, LinearMap.coe_comp,
        Function.comp_apply,
        LinearMap.id_coe, id_eq] using! congrArg (fun f : (EuclideanSpace ℝ (Fin d)) →ₗ[ℝ]
          (EuclideanSpace ℝ (Fin d)) => f x) h }

private lemma dual_coordinate_transport_maps_reference_lattice :
    Submodule.map ((dualCoordinateTransport (d := d) L).restrictScalars ℤ)
      (referenceIntegerLattice d) =
      polarIntegerLattice (d := d) L := by
  ext x
  have hdualStd : polarIntegerLattice (d := d) (referenceIntegerLattice d) =
    referenceIntegerLattice d := by
    simpa only [polarIntegerLattice] using!
      (PoissonSummation.Standard.reference_lattice_dual_self (d := d))
  constructor
  · rintro ⟨y, hy, rfl⟩
    intro z hz
    rcases (show (z : (EuclideanSpace ℝ (Fin d))) ∈
        Submodule.map ((latticeCoordinateTransport (d := d) L).toLinearMap.restrictScalars ℤ)
          (referenceIntegerLattice d) by
      simpa only [latticeCoordinateTransport,
        coordinate_transport_maps_reference_lattice (d := d) L] using! hz) with ⟨w, hw, rfl⟩
    have hydual : y ∈ polarIntegerLattice (d := d) (referenceIntegerLattice d) := by
      simpa only [hdualStd, SetLike.mem_coe] using! hy
    have hinter :
        inner ℝ ((dualCoordinateTransport (d := d) L) y) ((latticeCoordinateTransport (d := d)
          (L := L)) w) = inner ℝ y w := by
      simpa only [dualCoordinateTransport, latticeCoordinateTransport, LinearEquiv.coe_coe,
        LinearEquiv.symm_apply_apply] using!
        (LinearMap.adjoint_inner_left ((latticeCoordinateTransport (d := d) (L :=
          L)).symm.toLinearMap)
          ((latticeCoordinateTransport (d := d) (L := L)) w) y)
    simpa only [LinearMap.coe_restrictScalars, LinearEquiv.coe_coe, innerₗ_apply_apply, hinter,
      Submodule.mem_one,
      algebraMap_int_eq, eq_intCast] using! hydual w hw
  · intro hx
    refine ⟨(latticeCoordinateAdjoint (d := d) L) x, ?_, ?_⟩
    · have hydual :
          (latticeCoordinateAdjoint (d := d) L) x ∈
            polarIntegerLattice (d := d) (referenceIntegerLattice d) := by
        intro w hw
        have hwL : (latticeCoordinateTransport (d := d) (L := L)) w ∈ L := by
          have : (latticeCoordinateTransport (d := d) (L := L)) w ∈
              Submodule.map (((latticeCoordinateTransport (d := d) (L :=
                L)).toLinearMap).restrictScalars ℤ)
                (referenceIntegerLattice d) :=
            ⟨w, hw, rfl⟩
          simpa only [latticeCoordinateTransport,
            coordinate_transport_maps_reference_lattice (d := d) L] using! this
        have hinner :
            inner ℝ ((latticeCoordinateAdjoint (d := d) L) x) w = inner ℝ x
              ((latticeCoordinateTransport (d := d) (L := L)) w) := by
          simpa only [latticeCoordinateAdjoint, latticeCoordinateTransport,
            LinearEquiv.coe_coe] using!
            (LinearMap.adjoint_inner_left ((latticeCoordinateTransport (d := d) (L :=
              L)).toLinearMap) w x)
        simpa only [innerₗ_apply_apply, hinner, Submodule.mem_one, algebraMap_int_eq,
          eq_intCast] using!
          hx ((latticeCoordinateTransport (d := d) (L := L)) w) hwL
      simpa only [SetLike.mem_coe, hdualStd] using! hydual
    · have h := dual_transport_comp_coordinate_adjoint (d := d) (L := L)
      simpa only [LinearMap.coe_restrictScalars, LinearMap.coe_comp, Function.comp_apply,
        LinearMap.id_coe,
        id_eq] using! congrArg (fun f : (EuclideanSpace ℝ (Fin d)) →ₗ[ℝ] (EuclideanSpace ℝ (Fin
          d)) => f x) h

private noncomputable def referenceLatticePolarEquiv :
    SchwartzMap.referenceIntegerLattice d ≃ₗ[ℤ] polarIntegerLattice (d := d) L :=
  (LinearEquiv.restrictScalars ℤ (dualAdjointCoordinateEquiv (d := d) (L := L))).ofSubmodules
    (SchwartzMap.referenceIntegerLattice d) (polarIntegerLattice (d := d) L)
    (by
      simpa only [LinearEquiv.restrictScalars_toLinearMap] using!
        (dual_coordinate_transport_maps_reference_lattice (d := d) (L := L)))

private noncomputable def integerVectorPolarLatticeEquiv : (Fin d → ℤ) ≃ polarIntegerLattice (d
  := d) L :=
  (PoissonSummation.Standard.integerVectorLatticeEquiv (d := d)).trans
    (referenceLatticePolarEquiv (d := d) L).toEquiv

@[simp]
private lemma reference_lattice_polar_equiv_apply (x : SchwartzMap.referenceIntegerLattice d) :
    ((referenceLatticePolarEquiv (d := d) L x : polarIntegerLattice (d := d) L) :
      (EuclideanSpace ℝ (Fin d))) =
      (dualCoordinateTransport (d := d) L) x := by simp only [referenceLatticePolarEquiv,
        dualAdjointCoordinateEquiv, LinearEquiv.ofSubmodules_apply,
                                                     LinearEquiv.restrictScalars_apply,
                                                       LinearEquiv.coe_mk]

@[simp]
private lemma integer_vector_polar_equiv_coe (n : Fin d → ℤ) :
    ((integerVectorPolarLatticeEquiv (d := d) L n : polarIntegerLattice (d := d) L) :
      (EuclideanSpace ℝ (Fin d))) =
      (dualCoordinateTransport (d := d) L)
        (SchwartzMap.PoissonSummation.Standard.embeddedIntegerVector (d := d) n) := by
  change
    (dualCoordinateTransport (d := d) L)
        (SchwartzMap.PoissonSummation.Standard.embeddedIntegerVector
          (d := d) n) = _
  rfl

private theorem integer_lattice_poisson_identity (f : SchwartzMap (EuclideanSpace ℝ (Fin d)) ℂ)
  (v : (EuclideanSpace ℝ (Fin d))) :
    (∑' ℓ : L, f (v + (ℓ : (EuclideanSpace ℝ (Fin d))))) =
      (1 / ZLattice.covolume L) *
        ∑' m : polarIntegerLattice (d := d) L,
          (𝓕 (fun x : (EuclideanSpace ℝ (Fin d)) => f x) m) * Complex.exp (2 * π * Complex.I *
            ⟪v, m⟫_[ℝ]) := by
  let A : (EuclideanSpace ℝ (Fin d)) ≃ₗ[ℝ] (EuclideanSpace ℝ (Fin d)) :=
    latticeCoordinateTransport (d := d) (L := L)
  let g : SchwartzMap (EuclideanSpace ℝ (Fin d)) ℂ :=
    SchwartzMap.compCLMOfContinuousLinearEquiv ℂ A.toContinuousLinearEquiv f
  have hstd :=
    SchwartzMap.PoissonSummation.Standard.reference_lattice_poisson_formula
      (d := d) (f := g) (v := A.symm v)
  have hlhs :
      (∑' ℓ : SchwartzMap.referenceIntegerLattice d,
        g (A.symm v + (ℓ : (EuclideanSpace ℝ (Fin d))))) =
        ∑' ℓ : L, f (v + (ℓ : (EuclideanSpace ℝ (Fin d)))) := by
    calc
      (∑' ℓ : SchwartzMap.referenceIntegerLattice d,
        g (A.symm v + (ℓ : (EuclideanSpace ℝ (Fin d))))) =
          ∑' ℓ : SchwartzMap.referenceIntegerLattice d,
            f (v + A (ℓ : (EuclideanSpace ℝ (Fin d)))) := by
            refine tsum_congr fun ℓ ↦ ?_
            simp only [compCLMOfContinuousLinearEquiv_apply,
              LinearEquiv.coe_toContinuousLinearEquiv',
              Function.comp_apply, map_add, LinearEquiv.apply_symm_apply, g]
      _ = ∑' ℓ : L, f (v + (ℓ : (EuclideanSpace ℝ (Fin d)))) := by
          simpa only [LinearEquiv.coe_toEquiv, reference_lattice_coordinate_equiv_apply] using!
            ((referenceLatticeCoordinateEquiv (d := d) L).toEquiv.tsum_eq
              (f := fun ℓ : L => f (v + (ℓ : (EuclideanSpace ℝ (Fin d))))))
  have hrhs :
      (∑' n : Fin d → ℤ,
          (𝓕 (fun x : (EuclideanSpace ℝ (Fin d)) => g x)
            (SchwartzMap.PoissonSummation.Standard.embeddedIntegerVector (d := d) n)) *
            Complex.exp
              (2 * π * Complex.I *
                ⟪A.symm v, SchwartzMap.PoissonSummation.Standard.embeddedIntegerVector (d := d)
                  n⟫_[ℝ])) =
        (1 / ZLattice.covolume L) *
          ∑' m : polarIntegerLattice (d := d) L,
            (𝓕 (fun x : (EuclideanSpace ℝ (Fin d)) => f x) m) * Complex.exp (2 * π * Complex.I *
              ⟪v, m⟫_[ℝ]) := by
    let F : polarIntegerLattice (d := d) L → ℂ :=
      fun m => (𝓕 (fun x : (EuclideanSpace ℝ (Fin d)) => f x) m) * Complex.exp (2 * π *
        Complex.I * ⟪v, m⟫_[ℝ])
    let detA : ℝ := (LinearMap.det : ((EuclideanSpace ℝ (Fin d)) →ₗ[ℝ] (EuclideanSpace ℝ (Fin
      d))) →* ℝ) (A : (EuclideanSpace ℝ (Fin d)) →ₗ[ℝ] (EuclideanSpace ℝ (Fin d)))
    let cC : ℂ := ((abs detA)⁻¹ : ℝ)
    have hfourier (w : (EuclideanSpace ℝ (Fin d))) :
        𝓕 (fun x : (EuclideanSpace ℝ (Fin d)) => g x) w =
          cC * 𝓕 (fun x : (EuclideanSpace ℝ (Fin d)) => f x) ((dualCoordinateTransport (d := d)
            L) w) := by
      simpa [g, A, dualCoordinateTransport, detA, cC, Complex.real_smul] using!
        (SpherePacking.ForMathlib.Fourier.fourier_precompose_linear_equivalence
          (A := A) (f := fun x : (EuclideanSpace ℝ (Fin d)) => f x) w)
    have hexp (w : (EuclideanSpace ℝ (Fin d))) :
        Complex.exp (2 * π * Complex.I * ⟪A.symm v, w⟫_[ℝ]) =
          Complex.exp (2 * π * Complex.I * ⟪v, (dualCoordinateTransport (d := d) L) w⟫_[ℝ]) := by
      have hinner : ⟪A.symm v, w⟫_[ℝ] = ⟪v, (dualCoordinateTransport (d := d) L) w⟫_[ℝ] := by
        have : inner ℝ (A.symm v) w = inner ℝ v ((dualCoordinateTransport (d := d) L) w) := by
          simpa only [dualCoordinateTransport, LinearEquiv.coe_coe] using!
            (LinearMap.adjoint_inner_right ((A.symm : (EuclideanSpace ℝ (Fin d)) ≃ₗ[ℝ]
              (EuclideanSpace ℝ (Fin d))).toLinearMap) v w).symm
        simpa only [RCLike.inner_eq_wInner_one] using! this
      simp only [hinner]
    have hdetC : cC = (1 / ZLattice.covolume L) := by
      have hcovol : ZLattice.covolume L = abs detA := by
        simpa only [latticeCoordinateTransport] using!
          (lattice_covolume_eq_coordinate_determinant (d := d) (L := L))
      simp only [Complex.ofReal_inv, hcovol, one_div, cC]
    have hsum :
        (∑' n : Fin d → ℤ,
            (𝓕 (fun x : (EuclideanSpace ℝ (Fin d)) => g x)
              (SchwartzMap.PoissonSummation.Standard.embeddedIntegerVector (d := d) n)) *
              Complex.exp
                (2 * π * Complex.I *
                  ⟪A.symm v, SchwartzMap.PoissonSummation.Standard.embeddedIntegerVector (d :=
                    d) n⟫_[ℝ])) =
          cC * ∑' m : polarIntegerLattice (d := d) L, F m := by
      calc
        (∑' n : Fin d → ℤ,
            (𝓕 (fun x : (EuclideanSpace ℝ (Fin d)) => g x)
              (SchwartzMap.PoissonSummation.Standard.embeddedIntegerVector (d := d) n)) *
              Complex.exp
                (2 * π * Complex.I *
                  ⟪A.symm v, SchwartzMap.PoissonSummation.Standard.embeddedIntegerVector (d :=
                    d) n⟫_[ℝ])) =
            ∑' n : Fin d → ℤ, cC * F (integerVectorPolarLatticeEquiv (d := d) L n) := by
              refine tsum_congr fun n ↦ ?_
              simpa only [mul_assoc, integer_vector_polar_equiv_coe, F] using!
                congrArg₂ (· * ·)
                  (hfourier (w := SchwartzMap.PoissonSummation.Standard.embeddedIntegerVector (d
                    := d) n))
                  (hexp (w := SchwartzMap.PoissonSummation.Standard.embeddedIntegerVector (d :=
                    d) n))
        _ = cC * ∑' n : Fin d → ℤ, F (integerVectorPolarLatticeEquiv (d := d) L n) := tsum_mul_left
        _ = cC * ∑' m : polarIntegerLattice (d := d) L, F m := by
              rw [(integerVectorPolarLatticeEquiv (d := d) L).tsum_eq]
    simp only [hsum, hdetC, one_div, F]
  simpa only [one_div, hlhs, hrhs] using! hstd

end SchwartzMap.PoissonSummationLattices

end

section

variable {d : ℕ} [Fact (0 < d)]
variable (Λ : Submodule ℤ (EuclideanSpace ℝ (Fin d))) [DiscreteTopology Λ] [IsZLattice ℝ Λ]

section

open scoped BigOperators FourierTransform

namespace SchwartzMap

omit [Fact (0 < d)] in
private theorem latticePoissonSummationFormula (f : SchwartzMap (EuclideanSpace ℝ (Fin d)) ℂ)
  (v : EuclideanSpace ℝ (Fin d)) : ∑' ℓ : Λ, f (v + ℓ) = (1 / ZLattice.covolume Λ) *
  ∑' m : polarIntegerLattice (d := d) Λ, (𝓕 ⇑f m) *
    Complex.exp (2 * Real.pi * Complex.I * ⟪v, m⟫_[ℝ]) := by
  simpa only [one_div] using! (SchwartzMap.integer_lattice_poisson_identity (d := d) (L := Λ) f v)

section FourierSchwartz

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
  {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
    [MeasurableSpace V] [BorelSpace V]
  (f : 𝓢(V, E))

@[simp]
private theorem schwartz_fourier_inverse_identity : 𝓕⁻ (𝓕 ⇑f) = f := by
  simpa only [SchwartzMap.fourierInv_coe, SchwartzMap.fourier_coe] using
    congrArg (fun g : 𝓢(V, E) => (g : V → E))
      (show (𝓕⁻ (𝓕 f : 𝓢(V, E)) : 𝓢(V, E)) = f from
        FourierTransform.fourierInv_fourier_eq f)

end FourierSchwartz

end SchwartzMap
section Positivity_on_Nhd

variable {E : Type*} [TopologicalSpace E]

open MeasureTheory

variable [MeasureSpace E] [BorelSpace E]

end Positivity_on_Nhd

section Integration

open MeasureTheory Filter

variable {E : Type*} [NormedAddCommGroup E]
variable [TopologicalSpace E] [IsTopologicalAddGroup E] [MeasureSpace E] [BorelSpace E]
variable [(volume : Measure E).IsAddLeftInvariant] [(volume : Measure E).Regular]
  [NeZero (volume : Measure E)]

private noncomputable instance : (volume : Measure E).IsOpenPosMeasure :=
  isOpenPosMeasure_of_addLeftInvariant_of_regular

private theorem Continuous.nonnegative_integral_vanishes_iff_function_vanishes {f : E → ℝ} (hf₁
  : Continuous f)
  (hf₂ : Integrable f) (hnn : ∀ x, 0 ≤ f x) : ∫ (v : E), f v = 0 ↔ f = 0 := by
  constructor
  · intro hzero
    funext x
    change f x = 0
    by_contra hx
    have hopen : IsOpen (Function.support f) := by
      exact (isOpen_ne : IsOpen {y : ℝ | y ≠ 0}).preimage hf₁
    have hmeasure : 0 < volume (Function.support f) :=
      hopen.measure_pos volume ⟨x, hx⟩
    have hpositive : 0 < ∫ v : E, f v :=
      (integral_pos_iff_support_of_nonneg hnn hf₂).2 hmeasure
    linarith
  · intro hzero
    simp only [hzero, Pi.zero_apply, integral_zero]

end Integration

section Misc

private noncomputable instance : DecidableEq (EuclideanSpace ℝ (Fin d)) := inferInstance

omit [Fact (0 < d)]

private theorem Complex.negative_imaginary_exponential_eq_conjugate (x m : EuclideanSpace ℝ (Fin
  d)) :
  Complex.exp (-(2 * (Real.pi : ℂ) * Complex.I * (⟪x, m⟫_[ℝ] : ℂ))) =
    (starRingEnd ℂ) (Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (⟪x, m⟫_[ℝ] : ℂ))) :=
  calc
    Complex.exp (-(2 * (Real.pi : ℂ) * Complex.I * (⟪x, m⟫_[ℝ] : ℂ)))
        = Circle.exp (-2 * Real.pi * ⟪x, m⟫_[ℝ])
      := by
          rw [Circle.coe_exp]
          push_cast
          ring_nf
    _ = (starRingEnd ℂ) (Circle.exp (2 * Real.pi * ⟪x, m⟫_[ℝ]))
      := by rw [mul_assoc, neg_mul, ← mul_assoc, ← Circle.coe_inv_eq_conj, Circle.exp_neg]
    _ = (starRingEnd ℂ) (Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (⟪x, m⟫_[ℝ] : ℂ)))
      := by
          rw [Circle.coe_exp]
          apply congrArg (starRingEnd ℂ)
          push_cast
          ring_nf

end Misc

end

end

section

open scoped RealInnerProductSpace

open Module

namespace SpherePacking.CohnElkies

variable {d : ℕ}

private noncomputable instance (Λ : Submodule ℤ (EuclideanSpace ℝ (Fin d))) [DiscreteTopology Λ]
    [IsZLattice ℝ Λ] :
    DiscreteTopology
      (LinearMap.BilinForm.dualSubmodule (B := innerₗ (EuclideanSpace ℝ (Fin d))) Λ) := by
  let ι := Module.Free.ChooseBasisIndex ℤ Λ
  let bZ : Basis ι ℤ Λ := Module.Free.chooseBasis ℤ Λ
  let bR : Basis ι ℝ (EuclideanSpace ℝ (Fin d)) := bZ.ofZLatticeBasis ℝ Λ
  have hB :
      LinearMap.BilinForm.Nondegenerate (innerₗ (EuclideanSpace ℝ (Fin d)) :
        LinearMap.BilinForm ℝ (EuclideanSpace ℝ (Fin d))) := by
    constructor <;> intro x hx
    all_goals
      have : ⟪x, x⟫ = (0 : ℝ) := by
        simpa only [inner_self_eq_norm_sq_to_K, Real.ringHom_apply, ne_eq, OfNat.ofNat_ne_zero,
          not_false_eq_true,
          pow_eq_zero_iff, norm_eq_zero, innerₗ_apply_apply] using! hx x
      exact inner_self_eq_zero.1 this
  have hdual :
      LinearMap.BilinForm.dualSubmodule (B := innerₗ (EuclideanSpace ℝ (Fin d))) Λ =
        Submodule.span ℤ
          (Set.range
            (LinearMap.BilinForm.dualBasis
              (B := innerₗ (EuclideanSpace ℝ (Fin d))) hB bR)) := by
    simpa [bR, bZ.ofZLatticeBasis_span (K := ℝ) (L := Λ)] using!
      (LinearMap.BilinForm.dualSubmodule_span_of_basis (B := innerₗ (EuclideanSpace ℝ (Fin d)))
        (R := ℤ) (S := ℝ) (M := EuclideanSpace ℝ (Fin d)) hB bR)
  exact hdual ▸
    (inferInstance :
      DiscreteTopology (Submodule.span ℤ
        (Set.range
          (LinearMap.BilinForm.dualBasis (B := innerₗ (EuclideanSpace ℝ (Fin d))) hB bR))))

end SpherePacking.CohnElkies

end

section

open scoped SchwartzMap
open scoped FourierTransform

open BigOperators

namespace SpherePacking.CohnElkies
variable {d : ℕ}

namespace LPBoundAux

section ZLatticeSummability

variable (Λ : Submodule ℤ (EuclideanSpace ℝ (Fin d))) [DiscreteTopology Λ]

private lemma summable_norm_on_translated_integral_lattice (f : 𝓢(EuclideanSpace ℝ (Fin d), ℂ))
    (a : EuclideanSpace ℝ (Fin d)) :
    Summable (fun ℓ : Λ => ‖f (a + (ℓ : EuclideanSpace ℝ (Fin d)))‖) := by
  let k : ℕ := Module.finrank ℤ Λ + 1
  obtain ⟨C, hCpos, hC⟩ := f.decay k 0
  have hdecay : ∀ x : EuclideanSpace ℝ (Fin d), ‖x‖ ^ k * ‖f x‖ ≤ C := by
    simpa only [norm_iteratedFDeriv_zero] using! hC
  let R : ℝ := max (2 * ‖a‖) 1
  have hfinite : ({ℓ : Λ | ‖(ℓ : EuclideanSpace ℝ (Fin d))‖ ≤ R} : Set Λ).Finite := by
    have : DiscreteTopology Λ.toAddSubgroup :=
      (inferInstance : DiscreteTopology Λ)
    have hfiniteAmbient :
        (Metric.closedBall (0 : EuclideanSpace ℝ (Fin d)) R ∩
          (Λ.toAddSubgroup : Set (EuclideanSpace ℝ (Fin d)))).Finite :=
      Metric.finite_isBounded_inter_isClosed DiscreteTopology.isDiscrete
        Metric.isBounded_closedBall AddSubgroup.isClosed_of_discrete
    let e : Λ ↪ EuclideanSpace ℝ (Fin d) :=
      ⟨fun ℓ => (ℓ : EuclideanSpace ℝ (Fin d)), Subtype.coe_injective⟩
    have hpreimage :
        (e ⁻¹' (Metric.closedBall (0 : EuclideanSpace ℝ (Fin d)) R ∩
          (Λ : Set (EuclideanSpace ℝ (Fin d))))).Finite := by
      apply Set.Finite.preimage_embedding e
      simpa only [AddSubgroup.coe_set_mk, Submodule.coe_toAddSubmonoid] using! hfiniteAmbient
    have hset :
        e ⁻¹' (Metric.closedBall (0 : EuclideanSpace ℝ (Fin d)) R ∩
          (Λ : Set (EuclideanSpace ℝ (Fin d)))) =
            {ℓ : Λ | ‖(ℓ : EuclideanSpace ℝ (Fin d))‖ ≤ R} := by
      ext ℓ
      simp only [Function.Embedding.coeFn_mk, Set.preimage_inter, Set.mem_inter_iff,
        Set.mem_preimage,
        Metric.mem_closedBall, dist_eq_norm, sub_zero, Subtype.coe_prop, and_true,
          Set.mem_ofPred_eq, e]
    simpa only [hset] using! hpreimage
  have hsumPow :
      Summable (fun ℓ : Λ =>
        (‖(ℓ : EuclideanSpace ℝ (Fin d))‖⁻¹ ^ k : ℝ)) := by
    simpa only [inv_pow, AddSubgroupClass.coe_norm] using!
      (ZLattice.summable_norm_pow_inv (L := Λ) (n := k)
        (Nat.lt_succ_self (Module.finrank ℤ Λ)))
  have hsumBound :
      Summable (fun ℓ : Λ =>
        (C * (2 ^ k : ℝ)) *
          (‖(ℓ : EuclideanSpace ℝ (Fin d))‖⁻¹ ^ k)) :=
    hsumPow.mul_left (C * (2 ^ k : ℝ))
  refine Summable.of_norm_bounded_eventually hsumBound ?_
  filter_upwards [hfinite.eventually_cofinite_notMem] with ℓ hℓ
  have hR : R < ‖(ℓ : EuclideanSpace ℝ (Fin d))‖ :=
    lt_of_not_ge (by simpa only [not_le] using! hℓ)
  have hlarge : 2 * ‖a‖ < ‖(ℓ : EuclideanSpace ℝ (Fin d))‖ :=
    lt_of_le_of_lt (le_max_left _ _) hR
  have hpositive : 0 < ‖(ℓ : EuclideanSpace ℝ (Fin d))‖ :=
    lt_of_lt_of_le zero_lt_one ((le_max_right _ _).trans hR.le)
  have htranslate :
      (1 / 2 : ℝ) * ‖(ℓ : EuclideanSpace ℝ (Fin d))‖ ≤
        ‖a + (ℓ : EuclideanSpace ℝ (Fin d))‖ := by
    have htriangle :
        ‖(ℓ : EuclideanSpace ℝ (Fin d))‖ - ‖a‖ ≤
          ‖a + (ℓ : EuclideanSpace ℝ (Fin d))‖ := by
      simpa only [tsub_le_iff_right, add_comm, norm_neg, sub_neg_eq_add] using!
        (norm_sub_norm_le (ℓ : EuclideanSpace ℝ (Fin d)) (-a))
    linarith
  have htranslatePositive :
      0 < ‖a + (ℓ : EuclideanSpace ℝ (Fin d))‖ :=
    (mul_pos (by norm_num : (0 : ℝ) < 1 / 2) hpositive).trans_le htranslate
  have hpowPositive :
      0 < ‖a + (ℓ : EuclideanSpace ℝ (Fin d))‖ ^ k :=
    pow_pos htranslatePositive _
  have hbound :
      ‖f (a + (ℓ : EuclideanSpace ℝ (Fin d)))‖ ≤
        C / ‖a + (ℓ : EuclideanSpace ℝ (Fin d))‖ ^ k :=
    (le_div_iff₀' hpowPositive).2
      (hdecay (a + (ℓ : EuclideanSpace ℝ (Fin d))))
  have hpower :
      ((1 / 2 : ℝ) * ‖(ℓ : EuclideanSpace ℝ (Fin d))‖) ^ k ≤
        ‖a + (ℓ : EuclideanSpace ℝ (Fin d))‖ ^ k :=
    pow_le_pow_left₀ (by positivity) htranslate _
  have hsourcePositive :
      0 < ((1 / 2 : ℝ) * ‖(ℓ : EuclideanSpace ℝ (Fin d))‖) ^ k :=
    pow_pos (mul_pos (by norm_num : (0 : ℝ) < 1 / 2) hpositive) _
  have hinverse :
      (‖a + (ℓ : EuclideanSpace ℝ (Fin d))‖ ^ k)⁻¹ ≤
        (2 ^ k : ℝ) *
          (‖(ℓ : EuclideanSpace ℝ (Fin d))‖⁻¹ ^ k) := by
    have h := one_div_le_one_div_of_le hsourcePositive hpower
    simpa only [inv_pow, ge_iff_le, one_div, mul_pow, mul_inv_rev, inv_inv, mul_comm]
      using! h
  have hfinal :=
    (mul_le_mul_of_nonneg_left hinverse hCpos.le)
  have hresult :
      ‖f (a + (ℓ : EuclideanSpace ℝ (Fin d)))‖ ≤
        (C * (2 ^ k : ℝ)) *
          (‖(ℓ : EuclideanSpace ℝ (Fin d))‖⁻¹ ^ k) := by
    calc
      ‖f (a + (ℓ : EuclideanSpace ℝ (Fin d)))‖ ≤
          C / ‖a + (ℓ : EuclideanSpace ℝ (Fin d))‖ ^ k := hbound
      _ ≤ (C * (2 ^ k : ℝ)) *
          (‖(ℓ : EuclideanSpace ℝ (Fin d))‖⁻¹ ^ k) := by
        simpa only [div_eq_mul_inv, inv_pow, mul_assoc] using! hfinal
  simpa only [norm_norm, inv_pow, ge_iff_le] using! hresult

end SpherePacking.CohnElkies.LPBoundAux.ZLatticeSummability

end

section

open scoped Real
open scoped SchwartzMap FourierTransform

namespace SpherePacking.CohnElkies

private noncomputable def centerFourierExponentialSum {d : ℕ} (P : PeriodicSpherePacking d)
    (D : Set (EuclideanSpace ℝ (Fin d))) :
    ↥(SchwartzMap.polarIntegerLattice (d := d) P.lattice) → ℂ :=
  fun m =>
    ∑' x : ↑(P.centers ∩ D),
      Complex.exp (2 * π * Complex.I * ⟪(x : EuclideanSpace ℝ (Fin d)),
        (m : EuclideanSpace ℝ (Fin d))⟫_[ℝ])

private lemma origin_character_sum_norm_sq_eq_orbit_count_sq {d : ℕ} (P : PeriodicSpherePacking d)
    {D : Set (EuclideanSpace ℝ (Fin d))} (hd : 0 < d) (hD_isBounded : Bornology.IsBounded D) :
    norm (∑' x : ↑(P.centers ∩ D),
        Complex.exp (2 * π * Complex.I *
          ⟪(x : EuclideanSpace ℝ (Fin d)),
            (0 : EuclideanSpace ℝ (Fin d))⟫_[ℝ])) ^ 2
      =
      (P.boundedCenterRepresentativeCount hd hD_isBounded : ℝ) ^ 2 := by
  let := P.instFintypeBoundedCenterRepresentatives hd hD_isBounded
  simp only [WithLp.ofLp_zero, RCLike.wInner_zero_right, Complex.ofReal_zero, mul_zero,
    Complex.exp_zero,
    tsum_fintype, Finset.sum_const, Finset.card_univ, Set.fintypeCard_eq_ncard, nsmul_eq_mul,
      mul_one,
    RCLike.norm_natCast, PeriodicSpherePacking.boundedCenterRepresentativeCount]

private lemma nonnegative_weighted_nonzero_frequency_sum {d : ℕ}
    (f : 𝓢(EuclideanSpace ℝ (Fin d), ℂ)) (P : PeriodicSpherePacking d)
    (D : Set (EuclideanSpace ℝ (Fin d)))
    (hCohnElkies₂ : ∀ x : EuclideanSpace ℝ (Fin d), (𝓕 f x).re ≥ 0) :
    0 ≤
      ∑' m : ↥(SchwartzMap.polarIntegerLattice (d := d) P.lattice),
        (if m = (0 : ↥(SchwartzMap.polarIntegerLattice (d := d) P.lattice)) then 0
        else
          (𝓕 ⇑f m).re *
            (norm (∑' x : ↑(P.centers ∩ D),
              Complex.exp (2 * π * Complex.I *
                ⟪(x : EuclideanSpace ℝ (Fin d)),
                  (m : EuclideanSpace ℝ (Fin d))⟫_[ℝ])) ^ 2)) := by
  refine tsum_nonneg (fun m => ?_)
  by_cases hm : m = (0 : ↥(SchwartzMap.polarIntegerLattice (d := d) P.lattice))
  · simp only [hm, ↓reduceIte, Std.le_refl]
  · have hf : 0 ≤ (𝓕 ⇑f m).re := by
      simpa only [ge_iff_le] using! hCohnElkies₂ (m : EuclideanSpace ℝ (Fin d))
    simpa only [hm, ↓reduceIte, ge_iff_le,
      centerFourierExponentialSum] using! (mul_nonneg hf (sq_nonneg (norm
      (centerFourierExponentialSum P D m))))

end SpherePacking.CohnElkies

end

section

open scoped BigOperators FourierTransform SchwartzMap Real
open Complex MeasureTheory

namespace SpherePacking.CohnElkies

variable {d : ℕ}

private lemma packing_spectral_sum_exchange (f : 𝓢(EuclideanSpace ℝ (Fin d), ℂ))
    (hRealFourier : ∀ x : EuclideanSpace ℝ (Fin d), (((𝓕 f) x).re : ℂ) = (𝓕 f) x)
    (P : PeriodicSpherePacking d) {D : Set (EuclideanSpace ℝ (Fin d))}
    (hD_isBounded : Bornology.IsBounded D) (hd : 0 < d) :
    (∑' x : ↑(P.centers ∩ D),
        ∑' y : ↑(P.centers ∩ D),
          (1 / ZLattice.covolume P.lattice volume) *
            ∑' m : SchwartzMap.polarIntegerLattice (d := d) P.lattice,
              (𝓕 f m) *
                exp (2 * π * I *
                  ⟪(x : EuclideanSpace ℝ (Fin d)) - (y : EuclideanSpace ℝ (Fin d)),
                    (m : EuclideanSpace ℝ (Fin d))⟫_[ℝ])).re
      =
      ((1 / ZLattice.covolume P.lattice volume) *
          ∑' m : SchwartzMap.polarIntegerLattice (d := d) P.lattice,
            (𝓕 f m).re *
              (∑' x : ↑(P.centers ∩ D),
                ∑' y : ↑(P.centers ∩ D),
                  exp (2 * π * I *
                    ⟪(x : EuclideanSpace ℝ (Fin d)) - (y : EuclideanSpace ℝ (Fin d)),
                      (m : EuclideanSpace ℝ (Fin d))⟫_[ℝ]))).re := by
  classical
  let := P.instFintypeBoundedCenterRepresentatives hd hD_isBounded
  have hFourierNorm :
      Summable (fun m : SchwartzMap.polarIntegerLattice (d := d) P.lattice =>
        ‖(𝓕 f) (m : EuclideanSpace ℝ (Fin d))‖) := by
    simpa only [zero_add] using
      (LPBoundAux.summable_norm_on_translated_integral_lattice
        (SchwartzMap.polarIntegerLattice (d := d) P.lattice) (𝓕 f)
        (0 : EuclideanSpace ℝ (Fin d)))
  have hWeighted (x y : ↑(P.centers ∩ D)) :
      Summable (fun m : SchwartzMap.polarIntegerLattice (d := d) P.lattice =>
        (𝓕 f m) * exp (2 * π * I *
          ⟪(x : EuclideanSpace ℝ (Fin d)) - (y : EuclideanSpace ℝ (Fin d)),
            (m : EuclideanSpace ℝ (Fin d))⟫_[ℝ])) := by
    apply Summable.of_norm
    simpa only [mul_assoc, WithLp.ofLp_sub, Complex.norm_mul, norm_exp, mul_re, re_ofNat,
      ofReal_re, I_re,
      zero_mul, I_im, ofReal_im, mul_zero, sub_self, mul_im, one_mul, zero_add, im_ofNat,
        add_zero, Real.exp_zero,
      mul_one] using hFourierNorm
  have hSwap
      (g : ↑(P.centers ∩ D) →
        SchwartzMap.polarIntegerLattice (d := d) P.lattice → ℂ)
      (hg : ∀ x, Summable (g x)) :
      Summable (fun m => ∑ x : ↑(P.centers ∩ D), g x m) ∧
        (∑ x : ↑(P.centers ∩ D), ∑' m, g x m) =
          ∑' m, ∑ x : ↑(P.centers ∩ D), g x m := by
    have hAux (s : Finset ↑(P.centers ∩ D)) :
        Summable (fun m => ∑ x ∈ s, g x m) ∧
          (∑ x ∈ s, ∑' m, g x m) = ∑' m, ∑ x ∈ s, g x m := by
      induction s using Finset.induction_on with
      | empty => simp only [Finset.sum_empty, summable_zero, tsum_zero, and_self]
      | @insert x s hx ih =>
        constructor
        · simpa only [hx, not_false_eq_true, Finset.sum_insert] using (hg x).add ih.1
        · simpa only [hx, not_false_eq_true, Finset.sum_insert,
          ih.2] using ((hg x).tsum_add ih.1).symm
    simpa only  using hAux Finset.univ
  let c : ℂ := 1 / ZLattice.covolume P.lattice volume
  have hInner (x : ↑(P.centers ∩ D)) :
      Summable (fun m : SchwartzMap.polarIntegerLattice (d := d) P.lattice =>
        ∑ y : ↑(P.centers ∩ D),
          (𝓕 f m) * exp (2 * π * I *
            ⟪(x : EuclideanSpace ℝ (Fin d)) - (y : EuclideanSpace ℝ (Fin d)),
              (m : EuclideanSpace ℝ (Fin d))⟫_[ℝ])) ∧
      (∑ y : ↑(P.centers ∩ D),
        ∑' m : SchwartzMap.polarIntegerLattice (d := d) P.lattice,
          (𝓕 f m) * exp (2 * π * I *
            ⟪(x : EuclideanSpace ℝ (Fin d)) - (y : EuclideanSpace ℝ (Fin d)),
              (m : EuclideanSpace ℝ (Fin d))⟫_[ℝ])) =
        ∑' m : SchwartzMap.polarIntegerLattice (d := d) P.lattice,
          ∑ y : ↑(P.centers ∩ D),
            (𝓕 f m) * exp (2 * π * I *
              ⟪(x : EuclideanSpace ℝ (Fin d)) - (y : EuclideanSpace ℝ (Fin d)),
                (m : EuclideanSpace ℝ (Fin d))⟫_[ℝ]) := by
    exact hSwap
      (fun y m => (𝓕 f m) * exp (2 * π * I *
        ⟪(x : EuclideanSpace ℝ (Fin d)) - (y : EuclideanSpace ℝ (Fin d)),
          (m : EuclideanSpace ℝ (Fin d))⟫_[ℝ]))
      (hWeighted x)
  have hOuter :
      (∑ x : ↑(P.centers ∩ D),
        ∑' m : SchwartzMap.polarIntegerLattice (d := d) P.lattice,
          ∑ y : ↑(P.centers ∩ D),
            (𝓕 f m) * exp (2 * π * I *
              ⟪(x : EuclideanSpace ℝ (Fin d)) - (y : EuclideanSpace ℝ (Fin d)),
                (m : EuclideanSpace ℝ (Fin d))⟫_[ℝ])) =
        ∑' m : SchwartzMap.polarIntegerLattice (d := d) P.lattice,
          ∑ x : ↑(P.centers ∩ D),
            ∑ y : ↑(P.centers ∩ D),
              (𝓕 f m) * exp (2 * π * I *
                ⟪(x : EuclideanSpace ℝ (Fin d)) - (y : EuclideanSpace ℝ (Fin d)),
                  (m : EuclideanSpace ℝ (Fin d))⟫_[ℝ]) := by
    exact (hSwap
      (fun x m => ∑ y : ↑(P.centers ∩ D),
        (𝓕 f m) * exp (2 * π * I *
          ⟪(x : EuclideanSpace ℝ (Fin d)) - (y : EuclideanSpace ℝ (Fin d)),
            (m : EuclideanSpace ℝ (Fin d))⟫_[ℝ]))
      (fun x => (hInner x).1)).2
  have hExchange :
      (∑ x : ↑(P.centers ∩ D),
        ∑ y : ↑(P.centers ∩ D),
          c * ∑' m : SchwartzMap.polarIntegerLattice (d := d) P.lattice,
            (𝓕 f m) * exp (2 * π * I *
              ⟪(x : EuclideanSpace ℝ (Fin d)) - (y : EuclideanSpace ℝ (Fin d)),
                (m : EuclideanSpace ℝ (Fin d))⟫_[ℝ])) =
        c * ∑' m : SchwartzMap.polarIntegerLattice (d := d) P.lattice,
          (𝓕 f m) *
            (∑ x : ↑(P.centers ∩ D), ∑ y : ↑(P.centers ∩ D),
              exp (2 * π * I *
                ⟪(x : EuclideanSpace ℝ (Fin d)) - (y : EuclideanSpace ℝ (Fin d)),
                  (m : EuclideanSpace ℝ (Fin d))⟫_[ℝ])) := by
    calc
      _ = c * ∑ x : ↑(P.centers ∩ D), ∑ y : ↑(P.centers ∩ D),
          ∑' m : SchwartzMap.polarIntegerLattice (d := d) P.lattice,
            (𝓕 f m) * exp (2 * π * I *
              ⟪(x : EuclideanSpace ℝ (Fin d)) - (y : EuclideanSpace ℝ (Fin d)),
                (m : EuclideanSpace ℝ (Fin d))⟫_[ℝ]) := by
        simp only [WithLp.ofLp_sub, Finset.mul_sum]
      _ = c * ∑ x : ↑(P.centers ∩ D),
          ∑' m : SchwartzMap.polarIntegerLattice (d := d) P.lattice,
            ∑ y : ↑(P.centers ∩ D),
              (𝓕 f m) * exp (2 * π * I *
                ⟪(x : EuclideanSpace ℝ (Fin d)) - (y : EuclideanSpace ℝ (Fin d)),
                  (m : EuclideanSpace ℝ (Fin d))⟫_[ℝ]) := by
        congr 1
        exact Finset.sum_congr rfl (fun x _ => (hInner x).2)
      _ = c * ∑' m : SchwartzMap.polarIntegerLattice (d := d) P.lattice,
          ∑ x : ↑(P.centers ∩ D), ∑ y : ↑(P.centers ∩ D),
            (𝓕 f m) * exp (2 * π * I *
              ⟪(x : EuclideanSpace ℝ (Fin d)) - (y : EuclideanSpace ℝ (Fin d)),
                (m : EuclideanSpace ℝ (Fin d))⟫_[ℝ]) :=
        congrArg (fun z : ℂ => c * z) hOuter
      _ = _ := by
        congr 1
        apply tsum_congr
        intro m
        simp only [mul_assoc, WithLp.ofLp_sub, Finset.mul_sum]
  have hRealCoeff (m : SchwartzMap.polarIntegerLattice (d := d) P.lattice) :
      (((𝓕 f m).re : ℝ) : ℂ) = 𝓕 f m :=
    hRealFourier (m : EuclideanSpace ℝ (Fin d))
  simpa [tsum_fintype, c, hRealCoeff] using congrArg Complex.re hExchange

end SpherePacking.CohnElkies

end

section

open scoped BigOperators
open scoped SchwartzMap

namespace SpherePacking.CohnElkies

variable {d : ℕ}

namespace LPBoundSummability

open SpherePacking.CohnElkies.LPBoundAux

section ZLattice

variable (Λ : Submodule ℤ (EuclideanSpace ℝ (Fin d))) [DiscreteTopology Λ]
variable (f : 𝓢(EuclideanSpace ℝ (Fin d), ℂ)) (a : EuclideanSpace ℝ (Fin d))

private theorem summable_lattice_shift_values :
    Summable (fun ℓ : Λ => f (a + (ℓ : EuclideanSpace ℝ (Fin d)))) :=
  Summable.of_norm (summable_norm_on_translated_integral_lattice (Λ := Λ) f a)

private theorem summable_lattice_shift_real_parts :
    Summable (fun ℓ : Λ => (f (a + (ℓ : EuclideanSpace ℝ (Fin d)))).re) :=
  Complex.reCLM.summable (summable_lattice_shift_values (Λ := Λ) f a)

end SpherePacking.CohnElkies.LPBoundSummability.ZLattice

end

section

namespace SpherePacking.CohnElkies

section

open scoped BigOperators SchwartzMap

variable {d : ℕ}

private noncomputable def fundamentalCentersLatticeProductEquiv (P : PeriodicSpherePacking d)
    {D : Set (EuclideanSpace ℝ (Fin d))}
    (hD_unique_covers : ∀ x, ∃! g : P.lattice, g +ᵥ x ∈ D) :
    (↑(P.centers ∩ D) × P.lattice) ≃ P.centers := by
  classical
  let E := EuclideanSpace ℝ (Fin d)
  refine
    { toFun := fun z =>
        ⟨(z.2 : E) + (z.1 : E),
          P.lattice_action z.2.property z.1.property.1⟩
      invFun := fun x =>
        let g := Classical.choose (hD_unique_covers (x : E))
        (⟨(g : E) + (x : E),
            P.lattice_action g.property x.property,
            (Classical.choose_spec (hD_unique_covers (x : E))).1⟩,
          -g)
      left_inv := ?_
      right_inv := ?_ }
  · rintro ⟨x, g⟩
    let k := Classical.choose (hD_unique_covers ((g : E) + (x : E)))
    have hk : k = -g := by
      symm
      apply (Classical.choose_spec
        (hD_unique_covers ((g : E) + (x : E)))).2
      simpa only [Submodule.vadd_def, NegMemClass.coe_neg, vadd_eq_add,
        neg_add_cancel_left] using x.property.2
    change
      (⟨(k : E) + ((g : E) + (x : E)), _⟩, -k) = (x, g)
    apply Prod.ext
    · apply Subtype.ext
      change (k : E) + ((g : E) + (x : E)) = (x : E)
      simp only [hk, NegMemClass.coe_neg, neg_add_cancel_left]
    · change -k = g
      simp only [hk, neg_neg]
  · intro x
    let g := Classical.choose (hD_unique_covers (x : E))
    change
      (⟨((-g : P.lattice) : E) + ((g : E) + (x : E)), _⟩ : P.centers) = x
    apply Subtype.ext
    simp only [NegMemClass.coe_neg, neg_add_cancel_left]

private lemma center_double_sum_eq_region_lattice_sum
    (f : 𝓢(EuclideanSpace ℝ (Fin d), ℂ))
    (P : PeriodicSpherePacking d)
    {D : Set (EuclideanSpace ℝ (Fin d))}
    (hD_isBounded : Bornology.IsBounded D)
    (hD_unique_covers : ∀ x, ∃! g : P.lattice, g +ᵥ x ∈ D)
    (hd : 0 < d) :
    ∑' (x : P.centers) (y : ↑(P.centers ∩ D)), (f (x - (y : EuclideanSpace ℝ (Fin d)))).re =
      ∑' (x : ↑(P.centers ∩ D)) (y : ↑(P.centers ∩ D)) (ℓ : P.lattice),
        (f ((x : EuclideanSpace ℝ (Fin d)) - (y : EuclideanSpace ℝ (Fin d)) +
          (ℓ : EuclideanSpace ℝ (Fin d)))).re := by
  classical
  let : Fintype ↑(P.centers ∩ D) :=
    @Fintype.ofFinite _
      (finite_centers_in_bounded_region P D hD_isBounded hd)
  let e := fundamentalCentersLatticeProductEquiv P hD_unique_covers
  have hs (x y : ↑(P.centers ∩ D)) :
      Summable (fun ℓ : P.lattice =>
        (f ((x : EuclideanSpace ℝ (Fin d)) -
          (y : EuclideanSpace ℝ (Fin d)) +
          (ℓ : EuclideanSpace ℝ (Fin d)))).re) :=
    LPBoundSummability.summable_lattice_shift_real_parts
      (Λ := P.lattice) f
      ((x : EuclideanSpace ℝ (Fin d)) - (y : EuclideanSpace ℝ (Fin d)))
  have hswap (x : ↑(P.centers ∩ D)) :
      Summable (fun ℓ : P.lattice => ∑' y : ↑(P.centers ∩ D),
        (f ((x : EuclideanSpace ℝ (Fin d)) -
          (y : EuclideanSpace ℝ (Fin d)) +
          (ℓ : EuclideanSpace ℝ (Fin d)))).re) ∧
      (∑' ℓ : P.lattice, ∑' y : ↑(P.centers ∩ D),
        (f ((x : EuclideanSpace ℝ (Fin d)) -
          (y : EuclideanSpace ℝ (Fin d)) +
          (ℓ : EuclideanSpace ℝ (Fin d)))).re) =
        ∑' y : ↑(P.centers ∩ D), ∑' ℓ : P.lattice,
          (f ((x : EuclideanSpace ℝ (Fin d)) -
            (y : EuclideanSpace ℝ (Fin d)) +
            (ℓ : EuclideanSpace ℝ (Fin d)))).re := by
    have haux (s : Finset ↑(P.centers ∩ D)) :
        Summable (fun ℓ : P.lattice => ∑ y ∈ s,
          (f ((x : EuclideanSpace ℝ (Fin d)) -
            (y : EuclideanSpace ℝ (Fin d)) +
            (ℓ : EuclideanSpace ℝ (Fin d)))).re) ∧
        (∑' ℓ : P.lattice, ∑ y ∈ s,
          (f ((x : EuclideanSpace ℝ (Fin d)) -
            (y : EuclideanSpace ℝ (Fin d)) +
            (ℓ : EuclideanSpace ℝ (Fin d)))).re) =
          ∑ y ∈ s, ∑' ℓ : P.lattice,
            (f ((x : EuclideanSpace ℝ (Fin d)) -
              (y : EuclideanSpace ℝ (Fin d)) +
              (ℓ : EuclideanSpace ℝ (Fin d)))).re := by
      induction s using Finset.induction_on with
      | empty => simp only [Finset.sum_empty, summable_zero, tsum_zero, and_self]
      | @insert y s hy ih =>
        constructor
        · simpa only [hy, not_false_eq_true, Finset.sum_insert] using
            (hs x y).add ih.1
        · simpa only [hy, not_false_eq_true, Finset.sum_insert, ih.2] using
            (hs x y).tsum_add ih.1
    constructor
    · simpa only [tsum_fintype] using (haux Finset.univ).1
    · simpa only [tsum_fintype] using (haux Finset.univ).2
  calc
    _ = ∑' z : ↑(P.centers ∩ D) × P.lattice,
          ∑' y : ↑(P.centers ∩ D),
            (f (((z.2 : P.lattice) : EuclideanSpace ℝ (Fin d)) +
              (z.1 : EuclideanSpace ℝ (Fin d)) -
              (y : EuclideanSpace ℝ (Fin d)))).re := by
      simpa only [tsum_fintype, fundamentalCentersLatticeProductEquiv,
        Subtype.forall, Equiv.coe_fn_mk, e] using
        (e.tsum_eq (f := fun x : P.centers =>
          ∑' y : ↑(P.centers ∩ D),
            (f ((x : EuclideanSpace ℝ (Fin d)) -
              (y : EuclideanSpace ℝ (Fin d)))).re)).symm
    _ = ∑' x : ↑(P.centers ∩ D), ∑' ℓ : P.lattice,
          ∑' y : ↑(P.centers ∩ D),
            (f ((x : EuclideanSpace ℝ (Fin d)) -
              (y : EuclideanSpace ℝ (Fin d)) +
              (ℓ : EuclideanSpace ℝ (Fin d)))).re := by
      let ep :
          (Σ _ : ↑(P.centers ∩ D), P.lattice) ≃
            (↑(P.centers ∩ D) × P.lattice) :=
        Equiv.sigmaEquivProd _ _
      have htotal :
          Summable (fun z : Σ _ : ↑(P.centers ∩ D), P.lattice =>
            ∑' y : ↑(P.centers ∩ D),
              (f ((z.1 : EuclideanSpace ℝ (Fin d)) -
                (y : EuclideanSpace ℝ (Fin d)) +
                ((z.2 : P.lattice) : EuclideanSpace ℝ (Fin d)))).re) := by
        let G : (Σ _ : ↑(P.centers ∩ D), P.lattice) → ℝ := fun z =>
          ∑' y : ↑(P.centers ∩ D),
            (f ((z.1 : EuclideanSpace ℝ (Fin d)) -
              (y : EuclideanSpace ℝ (Fin d)) +
              ((z.2 : P.lattice) : EuclideanSpace ℝ (Fin d)))).re
        change Summable G
        have hind (x : ↑(P.centers ∩ D)) :
            Summable
              (({z : Σ _ : ↑(P.centers ∩ D), P.lattice | z.1 = x}).indicator G) := by
          let ex : P.lattice ≃
              {z : Σ _ : ↑(P.centers ∩ D), P.lattice | z.1 = x} :=
            { toFun := fun ℓ => ⟨⟨x, ℓ⟩, rfl⟩
              invFun := fun z => z.val.2
              left_inv := fun _ => rfl
              right_inv := by
                intro z
                apply Subtype.ext
                cases z with
                | mk z hz =>
                  cases z with
                  | mk x' ℓ =>
                    cases hz
                    rfl }
          apply summable_subtype_iff_indicator.mp
          apply (ex.summable_iff).mp
          simpa only [G, ex, tsum_fintype, Set.mem_ofPred_eq, Function.comp_def,
            Equiv.coe_fn_mk] using (hswap x).1
        have hall := summable_sum (s := Finset.univ) (fun x _ => hind x)
        simpa only [Set.indicator, eq_comm, Set.mem_ofPred_eq,
          Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte] using hall
      calc
        _ = ∑' z : Σ _ : ↑(P.centers ∩ D), P.lattice,
              ∑' y : ↑(P.centers ∩ D),
                (f (((z.2 : P.lattice) : EuclideanSpace ℝ (Fin d)) +
                  (z.1 : EuclideanSpace ℝ (Fin d)) -
                  (y : EuclideanSpace ℝ (Fin d)))).re := by
          simpa only [tsum_fintype, Equiv.sigmaEquivProd_apply, ep] using
            (ep.tsum_eq (f := fun z : ↑(P.centers ∩ D) × P.lattice =>
              ∑' y : ↑(P.centers ∩ D),
                (f (((z.2 : P.lattice) : EuclideanSpace ℝ (Fin d)) +
                  (z.1 : EuclideanSpace ℝ (Fin d)) -
                  (y : EuclideanSpace ℝ (Fin d)))).re)).symm
        _ = ∑' z : Σ _ : ↑(P.centers ∩ D), P.lattice,
              ∑' y : ↑(P.centers ∩ D),
                (f ((z.1 : EuclideanSpace ℝ (Fin d)) -
                  (y : EuclideanSpace ℝ (Fin d)) +
                  ((z.2 : P.lattice) : EuclideanSpace ℝ (Fin d)))).re := by
          apply tsum_congr
          intro z
          apply tsum_congr
          intro y
          congr 2
          abel
        _ = _ :=
          Summable.tsum_sigma' (fun x => (hswap x).1) htotal
    _ = _ := by
      apply tsum_congr
      intro x
      exact (hswap x).2

end

end SpherePacking.CohnElkies

end

section

open scoped BigOperators SchwartzMap

namespace SpherePacking.CohnElkies

variable {d : ℕ}
variable {f : 𝓢(EuclideanSpace ℝ (Fin d), ℂ)}

section FundamentalDomain

variable {P : PeriodicSpherePacking d}
variable {D : Set (EuclideanSpace ℝ (Fin d))}

private lemma real_lattice_sum_bounded_by_origin_term (hP : P.separation = 1)
    (hD_unique_covers : ∀ x, ∃! g : P.lattice, g +ᵥ x ∈ D)
    (hCohnElkies₁ : ∀ x : EuclideanSpace ℝ (Fin d), ‖x‖ ≥ 1 → (f x).re ≤ 0)
    (x y : ↑(P.centers ∩ D)) :
    (∑' ℓ : P.lattice,
          (f ((x : EuclideanSpace ℝ (Fin d)) - (y : EuclideanSpace ℝ (Fin d)) +
            (ℓ : EuclideanSpace ℝ (Fin d)))).re)
      ≤ ite (x = y) (f 0).re 0 := by
  classical
  let E := EuclideanSpace ℝ (Fin d)
  have hsum :
      Summable (fun ℓ : P.lattice =>
        (f ((x : E) - (y : E) + (ℓ : E))).re) :=
    SpherePacking.CohnElkies.LPBoundSummability.summable_lattice_shift_real_parts
      (Λ := P.lattice) (f := f) ((x : E) - (y : E))
  have hnonpos (ℓ : P.lattice)
      (hne : (ℓ : E) + (x : E) ≠ (y : E)) :
      (f ((x : E) - (y : E) + (ℓ : E))).re ≤ 0 := by
    have hcenter : (ℓ : E) + (x : E) ∈ P.centers :=
      P.lattice_action ℓ.property x.property.1
    have hdist : 1 ≤ dist ((ℓ : E) + (x : E)) (y : E) := by
      rw [← hP]
      exact P.toSpherePacking.distinct_centers_separation_bound
        ((ℓ : E) + (x : E)) (y : E) hcenter y.property.1 hne
    apply hCohnElkies₁
    simpa only [sub_eq_add_neg, add_comm, add_left_comm, ge_iff_le, dist_eq_norm, add_assoc]
      using hdist
  by_cases hxy : x = y
  · subst y
    simp only []
    have hmajor :
        Summable (fun ℓ : P.lattice =>
          if ℓ = 0 then (f 0).re else 0) := by
      apply summable_of_ne_finset_zero (s := {0})
      intro ℓ hℓ
      have hne : ℓ ≠ 0 := by
        intro hzero
        exact hℓ (by simp only [hzero, Finset.mem_singleton])
      simp only [hne, ↓reduceIte]
    calc
      (∑' ℓ : P.lattice,
        (f ((x : E) - (x : E) + (ℓ : E))).re)
          ≤ ∑' ℓ : P.lattice, if ℓ = 0 then (f 0).re else 0 := by
            apply Summable.tsum_le_tsum (hf := hsum) (hg := hmajor)
            intro ℓ
            by_cases hℓ : ℓ = 0
            · simp only [sub_self, hℓ, ZeroMemClass.coe_zero, add_zero, ↓reduceIte, Std.le_refl]
            · simp only [ite_eq_right hℓ]
              apply hnonpos ℓ
              intro heq
              apply hℓ
              apply Subtype.ext
              have hz := congrArg (fun z : E => z - (x : E)) heq
              simpa only [ZeroMemClass.coe_zero, ZeroMemClass.coe_eq_zero, add_sub_cancel_right,
                sub_self] using hz
      _ = (f 0).re := by simp only [tsum_ite_eq]
  · simp only [ite_eq_right hxy]
    have hterms (ℓ : P.lattice) :
        (f ((x : E) - (y : E) + (ℓ : E))).re ≤ 0 := by
      apply hnonpos ℓ
      intro heq
      have hℓD : ℓ +ᵥ (x : E) ∈ D := by
        change (ℓ : E) + (x : E) ∈ D
        rw [heq]
        exact y.property.2
      have hzeroD : (0 : P.lattice) +ᵥ (x : E) ∈ D := by
        simpa only [zero_vadd] using x.property.2
      have hℓ : ℓ = (0 : P.lattice) :=
        (hD_unique_covers (x : E)).unique hℓD hzeroD
      apply hxy
      apply Subtype.ext
      simpa only [hℓ, ZeroMemClass.coe_zero, zero_add] using heq
    simpa only [ge_iff_le, tsum_zero] using
      (Summable.tsum_le_tsum hterms hsum
        (summable_zero : Summable (fun _ : P.lattice => (0 : ℝ))))

end FundamentalDomain

end SpherePacking.CohnElkies

end

section

open scoped FourierTransform ENNReal SchwartzMap BigOperators
open SpherePacking MeasureTheory Complex Real Bornology Module

variable {d : ℕ}

variable {f : 𝓢(EuclideanSpace ℝ (Fin d), ℂ)} (hne_zero : f ≠ 0)

variable (hReal : ∀ x : EuclideanSpace ℝ (Fin d), ↑(f x).re = (f x))

variable (hRealFourier : ∀ x : EuclideanSpace ℝ (Fin d), ↑(𝓕 f x).re = (𝓕 f x))

variable (hCohnElkies₁ : ∀ x : EuclideanSpace ℝ (Fin d), ‖x‖ ≥ 1 → (f x).re ≤ 0)
variable (hCohnElkies₂ : ∀ x : EuclideanSpace ℝ (Fin d), (𝓕 f x).re ≥ 0)

section Complex_Function_Helpers

end Complex_Function_Helpers

section Nonnegativity

private theorem fourier_transform_is_integrable : MeasureTheory.Integrable (𝓕 ⇑f) :=
  ((FourierTransform.fourierCLE ℝ (SchwartzMap (EuclideanSpace ℝ (Fin d)) ℂ)) f).integrable

include hne_zero in
private theorem fourier_transform_nonzero : 𝓕 f ≠ 0 := by
  intro hFourierZero
  apply hne_zero
  rw [← ContinuousLinearEquiv.map_eq_zero_iff (FourierTransform.fourierCLE ℝ _)]
  exact hFourierZero

include hCohnElkies₂ in
private theorem test_function_nonnegative_at_origin : 0 ≤ (f 0).re := by
  rw [← f.schwartz_fourier_inverse_identity, fourierInv_eq]
  simp only [inner_zero_right, AddChar.map_zero_eq_one, one_smul]
  rw [← RCLike.re_eq_complex_re, ← integral_re fourier_transform_is_integrable]
  refine integral_nonneg ?_
  intro v
  simpa only [Pi.zero_apply, RCLike.re_to_complex, ge_iff_le] using! hCohnElkies₂ v

include hReal hRealFourier hCohnElkies₂ hne_zero in
private theorem test_function_positive_at_origin : 0 < (f 0).re := by
  have h0 : 0 ≤ (f 0).re := test_function_nonnegative_at_origin (f := f) hCohnElkies₂
  refine lt_of_le_of_ne h0 ?_
  intro hf0re
  have hf0 : f 0 = 0 := by
    simpa only [hf0re.symm, ofReal_zero] using! (hReal 0).symm
  have hint0 : (∫ v : EuclideanSpace ℝ (Fin d), 𝓕 (⇑f) v) = 0 := by
    have hInv : 𝓕⁻ (𝓕 ⇑f) 0 = f 0 :=
      congrArg (fun g : EuclideanSpace ℝ (Fin d) → ℂ => g 0) (f.schwartz_fourier_inverse_identity)
    simpa only [fourierInv_eq, inner_zero_right, AddChar.map_zero_eq_one, one_smul, hf0] using! hInv
  have hintRe : ∫ v : EuclideanSpace ℝ (Fin d), (𝓕 (⇑f) v).re = 0 := by
    have : (∫ v : EuclideanSpace ℝ (Fin d), 𝓕 (⇑f) v).re = 0 := by
      simpa only [zero_re] using! congrArg Complex.re hint0
    have hre :
        (∫ v : EuclideanSpace ℝ (Fin d), (𝓕 (⇑f) v).re) =
          (∫ v : EuclideanSpace ℝ (Fin d), 𝓕 (⇑f) v).re := by
      simpa only [RCLike.re_to_complex] using!
        (integral_re (f := fun v : EuclideanSpace ℝ (Fin d) => 𝓕 (⇑f) v)
          fourier_transform_is_integrable)
    exact hre.trans this
  have hcont : Continuous (fun x : EuclideanSpace ℝ (Fin d) => (𝓕 f x).re) := by
    fun_prop
  have hfun : (fun x : EuclideanSpace ℝ (Fin d) => (𝓕 f x).re) = 0 := by
    refine (Continuous.nonnegative_integral_vanishes_iff_function_vanishes hcont ?_
      hCohnElkies₂).1 ?_
    · have h𝓕_int : MeasureTheory.Integrable
          (fun x : EuclideanSpace ℝ (Fin d) => 𝓕 f x) := by
        rw [← FourierTransform.fourierCLE_apply (R := ℝ)
          (E := 𝓢(EuclideanSpace ℝ (Fin d), ℂ)) f]
        exact ((FourierTransform.fourierCLE ℝ (SchwartzMap (EuclideanSpace ℝ (Fin d)) ℂ))
          f).integrable
      exact h𝓕_int.re
    simpa only  using! hintRe
  have h𝓕fzero : 𝓕 f = 0 := by
    ext x
    have hx : (𝓕 f x).re = 0 := by simpa only [Pi.zero_apply] using! congrArg (fun g => g x) hfun
    simpa only [zero_apply, hx, ofReal_zero] using! (hRealFourier x).symm
  exact fourier_transform_nonzero hne_zero h𝓕fzero

end Nonnegativity

section Fundamental_Domain_Dependent

variable {P : PeriodicSpherePacking d} (hP : P.separation = 1) [Nonempty P.centers]
variable {D : Set (EuclideanSpace ℝ (Fin d))} (hD_isBounded : IsBounded D)
variable (hD_unique_covers : ∀ x, ∃! g : P.lattice, g +ᵥ x ∈ D) (hD_measurable : MeasurableSet D)

omit [Nonempty P.centers] in
include hP hCohnElkies₁ in
open Classical in
private theorem packing_bound_auxiliary_estimate (hd : 0 < d)
    (hD_unique_covers : ∀ x, ∃! g : P.lattice, g +ᵥ x ∈ D) :
    ∑' x : P.centers, ∑' y : ↑(P.centers ∩ D), (f (x - (y : EuclideanSpace ℝ (Fin d)))).re
      ≤ ↑(P.boundedCenterRepresentativeCount hd hD_isBounded) * (f 0).re := by
  let := P.instFintypeBoundedCenterRepresentatives hd hD_isBounded
  rw [SpherePacking.CohnElkies.center_double_sum_eq_region_lattice_sum
    f P hD_isBounded hD_unique_covers hd]
  simp_rw [tsum_fintype]
  calc
    (∑ x : ↑(P.centers ∩ D), ∑ y : ↑(P.centers ∩ D),
      ∑' ℓ : P.lattice,
        (f ((x : EuclideanSpace ℝ (Fin d)) -
          (y : EuclideanSpace ℝ (Fin d)) +
            (ℓ : EuclideanSpace ℝ (Fin d)))).re)
      ≤ ∑ x : ↑(P.centers ∩ D), ∑ y : ↑(P.centers ∩ D),
          ite (x = y) (f 0).re 0 := by
            exact Finset.sum_le_sum fun x _ =>
              Finset.sum_le_sum fun y _ =>
                SpherePacking.CohnElkies.real_lattice_sum_bounded_by_origin_term
                  hP hD_unique_covers hCohnElkies₁ x y
    _ = ↑(P.boundedCenterRepresentativeCount hd hD_isBounded) *
          (f 0).re := by
            simp only [Finset.sum_ite_eq, Finset.mem_univ, ↓reduceIte, Finset.sum_const,
              Finset.card_univ,
              Set.fintypeCard_eq_ncard, nsmul_eq_mul,
                PeriodicSpherePacking.boundedCenterRepresentativeCount]

omit [Nonempty ↑P.centers] in
include hD_isBounded in
private lemma packing_bound_complete_estimate_refined (hd : 0 < d) :
    ∑' (x : ↑(P.centers ∩ D)) (y : ↑(P.centers ∩ D)) (ℓ : ↥P.lattice), (f (↑x - ↑y + ↑ℓ)).re =
    (∑' (x : ↑(P.centers ∩ D)) (y : ↑(P.centers ∩ D)) (ℓ : ↥P.lattice), f (↑x - ↑y + ↑ℓ)).re := by
  have : Finite ↑(P.centers ∩ D) := finite_centers_in_bounded_region P D hD_isBounded hd
  rw [re_tsum Summable.of_finite]
  refine tsum_congr fun x => ?_
  rw [re_tsum Summable.of_finite]
  refine tsum_congr fun y => ?_
  simpa only [sub_eq_add_neg, add_comm, add_left_comm] using!
    (re_tsum
        (SpherePacking.CohnElkies.LPBoundSummability.summable_lattice_shift_values (Λ := P.lattice)
          (f := f) (a := (↑x - ↑y : EuclideanSpace ℝ (Fin d))))).symm

omit [Nonempty P.centers] in
include d f hP hne_zero hReal hRealFourier hCohnElkies₁ hCohnElkies₂ hD_unique_covers in
omit hne_zero hReal hCohnElkies₂ in
private theorem packing_bound_geometric_estimate (hd : 0 < d) :
    ↑(P.boundedCenterRepresentativeCount hd hD_isBounded) * (f 0).re ≥
      (1 / ZLattice.covolume P.lattice volume) *
        ∑' m : SchwartzMap.polarIntegerLattice (d := d) P.lattice,
          (𝓕 ⇑f m).re *
            (norm (∑' x : ↑(P.centers ∩ D),
              exp (2 * π * I *
                ⟪↑x, (m : EuclideanSpace ℝ (Fin d))⟫_[ℝ])) ^ 2) := by
  classical
  let : Fintype ↑(P.centers ∩ D) :=
    P.instFintypeBoundedCenterRepresentatives hd hD_isBounded
  have hcharacter (x y : ↑(P.centers ∩ D))
      (m : SchwartzMap.polarIntegerLattice (d := d) P.lattice) :
      exp (2 * π * I *
          ⟪(x : EuclideanSpace ℝ (Fin d)) - (y : EuclideanSpace ℝ (Fin d)),
            (m : EuclideanSpace ℝ (Fin d))⟫_[ℝ]) =
        exp (2 * π * I *
          ⟪(x : EuclideanSpace ℝ (Fin d)),
            (m : EuclideanSpace ℝ (Fin d))⟫_[ℝ]) *
          (starRingEnd ℂ)
            (exp (2 * π * I *
              ⟪(y : EuclideanSpace ℝ (Fin d)),
                (m : EuclideanSpace ℝ (Fin d))⟫_[ℝ])) := by
    have hinner :
        ⟪(x : EuclideanSpace ℝ (Fin d)) - (y : EuclideanSpace ℝ (Fin d)),
          (m : EuclideanSpace ℝ (Fin d))⟫_[ℝ] =
          ⟪(x : EuclideanSpace ℝ (Fin d)),
            (m : EuclideanSpace ℝ (Fin d))⟫_[ℝ] -
          ⟪(y : EuclideanSpace ℝ (Fin d)),
            (m : EuclideanSpace ℝ (Fin d))⟫_[ℝ] := by
      simpa only [← RCLike.inner_eq_wInner_one] using
        (inner_sub_left
          (x : EuclideanSpace ℝ (Fin d))
          (y : EuclideanSpace ℝ (Fin d))
          (m : EuclideanSpace ℝ (Fin d)))
    rw [hinner]
    have hsplit :
        (2 * (π : ℂ) * I *
          ((⟪(x : EuclideanSpace ℝ (Fin d)),
              (m : EuclideanSpace ℝ (Fin d))⟫_[ℝ] -
            ⟪(y : EuclideanSpace ℝ (Fin d)),
              (m : EuclideanSpace ℝ (Fin d))⟫_[ℝ] : ℝ) : ℂ)) =
          2 * (π : ℂ) * I *
            (⟪(x : EuclideanSpace ℝ (Fin d)),
              (m : EuclideanSpace ℝ (Fin d))⟫_[ℝ] : ℂ) +
            -(2 * (π : ℂ) * I *
              (⟪(y : EuclideanSpace ℝ (Fin d)),
                (m : EuclideanSpace ℝ (Fin d))⟫_[ℝ] : ℂ)) := by
      push_cast
      ring
    rw [hsplit, Complex.exp_add,
      Complex.negative_imaginary_exponential_eq_conjugate]
  have hfactor
      (m : SchwartzMap.polarIntegerLattice (d := d) P.lattice) :
      (∑' x : ↑(P.centers ∩ D),
        ∑' y : ↑(P.centers ∩ D),
          exp (2 * π * I *
            ⟪(x : EuclideanSpace ℝ (Fin d)) -
                (y : EuclideanSpace ℝ (Fin d)),
              (m : EuclideanSpace ℝ (Fin d))⟫_[ℝ])) =
        (norm (∑' x : ↑(P.centers ∩ D),
          exp (2 * π * I *
            ⟪(x : EuclideanSpace ℝ (Fin d)),
              (m : EuclideanSpace ℝ (Fin d))⟫_[ℝ])) ^ 2 : ℝ) := by
    simp_rw [tsum_fintype, hcharacter]
    calc
      _ =
          (∑ x : ↑(P.centers ∩ D),
            exp (2 * π * I *
              ⟪(x : EuclideanSpace ℝ (Fin d)),
                (m : EuclideanSpace ℝ (Fin d))⟫_[ℝ])) *
            (∑ y : ↑(P.centers ∩ D),
              (starRingEnd ℂ)
                (exp (2 * π * I *
                  ⟪(y : EuclideanSpace ℝ (Fin d)),
                    (m : EuclideanSpace ℝ (Fin d))⟫_[ℝ]))) := by
            symm
            rw [Finset.sum_mul]
            apply Finset.sum_congr rfl
            intro x hx
            rw [Finset.mul_sum]
      _ =
          (∑ x : ↑(P.centers ∩ D),
            exp (2 * π * I *
              ⟪(x : EuclideanSpace ℝ (Fin d)),
                (m : EuclideanSpace ℝ (Fin d))⟫_[ℝ])) *
            (starRingEnd ℂ)
              (∑ y : ↑(P.centers ∩ D),
                exp (2 * π * I *
                  ⟪(y : EuclideanSpace ℝ (Fin d)),
                    (m : EuclideanSpace ℝ (Fin d))⟫_[ℝ])) := by
            rw [map_sum]
      _ = _ := by
        rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]
  have hFourierNorm :
      Summable (fun m : SchwartzMap.polarIntegerLattice (d := d) P.lattice =>
        ‖(𝓕 f) (m : EuclideanSpace ℝ (Fin d))‖) := by
    simpa only [zero_add] using
      (SpherePacking.CohnElkies.LPBoundAux.summable_norm_on_translated_integral_lattice
        (SchwartzMap.polarIntegerLattice (d := d) P.lattice) (𝓕 f)
        (0 : EuclideanSpace ℝ (Fin d)))
  have hWeighted (x y : ↑(P.centers ∩ D)) :
      Summable (fun m : SchwartzMap.polarIntegerLattice (d := d) P.lattice =>
        (𝓕 f m) * exp (2 * π * I *
          ⟪(x : EuclideanSpace ℝ (Fin d)) - (y : EuclideanSpace ℝ (Fin d)),
            (m : EuclideanSpace ℝ (Fin d))⟫_[ℝ])) := by
    apply Summable.of_norm
    simpa only [mul_assoc, WithLp.ofLp_sub, Complex.norm_mul, norm_exp, mul_re, re_ofNat,
      ofReal_re, I_re,
      zero_mul, I_im, ofReal_im, mul_zero, sub_self, mul_im, one_mul, zero_add, im_ofNat,
        add_zero, Real.exp_zero,
      mul_one] using hFourierNorm
  have hFull :
      Summable (fun m : SchwartzMap.polarIntegerLattice (d := d) P.lattice =>
        ∑ x : ↑(P.centers ∩ D), ∑ y : ↑(P.centers ∩ D),
          (𝓕 f m) * exp (2 * π * I *
            ⟪(x : EuclideanSpace ℝ (Fin d)) -
                (y : EuclideanSpace ℝ (Fin d)),
              (m : EuclideanSpace ℝ (Fin d))⟫_[ℝ])) :=
    summable_sum fun x _ => summable_sum fun y _ => hWeighted x y
  have hSpectral :
      Summable (fun m : SchwartzMap.polarIntegerLattice (d := d) P.lattice =>
        ((𝓕 f m).re : ℂ) *
          (norm (∑' x : ↑(P.centers ∩ D),
            exp (2 * π * I *
              ⟪(x : EuclideanSpace ℝ (Fin d)),
                (m : EuclideanSpace ℝ (Fin d))⟫_[ℝ])) ^ 2 : ℝ)) := by
    refine (summable_congr ?_).mp hFull
    intro m
    rw [← hRealFourier (m : EuclideanSpace ℝ (Fin d)),
      ← hfactor m]
    simp only [WithLp.ofLp_sub, ofReal_re, tsum_fintype, Finset.mul_sum]
  have hgeom :
      (∑' (x : ↑(P.centers ∩ D)) (y : ↑(P.centers ∩ D))
        (ℓ : ↥P.lattice), (f (↑x - ↑y + ↑ℓ)).re) =
        (1 / ZLattice.covolume P.lattice volume) *
          ∑' m : SchwartzMap.polarIntegerLattice (d := d) P.lattice,
            (𝓕 ⇑f m).re *
              (norm (∑' x : ↑(P.centers ∩ D),
                exp (2 * π * I *
                  ⟪↑x, (m : EuclideanSpace ℝ (Fin d))⟫_[ℝ])) ^ 2) := by
    rw [packing_bound_complete_estimate_refined hD_isBounded hd]
    simp_rw [SchwartzMap.latticePoissonSummationFormula P.lattice f]
    simp_rw [← SchwartzMap.fourier_coe]
    rw [SpherePacking.CohnElkies.packing_spectral_sum_exchange
      f hRealFourier P hD_isBounded hd]
    simp_rw [hfactor]
    have hcov :
        (1 / (ZLattice.covolume P.lattice volume : ℂ)) =
          ((1 / ZLattice.covolume P.lattice volume : ℝ) : ℂ) := by
      norm_cast
    rw [hcov, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
      zero_mul, sub_zero, Complex.re_tsum hSpectral]
    congr 1
    apply tsum_congr
    intro m
    simp only [pow_two, Complex.mul_re, Complex.ofReal_re,
      Complex.ofReal_im, mul_zero, sub_zero]
  have hbound := packing_bound_auxiliary_estimate
    (f := f) hCohnElkies₁ hP hD_isBounded hd hD_unique_covers
  rw [SpherePacking.CohnElkies.center_double_sum_eq_region_lattice_sum
    (f := f) (P := P) (D := D) hD_isBounded hD_unique_covers hd] at hbound
  linarith [hgeom]

include d f hP hne_zero hReal hRealFourier hCohnElkies₁ hCohnElkies₂ in
omit hne_zero hReal hRealFourier hCohnElkies₁ hP [Nonempty ↑P.centers] in
private theorem packing_bound_spectral_estimate (hd : 0 < d) :
    (1 / ZLattice.covolume P.lattice volume) *
        ∑' m : SchwartzMap.polarIntegerLattice (d := d) P.lattice,
          (𝓕 ⇑f m).re *
            (norm (∑' x : ↑(P.centers ∩ D),
              exp (2 * π * I *
                ⟪↑x, (m : EuclideanSpace ℝ (Fin d))⟫_[ℝ])) ^ 2)
      ≥
      ↑(P.boundedCenterRepresentativeCount hd hD_isBounded) ^ 2 * (𝓕 f 0).re / ZLattice.covolume
        P.lattice volume := by
  classical
  let := P.instFintypeBoundedCenterRepresentatives hd hD_isBounded
  let N : ℝ := P.boundedCenterRepresentativeCount hd hD_isBounded
  let F : SchwartzMap.polarIntegerLattice (d := d) P.lattice → ℝ :=
    fun m =>
      (𝓕 ⇑f m).re *
        (norm (∑' x : ↑(P.centers ∩ D),
          exp (2 * π * I *
            ⟪↑x, (m : EuclideanSpace ℝ (Fin d))⟫_[ℝ])) ^ 2)
  have hFourierNorm :
      Summable (fun m : SchwartzMap.polarIntegerLattice (d := d) P.lattice =>
        ‖(𝓕 f) (m : EuclideanSpace ℝ (Fin d))‖) := by
    simpa only [zero_add] using
      (SpherePacking.CohnElkies.LPBoundAux.summable_norm_on_translated_integral_lattice
        (SchwartzMap.polarIntegerLattice (d := d) P.lattice) (𝓕 f)
        (0 : EuclideanSpace ℝ (Fin d)))
  have hCharacterBound (m : SchwartzMap.polarIntegerLattice (d := d) P.lattice) :
      norm (∑' x : ↑(P.centers ∩ D),
        exp (2 * π * I *
          ⟪↑x, (m : EuclideanSpace ℝ (Fin d))⟫_[ℝ])) ≤ N := by
    rw [tsum_fintype]
    calc
      _ ≤ ∑ x : ↑(P.centers ∩ D),
        ‖exp (2 * π * I *
          ⟪(x : EuclideanSpace ℝ (Fin d)),
            (m : EuclideanSpace ℝ (Fin d))⟫_[ℝ])‖ := norm_sum_le _ _
      _ = N := by
        simp only [mul_assoc, norm_exp, mul_re, re_ofNat, ofReal_re, I_re, zero_mul, I_im,
          ofReal_im, mul_zero,
          sub_self, mul_im, one_mul, zero_add, im_ofNat, add_zero, Real.exp_zero,
            Finset.sum_const, Finset.card_univ,
          Set.fintypeCard_eq_ncard, nsmul_eq_mul, mul_one,
            PeriodicSpherePacking.boundedCenterRepresentativeCount, N]
  have hFnonneg (m : SchwartzMap.polarIntegerLattice (d := d) P.lattice) :
      0 ≤ F m := by
    exact mul_nonneg (hCohnElkies₂ _) (sq_nonneg _)
  have hFsummable : Summable F := by
    refine Summable.of_nonneg_of_le hFnonneg (fun m => ?_)
      (hFourierNorm.mul_left (N ^ 2))
    have hcoeff :
        (𝓕 ⇑f (m : EuclideanSpace ℝ (Fin d))).re ≤
          ‖(𝓕 f) (m : EuclideanSpace ℝ (Fin d))‖ := by
      exact (le_abs_self _).trans
        (Complex.abs_re_le_norm ((𝓕 f) (m : EuclideanSpace ℝ (Fin d))))
    have hsq :
        norm (∑' x : ↑(P.centers ∩ D),
          exp (2 * π * I *
            ⟪↑x, (m : EuclideanSpace ℝ (Fin d))⟫_[ℝ])) ^ 2 ≤ N ^ 2 := by
      have hN : 0 ≤ N := by
        dsimp [N]
        positivity
      nlinarith [hCharacterBound m, norm_nonneg
        (∑' x : ↑(P.centers ∩ D),
          exp (2 * π * I *
            ⟪↑x, (m : EuclideanSpace ℝ (Fin d))⟫_[ℝ]))]
    change _ ≤ N ^ 2 * ‖(𝓕 f) (m : EuclideanSpace ℝ (Fin d))‖
    simpa [F, mul_comm] using
      (mul_le_mul hcoeff hsq (sq_nonneg _) (norm_nonneg _))
  have htail :
      0 ≤ ∑' m : SchwartzMap.polarIntegerLattice (d := d) P.lattice,
        if m = 0 then 0 else F m := by
    exact SpherePacking.CohnElkies.nonnegative_weighted_nonzero_frequency_sum
      f P D hCohnElkies₂
  have horigin :
      F (0 : SchwartzMap.polarIntegerLattice (d := d) P.lattice) =
        (𝓕 f 0).re * N ^ 2 := by
    change (𝓕 f (0 : EuclideanSpace ℝ (Fin d))).re *
      norm (∑' x : ↑(P.centers ∩ D),
        exp (2 * π * I *
          ⟪↑x, (0 : EuclideanSpace ℝ (Fin d))⟫_[ℝ])) ^ 2 =
      (𝓕 f 0).re * N ^ 2
    rw [SpherePacking.CohnElkies.origin_character_sum_norm_sq_eq_orbit_count_sq
      P hd hD_isBounded]
  have hsum : (𝓕 f 0).re * N ^ 2 ≤ ∑' m, F m := by
    rw [hFsummable.tsum_eq_add_tsum_ite 0, horigin]
    linarith
  have hcovol : 0 ≤ ZLattice.covolume P.lattice volume := by
    rw [SchwartzMap.lattice_covolume_eq_coordinate_determinant]
    exact abs_nonneg _
  have hscaled := mul_le_mul_of_nonneg_left hsum
    (by positivity : 0 ≤ (1 / ZLattice.covolume P.lattice volume : ℝ))
  simpa [F, N, div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using hscaled

omit [Nonempty P.centers] in
include d f hP hne_zero hReal hRealFourier hCohnElkies₁ hCohnElkies₂ hD_unique_covers in
omit hne_zero hReal in
private theorem packing_bound_complete_estimate (hd : 0 < d) :
    ↑(P.boundedCenterRepresentativeCount hd hD_isBounded) * (f 0).re ≥
      ↑(P.boundedCenterRepresentativeCount hd hD_isBounded) ^ 2 *
      (𝓕 f 0).re / ZLattice.covolume P.lattice volume := by
  exact
    (packing_bound_spectral_estimate (P := P) hCohnElkies₂ hD_isBounded hd).trans
      (packing_bound_geometric_estimate hRealFourier hCohnElkies₁ hP
        hD_isBounded hD_unique_covers hd)

end Fundamental_Domain_Dependent

section Main_Theorem_For_One_Packing

variable {P : PeriodicSpherePacking d} (hP : P.separation = 1) [Nonempty P.centers]
variable {D : Set (EuclideanSpace ℝ (Fin d))} (hD_isBounded : IsBounded D)
variable (hD_unique_covers : ∀ x, ∃! g : P.lattice, g +ᵥ x ∈ D)

include d f hne_zero hReal hRealFourier hCohnElkies₁ hCohnElkies₂ P hP D hD_isBounded
  hD_unique_covers

private theorem LinearProgrammingBound' (hd : 0 < d) :
  P.upperPackingDensity ≤ (f 0).re.toNNReal / (𝓕 f 0).re.toNNReal *
  volume (Metric.ball (0 : EuclideanSpace ℝ (Fin d)) (1 / 2)) := by
  classical
  let : Nonempty (Fin d) := Fin.pos_iff_nonempty.mp hd
  have hfunction : 0 < (f 0).re :=
    test_function_positive_at_origin hne_zero hReal hRealFourier hCohnElkies₂
  have hball :
      volume (Metric.ball (0 : EuclideanSpace ℝ (Fin d)) (1 / 2)) ≠ 0 :=
    (EuclideanSpace.euclidean_ball_volume_positive (0 : EuclideanSpace ℝ (Fin d))
      (by norm_num : (0 : ℝ) < 1 / 2)).ne'
  have hball_inv :
      volume (Metric.ball (0 : EuclideanSpace ℝ (Fin d)) (2 : ℝ)⁻¹) ≠ 0 := by
    simpa only [one_div] using hball
  by_cases hfourier_zero : (𝓕 f 0).re = 0
  · simp only [hfourier_zero, toNNReal_zero, ENNReal.coe_zero, div_eq_mul_inv, ENNReal.inv_zero,
    ne_eq,
      ENNReal.coe_eq_zero, (Real.toNNReal_pos.mpr hfunction).ne', not_false_eq_true,
        ENNReal.mul_top, one_mul, hball_inv,
      ENNReal.top_mul, le_top]
  · have hfourier : 0 < (𝓕 f 0).re :=
      lt_of_le_of_ne (hCohnElkies₂ 0) (Ne.symm hfourier_zero)
    have hcount_nat : 0 < P.centerOrbitCardinality := by
      unfold PeriodicSpherePacking.centerOrbitCardinality
      exact Fintype.card_pos_iff.mpr
        ⟨Quotient.mk _ (Classical.choice (inferInstance : Nonempty P.centers))⟩
    have hcount :
        0 < (P.boundedCenterRepresentativeCount hd hD_isBounded : ℝ) := by
      rw [← P.orbit_cardinality_eq_bounded_representatives hd hD_isBounded
        hD_unique_covers]
      exact_mod_cast hcount_nat
    have hcovolume : 0 < ZLattice.covolume P.lattice volume := by
      rw [SchwartzMap.lattice_covolume_eq_coordinate_determinant]
      apply abs_pos.mpr
      intro hdet
      let e := SchwartzMap.latticeCoordinateEquiv P.lattice
      have hcomp : e.toLinearMap * e.symm.toLinearMap = 1 := by
        ext x
        simp only [End.mul_apply, LinearEquiv.coe_coe, LinearEquiv.apply_symm_apply, End.one_apply]
      have hdetcomp := congrArg
        (LinearMap.det :
          ((EuclideanSpace ℝ (Fin d)) →ₗ[ℝ]
            (EuclideanSpace ℝ (Fin d))) →* ℝ) hcomp
      simp only [map_mul, hdet, zero_mul, map_one, zero_ne_one, e] at hdetcomp
    have hestimate :=
      packing_bound_complete_estimate (f := f) hRealFourier hCohnElkies₁
        hCohnElkies₂ hP hD_isBounded hD_unique_covers hd
    have hscaled :
        (P.boundedCenterRepresentativeCount hd hD_isBounded : ℝ) ^ 2 *
            (𝓕 f 0).re ≤
          ((P.boundedCenterRepresentativeCount hd hD_isBounded : ℝ) *
            (f 0).re) * ZLattice.covolume P.lattice volume :=
      (div_le_iff₀ hcovolume).mp hestimate
    have hcancel :
        (P.boundedCenterRepresentativeCount hd hD_isBounded : ℝ) *
            (𝓕 f 0).re ≤
          (f 0).re * ZLattice.covolume P.lattice volume := by
      apply le_of_mul_le_mul_left _ hcount
      simpa only [mul_comm, pow_two, mul_assoc, mul_left_comm] using hscaled
    have hreal :
        (P.boundedCenterRepresentativeCount hd hD_isBounded : ℝ) /
            ZLattice.covolume P.lattice volume ≤
          (f 0).re / (𝓕 f 0).re :=
      (div_le_div_iff₀ hcovolume hfourier).mpr hcancel
    have hnonnegative := ENNReal.ofReal_le_ofReal hreal
    rw [ENNReal.ofReal_div_of_pos hcovolume,
      ENNReal.ofReal_div_of_pos hfourier] at hnonnegative
    have hnonnegative' :
      (P.boundedCenterRepresentativeCount hd hD_isBounded : ℝ≥0∞) /
          (ZLattice.covolume P.lattice volume).toNNReal ≤
        (f 0).re.toNNReal / (𝓕 f 0).re.toNNReal := by
      simpa only [ENNReal.ofReal, toNNReal_natCast, ENNReal.coe_natCast] using hnonnegative
    rw [P.density_eq_numReps_mul_volume_ball_div_covolume hd, hP,
      P.orbit_cardinality_eq_bounded_representatives hd hD_isBounded
        hD_unique_covers]
    simpa only [ENat.toENNReal_coe, div_eq_mul_inv, one_mul, mul_comm, mul_left_comm, mul_assoc,
      ge_iff_le] using
      mul_le_mul_left hnonnegative'
        (volume (Metric.ball (0 : EuclideanSpace ℝ (Fin d)) (1 / 2)))

end Main_Theorem_For_One_Packing

section Main_Theorem

include d f hne_zero hReal hRealFourier hCohnElkies₁ hCohnElkies₂

private theorem LinearProgrammingBound (hd : 0 < d) : SpherePackingConstant d ≤
  (f 0).re.toNNReal / (𝓕 ⇑f 0).re.toNNReal *
    volume (Metric.ball (0 : EuclideanSpace ℝ (Fin d)) (1 / 2))
  := by
  rw [← periodic_packing_supremum_eq_unrestricted hd,
    periodic_packing_supremum_eq_unit_separation (d := d)]
  refine iSup_le fun P => ?_
  refine iSup_le fun hP => ?_
  cases isEmpty_or_nonempty ↑P.centers with
  | inl instEmpty =>
      simp only [P.packing_density_zero_of_empty_centers hd, one_div, zero_le]
  | inr instNonempty =>
      let b : Basis (Fin d) ℤ ↥P.lattice :=
        ((ZLattice.module_free ℝ P.lattice).chooseBasis).reindex
          (PeriodicSpherePacking.coordinateIndexEquiv P)
      exact LinearProgrammingBound' hne_zero hReal hRealFourier hCohnElkies₁ hCohnElkies₂ hP
        (ZSpan.fundamentalDomain_isBounded (Basis.ofZLatticeBasis ℝ P.lattice b))
        (PeriodicSpherePacking.basis_region_translates_cover_uniquely (S := P) b) hd

end Main_Theorem

end

end
