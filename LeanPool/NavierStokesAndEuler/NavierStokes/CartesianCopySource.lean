/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.NavierStokes.LocalPhysicalCopyBounds

/-!
# Cartesian source classes for actual native copies

The cylindrical radius and the Cartesian rotation are evaluated directly on
the lift. Their derivatives are bounded on a fixed annulus, and the original
flat weight is pulled back exactly.
-/

@[expose] public section


noncomputable section

open Set Function Filter
open scoped Topology ContDiff

namespace NavierStokes.CartesianCopySource

open WeightedClasses LabelSumBounds PhysicalClassBounds

/-- Plane: an abbreviation for `PhysicalGraphBounds.Plane`. -/
abbrev Plane := PhysicalGraphBounds.Plane
/-- Lift point: an abbreviation for `PhysicalWaveSum.LiftPoint`. -/
abbrev LiftPoint := PhysicalWaveSum.LiftPoint
/-- Native: an abbreviation for `PhysicalClassBounds.CylindricalPoint`. -/
abbrev Native := PhysicalClassBounds.CylindricalPoint
/-- Complex vector: an abbreviation for `HarmonicCalculus.ComplexVector`. -/
abbrev ComplexVector := HarmonicCalculus.ComplexVector

private theorem nat_le_infty (m : ℕ) : (m : WithTop ℕ∞) ≤ ∞ :=
  ENat.natCast_le_of_coe_top_le_withTop le_rfl m

theorem cylindricalMap_continuous : Continuous cylindricalMap :=
  ((Real.continuous_sqrt.comp ((continuous_fst.pow 2).add (continuous_snd.pow 2))).comp
    PhysicalGraphBounds.liftXY.continuous).prodMk slowFast.continuous

/-- Restriction to a padded annulus and the genuine native domain. The
weight, edge distance, viscosity and slow scales are unchanged by pullback. -/
noncomputable def pullStrip (s : StripData Native) (a b : ℝ) (ha : 0 < a) : StripData LiftPoint
    where
  domain := cylindricalDomain a b ∩ cylindricalMap ⁻¹' s.domain
  isOpen_domain := (cylindricalDomain_open a b).inter (s.isOpen_domain.preimage
      cylindricalMap_continuous)
  epsilon := s.epsilon
  epsilon_pos := s.epsilon_pos
  epsilon_le_one := s.epsilon_le_one
  slow := s.slow
  one_le_slow := s.one_le_slow
  delta x := s.delta (cylindricalMap x)
  delta_pos _ hx := s.delta_pos _ hx.2
  zeta x := s.zeta (cylindricalMap x)
  zeta_smooth := s.zeta_smooth.comp ((cylindricalMap_smooth ha).mono inter_subset_left) (fun _ hx
      => hx.2)
  zeta_nonneg _ hx := s.zeta_nonneg _ hx.2

@[simp] theorem pullStrip_zeta (s : StripData Native) (a b : ℝ) (ha : 0 < a) (x : LiftPoint) :
    (pullStrip s a b ha).zeta x = s.zeta (cylindricalMap x) := rfl

@[simp] theorem pullStrip_growth (s : StripData Native) (a b : ℝ) (ha : 0 < a)
    (n : ℕ) (x : LiftPoint) :
    (pullStrip s a b ha).growth n x = s.growth n (cylindricalMap x) := rfl

section Pullback

variable {ι : Type*} {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {s : StripData Native} {w : ι → ℕ → Native → ℝ} {f : ι → ℕ → Native → E} {α : ℝ}
  {a b : ℝ} (ha : 0 < a)

/-- Constants are chosen before labels, bands and copies. No positive
minimum of the flat weight occurs in this composition argument. -/
theorem uniform_pullback (hf : UniformClass s w α f) :
    UniformClass (pullStrip s a b ha) (fun l n x => w l n (cylindricalMap x)) α
      (fun l n x => f l n (cylindricalMap x)) := by
  refine ⟨fun l n x hx => hf.weight_nonneg l n _ hx.2,
    fun l n => (hf.smooth l n).comp ((cylindricalMap_smooth ha).mono inter_subset_left)
      (fun _ hx => hx.2), ?_⟩
  intro m
  obtain ⟨C, hC, p, hbound⟩ := hf.bounds m
  obtain ⟨B, hB, hmap⟩ := cylindricalMap_positiveJets (b := b) ha m
  refine ⟨(m.factorial : ℝ) * C * B ^ m, by positivity, p, ?_⟩
  intro l n x hx j hj
  have hA := majorant_nonneg s (w l) α hC p n (cylindricalMap x) (hf.weight_nonneg l n _ hx.2)
  have hb := LocalPhysicalCopyBounds.composition_jet_bound_on
    (pullStrip s a b ha).isOpen_domain s.isOpen_domain (hf.smooth l n)
    ((cylindricalMap_smooth ha).mono inter_subset_left) (fun _ hz => hz.2) hx m hA hB
    (hbound l n _ hx.2) (hmap x hx.1) j hj
  exact hb.trans_eq (by
      change _ = (m.factorial : ℝ) * C * B ^ m * s.epsilon n ^ α * s.growth n (cylindricalMap x) ^
          p * w l n (cylindricalMap x); unfold majorant; ring)

variable {cL cR L : ℝ} {ρ : Native → ℝ}

theorem flatGeometry_pullback (hflat : FlatGeometry s cL cR L ρ) :
    FlatGeometry (pullStrip s a b ha) cL cR L (fun x => ρ (cylindricalMap x)) :=
  ⟨hflat.left_pos, hflat.right_pos, fun _ hx => hflat.position _ hx.2,
    fun _ hx => hflat.delta_eq _ hx.2, fun _ hx => hflat.zeta_eq _ hx.2⟩

theorem sourceBounds_pullback {h : ℝ} (hf : LocalPhysicalCopyBounds.LocalSourceBounds s h α w f) :
    LocalPhysicalCopyBounds.LocalSourceBounds (pullStrip s a b ha) h α
      (fun l n x => w l n (cylindricalMap x)) (fun l n x => f l n (cylindricalMap x)) := by
  refine ⟨uniform_pullback ha hf.uniform, ?_, ?_, hf.epsilon_eq, hf.slow_le⟩
  · obtain ⟨cL, cR, L, ρ, hflat⟩ := hf.flat_geometry
    exact ⟨cL, cR, L, _, flatGeometry_pullback ha hflat⟩
  · obtain ⟨c, hc, hb⟩ := hf.weight_le
    exact ⟨c, hc, fun l n x hx => hb l n _ hx.2⟩

end Pullback

/-! ## Actual Cartesian rotation -/

/-- Horizontal, given by `ContinuousLinearMap.pi ![ContinuousLinearMap.proj 0,
ContinuousLinearMap.proj 1, 0]`. -/
noncomputable def horizontal : ComplexVector →L[ℝ] ComplexVector :=
  ContinuousLinearMap.pi ![ContinuousLinearMap.proj 0, ContinuousLinearMap.proj 1, 0]

/-- Connection, given by `ContinuousLinearMap.pi ![-ContinuousLinearMap.proj 1,
ContinuousLinearMap.proj 0, 0]`. -/
noncomputable def connection : ComplexVector →L[ℝ] ComplexVector :=
  ContinuousLinearMap.pi ![-ContinuousLinearMap.proj 1, ContinuousLinearMap.proj 0, 0]

/-- Vertical, given by `ContinuousLinearMap.pi ![0, 0, ContinuousLinearMap.proj 2]`. -/
noncomputable def vertical : ComplexVector →L[ℝ] ComplexVector :=
  ContinuousLinearMap.pi ![0, 0, ContinuousLinearMap.proj 2]

/-- Rotation map, given by `(y.1 / cartesianRadius y) • horizontal + (y.2 / cartesianRadius y) •
connection + vertical`. -/
noncomputable def rotationMap (y : Plane) : ComplexVector →L[ℝ] ComplexVector :=
  (y.1 / cartesianRadius y) • horizontal + (y.2 / cartesianRadius y) • connection + vertical

theorem rotationMap_apply (y : Plane) (v : ComplexVector) :
    rotationMap y v = ![(y.1 / cartesianRadius y : ℝ) • v 0 - (y.2 / cartesianRadius y : ℝ) • v 1,
      (y.2 / cartesianRadius y : ℝ) • v 0 + (y.1 / cartesianRadius y : ℝ) • v 1, v 2] := by
  ext i
  fin_cases i <;> simp [rotationMap, horizontal, connection, vertical, sub_eq_add_neg, add_comm]

theorem rotationMap_smooth : ContDiffOn ℝ ∞ rotationMap {y : Plane | y ≠ 0} := by
  have hr : ∀ y : Plane, y ≠ 0 → cartesianRadius y ≠ 0 := by
    intro y hy
    exact (Real.sqrt_pos.mpr (PhysicalGraphBounds.sum_sq_pos hy)).ne'
  exact (((contDiffOn_fst.div cartesianRadius_smooth hr).smul contDiffOn_const).add
    ((contDiffOn_snd.div cartesianRadius_smooth hr).smul contDiffOn_const)).add contDiffOn_const

/-- Actual all-order rotation jets have uniform bounds on the padded
annulus, independently of every slow and auxiliary coordinate. -/
theorem rotationMap_jets {a b : ℝ} (ha : 0 < a) (m : ℕ) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ x ∈ cylindricalDomain a b, ∀ j ≤ m,
      ‖iteratedFDeriv ℝ j (fun y => rotationMap (PhysicalGraphBounds.liftXY y)) x‖ ≤ C := by
  obtain ⟨C, hC, hb⟩ := PhysicalGraphBounds.compact_jet_bound
    PhysicalGraphBounds.axisFree_open rotationMap_smooth
    (PhysicalGraphBounds.isCompact_annulus (a / 2) (b + 1))
    (PhysicalGraphBounds.annulus_axisFree (half_pos ha)) m
  refine ⟨C, hC, ?_⟩
  intro x hx j hj
  have hann : PhysicalGraphBounds.liftXY x ∈ PhysicalGraphBounds.annulus (a / 2) (b + 1) := by
    refine ⟨?_, hx.1.le⟩
    simpa only [Metric.mem_closedBall, dist_zero_right] using hx.2.le
  exact (PhysicalGraphBounds.norm_jet_comp_linear PhysicalGraphBounds.axisFree_open
      rotationMap_smooth
    PhysicalGraphBounds.liftXY (cylindricalDomain_axisFree ha hx) j).trans
    ((mul_le_mul (hb j hj _ hann)
      (pow_le_one₀ (norm_nonneg _) PhysicalGraphBounds.norm_liftXY_le)
      (by positivity) (zero_le_one.trans hC)).trans_eq (mul_one C))

theorem rotation_uniform {ι : Type*} (s : StripData Native) {a b : ℝ} (ha : 0 < a) :
    UniformClass (pullStrip s a b ha) (fun (_ : ι) _ _ => 1) 0
      (fun _ _ x => rotationMap (PhysicalGraphBounds.liftXY x)) := by
  refine ⟨fun _ _ _ _ => zero_le_one, fun _ _ => rotationMap_smooth.comp
    PhysicalGraphBounds.liftXY.contDiff.contDiffOn (fun _ hx => cylindricalDomain_axisFree ha
        hx.1), ?_⟩
  intro m
  obtain ⟨C, hC, hb⟩ := rotationMap_jets (b := b) ha m
  refine ⟨C, zero_le_one.trans hC, 0, ?_⟩
  intro l n x hx j hj
  simpa only [majorant, Real.rpow_zero, pow_zero, mul_one] using hb x hx.1 j hj

/-- Rotated source, given by `rotationMap (PhysicalGraphBounds.liftXY x) (f l n (cylindricalMap
x))`. -/
noncomputable def rotatedSource {ι : Type*} (f : ι → ℕ → Native → ComplexVector)
    (l : ι) (n : ℕ) (x : LiftPoint) : ComplexVector :=
  rotationMap (PhysicalGraphBounds.liftXY x) (f l n (cylindricalMap x))

theorem uniform_rotated {ι : Type*} {s : StripData Native} {w : ι → ℕ → Native → ℝ}
    {f : ι → ℕ → Native → ComplexVector} {α a b : ℝ} (ha : 0 < a)
    (hf : UniformClass s w α f) :
    UniformClass (pullStrip s a b ha) (fun l n x => w l n (cylindricalMap x)) α (rotatedSource f)
        := by
  have he := (rotation_uniform (ι := ι) s (b := b) ha).bilinear (uniform_pullback ha hf)
    (ContinuousLinearMap.apply ℝ ComplexVector).flip
  simp only [one_mul, zero_add, ContinuousLinearMap.flip_apply, ContinuousLinearMap.apply_apply]
      at he ⊢
  exact he

theorem sourceBounds_rotated {ι : Type*} {s : StripData Native} {w : ι → ℕ → Native → ℝ}
    {f : ι → ℕ → Native → ComplexVector} {α h a b : ℝ} (ha : 0 < a)
    (hf : LocalPhysicalCopyBounds.LocalSourceBounds s h α w f) :
    LocalPhysicalCopyBounds.LocalSourceBounds (pullStrip s a b ha) h α
      (fun l n x => w l n (cylindricalMap x)) (rotatedSource f) := by
  have hp := sourceBounds_pullback (b := b) ha hf
  exact ⟨uniform_rotated ha hf.uniform, hp.flat_geometry, hp.weight_le, hp.epsilon_eq, hp.slow_le⟩

theorem sourceBounds_rotated_component {ι : Type*} {s : StripData Native} {w : ι → ℕ → Native → ℝ}
    {f : ι → ℕ → Native → ComplexVector} {α h a b : ℝ} (ha : 0 < a)
    (hf : LocalPhysicalCopyBounds.LocalSourceBounds s h α w f) (i : Fin 3) :
    LocalPhysicalCopyBounds.LocalSourceBounds (pullStrip s a b ha) h α
      (fun l n x => w l n (cylindricalMap x)) (fun l n x => rotatedSource f l n x i) := by
  have hp := sourceBounds_rotated (b := b) ha hf
  exact ⟨hp.uniform.map (ContinuousLinearMap.proj i), hp.flat_geometry,
    hp.weight_le, hp.epsilon_eq, hp.slow_le⟩

end NavierStokes.CartesianCopySource
