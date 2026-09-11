/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import LeanPool.NavierStokesAndEuler.NavierStokes.CylindricalResidual
public import LeanPool.NavierStokesAndEuler.NavierStokes.TimeLocalization
import LeanPool.NavierStokesAndEuler.NavierStokes.ResidualRegularity
import LeanPool.NavierStokesAndEuler.NavierStokes.SolenoidalDiagonal
public import LeanPool.NavierStokesAndEuler.NavierStokes.ProblemStatement
import Mathlib.Analysis.Calculus.ContDiff.Operations

/-!
# Spatial localization through actual Cartesian potentials

The fixed cutoff is a smooth function of `x₀² + x₁²` and `x₂`.  It is one
on an open cylinder containing the origin and has support strictly inside a
unit period cube.  We multiply the potential before taking any curl, and
periodize the resulting potential by the actual locally finite lattice sum.
The pressure is cut and periodized as a scalar.

The conclusions concern the spatial construction and the existing time
activation.  No terminal residual limit is assumed or asserted here.
-/

section

/-!
# Spatial periodization in physical Euclidean three-space

The periodization is the actual sum over integer lattice translations. A fixed
spatial support bound makes this family locally finite, uniformly in time.
Consequently every smoothness order is preserved. The construction agrees with
the original field on an explicit cube whenever the other translates vanish.
-/

@[expose] public section

noncomputable section

namespace NavierStokes.PeriodicLocalization

open ProblemStatement Set Filter
open scoped BigOperators ContDiff Topology

/-- Lattice: an abbreviation for `Fin 3 → ℤ`. -/
abbrev Lattice := Fin 3 → ℤ

/-- The integer lattice embedded in the Euclidean space of the PDE statement. -/
def lattice (n : Lattice) : Space :=
  (WithLp.equiv 2 (Fin 3 → ℝ)).symm (fun i => (n i : ℝ))

@[simp] theorem lattice_apply (n : Lattice) (i : Fin 3) :
    lattice n i = (n i : ℝ) := rfl

@[simp] theorem lattice_zero : lattice 0 = 0 := by
  ext i
  simp [lattice]

@[simp] theorem lattice_add (m n : Lattice) :
    lattice (m + n) = lattice m + lattice n := by
  ext i
  simp [lattice]

@[simp] theorem lattice_single (i : Fin 3) :
    lattice (Pi.single i 1) = coordinateVector i := by
  ext j
  simp [lattice, coordinateVector, Pi.single_apply]

variable {V : Type*} [NormedAddCommGroup V]

/-- A spatial support bound, uniform over all physical times. -/
def SupportedInCube (r : ℝ) (f : SpaceTime → V) : Prop :=
  ∀ z, f z ≠ 0 → ∀ i : Fin 3, |z.2 i| ≤ r

/-- Translate only in space; physical time is unchanged. -/
def translate (f : SpaceTime → V) (n : Lattice) (z : SpaceTime) : V :=
  f (z.1, z.2 - lattice n)

/-- The actual lattice sum, rather than an assumed periodic extension. -/
def periodize (f : SpaceTime → V) (z : SpaceTime) : V :=
  ∑' n : Lattice, translate f n z

/-- A finite box in the three-dimensional integer lattice. -/
def latticeBox (N : ℕ) : Set Lattice :=
  {n | ∀ i, n i ∈ Icc (-(N : ℤ)) (N : ℤ)}

theorem finite_latticeBox (N : ℕ) : (latticeBox N).Finite :=
  Set.Finite.pi' (fun _ : Fin 3 => Set.finite_Icc _ _)

/-- Lattice box finset, given by `(finite_latticeBox N).toFinset`. -/
def latticeBoxFinset (N : ℕ) : Finset Lattice := (finite_latticeBox N).toFinset

@[simp] theorem mem_latticeBoxFinset (N : ℕ) (n : Lattice) :
    n ∈ latticeBoxFinset N ↔ n ∈ latticeBox N := by
  simp [latticeBoxFinset]

/-- Only a finite lattice box can contribute on a bounded spatial region. -/
theorem mem_latticeBox_of_translate_ne_zero {r R : ℝ} {f : SpaceTime → V}
    (hf : SupportedInCube r f) {N : ℕ} (hN : R + r ≤ (N : ℝ))
    {z : SpaceTime} (hz : ‖z.2‖ ≤ R) {n : Lattice}
    (hn : translate f n z ≠ 0) : n ∈ latticeBox N := by
  intro i
  have hi : |z.2 i - (n i : ℝ)| ≤ r := by
    simpa [translate, lattice] using hf (z.1, z.2 - lattice n) hn i
  have hx : |z.2 i| ≤ R := by
    have hx' : |z.2 i| ≤ ‖z.2‖ := by
      simpa only [Real.norm_eq_abs] using PiLp.norm_apply_le z.2 i
    exact hx'.trans hz
  have hni : |(n i : ℝ)| ≤ (N : ℝ) := by
    calc
      |(n i : ℝ)| = |z.2 i - (z.2 i - (n i : ℝ))| := by ring_nf
      _ ≤ |z.2 i| + |z.2 i - (n i : ℝ)| := by
        simpa only [sub_zero, zero_sub, abs_neg] using
          abs_sub_le (z.2 i) 0 (z.2 i - (n i : ℝ))
      _ ≤ R + r := add_le_add hx hi
      _ ≤ (N : ℝ) := hN
  have hlo := (abs_le.mp hni).1
  have hhi := (abs_le.mp hni).2
  exact ⟨by exact_mod_cast hlo, by exact_mod_cast hhi⟩

/-- Near any spacetime point, every translate outside one fixed finite
integer box vanishes. No restriction on nearby time coordinates is needed. -/
theorem exists_local_latticeBox {r : ℝ} {f : SpaceTime → V}
    (hf : SupportedInCube r f) (z : SpaceTime) :
    ∃ N : ℕ, ∀ᶠ w in 𝓝 z, ∀ n ∉ latticeBoxFinset N, translate f n w = 0 := by
  obtain ⟨N, hN⟩ := exists_nat_gt (‖z.2‖ + 1 + r)
  refine ⟨N, ?_⟩
  have hU : {w : SpaceTime | ‖w.2‖ < ‖z.2‖ + 1} ∈ 𝓝 z :=
    (isOpen_lt (continuous_norm.comp continuous_snd) continuous_const).mem_nhds (by simp)
  filter_upwards [hU] with w hw n hn
  by_contra hne
  exact hn ((mem_latticeBoxFinset N n).mpr
    (mem_latticeBox_of_translate_ne_zero hf hN.le hw.le hne))

/-- The supports of the lattice translates form a locally finite family. -/
theorem locallyFinite_support_translate {r : ℝ} {f : SpaceTime → V}
    (hf : SupportedInCube r f) :
    LocallyFinite (fun n : Lattice => Function.support (translate f n)) := by
  intro z
  obtain ⟨N, hN⟩ := exists_local_latticeBox hf z
  refine ⟨{w | ∀ n ∉ latticeBoxFinset N, translate f n w = 0}, hN, ?_⟩
  apply (finite_latticeBox N).subset
  intro n hn
  obtain ⟨w, hw, hzero⟩ := hn
  by_contra hnot
  exact hw (hzero n (by simpa using hnot))

/-- The series is genuinely summable at every spacetime point. -/
theorem summable_translate {r : ℝ} {f : SpaceTime → V}
    (hf : SupportedInCube r f) (z : SpaceTime) :
    Summable (fun n : Lattice => translate f n z) :=
  summable_of_hasFiniteSupport ((locallyFinite_support_translate hf).point_finite z)

/-- Locally, the infinite sum equals a single finite sum of smooth translates. -/
theorem periodize_locally_eq_sum {r : ℝ} {f : SpaceTime → V}
    (hf : SupportedInCube r f) (z : SpaceTime) :
    ∃ N : ℕ, periodize f =ᶠ[𝓝 z]
      (fun w => ∑ n ∈ latticeBoxFinset N, translate f n w) := by
  obtain ⟨N, hN⟩ := exists_local_latticeBox hf z
  refine ⟨N, hN.mono ?_⟩
  intro w hw
  exact tsum_eq_sum hw

section Regularity

variable [NormedSpace ℝ V]

theorem contDiff_translate {f : SpaceTime → V} {m : WithTop ℕ∞}
    (hf : ContDiff ℝ m f) (n : Lattice) : ContDiff ℝ m (translate f n) :=
  hf.comp (contDiff_fst.prodMk (contDiff_snd.sub contDiff_const))

/-- Spatial periodization preserves every given differentiability order,
in particular `m = ∞`, through locally finite sums. -/
theorem contDiff_periodize {r : ℝ} {f : SpaceTime → V} {m : WithTop ℕ∞}
    (hs : SupportedInCube r f) (hf : ContDiff ℝ m f) :
    ContDiff ℝ m (periodize f) := by
  rw [contDiff_iff_contDiffAt]
  intro z
  obtain ⟨N, hN⟩ := periodize_locally_eq_sum hs z
  have hsum : ContDiff ℝ m
      (fun w => ∑ n ∈ latticeBoxFinset N, translate f n w) :=
    ContDiff.sum fun n _ => contDiff_translate hf n
  exact hsum.contDiffAt.congr_of_eventuallyEq hN

/-- A translation preserves smoothness relative to any set of times. -/
theorem contDiffOn_translate {f : SpaceTime → V} {m : WithTop ℕ∞} {times : Set ℝ}
    (hf : ContDiffOn ℝ m f (times ×ˢ (univ : Set Space))) (n : Lattice) :
    ContDiffOn ℝ m (translate f n) (times ×ˢ (univ : Set Space)) := by
  apply hf.comp (contDiff_fst.prodMk (contDiff_snd.sub contDiff_const)).contDiffOn
  intro z hz
  exact ⟨hz.1, mem_univ _⟩

/-- Periodization also preserves relative smoothness at time boundaries,
including the closed initial-time boundary in the PDE specification. -/
theorem contDiffOn_periodize {r : ℝ} {f : SpaceTime → V} {m : WithTop ℕ∞}
    {times : Set ℝ} (hs : SupportedInCube r f)
    (hf : ContDiffOn ℝ m f (times ×ˢ (univ : Set Space))) :
    ContDiffOn ℝ m (periodize f) (times ×ˢ (univ : Set Space)) := by
  intro z hz
  obtain ⟨N, hN⟩ := periodize_locally_eq_sum hs z
  have hsum : ContDiffOn ℝ m
      (fun w => ∑ n ∈ latticeBoxFinset N, translate f n w)
      (times ×ˢ (univ : Set Space)) :=
    ContDiffOn.sum fun n _ => contDiffOn_translate hf n
  exact (hsum z hz).congr_of_eventuallyEq
    (hN.filter_mono nhdsWithin_le_nhds) hN.self_of_nhds

end Regularity

/-- Reindexing the actual sum gives every integer lattice period. -/
theorem periodize_add_lattice (f : SpaceTime → V) (t : ℝ) (x : Space) (m : Lattice) :
    periodize f (t, x + lattice m) = periodize f (t, x) := by
  unfold periodize translate
  calc
    (∑' n : Lattice, f (t, x + lattice m - lattice n)) =
        ∑' n : Lattice, f (t, x + lattice m - lattice (n + m)) :=
      ((Equiv.addRight m).tsum_eq _).symm
    _ = ∑' n : Lattice, f (t, x - lattice n) := by
      apply tsum_congr
      intro n
      rw [lattice_add]
      congr 2
      abel

/-- The periods are the exact coordinate periods in the PDE specification. -/
theorem unitSpatialPeriodsOn_periodize (f : SpaceTime → V) (times : Set ℝ) :
    UnitSpatialPeriodsOn times (periodize f) := by
  intro t _ x i
  simpa only [lattice_single] using periodize_add_lattice f t x (Pi.single i 1)

/-- The open spatial cube on which other copies are excluded. -/
def innerCube (r : ℝ) : Set Space := {x | ∀ i : Fin 3, |x i| < 1 - r}

/-- In this cube, a nonzero translate must be the zero lattice translate. -/
theorem translate_eq_zero_on_innerCube {r : ℝ} {f : SpaceTime → V}
    (hf : SupportedInCube r f) {x : Space} (hx : x ∈ innerCube r)
    (t : ℝ) {n : Lattice} (hn : n ≠ 0) : translate f n (t, x) = 0 := by
  by_contra hne
  apply hn
  funext i
  have hi : |x i - (n i : ℝ)| ≤ r := by
    simpa [translate, lattice] using hf (t, x - lattice n) hne i
  have hni : |(n i : ℝ)| < 1 := by
    calc
      |(n i : ℝ)| = |x i - (x i - (n i : ℝ))| := by ring_nf
      _ ≤ |x i| + |x i - (n i : ℝ)| := by
        simpa only [sub_zero, zero_sub, abs_neg] using
          abs_sub_le (x i) 0 (x i - (n i : ℝ))
      _ < 1 := by have := hx i; linarith
  have hlo : (-1 : ℤ) < n i := by exact_mod_cast (abs_lt.mp hni).1
  have hhi : n i < (1 : ℤ) := by exact_mod_cast (abs_lt.mp hni).2
  change n i = 0
  omega

/-- Exact equality on an explicit open cube, uniformly over time. -/
theorem periodize_eq_on_innerCube {r : ℝ} {f : SpaceTime → V}
    (hf : SupportedInCube r f) {x : Space} (hx : x ∈ innerCube r) (t : ℝ) :
    periodize f (t, x) = f (t, x) := by
  have h := tsum_eq_single (L := SummationFilter.unconditional Lattice) (0 : Lattice)
    (fun n hn => translate_eq_zero_on_innerCube hf hx t hn)
  simpa only [periodize, translate, lattice_zero, sub_zero] using h

theorem isOpen_innerCube (r : ℝ) : IsOpen (innerCube r) := by
  change IsOpen {x : Space | ∀ i : Fin 3, |x i| < 1 - r}
  simp only [Set.ofPred_forall]
  exact isOpen_iInter_of_finite fun i =>
    isOpen_lt (continuous_abs.comp (EuclideanSpace.proj i).continuous) continuous_const

/-- Equality holds on a neighborhood of every point in the inner cube, so
local derivatives of the periodization also agree with those of the original. -/
theorem periodize_eventuallyEq {r : ℝ} {f : SpaceTime → V}
    (hf : SupportedInCube r f) {z : SpaceTime} (hz : z.2 ∈ innerCube r) :
    periodize f =ᶠ[𝓝 z] f := by
  have hU : Prod.snd ⁻¹' innerCube r ∈ 𝓝 z :=
    ((isOpen_innerCube r).preimage continuous_snd).mem_nhds hz
  filter_upwards [hU] with w hw
  exact periodize_eq_on_innerCube hf hw w.1

/-- A cube strictly inside the fundamental unit cube gives equality near the
spatial origin at every time. -/
theorem periodize_eventuallyEq_at_origin {r : ℝ} {f : SpaceTime → V}
    (hf : SupportedInCube r f) (hr : r < 1 / 2) (t : ℝ) :
    periodize f =ᶠ[𝓝 (t, (0 : Space))] f := by
  apply periodize_eventuallyEq hf
  intro i
  simp only [PiLp.zero_apply, abs_zero]
  linarith

/-- For support strictly inside the fundamental cube, equality holds on the
whole closed fundamental cube, including its boundary. -/
theorem periodize_eq_on_unitCube {r : ℝ} {f : SpaceTime → V}
    (hf : SupportedInCube r f) (hr : r < 1 / 2) {x : Space}
    (hx : ∀ i : Fin 3, |x i| ≤ 1 / 2) (t : ℝ) :
    periodize f (t, x) = f (t, x) := by
  apply periodize_eq_on_innerCube hf (t := t)
  intro i
  have := hx i
  linarith

/-- Spatial periodization preserves every zero time slice. -/
theorem periodize_eq_zero_of_timeSlice {f : SpaceTime → V} {t : ℝ}
    (hf : ∀ x : Space, f (t, x) = 0) (x : Space) : periodize f (t, x) = 0 := by
  simp only [periodize, translate, hf, tsum_zero]

/-- In particular, the common future time-support endpoint is preserved. -/
theorem compactFutureTimeSupport_periodize {f : VelocityField}
    (hf : CompactFutureTimeSupport f) : CompactFutureTimeSupport (periodize f) := by
  obtain ⟨T, hT, hzero⟩ := hf
  exact ⟨T, hT, fun t ht x => periodize_eq_zero_of_timeSlice (hzero t ht) x⟩

end NavierStokes.PeriodicLocalization

end
end

end

@[expose] public section

namespace NavierStokes.SpatialLocalization

noncomputable section

open ProblemStatement Set Filter
open AxisymmetricFields (projection)
open scoped ContDiff Topology

private theorem nat_le_infty (n : ℕ) : (n : WithTop ℕ∞) ≤ ∞ :=
  (ENat.natCast_lt_of_coe_top_le_withTop le_rfl n).le

/-- Squared distance to the symmetry axis, with no square-root singularity. -/
noncomputable def radialSquare (x : Space) : ℝ := (x 0) ^ 2 + (x 1) ^ 2

theorem radialSquare_nonneg (x : Space) : 0 ≤ radialSquare x :=
  add_nonneg (sq_nonneg _) (sq_nonneg _)

theorem radialSquare_contDiff : ContDiff ℝ ∞ radialSquare :=
  ((projection 0).contDiff.pow 2).add ((projection 1).contDiff.pow 2)

/-- A globally smooth profile in squared radius and axial position. -/
noncomputable def cutoffProfile (p : ℝ × ℝ) : ℝ :=
  SmoothCutoffs.cutoff (16 * p.1) * SmoothCutoffs.cutoff (4 * p.2)

theorem cutoffProfile_contDiff : ContDiff ℝ ∞ cutoffProfile :=
  (SmoothCutoffs.cutoff_contDiff.comp (contDiff_const.mul contDiff_fst)).mul
    (SmoothCutoffs.cutoff_contDiff.comp (contDiff_const.mul contDiff_snd))

/-- The explicit spatial cutoff used in both the potential and the pressure. -/
noncomputable def spatialCutoff (x : Space) : ℝ :=
  cutoffProfile (radialSquare x, x 2)

theorem spatialCutoff_contDiff : ContDiff ℝ ∞ spatialCutoff :=
  cutoffProfile_contDiff.comp (radialSquare_contDiff.prodMk (projection 2).contDiff)

theorem spatialCutoff_mem_Icc (x : Space) : spatialCutoff x ∈ Icc (0 : ℝ) 1 := by
  have hr := SmoothCutoffs.cutoff_mem_Icc (16 * radialSquare x)
  have hz := SmoothCutoffs.cutoff_mem_Icc (4 * x 2)
  exact ⟨mul_nonneg hr.1 hz.1, (mul_le_of_le_one_left hz.1 hr.2).trans hz.2⟩

/-- Invariance under the actual Cartesian rotation about the third axis. -/
theorem spatialCutoff_rotation (θ : ℝ) (x : Space) :
    spatialCutoff (CylindricalResidual.frame θ x) = spatialCutoff x := by
  have hr : radialSquare (CylindricalResidual.frame θ x) = radialSquare x := by
    simp only [radialSquare, CylindricalResidual.frame_apply,
      AxisymmetricResidual.pack_zero, AxisymmetricResidual.pack_one]
    linear_combination ((x 0) ^ 2 + (x 1) ^ 2) * Real.cos_sq_add_sin_sq θ
  simp only [spatialCutoff]
  rw [hr]
  simp only [CylindricalResidual.frame_apply, AxisymmetricResidual.pack_two]

/-- The closed support cylinder has radius `1/4` and height `1/2`. -/
noncomputable def supportCylinder : Set Space :=
  {x | radialSquare x ≤ 1 / 16 ∧ |x 2| ≤ 1 / 4}

theorem isClosed_supportCylinder : IsClosed supportCylinder :=
  (isClosed_le radialSquare_contDiff.continuous continuous_const).inter
    (isClosed_le (projection 2).continuous.abs continuous_const)

theorem isCompact_supportCylinder : IsCompact supportCylinder := by
  convert! AxisymmetricFields.isCompact_cylinder (1 / 32) (1 / 4) using 1
  ext x
  simp only [supportCylinder, Set.mem_ofPred_eq, AxisymmetricFields.radialEnergy, radialSquare]
  constructor <;> intro hx <;> constructor
  · linarith [hx.1]
  · exact hx.2
  · linarith [hx.1]
  · exact hx.2

theorem spatialCutoff_support_subset : Function.support spatialCutoff ⊆ supportCylinder := by
  intro x hx
  have hprod : SmoothCutoffs.cutoff (16 * radialSquare x) *
      SmoothCutoffs.cutoff (4 * x 2) ≠ 0 := hx
  have hr : 16 * radialSquare x < 1 := by
    by_contra h
    exact (mul_ne_zero_iff.mp hprod).1
      (SmoothCutoffs.cutoff_zero_of_one_le (le_of_not_gt h))
  have hz : |4 * x 2| < 1 := by
    by_contra h
    exact (mul_ne_zero_iff.mp hprod).2
      (SmoothCutoffs.cutoff_zero_of_one_le_abs (le_of_not_gt h))
  simp only [abs_mul, abs_of_pos (show (0 : ℝ) < 4 by norm_num)] at hz
  exact ⟨by linarith, by linarith⟩

theorem spatialCutoff_tsupport_subset : tsupport spatialCutoff ⊆ supportCylinder :=
  closure_minimal spatialCutoff_support_subset isClosed_supportCylinder

theorem spatialCutoff_hasCompactSupport : HasCompactSupport spatialCutoff :=
  isCompact_supportCylinder.of_isClosed_subset (isClosed_tsupport _) spatialCutoff_tsupport_subset

theorem supportCylinder_coordinate_bound {x : Space} (hx : x ∈ supportCylinder)
    (i : Fin 3) : |x i| ≤ 1 / 4 := by
  have hr := hx.1
  change (x 0) ^ 2 + (x 1) ^ 2 ≤ 1 / 16 at hr
  fin_cases i
  · change |x 0| ≤ 1 / 4
    have hs : |x 0| ^ 2 ≤ (1 / 4 : ℝ) ^ 2 := by
      rw [sq_abs]
      nlinarith [sq_nonneg (x 1)]
    nlinarith [abs_nonneg (x 0)]
  · change |x 1| ≤ 1 / 4
    have hs : |x 1| ^ 2 ≤ (1 / 4 : ℝ) ^ 2 := by
      rw [sq_abs]
      nlinarith [sq_nonneg (x 0)]
    nlinarith [abs_nonneg (x 1)]
  · exact hx.2

/-- The support is strictly inside the centered fundamental period cube. -/
theorem spatialCutoff_strictly_inside_cube {x : Space} (hx : x ∈ tsupport spatialCutoff)
    (i : Fin 3) : |x i| < 1 / 2 := by
  have := supportCylinder_coordinate_bound (spatialCutoff_tsupport_subset hx) i
  linarith

/-- An open cylinder on which the cutoff is identically one. -/
noncomputable def plateau : Set Space := {x | radialSquare x < 1 / 32 ∧ |x 2| < 1 / 8}

theorem isOpen_plateau : IsOpen plateau :=
  (isOpen_lt radialSquare_contDiff.continuous continuous_const).inter
    (isOpen_lt (projection 2).continuous.abs continuous_const)

theorem zero_mem_plateau : (0 : Space) ∈ plateau := by
  norm_num [plateau, radialSquare]

theorem spatialCutoff_eq_one {x : Space} (hx : x ∈ plateau) : spatialCutoff x = 1 := by
  have hr : |16 * radialSquare x| ≤ 1 / 2 := by
    rw [abs_of_nonneg (mul_nonneg (by norm_num) (radialSquare_nonneg x))]
    linarith [hx.1]
  have hz : |4 * x 2| ≤ 1 / 2 := by
    rw [abs_mul, abs_of_pos (show (0 : ℝ) < 4 by norm_num)]
    linarith [hx.2]
  simp only [spatialCutoff, cutoffProfile, SmoothCutoffs.cutoff_one_of_abs_le hr,
    SmoothCutoffs.cutoff_one_of_abs_le hz, one_mul]

theorem spatialCutoff_eventually_one {x : Space} (hx : x ∈ plateau) :
    spatialCutoff =ᶠ[𝓝 x] (fun _ => 1) := by
  filter_upwards [isOpen_plateau.mem_nhds hx] with y hy
  exact spatialCutoff_eq_one hy

theorem plateau_subset_innerCube : plateau ⊆ PeriodicLocalization.innerCube (1 / 4) := by
  intro x hx i
  have hb : x ∈ supportCylinder := ⟨by linarith [hx.1], by linarith [hx.2]⟩
  have := supportCylinder_coordinate_bound hb i
  linarith

/-- Multiplication of the actual Cartesian potential, before any curl. -/
noncomputable def cutPotential (A : VelocityField) : VelocityField :=
  fun z => spatialCutoff z.2 • A z

/-- Cut pressure, defined pointwise by `spatialCutoff z.2 * p z`. -/
noncomputable def cutPressure (p : PressureField) : PressureField :=
  fun z => spatialCutoff z.2 * p z

/-- Cut velocity, given by `SpatialCurl.spatialCurl (cutPotential A)`. -/
noncomputable def cutVelocity (A : VelocityField) : VelocityField :=
  SpatialCurl.spatialCurl (cutPotential A)

theorem cutPotential_supported (A : VelocityField) :
    PeriodicLocalization.SupportedInCube (1 / 4) (cutPotential A) := by
  intro z hz i
  have hc : spatialCutoff z.2 ≠ 0 := by
    intro h
    exact hz (by simp only [cutPotential, h, zero_smul])
  exact supportCylinder_coordinate_bound (spatialCutoff_support_subset hc) i

theorem cutPressure_supported (p : PressureField) :
    PeriodicLocalization.SupportedInCube (1 / 4) (cutPressure p) := by
  intro z hz i
  have hc : spatialCutoff z.2 ≠ 0 := by
    intro h
    exact hz (by simp only [cutPressure, h, zero_mul])
  exact supportCylinder_coordinate_bound (spatialCutoff_support_subset hc) i

theorem cutVelocity_tsupport (A : VelocityField) (t : ℝ) :
    tsupport (fun x => cutVelocity A (t, x)) ⊆ supportCylinder :=
  (SpatialCurl.tsupport_curl_cutoff_subset spatialCutoff (fun x => A (t, x))).trans
    spatialCutoff_tsupport_subset

theorem cutVelocity_hasCompactSupport (A : VelocityField) (t : ℝ) :
    HasCompactSupport (fun x => cutVelocity A (t, x)) :=
  SpatialCurl.hasCompactSupport_curl_cutoff spatialCutoff_hasCompactSupport (fun x => A (t, x))

/-- This identity displays the entire cutoff derivative term. -/
theorem cutVelocity_product_rule (A : VelocityField) (t : ℝ) (x : Space)
    (hA : DifferentiableAt ℝ (fun y => A (t, y)) x) :
    cutVelocity A (t, x) = spatialCutoff x • SpatialCurl.spatialCurl A (t, x) +
      SpatialCurl.curlLinear ((fderiv ℝ spatialCutoff x).smulRight (A (t, x))) := by
  change SpatialCurl.curlLinear (fderiv ℝ (fun y => spatialCutoff y • A (t, y)) x) = _
  rw [fderiv_fun_smul (spatialCutoff_contDiff.differentiable (by simp) x) hA, map_add,
    map_smul]
  rfl

/-- The actual lattice sum of the cut potential. -/
noncomputable def periodicPotential (A : VelocityField) : VelocityField :=
  PeriodicLocalization.periodize (cutPotential A)

/-- Periodic velocity, given by `SpatialCurl.spatialCurl (periodicPotential A)`. -/
noncomputable def periodicVelocity (A : VelocityField) : VelocityField :=
  SpatialCurl.spatialCurl (periodicPotential A)

/-- Periodic pressure, given by `PeriodicLocalization.periodize (cutPressure p)`. -/
noncomputable def periodicPressure (p : PressureField) : PressureField :=
  PeriodicLocalization.periodize (cutPressure p)

theorem periodicPotential_locally_finite (A : VelocityField) :
    LocallyFinite (fun n : PeriodicLocalization.Lattice =>
      Function.support (PeriodicLocalization.translate (cutPotential A) n)) :=
  PeriodicLocalization.locallyFinite_support_translate (cutPotential_supported A)

theorem periodicPressure_locally_finite (p : PressureField) :
    LocallyFinite (fun n : PeriodicLocalization.Lattice =>
      Function.support (PeriodicLocalization.translate (cutPressure p) n)) :=
  PeriodicLocalization.locallyFinite_support_translate (cutPressure_supported p)

theorem periodicPotential_smoothOn {A : VelocityField} {times : Set ℝ}
    (hA : ContDiffOn ℝ ∞ A (times ×ˢ (univ : Set Space))) :
    ContDiffOn ℝ ∞ (periodicPotential A) (times ×ˢ (univ : Set Space)) :=
  PeriodicLocalization.contDiffOn_periodize (cutPotential_supported A)
    ((spatialCutoff_contDiff.comp contDiff_snd).contDiffOn.smul hA)

theorem periodicVelocity_smoothOn {A : VelocityField} {times : Set ℝ}
    (hA : ContDiffOn ℝ ∞ A (times ×ˢ (univ : Set Space))) :
    ContDiffOn ℝ ∞ (periodicVelocity A) (times ×ˢ (univ : Set Space)) :=
  SpatialCurl.contDiffOn_spatialCurl (periodicPotential_smoothOn hA) (by simp)

theorem periodicPressure_smoothOn {p : PressureField} {times : Set ℝ}
    (hp : ContDiffOn ℝ ∞ p (times ×ˢ (univ : Set Space))) :
    ContDiffOn ℝ ∞ (periodicPressure p) (times ×ˢ (univ : Set Space)) :=
  PeriodicLocalization.contDiffOn_periodize (cutPressure_supported p)
    ((spatialCutoff_contDiff.comp contDiff_snd).contDiffOn.mul hp)

theorem periodicPotential_periodic (A : VelocityField) (times : Set ℝ) :
    UnitSpatialPeriodsOn times (periodicPotential A) :=
  PeriodicLocalization.unitSpatialPeriodsOn_periodize (cutPotential A) times

theorem periodicVelocity_periodic (A : VelocityField) (times : Set ℝ) :
    UnitSpatialPeriodsOn times (periodicVelocity A) :=
  SpatialCurl.spatialCurl_periodic (periodicPotential_periodic A times)

theorem periodicPressure_periodic (p : PressureField) (times : Set ℝ) :
    UnitSpatialPeriodsOn times (periodicPressure p) :=
  PeriodicLocalization.unitSpatialPeriodsOn_periodize (cutPressure p) times

theorem periodicVelocity_divergence_free {A : VelocityField} {times : Set ℝ}
    (hA : ContDiffOn ℝ ∞ A (times ×ˢ (univ : Set Space))) {t : ℝ}
    (ht : t ∈ times) (x : Space) : spatialDivergence (periodicVelocity A) t x = 0 :=
  SpatialCurl.spatialDivergence_spatialCurl_on
    ((periodicPotential_smoothOn hA).of_le (nat_le_infty 2)) ht x

/-- Throughout the central no-overlap cube, periodization agrees locally
with the actual cut field, including its cutoff derivative terms. -/
theorem periodicVelocity_eventuallyEq_cut (A : VelocityField) {z : SpaceTime}
    (hz : z.2 ∈ PeriodicLocalization.innerCube (1 / 4)) :
    periodicVelocity A =ᶠ[𝓝 z] cutVelocity A :=
  SolenoidalDiagonal.spatialCurl_eventuallyEq
    (PeriodicLocalization.periodize_eventuallyEq (cutPotential_supported A) hz)

theorem periodicPressure_eventuallyEq_cut (p : PressureField) {z : SpaceTime}
    (hz : z.2 ∈ PeriodicLocalization.innerCube (1 / 4)) :
    periodicPressure p =ᶠ[𝓝 z] cutPressure p :=
  PeriodicLocalization.periodize_eventuallyEq (cutPressure_supported p) hz

theorem periodic_residual_eventuallyEq_cut (A : VelocityField) (p : PressureField)
    {z : SpaceTime} (hz : z.2 ∈ PeriodicLocalization.innerCube (1 / 4)) :
    (fun w => navierStokesResidual (periodicVelocity A) (periodicPressure p) w.1 w.2)
      =ᶠ[𝓝 z] (fun w => navierStokesResidual (cutVelocity A) (cutPressure p) w.1 w.2) :=
  ResidualRegularity.residual_eventuallyEq (periodicVelocity_eventuallyEq_cut A hz)
    (periodicPressure_eventuallyEq_cut p hz)

theorem periodic_fields_eq_cut_on_unitCube (A : VelocityField) (p : PressureField)
    (t : ℝ) {x : Space} (hx : ∀ i : Fin 3, |x i| ≤ 1 / 2) :
    periodicVelocity A (t, x) = cutVelocity A (t, x) ∧
      periodicPressure p (t, x) = cutPressure p (t, x) ∧
      navierStokesResidual (periodicVelocity A) (periodicPressure p) t x =
        navierStokesResidual (cutVelocity A) (cutPressure p) t x := by
  have hi : x ∈ PeriodicLocalization.innerCube (1 / 4) := by
    intro i
    have := hx i
    linarith
  exact ⟨(periodicVelocity_eventuallyEq_cut A (z := (t, x)) hi).self_of_nhds,
    (periodicPressure_eventuallyEq_cut p (z := (t, x)) hi).self_of_nhds,
    (periodic_residual_eventuallyEq_cut A p (z := (t, x)) hi).self_of_nhds⟩

theorem cutPotential_eventuallyEq (A : VelocityField) {z : SpaceTime}
    (hz : z.2 ∈ plateau) : cutPotential A =ᶠ[𝓝 z] A := by
  have he := (spatialCutoff_eventually_one hz).comp_tendsto continuous_snd.continuousAt
  filter_upwards [he] with w hw
  change spatialCutoff w.2 = 1 at hw
  simp only [cutPotential, hw, one_smul]

theorem cutPressure_eventuallyEq (p : PressureField) {z : SpaceTime}
    (hz : z.2 ∈ plateau) : cutPressure p =ᶠ[𝓝 z] p := by
  have he := (spatialCutoff_eventually_one hz).comp_tendsto continuous_snd.continuousAt
  filter_upwards [he] with w hw
  change spatialCutoff w.2 = 1 at hw
  simp only [cutPressure, hw, one_mul]

/-- Local equality includes all nearby physical times and all spatial directions. -/
theorem periodicPotential_eventuallyEq (A : VelocityField) {z : SpaceTime}
    (hz : z.2 ∈ plateau) : periodicPotential A =ᶠ[𝓝 z] A :=
  (PeriodicLocalization.periodize_eventuallyEq (cutPotential_supported A)
    (plateau_subset_innerCube hz)).trans (cutPotential_eventuallyEq A hz)

theorem periodicVelocity_eventuallyEq (A : VelocityField) {z : SpaceTime}
    (hz : z.2 ∈ plateau) : periodicVelocity A =ᶠ[𝓝 z] SpatialCurl.spatialCurl A :=
  SolenoidalDiagonal.spatialCurl_eventuallyEq (periodicPotential_eventuallyEq A hz)

theorem periodicPressure_eventuallyEq (p : PressureField) {z : SpaceTime}
    (hz : z.2 ∈ plateau) : periodicPressure p =ᶠ[𝓝 z] p :=
  (PeriodicLocalization.periodize_eventuallyEq (cutPressure_supported p)
    (plateau_subset_innerCube hz)).trans (cutPressure_eventuallyEq p hz)

theorem periodicVelocity_eq (A : VelocityField) {z : SpaceTime} (hz : z.2 ∈ plateau) :
    periodicVelocity A z = SpatialCurl.spatialCurl A z :=
  (periodicVelocity_eventuallyEq A hz).self_of_nhds

theorem periodicPressure_eq (p : PressureField) {z : SpaceTime} (hz : z.2 ∈ plateau) :
    periodicPressure p z = p z := (periodicPressure_eventuallyEq p hz).self_of_nhds

theorem periodicVelocity_jets_eq (A : VelocityField) {z : SpaceTime}
    (hz : z.2 ∈ plateau) (m : ℕ) :
    iteratedFDeriv ℝ m (periodicVelocity A) z =
      iteratedFDeriv ℝ m (SpatialCurl.spatialCurl A) z :=
  (SolenoidalDiagonal.iteratedFDeriv_eventuallyEq (periodicVelocity_eventuallyEq A hz)
      m).self_of_nhds

theorem periodicPressure_jets_eq (p : PressureField) {z : SpaceTime}
    (hz : z.2 ∈ plateau) (m : ℕ) :
    iteratedFDeriv ℝ m (periodicPressure p) z = iteratedFDeriv ℝ m p z :=
  (SolenoidalDiagonal.iteratedFDeriv_eventuallyEq (periodicPressure_eventuallyEq p hz)
      m).self_of_nhds

theorem periodic_residual_eventuallyEq (A : VelocityField) (p : PressureField)
    {z : SpaceTime} (hz : z.2 ∈ plateau) :
    (fun w => navierStokesResidual (periodicVelocity A) (periodicPressure p) w.1 w.2)
      =ᶠ[𝓝 z] (fun w => navierStokesResidual (SpatialCurl.spatialCurl A) p w.1 w.2) :=
  ResidualRegularity.residual_eventuallyEq (periodicVelocity_eventuallyEq A hz)
    (periodicPressure_eventuallyEq p hz)

theorem periodic_residual_eq (A : VelocityField) (p : PressureField)
    {z : SpaceTime} (hz : z.2 ∈ plateau) :
    navierStokesResidual (periodicVelocity A) (periodicPressure p) z.1 z.2 =
      navierStokesResidual (SpatialCurl.spatialCurl A) p z.1 z.2 :=
  (periodic_residual_eventuallyEq A p hz).self_of_nhds

theorem periodic_residual_jets_eq (A : VelocityField) (p : PressureField)
    {z : SpaceTime} (hz : z.2 ∈ plateau) (m : ℕ) :
    iteratedFDeriv ℝ m
        (fun w => navierStokesResidual (periodicVelocity A) (periodicPressure p) w.1 w.2) z =
      iteratedFDeriv ℝ m
        (fun w => navierStokesResidual (SpatialCurl.spatialCurl A) p w.1 w.2) z :=
  (SolenoidalDiagonal.iteratedFDeriv_eventuallyEq
    (periodic_residual_eventuallyEq A p hz) m).self_of_nhds

theorem periodicVelocity_origin (A : VelocityField) (t : ℝ) :
    periodicVelocity A (t, 0) = SpatialCurl.spatialCurl A (t, 0) :=
  periodicVelocity_eq A zero_mem_plateau

theorem periodicPressure_origin (p : PressureField) (t : ℝ) :
    periodicPressure p (t, 0) = p (t, 0) := periodicPressure_eq p zero_mem_plateau

theorem periodicVelocity_origin_blowup (A : VelocityField)
    (hA : Tendsto (fun t : ℝ => ‖SpatialCurl.spatialCurl A (t, 0)‖) (𝓝[<] 1) atTop) :
    Tendsto (fun t : ℝ => ‖periodicVelocity A (t, 0)‖) (𝓝[<] 1) atTop := by
  simpa only [periodicVelocity_origin] using hA

/-- The previously constructed time switch is applied to the spatially
localized fields.  It is independent of the spatial variables. -/
noncomputable def localizedVelocity (A : VelocityField) : VelocityField :=
  TimeLocalization.activatedVelocity (periodicVelocity A)

/-- Localized pressure, given by `TimeLocalization.activatedPressure (periodicPressure p)`. -/
noncomputable def localizedPressure (p : PressureField) : PressureField :=
  TimeLocalization.activatedPressure (periodicPressure p)

/-- The same time activation can be performed on the actual potential. -/
noncomputable def localizedPotential (A : VelocityField) : VelocityField :=
  TimeLocalization.activatedVelocity (periodicPotential A)

theorem localizedPotential_smoothOn {A : VelocityField} {times : Set ℝ}
    (hA : ContDiffOn ℝ ∞ A (times ×ˢ (univ : Set Space))) :
    ContDiffOn ℝ ∞ (localizedPotential A) (times ×ˢ (univ : Set Space)) :=
  (SmoothCutoffs.timeSwitch_contDiff.comp contDiff_fst).contDiffOn.smul
    (periodicPotential_smoothOn hA)

theorem localizedVelocity_eq_curl {A : VelocityField} {times : Set ℝ}
    (hA : ContDiffOn ℝ ∞ A (times ×ˢ (univ : Set Space)))
    {t : ℝ} (ht : t ∈ times) (x : Space) :
    localizedVelocity A (t, x) = SpatialCurl.spatialCurl (localizedPotential A) (t, x) := by
  have hd : DifferentiableAt ℝ (fun y => periodicPotential A (t, y)) x :=
    (SpatialCurl.contDiff_spatialSlice (periodicPotential_smoothOn hA) ht).differentiable
      (by simp) x
  change SmoothCutoffs.timeSwitch t •
      SpatialCurl.curlLinear (fderiv ℝ (fun y => periodicPotential A (t, y)) x) =
    SpatialCurl.curlLinear
      (fderiv ℝ (fun y => SmoothCutoffs.timeSwitch t • periodicPotential A (t, y)) x)
  rw [fderiv_fun_const_smul hd, map_smul]

theorem localizedVelocity_smooth {A : VelocityField}
    (hA : ContDiffOn ℝ ∞ A preSingularDomain) :
    ContDiffOn ℝ ∞ (localizedVelocity A) preSingularDomain :=
  TimeLocalization.activatedVelocity_smooth _ (periodicVelocity_smoothOn hA)

theorem localizedPressure_smooth {p : PressureField}
    (hp : ContDiffOn ℝ ∞ p preSingularDomain) :
    ContDiffOn ℝ ∞ (localizedPressure p) preSingularDomain :=
  TimeLocalization.activatedPressure_smooth _ (periodicPressure_smoothOn hp)

theorem localizedVelocity_smooth_before {A : VelocityField}
    (hA : ContDiffOn ℝ ∞ A (Iio (1 : ℝ) ×ˢ (univ : Set Space))) :
    ContDiffOn ℝ ∞ (localizedVelocity A) preSingularDomain :=
  localizedVelocity_smooth (hA.mono (fun _ hz => ⟨hz.1.2, hz.2⟩))

theorem localizedPressure_smooth_before {p : PressureField}
    (hp : ContDiffOn ℝ ∞ p (Iio (1 : ℝ) ×ˢ (univ : Set Space))) :
    ContDiffOn ℝ ∞ (localizedPressure p) preSingularDomain :=
  localizedPressure_smooth (hp.mono (fun _ hz => ⟨hz.1.2, hz.2⟩))

theorem localizedVelocity_periodic (A : VelocityField) (times : Set ℝ) :
    UnitSpatialPeriodsOn times (localizedVelocity A) :=
  TimeLocalization.activatedVelocity_periodic _ times (periodicVelocity_periodic A times)

theorem localizedPressure_periodic (p : PressureField) (times : Set ℝ) :
    UnitSpatialPeriodsOn times (localizedPressure p) :=
  TimeLocalization.activatedPressure_periodic _ times (periodicPressure_periodic p times)

theorem localizedVelocity_zero_initial (A : VelocityField) (x : Space) :
    localizedVelocity A (0, x) = 0 := TimeLocalization.activatedVelocity_zero_initial _ x

theorem localizedPressure_zero_initial (p : PressureField) (x : Space) :
    localizedPressure p (0, x) = 0 := TimeLocalization.activatedPressure_zero_initial _ x

theorem localizedVelocity_zero_early (A : VelocityField) {t : ℝ}
    (ht : |t| ≤ 3 / 8) (x : Space) : localizedVelocity A (t, x) = 0 :=
  TimeLocalization.activatedVelocity_zero_early _ ht x

theorem localizedPressure_zero_early (p : PressureField) {t : ℝ}
    (ht : |t| ≤ 3 / 8) (x : Space) : localizedPressure p (t, x) = 0 :=
  TimeLocalization.activatedPressure_zero_early _ ht x

theorem localizedVelocity_divergence_free {A : VelocityField}
    (hA : ContDiffOn ℝ ∞ A preSingularDomain) :
    ∀ t ∈ Ico (0 : ℝ) 1, ∀ x : Space, spatialDivergence (localizedVelocity A) t x = 0 :=
  TimeLocalization.activatedVelocity_divergence_free _ (periodicVelocity_smoothOn hA)
    (fun _ ht x => periodicVelocity_divergence_free hA ht x)

theorem localizedVelocity_eventuallyEq (A : VelocityField) {z : SpaceTime}
    (ht : 3 / 4 < z.1) (hz : z.2 ∈ plateau) :
    localizedVelocity A =ᶠ[𝓝 z] SpatialCurl.spatialCurl A :=
  (TimeLocalization.activatedVelocity_eventuallyEq_late _ ht z.2).trans
    (periodicVelocity_eventuallyEq A hz)

theorem localizedPressure_eventuallyEq (p : PressureField) {z : SpaceTime}
    (ht : 3 / 4 < z.1) (hz : z.2 ∈ plateau) :
    localizedPressure p =ᶠ[𝓝 z] p :=
  (TimeLocalization.activatedPressure_eventuallyEq_late _ ht z.2).trans
    (periodicPressure_eventuallyEq p hz)

theorem localizedVelocity_eq (A : VelocityField) {z : SpaceTime}
    (ht : 3 / 4 ≤ z.1) (hz : z.2 ∈ plateau) :
    localizedVelocity A z = SpatialCurl.spatialCurl A z := by
  rw [localizedVelocity, TimeLocalization.activatedVelocity_eq_late _ ht,
    periodicVelocity_eq A hz]

theorem localizedPressure_eq (p : PressureField) {z : SpaceTime}
    (ht : 3 / 4 ≤ z.1) (hz : z.2 ∈ plateau) : localizedPressure p z = p z := by
  rw [localizedPressure, TimeLocalization.activatedPressure_eq_late _ ht,
    periodicPressure_eq p hz]

theorem localized_residual_eventuallyEq (A : VelocityField) (p : PressureField)
    {z : SpaceTime} (ht : 3 / 4 < z.1) (hz : z.2 ∈ plateau) :
    (fun w => navierStokesResidual (localizedVelocity A) (localizedPressure p) w.1 w.2)
      =ᶠ[𝓝 z] (fun w => navierStokesResidual (SpatialCurl.spatialCurl A) p w.1 w.2) :=
  ResidualRegularity.residual_eventuallyEq (localizedVelocity_eventuallyEq A ht hz)
    (localizedPressure_eventuallyEq p ht hz)

theorem localized_residual_eq (A : VelocityField) (p : PressureField)
    {z : SpaceTime} (ht : 3 / 4 < z.1) (hz : z.2 ∈ plateau) :
    navierStokesResidual (localizedVelocity A) (localizedPressure p) z.1 z.2 =
      navierStokesResidual (SpatialCurl.spatialCurl A) p z.1 z.2 :=
  (localized_residual_eventuallyEq A p ht hz).self_of_nhds

/-- An existing physical potential representation can be supplied as a local
identity.  No additional regularity is needed to transfer the residual germ. -/
theorem localized_residual_of_potential_germ (A u : VelocityField) (p : PressureField)
    {z : SpaceTime} (ht : 3 / 4 < z.1) (hz : z.2 ∈ plateau)
    (hAu : SpatialCurl.spatialCurl A =ᶠ[𝓝 z] u) :
    (fun w => navierStokesResidual (localizedVelocity A) (localizedPressure p) w.1 w.2)
      =ᶠ[𝓝 z] (fun w => navierStokesResidual u p w.1 w.2) :=
  ResidualRegularity.residual_eventuallyEq
    ((localizedVelocity_eventuallyEq A ht hz).trans hAu)
    (localizedPressure_eventuallyEq p ht hz)

theorem localizedVelocity_jets_eq (A : VelocityField) {z : SpaceTime}
    (ht : 3 / 4 < z.1) (hz : z.2 ∈ plateau) (m : ℕ) :
    iteratedFDeriv ℝ m (localizedVelocity A) z =
      iteratedFDeriv ℝ m (SpatialCurl.spatialCurl A) z :=
  (SolenoidalDiagonal.iteratedFDeriv_eventuallyEq
    (localizedVelocity_eventuallyEq A ht hz) m).self_of_nhds

theorem localizedPressure_jets_eq (p : PressureField) {z : SpaceTime}
    (ht : 3 / 4 < z.1) (hz : z.2 ∈ plateau) (m : ℕ) :
    iteratedFDeriv ℝ m (localizedPressure p) z = iteratedFDeriv ℝ m p z :=
  (SolenoidalDiagonal.iteratedFDeriv_eventuallyEq
    (localizedPressure_eventuallyEq p ht hz) m).self_of_nhds

theorem localized_residual_jets_eq (A : VelocityField) (p : PressureField)
    {z : SpaceTime} (ht : 3 / 4 < z.1) (hz : z.2 ∈ plateau) (m : ℕ) :
    iteratedFDeriv ℝ m
        (fun w => navierStokesResidual (localizedVelocity A) (localizedPressure p) w.1 w.2) z =
      iteratedFDeriv ℝ m
        (fun w => navierStokesResidual (SpatialCurl.spatialCurl A) p w.1 w.2) z :=
  (SolenoidalDiagonal.iteratedFDeriv_eventuallyEq
    (localized_residual_eventuallyEq A p ht hz) m).self_of_nhds

theorem localizedVelocity_origin (A : VelocityField) {t : ℝ} (ht : 3 / 4 ≤ t) :
    localizedVelocity A (t, 0) = SpatialCurl.spatialCurl A (t, 0) :=
  localizedVelocity_eq A ht zero_mem_plateau

theorem localizedVelocity_origin_blowup (A : VelocityField)
    (hA : Tendsto (fun t : ℝ => ‖SpatialCurl.spatialCurl A (t, 0)‖) (𝓝[<] 1) atTop) :
    Tendsto (fun t : ℝ => ‖localizedVelocity A (t, 0)‖) (𝓝[<] 1) atTop := by
  apply hA.congr'
  have hlate : ∀ᶠ t in 𝓝[<] (1 : ℝ), 3 / 4 < t :=
    mem_nhdsWithin_of_mem_nhds (Ioi_mem_nhds (by norm_num))
  filter_upwards [hlate] with t ht
  rw [localizedVelocity_origin A ht.le]

private theorem unbounded_of_origin_blowup {u : VelocityField}
    (hu : Tendsto (fun t : ℝ => ‖u (t, 0)‖) (𝓝[<] 1) atTop) :
    SpeedUnboundedAtOne u := by
  intro M _ δ hδ
  have hlow : Ioi (max 0 (1 - δ)) ∈ 𝓝[<] (1 : ℝ) :=
    mem_nhdsWithin_of_mem_nhds (Ioi_mem_nhds (max_lt (by norm_num) (by linarith)))
  have hlarge : ∀ᶠ t in 𝓝[<] (1 : ℝ), M < ‖u (t, 0)‖ :=
    hu.eventually (eventually_gt_atTop M)
  have hbefore : ∀ᶠ t in 𝓝[<] (1 : ℝ), t < 1 := self_mem_nhdsWithin
  obtain ⟨t, ht, hMt, hlo⟩ := (hbefore.and (hlarge.and hlow)).exists
  exact ⟨t, 0, ⟨(le_max_left _ _).trans_lt hlo, ht⟩,
    (le_max_right _ _).trans_lt hlo, hMt⟩

theorem localizedVelocity_speed_unbounded (A : VelocityField)
    (hA : Tendsto (fun t : ℝ => ‖SpatialCurl.spatialCurl A (t, 0)‖) (𝓝[<] 1) atTop) :
    SpeedUnboundedAtOne (localizedVelocity A) :=
  unbounded_of_origin_blowup (localizedVelocity_origin_blowup A hA)

/-- The actual constructed pair, including its initial data and genuine local
Navier--Stokes residual equality.  The only blowup input is at the origin of
the original curl field; no localization or residual-output estimate is assumed. -/
theorem localization_properties (A : VelocityField) (p : PressureField)
    (hA : ContDiffOn ℝ ∞ A (Iio (1 : ℝ) ×ˢ (univ : Set Space)))
    (hp : ContDiffOn ℝ ∞ p (Iio (1 : ℝ) ×ˢ (univ : Set Space)))
    (haxis : Tendsto (fun t : ℝ => ‖SpatialCurl.spatialCurl A (t, 0)‖) (𝓝[<] 1) atTop) :
    ContDiffOn ℝ ∞ (localizedVelocity A) preSingularDomain ∧
      ContDiffOn ℝ ∞ (localizedPressure p) preSingularDomain ∧
      UnitSpatialPeriodsOn (Ico (0 : ℝ) 1) (localizedVelocity A) ∧
      UnitSpatialPeriodsOn (Ico (0 : ℝ) 1) (localizedPressure p) ∧
      (∀ x : Space, localizedVelocity A (0, x) = 0) ∧
      (∀ t ∈ Ico (0 : ℝ) 1, ∀ x : Space,
        spatialDivergence (localizedVelocity A) t x = 0) ∧
      SpeedUnboundedAtOne (localizedVelocity A) ∧
      (∀ z : SpaceTime, 3 / 4 < z.1 → z.2 ∈ plateau →
        localizedVelocity A z = SpatialCurl.spatialCurl A z ∧
        localizedPressure p z = p z ∧
        navierStokesResidual (localizedVelocity A) (localizedPressure p) z.1 z.2 =
          navierStokesResidual (SpatialCurl.spatialCurl A) p z.1 z.2) := by
  refine ⟨localizedVelocity_smooth_before hA, localizedPressure_smooth_before hp,
    localizedVelocity_periodic A _, localizedPressure_periodic p _,
    localizedVelocity_zero_initial A, ?_, localizedVelocity_speed_unbounded A haxis, ?_⟩
  · exact localizedVelocity_divergence_free (hA.mono (fun _ hz => ⟨hz.1.2, hz.2⟩))
  · intro z ht hz
    exact ⟨localizedVelocity_eq A ht.le hz, localizedPressure_eq p ht.le hz,
      localized_residual_eq A p ht hz⟩

end

end NavierStokes.SpatialLocalization
