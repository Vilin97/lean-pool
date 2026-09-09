/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.NavierStokes.ProblemStatement
public import Mathlib.Analysis.Calculus.ContDiff.Operations
public import Mathlib.Topology.Algebra.InfiniteSum.Basic
public import Mathlib.Topology.LocallyFinite
public import Mathlib.Data.Int.Interval
public import Mathlib.Data.Fintype.Pi
public import Mathlib.Tactic.Abel
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Ring

@[expose] public section

/-!
# Spatial periodization in physical Euclidean three-space

The periodization is the actual sum over integer lattice translations. A fixed
spatial support bound makes this family locally finite, uniformly in time.
Consequently every smoothness order is preserved. The construction agrees with
the original field on an explicit cube whenever the other translates vanish.
-/

noncomputable section

namespace NavierStokes.PeriodicLocalization

open ProblemStatement Set Filter
open scoped BigOperators ContDiff Topology

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
