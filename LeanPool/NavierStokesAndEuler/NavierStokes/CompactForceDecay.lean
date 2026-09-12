/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.NavierStokes.ProblemStatement
import Mathlib.Analysis.Calculus.ContDiff.Basic

/-!
# Decay of all derivatives of a smooth periodic force with bounded time support

Each actual iterated derivative is continuous and spatially periodic, hence
bounded on a compact time interval after reduction to a fundamental cube.
Beyond the time support it is zero by locality of differentiation.
-/

@[expose] public section


namespace NavierStokes.CompactForceDecay

noncomputable section

open ProblemStatement Set Filter
open scoped BigOperators ContDiff Topology

/-- The closed spatial unit cube, transported to the Euclidean space used by
the PDE statement. -/
def unitCube : Set Space :=
  (WithLp.equiv 2 (Fin 3 → ℝ)).symm ''
    Set.pi univ (fun _ : Fin 3 => Icc (0 : ℝ) 1)

theorem isCompact_unitCube : IsCompact unitCube := by
  exact (isCompact_univ_pi (fun _ : Fin 3 => isCompact_Icc)).image
    (PiLp.continuous_toLp 2 (fun _ : Fin 3 => ℝ))

/-- Integer coordinate translation. -/
def integerShift (n : Fin 3 → ℤ) : Space :=
  ∑ i : Fin 3, n i • coordinateVector i

@[simp] theorem integerShift_apply (n : Fin 3 → ℤ) (j : Fin 3) :
    integerShift n j = (n j : ℝ) := by
  change (EuclideanSpace.proj j) (integerShift n) = _
  simp [integerShift, coordinateVector, zsmul_eq_mul]

/-- The coordinatewise fractional part of a spatial point. -/
def fractionalPoint (x : Space) : Space :=
  (WithLp.equiv 2 (Fin 3 → ℝ)).symm (fun i => Int.fract (x i))

theorem fractionalPoint_mem_unitCube (x : Space) : fractionalPoint x ∈ unitCube := by
  refine ⟨fun i => Int.fract (x i), ?_, rfl⟩
  intro i _
  exact ⟨Int.fract_nonneg _, (Int.fract_lt_one _).le⟩

theorem fractionalPoint_eq_sub (x : Space) :
    fractionalPoint x = x - integerShift (fun i => Int.floor (x i)) := by
  ext i
  simp only [fractionalPoint, WithLp.equiv_symm_apply, PiLp.toLp_apply, PiLp.sub_apply,
    integerShift_apply]
  exact (Int.self_sub_floor _).symm

variable {V : Type*}

theorem periodic_integerShift {g : SpaceTime → V}
    (hg : UnitSpatialPeriodsOn univ g) (t : ℝ) (n : Fin 3 → ℤ) :
    Function.Periodic (fun x : Space => g (t, x)) (integerShift n) := by
  have hbase (i : Fin 3) : Function.Periodic (fun x : Space => g (t, x))
      (coordinateVector i) := fun x => hg t (mem_univ _) x i
  have hs (s : Finset (Fin 3)) : Function.Periodic (fun x : Space => g (t, x))
      (∑ i ∈ s, n i • coordinateVector i) := by
    induction s using Finset.induction_on with
    | empty => intro x; simp
    | @insert i s hi ih =>
      rw [Finset.sum_insert hi]
      exact ((hbase i).zsmul (n i)).add_period ih
  exact hs Finset.univ

/-- All points have the same field value as a point in the closed unit cube. -/
theorem periodic_fractionalPoint {g : SpaceTime → V}
    (hg : UnitSpatialPeriodsOn univ g) (t : ℝ) (x : Space) :
    g (t, fractionalPoint x) = g (t, x) := by
  rw [fractionalPoint_eq_sub]
  exact (periodic_integerShift hg t (fun i => Int.floor (x i))).sub_eq x

section Normed

variable [NormedAddCommGroup V]

/-- A bound for a continuous periodic field on a compact interval follows
from compactness of the interval times the actual fundamental cube. -/
theorem periodic_bound_on_timeInterval {g : SpaceTime → V}
    (hg : Continuous g) (hper : UnitSpatialPeriodsOn univ g) (a b : ℝ) :
    ∃ C : ℝ, 0 < C ∧ ∀ t ∈ Icc a b, ∀ x : Space, ‖g (t, x)‖ ≤ C := by
  obtain ⟨C, hC⟩ := (isCompact_Icc.prod isCompact_unitCube).exists_bound_of_continuousOn
    hg.continuousOn
  refine ⟨max C 1, lt_of_lt_of_le zero_lt_one (le_max_right _ _), ?_⟩
  intro t ht x
  rw [← periodic_fractionalPoint hper t x]
  exact (hC (t, fractionalPoint x) ⟨ht, fractionalPoint_mem_unitCube x⟩).trans
    (le_max_left _ _)

variable [NormedSpace ℝ V]

/-- Unit spatial periods pass to the full derivative tensor, including all
time and mixed derivatives. No derivative bound is assumed here. -/
theorem iteratedFDeriv_periods {f : SpaceTime → V}
    (hf : UnitSpatialPeriodsOn univ f) (m : ℕ) :
    UnitSpatialPeriodsOn univ (iteratedFDeriv ℝ m f) := by
  intro t _ x i
  have heq : (fun z : SpaceTime => f (z + (0, coordinateVector i))) = f := by
    funext z
    change f (z.1 + 0, z.2 + coordinateVector i) = f z
    simpa only [add_zero] using hf z.1 (mem_univ _) z.2 i
  have hd := iteratedFDeriv_comp_add_right (𝕜 := ℝ) (f := f)
    m (0, coordinateVector i) (t, x)
  rw [heq] at hd
  simpa using hd.symm

/-- Differentiation is local: every full derivative vanishes at times strictly
after a uniform zero-tail threshold, including derivative order zero. -/
theorem iteratedFDeriv_eq_zero_after {f : SpaceTime → V} {T : ℝ}
    (hzero : ∀ t : ℝ, T ≤ t → ∀ x : Space, f (t, x) = 0)
    (m : ℕ) {t : ℝ} (ht : T < t) (x : Space) :
    iteratedFDeriv ℝ m f (t, x) = 0 := by
  have heq : f =ᶠ[𝓝 (t, x)] (fun _ => 0) := by
    have hU : {z : SpaceTime | T < z.1} ∈ 𝓝 (t, x) :=
      (isOpen_lt continuous_const continuous_fst).mem_nhds ht
    filter_upwards [hU] with z hz
    exact hzero z.1 hz.le z.2
  have heq' : f =ᶠ[𝓝[univ] (t, x)] (fun _ => 0) := by
    simpa only [nhdsWithin_univ] using heq
  have hj := heq'.iteratedFDerivWithin_eq heq.self_of_nhds m (𝕜 := ℝ)
  simpa [iteratedFDerivWithin_univ, iteratedFDeriv_fun_zero] using hj

end Normed

/-- Every actual full derivative has arbitrary polynomial decay. The input
smoothness and periods are global; compact future time support is the exact
notion from the PDE specification. -/
theorem iteratedFDeriv_decay (f : VelocityField)
    (hf : ContDiff ℝ ∞ f) (hper : UnitSpatialPeriodsOn univ f)
    (hsupport : CompactFutureTimeSupport f) (m : ℕ) (K : ℝ) (hK : 0 ≤ K) :
    ∃ C : ℝ, 0 < C ∧ ∀ t : ℝ, 0 ≤ t → ∀ x : Space,
      ‖iteratedFDeriv ℝ m f (t, x)‖ ≤ C * (1 + t) ^ (-K) := by
  obtain ⟨T, hT, hzero⟩ := hsupport
  have hcont : Continuous (iteratedFDeriv ℝ m f) :=
    ContDiff.continuous_iteratedFDeriv
      (ENat.natCast_le_of_coe_top_le_withTop le_rfl m) hf
  obtain ⟨M, hMpos, hM⟩ := periodic_bound_on_timeInterval hcont
    (iteratedFDeriv_periods hper m) 0 (T + 1)
  let C : ℝ := M * (1 + (T + 1)) ^ K
  have hbase : 0 < 1 + (T + 1) := by linarith
  have hCpos : 0 < C := mul_pos hMpos (Real.rpow_pos_of_pos hbase K)
  refine ⟨C, hCpos, ?_⟩
  intro t ht x
  by_cases hsmall : t ≤ T + 1
  · have hpow : (1 + (T + 1)) ^ (-K) ≤ (1 + t) ^ (-K) :=
      Real.rpow_le_rpow_of_nonpos (by linarith) (by linarith)
        (neg_nonpos.mpr hK)
    have hcancel : C * (1 + (T + 1)) ^ (-K) = M := by
      dsimp [C]
      rw [mul_assoc, ← Real.rpow_add hbase]
      simp
    calc
      ‖iteratedFDeriv ℝ m f (t, x)‖ ≤ M := hM t ⟨ht, hsmall⟩ x
      _ = C * (1 + (T + 1)) ^ (-K) := hcancel.symm
      _ ≤ C * (1 + t) ^ (-K) := mul_le_mul_of_nonneg_left hpow hCpos.le
  · rw [iteratedFDeriv_eq_zero_after hzero m (by linarith : T < t) x, norm_zero]
    exact mul_nonneg hCpos.le (Real.rpow_nonneg (by linarith) _)

/-- The four coordinate directions in the product spacetime norm. -/
def spacetimeCoordinate : Fin 4 → SpaceTime :=
  Fin.cases (1, 0) (fun i : Fin 3 => (0, coordinateVector i))

@[simp] theorem norm_spacetimeCoordinate (i : Fin 4) : ‖spacetimeCoordinate i‖ = 1 := by
  refine Fin.cases ?_ ?_ i
  · simp [spacetimeCoordinate, Prod.norm_def]
  · intro j
    simp [spacetimeCoordinate, Prod.norm_def, coordinateVector]

/-- Evaluating a full derivative on coordinate unit vectors, then taking one
output component, is controlled by its full multilinear operator norm. -/
theorem mixed_component_le_full (f : VelocityField) (m : ℕ) (z : SpaceTime)
    (directions : Fin m → Fin 4) (j : Fin 3) :
    |(iteratedFDeriv ℝ m f z (fun i => spacetimeCoordinate (directions i))) j| ≤
      ‖iteratedFDeriv ℝ m f z‖ := by
  have hproj := PiLp.norm_apply_le
    (iteratedFDeriv ℝ m f z (fun i => spacetimeCoordinate (directions i))) j
  have hop := (iteratedFDeriv ℝ m f z).le_opNorm
    (fun i => spacetimeCoordinate (directions i))
  have heval : ‖iteratedFDeriv ℝ m f z (fun i => spacetimeCoordinate (directions i))‖ ≤
      ‖iteratedFDeriv ℝ m f z‖ := by simpa using hop
  simpa only [Real.norm_eq_abs] using hproj.trans heval

/-- Arbitrary polynomial decay for every coordinate mixed differential of
every output component, with the same constant as the full derivative bound. -/
theorem mixed_coordinate_decay (f : VelocityField)
    (hf : ContDiff ℝ ∞ f) (hper : UnitSpatialPeriodsOn univ f)
    (hsupport : CompactFutureTimeSupport f) (m : ℕ) (K : ℝ) (hK : 0 ≤ K) :
    ∃ C : ℝ, 0 < C ∧ ∀ t : ℝ, 0 ≤ t → ∀ x : Space,
      ∀ directions : Fin m → Fin 4, ∀ j : Fin 3,
        |(iteratedFDeriv ℝ m f (t, x) (fun i => spacetimeCoordinate (directions i))) j| ≤
          C * (1 + t) ^ (-K) := by
  obtain ⟨C, hC, hbound⟩ := iteratedFDeriv_decay f hf hper hsupport m K hK
  refine ⟨C, hC, ?_⟩
  intro t ht x directions j
  exact (mixed_component_le_full f m (t, x) directions j).trans (hbound t ht x)

end

end NavierStokes.CompactForceDecay
