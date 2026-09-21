/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

import LeanPool.CoarseGraining.Homogenization.Deterministic.ConstantCoefficientDirichletBesov.OverlapLp

/-! # Overlap Centers -/

namespace Homogenization

noncomputable section

open MeasureTheory
open scoped BigOperators ENNReal Pointwise

/-- Fine-grid centers used by the overlapping norm at depth `j`.

The centers are descendants one generation below the cube scale.  We retain
only those centers whose overlapping cube lies inside the parent cube; this
keeps the local Dirichlet theorem from sampling outside the cube where the
solution representative has no Sobolev control. -/
noncomputable def overlapCentersAtDepth {d : ℕ}
    (Q : TriadicCube d) (j : ℕ) : Finset (TriadicCube d) := by
  classical
  exact (descendantsAtDepth Q (j + 1)).filter
    (fun S => overlapCubeSet S ⊆ cubeSet Q)

theorem mem_overlapCentersAtDepth_iff {d : ℕ}
    {Q S : TriadicCube d} {j : ℕ} :
    S ∈ overlapCentersAtDepth Q j ↔
      S ∈ descendantsAtDepth Q (j + 1) ∧ overlapCubeSet S ⊆ cubeSet Q := by
  classical
  simp [overlapCentersAtDepth]

theorem mem_descendantsAtDepth_of_mem_overlapCentersAtDepth {d : ℕ}
    {Q S : TriadicCube d} {j : ℕ}
    (hS : S ∈ overlapCentersAtDepth Q j) :
    S ∈ descendantsAtDepth Q (j + 1) :=
  (mem_overlapCentersAtDepth_iff.mp hS).1

theorem overlapCubeSet_subset_cubeSet_of_mem_overlapCentersAtDepth {d : ℕ}
    {Q S : TriadicCube d} {j : ℕ}
    (hS : S ∈ overlapCentersAtDepth Q j) :
    overlapCubeSet S ⊆ cubeSet Q :=
  (mem_overlapCentersAtDepth_iff.mp hS).2

theorem openOverlapCubeSet_subset_openCubeSet_of_mem_overlapCentersAtDepth {d : ℕ}
    {Q S : TriadicCube d} {j : ℕ}
    (hS : S ∈ overlapCentersAtDepth Q j) :
    openOverlapCubeSet S ⊆ openCubeSet Q := by
  have hsub : openOverlapCubeSet S ⊆ cubeSet Q :=
    (openOverlapCubeSet_subset_overlapCubeSet S).trans
      (overlapCubeSet_subset_cubeSet_of_mem_overlapCentersAtDepth hS)
  have hsub_int : openOverlapCubeSet S ⊆ interior (cubeSet Q) :=
    (isOpen_openOverlapCubeSet S).subset_interior_iff.2 hsub
  simpa [interior_cubeSet_eq_openCubeSet Q] using hsub_int

theorem memLp_normalizedOverlapCubeMeasure_of_memLp_normalizedCubeMeasure
    {d : ℕ} {E : Type*} [NormedAddCommGroup E]
    {Q S : TriadicCube d} {j : ℕ} {p : ℝ≥0∞} {f : Vec d → E}
    (hS : S ∈ overlapCentersAtDepth Q j)
    (hf : MeasureTheory.MemLp f p (normalizedCubeMeasure Q)) :
    MeasureTheory.MemLp f p (normalizedOverlapCubeMeasure S) := by
  have hfCube : MeasureTheory.MemLp f p (cubeMeasure Q) :=
    memLp_cubeMeasure_of_memLp_normalizedCubeMeasure Q hf
  have hle : overlapCubeMeasure S ≤ cubeMeasure Q := by
    rw [overlapCubeMeasure, cubeMeasure]
    exact MeasureTheory.Measure.restrict_mono_set MeasureTheory.volume
      (overlapCubeSet_subset_cubeSet_of_mem_overlapCentersAtDepth hS)
  have hfOverlap : MeasureTheory.MemLp f p (overlapCubeMeasure S) :=
    hfCube.mono_measure hle
  simpa [normalizedOverlapCubeMeasure] using
    hfOverlap.smul_measure ENNReal.ofReal_ne_top

theorem overlapCubeScaleFactor_eq_cubeScaleFactor_div_pow_of_mem_overlapCentersAtDepth
    {d : ℕ} {Q S : TriadicCube d} {j : ℕ}
    (hS : S ∈ overlapCentersAtDepth Q j) :
    overlapCubeScaleFactor S = cubeScaleFactor Q / (3 : ℝ) ^ j := by
  have hdesc : S ∈ descendantsAtDepth Q (j + 1) :=
    mem_descendantsAtDepth_of_mem_overlapCentersAtDepth hS
  unfold overlapCubeScaleFactor
  rw [cubeScaleFactor_eq_div_pow_of_mem_descendantsAtDepth hdesc]
  have hpow_succ : (3 : ℝ) ^ (j + 1) = (3 : ℝ) ^ j * 3 := by
    rw [pow_succ]
  rw [hpow_succ]
  field_simp [pow_ne_zero j (show (3 : ℝ) ≠ 0 by norm_num)]

theorem inv_cubeScaleFactor_eq_three_mul_inv_depthScale_of_mem_overlapCentersAtDepth
    {d : ℕ} {Q S : TriadicCube d} {j : ℕ}
    (hS : S ∈ overlapCentersAtDepth Q j) :
    (cubeScaleFactor S)⁻¹ =
      3 * (cubeScaleFactor Q / (3 : ℝ) ^ j)⁻¹ := by
  have hscale :=
    overlapCubeScaleFactor_eq_cubeScaleFactor_div_pow_of_mem_overlapCentersAtDepth hS
  unfold overlapCubeScaleFactor at hscale
  calc
    (cubeScaleFactor S)⁻¹ = (3 * cubeScaleFactor S)⁻¹ * 3 := by
      have hSpos : 0 < cubeScaleFactor S := by
        simpa [cubeScaleFactor] using
          (zpow_pos (show (0 : ℝ) < 3 by norm_num) S.scale)
      field_simp [hSpos.ne']
    _ = (cubeScaleFactor Q / (3 : ℝ) ^ j)⁻¹ * 3 := by
      rw [hscale]
    _ = 3 * (cubeScaleFactor Q / (3 : ℝ) ^ j)⁻¹ := by
      ring

theorem overlapCubeVolume_eq_cubeVolume_div_pow_of_mem_overlapCentersAtDepth
    {d : ℕ} {Q S : TriadicCube d} {j : ℕ}
    (hS : S ∈ overlapCentersAtDepth Q j) :
    overlapCubeVolume S = cubeVolume Q / (((3 : ℝ) ^ d) ^ j) := by
  have hscale :=
    overlapCubeScaleFactor_eq_cubeScaleFactor_div_pow_of_mem_overlapCentersAtDepth hS
  unfold overlapCubeVolume
  rw [hscale, div_pow, cubeVolume_eq_scaleFactor_pow]
  congr 1
  rw [← pow_mul, ← pow_mul, Nat.mul_comm]

theorem middleDescendant_succ_mem_overlapCentersAtDepth {d : ℕ}
    (Q : TriadicCube d) (j : ℕ) :
    middleDescendant Q (j + 1) ∈ overlapCentersAtDepth Q j := by
  rw [mem_overlapCentersAtDepth_iff]
  exact ⟨middleDescendant_mem_descendantsAtDepth Q (j + 1),
    overlapCubeSet_middleDescendant_succ_subset_cubeSet Q j⟩

theorem overlapCentersAtDepth_nonempty {d : ℕ}
    (Q : TriadicCube d) (j : ℕ) :
    (overlapCentersAtDepth Q j).Nonempty :=
  ⟨middleDescendant Q (j + 1),
    middleDescendant_succ_mem_overlapCentersAtDepth Q j⟩

theorem overlapCentersAtDepth_card_pos {d : ℕ}
    (Q : TriadicCube d) (j : ℕ) :
    0 < (overlapCentersAtDepth Q j).card :=
  Finset.card_pos.mpr (overlapCentersAtDepth_nonempty Q j)

theorem one_le_overlapCentersAtDepth_card {d : ℕ}
    (Q : TriadicCube d) (j : ℕ) :
    1 ≤ (overlapCentersAtDepth Q j).card :=
  overlapCentersAtDepth_card_pos Q j

theorem overlapCentersAtDepth_card_ne_zero {d : ℕ}
    (Q : TriadicCube d) (j : ℕ) :
    (overlapCentersAtDepth Q j).card ≠ 0 :=
  ne_of_gt (overlapCentersAtDepth_card_pos Q j)

theorem overlapCentersAtDepth_card_real_ne_zero {d : ℕ}
    (Q : TriadicCube d) (j : ℕ) :
    (((overlapCentersAtDepth Q j).card : ℕ) : ℝ) ≠ 0 := by
  exact_mod_cast overlapCentersAtDepth_card_ne_zero Q j

theorem overlapCentersAtDepth_card_le_descendantsAtDepth_card {d : ℕ}
    (Q : TriadicCube d) (j : ℕ) :
    (overlapCentersAtDepth Q j).card ≤
      (descendantsAtDepth Q (j + 1)).card := by
  classical
  unfold overlapCentersAtDepth
  exact Finset.card_filter_le _ _

theorem overlapCentersAtDepth_card_le_pow {d : ℕ}
    (Q : TriadicCube d) (j : ℕ) :
    (overlapCentersAtDepth Q j).card ≤ (3 ^ d) ^ (j + 1) := by
  rw [← descendantsAtDepth_card Q (j + 1)]
  exact overlapCentersAtDepth_card_le_descendantsAtDepth_card Q j

theorem middleChildCube_mem_overlapCentersAtDepth_of_mem_descendantsAtDepth
    {d : ℕ} {Q R : TriadicCube d} {j : ℕ}
    (hR : R ∈ descendantsAtDepth Q j) :
    middleChildCube R ∈ overlapCentersAtDepth Q j := by
  rw [mem_overlapCentersAtDepth_iff]
  refine ⟨?_, ?_⟩
  · rw [descendantsAtDepth_succ]
    exact Finset.mem_biUnion.mpr
      ⟨R, hR, middleChildCube_mem_childCubes R⟩
  · intro x hx
    have hxR : x ∈ cubeSet R := by
      simpa [overlapCubeSet_middleChildCube_eq_cubeSet R] using hx
    exact cubeSet_subset_of_mem_descendantsAtDepth hR hxR

theorem exists_mem_overlapCentersAtDepth_of_mem_cubeSet {d : ℕ}
    {Q : TriadicCube d} {x : Vec d} (j : ℕ)
    (hx : x ∈ cubeSet Q) :
    ∃ S ∈ overlapCentersAtDepth Q j, x ∈ overlapCubeSet S := by
  rcases exists_mem_descendantsAtDepth_of_mem_cubeSet j hx with ⟨R, hR, hxR⟩
  refine ⟨middleChildCube R,
    middleChildCube_mem_overlapCentersAtDepth_of_mem_descendantsAtDepth hR, ?_⟩
  simpa [overlapCubeSet_middleChildCube_eq_cubeSet R] using hxR

theorem cubeSet_subset_iUnion_overlapCentersAtDepth {d : ℕ}
    (Q : TriadicCube d) (j : ℕ) :
    cubeSet Q ⊆
      ⋃ S ∈ (overlapCentersAtDepth Q j : Set (TriadicCube d)),
        overlapCubeSet S := by
  intro x hx
  rcases exists_mem_overlapCentersAtDepth_of_mem_cubeSet (Q := Q) j hx
    with ⟨S, hS, hxS⟩
  exact Set.mem_iUnion.mpr ⟨S, Set.mem_iUnion.mpr ⟨hS, hxS⟩⟩

theorem descendantsAtDepth_card_le_overlapCentersAtDepth_card {d : ℕ}
    (Q : TriadicCube d) (j : ℕ) :
    (descendantsAtDepth Q j).card ≤ (overlapCentersAtDepth Q j).card := by
  classical
  refine Finset.card_le_card_of_injOn (fun R => middleChildCube R) ?_ ?_
  · intro R hR
    exact middleChildCube_mem_overlapCentersAtDepth_of_mem_descendantsAtDepth hR
  · intro R _hR S _hS hRS
    exact middleChildCube_injective hRS

theorem pow_le_overlapCentersAtDepth_card {d : ℕ}
    (Q : TriadicCube d) (j : ℕ) :
    (3 ^ d) ^ j ≤ (overlapCentersAtDepth Q j).card := by
  rw [← descendantsAtDepth_card Q j]
  exact descendantsAtDepth_card_le_overlapCentersAtDepth_card Q j

theorem cubeVolume_le_card_mul_overlapCubeVolume_of_mem_overlapCentersAtDepth
    {d : ℕ} {Q S : TriadicCube d} {j : ℕ}
    (hS : S ∈ overlapCentersAtDepth Q j) :
    cubeVolume Q ≤ ((overlapCentersAtDepth Q j).card : ℝ) * overlapCubeVolume S := by
  have hpow_cast :
      (((3 ^ d) ^ j : ℕ) : ℝ) = (((3 : ℝ) ^ d) ^ j) := by
    norm_num
  have hcard_nat := pow_le_overlapCentersAtDepth_card Q j
  have hcard :
      (((3 : ℝ) ^ d) ^ j) ≤ ((overlapCentersAtDepth Q j).card : ℝ) := by
    rw [← hpow_cast]
    exact_mod_cast hcard_nat
  have hden_pos : 0 < (((3 : ℝ) ^ d) ^ j) := by positivity
  have hquot_nonneg :
      0 ≤ cubeVolume Q / (((3 : ℝ) ^ d) ^ j) :=
    div_nonneg (cubeVolume_nonneg Q) hden_pos.le
  calc
    cubeVolume Q =
        (((3 : ℝ) ^ d) ^ j) *
          (cubeVolume Q / (((3 : ℝ) ^ d) ^ j)) := by
      field_simp [hden_pos.ne']
    _ ≤ ((overlapCentersAtDepth Q j).card : ℝ) *
          (cubeVolume Q / (((3 : ℝ) ^ d) ^ j)) := by
      exact mul_le_mul_of_nonneg_right hcard hquot_nonneg
    _ = ((overlapCentersAtDepth Q j).card : ℝ) * overlapCubeVolume S := by
      rw [overlapCubeVolume_eq_cubeVolume_div_pow_of_mem_overlapCentersAtDepth hS]

theorem card_mul_overlapCubeVolume_le_pow_mul_cubeVolume_of_mem_overlapCentersAtDepth
    {d : ℕ} {Q S : TriadicCube d} {j : ℕ}
    (hS : S ∈ overlapCentersAtDepth Q j) :
    ((overlapCentersAtDepth Q j).card : ℝ) * overlapCubeVolume S ≤
      (3 ^ d : ℝ) * cubeVolume Q := by
  have hcard_nat := overlapCentersAtDepth_card_le_pow Q j
  have hcard :
      ((overlapCentersAtDepth Q j).card : ℝ) ≤
        (((3 ^ d) ^ (j + 1) : ℕ) : ℝ) := by
    exact_mod_cast hcard_nat
  have hpow_cast :
      (((3 ^ d) ^ (j + 1) : ℕ) : ℝ) =
        (((3 : ℝ) ^ d) ^ (j + 1)) := by
    norm_num
  rw [hpow_cast] at hcard
  have hvol_nonneg : 0 ≤ overlapCubeVolume S := overlapCubeVolume_nonneg S
  calc
    ((overlapCentersAtDepth Q j).card : ℝ) * overlapCubeVolume S
        ≤ (((3 : ℝ) ^ d) ^ (j + 1)) * overlapCubeVolume S := by
          exact mul_le_mul_of_nonneg_right hcard hvol_nonneg
    _ =
        (((3 : ℝ) ^ d) ^ (j + 1)) *
          (cubeVolume Q / (((3 : ℝ) ^ d) ^ j)) := by
          rw [overlapCubeVolume_eq_cubeVolume_div_pow_of_mem_overlapCentersAtDepth hS]
    _ = (3 ^ d : ℝ) * cubeVolume Q := by
          have hbase_ne : (3 : ℝ) ^ d ≠ 0 := by positivity
          rw [pow_succ]
          field_simp [hbase_ne, pow_ne_zero j hbase_ne]

theorem inv_cubeVolume_le_pow_mul_inv_card_mul_inv_overlapCubeVolume_of_mem_overlapCentersAtDepth
    {d : ℕ} {Q S : TriadicCube d} {j : ℕ}
    (hS : S ∈ overlapCentersAtDepth Q j) :
    (cubeVolume Q)⁻¹ ≤
      (3 ^ d : ℝ) *
        (((overlapCentersAtDepth Q j).card : ℝ)⁻¹ *
          (overlapCubeVolume S)⁻¹) := by
  let a : ℝ := ((overlapCentersAtDepth Q j).card : ℝ) * overlapCubeVolume S
  let b : ℝ := cubeVolume Q
  let K : ℝ := (3 ^ d : ℝ)
  have ha_pos : 0 < a := by
    dsimp [a]
    exact mul_pos (by exact_mod_cast overlapCentersAtDepth_card_pos Q j)
      (overlapCubeVolume_pos S)
  have hb_pos : 0 < b := by
    dsimp [b]
    exact cubeVolume_pos Q
  have hab : a ≤ K * b := by
    simpa [a, b, K] using
      card_mul_overlapCubeVolume_le_pow_mul_cubeVolume_of_mem_overlapCentersAtDepth
        hS
  have hmain : a * b⁻¹ ≤ K := by
    rw [← div_eq_mul_inv]
    exact (div_le_iff₀ hb_pos).2 hab
  have hmain' : b⁻¹ ≤ K * a⁻¹ := by
    have hmain_comm : b⁻¹ * a ≤ K := by
      simpa [mul_comm] using hmain
    rw [← div_eq_mul_inv]
    exact (le_div_iff₀ ha_pos).2 hmain_comm
  simpa [a, b, K, mul_inv, mul_assoc, mul_left_comm, mul_comm] using hmain'

theorem inv_card_mul_inv_overlapCubeVolume_le_inv_cubeVolume_of_mem_overlapCentersAtDepth
    {d : ℕ} {Q S : TriadicCube d} {j : ℕ}
    (hS : S ∈ overlapCentersAtDepth Q j) :
    (((overlapCentersAtDepth Q j).card : ℝ)⁻¹) *
      (overlapCubeVolume S)⁻¹ ≤
      (cubeVolume Q)⁻¹ := by
  have hcard_pos : 0 < ((overlapCentersAtDepth Q j).card : ℝ) := by
    exact_mod_cast overlapCentersAtDepth_card_pos Q j
  have hprod_pos :
      0 < ((overlapCentersAtDepth Q j).card : ℝ) * overlapCubeVolume S :=
    mul_pos hcard_pos (overlapCubeVolume_pos S)
  calc
    (((overlapCentersAtDepth Q j).card : ℝ)⁻¹) *
        (overlapCubeVolume S)⁻¹ =
        (((overlapCentersAtDepth Q j).card : ℝ) * overlapCubeVolume S)⁻¹ := by
      rw [mul_inv]
    _ ≤ (cubeVolume Q)⁻¹ := by
      exact
        (inv_le_inv₀ hprod_pos (cubeVolume_pos Q)).2
          (cubeVolume_le_card_mul_overlapCubeVolume_of_mem_overlapCentersAtDepth hS)

theorem inv_card_mul_ofReal_inv_overlapCubeVolume_le_ofReal_inv_cubeVolume
    {d : ℕ} {Q S : TriadicCube d} {j : ℕ}
    (hS : S ∈ overlapCentersAtDepth Q j) :
    (((overlapCentersAtDepth Q j).card : ℝ≥0∞)⁻¹) *
        ENNReal.ofReal ((overlapCubeVolume S)⁻¹) ≤
      ENNReal.ofReal ((cubeVolume Q)⁻¹) := by
  have hcard_pos : 0 < ((overlapCentersAtDepth Q j).card : ℝ) := by
    exact_mod_cast overlapCentersAtDepth_card_pos Q j
  have hcard_inv_nonneg :
      0 ≤ (((overlapCentersAtDepth Q j).card : ℝ)⁻¹) := by positivity
  have hcard_ofReal :
      ENNReal.ofReal (((overlapCentersAtDepth Q j).card : ℝ)⁻¹) =
        (((overlapCentersAtDepth Q j).card : ℝ≥0∞)⁻¹) := by
    rw [ENNReal.ofReal_inv_of_pos hcard_pos]
    rw [ENNReal.ofReal_natCast]
  rw [← hcard_ofReal, ← ENNReal.ofReal_mul hcard_inv_nonneg]
  exact ENNReal.ofReal_le_ofReal
    (inv_card_mul_inv_overlapCubeVolume_le_inv_cubeVolume_of_mem_overlapCentersAtDepth hS)

theorem ofReal_inv_cubeVolume_le_pow_mul_inv_card_mul_ofReal_inv_overlapCubeVolume
    {d : ℕ} {Q S : TriadicCube d} {j : ℕ}
    (hS : S ∈ overlapCentersAtDepth Q j) :
    ENNReal.ofReal ((cubeVolume Q)⁻¹) ≤
      (3 ^ d : ℝ≥0∞) *
        (((overlapCentersAtDepth Q j).card : ℝ≥0∞)⁻¹ *
          ENNReal.ofReal ((overlapCubeVolume S)⁻¹)) := by
  have hcard_pos : 0 < ((overlapCentersAtDepth Q j).card : ℝ) := by
    exact_mod_cast overlapCentersAtDepth_card_pos Q j
  have hcard_inv_nonneg :
      0 ≤ (((overlapCentersAtDepth Q j).card : ℝ)⁻¹) := by positivity
  have hoverlap_inv_nonneg : 0 ≤ (overlapCubeVolume S)⁻¹ :=
    inv_nonneg.mpr (overlapCubeVolume_nonneg S)
  have hprod_nonneg :
      0 ≤ (((overlapCentersAtDepth Q j).card : ℝ)⁻¹ *
        (overlapCubeVolume S)⁻¹) :=
    mul_nonneg hcard_inv_nonneg hoverlap_inv_nonneg
  have hK_nonneg : 0 ≤ (3 ^ d : ℝ) := by positivity
  have hcard_ofReal :
      ENNReal.ofReal (((overlapCentersAtDepth Q j).card : ℝ)⁻¹) =
        (((overlapCentersAtDepth Q j).card : ℝ≥0∞)⁻¹) := by
    rw [ENNReal.ofReal_inv_of_pos hcard_pos]
    rw [ENNReal.ofReal_natCast]
  have hK_ofReal : ENNReal.ofReal (3 ^ d : ℝ) = (3 ^ d : ℝ≥0∞) := by
    norm_num
  rw [← hK_ofReal, ← hcard_ofReal]
  rw [← ENNReal.ofReal_mul hcard_inv_nonneg]
  rw [← ENNReal.ofReal_mul hK_nonneg]
  exact ENNReal.ofReal_le_ofReal
    (by
      simpa [mul_assoc] using
        inv_cubeVolume_le_pow_mul_inv_card_mul_inv_overlapCubeVolume_of_mem_overlapCentersAtDepth
          hS)

/-- Reverse normalized integral comparison for families indexed by retained
overlap centers.  Integrating a sum of overlap-supported nonnegative fields on
the parent normalized cube is controlled by the average of the normalized
overlap-cube integrals, with only a dimension constant. -/
theorem overlapCentersAtDepth_lintegral_sum_indicator_normalizedCubeMeasure_le
    {d : ℕ} (Q : TriadicCube d) (j : ℕ)
    {f : TriadicCube d → Vec d → ℝ≥0∞}
    (hfQ :
      ∀ S ∈ overlapCentersAtDepth Q j,
        AEMeasurable
          ((overlapCubeSet S).indicator (f S))
          (MeasureTheory.volume.restrict (cubeSet Q))) :
    ∫⁻ x,
        (overlapCentersAtDepth Q j).sum
          (fun S => (overlapCubeSet S).indicator (f S) x)
        ∂ normalizedCubeMeasure Q
      ≤
        (3 ^ d : ℝ≥0∞) *
          (((overlapCentersAtDepth Q j).card : ℝ≥0∞)⁻¹ *
            (overlapCentersAtDepth Q j).sum
              (fun S => ∫⁻ x, f S x ∂ normalizedOverlapCubeMeasure S)) := by
  classical
  let D : Finset (TriadicCube d) := overlapCentersAtDepth Q j
  let parentCoeff : ℝ≥0∞ := ENNReal.ofReal ((cubeVolume Q)⁻¹)
  let K : ℝ≥0∞ := (3 ^ d : ℝ≥0∞)
  let childCoeff : TriadicCube d → ℝ≥0∞ :=
    fun S => ENNReal.ofReal ((overlapCubeVolume S)⁻¹)
  let I : TriadicCube d → ℝ≥0∞ :=
    fun S => ∫⁻ x in overlapCubeSet S, f S x ∂MeasureTheory.volume
  have hparent :
      ∫⁻ x,
          D.sum (fun S => (overlapCubeSet S).indicator (f S) x)
          ∂ normalizedCubeMeasure Q =
        parentCoeff *
          ∫⁻ x in cubeSet Q,
            D.sum (fun S => (overlapCubeSet S).indicator (f S) x)
            ∂MeasureTheory.volume := by
    simpa [D, parentCoeff] using
      lintegral_normalizedCubeMeasure_eq Q
        (fun x =>
          D.sum (fun S => (overlapCubeSet S).indicator (f S) x))
  have hcube_sum :
      ∫⁻ x in cubeSet Q,
          D.sum (fun S => (overlapCubeSet S).indicator (f S) x)
          ∂MeasureTheory.volume =
        D.sum I := by
    calc
      ∫⁻ x in cubeSet Q,
          D.sum (fun S => (overlapCubeSet S).indicator (f S) x)
          ∂MeasureTheory.volume
          =
            D.sum
              (fun S =>
                ∫⁻ x in cubeSet Q,
                  (overlapCubeSet S).indicator (f S) x
                  ∂MeasureTheory.volume) := by
            rw [MeasureTheory.lintegral_finsetSum' D]
            intro S hS
            exact hfQ S (by simpa [D] using hS)
      _ = D.sum I := by
            refine Finset.sum_congr rfl ?_
            intro S hS
            have hsubset :
                overlapCubeSet S ⊆ cubeSet Q :=
              overlapCubeSet_subset_cubeSet_of_mem_overlapCentersAtDepth
                (by simpa [D] using hS)
            have hindicator :
                (cubeSet Q).indicator
                    (fun x => (overlapCubeSet S).indicator (f S) x) =
                  (overlapCubeSet S).indicator (f S) := by
              funext x
              by_cases hxS : x ∈ overlapCubeSet S
              · have hxQ : x ∈ cubeSet Q := hsubset hxS
                simp [Set.indicator, hxS, hxQ]
              · simp [Set.indicator, hxS]
            calc
              ∫⁻ x in cubeSet Q,
                  (overlapCubeSet S).indicator (f S) x
                  ∂MeasureTheory.volume
                  =
                    ∫⁻ x,
                      (cubeSet Q).indicator
                        (fun y => (overlapCubeSet S).indicator (f S) y) x
                      ∂MeasureTheory.volume := by
                    rw [MeasureTheory.lintegral_indicator (measurableSet_cubeSet Q)]
              _ = ∫⁻ x,
                    (overlapCubeSet S).indicator (f S) x
                    ∂MeasureTheory.volume := by
                    rw [hindicator]
              _ = I S := by
                    rw [MeasureTheory.lintegral_indicator
                      (measurableSet_overlapCubeSet S)]
  have hsum_coeff :
      parentCoeff * D.sum I ≤
        K * ((D.card : ℝ≥0∞)⁻¹ *
          D.sum (fun S => childCoeff S * I S)) := by
    calc
      parentCoeff * D.sum I
          = D.sum (fun S => parentCoeff * I S) := by
            rw [Finset.mul_sum]
      _ ≤ D.sum
            (fun S =>
              K * (((D.card : ℝ≥0∞)⁻¹ * childCoeff S) * I S)) := by
            refine Finset.sum_le_sum ?_
            intro S hS
            have hcoeff :
                parentCoeff ≤
                  K * (((D.card : ℝ≥0∞)⁻¹ * childCoeff S)) := by
              simpa [D, parentCoeff, K, childCoeff, mul_assoc] using
                ofReal_inv_cubeVolume_le_pow_mul_inv_card_mul_ofReal_inv_overlapCubeVolume
                  (by simpa [D] using hS)
            calc
              parentCoeff * I S
                  ≤ (K * (((D.card : ℝ≥0∞)⁻¹ * childCoeff S))) * I S := by
                    exact mul_le_mul_of_nonneg_right hcoeff zero_le
              _ = K * (((D.card : ℝ≥0∞)⁻¹ * childCoeff S) * I S) := by
                    rw [mul_assoc]
      _ = D.sum
            (fun S =>
              K * ((D.card : ℝ≥0∞)⁻¹ * (childCoeff S * I S))) := by
            refine Finset.sum_congr rfl ?_
            intro S _hS
            rw [mul_assoc ((D.card : ℝ≥0∞)⁻¹) (childCoeff S) (I S)]
      _ = K *
            D.sum
              (fun S => (D.card : ℝ≥0∞)⁻¹ * (childCoeff S * I S)) := by
            rw [Finset.mul_sum]
      _ = K * ((D.card : ℝ≥0∞)⁻¹ *
            D.sum (fun S => childCoeff S * I S)) := by
            congr 1
            rw [Finset.mul_sum]
  calc
    ∫⁻ x,
        (overlapCentersAtDepth Q j).sum
          (fun S => (overlapCubeSet S).indicator (f S) x)
        ∂ normalizedCubeMeasure Q
        =
          parentCoeff * D.sum I := by
          rw [hparent, hcube_sum]
    _ ≤
        K * ((D.card : ℝ≥0∞)⁻¹ *
          D.sum (fun S => childCoeff S * I S)) := hsum_coeff
    _ =
        (3 ^ d : ℝ≥0∞) *
          (((overlapCentersAtDepth Q j).card : ℝ≥0∞)⁻¹ *
            (overlapCentersAtDepth Q j).sum
              (fun S => ∫⁻ x, f S x ∂ normalizedOverlapCubeMeasure S)) := by
          refine congrArg (fun z => K * ((D.card : ℝ≥0∞)⁻¹ * z)) ?_
          refine Finset.sum_congr rfl ?_
          intro S _hS
          simpa [childCoeff, I] using
            (lintegral_normalizedOverlapCubeMeasure_eq S (f S)).symm

/-- The overlap centers at depth `j` whose overlap cube contains `x`. -/
noncomputable def overlapCentersAtDepthContaining {d : ℕ}
    (Q : TriadicCube d) (j : ℕ) (x : Vec d) : Finset (TriadicCube d) := by
  classical
  exact (overlapCentersAtDepth Q j).filter fun S => x ∈ overlapCubeSet S

theorem mem_overlapCentersAtDepthContaining_iff {d : ℕ}
    {Q S : TriadicCube d} {j : ℕ} {x : Vec d} :
    S ∈ overlapCentersAtDepthContaining Q j x ↔
      S ∈ overlapCentersAtDepth Q j ∧ x ∈ overlapCubeSet S := by
  classical
  simp [overlapCentersAtDepthContaining]

theorem cubeColor_injOn_overlapCentersAtDepthContaining {d : ℕ}
    (Q : TriadicCube d) (j : ℕ) (x : Vec d) :
    Set.InjOn cubeColor (overlapCentersAtDepthContaining Q j x : Set (TriadicCube d)) := by
  intro R hR S hS hcolor
  rcases mem_overlapCentersAtDepthContaining_iff.mp hR with ⟨hRcenter, hxR⟩
  rcases mem_overlapCentersAtDepthContaining_iff.mp hS with ⟨hScenter, hxS⟩
  by_contra hne
  have hscale :
      R.scale = S.scale := by
    calc
      R.scale = Q.scale - ((j + 1 : ℕ) : ℤ) := by
        simpa using
          scale_eq_sub_of_mem_descendantsAtDepth
            (mem_descendantsAtDepth_of_mem_overlapCentersAtDepth hRcenter)
      _ = S.scale := by
        symm
        simpa using
          scale_eq_sub_of_mem_descendantsAtDepth
            (mem_descendantsAtDepth_of_mem_overlapCentersAtDepth hScenter)
  exact
    (Set.disjoint_left.mp
      (disjoint_overlapCubeSet_of_scale_eq_of_cubeColor_eq_of_ne hscale hcolor hne))
      hxR hxS

theorem overlapCentersAtDepthContaining_card_le_pow {d : ℕ}
    (Q : TriadicCube d) (j : ℕ) (x : Vec d) :
    (overlapCentersAtDepthContaining Q j x).card ≤ 3 ^ d := by
  classical
  have hcard_univ :
      (overlapCentersAtDepthContaining Q j x).card ≤
        (Finset.univ : Finset (CubeColor d)).card := by
    refine Finset.card_le_card_of_injOn cubeColor ?_ ?_
    · intro S _hS
      simp
    · exact cubeColor_injOn_overlapCentersAtDepthContaining Q j x
  simpa [card_cubeColor] using hcard_univ

/-- Pointwise finite-overlap bound for the overlapping cubes.  This is the
indicator form of the multiplicity estimate: inside the parent cube at most
`3^d` overlap cubes contain a point, and outside the parent cube none of the
retained overlap cubes contribute. -/
theorem overlapCentersAtDepth_sum_indicator_le_mul_cubeSet_indicator {d : ℕ}
    (Q : TriadicCube d) (j : ℕ) (f : Vec d → ℝ≥0∞) :
    (fun x => ∑ S ∈ overlapCentersAtDepth Q j,
        (overlapCubeSet S).indicator f x) ≤
      fun x => (3 ^ d : ℝ≥0∞) * (cubeSet Q).indicator f x := by
  classical
  intro x
  let D := overlapCentersAtDepth Q j
  by_cases hxQ : x ∈ cubeSet Q
  · have hsum_eq :
        ∑ S ∈ D, (overlapCubeSet S).indicator f x =
          ∑ S ∈ overlapCentersAtDepthContaining Q j x, f x := by
      change
        ∑ S ∈ D, (overlapCubeSet S).indicator f x =
          ∑ S ∈ D.filter (fun S => x ∈ overlapCubeSet S), f x
      rw [Finset.sum_filter]
      refine Finset.sum_congr rfl ?_
      intro S hS
      by_cases hxS : x ∈ overlapCubeSet S
      · simp [Set.indicator, hxS]
      · simp [Set.indicator, hxS]
    have hcard :
        ((overlapCentersAtDepthContaining Q j x).card : ℝ≥0∞) ≤
          (3 ^ d : ℝ≥0∞) := by
      exact_mod_cast overlapCentersAtDepthContaining_card_le_pow Q j x
    calc
      ∑ S ∈ D, (overlapCubeSet S).indicator f x
          = (overlapCentersAtDepthContaining Q j x).card • f x := by
            rw [hsum_eq, Finset.sum_const]
      _ = ((overlapCentersAtDepthContaining Q j x).card : ℝ≥0∞) * f x := by
            rw [nsmul_eq_mul]
      _ ≤ (3 ^ d : ℝ≥0∞) * f x := by
            exact mul_le_mul_left hcard (f x)
      _ = (3 ^ d : ℝ≥0∞) * (cubeSet Q).indicator f x := by
            simp [Set.indicator, hxQ]
  · have hzero :
        ∑ S ∈ D, (overlapCubeSet S).indicator f x = 0 := by
      refine Finset.sum_eq_zero ?_
      intro S hS
      have hxS : x ∉ overlapCubeSet S := by
        intro hxS'
        exact hxQ (overlapCubeSet_subset_cubeSet_of_mem_overlapCentersAtDepth hS hxS')
      simp [Set.indicator, hxS]
    change
      ∑ S ∈ D, (overlapCubeSet S).indicator f x ≤
        (3 ^ d : ℝ≥0∞) * (cubeSet Q).indicator f x
    rw [hzero]
    simp [Set.indicator, hxQ]

/-- Integrated finite-overlap bound for nonnegative functions on the retained
overlap cubes.  This is the measure-level form of the geometry API used by the
overlapping Besov endpoint. -/
theorem overlapCentersAtDepth_sum_setLIntegral_le_mul_setLIntegral_cubeSet {d : ℕ}
    (Q : TriadicCube d) (j : ℕ) {f : Vec d → ℝ≥0∞}
    (hfQ : AEMeasurable f (MeasureTheory.volume.restrict (cubeSet Q)))
    (hfS :
      ∀ S ∈ overlapCentersAtDepth Q j,
        AEMeasurable f (MeasureTheory.volume.restrict (overlapCubeSet S))) :
    ∑ S ∈ overlapCentersAtDepth Q j,
        ∫⁻ x in overlapCubeSet S, f x ∂MeasureTheory.volume
      ≤ (3 ^ d : ℝ≥0∞) *
          ∫⁻ x in cubeSet Q, f x ∂MeasureTheory.volume := by
  classical
  let D := overlapCentersAtDepth Q j
  have hleft :
      ∑ S ∈ D, ∫⁻ x in overlapCubeSet S, f x ∂MeasureTheory.volume =
        ∫⁻ x, ∑ S ∈ D, (overlapCubeSet S).indicator f x
          ∂MeasureTheory.volume := by
    calc
      ∑ S ∈ D, ∫⁻ x in overlapCubeSet S, f x ∂MeasureTheory.volume
          = ∑ S ∈ D,
              ∫⁻ x, (overlapCubeSet S).indicator f x ∂MeasureTheory.volume := by
            refine Finset.sum_congr rfl ?_
            intro S hS
            rw [MeasureTheory.lintegral_indicator (measurableSet_overlapCubeSet S)]
      _ = ∫⁻ x, ∑ S ∈ D, (overlapCubeSet S).indicator f x
            ∂MeasureTheory.volume := by
            symm
            refine MeasureTheory.lintegral_finsetSum' D ?_
            intro S hS
            exact (aemeasurable_indicator_iff (measurableSet_overlapCubeSet S)).2
              (hfS S (by simpa [D] using hS))
  have hright :
      ∫⁻ x, (3 ^ d : ℝ≥0∞) * (cubeSet Q).indicator f x
          ∂MeasureTheory.volume =
        (3 ^ d : ℝ≥0∞) *
          ∫⁻ x in cubeSet Q, f x ∂MeasureTheory.volume := by
    have hindicator :
        AEMeasurable ((cubeSet Q).indicator f) MeasureTheory.volume :=
      (aemeasurable_indicator_iff (measurableSet_cubeSet Q)).2 hfQ
    rw [MeasureTheory.lintegral_const_mul'' _ hindicator]
    rw [MeasureTheory.lintegral_indicator (measurableSet_cubeSet Q)]
  rw [hleft, ← hright]
  exact MeasureTheory.lintegral_mono
    (overlapCentersAtDepth_sum_indicator_le_mul_cubeSet_indicator Q j f)

/-- Normalized finite-overlap comparison.  Averaging the normalized overlap
cube integrals over the retained centers costs only the pointwise overlap
multiplicity `3^d` relative to the normalized parent cube integral. -/
theorem overlapCentersAtDepth_average_lintegral_normalizedOverlapCubeMeasure_le
    {d : ℕ} (Q : TriadicCube d) (j : ℕ) {f : Vec d → ℝ≥0∞}
    (hfQ : AEMeasurable f (MeasureTheory.volume.restrict (cubeSet Q)))
    (hfS :
      ∀ S ∈ overlapCentersAtDepth Q j,
        AEMeasurable f (MeasureTheory.volume.restrict (overlapCubeSet S))) :
    (((overlapCentersAtDepth Q j).card : ℝ≥0∞)⁻¹) *
        (∑ S ∈ overlapCentersAtDepth Q j,
          ∫⁻ x, f x ∂(normalizedOverlapCubeMeasure S))
      ≤ (3 ^ d : ℝ≥0∞) *
          ∫⁻ x, f x ∂(normalizedCubeMeasure Q) := by
  classical
  let D := overlapCentersAtDepth Q j
  calc
    (((overlapCentersAtDepth Q j).card : ℝ≥0∞)⁻¹) *
        (∑ S ∈ overlapCentersAtDepth Q j,
          ∫⁻ x, f x ∂(normalizedOverlapCubeMeasure S))
        = ∑ S ∈ D,
            (((overlapCentersAtDepth Q j).card : ℝ≥0∞)⁻¹) *
              ∫⁻ x, f x ∂(normalizedOverlapCubeMeasure S) := by
          change
            (((D.card : ℝ≥0∞)⁻¹) *
                (∑ S ∈ D,
                  ∫⁻ x, f x ∂(normalizedOverlapCubeMeasure S))) =
              ∑ S ∈ D,
                (((overlapCentersAtDepth Q j).card : ℝ≥0∞)⁻¹) *
                  ∫⁻ x, f x ∂(normalizedOverlapCubeMeasure S)
          rw [Finset.mul_sum]
    _ ≤ ∑ S ∈ D,
          ENNReal.ofReal ((cubeVolume Q)⁻¹) *
            ∫⁻ x in overlapCubeSet S, f x ∂MeasureTheory.volume := by
          refine Finset.sum_le_sum ?_
          intro S hS
          rw [lintegral_normalizedOverlapCubeMeasure_eq]
          calc
            (((overlapCentersAtDepth Q j).card : ℝ≥0∞)⁻¹) *
                (ENNReal.ofReal ((overlapCubeVolume S)⁻¹) *
                  ∫⁻ x in overlapCubeSet S, f x ∂MeasureTheory.volume)
                =
                ((((overlapCentersAtDepth Q j).card : ℝ≥0∞)⁻¹) *
                  ENNReal.ofReal ((overlapCubeVolume S)⁻¹)) *
                    ∫⁻ x in overlapCubeSet S, f x ∂MeasureTheory.volume := by
              rw [mul_assoc]
            _ ≤ ENNReal.ofReal ((cubeVolume Q)⁻¹) *
                  ∫⁻ x in overlapCubeSet S, f x ∂MeasureTheory.volume := by
              exact mul_le_mul_left
                (inv_card_mul_ofReal_inv_overlapCubeVolume_le_ofReal_inv_cubeVolume
                  hS)
                (∫⁻ x in overlapCubeSet S, f x ∂MeasureTheory.volume)
    _ = ENNReal.ofReal ((cubeVolume Q)⁻¹) *
          (∑ S ∈ D,
            ∫⁻ x in overlapCubeSet S, f x ∂MeasureTheory.volume) := by
          rw [Finset.mul_sum]
    _ ≤ ENNReal.ofReal ((cubeVolume Q)⁻¹) *
          ((3 ^ d : ℝ≥0∞) *
            ∫⁻ x in cubeSet Q, f x ∂MeasureTheory.volume) := by
          exact mul_le_mul_right
            (overlapCentersAtDepth_sum_setLIntegral_le_mul_setLIntegral_cubeSet
              Q j hfQ hfS)
            (ENNReal.ofReal ((cubeVolume Q)⁻¹))
    _ = (3 ^ d : ℝ≥0∞) *
          (ENNReal.ofReal ((cubeVolume Q)⁻¹) *
            ∫⁻ x in cubeSet Q, f x ∂MeasureTheory.volume) := by
          ac_rfl
    _ = (3 ^ d : ℝ≥0∞) *
          ∫⁻ x, f x ∂(normalizedCubeMeasure Q) := by
          rw [lintegral_normalizedCubeMeasure_eq]


end

end Homogenization
