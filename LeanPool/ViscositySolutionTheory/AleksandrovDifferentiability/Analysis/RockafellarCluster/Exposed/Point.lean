/-
Copyright (c) 2026 AleksandrovDifferentiability contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/

module

public import LeanPool.ViscositySolutionTheory.AleksandrovDifferentiability.Analysis.RockafellarCluster.Exposed.Thickening

/-!
Ported for Lean Pool: imports relocated and code adapted to Lean/Mathlib v4.34.0.

# Strict exposed points

This module proves the singleton exposed-face characterization, unit-normal normalization, and the
singleton norm-thickening estimate for project-local exposed points.
-/

@[expose] public noncomputable section

namespace AleksandrovDifferentiability

open scoped Gradient Topology

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

omit [CompleteSpace E] in
/-- An exposing normal selects its exposed point as a member of the corresponding exposed face. -/
theorem ExposesPoint.mem_exposedFace
    {s : Set E} {normal p : E} (hexposed : ExposesPoint s normal p) :
    p ∈ exposedFace s normal := by
  refine ⟨hexposed.1, ?_⟩
  intro r hr
  by_cases h_eq : r = p
  · subst r
    exact le_rfl
  · exact (hexposed.2 hr h_eq).le

omit [CompleteSpace E] in
/-- A strictly exposing normal has singleton exposed face. -/
theorem ExposesPoint.exposedFace_eq_singleton
    {s : Set E} {normal p : E} (hexposed : ExposesPoint s normal p) :
    exposedFace s normal = {p} := by
  ext r
  constructor
  · intro hr
    by_contra h_ne
    have hlt : inner ℝ normal r < inner ℝ normal p :=
      hexposed.2 hr.1 h_ne
    have hp_le : inner ℝ normal p ≤ inner ℝ normal r :=
      hr.2 hexposed.1
    exact (not_le_of_gt hlt) hp_le
  · intro hr
    rw [Set.mem_singleton_iff] at hr
    subst r
    exact hexposed.mem_exposedFace

omit [CompleteSpace E] in
/-- If the exposed face in direction `normal` is `{p}`, then `normal` strictly exposes `p`.

This is the converse to `ExposesPoint.exposedFace_eq_singleton`, and lets us pass from
Rockafellar's exposed-face notation back to the project-local strict exposed-point predicate. -/
theorem exposesPoint_of_exposedFace_eq_singleton
    {s : Set E} {normal p : E}
    (hface : exposedFace s normal = {p}) :
    ExposesPoint s normal p := by
  have hpface : p ∈ exposedFace s normal := by
    rw [hface]
    exact Set.mem_singleton p
  refine ⟨hpface.1, ?_⟩
  intro r hr hne
  by_contra hnot
  have hp_le_r : inner ℝ normal p ≤ inner ℝ normal r := le_of_not_gt hnot
  have hrface : r ∈ exposedFace s normal := by
    refine ⟨hr, ?_⟩
    intro z hz
    exact le_trans (hpface.2 hz) hp_le_r
  have hrp : r = p := by
    have : r ∈ ({p} : Set E) := by
      simpa [hface] using hrface
    exact Set.mem_singleton_iff.mp this
  exact hne hrp

omit [CompleteSpace E] in
/-- Strict exposure is equivalent to the exposed face being the corresponding singleton. -/
theorem exposesPoint_iff_exposedFace_eq_singleton
    {s : Set E} {normal p : E} :
    ExposesPoint s normal p ↔ exposedFace s normal = {p} :=
  ⟨fun h => h.exposedFace_eq_singleton, exposesPoint_of_exposedFace_eq_singleton⟩

omit [CompleteSpace E] in
/-- Multiplying an exposing normal by a positive scalar preserves the exposed point. -/
theorem ExposesPoint.pos_smul
    {s : Set E} {normal p : E} (hexposed : ExposesPoint s normal p)
    {c : ℝ} (hc : 0 < c) :
    ExposesPoint s (c • normal) p := by
  refine ⟨hexposed.1, ?_⟩
  intro r hr hne
  have hlt : inner ℝ normal r < inner ℝ normal p :=
    hexposed.2 hr hne
  simpa [real_inner_smul_left] using mul_lt_mul_of_pos_left hlt hc

omit [CompleteSpace E] in
/-- The usual normalization of a nonzero vector has norm one. -/
theorem norm_inv_norm_smul_eq_one_of_ne {normal : E} (hnormal : normal ≠ 0) :
    ‖‖normal‖⁻¹ • normal‖ = 1 := by
  have hpos : 0 < ‖normal‖ := norm_pos_iff.mpr hnormal
  rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hpos)]
  exact inv_mul_cancel₀ hpos.ne'

omit [CompleteSpace E] in
/-- A nonzero exposing normal can be normalized to a unit exposing normal. -/
theorem ExposesPoint.unit_smul
    {s : Set E} {normal p : E} (hexposed : ExposesPoint s normal p)
    (hnormal : normal ≠ 0) :
    ExposesPoint s (‖normal‖⁻¹ • normal) p :=
  hexposed.pos_smul (inv_pos.mpr (norm_pos_iff.mpr hnormal))

omit [CompleteSpace E] in
/-- A packaged unit-normal version of a nonzero exposing normal. -/
theorem ExposesPoint.exists_unit_smul
    {s : Set E} {normal p : E} (hexposed : ExposesPoint s normal p)
    (hnormal : normal ≠ 0) :
    ∃ unitNormal : E, ‖unitNormal‖ = 1 ∧ ExposesPoint s unitNormal p :=
  ⟨‖normal‖⁻¹ • normal, norm_inv_norm_smul_eq_one_of_ne hnormal,
    hexposed.unit_smul hnormal⟩

omit [CompleteSpace E] in
/-- If the zero normal exposes `p`, then the exposed set is contained in `{p}`. -/
theorem ExposesPoint.subset_singleton_of_zero
    {s : Set E} {p : E} (hexposed : ExposesPoint s 0 p) :
    s ⊆ {p} := by
  intro r hr
  by_contra hne
  have hlt : inner ℝ (0 : E) r < inner ℝ (0 : E) p :=
    hexposed.2 hr hne
  simp at hlt

omit [CompleteSpace E] in
/-- If an exposed set contains a point different from `p`, then any normal exposing `p` is
nonzero. -/
theorem ExposesPoint.normal_ne_zero_of_exists_ne
    {s : Set E} {normal p : E} (hexposed : ExposesPoint s normal p)
    (hnontrivial : ∃ r ∈ s, r ≠ p) :
    normal ≠ 0 := by
  intro hzero
  rcases hnontrivial with ⟨r, hr, hr_ne⟩
  have hlt : inner ℝ normal r < inner ℝ normal p :=
    hexposed.2 hr hr_ne
  subst normal
  simp at hlt

omit [CompleteSpace E] in
/-- An exposed point either has a unit exposing normal, or the whole exposed set is the singleton
containing that point.

This is the precise normalization dichotomy behind Rockafellar's phrase "choose a unit vector
which exposes `p`": outside the degenerate singleton case, the exposing normal can be normalized. -/
theorem ExposesPoint.exists_unit_or_subset_singleton
    {s : Set E} {normal p : E} (hexposed : ExposesPoint s normal p) :
    (∃ unitNormal : E, ‖unitNormal‖ = 1 ∧ ExposesPoint s unitNormal p) ∨ s ⊆ {p} := by
  by_cases hnormal : normal = 0
  · right
    subst normal
    exact hexposed.subset_singleton_of_zero
  · left
    exact hexposed.exists_unit_smul hnormal

omit [CompleteSpace E] in
/-- If `s` is contained in `{p}` and contains `p`, then every normal exposes `p` on `s`.

This packages the degenerate singleton case of exposed points. -/
theorem ExposesPoint.of_subset_singleton
    {s : Set E} {p normal : E} (hp : p ∈ s) (hsubset : s ⊆ {p}) :
    ExposesPoint s normal p := by
  refine ⟨hp, ?_⟩
  intro r hr hne
  have hrp : r = p := by
    simpa using hsubset hr
  exact False.elim (hne hrp)

omit [CompleteSpace E] in
/-- If the ambient space has some unit vector, then every exposed point admits a unit exposing
normal.

For nonzero exposing normals this is normalization. For the zero-normal case, the exposed set is
contained in `{p}`, so any ambient unit vector exposes `p` vacuously. -/
theorem ExposesPoint.exists_unit_of_exists_unit_vector
    {s : Set E} {normal p : E} (hexposed : ExposesPoint s normal p)
    (hunit : ∃ unitNormal : E, ‖unitNormal‖ = 1) :
    ∃ unitNormal : E, ‖unitNormal‖ = 1 ∧ ExposesPoint s unitNormal p := by
  rcases hexposed.exists_unit_or_subset_singleton with h | hsingleton
  · exact h
  · rcases hunit with ⟨unitNormal, hunitNorm⟩
    exact ⟨unitNormal, hunitNorm, ExposesPoint.of_subset_singleton hexposed.1 hsingleton⟩

omit [InnerProductSpace ℝ E] [CompleteSpace E] in
/-- Thickening of a singleton gives the corresponding norm estimate. -/
theorem norm_sub_lt_of_mem_normThickening_singleton
    {x p : E} {ε : ℝ} (hx : x ∈ normThickening ({p} : Set E) ε) :
    ‖x - p‖ < ε := by
  rcases hx with ⟨a, ha, hxa⟩
  rw [Set.mem_singleton_iff] at ha
  subst a
  exact hxa

end AleksandrovDifferentiability
