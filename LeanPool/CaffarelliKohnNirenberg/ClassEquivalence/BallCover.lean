/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.ClassEquivalence.CompactLp
public import LeanPool.CaffarelliKohnNirenberg.Foundation.Parabolic.Vec3Norm

/-!
# Covering a compact space-time set by ball cylinders inside a local box

The spatial factor `Ω'` of a local box is an arbitrary open set with compact
closure, so no Sobolev extension is available on it and the embedding
`H¹ ↪ L⁶` cannot be applied there.  The embedding is available on Euclidean
balls, which is why `CKN.ball_time_sobolev` is stated on `vec3Ball x₀ r`.

This file supplies the geometry that bridges the two: a compact subset of the
space-time carrier is covered by finitely many cylinders `vec3Ball x_k r_k × J`
whose balls all lie inside the spatial factor of one local box.  The time
factor is never subdivided, because the interpolation on a ball accepts an
arbitrary order-connected time interval; so the cover is indexed by one finite
family and a finite union of integrability statements closes it.
-/

@[expose] public section

open MeasureTheory MeasureTheory.Measure Set Filter
open scoped ENNReal NNReal Topology
open CKN.Foundation.Parabolic


noncomputable section

namespace CKN

/-! ### Euclidean balls inside an open set -/

/-- A Euclidean ball of `Vec3` is contained in the metric ball of the same
centre and radius for the ambient supremum norm. -/
theorem vec3Ball_subset_ball (x : Vec3) (r : ℝ) : vec3Ball x r ⊆ Metric.ball x r := by
  intro y hy
  simp only [Metric.mem_ball, dist_eq_norm]
  exact lt_of_le_of_lt (norm_le_vec3EuclideanNorm (y - x)) hy

/-- The centre of a Euclidean ball of positive radius belongs to it. -/
theorem mem_vec3Ball_self {x : Vec3} {r : ℝ} (hr : 0 < r) : x ∈ vec3Ball x r := by
  simp only [mem_vec3Ball, sub_self]
  rwa [vec3EuclideanNorm_zero]

/-- Every point of an open subset of `Vec3` has a Euclidean ball around it
inside the set. -/
theorem exists_vec3Ball_subset_of_isOpen {U : Set Vec3} (hU : IsOpen U) {x : Vec3}
    (hx : x ∈ U) :
    ∃ r : ℝ, 0 < r ∧ vec3Ball x r ⊆ U := by
  obtain ⟨ε, hε, hsub⟩ := Metric.isOpen_iff.mp hU x hx
  exact ⟨ε, hε, (vec3Ball_subset_ball x ε).trans hsub⟩

/-! ### The finite cover -/

/-- A compact subset of the space-time carrier sits inside a local box whose
spatial factor is covered, over that same compact set, by finitely many
Euclidean balls of the factor.  The time factor of the box is used unchanged
for every ball. -/
theorem exists_localBox_ball_cover_of_compact_subset {Ω : Set Vec3} {I : Set ℝ}
    (hΩ : IsOpen Ω) (hI : IsOpen I) (hIord : I.OrdConnected)
    {K : Set ParabolicPoint} (hK : IsCompact K) (hKsub : K ⊆ spaceTimeSet Ω I) :
    ∃ (Ω' : Set Vec3) (J : Set ℝ) (n : ℕ) (c : Fin n → Vec3) (r : Fin n → ℝ),
      localBox Ω I Ω' J ∧ (∀ m, 0 < r m) ∧
      (∀ m, vec3Ball (c m) (r m) ⊆ Ω') ∧
      K ⊆ ⋃ m, spaceTimeSet (vec3Ball (c m) (r m)) J := by
  obtain ⟨Ω', J, hbox, hKbox⟩ :=
    caccioppoli_localBox_of_compact_subset hΩ hI hIord hK hKsub
  set Kx : Set Vec3 := Prod.fst '' K with hKxdef
  have hKx : IsCompact Kx := hK.image continuous_fst_parabolicPoint
  have hKxsub : Kx ⊆ Ω' := by
    rintro x ⟨z, hz, rfl⟩
    exact (hKbox hz).1
  have hchoice : ∀ x ∈ Kx, ∃ r : ℝ, 0 < r ∧ vec3Ball x r ⊆ Ω' :=
    fun x hx => exists_vec3Ball_subset_of_isOpen hbox.1 (hKxsub hx)
  choose! rad hradpos hradsub using hchoice
  have hcov : Kx ⊆ ⋃ x ∈ Kx, vec3Ball x (rad x) := fun x hx =>
    mem_biUnion hx (mem_vec3Ball_self (hradpos x hx))
  obtain ⟨b, hbsub, hbfin, hbcov⟩ :=
    hKx.elim_finite_subcover_image (fun x _hx => isOpen_vec3Ball x (rad x)) hcov
  classical
  refine ⟨Ω', J, hbfin.toFinset.card,
    fun m => ((hbfin.toFinset.equivFin.symm m : { x // x ∈ hbfin.toFinset }) : Vec3),
    fun m => rad ((hbfin.toFinset.equivFin.symm m : { x // x ∈ hbfin.toFinset }) : Vec3),
    hbox, ?_, ?_, ?_⟩
  · exact fun m => hradpos _
      (hbsub (hbfin.mem_toFinset.mp (hbfin.toFinset.equivFin.symm m).2))
  · exact fun m => hradsub _
      (hbsub (hbfin.mem_toFinset.mp (hbfin.toFinset.equivFin.symm m).2))
  · intro z hz
    have hx : z.1 ∈ Kx := ⟨z, hz, rfl⟩
    obtain ⟨x, hxb, hxball⟩ := mem_iUnion₂.mp (hbcov hx)
    have hxT : x ∈ hbfin.toFinset := hbfin.mem_toFinset.mpr hxb
    refine mem_iUnion.mpr ⟨hbfin.toFinset.equivFin ⟨x, hxT⟩, ?_⟩
    simp only [Equiv.symm_apply_apply]
    exact ⟨hxball, (hKbox hz).2⟩

/-- The ball cover of the previous statement, phrased for the data clauses of
`def:sws`, which supply the openness and order-connectedness hypotheses. -/
theorem exists_localBox_ball_cover_of_data {Ω : Set Vec3} {I : Set ℝ} {q : ℝ}
    {u : ParabolicPoint → Vec3} {Du : ParabolicPoint → Fin 3 → Vec3}
    {p : ParabolicPoint → ℝ} {f : ParabolicPoint → Vec3}
    (hdata : IsSuitableWeakSolutionData Ω I q u Du p f)
    {K : Set ParabolicPoint} (hK : IsCompact K) (hKsub : K ⊆ spaceTimeSet Ω I) :
    ∃ (Ω' : Set Vec3) (J : Set ℝ) (n : ℕ) (c : Fin n → Vec3) (r : Fin n → ℝ),
      localBox Ω I Ω' J ∧ (∀ m, 0 < r m) ∧
      (∀ m, vec3Ball (c m) (r m) ⊆ Ω') ∧
      K ⊆ ⋃ m, spaceTimeSet (vec3Ball (c m) (r m)) J :=
  exists_localBox_ball_cover_of_compact_subset hdata.isOpen_space hdata.isOpen_time
    hdata.ordConnected_time hK hKsub

end CKN
