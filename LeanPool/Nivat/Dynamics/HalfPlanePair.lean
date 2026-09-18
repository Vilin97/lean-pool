/-
Copyright (c) 2026 Boon Suan Ho. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boon Suan Ho
-/

import LeanPool.Nivat.Core.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith

/-
Upstream: https://github.com/boonsuan/nivat
Commit: 84fe839635bdebb7d5e80c209b4f578a0c767fcf
Originally released under MIT; the upstream copyright and permission notice follow.

MIT License

Copyright (c) 2026 Boon Suan Ho

Permission is hereby granted, free of charge, to any person obtaining a copy
of this software and associated documentation files (the "Software"), to deal
in the Software without restriction, including without limitation the rights
to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
copies of the Software, and to permit persons to whom the Software is
furnished to do so, subject to the following conditions:

The above copyright notice and this permission notice shall be included in all
copies or substantial portions of the Software.

THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE
SOFTWARE.
-/

/-!
# Half-plane agreement from compactness

This module proves Lemma 3.1 (`lem:halfplane-pair`) of `paper/nivat.tex`.
Nearest disagreements are chosen by minimizing their squared integer norms.
A simultaneous compact subsequence of the translated configurations and their
unit normals gives agreement on an open half-plane while retaining a fixed
origin disagreement.

The main results are `exists_halfPlane_pair` for a closed shift-invariant space
and `exists_halfPlane_pair_coordinates` with the normal written as a coordinate
pair.
-/

namespace Nivat.Dynamics

open Filter Set
open scoped Topology InnerProductSpace

/-- The Euclidean plane in which the unit normals of Lemma 3.1 (`lem:halfplane-pair`) converge. -/
abbrev RealPlane := EuclideanSpace ℝ (Fin 2)

/-- The real embedding of a lattice site used in the distance estimates of Lemma 3.1
(`lem:halfplane-pair`). -/
def latticeReal (z : Lattice) : RealPlane := !₂[(z.1 : ℝ), (z.2 : ℝ)]

/-- The natural-number squared norm used to select a nearest disagreement in Lemma 3.1
(`lem:halfplane-pair`). -/
def latticeSqNorm (z : Lattice) : ℕ := (z.1 ^ 2 + z.2 ^ 2).toNat

/-- The lattice embedding preserves addition, as used when translating agreement balls in Lemma
3.1 (`lem:halfplane-pair`). -/
@[simp] theorem latticeReal_add (z w : Lattice) :
    latticeReal (z + w) = latticeReal z + latticeReal w := by
  ext i
  fin_cases i <;> simp [latticeReal]

/-- The lattice origin embeds as the real origin in the geometry of Lemma 3.1
(`lem:halfplane-pair`). -/
@[simp] theorem latticeReal_zero : latticeReal 0 = 0 := by
  ext i
  fin_cases i <;> simp [latticeReal]

/-- The squared Euclidean norm is the sum of the two squared coordinates, as in the
nearest-disagreement argument of Lemma 3.1 (`lem:halfplane-pair`). -/
@[simp] theorem latticeReal_norm_sq (z : Lattice) :
    ‖latticeReal z‖ ^ 2 = (z.1 : ℝ) ^ 2 + (z.2 : ℝ) ^ 2 := by
  simp [EuclideanSpace.real_norm_sq_eq, latticeReal, Fin.sum_univ_two]

/-- The integer measure of a disagreement equals its squared Euclidean distance. This connects
well-ordering to the geometry in Lemma 3.1 (`lem:halfplane-pair`). -/
@[simp] theorem latticeSqNorm_cast (z : Lattice) :
    (latticeSqNorm z : ℝ) = ‖latticeReal z‖ ^ 2 := by
  rw [latticeReal_norm_sq]
  dsimp [latticeSqNorm]
  exact_mod_cast (Int.toNat_of_nonneg (add_nonneg (sq_nonneg z.1) (sq_nonneg z.2)))

/-- An infinite family over a finite alphabet contains distinct configurations agreeing on any
finite window. This is the initial pigeonhole step of Lemma 3.1 (`lem:halfplane-pair`). -/
theorem exists_ne_agree_on_finite {A : Type*} [Finite A]
    (X : Set (Configuration A)) (hX : X.Infinite) (D : Finset Lattice) :
    ∃ x ∈ X, ∃ y ∈ X, x ≠ y ∧ ∀ z ∈ D, x z = y z := by
  classical
  let r : Configuration A → (D → A) := fun x z => x z.val
  obtain ⟨x, hx, y, hy, hxy, heq⟩ :=
    hX.exists_ne_map_eq_of_mapsTo (f := r) (t := Set.univ)
      (fun _ _ => Set.mem_univ _) (Set.toFinite _)
  refine ⟨x, hx, y, hy, hxy, ?_⟩
  intro z hz
  exact congrFun heq ⟨z, hz⟩

/-- Distinct configurations have a disagreement of least Euclidean distance from the origin, by
minimizing a natural-number squared norm. This is the nearest-disagreement step of Lemma 3.1
(`lem:halfplane-pair`). -/
theorem exists_nearest_disagreement {A : Type*} (x y : Configuration A) (hxy : x ≠ y) :
    ∃ p : Lattice, x p ≠ y p ∧
      ∀ z : Lattice, ‖latticeReal z‖ < ‖latticeReal p‖ → x z = y z := by
  classical
  obtain ⟨p, hp⟩ : ∃ p, x p ≠ y p := by
    by_contra! heq
    exact hxy (funext heq)
  have hex : ∃ n : ℕ, ∃ p : Lattice, latticeSqNorm p = n ∧ x p ≠ y p :=
    ⟨latticeSqNorm p, p, rfl, hp⟩
  obtain ⟨p, hpn, hp⟩ := Nat.find_spec hex
  refine ⟨p, hp, ?_⟩
  intro z hz
  by_contra hdiff
  have hsq : ‖latticeReal z‖ ^ 2 < ‖latticeReal p‖ ^ 2 := by
    nlinarith [norm_nonneg (latticeReal z), norm_nonneg (latticeReal p)]
  rw [← latticeSqNorm_cast z, ← latticeSqNorm_cast p] at hsq
  have hn : latticeSqNorm z < latticeSqNorm p := by exact_mod_cast hsq
  rw [hpn] at hn
  exact Nat.find_min hex hn ⟨z, rfl, hdiff⟩

/-- A finite alphabet and infinitely many configurations give nearest disagreements arbitrarily
far from the origin. This implements the escaping agreement balls in Lemma 3.1
(`lem:halfplane-pair`). -/
theorem exists_far_nearest_disagreement {A : Type*} [Finite A]
    (X : Set (Configuration A)) (hX : X.Infinite) (n : ℕ) :
    ∃ x ∈ X, ∃ y ∈ X, ∃ p : Lattice,
      x p ≠ y p ∧ (n : ℝ) < ‖latticeReal p‖ ∧
        ∀ z : Lattice, ‖latticeReal z‖ < ‖latticeReal p‖ → x z = y z := by
  classical
  let D : Finset Lattice := (Finset.Icc (-(n : ℤ)) (n : ℤ)).product
    (Finset.Icc (-(n : ℤ)) (n : ℤ))
  obtain ⟨x, hx, y, hy, hxy, hagree⟩ := exists_ne_agree_on_finite X hX D
  obtain ⟨p, hp, hmin⟩ := exists_nearest_disagreement x y hxy
  refine ⟨x, hx, y, hy, p, hp, ?_, hmin⟩
  by_contra! hnorm
  have h0 := (PiLp.norm_apply_le (latticeReal p) (0 : Fin 2)).trans hnorm
  have h1 := (PiLp.norm_apply_le (latticeReal p) (1 : Fin 2)).trans hnorm
  have hp0 : -(n : ℤ) ≤ p.1 ∧ p.1 ≤ n := by
    have hr : -(n : ℝ) ≤ (p.1 : ℝ) ∧ (p.1 : ℝ) ≤ n := by
      simpa [latticeReal, abs_le] using h0
    exact_mod_cast hr
  have hp1 : -(n : ℤ) ≤ p.2 ∧ p.2 ≤ n := by
    have hr : -(n : ℝ) ≤ (p.2 : ℝ) ∧ (p.2 : ℝ) ≤ n := by
      simpa [latticeReal, abs_le] using h1
    exact_mod_cast hr
  apply hp
  apply hagree p
  exact Finset.mem_product.mpr ⟨Finset.mem_Icc.mpr hp0, Finset.mem_Icc.mpr hp1⟩

/-- A displacement strictly inside the limiting negative half-plane eventually shortens an
escaping radius. This is the displayed squared-distance estimate in the proof of Lemma 3.1
(`lem:halfplane-pair`). -/
theorem eventually_norm_add_lt_of_normal_tendsto (p : ℕ → RealPlane) (ν z : RealPlane)
    (hp : ∀ n, p n ≠ 0) (hr : Tendsto (fun n => ‖p n‖) atTop atTop)
    (hν : Tendsto (fun n => ‖p n‖⁻¹ • p n) atTop (𝓝 ν))
    (hz : ⟪ν, z⟫_ℝ < 0) : ∀ᶠ n in atTop, ‖p n + z‖ < ‖p n‖ := by
  have hinv : Tendsto (fun n => ‖p n‖⁻¹) atTop (𝓝 (0 : ℝ)) :=
    tendsto_inv_atTop_zero.comp hr
  have hinner : Tendsto (fun n => ⟪‖p n‖⁻¹ • p n, z⟫_ℝ) atTop (𝓝 ⟪ν, z⟫_ℝ) :=
    hν.inner tendsto_const_nhds
  have hg : Tendsto
      (fun n => 2 * ⟪‖p n‖⁻¹ • p n, z⟫_ℝ + ‖z‖ ^ 2 * ‖p n‖⁻¹)
      atTop (𝓝 (2 * ⟪ν, z⟫_ℝ)) := by
    simpa using (tendsto_const_nhds.mul hinner).add (tendsto_const_nhds.mul hinv)
  have he := hg.eventually_lt_const (by linarith : 2 * ⟪ν, z⟫_ℝ < 0)
  filter_upwards [he] with n hn
  have hr0 : 0 < ‖p n‖ := norm_pos_iff.mpr (hp n)
  have hn' : (2 * ⟪p n, z⟫_ℝ + ‖z‖ ^ 2) / ‖p n‖ < 0 := by
    simpa [real_inner_smul_left, div_eq_mul_inv, add_mul, mul_assoc, mul_left_comm,
      mul_comm] using hn
  have hnum : 2 * ⟪p n, z⟫_ℝ + ‖z‖ ^ 2 < 0 := by simpa using (div_lt_iff₀ hr0).mp hn'
  have hs := norm_add_sq_real (p n) z
  nlinarith [norm_nonneg (p n + z), norm_nonneg (p n)]

/-- Convergence in a product of discrete alphabets implies eventual equality at each fixed
coordinate. Lemma 3.1 (`lem:halfplane-pair`) uses this to preserve disagreement at the origin
and agreement inside the half-plane. -/
theorem eventually_eq_at_of_tendsto {A : Type*} [TopologicalSpace A] [DiscreteTopology A]
    {x : ℕ → Configuration A} {c : Configuration A}
    (h : Tendsto x atTop (𝓝 c)) (z : Lattice) : ∀ᶠ n in atTop, x n z = c z := by
  have hz := ((continuous_apply z).tendsto c).comp h
  simpa only [nhds_discrete, tendsto_pure, Function.comp_apply] using hz

/-- An infinite closed shift-invariant space over a finite discrete alphabet contains two
configurations disagreeing at the origin and agreeing on an open half-plane with a unit
normal. This is the compact-space form of Lemma 3.1 (`lem:halfplane-pair`). -/
theorem exists_halfPlane_pair {A : Type*} [TopologicalSpace A] [DiscreteTopology A]
    [Finite A] (X : Set (Configuration A)) (hX : X.Infinite) (hclosed : IsClosed X)
    (hshift : ∀ h : Lattice, ∀ c ∈ X, shift h c ∈ X) :
    ∃ x ∈ X, ∃ y ∈ X, ∃ ν : RealPlane,
      ‖ν‖ = 1 ∧ x 0 ≠ y 0 ∧
        ∀ z : Lattice, ⟪ν, latticeReal z⟫_ℝ < 0 → x z = y z := by
  classical
  choose x hx y hy p hdis hfar hmin using
    (fun n : ℕ => exists_far_nearest_disagreement X hX n)
  have hp : ∀ n, latticeReal (p n) ≠ 0 := by
    intro n
    apply norm_pos_iff.mp
    exact lt_of_le_of_lt (Nat.cast_nonneg n) (hfar n)
  let normal : ℕ → RealPlane := fun n =>
    ‖latticeReal (p n)‖⁻¹ • latticeReal (p n)
  let state : ℕ → (Configuration A × Configuration A) × RealPlane := fun n =>
    ((shift (p n) (x n), shift (p n) (y n)), normal n)
  let K : Set ((Configuration A × Configuration A) × RealPlane) :=
    (X ×ˢ X) ×ˢ Metric.sphere 0 1
  have hcompact : IsCompact K :=
    (hclosed.isCompact.prod hclosed.isCompact).prod (isCompact_sphere 0 1)
  have hmem : ∀ n, state n ∈ K := by
    intro n
    refine ⟨⟨hshift (p n) (x n) (hx n), hshift (p n) (y n) (hy n)⟩, ?_⟩
    change normal n ∈ Metric.sphere 0 1
    rw [mem_sphere_zero_iff_norm]
    exact norm_smul_inv_norm (𝕜 := ℝ) (hp n)
  obtain ⟨s, hs, φ, hφ, hlim⟩ := hcompact.tendsto_subseq hmem
  obtain ⟨⟨x', y'⟩, ν⟩ := s
  have hxlim : Tendsto (fun n => shift (p (φ n)) (x (φ n))) atTop (𝓝 x') :=
    hlim.fst_nhds.fst_nhds
  have hylim : Tendsto (fun n => shift (p (φ n)) (y (φ n))) atTop (𝓝 y') :=
    hlim.fst_nhds.snd_nhds
  have hνlim : Tendsto (fun n => ‖latticeReal (p (φ n))‖⁻¹ • latticeReal (p (φ n)))
      atTop (𝓝 ν) := hlim.snd_nhds
  refine ⟨x', hs.1.1, y', hs.1.2, ν, mem_sphere_zero_iff_norm.mp hs.2, ?_, ?_⟩
  · intro heq
    obtain ⟨n, hxn, hyn⟩ :=
      ((eventually_eq_at_of_tendsto hxlim 0).and
        (eventually_eq_at_of_tendsto hylim 0)).exists
    apply hdis (φ n)
    simpa [shift] using hxn.trans (heq.trans hyn.symm)
  · intro z hz
    have hr : Tendsto (fun n => ‖latticeReal (p n)‖) atTop atTop :=
      tendsto_atTop_mono (fun n => le_of_lt (hfar n)) tendsto_natCast_atTop_atTop
    have hshort := eventually_norm_add_lt_of_normal_tendsto
      (fun n => latticeReal (p (φ n))) ν (latticeReal z) (fun n => hp (φ n))
      (hr.comp hφ.tendsto_atTop) hνlim hz
    obtain ⟨n, hn, hxn, hyn⟩ :=
      (hshort.and ((eventually_eq_at_of_tendsto hxlim z).and
        (eventually_eq_at_of_tendsto hylim z))).exists
    have heq := hmin (φ n) (z + p (φ n)) (by
      simpa [latticeReal_add, add_comm] using hn)
    exact hxn.symm.trans (heq.trans hyn)

/-- The Euclidean inner product gives the coordinate formula for the normal functional in Lemma
3.1 (`lem:halfplane-pair`). -/
@[simp] theorem inner_latticeReal (ν : RealPlane) (z : Lattice) :
    ⟪ν, latticeReal z⟫_ℝ = ν 0 * (z.1 : ℝ) + ν 1 * (z.2 : ℝ) := by
  simp [PiLp.inner_apply, latticeReal, Fin.sum_univ_two, mul_comm]

/-- Coordinate form of Lemma 3.1 (`lem:halfplane-pair`), with the unit-normal equation and strict
half-plane inequality written explicitly. -/
theorem exists_halfPlane_pair_coordinates {A : Type*} [TopologicalSpace A]
    [DiscreteTopology A] [Finite A] (X : Set (Configuration A)) (hX : X.Infinite)
    (hclosed : IsClosed X) (hshift : ∀ h : Lattice, ∀ c ∈ X, shift h c ∈ X) :
    ∃ x ∈ X, ∃ y ∈ X, ∃ ν : ℝ × ℝ,
      ν.1 ^ 2 + ν.2 ^ 2 = 1 ∧ x 0 ≠ y 0 ∧
        ∀ z : Lattice, ν.1 * (z.1 : ℝ) + ν.2 * (z.2 : ℝ) < 0 → x z = y z := by
  obtain ⟨x, hx, y, hy, ν, hν, hxy, hhalf⟩ := exists_halfPlane_pair X hX hclosed hshift
  refine ⟨x, hx, y, hy, (ν 0, ν 1), ?_, hxy, ?_⟩
  · have hsq := congrArg (fun t : ℝ => t ^ 2) hν
    simpa [EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_two] using hsq
  · intro z hz
    exact hhalf z (by simpa using hz)

end Nivat.Dynamics
