/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, Claude Opus 5
-/
module

public import LeanPool.DavisKahan.ForTauCeti.Analysis.InnerProductSpace.BorelCalculus.CyclicDecomposition
public import Mathlib.Topology.Bases
public import LeanPool.DavisKahan.ForTauCeti.Analysis.InnerProductSpace.SeparableOrthonormal

/-!
# The cyclic decomposition is countable on a separable space

`ForTauCeti/Analysis/InnerProductSpace/BorelCalculus/CyclicDecomposition.lean` decomposes an
arbitrary complex Hilbert space into cyclic subspaces indexed by a Zorn-maximal set, with **no**
countability hypothesis.  Under separability that index set is countable, and the decomposition
can be re-indexed by `ℕ`.

Countability is elementary and does not need any Hilbert-space theory beyond one normalisation:
distinct members of an orthogonal cyclic set are orthogonal *vectors*, so after normalising they
are at distance `√2`, and a separable metric space contains no uncountable uniformly separated
set.

Re-indexing by `ℕ` **pads with the zero vector**, whose cyclic subspace is `⊥`.  A zero summand
is orthogonal to everything, including to another zero summand, so the padded family is still an
orthogonal family and the Hilbert sum survives.  Padding is what lets every downstream
statement be `ℕ`-indexed, which is what the level-set normal form of
`ForTauCeti/MeasureTheory/MultiplicityLevels.lean` requires -- ranks count *earlier* indices, so
the index type must be linearly ordered.

## Main results

* `TauCeti.countable_of_pairwise_dist_le` (now in
  `ForTauCeti/Analysis/InnerProductSpace/SeparableOrthonormal.lean`, with its orthonormal
  corollary): a uniformly separated set in a separable metric space
  is countable.
* `TauCeti.BorelCalculus.cyclicSubspace_zero`: the zero vector generates `⊥`.
* `TauCeti.BorelCalculus.exists_countable_isHilbertSum_lp_diagMeasure_complex`:
  **the `ℕ`-indexed cyclic decomposition.**

## Provenance

* Original repository: Davis--Kahan/DKPS formalization (Kitware, Inc.).
* Extraction class: **authored in place** for the Tau Ceti staging layer.
* Spectra influence: **none** -- this module imports only Mathlib and `ForTauCeti`.
-/

public section

open scoped InnerProductSpace

open MeasureTheory

namespace TauCeti

namespace BorelCalculus

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {a : H →L[ℂ] H}

/-- **The zero vector generates the trivial cyclic subspace.**  Every value of the calculus at
`0` is `0`, so the span is trivial and so is its closure. -/
theorem cyclicSubspace_zero (ha : IsStarNormal a) : cyclicSubspace ha (0 : H) = ⊥ := by
  refine le_antisymm (cyclicSubspace_le ha ?_ fun f hf => ?_) bot_le
  · rw [Submodule.bot_coe]
    exact isClosed_singleton
  · rw [map_zero]
    exact Submodule.zero_mem _

/-- A value of the cyclic isometry at the zero vector is zero. -/
theorem cyclicIsometry_zero_apply (ha : IsStarNormal a)
    (F : Lp ℂ 2 (diagMeasure ha (0 : H))) : cyclicIsometry ha (0 : H) F = 0 := by
  have hmem := cyclicIsometry_mem_cyclicSubspace ha (0 : H) F
  rw [cyclicSubspace_zero ha] at hmem
  exact hmem

/-- **An orthogonal cyclic set in a separable space is countable.**

Distinct members generate orthogonal cyclic subspaces and each member lies in its own, so
distinct members are orthogonal nonzero vectors.  Normalised they are at distance `√2 ≥ 1`. -/
theorem countable_of_isOrthogonalCyclicSet [TopologicalSpace.SeparableSpace H]
    {ha : IsStarNormal a} {S : Set H} (hS : IsOrthogonalCyclicSet ha S) : S.Countable := by
  classical
  have hne : ∀ x ∈ S, x ≠ 0 := fun x hx hx0 => hS.zero_notMem (hx0 ▸ hx)
  have hinner : ∀ x ∈ S, ∀ y ∈ S, x ≠ y → ⟪x, y⟫_ℂ = 0 := fun x hx y hy hxy =>
    (hS.isOrtho x hx y hy hxy).inner_eq (mem_cyclicSubspace_self ha x)
      (mem_cyclicSubspace_self ha y)
  set N : H → H := fun x => ((‖x‖⁻¹ : ℝ) : ℂ) • x with hNdef
  have hnormN : ∀ x ∈ S, ‖N x‖ = 1 := by
    intro x hx
    have hx0 : ‖x‖ ≠ 0 := norm_ne_zero_iff.mpr (hne x hx)
    rw [hNdef]
    simp only [norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_inv, abs_norm]
    exact inv_mul_cancel₀ hx0
  have hinnerN : ∀ x ∈ S, ∀ y ∈ S, x ≠ y → ⟪N x, N y⟫_ℂ = 0 := by
    intro x hx y hy hxy
    rw [hNdef]
    simp only [inner_smul_left, inner_smul_right, hinner x hx y hy hxy, mul_zero]
  have hsep : ∀ u ∈ N '' S, ∀ v ∈ N '' S, u ≠ v → (1 : ℝ) ≤ dist u v := by
    rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩ huv
    have hxy : x ≠ y := fun h => huv (by rw [h])
    have hpy : ‖N x - N y‖ * ‖N x - N y‖ = ‖N x‖ * ‖N x‖ + ‖N y‖ * ‖N y‖ := by
      have hz : ⟪N x, -N y⟫_ℂ = 0 := by
        rw [inner_neg_right, hinnerN x hx y hy hxy, neg_zero]
      have hsum := norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero (N x) (-N y) hz
      rw [← sub_eq_add_neg] at hsum
      simpa using hsum
    rw [hnormN x hx, hnormN y hy] at hpy
    have hge : (1 : ℝ) ≤ ‖N x - N y‖ := by nlinarith [norm_nonneg (N x - N y)]
    rwa [dist_eq_norm]
  have himg : (N '' S).Countable := countable_of_pairwise_dist_le one_pos hsep
  refine Set.MapsTo.countable_of_injOn (f := N) (Set.mapsTo_image N S) ?_ himg
  intro x hx y hy hxy
  by_contra hne'
  have h0 : ⟪N x, N y⟫_ℂ = 0 := hinnerN x hx y hy hne'
  rw [hxy, inner_self_eq_norm_sq_to_K, hnormN y hy] at h0
  norm_num at h0

/-- **The cyclic decomposition of a separable space, indexed by `ℕ`.**

The Zorn-maximal orthogonal cyclic set is countable, so it can be enumerated; indices not used
by the enumeration are filled with the zero vector, whose summand is trivial and therefore
orthogonal to everything. -/
theorem exists_countable_isHilbertSum_lp_diagMeasure_complex [TopologicalSpace.SeparableSpace H]
    (ha : IsStarNormal a) :
    ∃ ξ : ℕ → H, IsHilbertSum ℂ (fun n => Lp ℂ 2 (diagMeasure ha (ξ n)))
      (fun n => cyclicIsometry ha (ξ n)) := by
  classical
  obtain ⟨S, hSmax⟩ := exists_maximal_isOrthogonalCyclicSet ha
  obtain ⟨f, hf⟩ :=
    Set.countable_iff_exists_injOn.mp (countable_of_isOrthogonalCyclicSet hSmax.prop)
  set e : ℕ → H := fun n => if h : ∃ x, x ∈ S ∧ f x = n then h.choose else 0 with hedef
  have hspec : ∀ n, ∀ h : ∃ x, x ∈ S ∧ f x = n, e n ∈ S ∧ f (e n) = n := by
    intro n h
    simp only [hedef, dite_eq_left h]
    exact h.choose_spec
  have hzero : ∀ n, ¬(∃ x, x ∈ S ∧ f x = n) → e n = 0 := by
    intro n h
    simp only [hedef, dite_eq_right h]
  have hemem : ∀ n, e n = 0 ∨ (e n ∈ S ∧ f (e n) = n) := by
    intro n
    by_cases h : ∃ x, x ∈ S ∧ f x = n
    · exact Or.inr (hspec n h)
    · exact Or.inl (hzero n h)
  have heS : ∀ x ∈ S, e (f x) = x := fun x hx =>
    hf (hspec (f x) ⟨x, hx, rfl⟩).1 hx (hspec (f x) ⟨x, hx, rfl⟩).2
  have horth : ∀ m n : ℕ, m ≠ n → ∀ (v : Lp ℂ 2 (diagMeasure ha (e m)))
      (w : Lp ℂ 2 (diagMeasure ha (e n))),
      ⟪cyclicIsometry ha (e m) v, cyclicIsometry ha (e n) w⟫_ℂ = 0 := by
    intro m n hmn v w
    rcases hemem m with h0 | ⟨hmS, hmf⟩
    · have hbot : cyclicSubspace ha (e m) = ⊥ := by rw [h0]; exact cyclicSubspace_zero ha
      have hzerov : cyclicIsometry ha (e m) v = 0 := by
        have hmem := cyclicIsometry_mem_cyclicSubspace ha (e m) v
        rw [hbot] at hmem
        simpa using hmem
      rw [hzerov, inner_zero_left]
    · rcases hemem n with h0 | ⟨hnS, hnf⟩
      · have hbot : cyclicSubspace ha (e n) = ⊥ := by rw [h0]; exact cyclicSubspace_zero ha
        have hzerow : cyclicIsometry ha (e n) w = 0 := by
          have hmem := cyclicIsometry_mem_cyclicSubspace ha (e n) w
          rw [hbot] at hmem
          simpa using hmem
        rw [hzerow, inner_zero_right]
      · have hne : e m ≠ e n := by
          intro hcon
          exact hmn (by rw [← hmf, ← hnf, hcon])
        exact (hSmax.prop.isOrtho _ hmS _ hnS hne).inner_eq
          (cyclicIsometry_mem_cyclicSubspace ha (e m) v)
          (cyclicIsometry_mem_cyclicSubspace ha (e n) w)
  refine ⟨e, IsHilbertSum.mk (𝕜 := ℂ) (fun m n hmn v w => horth m n hmn v w) ?_⟩
  have hle : (⨆ x : S, cyclicSubspace ha (x : H)) ≤ ⨆ n, cyclicSubspace ha (e n) := by
    refine iSup_le fun x => ?_
    have := le_iSup (fun n => cyclicSubspace ha (e n)) (f (x : H))
    rwa [heS (x : H) x.2] at this
  have htotal := topologicalClosure_iSup_cyclicSubspace_of_maximal ha hSmax
  refine htotal.trans ((Submodule.topologicalClosure_mono hle).trans ?_)
  simp only [range_cyclicIsometry]
  exact le_rfl

end BorelCalculus

end TauCeti
