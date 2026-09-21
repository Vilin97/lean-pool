/-
Copyright (c) 2026 Mario Ullrich. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Ullrich
-/
import LeanPool.SNumbers.SNumbers.Basic
import LeanPool.SNumbers.SNumbers.PiLpCoordinates
import Mathlib.Analysis.Convex.KreinMilman

/-!
# Shared helpers for the worked examples

Geometric and rank ingredients used by more than one of the worked examples
(`SNumbers.Examples.Identity`, `SNumbers.Examples.DiagonalMatrices`), collected
here so that each statement is proved once.

## Main contents

* `rank_id_piLp` — the identity on `ℓ^p_k` has rank `k` (as a `Cardinal`); the
  standard way to bound the rank of an approximant that factors through `ℓ^p_k`.
* `exists_mem_ker_coords` — **coordinate pigeonhole**: a subspace of `𝕜^m` whose
  dimension exceeds the size of a coordinate set contains a nonzero vector
  vanishing on that set.
* `exists_flat_vector_weighted` — **weighted flatness lemma**: a subspace of
  dimension `≥ k` contains a vector dominated by a nonnegative weight `w` that
  attains `w` on at least `k` coordinates.
* `exists_flat_vector` — the unweighted case `w ≡ 1`, with nonvanishing.

The flatness lemmas are the geometric heart of the Gelfand-width lower bounds
(Pietsch, *Eigenvalues and s-numbers*, §11.11): they produce, inside any
subspace of large enough dimension, a vector that is "flat" in the sense of
saturating a prescribed coordinate bound on many coordinates. The proof is an
extreme-point argument (Krein–Milman) combined with the pigeonhole lemma.
-/

universe u

open scoped ENNReal

namespace SNumbers

variable {𝕜 : Type u} [RCLike 𝕜] {m : ℕ}

/-! ## Exponents -/

/-- A finite exponent `p` with `1 ≤ p` has `0 < p.toReal`. The `Fact (1 ≤ p)`
instance is how `PiLp` carries the admissibility of the exponent, so this is the
standard way to enter the `rpow` computations. -/
lemma toReal_pos_of_ne_top {p : ℝ≥0∞} [Fact (1 ≤ p)] (hp : p ≠ ∞) : 0 < p.toReal :=
  ENNReal.toReal_pos (lt_of_lt_of_le zero_lt_one Fact.out).ne' hp

/-! ## Rank of the identity on `ℓ^p_k` -/

variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- The rank of the identity on `ℓ^p_k` is `k` (as a `Cardinal`). Used to bound
the rank of finite-rank approximants that factor through `ℓ^p_k`. -/
lemma rank_id_piLp (k : ℕ) :
    (ContinuousLinearMap.id 𝕜 (PiLp p (fun _ : Fin k => 𝕜))).rank = (k : Cardinal) := by
  have h1 : (ContinuousLinearMap.id 𝕜 (PiLp p (fun _ : Fin k => 𝕜))).rank
      = Module.rank 𝕜 (PiLp p (fun _ : Fin k => 𝕜)) := by
    rw [ContinuousLinearMap.rank, ContinuousLinearMap.coe_id]
    change Module.rank 𝕜 (LinearMap.range (LinearMap.id : _ →ₗ[𝕜] _)) = _
    rw [LinearMap.range_id]; exact Submodule.topEquiv.rank_eq
  rw [h1, ← Module.finrank_eq_rank, finrank_piLp]

/-! ## The coordinate pigeonhole -/

/-- **Coordinate pigeonhole.** A subspace `V ⊆ 𝕜^m` whose dimension exceeds the
size of a coordinate set `A` contains a nonzero vector vanishing on `A`. The
restriction `V → (A → 𝕜)` has range of dimension `≤ |A| < dim V`, so a nonzero
kernel by rank–nullity. -/
lemma exists_mem_ker_coords {V : Submodule 𝕜 (Fin m → 𝕜)}
    {A : Finset (Fin m)} (hA : A.card < Module.finrank 𝕜 V) :
    ∃ y ∈ V, y ≠ 0 ∧ ∀ i ∈ A, y i = 0 := by
  classical
  set r : V →ₗ[𝕜] (A → 𝕜) :=
    LinearMap.pi (fun i : A => (LinearMap.proj (i : Fin m)).comp V.subtype) with hr
  have hne : LinearMap.ker r ≠ ⊥ :=
    LinearMap.ker_ne_bot_of_finrank_lt
      (by rwa [Module.finrank_pi, Fintype.card_coe])
  obtain ⟨z, hzmem, hz0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
  refine ⟨(z : Fin m → 𝕜), z.2, fun h => hz0 (Submodule.coe_eq_zero.mp h), fun i hi => ?_⟩
  have hz : r z = 0 := LinearMap.mem_ker.mp hzmem
  have hzi := congrFun hz ⟨i, hi⟩
  simpa [hr, LinearMap.pi_apply, LinearMap.comp_apply, LinearMap.proj_apply,
    Submodule.subtype_apply] using hzi

/-! ## The flatness lemmas -/

/-- **Weighted flatness lemma.** For a nonnegative weight `w`, a subspace
`V ⊆ 𝕜^m` of dimension `≥ k` contains a vector `x` with `‖x i‖ ≤ w i`
everywhere that **saturates** the weight (`‖x i‖ = w i`) on at least `k`
coordinates. An extreme point `x` of the compact set
`B = {x ∈ V : ∀ i, ‖x i‖ ≤ w i}` (Krein–Milman) must saturate `≥ dim V`
coordinates: otherwise the coordinate-pigeonhole vector `y` vanishing on the
saturated set `S` makes `x` the midpoint of a nondegenerate segment
`x ± ε·y ⊆ B`, contradicting extremality. (Nonvanishing of `x` is not asserted
here; for the unweighted case it is recovered in `exists_flat_vector`.) -/
lemma exists_flat_vector_weighted {V : Submodule 𝕜 (Fin m → 𝕜)} {k : ℕ}
    (w : Fin m → ℝ) (hw : ∀ i, 0 ≤ w i) (hkV : k ≤ Module.finrank 𝕜 V) :
    ∃ x ∈ V, (∀ i, ‖x i‖ ≤ w i) ∧
      k ≤ (Finset.univ.filter (fun i => ‖x i‖ = w i)).card := by
  classical
  set B : Set (Fin m → 𝕜) := {x | x ∈ V ∧ ∀ i, ‖x i‖ ≤ w i} with hBdef
  have hBne : B.Nonempty := ⟨0, V.zero_mem, fun i => by
    simpa only [Pi.zero_apply, norm_zero] using hw i⟩
  have hBeq : B = (V : Set (Fin m → 𝕜)) ∩ ⋂ i, {x : Fin m → 𝕜 | ‖x i‖ ≤ w i} := by
    ext x; simp only [hBdef, Set.mem_ofPred_eq, Set.mem_inter_iff, Set.mem_iInter, SetLike.mem_coe]
  have hBclosed : IsClosed B := by
    rw [hBeq]
    refine V.closed_of_finiteDimensional.inter (isClosed_iInter fun i => ?_)
    exact isClosed_le ((continuous_apply i).norm) continuous_const
  have hBbdd : Bornology.IsBounded B := by
    refine (Metric.isBounded_closedBall (x := (0 : Fin m → 𝕜)) (r := ⨆ i, w i)).subset ?_
    intro x hx
    simp only [Metric.mem_closedBall, dist_zero_right]
    refine (pi_norm_le_iff_of_nonneg (Real.iSup_nonneg hw)).mpr fun i => ?_
    exact (hx.2 i).trans (le_ciSup (Finite.bddAbove_range w) i)
  have hBcompact : IsCompact B := Metric.isCompact_of_isClosed_isBounded hBclosed hBbdd
  obtain ⟨x, hxep⟩ := hBcompact.extremePoints_nonempty hBne
  rw [mem_extremePoints_iff_left] at hxep
  obtain ⟨hxB, hxext⟩ := hxep
  set S : Finset (Fin m) := Finset.univ.filter (fun i => ‖x i‖ = w i) with hSdef
  have hxle : ∀ i, ‖x i‖ ≤ w i := hxB.2
  have hmemS : ∀ i, i ∈ S ↔ ‖x i‖ = w i := by
    intro i; rw [hSdef, Finset.mem_filter]; simp [Finset.mem_univ]
  have hcard : Module.finrank 𝕜 V ≤ S.card := by
    by_contra hlt
    push Not at hlt
    obtain ⟨y, hyV, hy0, hyS⟩ := exists_mem_ker_coords (V := V) (A := S) hlt
    have hSc : (Finset.univ.filter (fun i => i ∉ S)).Nonempty := by
      rw [Finset.filter_nonempty_iff]
      by_contra h
      push Not at h
      have : S = Finset.univ := Finset.eq_univ_of_forall fun i => h i (Finset.mem_univ i)
      rw [this, Finset.card_univ, Fintype.card_fin] at hlt
      exact absurd (lt_of_lt_of_le hlt (Submodule.finrank_le V)) (by simp)
    have hMpos : 0 < ‖y‖ := norm_pos_iff.mpr hy0
    set d : ℝ := (Finset.univ.filter (fun i => i ∉ S)).inf' hSc (fun i => w i - ‖x i‖) with hd
    have hdpos : 0 < d := by
      rw [hd, Finset.lt_inf'_iff]
      intro i hi
      rw [Finset.mem_filter] at hi
      have : ‖x i‖ < w i := lt_of_le_of_ne (hxle i) (fun hh => hi.2 ((hmemS i).mpr hh))
      linarith
    set ε : ℝ := d / ‖y‖ with hε
    have hεpos : 0 < ε := div_pos hdpos hMpos
    set c : 𝕜 := RCLike.ofReal ε with hc
    have hcnorm : ‖c‖ = ε := by rw [hc, RCLike.norm_ofReal, abs_of_pos hεpos]
    have hpm : ∀ (μ : 𝕜), ‖μ‖ ≤ ε → ∀ i, ‖x i + μ • y i‖ ≤ w i := by
      intro μ hμ i
      by_cases hi : i ∈ S
      · rw [hyS i hi, smul_zero, add_zero]; exact le_of_eq ((hmemS i).mp hi)
      · have hxiw : ‖x i‖ < w i := lt_of_le_of_ne (hxle i) (fun hh => hi ((hmemS i).mpr hh))
        have hslack : d ≤ w i - ‖x i‖ :=
          hd ▸ Finset.inf'_le _ (by rw [Finset.mem_filter]; exact ⟨Finset.mem_univ i, hi⟩)
        calc ‖x i + μ • y i‖ ≤ ‖x i‖ + ‖μ • y i‖ := norm_add_le _ _
          _ = ‖x i‖ + ‖μ‖ * ‖y i‖ := by rw [norm_smul]
          _ ≤ ‖x i‖ + ε * ‖y‖ := by gcongr; exact norm_le_pi_norm y i
          _ = ‖x i‖ + d := by rw [hε, div_mul_cancel₀ _ (ne_of_gt hMpos)]
          _ ≤ w i := by linarith
    have hmem1 : x + c • y ∈ B :=
      ⟨V.add_mem hxB.1 (V.smul_mem c hyV), fun i => by
        simpa [Pi.add_apply, Pi.smul_apply] using hpm c (le_of_eq hcnorm) i⟩
    have hmem2 : x - c • y ∈ B :=
      ⟨V.sub_mem hxB.1 (V.smul_mem c hyV), fun i => by
        have h := hpm (-c) (by rw [norm_neg]; exact le_of_eq hcnorm) i
        simpa [Pi.sub_apply, Pi.smul_apply, sub_eq_add_neg, neg_smul] using h⟩
    have hseg : x ∈ openSegment ℝ (x + c • y) (x - c • y) :=
      ⟨1/2, 1/2, by norm_num, by norm_num, by norm_num, by module⟩
    have heq := hxext (x + c • y) hmem1 (x - c • y) hmem2 hseg
    have hcy : c • y = 0 := by
      have h2 : x + c • y = x + 0 := by rw [add_zero]; exact heq
      exact add_left_cancel h2
    rcases smul_eq_zero.mp hcy with h | h
    · exact (RCLike.ofReal_ne_zero.mpr (ne_of_gt hεpos)) h
    · exact hy0 h
  exact ⟨x, hxB.1, hxB.2, le_trans hkV hcard⟩

/-- **Flatness lemma.** A subspace `V ⊆ 𝕜^m` of dimension `≥ k ≥ 1` contains a
nonzero vector `x` with `‖x i‖ ≤ 1` everywhere and `‖x i‖ = 1` on at least `k`
coordinates.

This is the unit-weight case `w ≡ 1` of `exists_flat_vector_weighted`; the
hypothesis `1 ≤ k` additionally forces `x ≠ 0`, since at least one coordinate
has `‖x i‖ = 1`. -/
lemma exists_flat_vector {V : Submodule 𝕜 (Fin m → 𝕜)} {k : ℕ}
    (hk : 1 ≤ k) (hkV : k ≤ Module.finrank 𝕜 V) :
    ∃ x ∈ V, x ≠ 0 ∧ (∀ i, ‖x i‖ ≤ 1) ∧
      k ≤ (Finset.univ.filter (fun i => ‖x i‖ = 1)).card := by
  classical
  obtain ⟨x, hxV, hxle, hxcard⟩ :=
    exists_flat_vector_weighted (V := V) (k := k) (fun _ => (1 : ℝ))
      (fun _ => zero_le_one) hkV
  refine ⟨x, hxV, ?_, hxle, hxcard⟩
  -- At least one coordinate is saturated, so `x` cannot vanish.
  intro hx0
  obtain ⟨i, hi⟩ := Finset.card_pos.mp (le_trans hk hxcard)
  have hxi : ‖x i‖ = 1 := by rw [Finset.mem_filter] at hi; exact hi.2
  rw [hx0] at hxi
  simp at hxi

end SNumbers

/- Adapted for Lean Pool: module imports and compatibility with its pinned toolchain. -/
