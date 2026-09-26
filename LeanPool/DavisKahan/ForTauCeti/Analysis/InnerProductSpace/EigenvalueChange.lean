/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, Claude Opus 4.8
-/

/-
Staged for Tau Ceti, roadmap topic T08.  Mathlib is not the destination
(`ForTauCeti/README.md`); what follows is where this material would have gone on
the closed Mathlib track —
additions to `Mathlib/Analysis/InnerProductSpace/` (new file
`EigenvalueChange.lean`).

Formalized by Claude Opus 4.8 (claude-opus-4-8[1m]).

Davis's lower bound for the change in eigenvalues (Davis 1963, Theorem 4.1): under
a separation hypothesis on the perturbed spectrum, the eigenvalue displacement
`∑ᵢ(λ'ᵢ − λᵢ)²` is bounded below by `‖𝒞H‖²_F − ‖𝒞⊥H‖²_F`, the diagonal minus
off-diagonal Frobenius energy of the perturbation.  This is the ingredient Davis
uses to upgrade the total-rotation estimate to off-diagonal control.

Source: Davis, *The rotation of eigenvectors by a perturbation*, J. Math. Anal.
Appl. 6 (1963), Theorem 4.1 (pp. 168–170).  See
`TauCeti/prose/non-distributable/Davis-1963-...tex` lines 641–754 and the
decomposition in `.mathlib-quality/decomposition.md`.
-/
module

public import Mathlib.Analysis.Convex.Birkhoff
public import Mathlib.GroupTheory.Perm.Support
public import LeanPool.DavisKahan.ForTauCeti.Analysis.InnerProductSpace.SchurHorn


/-! # Davis's eigenvalue-change lower bound (Davis 1963, Theorem 4.1)

For self-adjoint `T, S` on a finite-dimensional inner product space with `H = S − T`,
writing `𝒞H` for the diagonal part of `H` in `T`'s eigenbasis and `𝒞⊥H` for the
off-diagonal part, if the spectrum of `S` is `γ`-separated and `‖𝒞H‖_F ≤ γ/√2`, then
the eigenvalue displacement dominates the diagonal-minus-off-diagonal energy:
`∑ᵢ(λ'ᵢ − λᵢ)² ≥ ‖𝒞H‖²_F − ‖𝒞⊥H‖²_F`.

Davis proves this in the real Hilbert space of Hermitian matrices; since every matrix
involved is diagonal in `T`'s eigenbasis, the argument reduces to `EuclideanSpace ℝ (Fin n)`
about a point in the convex hull of a permutation orbit (`Submodule` §0 of the
decomposition note). The convex-hull membership is discharged from **Birkhoff's theorem**;
no vector-majorization API is needed.

## Main results

* `TauCeti.two_mul_sq_le_sum_sq_sub_perm` (L1): `2γ² ≤ ∑ᵢ(w(πᵢ) − wᵢ)²` for any
  non-identity permutation of a `γ`-separated tuple — the combinatorial core.
* `TauCeti.sqrt_two_inv_mul_norm_le_inner_of_mem_convexHull_perm` (L2): the geometric
  estimate `(γ/√2)‖w − c‖ ≤ ⟪w − c, w⟫` for `c` in the convex hull of the permutation
  orbit of `w` (Davis eq. 4.2).
* `TauCeti.sum_sq_sub_pinch_ge` (L4): the vector-level eigenvalue-change bound.
* `TauCeti.diag_mem_convexHull_perm_spectrum` (L3): the Birkhoff bridge placing the
  diagonal of `S` in the convex hull of the permutation orbit of `S`'s spectrum.
* `TauCeti.sum_sq_eigenvalues_sub_ge` (L5): Davis's Theorem 4.1 in operator form.

## References

* Chandler Davis, *The rotation of eigenvectors by a perturbation*, J. Math. Anal. Appl.
  6 (1963), 159–173, Theorem 4.1.
-/

@[expose] public section

namespace TauCeti

open scoped BigOperators

/-- **L1 — combinatorial minimum displacement.**  For a tuple `w : Fin n → ℝ` whose
entries are `γ`-separated (any two distinct coordinates differ by at least `γ ≥ 0`),
every non-identity permutation `π` moves the tuple by squared Euclidean distance at
least `2 γ²`:
`2 γ² ≤ ∑ i, (w (π i) − w i)²`.

This is the lower-bound half of Davis (1963) Thm 4.1's vertex estimate
("π must exchange two `λ'ᵢ` which differ by exactly `γ` … for this `π`,
`‖Bπ − B‖ = √2 γ`"): a non-identity permutation has support of size ≥ 2, and each
moved coordinate contributes at least `γ²`.  We need only the lower bound, so the
exact minimiser (a closest-pair transposition) is not required. -/
theorem two_mul_sq_le_sum_sq_sub_perm {n : ℕ} (w : Fin n → ℝ)
    {γ : ℝ} (hγ : 0 ≤ γ) (hgap : ∀ i j, i ≠ j → γ ≤ |w i - w j|)
    {π : Equiv.Perm (Fin n)} (hπ : π ≠ 1) :
    2 * γ ^ 2 ≤ ∑ i, (w (π i) - w i) ^ 2 := by
  classical
  -- The full sum collapses to the sum over the support (off-support terms vanish).
  have hsupp_sum : ∑ i, (w (π i) - w i) ^ 2 = ∑ i ∈ π.support, (w (π i) - w i) ^ 2 :=
    (Finset.sum_subset (Finset.subset_univ _)
      (fun i _ hi => by rw [not_not.mp (Equiv.Perm.mem_support.not.mp hi)]; ring)).symm
  rw [hsupp_sum]
  -- Each support term is at least γ².
  have hterm : ∀ i ∈ π.support, γ ^ 2 ≤ (w (π i) - w i) ^ 2 := fun i hi => by
    have hne : π i ≠ i := Equiv.Perm.mem_support.mp hi
    calc γ ^ 2 ≤ |w (π i) - w i| ^ 2 := by
            gcongr; exact hgap (π i) i hne
      _ = (w (π i) - w i) ^ 2 := sq_abs _
  -- A non-identity permutation moves at least two points.
  have hcard : 2 ≤ π.support.card := by
    have hne_empty : π.support ≠ ∅ := fun h => hπ (Equiv.Perm.support_eq_empty_iff.mp h)
    have h0 := Finset.card_pos.mpr (Finset.nonempty_iff_ne_empty.mpr hne_empty)
    have h1 := Equiv.Perm.card_support_ne_one π
    omega
  calc 2 * γ ^ 2 ≤ (π.support.card : ℝ) * γ ^ 2 := by
          gcongr; exact_mod_cast hcard
    _ = ∑ _i ∈ π.support, γ ^ 2 := by rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ ∑ i ∈ π.support, (w (π i) - w i) ^ 2 := Finset.sum_le_sum hterm

/-! ### Geometric core and operator wrapper

The geometric core (L2) and algebra (L4) live over `EuclideanSpace ℝ (Fin n)` — Davis's
pinching subspace `𝒞𝓕 ≅ ℝⁿ` — where the norm, inner product, and convexity of the
permutation orbit are native; the operator wrapper (L3, L5) lifts the eigenvalue tuples of
`S`, `T` through `WithLp.equiv` and restates the bound for `hT.eigenvalues`.

## Provenance

* Original repository: Davis--Kahan/DKPS formalization (Kitware, Inc.).
* Original module: `ForMathlib.Analysis.InnerProductSpace.EigenvalueChange`, moved to
  `ForTauCeti` in the Wave-1 staging migration; introduced at Davis--Kahan
  commit `9543631`.
* Extraction class: **moved**.  The Wave-1 migration renamed the namespace
  `ForMathlib` to `TauCeti`; declaration names and proofs are unchanged.
* Original authors / copyright: Jon Crall, Claude Opus 4.8; Copyright (c) 2026 Kitware, Inc.;
  Apache 2.0.
* Spectra influence: **none** — this module imports only Mathlib and sibling
  `ForTauCeti` staging modules.
-/

open scoped InnerProductSpace Matrix
open Module (finrank)

/-- Coordinate permutation of a Euclidean vector: `permuteCoords w π` has `i`-th entry `w (π i)`. -/
def permuteCoords {n : ℕ} (w : EuclideanSpace ℝ (Fin n)) (π : Equiv.Perm (Fin n)) :
    EuclideanSpace ℝ (Fin n) :=
  (WithLp.equiv 2 (Fin n → ℝ)).symm fun i => w (π i)

/-- The coordinate permutation, unfolded. -/
@[simp] lemma permEV_apply {n : ℕ} (w : EuclideanSpace ℝ (Fin n)) (π : Equiv.Perm (Fin n))
    (i : Fin n) : permuteCoords w π i = w (π i) := (rfl)

/-- A coordinate permutation is an isometry: `‖permuteCoords w π‖ = ‖w‖`. -/
lemma norm_permEV {n : ℕ} (w : EuclideanSpace ℝ (Fin n)) (π : Equiv.Perm (Fin n)) :
    ‖permuteCoords w π‖ = ‖w‖ := by
  rw [EuclideanSpace.norm_eq, EuclideanSpace.norm_eq]
  simp only [permEV_apply]
  exact congrArg _ (Equiv.sum_comp π fun j => ‖w j‖ ^ 2)

/-- The squared displacement of a coordinate permutation, in the form L1 consumes. -/
lemma norm_sub_permEV_sq {n : ℕ} (w : EuclideanSpace ℝ (Fin n)) (π : Equiv.Perm (Fin n)) :
    ‖w - permuteCoords w π‖ ^ 2 = ∑ i, (w i - w (π i)) ^ 2 := by
  rw [EuclideanSpace.norm_sq_eq]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [PiLp.sub_apply, permEV_apply, Real.norm_eq_abs, sq_abs]

/-- Because a coordinate permutation preserves the norm, the residual
`w − permuteCoords w π` makes an exact right-triangle relation
`2⟪w − permuteCoords w π, w⟫ = ‖w − permuteCoords w π‖²`
(Davis's "both vertices on the unit sphere"). -/
lemma two_mul_inner_sub_permEV {n : ℕ} (w : EuclideanSpace ℝ (Fin n)) (π : Equiv.Perm (Fin n)) :
    2 * ⟪w - permuteCoords w π, w⟫_ℝ = ‖w - permuteCoords w π‖ ^ 2 := by
  have hv : ‖permuteCoords w π‖ ^ 2 = ‖w‖ ^ 2 := by rw [norm_permEV]
  rw [norm_sub_sq_real, hv, inner_sub_left, real_inner_self_eq_norm_sq,
    real_inner_comm (permuteCoords w π) w]
  ring

/-- **L2 — geometric core (Davis eq. 4.2), unnormalised.**  If the coordinates of `w` are
`γ`-separated and `c` lies in the convex hull of the permutation orbit of `w`, then
`(γ/√2)·‖w − c‖ ≤ ⟪w − c, w⟫`.

Proof: extract `c = ∑ aₖ • pₖ` with each `pₖ = permuteCoords w πₖ` a vertex (`mem_convexHull_iff…`).
Then `⟪w − c, w⟫ = ∑ aₖ ⟪w − pₖ, w⟫` and, per vertex, `⟪w − pₖ, w⟫ = ½‖w − pₖ‖²`
(`two_mul_inner_sub_permEV`) with `‖w − pₖ‖ ≥ √2 γ` (from `two_mul_sq_le_sum_sq_sub_perm` when
`πₖ ≠ 1`, else `0`), giving `(γ/√2)‖w − pₖ‖ ≤ ⟪w − pₖ, w⟫`.  Summing and applying the triangle
inequality `‖w − c‖ ≤ ∑ aₖ‖w − pₖ‖` closes it. -/
theorem sqrt_two_inv_mul_norm_le_inner_of_mem_convexHull_perm {n : ℕ}
    (w c : EuclideanSpace ℝ (Fin n)) {γ : ℝ} (hγ : 0 ≤ γ)
    (hgap : ∀ i j, i ≠ j → γ ≤ |w i - w j|)
    (hc : c ∈ convexHull ℝ (Set.range fun π : Equiv.Perm (Fin n) => permuteCoords w π)) :
    γ / Real.sqrt 2 * ‖w - c‖ ≤ ⟪w - c, w⟫_ℝ := by
  obtain ⟨ι, _, a, p, ha0, ha1, hp, hpc⟩ := mem_convexHull_iff_exists_fintype.mp hc
  -- Choose, for each vertex `p k`, a permutation `π k` with `permuteCoords w (π k) = p k`.
  choose π hπ using hp
  replace hπ : ∀ k, permuteCoords w (π k) = p k := hπ
  have hγ2 : (0:ℝ) ≤ γ / Real.sqrt 2 := by positivity
  -- `w − c` is the convex combination `∑ aₖ • (w − p k)`.
  have hwc : w - c = ∑ k, a k • (w - p k) := by
    rw [← hpc]
    simp only [smul_sub, Finset.sum_sub_distrib, ← Finset.sum_smul, ha1, one_smul]
  -- Per-vertex bound: `(γ/√2)·‖w − p k‖ ≤ ⟪w − p k, w⟫`.
  have hvertex : ∀ k, γ / Real.sqrt 2 * ‖w - p k‖ ≤ ⟪w - p k, w⟫_ℝ := by
    intro k
    have hhalf : ⟪w - p k, w⟫_ℝ = ‖w - p k‖ ^ 2 / 2 := by
      have := two_mul_inner_sub_permEV w (π k); rw [hπ k] at this; linarith
    rw [hhalf]
    by_cases hk : π k = 1
    · have hpkw : p k = w := by rw [← hπ k, hk]; ext i; simp
      rw [hpkw]; simp
    · have hnn : (0:ℝ) ≤ ‖w - p k‖ := norm_nonneg _
      have hspos : (0:ℝ) < Real.sqrt 2 := by positivity
      have hL1 : 2 * γ ^ 2 ≤ ‖w - p k‖ ^ 2 := by
        rw [← hπ k, norm_sub_permEV_sq]
        have hbase := two_mul_sq_le_sum_sq_sub_perm (fun i => w i) hγ hgap hk
        calc 2 * γ ^ 2 ≤ ∑ i, (w (π k i) - w i) ^ 2 := hbase
          _ = ∑ i, (w i - w (π k i)) ^ 2 := by
              refine Finset.sum_congr rfl fun i _ => ?_; ring
      have hge : Real.sqrt 2 * γ ≤ ‖w - p k‖ := by
        rw [show Real.sqrt 2 * γ = Real.sqrt (2 * γ ^ 2) by
          rw [Real.sqrt_mul (by norm_num), Real.sqrt_sq hγ]]
        rw [show ‖w - p k‖ = Real.sqrt (‖w - p k‖ ^ 2) from (Real.sqrt_sq hnn).symm]
        exact Real.sqrt_le_sqrt hL1
      -- reduce `γ/√2 · ‖w−pk‖ ≤ ‖w−pk‖²/2` to `√2·γ·‖w−pk‖ ≤ ‖w−pk‖²`
      have e22 : (2:ℝ) / Real.sqrt 2 = Real.sqrt 2 := by
        rw [div_eq_iff (ne_of_gt hspos)]; exact (Real.mul_self_sqrt (by norm_num)).symm
      have goal2 : 2 * (γ / Real.sqrt 2 * ‖w - p k‖) ≤ ‖w - p k‖ ^ 2 := by
        have heq : 2 * (γ / Real.sqrt 2 * ‖w - p k‖)
            = (2 / Real.sqrt 2) * (γ * ‖w - p k‖) := by ring
        rw [heq, e22]
        nlinarith [mul_le_mul_of_nonneg_right hge hnn]
      linarith
  -- Sum the vertex bounds, then apply the triangle inequality.
  have hsum_inner : ⟪w - c, w⟫_ℝ = ∑ k, a k * ⟪w - p k, w⟫_ℝ := by
    rw [hwc, sum_inner]; exact Finset.sum_congr rfl fun k _ => real_inner_smul_left _ _ _
  have htri : ‖w - c‖ ≤ ∑ k, a k * ‖w - p k‖ := by
    rw [hwc]
    refine (norm_sum_le _ _).trans ?_
    exact Finset.sum_le_sum fun k _ => by rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (ha0 k)]
  calc γ / Real.sqrt 2 * ‖w - c‖
      ≤ γ / Real.sqrt 2 * ∑ k, a k * ‖w - p k‖ := by
        exact mul_le_mul_of_nonneg_left htri hγ2
    _ = ∑ k, a k * (γ / Real.sqrt 2 * ‖w - p k‖) := by
        rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun k _ => by ring
    _ ≤ ∑ k, a k * ⟪w - p k, w⟫_ℝ :=
        Finset.sum_le_sum fun k _ => mul_le_mul_of_nonneg_left (hvertex k) (ha0 k)
    _ = ⟪w - c, w⟫_ℝ := hsum_inner.symm

/-- **L4 — the eigenvalue-change lower bound at the vector level (Davis Thm 4.1).**  With
`w = λ'` (eigenvalues of `A+H`), `c` the diagonal of `A+H` in `A`'s eigenbasis, and `dH`
the diagonal (pinching) part `𝒞H` of the perturbation — a free vector of Frobenius norm
`≤ γ/√2` — the eigenvalue displacement `∑ᵢ(λ'ᵢ − λᵢ)²` (with `λ = c − dH`) dominates
`‖𝒞H‖² − ‖𝒞⊥H‖² = ∑ dHᵢ² − (∑ wᵢ² − ∑ cᵢ²)`.

Davis's Part 2: `Δ + (c − w) = dH`, so `‖Δ‖² − ‖dH‖² = ‖w−c‖² − 2⟪c−w, dH⟫`, minimised
over `dH` (Cauchy–Schwarz) at `−√2γ‖w−c‖ + ‖w−c‖²`; adding `‖𝒞⊥H‖² = ‖w‖²−‖c‖²` and using
`‖w−c‖²+‖w‖²−‖c‖² = 2⟪w−c,w⟫` reduces the claim to L2. -/
theorem sum_sq_sub_pinch_ge {n : ℕ} (w c dH : EuclideanSpace ℝ (Fin n))
    {γ : ℝ} (hγ : 0 ≤ γ) (hgap : ∀ i j, i ≠ j → γ ≤ |w i - w j|)
    (hc : c ∈ convexHull ℝ (Set.range fun π : Equiv.Perm (Fin n) => permuteCoords w π))
    (hdH : ‖dH‖ ≤ γ / Real.sqrt 2) :
    ‖dH‖ ^ 2 - (‖w‖ ^ 2 - ‖c‖ ^ 2) ≤ ‖w - (c - dH)‖ ^ 2 := by
  have hL2 := sqrt_two_inv_mul_norm_le_inner_of_mem_convexHull_perm w c hγ hgap hc
  -- Cauchy–Schwarz on the cross term, then `‖dH‖ ≤ γ/√2`.
  have hcs : -(‖w - c‖ * (γ / Real.sqrt 2)) ≤ ⟪w - c, dH⟫_ℝ := by
    have h1 : |⟪w - c, dH⟫_ℝ| ≤ ‖w - c‖ * ‖dH‖ := abs_real_inner_le_norm _ _
    have h2 : ‖w - c‖ * ‖dH‖ ≤ ‖w - c‖ * (γ / Real.sqrt 2) :=
      mul_le_mul_of_nonneg_left hdH (norm_nonneg _)
    linarith [(abs_le.mp (h1.trans h2)).1]
  -- expand the displacement and the parallelogram-type identity
  have hexp : ‖w - (c - dH)‖ ^ 2 = ‖w - c‖ ^ 2 + 2 * ⟪w - c, dH⟫_ℝ + ‖dH‖ ^ 2 := by
    rw [show w - (c - dH) = (w - c) + dH by abel, norm_add_sq_real]
  have hpar : ‖w - c‖ ^ 2 + ‖w‖ ^ 2 - ‖c‖ ^ 2 = 2 * ⟪w - c, w⟫_ℝ := by
    rw [norm_sub_sq_real, inner_sub_left, real_inner_self_eq_norm_sq, real_inner_comm w c]
    ring
  rw [hexp]
  nlinarith [hL2, hcs, hpar]

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  [FiniteDimensional 𝕜 E] {n : ℕ} {T S : E →ₗ[𝕜] E}

/-- **L3 — Birkhoff bridge.**  The diagonal of `S` in `T`'s eigenbasis, as the vector
`c i = re ⟪vᵢ, S vᵢ⟫`, lies in the convex hull of the permutation orbit of `S`'s spectrum.
This is Davis's "`C` is the pinching of a matrix unitarily equivalent to `B`, hence
`C = ∑_π a_π Bπ`" (lines 689–696), discharged from Birkhoff
(`doublyStochastic_eq_convexHull_permMatrix`) applied to the doubly-stochastic weight
matrix `‖⟪v'ⱼ, vᵢ⟫‖²` (whose double-stochasticity is `SchurHorn.schurWeight_row/col_sum`). -/
theorem diag_mem_convexHull_perm_spectrum (hT : T.IsSymmetric) (hS : S.IsSymmetric)
    (hn : finrank 𝕜 E = n) :
    (WithLp.equiv 2 (Fin n → ℝ)).symm
        (fun k => RCLike.re ⟪hT.eigenvectorBasis hn k, S (hT.eigenvectorBasis hn k)⟫_𝕜)
      ∈ convexHull ℝ (Set.range fun π : Equiv.Perm (Fin n) =>
          permuteCoords ((WithLp.equiv 2 (Fin n → ℝ)).symm (hS.eigenvalues hn)) π) := by
  classical
  set e := WithLp.equiv 2 (Fin n → ℝ) with he
  set v := hT.eigenvectorBasis hn with hv
  set W₀ : Fin n → ℝ := hS.eigenvalues hn with hW0
  set c₀ : Fin n → ℝ := fun k => RCLike.re ⟪v k, S (v k)⟫_𝕜 with hc0
  set M : Matrix (Fin n) (Fin n) ℝ := fun k i => schurWeight hS hn v i k with hM
  -- `M` is doubly stochastic (its rows/columns are the Schur weights).
  have hMds : M ∈ doublyStochastic ℝ (Fin n) := by
    rw [mem_doublyStochastic_iff_sum]
    refine ⟨fun a b => ?_, fun a => ?_, fun b => ?_⟩
    · simp only [hM]; exact schurWeight_nonneg hS hn v b a
    · simp only [hM]; exact schurWeight_row_sum hS hn v a
    · simp only [hM]; exact schurWeight_col_sum hS hn v b
  -- The diagonal is `M *ᵥ (spectrum of S)`.
  have hcMW : c₀ = M *ᵥ W₀ := by
    funext k
    have hsym : ⟪v k, S (v k)⟫_𝕜 = ⟪S (v k), v k⟫_𝕜 := (hS (v k) (v k)).symm
    -- states the goal as the inner-product identity the structure lemma expects.
    change RCLike.re ⟪v k, S (v k)⟫_𝕜 = (M *ᵥ W₀) k
    rw [hsym, re_inner_orthonormalBasis_self_eq_sum_eigenvalues_mul hS hn v k]
    simp only [hM, hW0, Matrix.mulVec, dotProduct]
    exact Finset.sum_congr rfl fun i _ => by ring
  -- Birkhoff: extract a finite convex combination of permutation matrices.
  have hMconv : M ∈ convexHull ℝ
      {N : Matrix (Fin n) (Fin n) ℝ | ∃ σ : Equiv.Perm (Fin n), σ.permMatrix ℝ = N} := by
    rw [← doublyStochastic_eq_convexHull_permMatrix]; exact hMds
  obtain ⟨ι, _, a, Q, ha0, ha1, hQ, hQsum⟩ := mem_convexHull_iff_exists_fintype.mp hMconv
  choose σ hσ using hQ
  -- Push through `· *ᵥ W₀`: `c₀ = ∑ aₖ • (W₀ ∘ σₖ)`.
  have hcombo : c₀ = ∑ k, a k • (W₀ ∘ ⇑(σ k)) := by
    rw [hcMW, ← hQsum, Matrix.sum_mulVec]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [Matrix.smul_mulVec, ← hσ k, Matrix.permMatrix_mulVec]
  have hmem0 : c₀ ∈ convexHull ℝ (Set.range fun π : Equiv.Perm (Fin n) => W₀ ∘ (⇑π)) :=
    mem_convexHull_of_exists_fintype a (fun k => W₀ ∘ ⇑(σ k)) ha0 ha1
      (fun k => Set.mem_range_self (σ k)) hcombo.symm
  -- Transfer the membership through the linear identification `(Fin n → ℝ) ≃ₗ EuclideanSpace`.
  set L := (WithLp.linearEquiv 2 ℝ (Fin n → ℝ)).symm.toLinearMap with hL
  have hLimg := LinearMap.image_convexHull L (Set.range fun π : Equiv.Perm (Fin n) => W₀ ∘ (⇑π))
  have hmem1 : L c₀ ∈ convexHull ℝ (L '' Set.range fun π : Equiv.Perm (Fin n) => W₀ ∘ (⇑π)) := by
    rw [← hLimg]; exact Set.mem_image_of_mem L hmem0
  -- Identify `L c₀` with the diagonal and `L '' orbit` with the `permuteCoords` orbit.
  have hLc : L c₀ = e.symm c₀ := rfl
  have hset : (L '' Set.range fun π : Equiv.Perm (Fin n) => W₀ ∘ (⇑π))
      = Set.range fun π : Equiv.Perm (Fin n) => permuteCoords (e.symm W₀) π := by
    rw [← Set.range_comp]
    exact congrArg _ (funext fun π => rfl)
  rw [hLc, hset] at hmem1
  exact hmem1

/-- **L5 — Davis's eigenvalue-change lower bound (operator form).**  For self-adjoint
`T, S` with `H = S − T`, writing `𝒞H` for the diagonal part of `H` in `T`'s eigenbasis
and `𝒞⊥H` for the off-diagonal part, if the spectrum of `S` is `γ`-separated and
`‖𝒞H‖_F ≤ γ/√2`, then `∑ᵢ(λ'ᵢ − λᵢ)² ≥ ‖𝒞H‖²_F − ‖𝒞⊥H‖²_F` (`λ = spec T`, `λ' = spec S`,
sorted correspondence).  Wraps L4 via L3 and the diagonalisation of `re⟪vᵢ, S vᵢ⟫`. -/
theorem sum_sq_eigenvalues_sub_ge (hT : T.IsSymmetric) (hS : S.IsSymmetric)
    (hn : finrank 𝕜 E = n) {γ : ℝ} (hγ : 0 ≤ γ)
    (hsep : ∀ i j, i ≠ j → γ ≤ |hS.eigenvalues hn i - hS.eigenvalues hn j|)
    (hCH : ∑ i, (RCLike.re ⟪hT.eigenvectorBasis hn i, (S - T) (hT.eigenvectorBasis hn i)⟫_𝕜) ^ 2
            ≤ (γ / Real.sqrt 2) ^ 2) :
    (∑ i, (RCLike.re ⟪hT.eigenvectorBasis hn i, (S - T) (hT.eigenvectorBasis hn i)⟫_𝕜) ^ 2)
        - ((∑ i, (hS.eigenvalues hn i) ^ 2)
            - ∑ i, (RCLike.re ⟪hT.eigenvectorBasis hn i, S (hT.eigenvectorBasis hn i)⟫_𝕜) ^ 2)
      ≤ ∑ i, (hS.eigenvalues hn i - hT.eigenvalues hn i) ^ 2 := by
  set e := WithLp.equiv 2 (Fin n → ℝ) with he
  set v := hT.eigenvectorBasis hn with hv
  set W₀ : Fin n → ℝ := hS.eigenvalues hn with hW0
  set c₀ : Fin n → ℝ := fun k => RCLike.re ⟪v k, S (v k)⟫_𝕜 with hc0
  set dH : Fin n → ℝ := fun k => RCLike.re ⟪v k, (S - T) (v k)⟫_𝕜 with hdH0
  have hea : ∀ (f : Fin n → ℝ) (i : Fin n), (e.symm f) i = f i := fun _ _ => rfl
  -- squared norm of a lifted real tuple is the sum of squares
  have normLift_sq : ∀ f : Fin n → ℝ, ‖e.symm f‖ ^ 2 = ∑ i, (f i) ^ 2 := fun f => by
    rw [EuclideanSpace.norm_sq_eq]
    exact Finset.sum_congr rfl fun i _ => by rw [hea, Real.norm_eq_abs, sq_abs]
  -- the pinched diagonal recovers `λ`: `re⟪vᵢ,S vᵢ⟫ − re⟪vᵢ,(S−T)vᵢ⟫ = λᵢ`
  have hci : ∀ i, c₀ i - dH i = hT.eigenvalues hn i := fun i => by
    have hTeig : RCLike.re ⟪v i, T (v i)⟫_𝕜 = hT.eigenvalues hn i := by
      rw [hT.apply_eigenvectorBasis hn i, inner_smul_right,
        orthonormal_iff_ite.mp v.orthonormal i i]
      simp
    -- states the goal as the inner-product identity the structure lemma expects.
    change RCLike.re ⟪v i, S (v i)⟫_𝕜 - RCLike.re ⟪v i, (S - T) (v i)⟫_𝕜 = hT.eigenvalues hn i
    rw [← hTeig, ← map_sub, ← inner_sub_right]
    congr 2
    simp [LinearMap.sub_apply]
  -- assemble the hypotheses of L4
  have hdHnorm : ‖e.symm dH‖ ≤ γ / Real.sqrt 2 := by
    have h1 : ‖e.symm dH‖ ^ 2 ≤ (γ / Real.sqrt 2) ^ 2 := by rw [normLift_sq]; exact hCH
    calc ‖e.symm dH‖ = Real.sqrt (‖e.symm dH‖ ^ 2) := (Real.sqrt_sq (norm_nonneg _)).symm
      _ ≤ Real.sqrt ((γ / Real.sqrt 2) ^ 2) := Real.sqrt_le_sqrt h1
      _ = γ / Real.sqrt 2 := Real.sqrt_sq (by positivity)
  have hL4 := sum_sq_sub_pinch_ge (e.symm W₀) (e.symm c₀) (e.symm dH) hγ hsep
    (diag_mem_convexHull_perm_spectrum hT hS hn) hdHnorm
  -- rewrite the three norms and the displacement into sums
  have hRHS : ‖e.symm W₀ - (e.symm c₀ - e.symm dH)‖ ^ 2
      = ∑ i, (W₀ i - hT.eigenvalues hn i) ^ 2 := by
    rw [EuclideanSpace.norm_sq_eq]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [PiLp.sub_apply, Real.norm_eq_abs, sq_abs, hea, hci i]
  rw [normLift_sq, normLift_sq, normLift_sq, hRHS] at hL4
  exact hL4

end TauCeti
