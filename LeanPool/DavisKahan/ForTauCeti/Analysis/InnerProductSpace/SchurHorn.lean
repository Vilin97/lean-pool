/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, Claude Opus 4.8
-/

/-
Staged for Tau Ceti, roadmap topic T05.  Mathlib is not the destination
(`ForTauCeti/README.md`); what follows is where this material would have gone on
the closed Mathlib track —
additions to `Mathlib/Analysis/InnerProductSpace/` (new file
`SchurHorn.lean`).

Formalized by Claude Opus 4.8 (claude-opus-4-8[1m]).

The forward ("Schur") direction of the Schur–Horn theorem in convex/Karamata
form: the diagonal of a symmetric operator in *any* orthonormal basis is
majorized by its spectrum.  This is the foundation of Davis's eigenvalue-change
lower bound and hence of the sharper Davis–Kahan total-rotation estimate.

Proof strategy read from and credited to rjwalters/lean-genius,
`proofs/Proofs/SchurHornMajorization.lean` (commit
3e09c97392dc68d068becb89e2068b1830234661, retrieved 2026-07-04; no license
declared upstream).  Independently re-derived here on this project's existing
`LinearMap.IsSymmetric.re_inner_apply_self_eq_sum_eigenvalues_mul_sq`.
-/
module

public import Mathlib.Analysis.Convex.Jensen
public import Mathlib.Analysis.Convex.Mul
public import LeanPool.DavisKahan.ForTauCeti.Analysis.InnerProductSpace.CourantFischer


/-! # Schur–Horn majorization (forward direction, Karamata form)

Let `T` be a symmetric operator on a finite-dimensional inner product space over
`𝕜 = ℝ, ℂ`, with sorted eigenvalues `λ` (`hT.eigenvalues hn`) and orthonormal
eigenbasis `v` (`hT.eigenvectorBasis hn`).  Fix *any* orthonormal basis `e`.  The
"diagonal" of `T` in `e` is the tuple `d k = re ⟪T (e k), e k⟫`.

The forward direction of the **Schur–Horn theorem** (due to Schur, 1923) says the
diagonal is majorized by the spectrum, `diag T ≺ spec T`.  We prove the
equivalent Hardy–Littlewood–Pólya / **Karamata** characterisation:
`∑ φ (d k) ≤ ∑ φ (λ i)` for every convex `φ` defined on a set containing the
eigenvalues.

The mechanism is the doubly-stochastic weight matrix `w i k = ‖⟪vᵢ, e k⟫‖²`
(`schurWeight`): its rows and columns sum to `1` by Parseval, and the diagonal is
its image of the spectrum, `d k = ∑ i, λ i * w i k`.  Row-wise Jensen followed by
a sum swap over the column sums gives the inequality.

Mathlib has the spectral theorem and Birkhoff's theorem but no majorization
predicate and no Schur–Horn theorem (only a comment in
`Mathlib/Analysis/InnerProductSpace/Spectrum.lean`); this file supplies the
forward direction in the self-contained convex-function form.

## Main results

* `TauCeti.schurWeight` and `schurWeight_row_sum` / `schurWeight_col_sum`: the
  doubly-stochastic weight matrix.
* `TauCeti.re_inner_orthonormalBasis_self_eq_sum_eigenvalues_mul`: the diagonal
  is the doubly-stochastic image of the spectrum.
* `TauCeti.convexOn_sum_re_inner_orthonormalBasis_self_le`: **forward
  Schur–Horn** (Karamata form), `∑ φ (d k) ≤ ∑ φ (λ i)`.
* `TauCeti.sum_re_inner_orthonormalBasis_self_eq_sum_eigenvalues`: basis
  independence of the trace (the equality case).
* `TauCeti.sum_sq_re_inner_orthonormalBasis_self_le_sum_sq_eigenvalues`: the
  `φ = (·)²` instance — the diagonal has Euclidean length ≤ that of the spectrum.

## References

* I. Schur, *Über eine Klasse von Mittelbildungen mit Anwendungen auf die
  Determinantentheorie*, Sitzungsber. Berl. Math. Ges. 22 (1923), 9–20.
* A. W. Marshall, I. Olkin, B. C. Arnold, *Inequalities: Theory of Majorization
  and Its Applications*, 2nd ed., Theorem 9.B.1.

## Provenance

* Original repository: Davis--Kahan/DKPS formalization (Kitware, Inc.).
* Original module: `ForMathlib.Analysis.InnerProductSpace.SchurHorn`, moved to
  `ForTauCeti` in the Wave-1 staging migration; introduced at Davis--Kahan
  commit `9543631`.
* Extraction class: **moved**.  The Wave-1 migration renamed the namespace
  `ForMathlib` to `TauCeti`; declaration names and proofs are unchanged.
* Original authors / copyright: Jon Crall, Claude Opus 4.8; Copyright (c) 2026 Kitware, Inc.;
  Apache 2.0.
* Spectra influence: **none** — this module imports only Mathlib and sibling
  `ForTauCeti` staging modules.
-/

public section

namespace TauCeti

open scoped InnerProductSpace BigOperators
open Module (finrank)

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  [FiniteDimensional 𝕜 E] {n : ℕ} {T : E →ₗ[𝕜] E}

/-- The doubly-stochastic weight `w i k = ‖⟪vᵢ, e k⟫‖²` of the `i`-th eigenvector
`vᵢ` of `T` against the `k`-th vector of a chosen orthonormal basis `e`. -/
noncomputable def schurWeight (hT : T.IsSymmetric) (hn : finrank 𝕜 E = n)
    (e : OrthonormalBasis (Fin n) 𝕜 E) (i k : Fin n) : ℝ :=
  ‖⟪hT.eigenvectorBasis hn i, e k⟫_𝕜‖ ^ 2

/-- Schur--Horn weights are nonnegative, being squared moduli of basis coefficients. -/
theorem schurWeight_nonneg (hT : T.IsSymmetric) (hn : finrank 𝕜 E = n)
    (e : OrthonormalBasis (Fin n) 𝕜 E) (i k : Fin n) :
    0 ≤ schurWeight hT hn e i k :=
  sq_nonneg _

/-- **Rows sum to one.** By Parseval for the eigenbasis `v`,
`∑ i, ‖⟪vᵢ, e k⟫‖² = ‖e k‖² = 1`. -/
theorem schurWeight_row_sum (hT : T.IsSymmetric) (hn : finrank 𝕜 E = n)
    (e : OrthonormalBasis (Fin n) 𝕜 E) (k : Fin n) :
    ∑ i, schurWeight hT hn e i k = 1 := by
  simp only [schurWeight]
  rw [(hT.eigenvectorBasis hn).sum_sq_norm_inner_right (e k),
    e.orthonormal.norm_eq_one k, one_pow]

/-- **Columns sum to one.** By Parseval for the basis `e`,
`∑ k, ‖⟪vᵢ, e k⟫‖² = ‖vᵢ‖² = 1`. -/
theorem schurWeight_col_sum (hT : T.IsSymmetric) (hn : finrank 𝕜 E = n)
    (e : OrthonormalBasis (Fin n) 𝕜 E) (i : Fin n) :
    ∑ k, schurWeight hT hn e i k = 1 := by
  simp only [schurWeight]
  rw [e.sum_sq_norm_inner_left (hT.eigenvectorBasis hn i),
    (hT.eigenvectorBasis hn).orthonormal.norm_eq_one i, one_pow]

/-- **Diagonal = doubly-stochastic image of the spectrum.** The diagonal entry
`re ⟪T (e k), e k⟫` of `T` in the basis `e` is the convex combination
`∑ i, λ i * w i k` of the eigenvalues.  Immediate from the diagonalisation of the
quadratic form together with `vⱼ.repr (e k) i = ⟪vᵢ, e k⟫`. -/
theorem re_inner_orthonormalBasis_self_eq_sum_eigenvalues_mul
    (hT : T.IsSymmetric) (hn : finrank 𝕜 E = n)
    (e : OrthonormalBasis (Fin n) 𝕜 E) (k : Fin n) :
    RCLike.re ⟪T (e k), e k⟫_𝕜
      = ∑ i, hT.eigenvalues hn i * schurWeight hT hn e i k := by
  rw [LinearMap.IsSymmetric.re_inner_apply_self_eq_sum_eigenvalues_mul_sq hT hn (e k)]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [schurWeight, OrthonormalBasis.repr_apply_apply]

/-- **Forward Schur–Horn theorem (convex / Karamata form).** For any convex
function `φ` on a set `s` containing all eigenvalues of the symmetric operator
`T`, the diagonal of `T` in *any* orthonormal basis `e` satisfies
`∑ k, φ (re ⟪T (e k), e k⟫) ≤ ∑ i, φ (λ i)`, i.e. `diag T ≺ spec T`.

Row-by-row Jensen against the doubly-stochastic weight matrix `schurWeight`,
followed by a sum swap collapsing the column sums. -/
theorem convexOn_sum_re_inner_orthonormalBasis_self_le
    (hT : T.IsSymmetric) (hn : finrank 𝕜 E = n) (e : OrthonormalBasis (Fin n) 𝕜 E)
    {φ : ℝ → ℝ} {s : Set ℝ} (hφ : ConvexOn ℝ s φ)
    (hmem : ∀ i, hT.eigenvalues hn i ∈ s) :
    ∑ k, φ (RCLike.re ⟪T (e k), e k⟫_𝕜) ≤ ∑ i, φ (hT.eigenvalues hn i) := by
  have step : ∀ k, φ (RCLike.re ⟪T (e k), e k⟫_𝕜)
      ≤ ∑ i, schurWeight hT hn e i k • φ (hT.eigenvalues hn i) := by
    intro k
    have hJ := hφ.map_sum_le (t := Finset.univ)
      (w := fun i => schurWeight hT hn e i k) (p := fun i => hT.eigenvalues hn i)
      (fun i _ => schurWeight_nonneg hT hn e i k) (schurWeight_row_sum hT hn e k)
      (fun i _ => hmem i)
    have hsum : (∑ i, schurWeight hT hn e i k • hT.eigenvalues hn i)
        = RCLike.re ⟪T (e k), e k⟫_𝕜 := by
      rw [re_inner_orthonormalBasis_self_eq_sum_eigenvalues_mul hT hn e k]
      exact Finset.sum_congr rfl fun i _ => by rw [smul_eq_mul, mul_comm]
    rwa [hsum] at hJ
  calc ∑ k, φ (RCLike.re ⟪T (e k), e k⟫_𝕜)
      ≤ ∑ k, ∑ i, schurWeight hT hn e i k • φ (hT.eigenvalues hn i) :=
        Finset.sum_le_sum fun k _ => step k
    _ = ∑ i, (∑ k, schurWeight hT hn e i k) • φ (hT.eigenvalues hn i) := by
        rw [Finset.sum_comm]
        exact Finset.sum_congr rfl fun i _ => by rw [Finset.sum_smul]
    _ = ∑ i, φ (hT.eigenvalues hn i) := by
        exact Finset.sum_congr rfl fun i _ => by
          rw [schurWeight_col_sum hT hn e i, one_smul]

/-- **Basis independence of the trace** (the equality case of Schur majorization).
The sum of the diagonal entries of `T` in any orthonormal basis equals the sum of
its eigenvalues.  No convexity needed. -/
theorem sum_re_inner_orthonormalBasis_self_eq_sum_eigenvalues
    (hT : T.IsSymmetric) (hn : finrank 𝕜 E = n) (e : OrthonormalBasis (Fin n) 𝕜 E) :
    ∑ k, RCLike.re ⟪T (e k), e k⟫_𝕜 = ∑ i, hT.eigenvalues hn i := by
  calc ∑ k, RCLike.re ⟪T (e k), e k⟫_𝕜
      = ∑ k, ∑ i, hT.eigenvalues hn i * schurWeight hT hn e i k :=
        Finset.sum_congr rfl fun k _ =>
          re_inner_orthonormalBasis_self_eq_sum_eigenvalues_mul hT hn e k
    _ = ∑ i, hT.eigenvalues hn i * (∑ k, schurWeight hT hn e i k) := by
        rw [Finset.sum_comm]
        exact Finset.sum_congr rfl fun i _ => by rw [Finset.mul_sum]
    _ = ∑ i, hT.eigenvalues hn i := by
        exact Finset.sum_congr rfl fun i _ => by rw [schurWeight_col_sum hT hn e i, mul_one]

/-- **Sum-of-squares bound** (the `φ = (·)²` instance of Schur majorization).  The
diagonal of `T` in any orthonormal basis has Euclidean length no larger than the
spectrum: `∑ k, (re ⟪T (e k), e k⟫)² ≤ ∑ i, (λ i)²`. -/
theorem sum_sq_re_inner_orthonormalBasis_self_le_sum_sq_eigenvalues
    (hT : T.IsSymmetric) (hn : finrank 𝕜 E = n) (e : OrthonormalBasis (Fin n) 𝕜 E) :
    ∑ k, (RCLike.re ⟪T (e k), e k⟫_𝕜) ^ 2 ≤ ∑ i, (hT.eigenvalues hn i) ^ 2 :=
  convexOn_sum_re_inner_orthonormalBasis_self_le hT hn e (φ := fun x => x ^ 2)
    (s := Set.univ) (Even.convexOn_pow (by decide)) (fun _ => Set.mem_univ _)

end TauCeti
