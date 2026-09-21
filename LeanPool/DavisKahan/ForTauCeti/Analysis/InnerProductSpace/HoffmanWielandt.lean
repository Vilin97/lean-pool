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
`HoffmanWielandt.lean`).

Formalized by Claude Opus 4.8 (claude-opus-4-8[1m]).  This file will build up to the
Hoffman–Wielandt eigenvalue-perturbation inequality; it currently supplies the
sorted-rearrangement ingredient (W2.1).
-/
module

public import Mathlib.Algebra.Order.Rearrangement
public import Mathlib.Analysis.Convex.Birkhoff
public import LeanPool.DavisKahan.ForTauCeti.Analysis.InnerProductSpace.SchurHorn


/-! # Hoffman–Wielandt building blocks

The Hoffman–Wielandt inequality bounds the ℓ² distance between the sorted
spectra of two symmetric operators by the Frobenius norm of their difference.
Its proof factors through the von Neumann trace inequality, whose sorted core is
the rearrangement inequality recorded here.

## Main results

* `TauCeti.sum_mul_comp_perm_le_sum_mul_of_antitone`: for two decreasingly
  sorted real tuples `f, g` and any permutation `σ`,
  `∑ i, f (σ i) * g i ≤ ∑ i, f i * g i` — pairing the sorted tuples in order
  maximises the inner product.
* `TauCeti.sum_eigenvalues_mul_re_inner_self_le`: the **von Neumann trace
  inequality** (sorted, `≤` direction) — `tr(TS) ≤ ∑ᵢ λᵢ(T) λᵢ(S)`, written as
  `∑ k, λₖ(T) · re ⟪uₖ, S uₖ⟫ ≤ ∑ i, λᵢ(T) λᵢ(S)` in `T`'s eigenbasis `u`.

## References

* A. J. Hoffman and H. W. Wielandt, *The variation of the spectrum of a normal
  matrix*, Duke Math. J. 20 (1953), 37–39.
* G. H. Hardy, J. E. Littlewood, G. Pólya, *Inequalities*, 2nd ed., §10.2
  (the rearrangement inequality).

## Provenance

* Original repository: Davis--Kahan/DKPS formalization (Kitware, Inc.).
* Original module: `ForMathlib.Analysis.InnerProductSpace.HoffmanWielandt`, moved to
  `ForTauCeti` in the Wave-1 staging migration; introduced at Davis--Kahan
  commit `dd93e70`.
* Extraction class: **moved**.  The Wave-1 migration renamed the namespace
  `ForMathlib` to `TauCeti`; declaration names and proofs are unchanged.
* Original authors / copyright: Jon Crall, Claude Opus 4.8; Copyright (c) 2026 Kitware, Inc.;
  Apache 2.0.
* Spectra influence: **none** — this module imports only Mathlib and sibling
  `ForTauCeti` staging modules.
-/

public section

namespace TauCeti

open scoped BigOperators InnerProductSpace
open Matrix
open Module (finrank)

/-- **Sorted rearrangement inequality.** For two decreasingly sorted (antitone)
real tuples `f, g : Fin n → ℝ` and any permutation `σ`, permuting one tuple can
only decrease the pointwise product sum:
`∑ i, f (σ i) * g i ≤ ∑ i, f i * g i`.

The in-order pairing of two similarly sorted tuples maximises `∑ f i * g i`.
Immediate from Mathlib's rearrangement inequality once antitone tuples are seen
to monovary. -/
theorem sum_mul_comp_perm_le_sum_mul_of_antitone {n : ℕ} {f g : Fin n → ℝ}
    (hf : Antitone f) (hg : Antitone g) (σ : Equiv.Perm (Fin n)) :
    ∑ i, f (σ i) * g i ≤ ∑ i, f i * g i := by
  simpa only [smul_eq_mul] using (hf.monovary hg).sum_comp_perm_smul_le_sum_smul (σ := σ)

/-- **Birkhoff bilinear bound.** For decreasingly sorted real tuples `a, b` and a
doubly stochastic matrix `M`, the bilinear form `∑ₖ aₖ ∑ⱼ Mₖⱼ bⱼ` is maximised
by the identity pairing: `∑ₖ aₖ ∑ⱼ Mₖⱼ bⱼ ≤ ∑ᵢ aᵢ bᵢ`.

By Birkhoff's theorem `M` is a convex combination of permutation matrices; the
form is linear in `M`, and on each permutation vertex `σ` it equals
`∑ₖ aₖ b (σ k)`, which the sorted rearrangement inequality bounds by `∑ aᵢ bᵢ`. -/
theorem sum_mul_sum_mul_le_sum_mul_of_antitone {n : ℕ} {a b : Fin n → ℝ}
    (ha : Antitone a) (hb : Antitone b) {M : Matrix (Fin n) (Fin n) ℝ}
    (hM : M ∈ doublyStochastic ℝ (Fin n)) :
    ∑ k, a k * ∑ j, M k j * b j ≤ ∑ i, a i * b i := by
  classical
  -- Birkhoff: `M` is a finite convex combination of permutation matrices.
  have hMconv : M ∈ convexHull ℝ
      {N : Matrix (Fin n) (Fin n) ℝ | ∃ σ : Equiv.Perm (Fin n), σ.permMatrix ℝ = N} := by
    rw [← doublyStochastic_eq_convexHull_permMatrix]; exact hM
  obtain ⟨ι, _, c, Q, hc0, hc1, hQ, hQsum⟩ := mem_convexHull_iff_exists_fintype.mp hMconv
  choose σ hσ using hQ
  -- Each vertex row acts as the permutation on `b`: `∑ⱼ (Q l) k j bⱼ = b (σ l k)`.
  have hrow : ∀ l k, ∑ j, Q l k j * b j = b (σ l k) := fun l k => by
    have h1 : Q l *ᵥ b = b ∘ σ l := by rw [← hσ l, permMatrix_mulVec]
    calc ∑ j, Q l k j * b j = (Q l *ᵥ b) k := rfl
      _ = b (σ l k) := by rw [h1]; rfl
  -- Expand `M` as the convex combination and collapse each vertex.
  have hcol : ∀ k, ∑ j, M k j * b j = ∑ l, c l * b (σ l k) := fun k => by
    have hMkj : ∀ j, M k j = ∑ l, c l * Q l k j := fun j => by
      rw [← hQsum]; simp [Matrix.sum_apply]
    calc ∑ j, M k j * b j
        = ∑ j, ∑ l, c l * Q l k j * b j := by simp_rw [hMkj, Finset.sum_mul]
      _ = ∑ l, c l * ∑ j, Q l k j * b j := by
          rw [Finset.sum_comm]; simp_rw [Finset.mul_sum, mul_assoc]
      _ = ∑ l, c l * b (σ l k) := by simp_rw [hrow]
  calc ∑ k, a k * ∑ j, M k j * b j
      = ∑ l, c l * ∑ k, a k * b (σ l k) := by
        simp_rw [hcol, Finset.mul_sum]
        rw [Finset.sum_comm]
        exact Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun k _ => by ring
    _ ≤ ∑ l, c l * ∑ i, a i * b i := by
        refine Finset.sum_le_sum fun l _ => mul_le_mul_of_nonneg_left ?_ (hc0 l)
        -- `∑ₖ aₖ b (σ k) = ∑ₘ a (σ⁻¹ m) b m ≤ ∑ aᵢ bᵢ`.
        have hreindex : ∑ k, a k * b (σ l k) = ∑ m, a ((σ l).symm m) * b m := by
          rw [← Equiv.sum_comp (σ l) (fun m => a ((σ l).symm m) * b m)]
          exact Finset.sum_congr rfl fun k _ => by rw [Equiv.symm_apply_apply]
        rw [hreindex]
        exact sum_mul_comp_perm_le_sum_mul_of_antitone ha hb (σ l).symm
    _ = ∑ i, a i * b i := by rw [← Finset.sum_mul, hc1, one_mul]

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  [FiniteDimensional 𝕜 E] {n : ℕ} {T S : E →ₗ[𝕜] E}

/-- **Von Neumann trace inequality (sorted, `≤` direction).** For symmetric `T, S`
with decreasingly sorted eigenvalues, `tr(T S) ≤ ∑ᵢ λᵢ(T) λᵢ(S)`.  Written in
`T`'s eigenbasis `u`, where `tr(T S) = ∑ₖ λₖ(T) · re ⟪uₖ, S uₖ⟫`:
`∑ k, λₖ(T) · re ⟪uₖ, S uₖ⟫ ≤ ∑ i, λᵢ(T) · λᵢ(S)`.

The diagonal `re ⟪uₖ, S uₖ⟫` is the doubly-stochastic image `∑ⱼ λⱼ(S) wⱼₖ` of
`S`'s spectrum (`schurWeight`); the claim is then the Birkhoff bilinear bound. -/
theorem sum_eigenvalues_mul_re_inner_self_le
    (hT : T.IsSymmetric) (hS : S.IsSymmetric) (hn : finrank 𝕜 E = n) :
    ∑ k, hT.eigenvalues hn k *
        RCLike.re ⟪hT.eigenvectorBasis hn k, S (hT.eigenvectorBasis hn k)⟫_𝕜
      ≤ ∑ i, hT.eigenvalues hn i * hS.eigenvalues hn i := by
  set u := hT.eigenvectorBasis hn with hu
  set M : Matrix (Fin n) (Fin n) ℝ := fun k j => schurWeight hS hn u j k with hM
  -- `M` is doubly stochastic (rows/cols are the Schur weights).
  have hMds : M ∈ doublyStochastic ℝ (Fin n) := by
    rw [mem_doublyStochastic_iff_sum]
    exact ⟨fun k j => schurWeight_nonneg hS hn u j k,
      fun k => schurWeight_row_sum hS hn u k, fun j => schurWeight_col_sum hS hn u j⟩
  -- The diagonal of `S` in `u` is `∑ⱼ Mₖⱼ λⱼ(S)`.
  have hdiag : ∀ k, RCLike.re ⟪u k, S (u k)⟫_𝕜 = ∑ j, M k j * hS.eigenvalues hn j := by
    intro k
    rw [show ⟪u k, S (u k)⟫_𝕜 = ⟪S (u k), u k⟫_𝕜 from (hS (u k) (u k)).symm,
      re_inner_orthonormalBasis_self_eq_sum_eigenvalues_mul hS hn u k]
    exact Finset.sum_congr rfl fun j _ => by rw [hM]; ring
  simp_rw [hdiag]
  exact sum_mul_sum_mul_le_sum_mul_of_antitone (hT.eigenvalues_antitone hn)
    (hS.eigenvalues_antitone hn) hMds

/-- **Basis independence of the squared Frobenius norm.** For symmetric `S` and
any orthonormal basis `e`, `∑ₖ ‖S (e k)‖² = ∑ᵢ λᵢ(S)²`: the Hilbert–Schmidt norm
of `S` equals the ℓ² norm of its spectrum.  A double Parseval swap through `S`'s
own eigenbasis, using self-adjointness to move `S` across the inner product. -/
theorem sum_sq_norm_apply_eq_sum_sq_eigenvalues
    (hS : S.IsSymmetric) (hn : finrank 𝕜 E = n) (e : OrthonormalBasis (Fin n) 𝕜 E) :
    ∑ k, ‖S (e k)‖ ^ 2 = ∑ j, (hS.eigenvalues hn j) ^ 2 := by
  have hterm : ∀ j k, ‖⟪hS.eigenvectorBasis hn j, S (e k)⟫_𝕜‖ ^ 2
      = (hS.eigenvalues hn j) ^ 2 * ‖⟪hS.eigenvectorBasis hn j, e k⟫_𝕜‖ ^ 2 := by
    intro j k
    simp only [← hS (hS.eigenvectorBasis hn j) (e k), hS.apply_eigenvectorBasis hn j,
      inner_smul_left, RCLike.conj_ofReal, norm_mul, mul_pow, RCLike.norm_ofReal, sq_abs]
  calc ∑ k, ‖S (e k)‖ ^ 2
      = ∑ k, ∑ j, ‖⟪hS.eigenvectorBasis hn j, S (e k)⟫_𝕜‖ ^ 2 :=
        Finset.sum_congr rfl fun k _ =>
          ((hS.eigenvectorBasis hn).sum_sq_norm_inner_right (S (e k))).symm
    _ = ∑ j, (hS.eigenvalues hn j) ^ 2 * ∑ k, ‖⟪hS.eigenvectorBasis hn j, e k⟫_𝕜‖ ^ 2 := by
        rw [Finset.sum_comm]
        exact Finset.sum_congr rfl fun j _ => by
          rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun k _ => hterm j k
    _ = ∑ j, (hS.eigenvalues hn j) ^ 2 :=
        Finset.sum_congr rfl fun j _ => by
          rw [e.sum_sq_norm_inner_left (hS.eigenvectorBasis hn j),
            (hS.eigenvectorBasis hn).orthonormal.norm_eq_one j, one_pow, mul_one]

/-- **Hoffman–Wielandt inequality.** For symmetric `T, S` with decreasingly sorted
eigenvalues, the ℓ² distance between the two spectra is at most the squared
Frobenius norm of the perturbation:
`∑ᵢ (λᵢ(T) − λᵢ(S))² ≤ ∑ₖ ‖(S − T) uₖ‖²` (`u` = `T`'s eigenbasis).

Expanding both sides: the `∑ λᵢ(T)²` and `∑ λᵢ(S)²` pieces match (the latter via
basis independence of the Frobenius norm), and the cross terms reduce the claim
to the von Neumann trace inequality `sum_eigenvalues_mul_re_inner_self_le`. -/
@[simp]
theorem sum_sq_eigenvalues_sub_le_sum_sq_norm_apply
    (hT : T.IsSymmetric) (hS : S.IsSymmetric) (hn : finrank 𝕜 E = n) :
    ∑ i, (hT.eigenvalues hn i - hS.eigenvalues hn i) ^ 2
      ≤ ∑ k, ‖(S - T) (hT.eigenvectorBasis hn k)‖ ^ 2 := by
  set u := hT.eigenvectorBasis hn with hu
  -- Per-column expansion of the perturbation Frobenius norm.
  have hexp : ∀ k, ‖(S - T) (u k)‖ ^ 2
      = ‖S (u k)‖ ^ 2
        - 2 * (hT.eigenvalues hn k * RCLike.re ⟪u k, S (u k)⟫_𝕜)
        + (hT.eigenvalues hn k) ^ 2 := by
    intro k
    have h1 : (S - T) (u k) = S (u k) - (hT.eigenvalues hn k : 𝕜) • u k := by
      rw [LinearMap.sub_apply, hu, hT.apply_eigenvectorBasis hn k]
    have h2 : RCLike.re ⟪S (u k), (hT.eigenvalues hn k : 𝕜) • u k⟫_𝕜
        = hT.eigenvalues hn k * RCLike.re ⟪u k, S (u k)⟫_𝕜 := by
      rw [inner_smul_right, RCLike.re_ofReal_mul, hS (u k) (u k)]
    have h3 : ‖(hT.eigenvalues hn k : 𝕜) • u k‖ ^ 2 = (hT.eigenvalues hn k) ^ 2 := by
      rw [norm_smul, mul_pow, RCLike.norm_ofReal, sq_abs,
        (hT.eigenvectorBasis hn).orthonormal.norm_eq_one k]
      simp
    rw [h1, norm_sub_sq (𝕜 := 𝕜), h2, h3]
  -- Sum the expansion; expand the LHS; use basis independence and von Neumann.
  have hRHS : ∑ k, ‖(S - T) (u k)‖ ^ 2
      = ∑ k, ‖S (u k)‖ ^ 2
        - 2 * ∑ k, hT.eigenvalues hn k * RCLike.re ⟪u k, S (u k)⟫_𝕜
        + ∑ k, (hT.eigenvalues hn k) ^ 2 := by
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun k _ => hexp k
  have hLHS : ∑ i, (hT.eigenvalues hn i - hS.eigenvalues hn i) ^ 2
      = ∑ i, (hT.eigenvalues hn i) ^ 2
        - 2 * ∑ i, hT.eigenvalues hn i * hS.eigenvalues hn i
        + ∑ i, (hS.eigenvalues hn i) ^ 2 := by
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun i _ => by rw [sub_sq]; ring
  rw [hLHS, hRHS, sum_sq_norm_apply_eq_sum_sq_eigenvalues hS hn u]
  have hvn := sum_eigenvalues_mul_re_inner_self_le hT hS hn
  rw [← hu] at hvn
  linarith [hvn]

end TauCeti
