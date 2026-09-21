/-
Copyright (c) 2026 Mario Ullrich. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Ullrich
-/
import LeanPool.SNumbers.SNumbers.Approximation
import LeanPool.SNumbers.SNumbers.Bernstein
import LeanPool.SNumbers.SNumbers.Gelfand
import LeanPool.SNumbers.SNumbers.Kolmogorov
import LeanPool.SNumbers.SNumbers.Hilbert
import LeanPool.SNumbers.SNumbers.PiLpCoordinates
import LeanPool.SNumbers.SNumbers.Examples.ExHelpers
import LeanPool.SNumbers.SNumbers.Examples.Identity
import Mathlib.Analysis.Normed.Lp.PiLp
import Mathlib.Analysis.MeanInequalities

/-!
# Example: s-numbers of diagonal operators

This file is a worked **example** illustrating the abstract s-number theory on a
concrete family of operators: the **diagonal operators**

`D_σ x = (σ_i · x_i)_i`,

where `σ : Fin m → 𝕜` is the diagonal and the spaces are the finite-dimensional
sequence spaces `ℓ^p_m = PiLp p (fun _ : Fin m => 𝕜)`. It covers **all pairs of
exponents**, in two parts.

## Part I — the same exponent, `D_σ : ℓ^p_m → ℓ^p_m`

* `DiagCLM p σ` — the diagonal operator as a continuous linear map, with operator
  norm `norm_DiagCLM : ‖D_σ‖ = ⨆ i, ‖σ i‖`.
* `sn_DiagCLM_eq` — the main result: for every **strict** s-number sequence `s`,
  `sₙ(D_σ) = ‖σ_n‖` (the `(n+1)`-th largest entry) when the diagonal is
  non-increasing in modulus and `n < m`. Specialised to the named examples:
  `approximationNumber_DiagCLM_eq`, `gelfandNumber_DiagCLM_eq`,
  `kolmogorovNumber_DiagCLM_eq`, `bernsteinNumber_DiagCLM_eq`.
* `hilbertNumber_DiagCLM_le` — for the Hilbert numbers only the bound
  `hₙ(D_σ) ≤ ‖σ_n‖` holds (equality can fail for `p ≠ 2`).
* `sn_id_piLp` — the unit diagonal `σ ≡ 1` is the identity, with `sₙ(id) = 1`
  for `n < m` directly from (S5').

## Part II — mixed exponents, `D_σ : ℓ^q_m → ℓ^p_m`

* `DiagCLMpq p q σ` — the operator, with `DiagCLMpq_self` / `DiagCLMpq_one`
  identifying it with `DiagCLM` (when `q = p`) and with the identity embedding
  `idEmbed` (when `σ ≡ 1`).
* `diagExp p q` — the conjugate exponent `r`, `1/r = 1/p − 1/q`.
* `norm_DiagCLMpq_eq` — the operator norm `‖D_σ‖ = ‖σ‖_{ℓ^r}` (the `n = 0` case).
* `approximationNumber_DiagCLMpq_eq` — for `1 ≤ p < q < ∞` the main result
  `aₙ(D_σ) = (∑_{k≥n} ‖σ_k‖^r)^{1/r}`, the `ℓ^r`-norm of the tail (the `m − n`
  smallest entries); `sn_DiagCLMpq_le` is the universal upper bound for every
  s-number sequence. Unlike the same-exponent case, for `p < q` the various
  strict s-numbers genuinely differ, so only `aₙ` is pinned down exactly.
* The reverse regime `q ≤ p` (including `p = ∞`) degenerates to `r = ∞`:
  `norm_DiagCLMpq_iSup` (`‖D_σ‖ = ⨆ i, ‖σ i‖`) and the universal upper bound
  `sn_DiagCLMpq_le_of_exponent_ge` (`sₙ(D_σ) ≤ ‖σ_n‖`), both inherited from
  Part I through the factorisation `D_σ = (id : ℓ^q → ℓ^p) ∘ D_σ^{(q)}`. For
  `p > q` the exact approximation numbers have no elementary closed form (the
  Gelfand/Kolmogorov-width regime), so only these two bounds are recorded.

The unit-diagonal case is developed separately and self-containedly in
`SNumbers.Examples.Identity`, which this file builds on; the shared geometric
and rank ingredients are in `SNumbers.Examples.ExHelpers`, and the coordinate
maps `projFin` / `padFin` in `SNumbers.PiLpCoordinates`.

## References

* A. Pietsch, *Eigenvalues and s-numbers*, Cambridge Studies in Advanced
  Mathematics 13, Cambridge University Press, 1987,
  [link](https://zbmath.org/3996455).
-/

universe u

open scoped ENNReal
open ContinuousLinearMap

namespace SNumbers

variable {𝕜 : Type u} [RCLike 𝕜] {m : ℕ} {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-! ## Stage 0 — the diagonal operator and its norm -/

/-- The **diagonal operator** `D_σ : ℓ^p_m → ℓ^p_m`, `x ↦ (σ_i · x_i)`, as a
continuous linear map. The domain is finite-dimensional, so continuity is
automatic (`LinearMap.toContinuousLinearMap`). -/
noncomputable def DiagCLM (p : ℝ≥0∞) [Fact (1 ≤ p)] (σ : Fin m → 𝕜) :
    PiLp p (fun _ : Fin m => 𝕜) →L[𝕜] PiLp p (fun _ : Fin m => 𝕜) :=
  LinearMap.toContinuousLinearMap
    { toFun := fun x => WithLp.toLp p (fun i => σ i • x i)
      map_add' := fun x y => by
        ext i; simp [mul_add]
      map_smul' := fun c x => by
        ext i; simp [mul_left_comm] }

@[simp] lemma DiagCLM_apply (σ : Fin m → 𝕜) (x : PiLp p (fun _ : Fin m => 𝕜))
    (i : Fin m) : (DiagCLM p σ x) i = σ i • x i := rfl

/-- **Operator norm of a diagonal operator** (same exponent `p` on both sides):
`‖D_σ‖ = ⨆ i, ‖σ i‖`, the largest modulus of a diagonal entry. The supremum is
attained at some coordinate `j₀`; the upper bound dominates `D_σ` coordinatewise
by the scalar multiple `σ j₀ • ·`, and the lower bound tests `D_σ` on the basis
vector `e_{j₀}`. -/
theorem norm_DiagCLM [Nonempty (Fin m)] (σ : Fin m → 𝕜) :
    ‖DiagCLM p σ‖ = ⨆ i, ‖σ i‖ := by
  obtain ⟨j₀, hj₀⟩ := Finite.exists_max (fun i => ‖σ i‖)
  have hMeq : (⨆ i, ‖σ i‖) = ‖σ j₀‖ :=
    le_antisymm (ciSup_le hj₀) (le_ciSup (Finite.bddAbove_range fun i => ‖σ i‖) j₀)
  rw [hMeq]
  refine le_antisymm ?_ ?_
  · -- Upper bound: `‖D_σ x‖ ≤ ‖σ j₀‖ * ‖x‖` for all `x`.
    refine opNorm_le_bound _ (norm_nonneg _) fun x => ?_
    calc ‖DiagCLM p σ x‖
        ≤ ‖σ j₀ • x‖ := by
          refine piLp_norm_mono fun i => ?_
          rw [DiagCLM_apply, PiLp.smul_apply, norm_smul, norm_smul]
          exact mul_le_mul_of_nonneg_right (hj₀ i) (norm_nonneg _)
      _ = ‖σ j₀‖ * ‖x‖ := norm_smul _ _
  · -- Lower bound: test on the basis vector `e_{j₀} = single p j₀ 1`.
    set e : PiLp p (fun _ : Fin m => 𝕜) := PiLp.single p j₀ (1 : 𝕜) with he_def
    have hDe : DiagCLM p σ e = PiLp.single p j₀ (σ j₀) := by
      ext k
      rcases eq_or_ne k j₀ with rfl | hk
      · simp [he_def]
      · simp [he_def, hk]
    have he : ‖e‖ = 1 := by rw [he_def, PiLp.norm_single, norm_one]
    have hbound := (DiagCLM p σ).le_opNorm e
    rw [hDe, PiLp.norm_single, he, mul_one] at hbound
    exact hbound

/-! ## Stage 2 — the upper bound `aₙ(D_σ) ≤ σ_{n+1}` for every s-number

We assume the diagonal is arranged in non-increasing order of modulus
(`Antitone fun i => ‖σ i‖`), so the `(n+1)`-th largest entry is `‖σ_n‖`.
Truncating `D_σ` to its top `n` coordinates yields a rank-`≤ n` approximant
whose residual is the diagonal of the remaining entries, of norm `‖σ_n‖`.
Since the approximation numbers are the largest s-numbers, the bound transfers
to **every** s-number sequence. -/

/-- **Upper bound.** If the diagonal is non-increasing in modulus, the `n`-th
approximation number of `D_σ : ℓ^p_m → ℓ^p_m` is at most `‖σ_n‖` (the
`(n+1)`-th largest entry), for `n < m`. -/
theorem approximationNumber_DiagCLM_le {σ : Fin m → 𝕜}
    (hσ : _root_.Antitone fun i => ‖σ i‖) {n : ℕ} (hn : n < m) :
    approximationNumber (DiagCLM p σ) n ≤ ‖σ ⟨n, hn⟩‖ := by
  have : Nonempty (Fin m) := ⟨⟨n, hn⟩⟩
  -- The rank-`≤ n` approximant `L = D_σ ∘ Pₙ`, written as `B ∘ id_{ℓ^p_n} ∘ A`
  -- so its rank is bounded by `dim ℓ^p_n = n`.
  set A : PiLp p (fun _ : Fin m => 𝕜) →L[𝕜] PiLp p (fun _ : Fin n => 𝕜) :=
    projFin hn.le with hA
  set B : PiLp p (fun _ : Fin n => 𝕜) →L[𝕜] PiLp p (fun _ : Fin m => 𝕜) :=
    (DiagCLM p σ).comp padFin with hB
  set L := B.comp ((ContinuousLinearMap.id 𝕜 (PiLp p (fun _ : Fin n => 𝕜))).comp A) with hL
  -- The residual diagonal `ρ`: the entries from index `n` on.
  set ρ : Fin m → 𝕜 := fun i => if (i : ℕ) < n then 0 else σ i with hρ
  have hLrank : L.rank ≤ (n : Cardinal) :=
    (ContinuousLinearMap.rank_comp_comp_le A _ B).trans_eq (rank_id_piLp n)
  -- `D_σ - L = DiagCLM ρ`.
  have hres : DiagCLM p σ - L = DiagCLM p ρ := by
    ext x i
    simp only [hL, hA, hB, sub_apply, ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.id_apply, DiagCLM_apply, PiLp.sub_apply]
    rw [padFin_projFin_apply]
    by_cases hi : (i : ℕ) < n <;> simp [hρ, hi]
  -- The residual norm is `⨆_{i ≥ n} ‖σ i‖ = ‖σ_n‖`.
  have hsup : (⨆ i, ‖ρ i‖) = ‖σ ⟨n, hn⟩‖ := by
    refine le_antisymm (ciSup_le fun i => ?_) ?_
    · by_cases hi : (i : ℕ) < n
      · simp [hρ, hi]
      · have hle : (⟨n, hn⟩ : Fin m) ≤ i := by
          simp only [Fin.le_def]; omega
        simpa [hρ, hi] using hσ hle
    · have : ‖σ ⟨n, hn⟩‖ = ‖ρ ⟨n, hn⟩‖ := by simp [hρ]
      rw [this]
      exact le_ciSup (Finite.bddAbove_range fun i => ‖ρ i‖) (⟨n, hn⟩ : Fin m)
  calc approximationNumber (DiagCLM p σ) n
      ≤ ‖DiagCLM p σ - L‖ := approximationNumber_le_norm_sub hLrank
    _ = ‖DiagCLM p ρ‖ := by rw [hres]
    _ = ⨆ i, ‖ρ i‖ := norm_DiagCLM ρ
    _ = ‖σ ⟨n, hn⟩‖ := hsup

/-! ## Stage 3 — the lower bound `σ_{n+1} ≤ sₙ(D_σ)` for strict s-numbers

For the lower bound we factor the identity on `ℓ^p_{n+1}` (whose dimension
`n+1 > n` forces `sₙ(id) = 1` by the strict normalisation (S5')) through `D_σ`:

`id_{ℓ^p_{n+1}} = B ∘ D_σ ∘ A`,

with `A = padFin` the isometric embedding of the top `n+1` coordinates
(`‖A‖ ≤ 1`) and `B` the projection followed by division by the diagonal entries
(`‖B‖ ≤ ‖σ_n‖⁻¹`). The (S3) ideal property then gives
`1 = sₙ(id) ≤ ‖B‖ · sₙ(D_σ) · ‖A‖ ≤ ‖σ_n‖⁻¹ · sₙ(D_σ)`, i.e. `‖σ_n‖ ≤ sₙ(D_σ)`.
This needs (S5'), so it holds for every **strict** s-number sequence — the
approximation, Bernstein, Gelfand, and Kolmogorov numbers. -/

/-- **Lower bound.** For every *strict* s-number sequence `s` and a diagonal
non-increasing in modulus, `‖σ_n‖ ≤ sₙ(D_σ)` (`n < m`). -/
theorem le_sn_DiagCLM {s : Family 𝕜} (hs : IsStrictSNumberSequence s)
    {σ : Fin m → 𝕜} (hσ : _root_.Antitone fun i => ‖σ i‖) {n : ℕ} (hn : n < m) :
    ‖σ ⟨n, hn⟩‖ ≤ s (DiagCLM p σ) n := by
  rcases eq_or_ne ‖σ ⟨n, hn⟩‖ 0 with h0 | h0
  · rw [h0]; exact hs.nonneg _ _
  have hpos : 0 < ‖σ ⟨n, hn⟩‖ := (norm_nonneg _).lt_of_ne (Ne.symm h0)
  have hnm : n + 1 ≤ m := hn
  have : Nonempty (Fin (n + 1)) := ⟨⟨0, Nat.succ_pos n⟩⟩
  -- The top `n+1` entries dominate `‖σ_n‖`, hence are nonzero.
  have hdom : ∀ j : Fin (n + 1), ‖σ ⟨n, hn⟩‖ ≤ ‖σ (Fin.castLE hnm j)‖ := by
    intro j
    refine hσ ?_
    simp only [Fin.le_def, Fin.val_castLE]
    omega
  have hne : ∀ j : Fin (n + 1), σ (Fin.castLE hnm j) ≠ 0 := fun j hj => by
    have := hdom j; rw [hj, norm_zero] at this; exact absurd this (not_le.mpr hpos)
  -- The factorisation `id = B ∘ D_σ ∘ A`.
  set A : PiLp p (fun _ : Fin (n + 1) => 𝕜) →L[𝕜] PiLp p (fun _ : Fin m => 𝕜) :=
    padFin with hA
  set B : PiLp p (fun _ : Fin m => 𝕜) →L[𝕜] PiLp p (fun _ : Fin (n + 1) => 𝕜) :=
    (DiagCLM p fun j => (σ (Fin.castLE hnm j))⁻¹).comp (projFin hnm) with hB
  have hfact : B.comp ((DiagCLM p σ).comp A)
      = ContinuousLinearMap.id 𝕜 (PiLp p (fun _ : Fin (n + 1) => 𝕜)) := by
    ext w j
    simp only [hB, hA, ContinuousLinearMap.comp_apply, ContinuousLinearMap.id_apply,
      DiagCLM_apply, projFin_apply]
    rw [padFin_castLE, smul_smul, inv_mul_cancel₀ (hne j), one_smul]
  -- Norm bounds on the factors.
  have hAle : ‖A‖ ≤ 1 := by rw [hA]; exact norm_padFin_clm_le hnm
  have hBle : ‖B‖ ≤ ‖σ ⟨n, hn⟩‖⁻¹ := by
    rw [hB]
    calc ‖(DiagCLM p fun j => (σ (Fin.castLE hnm j))⁻¹).comp (projFin hnm)‖
        ≤ ‖DiagCLM p fun j => (σ (Fin.castLE hnm j))⁻¹‖ * ‖projFin hnm‖ :=
          ContinuousLinearMap.opNorm_comp_le _ _
      _ ≤ (⨆ j, ‖(σ (Fin.castLE hnm j))⁻¹‖) * 1 := by
          rw [norm_DiagCLM]
          exact mul_le_mul_of_nonneg_left (norm_projFin_clm_le hnm)
            (Real.iSup_nonneg fun j => norm_nonneg _)
      _ = ⨆ j, ‖(σ (Fin.castLE hnm j))⁻¹‖ := mul_one _
      _ ≤ ‖σ ⟨n, hn⟩‖⁻¹ := by
          refine ciSup_le fun j => ?_
          rw [norm_inv]
          exact inv_anti₀ hpos (hdom j)
  -- Assemble via (S3) and (S5').
  have hideal := hs.ideal A (DiagCLM p σ) B n
  rw [hfact, hs.strictly_normalised_at_id n (by rw [finrank_piLp]; omega)] at hideal
  have hsnn : 0 ≤ s (DiagCLM p σ) n := hs.nonneg _ _
  have hchain : (1 : ℝ) ≤ ‖σ ⟨n, hn⟩‖⁻¹ * s (DiagCLM p σ) n := by
    calc (1 : ℝ) ≤ ‖B‖ * s (DiagCLM p σ) n * ‖A‖ := hideal
      _ ≤ ‖σ ⟨n, hn⟩‖⁻¹ * s (DiagCLM p σ) n * 1 :=
          mul_le_mul (mul_le_mul_of_nonneg_right hBle hsnn) hAle (norm_nonneg _)
            (mul_nonneg (inv_nonneg.mpr (norm_nonneg _)) hsnn)
      _ = ‖σ ⟨n, hn⟩‖⁻¹ * s (DiagCLM p σ) n := mul_one _
  have hfinal := mul_le_mul_of_nonneg_left hchain (norm_nonneg (σ ⟨n, hn⟩))
  rwa [mul_one, ← mul_assoc, mul_inv_cancel₀ (ne_of_gt hpos), one_mul] at hfinal

/-! ## Stage 4 — the s-numbers of a diagonal operator

Combining the upper bound (Stage 2, valid for every s-number) with the lower
bound (Stage 3, valid for every *strict* s-number) gives the exact value
`sₙ(D_σ) = ‖σ_n‖` for every strict s-number sequence, hence simultaneously for
the approximation, Gelfand, Kolmogorov, and Bernstein numbers. The Hilbert
numbers, only known to satisfy (S5) (not (S5')), are merely bounded above; for
`p ≠ 2` the inequality `hₙ(D_σ) ≤ ‖σ_n‖` is strict in general. -/

/-- **Main result.** For every *strict* s-number sequence `s` and a diagonal
operator `D_σ : ℓ^p_m → ℓ^p_m` whose entries are non-increasing in modulus,
`sₙ(D_σ) = ‖σ_n‖` (the `(n+1)`-th largest entry), for `n < m`. -/
theorem sn_DiagCLM_eq {s : Family 𝕜} (hs : IsStrictSNumberSequence s)
    {σ : Fin m → 𝕜} (hσ : _root_.Antitone fun i => ‖σ i‖) {n : ℕ} (hn : n < m) :
    s (DiagCLM p σ) n = ‖σ ⟨n, hn⟩‖ :=
  le_antisymm
    ((sn_le_approximationNumber hs.toIsSNumberSequence (DiagCLM p σ) n).trans
      (approximationNumber_DiagCLM_le hσ hn))
    (le_sn_DiagCLM hs hσ hn)

/-- The approximation numbers of a diagonal operator: `aₙ(D_σ) = ‖σ_n‖`. -/
theorem approximationNumber_DiagCLM_eq {σ : Fin m → 𝕜}
    (hσ : _root_.Antitone fun i => ‖σ i‖) {n : ℕ} (hn : n < m) :
    approximationNumber (DiagCLM p σ) n = ‖σ ⟨n, hn⟩‖ :=
  le_antisymm (approximationNumber_DiagCLM_le hσ hn)
    (le_sn_DiagCLM isStrictSNumberSequence_approximationNumber hσ hn)

/-- The Gelfand numbers of a diagonal operator: `cₙ(D_σ) = ‖σ_n‖`. -/
theorem gelfandNumber_DiagCLM_eq {σ : Fin m → 𝕜}
    (hσ : _root_.Antitone fun i => ‖σ i‖) {n : ℕ} (hn : n < m) :
    gelfandNumber (DiagCLM p σ) n = ‖σ ⟨n, hn⟩‖ :=
  sn_DiagCLM_eq isStrictSNumberSequence_gelfandNumber hσ hn

/-- The Kolmogorov numbers of a diagonal operator: `dₙ(D_σ) = ‖σ_n‖`. -/
theorem kolmogorovNumber_DiagCLM_eq {σ : Fin m → 𝕜}
    (hσ : _root_.Antitone fun i => ‖σ i‖) {n : ℕ} (hn : n < m) :
    kolmogorovNumber (DiagCLM p σ) n = ‖σ ⟨n, hn⟩‖ :=
  sn_DiagCLM_eq isStrictSNumberSequence_kolmogorovNumber hσ hn

/-- The Bernstein numbers of a diagonal operator: `bₙ(D_σ) = ‖σ_n‖`. -/
theorem bernsteinNumber_DiagCLM_eq {σ : Fin m → 𝕜}
    (hσ : _root_.Antitone fun i => ‖σ i‖) {n : ℕ} (hn : n < m) :
    bernsteinNumber (DiagCLM p σ) n = ‖σ ⟨n, hn⟩‖ :=
  sn_DiagCLM_eq isStrictSNumberSequence_bernsteinNumber hσ hn

/-- The Hilbert numbers of a diagonal operator satisfy `hₙ(D_σ) ≤ ‖σ_n‖`. Unlike
the strict s-numbers above, equality can fail for `p ≠ 2`: the Hilbert numbers
measure the Hilbertian part of `ℓ^p`, which is genuinely smaller. -/
theorem hilbertNumber_DiagCLM_le {σ : Fin m → 𝕜}
    (hσ : _root_.Antitone fun i => ‖σ i‖) {n : ℕ} (hn : n < m) :
    hilbertNumber (DiagCLM p σ) n ≤ ‖σ ⟨n, hn⟩‖ :=
  (sn_le_approximationNumber isSNumberSequence_hilbertNumber (DiagCLM p σ) n).trans
    (approximationNumber_DiagCLM_le hσ hn)

/-! ## The unit diagonal (identity operator)

The simplest case `σ ≡ 1` is the identity `id : ℓ^p_m → ℓ^p_m`. Here no norm
machinery is needed: `sₙ(id) = 1` for `n < m` is exactly the strict
normalisation (S5'), and `sₙ(id) = 0` for `n ≥ m` is the rank axiom (S4). -/

/-- The unit diagonal is the identity operator. -/
@[simp] lemma DiagCLM_one :
    DiagCLM p (fun _ : Fin m => (1 : 𝕜)) = ContinuousLinearMap.id 𝕜 (PiLp p (fun _ : Fin m =>
        𝕜)) := by
  ext x i; simp

/-- For every strict s-number sequence, the identity on `ℓ^p_m` has `sₙ(id) = 1`
whenever `n < m` (directly from (S5'), via `dim ℓ^p_m = m`). -/
theorem sn_id_piLp {s : Family 𝕜} (hs : IsStrictSNumberSequence s) {n : ℕ} (hn : n < m) :
    s (ContinuousLinearMap.id 𝕜 (PiLp p (fun _ : Fin m => 𝕜))) n = 1 :=
  hs.strictly_normalised_at_id n (by rw [finrank_piLp]; exact hn)


/-! # Part II — mixed exponents: `D_σ : ℓ^q_m → ℓ^p_m`

Everything above keeps the *same* exponent on both sides. We now allow the
domain and codomain exponents to differ, which is where the theory becomes
genuinely richer: the approximation numbers are an `ℓ^r`-norm of the tail of the
diagonal, for the conjugate exponent `1/r = 1/p − 1/q`.
-/

section MixedExponent

variable {q : ℝ≥0∞} [Fact (1 ≤ q)]
/-! ## The operator and its identifications -/

/-- The **mixed-exponent diagonal operator** `D_σ : ℓ^q_m → ℓ^p_m`,
`x ↦ (σ_i · x_i)`, as a continuous linear map. The domain is finite-dimensional,
so continuity is automatic. Specialises to `DiagCLM p σ` when `q = p`
(`DiagCLMpq_self`) and to the identity embedding `idEmbed p q` when `σ ≡ 1`
(`DiagCLMpq_one`). -/
noncomputable def DiagCLMpq (p q : ℝ≥0∞) [Fact (1 ≤ p)] [Fact (1 ≤ q)] (σ : Fin m → 𝕜) :
    PiLp q (fun _ : Fin m => 𝕜) →L[𝕜] PiLp p (fun _ : Fin m => 𝕜) :=
  LinearMap.toContinuousLinearMap
    { toFun := fun x => WithLp.toLp p (fun i => σ i • x i)
      map_add' := fun x y => by ext i; simp [mul_add]
      map_smul' := fun c x => by ext i; simp [mul_left_comm] }

@[simp] lemma DiagCLMpq_apply (σ : Fin m → 𝕜) (x : PiLp q (fun _ : Fin m => 𝕜)) (i : Fin m) :
    (DiagCLMpq p q σ x) i = σ i • x i := rfl

/-- When the two exponents agree, the mixed-exponent diagonal operator is the
same-exponent diagonal operator `DiagCLM`. -/
@[simp] lemma DiagCLMpq_self (σ : Fin m → 𝕜) : DiagCLMpq p p σ = DiagCLM p σ := by
  ext x i; simp

/-- With unit diagonal the mixed-exponent diagonal operator is the identity
embedding `idEmbed`. -/
@[simp] lemma DiagCLMpq_one : DiagCLMpq p q (fun _ : Fin m => (1 : 𝕜)) = idEmbed p q := by
  ext x i; simp

/-! ## The conjugate exponent `r`

The value `aₙ(D_σ)` is an `ℓ^r`-norm for the exponent `r` determined by
`1/r = 1/p − 1/q`. We work throughout with `1 ≤ p < q < ∞`, so `r` is a finite
positive real. -/

/-- The **conjugate exponent** `r` of the pair `(p, q)`, determined by
`1/r = 1/p − 1/q`; equivalently `r = pq/(q−p)`. -/
noncomputable def diagExp (p q : ℝ≥0∞) : ℝ := (1 / p.toReal - 1 / q.toReal)⁻¹

/-- `r⁻¹ = 1/p − 1/q`, unconditionally (it is the definition, up to `inv_inv`). -/
lemma diagExp_inv (p q : ℝ≥0∞) : (diagExp p q)⁻¹ = 1 / p.toReal - 1 / q.toReal :=
  inv_inv _

omit [Fact (1 ≤ p)] [Fact (1 ≤ q)] in
/-- For `p < q < ∞`, `p` is finite. -/
private lemma p_ne_top (hpq : p < q) (hq : q ≠ ∞) : p ≠ ∞ := ne_top_of_le_ne_top hq hpq.le

omit [Fact (1 ≤ p)] [Fact (1 ≤ q)] in
/-- The real parts are strictly ordered: `p.toReal < q.toReal`. -/
private lemma toReal_lt (hpq : p < q) (hq : q ≠ ∞) : p.toReal < q.toReal :=
  (ENNReal.toReal_lt_toReal (p_ne_top hpq hq) hq).mpr hpq

omit [Fact (1 ≤ q)] in
/-- `1/p − 1/q > 0` (real parts), the reciprocal of which is `r`. -/
private lemma one_div_sub_pos (hpq : p < q) (hq : q ≠ ∞) :
    0 < 1 / p.toReal - 1 / q.toReal := by
  have hP : 0 < p.toReal := toReal_pos_of_ne_top (p_ne_top hpq hq)
  have hPQ : p.toReal < q.toReal := toReal_lt hpq hq
  exact sub_pos.mpr (one_div_lt_one_div_of_lt hP hPQ)

omit [Fact (1 ≤ q)] in
/-- `r > 0`. -/
private lemma diagExp_pos (hpq : p < q) (hq : q ≠ ∞) : 0 < diagExp p q :=
  inv_pos.mpr (one_div_sub_pos hpq hq)

/-- The Hölder triple `(r, q, p)`: `r⁻¹ + q⁻¹ = p⁻¹`, with `r, q > 0`. This is
the shape consumed by `Real.Lr_rpow_le_Lp_mul_Lq_of_nonneg`. -/
private lemma holderTriple_diagExp (hpq : p < q) (hq : q ≠ ∞) :
    (diagExp p q).HolderTriple q.toReal p.toReal where
  inv_add_inv_eq_inv := by rw [diagExp_inv]; ring
  left_pos := diagExp_pos hpq hq
  right_pos := toReal_pos_of_ne_top hq

/-- The closed form `r = pq/(q−p)`. -/
private lemma diagExp_eq (hpq : p < q) (hq : q ≠ ∞) :
    diagExp p q = p.toReal * q.toReal / (q.toReal - p.toReal) := by
  have hP : (0 : ℝ) < p.toReal := toReal_pos_of_ne_top (p_ne_top hpq hq)
  have hQ : (0 : ℝ) < q.toReal := toReal_pos_of_ne_top hq
  rw [diagExp, div_sub_div _ _ hP.ne' hQ.ne', one_mul, mul_one, inv_div]

/-- The defining product identity `r·(q−p) = p·q`, the source of `hexp1`/`hexp2`. -/
private lemma diagExp_mul (hpq : p < q) (hq : q ≠ ∞) :
    diagExp p q * (q.toReal - p.toReal) = p.toReal * q.toReal := by
  have hPQ : p.toReal < q.toReal := toReal_lt hpq hq
  rw [diagExp_eq hpq hq, div_mul_cancel₀ _ (sub_ne_zero.mpr hPQ.ne')]

/-- `(1 + r/q)·p = r` (drives the numerator equality in the ratio lemma). -/
private lemma diagExp_hexp1 (hpq : p < q) (hq : q ≠ ∞) :
    (1 + diagExp p q / q.toReal) * p.toReal = diagExp p q := by
  have hQ : (0 : ℝ) < q.toReal := toReal_pos_of_ne_top hq
  have hPQ : p.toReal < q.toReal := toReal_lt hpq hq
  have hQP : q.toReal - p.toReal ≠ 0 := sub_ne_zero.mpr hPQ.ne'
  rw [diagExp_eq hpq hq]
  field_simp
  ring

/-- `(r/q)·(q−p) = p` (drives the exponent bound in the ratio lemma). -/
private lemma diagExp_hexp2 (hpq : p < q) (hq : q ≠ ∞) :
    diagExp p q / q.toReal * (q.toReal - p.toReal) = p.toReal := by
  have hQ : (0 : ℝ) < q.toReal := toReal_pos_of_ne_top hq
  have hPQ : p.toReal < q.toReal := toReal_lt hpq hq
  have hQP : q.toReal - p.toReal ≠ 0 := sub_ne_zero.mpr hPQ.ne'
  rw [diagExp_eq hpq hq]
  field_simp

/-- The reciprocal relation `1/r + 1/q = 1/p`. -/
private lemma diagExp_inv_add (hpq : p < q) (hq : q ≠ ∞) :
    1 / diagExp p q + 1 / q.toReal = 1 / p.toReal := by
  simpa only [one_div] using (holderTriple_diagExp hpq hq).inv_add_inv_eq_inv

/-! ## The operator norm via Hölder's inequality

The `L^p`/`L^q` mixed norm of `D_σ` is the `ℓ^r`-norm of the diagonal,
`‖D_σ‖ = (∑ ‖σ_i‖^r)^{1/r}`. The upper bound is Hölder's inequality with the
triple `(r, q, p)`; the lower bound tests `D_σ` on the extremal diagonal
vector `x_i = ‖σ_i‖^{r/q}`. -/

/-- **Pointwise Hölder bound.** `‖D_σ x‖ ≤ (∑ ‖σ_i‖^r)^{1/r} · ‖x‖`. -/
theorem norm_DiagCLMpq_apply_le (hpq : p < q) (hq : q ≠ ∞) (σ : Fin m → 𝕜)
    (x : PiLp q (fun _ : Fin m => 𝕜)) :
    ‖DiagCLMpq p q σ x‖
      ≤ (∑ i, ‖σ i‖ ^ diagExp p q) ^ (1 / diagExp p q) * ‖x‖ := by
  have hpf : p ≠ ∞ := p_ne_top hpq hq
  have hP : 0 < p.toReal := toReal_pos_of_ne_top hpf
  have hQ : 0 < q.toReal := toReal_pos_of_ne_top hq
  have hR : 0 < diagExp p q := diagExp_pos hpq hq
  have hPne : p.toReal ≠ 0 := hP.ne'
  have hQne : q.toReal ≠ 0 := hQ.ne'
  have hRne : diagExp p q ≠ 0 := hR.ne'
  rw [PiLp.norm_eq_sum hP, PiLp.norm_eq_sum hQ]
  -- Rewrite the codomain sum `∑ ‖σ_i • x_i‖^p = ∑ (‖σ_i‖·‖x_i‖)^p`.
  have hlhs : ∑ i, ‖(DiagCLMpq p q σ x) i‖ ^ p.toReal
      = ∑ i, (‖σ i‖ * ‖x i‖) ^ p.toReal :=
    Finset.sum_congr rfl fun i _ => by rw [DiagCLMpq_apply, norm_smul]
  rw [hlhs]
  -- Nonnegativity of the two `L^r` / `L^q` sums.
  have hSσ : 0 ≤ ∑ i, ‖σ i‖ ^ diagExp p q :=
    Finset.sum_nonneg fun i _ => Real.rpow_nonneg (norm_nonneg _) _
  have hSx : 0 ≤ ∑ i, ‖x i‖ ^ q.toReal :=
    Finset.sum_nonneg fun i _ => Real.rpow_nonneg (norm_nonneg _) _
  -- Hölder for the triple `(r, q, p)`.
  have hhold := Real.Lr_rpow_le_Lp_mul_Lq_of_nonneg Finset.univ
    (holderTriple_diagExp hpq hq) (f := fun i => ‖σ i‖) (g := fun i => ‖x i‖)
    (fun i _ => norm_nonneg _) (fun i _ => norm_nonneg _)
  have hTnn : 0 ≤ ∑ i, (‖σ i‖ * ‖x i‖) ^ p.toReal :=
    Finset.sum_nonneg fun i _ => Real.rpow_nonneg (mul_nonneg (norm_nonneg _) (norm_nonneg _)) _
  have h2 := Real.rpow_le_rpow hTnn hhold (by positivity : (0 : ℝ) ≤ 1 / p.toReal)
  rw [Real.mul_rpow (Real.rpow_nonneg hSσ _) (Real.rpow_nonneg hSx _),
    ← Real.rpow_mul hSσ, ← Real.rpow_mul hSx] at h2
  have e1 : p.toReal / diagExp p q * (1 / p.toReal) = 1 / diagExp p q := by
    field_simp
  have e2 : p.toReal / q.toReal * (1 / p.toReal) = 1 / q.toReal := by
    field_simp
  rwa [e1, e2] at h2

/-- **Operator-norm upper bound.** `‖D_σ‖ ≤ (∑ ‖σ_i‖^r)^{1/r}`. -/
theorem norm_DiagCLMpq_le (hpq : p < q) (hq : q ≠ ∞) (σ : Fin m → 𝕜) :
    ‖DiagCLMpq p q σ‖ ≤ (∑ i, ‖σ i‖ ^ diagExp p q) ^ (1 / diagExp p q) :=
  opNorm_le_bound _
    (Real.rpow_nonneg (Finset.sum_nonneg fun _ _ => Real.rpow_nonneg (norm_nonneg _) _) _)
    (norm_DiagCLMpq_apply_le hpq hq σ)

/-! ## The tail value -/

/-- The **tail value** `(∑_{k=n}^{m-1} ‖σ_k‖^r)^{1/r}`, the `ℓ^r`-norm of the
diagonal restricted to the `m − n` largest indices. This is the value of
`aₙ(D_σ)` (Theorem `approximationNumber_DiagCLMpq_eq`). -/
noncomputable def diagTail (p q : ℝ≥0∞) (σ : Fin m → 𝕜) (n : ℕ) : ℝ :=
  (∑ i ∈ Finset.univ.filter (fun i : Fin m => n ≤ (i : ℕ)), ‖σ i‖ ^ diagExp p q) ^
    (1 / diagExp p q)

/-! ## Upper bound for the approximation numbers

Truncating `D_σ` to its top `n` coordinates gives a rank-`≤ n` approximant; the
residual is the diagonal on the remaining `m − n` coordinates, of `ℓ^r`-norm
`diagTail`. As the approximation numbers are the largest s-numbers, the bound
holds for every s-number. -/

/-- **Upper bound.** The `n`-th approximation number of `D_σ : ℓ^q_m → ℓ^p_m`
is at most the tail value `(∑_{k≥n} ‖σ_k‖^r)^{1/r}` (`n ≤ m`). -/
theorem approximationNumber_DiagCLMpq_le (hpq : p < q) (hq : q ≠ ∞) (σ : Fin m → 𝕜)
    {n : ℕ} (hn : n ≤ m) :
    approximationNumber (DiagCLMpq p q σ) n ≤ diagTail p q σ n := by
  have hR : 0 < diagExp p q := diagExp_pos hpq hq
  -- The rank-`≤ n` approximant `L = (D_σ ∘ padFin) ∘ id_{ℓ^q_n} ∘ projFin`.
  set A : PiLp q (fun _ : Fin m => 𝕜) →L[𝕜] PiLp q (fun _ : Fin n => 𝕜) :=
    projFin hn with hA
  set B : PiLp q (fun _ : Fin n => 𝕜) →L[𝕜] PiLp p (fun _ : Fin m => 𝕜) :=
    (DiagCLMpq p q σ).comp padFin with hB
  set L := B.comp ((ContinuousLinearMap.id 𝕜 (PiLp q (fun _ : Fin n => 𝕜))).comp A) with hL
  -- The residual diagonal `ρ`: entries from index `n` on.
  set ρ : Fin m → 𝕜 := fun i => if (i : ℕ) < n then 0 else σ i with hρ
  have hLrank : L.rank ≤ (n : Cardinal) :=
    (ContinuousLinearMap.rank_comp_comp_le A _ B).trans_eq (rank_id_piLp n)
  -- `D_σ − L = D_ρ`.
  have hres : DiagCLMpq p q σ - L = DiagCLMpq p q ρ := by
    ext x i
    simp only [hL, hA, hB, sub_apply, ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.id_apply, DiagCLMpq_apply, PiLp.sub_apply]
    rw [padFin_projFin_apply]
    by_cases hi : (i : ℕ) < n <;> simp [hρ, hi]
  -- The residual `ℓ^r`-sum is the tail sum.
  have hsum : ∑ i, ‖ρ i‖ ^ diagExp p q
      = ∑ i ∈ Finset.univ.filter (fun i : Fin m => n ≤ (i : ℕ)), ‖σ i‖ ^ diagExp p q := by
    rw [← Finset.sum_filter_add_sum_filter_not Finset.univ (fun i : Fin m => n ≤ (i : ℕ))
        (fun i => ‖ρ i‖ ^ diagExp p q)]
    have h1 : ∑ i ∈ Finset.univ.filter (fun i : Fin m => n ≤ (i : ℕ)), ‖ρ i‖ ^ diagExp p q
        = ∑ i ∈ Finset.univ.filter (fun i : Fin m => n ≤ (i : ℕ)), ‖σ i‖ ^ diagExp p q := by
      refine Finset.sum_congr rfl fun i hi => ?_
      rw [Finset.mem_filter] at hi
      simp only [hρ, ite_eq_right (not_lt.mpr hi.2)]
    have h2 : ∑ i ∈ Finset.univ.filter (fun i : Fin m => ¬ n ≤ (i : ℕ)), ‖ρ i‖ ^ diagExp p q =
        0 := by
      refine Finset.sum_eq_zero fun i hi => ?_
      rw [Finset.mem_filter, not_le] at hi
      simp only [hρ, ite_eq_left hi.2, norm_zero, Real.zero_rpow hR.ne']
    rw [h1, h2, add_zero]
  calc approximationNumber (DiagCLMpq p q σ) n
      ≤ ‖DiagCLMpq p q σ - L‖ := approximationNumber_le_norm_sub hLrank
    _ = ‖DiagCLMpq p q ρ‖ := by rw [hres]
    _ ≤ (∑ i, ‖ρ i‖ ^ diagExp p q) ^ (1 / diagExp p q) := norm_DiagCLMpq_le hpq hq ρ
    _ = diagTail p q σ n := by rw [diagTail, hsum]

/-! ## Lower bound — the weighted flat vector

For any rank-`≤ n` operator `L`, its kernel has dimension `≥ m − n`, and
`(D_σ − L)` agrees with `D_σ` there. We must produce, in any subspace of
dimension `≥ m − n`, a vector `x` with `‖D_σ x‖_p ≥ diagTail · ‖x‖_q`. The
argument is the classical Gelfand-width construction adapted to the weight
`w_i = ‖σ_i‖^{r/q}`, using the weighted flatness lemma
`exists_flat_vector_weighted` of `SNumbers.Examples.ExHelpers` (an extreme-point
argument, built on a coordinate pigeonhole). -/

/-! ## Lower bound — the weighted ratio inequality

For the weight `w_i = ‖σ_i‖^{r/q}`, a vector `x` bounded by `w` and saturating
it on a set `S` has `‖D_σ x‖_p ≥ (∑_{i∈S} ‖σ_i‖^r)^{1/r} · ‖x‖_q`. With
`T := ∑ (‖σ_i‖·‖x_i‖)^p = ‖D_σ x‖_p^p`: on `S` each `(‖σ_i‖·w_i)^p = ‖σ_i‖^r`
(so `∑_{i∈S} ‖σ_i‖^r ≤ T`), and pointwise `‖x_i‖^q ≤ (‖σ_i‖·‖x_i‖)^p`
(so `‖x‖_q^q ≤ T`); combining with `1/r + 1/q = 1/p` gives the claim. -/

/-- **Weighted ratio inequality.** With weight `w_i = ‖σ_i‖^{r/q}`, if `x` is
bounded by `w` everywhere and saturates it on `S`, then
`(∑_{i∈S} ‖σ_i‖^r)^{1/r} · ‖x‖_q ≤ ‖D_σ x‖_p`. -/
private lemma norm_ratio_of_flat_weighted (hpq : p < q) (hq : q ≠ ∞) (σ x : Fin m → 𝕜)
    (hle : ∀ i, ‖x i‖ ≤ ‖σ i‖ ^ (diagExp p q / q.toReal))
    {S : Finset (Fin m)}
    (hS : ∀ i ∈ S, ‖x i‖ = ‖σ i‖ ^ (diagExp p q / q.toReal)) :
    (∑ i ∈ S, ‖σ i‖ ^ diagExp p q) ^ (1 / diagExp p q)
        * ‖(WithLp.toLp q x : PiLp q (fun _ : Fin m => 𝕜))‖
      ≤ ‖DiagCLMpq p q σ (WithLp.toLp q x)‖ := by
  have hpf : p ≠ ∞ := p_ne_top hpq hq
  have hP : 0 < p.toReal := toReal_pos_of_ne_top hpf
  have hQ : 0 < q.toReal := toReal_pos_of_ne_top hq
  have hR : 0 < diagExp p q := diagExp_pos hpq hq
  have hPQ : p.toReal < q.toReal := toReal_lt hpq hq
  -- The three relevant norms.
  have hnormD : ‖DiagCLMpq p q σ (WithLp.toLp q x)‖
      = (∑ i, (‖σ i‖ * ‖x i‖) ^ p.toReal) ^ (1 / p.toReal) := by
    rw [PiLp.norm_eq_sum hP]
    congr 1
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [show (DiagCLMpq p q σ (WithLp.toLp q x)) i = σ i • x i from rfl, norm_smul]
  have hnormx : ‖(WithLp.toLp q x : PiLp q (fun _ : Fin m => 𝕜))‖
      = (∑ i, ‖x i‖ ^ q.toReal) ^ (1 / q.toReal) := by
    rw [PiLp.norm_eq_sum hQ]
  set T : ℝ := ∑ i, (‖σ i‖ * ‖x i‖) ^ p.toReal with hTdef
  have hTnn : 0 ≤ T :=
    Finset.sum_nonneg fun i _ => Real.rpow_nonneg (mul_nonneg (norm_nonneg _) (norm_nonneg _)) _
  -- Claim (i): the `S`-sum of `‖σ_i‖^r` is at most `T`.
  have hterm1 : ∀ i ∈ S, (‖σ i‖ * ‖x i‖) ^ p.toReal = ‖σ i‖ ^ diagExp p q := by
    intro i hi
    rw [hS i hi]
    rcases eq_or_ne ‖σ i‖ 0 with h0 | h0
    · rw [h0, zero_mul, Real.zero_rpow hP.ne']
      exact (Real.zero_rpow hR.ne').symm
    · have hpos : 0 < ‖σ i‖ := (norm_nonneg _).lt_of_ne (Ne.symm h0)
      have hmul : ‖σ i‖ * ‖σ i‖ ^ (diagExp p q / q.toReal)
          = ‖σ i‖ ^ (1 + diagExp p q / q.toReal) := by
        rw [Real.rpow_add hpos, Real.rpow_one]
      rw [hmul, ← Real.rpow_mul (norm_nonneg _), diagExp_hexp1 hpq hq]
  have claim_i : ∑ i ∈ S, ‖σ i‖ ^ diagExp p q ≤ T := by
    calc ∑ i ∈ S, ‖σ i‖ ^ diagExp p q
        = ∑ i ∈ S, (‖σ i‖ * ‖x i‖) ^ p.toReal :=
          (Finset.sum_congr rfl hterm1).symm
      _ ≤ ∑ i, (‖σ i‖ * ‖x i‖) ^ p.toReal :=
          Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
            (fun i _ _ => Real.rpow_nonneg (mul_nonneg (norm_nonneg _) (norm_nonneg _)) _)
  -- Claim (ii): `∑ ‖x_i‖^q ≤ T` pointwise.
  have hterm2 : ∀ i, ‖x i‖ ^ q.toReal ≤ (‖σ i‖ * ‖x i‖) ^ p.toReal := by
    intro i
    rcases eq_or_ne ‖x i‖ 0 with h0 | h0
    · rw [h0, Real.zero_rpow hQ.ne']
      positivity
    · have hxpos : 0 < ‖x i‖ := (norm_nonneg _).lt_of_ne (Ne.symm h0)
      have hbase : ‖x i‖ ^ (q.toReal - p.toReal) ≤ ‖σ i‖ ^ p.toReal := by
        calc ‖x i‖ ^ (q.toReal - p.toReal)
            ≤ (‖σ i‖ ^ (diagExp p q / q.toReal)) ^ (q.toReal - p.toReal) :=
              Real.rpow_le_rpow (norm_nonneg _) (hle i) (by linarith)
          _ = ‖σ i‖ ^ p.toReal := by
              rw [← Real.rpow_mul (norm_nonneg _), diagExp_hexp2 hpq hq]
      calc ‖x i‖ ^ q.toReal
          = ‖x i‖ ^ (q.toReal - p.toReal) * ‖x i‖ ^ p.toReal := by
            rw [← Real.rpow_add hxpos]; congr 1; ring
        _ ≤ ‖σ i‖ ^ p.toReal * ‖x i‖ ^ p.toReal :=
            mul_le_mul_of_nonneg_right hbase (Real.rpow_nonneg (norm_nonneg _) _)
        _ = (‖σ i‖ * ‖x i‖) ^ p.toReal := (Real.mul_rpow (norm_nonneg _) (norm_nonneg _)).symm
  have claim_ii : ∑ i, ‖x i‖ ^ q.toReal ≤ T := Finset.sum_le_sum fun i _ => hterm2 i
  -- Combine.
  rw [hnormD, hnormx]
  have hSσnn : 0 ≤ ∑ i ∈ S, ‖σ i‖ ^ diagExp p q :=
    Finset.sum_nonneg fun _ _ => Real.rpow_nonneg (norm_nonneg _) _
  have hxQnn : 0 ≤ ∑ i, ‖x i‖ ^ q.toReal :=
    Finset.sum_nonneg fun _ _ => Real.rpow_nonneg (norm_nonneg _) _
  have hcR : (∑ i ∈ S, ‖σ i‖ ^ diagExp p q) ^ (1 / diagExp p q) ≤ T ^ (1 / diagExp p q) :=
    Real.rpow_le_rpow hSσnn claim_i (by positivity)
  have hxq : (∑ i, ‖x i‖ ^ q.toReal) ^ (1 / q.toReal) ≤ T ^ (1 / q.toReal) :=
    Real.rpow_le_rpow hxQnn claim_ii (by positivity)
  calc (∑ i ∈ S, ‖σ i‖ ^ diagExp p q) ^ (1 / diagExp p q)
          * (∑ i, ‖x i‖ ^ q.toReal) ^ (1 / q.toReal)
      ≤ T ^ (1 / diagExp p q) * T ^ (1 / q.toReal) :=
        mul_le_mul hcR hxq (Real.rpow_nonneg hxQnn _) (Real.rpow_nonneg hTnn _)
    _ = T ^ (1 / p.toReal) := by
        rcases eq_or_lt_of_le hTnn with hT0 | hTpos
        · rw [← hT0, Real.zero_rpow (one_div_ne_zero hR.ne'),
            Real.zero_rpow (one_div_ne_zero hQ.ne'),
            Real.zero_rpow (one_div_ne_zero hP.ne'), mul_zero]
        · rw [← Real.rpow_add hTpos, diagExp_inv_add hpq hq]

/-! ## Lower bound — minimality of the tail

Because `‖σ_i‖^r` is antitone in `i`, the tail `{i : n ≤ i}` carries the `m − n`
smallest values, so any coordinate set `S` of size `≥ m − n` has a larger
`ℓ^r`-sum. This selects the tail as the minimizer feeding the lower bound. -/

omit [Fact (1 ≤ q)] in
/-- **Selection inequality.** For `‖σ_i‖^r` antitone, the tail sum is dominated by
the sum over any `S` with `|S| ≥ m − n`. -/
private lemma tail_sum_le_sum_of_card_ge (hpq : p < q) (hq : q ≠ ∞) (σ : Fin m → 𝕜)
    (hσ : _root_.Antitone fun i => ‖σ i‖) {n : ℕ} (hn : n ≤ m)
    {S : Finset (Fin m)} (hScard : m - n ≤ S.card) :
    ∑ i ∈ Finset.univ.filter (fun i : Fin m => n ≤ (i : ℕ)), ‖σ i‖ ^ diagExp p q
      ≤ ∑ i ∈ S, ‖σ i‖ ^ diagExp p q := by
  classical
  have hR : 0 < diagExp p q := diagExp_pos hpq hq
  set f : Fin m → ℝ := fun i => ‖σ i‖ ^ diagExp p q with hf
  set tail : Finset (Fin m) := Finset.univ.filter (fun i : Fin m => n ≤ (i : ℕ)) with htail
  have hfanti : ∀ {a b : Fin m}, a ≤ b → f b ≤ f a := fun {a b} hab =>
    Real.rpow_le_rpow (norm_nonneg _) (hσ hab) hR.le
  have hfnn : ∀ i, 0 ≤ f i := fun i => Real.rpow_nonneg (norm_nonneg _) _
  -- Every `f`-value on `tail \ S` is dominated by every `f`-value on `S \ tail`.
  have hdom : ∀ b ∈ tail \ S, ∀ a ∈ S \ tail, f b ≤ f a := by
    intro b hb a ha
    simp only [Finset.mem_sdiff, htail, Finset.mem_filter, Finset.mem_univ, true_and] at hb ha
    obtain ⟨hbn, -⟩ := hb
    obtain ⟨-, han⟩ := ha
    exact hfanti (by rw [Fin.le_def]; omega)
  -- Cardinality count: `tail` has `m − n` elements, so `|tail \ S| ≤ |S \ tail|`.
  have hlt : (Finset.univ.filter (fun i : Fin m => (i : ℕ) < n)).card = n := by
    rw [show (Finset.univ.filter (fun i : Fin m => (i : ℕ) < n))
          = Finset.univ.image (Fin.castLE hn) from ?_,
      Finset.card_image_of_injective _ (Fin.castLE_injective hn), Finset.card_univ,
      Fintype.card_fin]
    ext i
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image]
    constructor
    · intro hi; exact ⟨⟨(i : ℕ), hi⟩, by simp⟩
    · rintro ⟨j, rfl⟩; simp only [Fin.val_castLE]; exact j.isLt
  have hcard_tail : tail.card = m - n := by
    have heq : tail = (Finset.univ.filter (fun i : Fin m => (i : ℕ) < n))ᶜ := by
      ext i; simp [htail, Finset.mem_filter, not_lt]
    rw [heq, Finset.card_compl, Fintype.card_fin, hlt]
  have hcard_le : (tail \ S).card ≤ (S \ tail).card := by
    have h1 : (tail \ S).card + (tail ∩ S).card = tail.card :=
      Finset.card_sdiff_add_card_inter tail S
    have h2 : (S \ tail).card + (S ∩ tail).card = S.card :=
      Finset.card_sdiff_add_card_inter S tail
    rw [Finset.inter_comm] at h1
    omega
  -- The domination sum inequality via a common threshold `M`.
  have key : ∑ i ∈ tail \ S, f i ≤ ∑ i ∈ S \ tail, f i := by
    rcases (tail \ S).eq_empty_or_nonempty with he | hne
    · rw [he, Finset.sum_empty]; exact Finset.sum_nonneg fun i _ => hfnn i
    · obtain ⟨a0, ha0⟩ := hne
      set M : ℝ := (tail \ S).sup' ⟨a0, ha0⟩ f with hM
      have hMnn : 0 ≤ M := le_trans (hfnn a0) (Finset.le_sup' f ha0)
      calc ∑ i ∈ tail \ S, f i
          ≤ (tail \ S).card • M := Finset.sum_le_card_nsmul _ _ _ fun i hi => Finset.le_sup' f hi
        _ = ((tail \ S).card : ℝ) * M := nsmul_eq_mul _ _
        _ ≤ ((S \ tail).card : ℝ) * M := mul_le_mul_of_nonneg_right (Nat.cast_le.mpr hcard_le) hMnn
        _ = (S \ tail).card • M := (nsmul_eq_mul _ _).symm
        _ ≤ ∑ i ∈ S \ tail, f i :=
            Finset.card_nsmul_le_sum _ _ _ fun a ha =>
              Finset.sup'_le ⟨a0, ha0⟩ f fun b hb => hdom b hb a ha
  -- Assemble via `∑_A = ∑_{A∩B} + ∑_{A\B}`.
  have htails : ∑ i ∈ tail, f i = ∑ i ∈ tail ∩ S, f i + ∑ i ∈ tail \ S, f i :=
    (Finset.sum_inter_add_sum_sdiff tail S f).symm
  have hSs : ∑ i ∈ S, f i = ∑ i ∈ S ∩ tail, f i + ∑ i ∈ S \ tail, f i :=
    (Finset.sum_inter_add_sum_sdiff S tail f).symm
  rw [Finset.inter_comm S tail] at hSs
  rw [htails, hSs]
  linarith [key]

/-! ## Lower bound — the geometric input -/

/-- **Geometric input.** Every subspace `V ⊆ ℓ^q_m` of dimension `≥ m − n`
contains a nonzero `x` with `diagTail · ‖x‖ ≤ ‖D_σ x‖`. When the tail vanishes
the bound is trivial for any nonzero `x`; otherwise the weighted flat vector
from `exists_flat_vector_weighted` works, and it is nonzero because its saturated
set cannot lie inside `{i : σ_i = 0}` (that would force `diagTail = 0`). -/
lemma exists_norm_ratio_ge_DiagCLMpq (hpq : p < q) (hq : q ≠ ∞) (σ : Fin m → 𝕜)
    (hσ : _root_.Antitone fun i => ‖σ i‖) {n : ℕ} (hn : n < m)
    (V : Submodule 𝕜 (PiLp q (fun _ : Fin m => 𝕜)))
    (hV : m - n ≤ Module.finrank 𝕜 V) :
    ∃ x ∈ V, x ≠ 0 ∧ diagTail p q σ n * ‖x‖ ≤ ‖DiagCLMpq p q σ x‖ := by
  have hR : 0 < diagExp p q := diagExp_pos hpq hq
  rcases eq_or_ne (diagTail p q σ n) 0 with htail0 | htailne
  · -- Vanishing tail: any nonzero vector of `V` works.
    have hVne : V ≠ ⊥ := fun h => by rw [h, finrank_bot] at hV; omega
    obtain ⟨x, hxV, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hVne
    exact ⟨x, hxV, hx0, by rw [htail0, zero_mul]; exact norm_nonneg _⟩
  · -- Positive tail: use the weighted flat vector.
    set e : PiLp q (fun _ : Fin m => 𝕜) ≃ₗ[𝕜] (Fin m → 𝕜) :=
      WithLp.linearEquiv q 𝕜 (Fin m → 𝕜) with he
    have hkV' : m - n ≤
        Module.finrank 𝕜 (V.map (e : PiLp q (fun _ : Fin m => 𝕜) →ₗ[𝕜] (Fin m → 𝕜))) :=
      le_of_le_of_eq hV (LinearEquiv.finrank_map_eq e V).symm
    obtain ⟨z, hzV', hzle, hzcard⟩ := exists_flat_vector_weighted (k := m - n)
      (fun i => ‖σ i‖ ^ (diagExp p q / q.toReal))
      (fun i => Real.rpow_nonneg (norm_nonneg _) _) hkV'
    obtain ⟨v, hvV, hev⟩ := Submodule.mem_map.mp hzV'
    have hxV : e.symm z ∈ V := by rw [← hev]; simpa using hvV
    set S : Finset (Fin m) :=
      Finset.univ.filter (fun i => ‖z i‖ = ‖σ i‖ ^ (diagExp p q / q.toReal)) with hSdef
    have hScard : m - n ≤ S.card := hzcard
    -- The flat vector is nonzero (else its saturated set forces `diagTail = 0`).
    have hzne : z ≠ 0 := by
      intro hz0
      apply htailne
      have hZcard : m - n ≤ (Finset.univ.filter (fun i => ‖σ i‖ = 0)).card := by
        refine le_trans hScard (Finset.card_le_card fun i hi => ?_)
        rw [hSdef, Finset.mem_filter] at hi
        rw [Finset.mem_filter]
        refine ⟨hi.1, ?_⟩
        have hzero : ‖σ i‖ ^ (diagExp p q / q.toReal) = 0 := by rw [← hi.2, hz0]; simp
        exact ((Real.rpow_eq_zero_iff_of_nonneg (norm_nonneg _)).mp hzero).1
      have hsel := tail_sum_le_sum_of_card_ge hpq hq σ hσ hn.le hZcard
      have hZsum : ∑ i ∈ Finset.univ.filter (fun i => ‖σ i‖ = 0), ‖σ i‖ ^ diagExp p q = 0 :=
        Finset.sum_eq_zero fun i hi => by
          rw [Finset.mem_filter] at hi; rw [hi.2, Real.zero_rpow hR.ne']
      have htailnn : 0 ≤ ∑ i ∈ Finset.univ.filter (fun i : Fin m => n ≤ (i : ℕ)),
          ‖σ i‖ ^ diagExp p q :=
        Finset.sum_nonneg fun _ _ => Real.rpow_nonneg (norm_nonneg _) _
      have heq0 : ∑ i ∈ Finset.univ.filter (fun i : Fin m => n ≤ (i : ℕ)),
          ‖σ i‖ ^ diagExp p q = 0 := le_antisymm (hZsum ▸ hsel) htailnn
      rw [diagTail, heq0, Real.zero_rpow (one_div_ne_zero hR.ne')]
    have hxne : e.symm z ≠ 0 := fun h0 => hzne (by simpa using congrArg e h0)
    refine ⟨e.symm z, hxV, hxne, ?_⟩
    have hratio := norm_ratio_of_flat_weighted hpq hq σ z hzle (S := S)
      (fun i hi => by rw [hSdef, Finset.mem_filter] at hi; exact hi.2)
    have hdiagle : diagTail p q σ n
        ≤ (∑ i ∈ S, ‖σ i‖ ^ diagExp p q) ^ (1 / diagExp p q) := by
      rw [diagTail]
      exact Real.rpow_le_rpow
        (Finset.sum_nonneg fun _ _ => Real.rpow_nonneg (norm_nonneg _) _)
        (tail_sum_le_sum_of_card_ge hpq hq σ hσ hn.le hScard) (by positivity)
    calc diagTail p q σ n * ‖e.symm z‖
        ≤ (∑ i ∈ S, ‖σ i‖ ^ diagExp p q) ^ (1 / diagExp p q) * ‖e.symm z‖ :=
          mul_le_mul_of_nonneg_right hdiagle (norm_nonneg _)
      _ ≤ ‖DiagCLMpq p q σ (e.symm z)‖ := hratio

/-! ## The approximation numbers -/

/-- **Lower bound.** `diagTail ≤ aₙ(D_σ)` (`n < m`): for any rank-`≤ n` `L`,
`ker L` has dimension `≥ m − n`, and `D_σ` agrees with `D_σ − L` on it. -/
theorem le_approximationNumber_DiagCLMpq (hpq : p < q) (hq : q ≠ ∞) (σ : Fin m → 𝕜)
    (hσ : _root_.Antitone fun i => ‖σ i‖) {n : ℕ} (hn : n < m) :
    diagTail p q σ n ≤ approximationNumber (DiagCLMpq p q σ) n := by
  refine le_csInf (approximationSet_nonempty _ _) ?_
  rintro r ⟨L, hL, rfl⟩
  have hker : m - n ≤ Module.finrank 𝕜 (LinearMap.ker
      (L : PiLp q (fun _ : Fin m => 𝕜) →ₗ[𝕜] PiLp p (fun _ : Fin m => 𝕜))) := by
    have hrn := (L : PiLp q (fun _ : Fin m => 𝕜) →ₗ[𝕜]
      PiLp p (fun _ : Fin m => 𝕜)).finrank_range_add_finrank_ker
    have hrange : Module.finrank 𝕜 (LinearMap.range
        (L : PiLp q (fun _ : Fin m => 𝕜) →ₗ[𝕜] PiLp p (fun _ : Fin m => 𝕜))) ≤ n :=
      Module.finrank_le_of_rank_le hL
    rw [finrank_piLp] at hrn
    omega
  obtain ⟨x, hxV, hxne, hxbound⟩ := exists_norm_ratio_ge_DiagCLMpq hpq hq σ hσ hn
    (LinearMap.ker (L : PiLp q (fun _ : Fin m => 𝕜) →ₗ[𝕜] PiLp p (fun _ : Fin m => 𝕜))) hker
  have hLx : L x = 0 := LinearMap.mem_ker.mp hxV
  have happ : (DiagCLMpq p q σ - L) x = DiagCLMpq p q σ x := by
    simp [hLx]
  have hxpos : 0 < ‖x‖ := norm_pos_iff.mpr hxne
  refine le_of_mul_le_mul_right ?_ hxpos
  calc diagTail p q σ n * ‖x‖
      ≤ ‖DiagCLMpq p q σ x‖ := hxbound
    _ = ‖(DiagCLMpq p q σ - L) x‖ := by rw [happ]
    _ ≤ ‖DiagCLMpq p q σ - L‖ * ‖x‖ := (DiagCLMpq p q σ - L).le_opNorm x

/-- **The approximation numbers of a mixed-exponent diagonal operator.** For
`1 ≤ p < q < ∞`, a diagonal non-increasing in modulus, and `n < m`,
`aₙ(D_σ : ℓ^q_m → ℓ^p_m) = (∑_{k≥n} ‖σ_k‖^r)^{1/r}` with `1/r = 1/p − 1/q`. -/
theorem approximationNumber_DiagCLMpq_eq (hpq : p < q) (hq : q ≠ ∞) (σ : Fin m → 𝕜)
    (hσ : _root_.Antitone fun i => ‖σ i‖) {n : ℕ} (hn : n < m) :
    approximationNumber (DiagCLMpq p q σ) n = diagTail p q σ n :=
  le_antisymm (approximationNumber_DiagCLMpq_le hpq hq σ hn.le)
    (le_approximationNumber_DiagCLMpq hpq hq σ hσ hn)

/-! ## Corollaries -/

/-- **Universal upper bound.** Every s-number sequence is bounded above by the
tail value: `sₙ(D_σ) ≤ (∑_{k≥n} ‖σ_k‖^r)^{1/r}` (`n ≤ m`). No ordering of the
diagonal or strictness is required. -/
theorem sn_DiagCLMpq_le {s : Family 𝕜} (hs : IsSNumberSequence s) (hpq : p < q) (hq : q ≠ ∞)
    (σ : Fin m → 𝕜) {n : ℕ} (hn : n ≤ m) :
    s (DiagCLMpq p q σ) n ≤ diagTail p q σ n :=
  (sn_le_approximationNumber hs (DiagCLMpq p q σ) n).trans
    (approximationNumber_DiagCLMpq_le hpq hq σ hn)

/-- **Operator norm** (the `n = 0` case): `‖D_σ‖ = (∑_i ‖σ_i‖^r)^{1/r} = ‖σ‖_{ℓ^r}`,
for a diagonal non-increasing in modulus. -/
theorem norm_DiagCLMpq_eq [NeZero m] (hpq : p < q) (hq : q ≠ ∞) (σ : Fin m → 𝕜)
    (hσ : _root_.Antitone fun i => ‖σ i‖) :
    ‖DiagCLMpq p q σ‖ = (∑ i, ‖σ i‖ ^ diagExp p q) ^ (1 / diagExp p q) := by
  have hm : 0 < m := Nat.pos_of_ne_zero (NeZero.ne m)
  rw [← approximationNumber_zero_eq_norm (DiagCLMpq p q σ),
    approximationNumber_DiagCLMpq_eq hpq hq σ hσ hm, diagTail]
  congr 1
  exact Finset.sum_congr (Finset.filter_true_of_mem fun i _ => Nat.zero_le _) fun _ _ => rfl

/-- **Cross-check against the identity embedding** (`σ ≡ 1`): the tail value
reduces to the Gelfand width `(m − n)^{1/p−1/q}`. -/
example (hpq : p < q) (hq : q ≠ ∞) {n : ℕ} (hn : n < m) :
    diagTail p q (fun _ : Fin m => (1 : 𝕜)) n
      = ((m - n : ℕ) : ℝ) ^ (1 / p.toReal - 1 / q.toReal) := by
  have h1 := approximationNumber_DiagCLMpq_eq hpq hq (fun _ : Fin m => (1 : 𝕜))
    (fun _ _ _ => le_refl _) hn
  rw [DiagCLMpq_one] at h1
  rw [← h1]
  exact approximationNumber_idEmbed_eq hpq.le hq hn

/-- **Cross-check against the same-exponent diagonal** (`p = q`): the `r = ∞`
case is `aₙ(D_σ) = ‖σ_n‖`, from `SNumbers.Examples.DiagonalMatrices`. -/
example (σ : Fin m → 𝕜) (hσ : _root_.Antitone fun i => ‖σ i‖) {n : ℕ} (hn : n < m) :
    approximationNumber (DiagCLMpq p p σ) n = ‖σ ⟨n, hn⟩‖ := by
  rw [DiagCLMpq_self]; exact approximationNumber_DiagCLM_eq hσ hn

/-! ## The regime `q ≤ p`

When the codomain exponent dominates the domain exponent (`q ≤ p`), the picture
degenerates to the `r = ∞` case: the operator norm is the *maximum* diagonal
modulus (written `⨆ i, ‖σ i‖`, a supremum), and every s-number is bounded above
by the tail maximum `‖σ_n‖`. Both facts are inherited from the same-exponent
example `DiagonalMatrices` through the factorisation
`D_σ = (id : ℓ^q → ℓ^p) ∘ D_σ^{(q)}`, since `id : ℓ^q_m → ℓ^p_m` is a contraction
for `q ≤ p`. The `ℓ^∞` codomain (`p = ∞`) is included. -/

/-- **`L^p`-norm monotonicity in the exponent** on a finite product: for `q ≤ p`,
`‖x‖_p ≤ ‖x‖_q` (the same underlying vector, re-measured). Mathlib has no `PiLp`
version; a candidate for upstreaming. -/
lemma piLp_norm_le_of_exponent_ge [Nonempty (Fin m)] (hqp : q ≤ p) (f : Fin m → 𝕜) :
    ‖(WithLp.toLp p f : PiLp p (fun _ : Fin m => 𝕜))‖
      ≤ ‖(WithLp.toLp q f : PiLp q (fun _ : Fin m => 𝕜))‖ := by
  have hfp : ∀ i, (WithLp.toLp p f : PiLp p (fun _ : Fin m => 𝕜)) i = f i := fun _ => rfl
  have hfq : ∀ i, (WithLp.toLp q f : PiLp q (fun _ : Fin m => 𝕜)) i = f i := fun _ => rfl
  rcases p.dichotomy with rfl | hp
  · -- `p = ∞`: the sup is dominated by any `ℓ^q`-norm.
    rw [PiLp.norm_eq_ciSup]
    rcases q.dichotomy with rfl | hq
    · rw [PiLp.norm_eq_ciSup]
    · have hQ : 0 < q.toReal := zero_lt_one.trans_le hq
      rw [PiLp.norm_eq_sum hQ]
      refine ciSup_le fun j => ?_
      rw [hfp j]
      calc ‖f j‖ = (‖f j‖ ^ q.toReal) ^ (1 / q.toReal) := by
            rw [← Real.rpow_mul (norm_nonneg _), mul_one_div, div_self hQ.ne', Real.rpow_one]
        _ ≤ (∑ i, ‖(WithLp.toLp q f : PiLp q (fun _ : Fin m => 𝕜)) i‖ ^ q.toReal) ^ (1 /
            q.toReal) := by
            refine Real.rpow_le_rpow (Real.rpow_nonneg (norm_nonneg _) _) ?_ (by positivity)
            rw [← hfq j]
            exact Finset.single_le_sum
              (fun i _ => Real.rpow_nonneg (norm_nonneg _) _) (Finset.mem_univ j)
  · -- `p` finite, hence `q` finite with `q.toReal ≤ p.toReal`.
    have hP : 0 < p.toReal := zero_lt_one.trans_le hp
    have hpt : p ≠ ∞ := by intro h; rw [h, ENNReal.toReal_top] at hp; norm_num at hp
    have hqt : q ≠ ∞ := ne_top_of_le_ne_top hpt hqp
    have hQ : 0 < q.toReal := toReal_pos_of_ne_top hqt
    have hQP : q.toReal ≤ p.toReal := ENNReal.toReal_mono hpt hqp
    have esum_p : ∑ i, ‖(WithLp.toLp p f : PiLp p (fun _ : Fin m => 𝕜)) i‖ ^ p.toReal
        = ∑ i, ‖f i‖ ^ p.toReal := rfl
    have esum_q : ∑ i, ‖(WithLp.toLp q f : PiLp q (fun _ : Fin m => 𝕜)) i‖ ^ q.toReal
        = ∑ i, ‖f i‖ ^ q.toReal := rfl
    rw [PiLp.norm_eq_sum hP, PiLp.norm_eq_sum hQ, esum_p, esum_q]
    set SQ : ℝ := ∑ i, ‖f i‖ ^ q.toReal with hSQ
    have hSQnn : 0 ≤ SQ := Finset.sum_nonneg fun _ _ => Real.rpow_nonneg (norm_nonneg _) _
    -- `∑ ‖f i‖^p ≤ SQ^{p/q}`.
    have hkey : ∑ i, ‖f i‖ ^ p.toReal ≤ SQ ^ (p.toReal / q.toReal) := by
      have hterm : ∀ i, ‖f i‖ ^ p.toReal
          ≤ ‖f i‖ ^ q.toReal * SQ ^ ((p.toReal - q.toReal) / q.toReal) := by
        intro i
        rcases eq_or_ne ‖f i‖ 0 with h0 | h0
        · rw [h0]; simp [Real.zero_rpow hP.ne', Real.zero_rpow hQ.ne']
        · have hpos : 0 < ‖f i‖ := (norm_nonneg _).lt_of_ne (Ne.symm h0)
          have hsingle : ‖f i‖ ^ q.toReal ≤ SQ :=
            Finset.single_le_sum (fun j _ => Real.rpow_nonneg (norm_nonneg _) _) (Finset.mem_univ i)
          have hle : ‖f i‖ ^ (p.toReal - q.toReal)
              ≤ SQ ^ ((p.toReal - q.toReal) / q.toReal) := by
            have heq : ‖f i‖ ^ (p.toReal - q.toReal)
                = (‖f i‖ ^ q.toReal) ^ ((p.toReal - q.toReal) / q.toReal) := by
              rw [← Real.rpow_mul (norm_nonneg _)]
              congr 1
              field_simp
            rw [heq]
            exact Real.rpow_le_rpow (Real.rpow_nonneg (norm_nonneg _) _) hsingle
              (div_nonneg (by linarith) hQ.le)
          calc ‖f i‖ ^ p.toReal
              = ‖f i‖ ^ q.toReal * ‖f i‖ ^ (p.toReal - q.toReal) := by
                rw [← Real.rpow_add hpos]; congr 1; ring
            _ ≤ ‖f i‖ ^ q.toReal * SQ ^ ((p.toReal - q.toReal) / q.toReal) :=
                mul_le_mul_of_nonneg_left hle (Real.rpow_nonneg (norm_nonneg _) _)
      have hcombine : SQ * SQ ^ ((p.toReal - q.toReal) / q.toReal) = SQ ^ (p.toReal / q.toReal)
          := by
        rcases eq_or_lt_of_le hSQnn with h0 | hpos
        · rw [← h0, zero_mul, Real.zero_rpow (by positivity : (0:ℝ) < p.toReal / q.toReal).ne']
        · have hstep : SQ * SQ ^ ((p.toReal - q.toReal) / q.toReal)
              = SQ ^ (1 + (p.toReal - q.toReal) / q.toReal) := by
            rw [Real.rpow_add hpos, Real.rpow_one]
          rw [hstep]; congr 1; field_simp; ring
      calc ∑ i, ‖f i‖ ^ p.toReal
          ≤ ∑ i, ‖f i‖ ^ q.toReal * SQ ^ ((p.toReal - q.toReal) / q.toReal) :=
            Finset.sum_le_sum fun i _ => hterm i
        _ = SQ * SQ ^ ((p.toReal - q.toReal) / q.toReal) := by rw [← Finset.sum_mul, ← hSQ]
        _ = SQ ^ (p.toReal / q.toReal) := hcombine
    calc (∑ i, ‖f i‖ ^ p.toReal) ^ (1 / p.toReal)
        ≤ (SQ ^ (p.toReal / q.toReal)) ^ (1 / p.toReal) :=
          Real.rpow_le_rpow (Finset.sum_nonneg fun _ _ => Real.rpow_nonneg (norm_nonneg _) _)
            hkey (by positivity)
      _ = SQ ^ (1 / q.toReal) := by
          rw [← Real.rpow_mul hSQnn]; congr 1; field_simp

/-- **The identity embedding is a contraction** when `q ≤ p`: `‖id : ℓ^q_m → ℓ^p_m‖ ≤ 1`.
(The companion of `norm_idEmbed`, which computes the norm for `p ≤ q`.) -/
lemma norm_idEmbed_le_one [Nonempty (Fin m)] (hqp : q ≤ p) :
    ‖idEmbed (𝕜 := 𝕜) (m := m) p q‖ ≤ 1 :=
  opNorm_le_bound _ zero_le_one fun x => by
    rw [one_mul]; exact piLp_norm_le_of_exponent_ge hqp (WithLp.ofLp x)

/-- **Factorisation through the same-exponent diagonal**:
`D_σ : ℓ^q_m → ℓ^p_m` equals the identity embedding `ℓ^q_m → ℓ^p_m` after the
same-exponent diagonal `D_σ : ℓ^q_m → ℓ^q_m`. -/
lemma DiagCLMpq_eq_comp (σ : Fin m → 𝕜) :
    DiagCLMpq p q σ = (idEmbed p q).comp (DiagCLM q σ) := by
  ext x i; simp

/-- **Operator norm for `q ≤ p`**: `‖D_σ : ℓ^q_m → ℓ^p_m‖ = ⨆ i, ‖σ i‖`, the
largest diagonal modulus (`= ‖σ‖_{ℓ^∞}`; `⨆` is the supremum). -/
theorem norm_DiagCLMpq_iSup [Nonempty (Fin m)] (hqp : q ≤ p) (σ : Fin m → 𝕜) :
    ‖DiagCLMpq p q σ‖ = ⨆ i, ‖σ i‖ := by
  refine le_antisymm ?_ ?_
  · -- Upper bound via the factorisation.
    rw [DiagCLMpq_eq_comp]
    calc ‖(idEmbed p q).comp (DiagCLM q σ)‖
        ≤ ‖idEmbed (𝕜 := 𝕜) (m := m) p q‖ * ‖DiagCLM q σ‖ := opNorm_comp_le _ _
      _ ≤ 1 * ⨆ i, ‖σ i‖ := by
          rw [norm_DiagCLM]
          exact mul_le_mul_of_nonneg_right (norm_idEmbed_le_one hqp)
            (Real.iSup_nonneg fun i => norm_nonneg _)
      _ = ⨆ i, ‖σ i‖ := one_mul _
  · -- Lower bound: test on each basis vector.
    refine ciSup_le fun j => ?_
    have hDe : DiagCLMpq p q σ (PiLp.single q j (1 : 𝕜)) = PiLp.single p j (σ j) := by
      ext k
      rcases eq_or_ne k j with rfl | hk
      · simp
      · simp [hk]
    have hbound := (DiagCLMpq p q σ).le_opNorm (PiLp.single q j (1 : 𝕜))
    rw [hDe, PiLp.norm_single, PiLp.norm_single, norm_one, mul_one] at hbound
    exact hbound

/-- **Universal upper bound for `q ≤ p`** (approximation numbers): for a diagonal
non-increasing in modulus, `aₙ(D_σ) ≤ ‖σ_n‖` (`n < m`). Inherited from the
same-exponent value `aₙ(D_σ^{(q)}) = ‖σ_n‖` through the contraction `id`. -/
theorem approximationNumber_DiagCLMpq_le_of_exponent_ge (hqp : q ≤ p) (σ : Fin m → 𝕜)
    (hσ : _root_.Antitone fun i => ‖σ i‖) {n : ℕ} (hn : n < m) :
    approximationNumber (DiagCLMpq p q σ) n ≤ ‖σ ⟨n, hn⟩‖ := by
  have : Nonempty (Fin m) := ⟨⟨n, hn⟩⟩
  rw [DiagCLMpq_eq_comp]
  calc approximationNumber ((idEmbed p q).comp (DiagCLM q σ)) n
      = approximationNumber ((idEmbed p q).comp ((DiagCLM q σ).comp
          (ContinuousLinearMap.id 𝕜 (PiLp q (fun _ : Fin m => 𝕜))))) n := by
        rw [ContinuousLinearMap.comp_id]
    _ ≤ ‖idEmbed (𝕜 := 𝕜) (m := m) p q‖ * approximationNumber (DiagCLM q σ) n
          * ‖ContinuousLinearMap.id 𝕜 (PiLp q (fun _ : Fin m => 𝕜))‖ :=
        approximationNumber_comp_comp_le _ _ _ _
    _ = ‖idEmbed (𝕜 := 𝕜) (m := m) p q‖ * ‖σ ⟨n, hn⟩‖
          * ‖ContinuousLinearMap.id 𝕜 (PiLp q (fun _ : Fin m => 𝕜))‖ := by
        rw [approximationNumber_DiagCLM_eq hσ hn]
    _ ≤ 1 * ‖σ ⟨n, hn⟩‖ * 1 := by
        gcongr
        · exact norm_idEmbed_le_one hqp
        · exact norm_id_le
    _ = ‖σ ⟨n, hn⟩‖ := by ring

/-- **Universal upper bound for `q ≤ p`** (all s-numbers): `sₙ(D_σ) ≤ ‖σ_n‖`. -/
theorem sn_DiagCLMpq_le_of_exponent_ge {s : Family 𝕜} (hs : IsSNumberSequence s)
    (hqp : q ≤ p) (σ : Fin m → 𝕜) (hσ : _root_.Antitone fun i => ‖σ i‖) {n : ℕ} (hn : n < m) :
    s (DiagCLMpq p q σ) n ≤ ‖σ ⟨n, hn⟩‖ :=
  (sn_le_approximationNumber hs (DiagCLMpq p q σ) n).trans
    (approximationNumber_DiagCLMpq_le_of_exponent_ge hqp σ hσ hn)

/-! ## Remark on `p > q`

For `p > q` the tail-maximum upper bound `aₙ(D_σ) ≤ ‖σ_n‖` above need not be
sharp: the exact approximation numbers have no elementary closed form and belong
to the harder theory of Gelfand and Kolmogorov widths. Only the two clean results
of this section — the operator norm and the universal upper bound — are recorded
here. -/

end MixedExponent

end SNumbers

/- Adapted for Lean Pool: module imports and compatibility with its pinned toolchain. -/
