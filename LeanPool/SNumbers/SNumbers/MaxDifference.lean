/-
Copyright (c) 2026 Mario Ullrich. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Ullrich
-/
import LeanPool.SNumbers.SNumbers.Inequalities
import LeanPool.SNumbers.SNumbers.PiLpCoordinates
import LeanPool.SNumbers.BasicResults.Determinant
import LeanPool.SNumbers.BasicResults.SVD

/-!
# The maximal difference theorem: `aₙ ≤ e·(n+1)·hₙ`

For every bounded operator `S : X →L[𝕜] Y` between normed spaces over
`𝕜 ∈ {ℝ, ℂ}` and every `n`, the **maximal difference theorem**: the
approximation numbers are bounded by the Hilbert numbers,

  `aₙ(S) ≤ e·(n+1)·hₙ(S)`

(`approximationNumber_le_e_mul_hilbertNumber`; the proof gives the slightly
sharper constant `(n+1)^{n+1}/nⁿ ≤ e·(n+1)`). Since `aₙ` is the largest and
`hₙ` the smallest s-number sequence, this bounds *any* s-number sequence by
*any* other, `sₙ(S) ≤ e·(n+1)·tₙ(S)` (`sn_le_e_mul_tn`) — the maximal
possible difference between two s-number sequences is a factor linear in `n`.
It proves the conjecture of Carl and Pietsch up to the constant `e`. The
factor `n+1` is optimal, e.g. for the identity `ℓ₁ → ℓ∞`.

Because `cₙ, dₙ ≤ aₙ`, the theorem specialises to the Gelfand and Kolmogorov
numbers, `max (cₙ(S), dₙ(S)) ≤ e·(n+1)·sₙ(S)` for every s-number sequence `s`
(`max_gelfandNumber_kolmogorovNumber_le_e_mul_sn`), which for `s = bₙ` is the
**Mityagin–Henkin conjecture** up to the constant `e`.

## Main results

The two theorems and, below them, their consequences.

* `approximationNumber_le_mul_hilbertNumber` — `aₙ ≤ ((n+1)^{n+1}/nⁿ)·hₙ`, the
  sharp constant this proof produces.
* `approximationNumber_le_e_mul_hilbertNumber` — the same in the readable form
  `aₙ ≤ e·(n+1)·hₙ` (via `ratio_le_exp_mul`).
* `approximationNumber_le_e_mul_sn` — `hₙ` replaced by an arbitrary s-number
  sequence, since `hₙ` is the smallest one (`hilbertNumber_le_sn`).
* `sn_le_e_mul_tn` — `sₙ ≤ e·(n+1)·tₙ` for *any two* s-number sequences, since
  `aₙ` is the largest one (`sn_le_approximationNumber`). Carl–Pietsch up to `e`.
* `gelfandNumber_le_approximationNumber`, `kolmogorovNumber_le_approximationNumber`
  — `cₙ, dₙ ≤ aₙ`, the inputs for the classical numbers.
* `max_gelfandNumber_kolmogorovNumber_le_e_mul_sn` — `max(cₙ,dₙ) ≤ e·(n+1)·sₙ`
  for every s-number sequence `s`, with the two named instances
  `max_gelfandNumber_kolmogorovNumber_le_e_mul_hilbertNumber` (`s = hₙ`) and
  `max_gelfandNumber_kolmogorovNumber_le_e_mul_bernsteinNumber` (`s = bₙ`, the
  Mityagin–Henkin form).

## The argument

Everything runs through the **determinant quantities**

  `Δₖ(S) := sup { |det (B ∘ S ∘ A)| : A : ℓ₂ᵏ → X, B : Y → ℓ₂ᵏ, ‖A‖ ≤ 1, ‖B‖ ≤ 1 }`

(`detNumber`). Here `B ∘ S ∘ A` is an endomorphism of the `k`-dimensional
Hilbert space `ℓ₂ᵏ = EuclideanSpace 𝕜 (Fin k)`, so its determinant is a
scalar; for `k = 0` the space is trivial and `Δ₀(S) = 1` automatically. One
has `Δₖ(S) ≤ ‖S‖ᵏ < ∞` (`detNumber_le_pow_norm`, via `∏ aᵢ(T) = |det T|`).
The `Δₖ` are squeezed between the two quantities of interest:

* **Upper bound** `Δₙ₊₁(S) ≤ hₙ(S)·Δₙ(S)`
  (`detNumber_succ_le_hilbertNumber_mul`): for any admissible pair for `Δₙ₊₁`
  and `T := B∘S∘A`, split `|det T| = ∏_{k≤n} aₖ(T)`
  (`prod_approximationNumber_eq_norm_det`) into the top `n` factors — at most
  `Δₙ(S)`, because the diagonal factorisation
  `B₁∘T∘A₁ = diag(a₀,…,aₙ)` (`SVD.IsCompactOperator.diagonalFactorisation`),
  compressed to the first `n` coordinates, is admissible for `Δₙ`
  (`prod_approximationNumber_le_detNumber`) — and the last factor
  `aₙ(T) ≤ hₙ(S)`.
* **Lower bound (growth lemma)** `Δₖ₊₁(S) ≥ (kᵏ/(k+1)^{k+1})·aₖ(S)·Δₖ(S)`
  (`approximationNumber_mul_detNumber_le_detNumber_succ`): given an admissible
  pair with `det (BSA) ≠ 0`, the operator

    `L := S∘A∘(B∘S∘A)⁻¹∘B∘S`

  has rank at most `k`, so `‖S - L‖ ≥ aₖ(S)` by the very definition of the
  approximation numbers. Bordering `(A, B)` by a vector `x ∈ B_X` and a
  functional `b ∈ B_{Y'}`, weighted by `λ² + μ² = 1`,

    `A₀(ξ ⊕ τ) = λ·Aξ + μ·τ·x`,   `B₀ y = (λ·By) ⊕ (μ·b y)`,

  produces an admissible pair for `Δₖ₊₁(S)` whose determinant is

    `det (B₀SA₀) = λ^{2k}·μ²·b((S - L)x)·det (BSA)`.                     (∗)

  Choosing `x` and `b` so that `b((S - L)x)` almost equals `‖S - L‖ ≥ aₖ(S)`
  (the operator norm characterisation plus Hahn–Banach) and optimising
  `λ² = k/(k+1)`, `μ² = 1/(k+1)` yields the lower bound.

Dividing the two bounds at `k = n` by `Δₙ(S) > 0`
(`detNumber_pos_of_approximationNumber_pos`) gives
`aₙ(S) ≤ ((n+1)^{n+1}/nⁿ)·hₙ(S) ≤ e·(n+1)·hₙ(S)`.

Identity (∗) is a *column operation*, not a Schur complement: writing
`ζ := (BSA)⁻¹B(Sx)`, the last column of the matrix of `B₀SA₀` equals
`μ/λ` times the combination of its first `k` columns with coefficients `ζ`,
*above the corner*. Subtracting that combination therefore leaves a matrix
whose last column is zero except at the corner, where it equals
`μ²·(b(Sx) - b(S(Aζ))) = μ²·b((S - L)x)`; Laplace expansion along that column
finishes. This is `Matrix.det_eq_corner_mul_det_submatrix`
(`BasicResults.Determinant`), a statement about matrices over any commutative
ring that needs no invertibility hypothesis.

## Remaining work

The sharper bound `aₙ(S) ≤ √(e·(n+1))·hₙ(S)` valid when `X` or `Y` is a
Hilbert space is **not** formalised here.

## References

* M. Ullrich, *On bounds between all s-numbers and widths of convex sets*,
  preprint, 2026, [arxiv](https://arxiv.org/abs/2608.05024), Theorem 1
  (general case).
-/

universe u

open ContinuousLinearMap
open scoped Pointwise

namespace SNumbers

variable {𝕜 : Type u} [RCLike 𝕜]
variable {X Y : Type u}
variable [NormedAddCommGroup X] [NormedSpace 𝕜 X]
variable [NormedAddCommGroup Y] [NormedSpace 𝕜 Y]

/-! ### Definition -/

/-- The set of values `|det (B ∘ S ∘ A)|` over contraction pairs
`A : ℓ₂ᵏ → X`, `B : Y → ℓ₂ᵏ`; its supremum is `Δₖ(S)`. -/
def detSet (S : X →L[𝕜] Y) (k : ℕ) : Set ℝ :=
  {r | ∃ (A : EuclideanSpace 𝕜 (Fin k) →L[𝕜] X) (B : Y →L[𝕜] EuclideanSpace 𝕜 (Fin k)),
      ‖A‖ ≤ 1 ∧ ‖B‖ ≤ 1 ∧
      r = ‖LinearMap.det (B.comp (S.comp A) :
          EuclideanSpace 𝕜 (Fin k) →ₗ[𝕜] EuclideanSpace 𝕜 (Fin k))‖}

/-- The `k`-th **determinant quantity**
`Δₖ(S) = sup { |det (B∘S∘A)| : ‖A‖ ≤ 1, ‖B‖ ≤ 1 }` of a bounded operator.
For `k = 0` this equals `1` (`detNumber_zero`). -/
noncomputable def detNumber (S : X →L[𝕜] Y) (k : ℕ) : ℝ :=
  sSup (detSet S k)

/-! ### Elementary properties -/

/-- The admissible set is nonempty (take `A = 0`, `B = 0`). -/
lemma detSet_nonempty (S : X →L[𝕜] Y) (k : ℕ) : (detSet S k).Nonempty :=
  ⟨_, 0, 0, by simp, by simp, rfl⟩

omit [RCLike 𝕜] in
/-- The trivial space `ℓ₂⁰` has only one element. -/
private lemma subsingleton_euclidean_zero :
    Subsingleton (EuclideanSpace 𝕜 (Fin 0)) :=
  ⟨fun _ _ => PiLp.ext fun i => i.elim0⟩

/-- **`|det T| ≤ ‖T‖ᵏ`** for an endomorphism `T` of `ℓ₂ᵏ`. For `k ≥ 1` this is
the identity `∏ᵢ aᵢ(T) = |det T|` (`prod_approximationNumber_eq_norm_det`)
together with `aᵢ(T) ≤ ‖T‖`; for `k = 0` both sides are `1`. -/
lemma norm_det_le_pow_norm {k : ℕ}
    (T : EuclideanSpace 𝕜 (Fin k) →L[𝕜] EuclideanSpace 𝕜 (Fin k)) :
    ‖LinearMap.det (T : EuclideanSpace 𝕜 (Fin k) →ₗ[𝕜] EuclideanSpace 𝕜 (Fin k))‖
      ≤ ‖T‖ ^ k := by
  cases k with
  | zero =>
    have := subsingleton_euclidean_zero (𝕜 := 𝕜)
    rw [LinearMap.det_eq_one_of_subsingleton, norm_one, pow_zero]
  | succ m =>
    have : Nontrivial (EuclideanSpace 𝕜 (Fin (m + 1))) :=
      Module.nontrivial_of_finrank_pos (by rw [finrank_euclideanSpace_fin]; omega)
    have h := prod_approximationNumber_eq_norm_det T
    rw [finrank_euclideanSpace_fin] at h
    rw [← h]
    calc ∏ i ∈ Finset.range (m + 1), approximationNumber T i
        ≤ ∏ _i ∈ Finset.range (m + 1), ‖T‖ :=
          Finset.prod_le_prod₀ (fun i _ => approximationNumber_nonneg T i)
            (fun i _ => approximationNumber_le_norm T i)
      _ = ‖T‖ ^ (m + 1) := by rw [Finset.prod_const, Finset.card_range]

/-- Each admissible value is at most `‖S‖ᵏ` (since `‖B∘S∘A‖ ≤ ‖S‖`). -/
private lemma detSet_le_pow_norm (S : X →L[𝕜] Y) (k : ℕ) :
    ∀ r ∈ detSet S k, r ≤ ‖S‖ ^ k := by
  rintro r ⟨A, B, hA, hB, rfl⟩
  refine (norm_det_le_pow_norm _).trans (pow_le_pow_left₀ (norm_nonneg _) ?_ k)
  calc ‖B.comp (S.comp A)‖
      ≤ ‖B‖ * ‖S‖ * ‖A‖ := norm_comp_comp_le A S B
    _ ≤ 1 * ‖S‖ * 1 := by gcongr
    _ = ‖S‖ := by ring

/-- The admissible set is bounded above by `‖S‖ᵏ`. -/
lemma detSet_bddAbove (S : X →L[𝕜] Y) (k : ℕ) : BddAbove (detSet S k) :=
  ⟨‖S‖ ^ k, detSet_le_pow_norm S k⟩

/-- Every admissible pair bounds `Δₖ(S)` from below. -/
lemma norm_det_le_detNumber (S : X →L[𝕜] Y) {k : ℕ}
    {A : EuclideanSpace 𝕜 (Fin k) →L[𝕜] X} {B : Y →L[𝕜] EuclideanSpace 𝕜 (Fin k)}
    (hA : ‖A‖ ≤ 1) (hB : ‖B‖ ≤ 1) :
    ‖LinearMap.det (B.comp (S.comp A) :
        EuclideanSpace 𝕜 (Fin k) →ₗ[𝕜] EuclideanSpace 𝕜 (Fin k))‖ ≤ detNumber S k :=
  le_csSup (detSet_bddAbove S k) ⟨A, B, hA, hB, rfl⟩

lemma detNumber_nonneg (S : X →L[𝕜] Y) (k : ℕ) : 0 ≤ detNumber S k :=
  Real.sSup_nonneg <| by rintro r ⟨A, B, _, _, rfl⟩; exact norm_nonneg _

/-- **`Δ₀(S) = 1`.** Every endomorphism of the trivial space `ℓ₂⁰` has
determinant `1`, so the admissible set is exactly `{1}`. -/
lemma detNumber_zero (S : X →L[𝕜] Y) : detNumber S 0 = 1 := by
  have := subsingleton_euclidean_zero (𝕜 := 𝕜)
  have hset : detSet S 0 = {(1 : ℝ)} := by
    ext r
    constructor
    · rintro ⟨A, B, _, _, rfl⟩
      rw [Set.mem_singleton_iff, LinearMap.det_eq_one_of_subsingleton, norm_one]
    · rintro hr
      rw [Set.mem_singleton_iff] at hr
      subst hr
      exact ⟨0, 0, by simp, by simp,
        by rw [LinearMap.det_eq_one_of_subsingleton, norm_one]⟩
  rw [detNumber, hset, csSup_singleton]

/-- `Δₖ(S) ≤ ‖S‖ᵏ`. -/
lemma detNumber_le_pow_norm (S : X →L[𝕜] Y) (k : ℕ) : detNumber S k ≤ ‖S‖ ^ k :=
  csSup_le (detSet_nonempty S k) (detSet_le_pow_norm S k)


/-! ### Elementary helpers -/

/-- `0 < nⁿ` in `ℝ` (with the convention `0⁰ = 1`). -/
private lemma pow_self_pos (n : ℕ) : (0 : ℝ) < (n : ℝ) ^ n := by
  cases n with
  | zero => norm_num
  | succ m => exact pow_pos (by exact_mod_cast Nat.succ_pos m) _

/-- The per-step growth factor `kᵏ/(k+1)^{k+1}` is positive. -/
private lemma growth_ratio_pos (k : ℕ) :
    (0 : ℝ) < (k : ℝ) ^ k / ((k : ℝ) + 1) ^ (k + 1) :=
  div_pos (pow_self_pos k) (pow_pos (by positivity) _)

/-- Two-term Cauchy–Schwarz: for `λ² + μ² = 1` and `c ≥ 0` with `a² + b² = c²`,
`λ·a + μ·b ≤ c`. No sign assumption on `λ, μ, a, b` is needed: expanding
`(λa + μb)² + (λb − μa)² = (λ² + μ²)(a² + b²)` already gives `(λa + μb)² ≤ c²`. -/
private lemma lam_mul_add_mu_mul_le {lam mu a b c : ℝ}
    (hlm : lam ^ 2 + mu ^ 2 = 1) (hc : 0 ≤ c) (hsq : a ^ 2 + b ^ 2 = c ^ 2) :
    lam * a + mu * b ≤ c := by
  have h1 : (lam * a + mu * b) ^ 2 ≤ c ^ 2 := by
    nlinarith [sq_nonneg (lam * b - mu * a)]
  exact le_of_sq_le_sq h1 hc

/-- `(n+1)^{n+1}/nⁿ = (n+1)·(1+1/n)ⁿ ≤ e·(n+1)`, from `1 + x ≤ eˣ` at
`x = 1/n` raised to the `n`-th power. -/
private lemma ratio_le_exp_mul (n : ℕ) :
    ((n : ℝ) + 1) ^ (n + 1) / (n : ℝ) ^ n ≤ Real.exp 1 * ((n : ℝ) + 1) := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · norm_num
  · have hN : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
    have h1 : 1 + 1 / (n : ℝ) ≤ Real.exp (1 / (n : ℝ)) := by
      have := Real.add_one_le_exp (1 / (n : ℝ)); linarith
    have h2 : (1 + 1 / (n : ℝ)) ^ n ≤ Real.exp 1 := by
      calc (1 + 1 / (n : ℝ)) ^ n
          ≤ Real.exp (1 / (n : ℝ)) ^ n := pow_le_pow_left₀ (by positivity) h1 n
        _ = Real.exp ((n : ℝ) * (1 / (n : ℝ))) := (Real.exp_nat_mul _ n).symm
        _ = Real.exp 1 := by rw [mul_one_div, div_self hN.ne']
    have h3 : ((n : ℝ) + 1) ^ n ≤ Real.exp 1 * (n : ℝ) ^ n := by
      have hfac : (n : ℝ) + 1 = (n : ℝ) * (1 + 1 / (n : ℝ)) := by field_simp
      calc ((n : ℝ) + 1) ^ n = (n : ℝ) ^ n * (1 + 1 / (n : ℝ)) ^ n := by
            rw [hfac, mul_pow]
        _ ≤ (n : ℝ) ^ n * Real.exp 1 := mul_le_mul_of_nonneg_left h2 (by positivity)
        _ = Real.exp 1 * (n : ℝ) ^ n := mul_comm _ _
    rw [div_le_iff₀ (pow_self_pos n)]
    calc ((n : ℝ) + 1) ^ (n + 1) = ((n : ℝ) + 1) ^ n * ((n : ℝ) + 1) := pow_succ _ _
      _ ≤ Real.exp 1 * (n : ℝ) ^ n * ((n : ℝ) + 1) :=
          mul_le_mul_of_nonneg_right h3 (by positivity)
      _ = Real.exp 1 * ((n : ℝ) + 1) * (n : ℝ) ^ n := by ring


/-! ### The compression bound and the upper bound `Δₙ₊₁ ≤ hₙ·Δₙ` -/

/-- **Compression bound.** For contractions `A : ℓ₂ⁿ⁺¹ → X`,
`B : Y → ℓ₂ⁿ⁺¹` and `T := B∘S∘A`, the product of the top `n` approximation
numbers of `T` is at most `Δₙ(S)`: the diagonal factorisation
`B₁∘T∘A₁ = diag(a₀(T),…,aₙ(T))` through contractions
(`SVD.IsCompactOperator.diagonalFactorisation`), compressed to the first `n`
coordinates by `padFin`/`projFin`, realises `∏_{k<n} aₖ(T)` as an admissible
determinant for `Δₙ(S)`. -/
lemma prod_approximationNumber_le_detNumber (S : X →L[𝕜] Y) {n : ℕ}
    {A : EuclideanSpace 𝕜 (Fin (n + 1)) →L[𝕜] X}
    {B : Y →L[𝕜] EuclideanSpace 𝕜 (Fin (n + 1))}
    (hA : ‖A‖ ≤ 1) (hB : ‖B‖ ≤ 1) :
    ∏ i ∈ Finset.range n, approximationNumber (B.comp (S.comp A)) i
      ≤ detNumber S n := by
  classical
  have : Nontrivial (EuclideanSpace 𝕜 (Fin (n + 1))) :=
    Module.nontrivial_of_finrank_pos (by rw [finrank_euclideanSpace_fin]; omega)
  set T := B.comp (S.comp A) with hTdef
  have hTc : IsCompactOperator T := isCompactOperator_of_locallyCompactSpace_rng T
  obtain ⟨A₁, B₁, hA₁, hB₁, hdiag⟩ := SVD.IsCompactOperator.diagonalFactorisation hTc n
  have hle : n ≤ n + 1 := Nat.le_succ n
  have hcast : ∀ i : Fin n, Fin.castLE hle i = Fin.castSucc i := fun i => rfl
  -- The compressed admissible pair.
  set A₂ : EuclideanSpace 𝕜 (Fin n) →L[𝕜] X :=
    (A.comp A₁).comp (padFin (p := 2)) with hA₂def
  set B₂ : Y →L[𝕜] EuclideanSpace 𝕜 (Fin n) :=
    (projFin (p := 2) hle).comp (B₁.comp B) with hB₂def
  have hA₂n : ‖A₂‖ ≤ 1 := by
    refine (opNorm_comp_le _ _).trans (Bound.mul_le_one ?_ (norm_padFin_clm_le hle)
      (Or.inr (norm_nonneg _)))
    exact (opNorm_comp_le _ _).trans (Bound.mul_le_one hA hA₁ (Or.inr (norm_nonneg _)))
  have hB₂n : ‖B₂‖ ≤ 1 := by
    refine (opNorm_comp_le _ _).trans (Bound.mul_le_one (norm_projFin_clm_le hle) ?_
      (Or.inr (norm_nonneg _)))
    exact (opNorm_comp_le _ _).trans (Bound.mul_le_one hB₁ hB (Or.inr (norm_nonneg _)))
  -- `padFin`/`projFin` act on standard basis vectors as expected.
  have hpad_single : ∀ j : Fin n,
      padFin (p := 2) (EuclideanSpace.single j (1 : 𝕜))
        = EuclideanSpace.single (Fin.castSucc j) (1 : 𝕜) := by
    intro j
    ext i
    rw [padFin_apply, PiLp.single_apply]
    by_cases hi : (i : ℕ) < n
    · rw [dite_eq_left hi, PiLp.single_apply]
      refine if_congr ?_ rfl rfl
      rw [Fin.ext_iff, Fin.ext_iff, Fin.val_castSucc]
    · rw [dite_eq_right hi, ite_eq_right fun h => hi (by rw [h, Fin.val_castSucc]; exact j.isLt)]
  have hproj_single : ∀ j : Fin n,
      projFin (p := 2) hle (EuclideanSpace.single (Fin.castSucc j) (1 : 𝕜))
        = EuclideanSpace.single j (1 : 𝕜) := by
    intro j
    ext i
    rw [projFin_apply, PiLp.single_apply, PiLp.single_apply, hcast i]
    exact if_congr Fin.castSucc_inj.symm.symm rfl rfl
  -- The compressed operator is diagonal with entries `a₀(T), …, a_{n-1}(T)`.
  have hD : ∀ j : Fin n, (B₂.comp (S.comp A₂)) (EuclideanSpace.single j (1 : 𝕜))
      = (approximationNumber T (j : ℕ) : 𝕜) • EuclideanSpace.single j (1 : 𝕜) := by
    intro j
    have h1 : (B₂.comp (S.comp A₂)) (EuclideanSpace.single j (1 : 𝕜))
        = projFin (p := 2) hle
            (B₁ (T (A₁ (EuclideanSpace.single (Fin.castSucc j) (1 : 𝕜))))) := by
      rw [hA₂def, hB₂def, hTdef]
      simp only [ContinuousLinearMap.comp_apply, hpad_single j]
    rw [h1, hdiag (Fin.castSucc j), map_smul, hproj_single j, Fin.val_castSucc]
  -- Its determinant is the product of the diagonal entries (it is diagonal in the
  -- standard basis, by `hD`), via the general `det_eq_prod_of_apply_eq_smul`.
  have hdet : LinearMap.det (B₂.comp (S.comp A₂) :
        EuclideanSpace 𝕜 (Fin n) →ₗ[𝕜] EuclideanSpace 𝕜 (Fin n))
      = ∏ j : Fin n, (approximationNumber T (j : ℕ) : 𝕜) :=
    LinearMap.det_eq_prod_of_apply_eq_smul
      (EuclideanSpace.basisFun (Fin n) 𝕜).toBasis
      (B₂.comp (S.comp A₂) : EuclideanSpace 𝕜 (Fin n) →ₗ[𝕜] EuclideanSpace 𝕜 (Fin n))
      (fun j => (approximationNumber T (j : ℕ) : 𝕜))
      (fun j => by
        simpa [OrthonormalBasis.coe_toBasis, EuclideanSpace.basisFun_apply] using hD j)
  -- Conclude.
  have hnorm : ‖LinearMap.det (B₂.comp (S.comp A₂) :
        EuclideanSpace 𝕜 (Fin n) →ₗ[𝕜] EuclideanSpace 𝕜 (Fin n))‖
      = ∏ i ∈ Finset.range n, approximationNumber T i := by
    rw [hdet, norm_prod, ← Fin.prod_univ_eq_prod_range (fun i => approximationNumber T i) n]
    exact Finset.prod_congr rfl fun j _ => by
      rw [RCLike.norm_ofReal, abs_of_nonneg (approximationNumber_nonneg _ _)]
  calc ∏ i ∈ Finset.range n, approximationNumber T i
      = ‖LinearMap.det (B₂.comp (S.comp A₂) :
          EuclideanSpace 𝕜 (Fin n) →ₗ[𝕜] EuclideanSpace 𝕜 (Fin n))‖ := hnorm.symm
    _ ≤ detNumber S n := norm_det_le_detNumber S hA₂n hB₂n

/-- **Upper bound `Δₙ₊₁(S) ≤ hₙ(S)·Δₙ(S)`.** For every admissible pair for
`Δₙ₊₁` and `T := B∘S∘A`, split `|det T| = ∏_{k≤n} aₖ(T)` into the top `n`
factors (at most `Δₙ(S)`, by the compression bound) and the last factor
`aₙ(T) ≤ hₙ(S)`. This bounds **every** element of the supremum defining
`Δₙ₊₁(S)`, so no near-maximiser is needed. -/
lemma detNumber_succ_le_hilbertNumber_mul (S : X →L[𝕜] Y) (n : ℕ) :
    detNumber S (n + 1) ≤ hilbertNumber S n * detNumber S n := by
  refine csSup_le (detSet_nonempty S (n + 1)) ?_
  rintro r ⟨A, B, hA, hB, rfl⟩
  have : Nontrivial (EuclideanSpace 𝕜 (Fin (n + 1))) :=
    Module.nontrivial_of_finrank_pos (by rw [finrank_euclideanSpace_fin]; omega)
  have h1 : ‖LinearMap.det (B.comp (S.comp A) :
        EuclideanSpace 𝕜 (Fin (n + 1)) →ₗ[𝕜] EuclideanSpace 𝕜 (Fin (n + 1)))‖
      = ∏ i ∈ Finset.range (n + 1), approximationNumber (B.comp (S.comp A)) i := by
    have h := prod_approximationNumber_eq_norm_det (B.comp (S.comp A))
    rw [finrank_euclideanSpace_fin] at h
    exact h.symm
  have h2 : ∏ i ∈ Finset.range n, approximationNumber (B.comp (S.comp A)) i
      ≤ detNumber S n := prod_approximationNumber_le_detNumber S hA hB
  have h3 : approximationNumber (B.comp (S.comp A)) n ≤ hilbertNumber S n := by
    have h := approximationNumber_eucl_comp_comp_le_mul_hilbertNumber S n n A B
    calc approximationNumber (B.comp (S.comp A)) n
        ≤ ‖B‖ * ‖A‖ * hilbertNumber S n := h
      _ ≤ 1 * hilbertNumber S n :=
          mul_le_mul_of_nonneg_right (Bound.mul_le_one hB hA (Or.inr (norm_nonneg _)))
            (hilbertNumber_nonneg S n)
      _ = hilbertNumber S n := one_mul _
  rw [h1, Finset.prod_range_succ]
  calc (∏ i ∈ Finset.range n, approximationNumber (B.comp (S.comp A)) i) *
        approximationNumber (B.comp (S.comp A)) n
      ≤ detNumber S n * hilbertNumber S n :=
        mul_le_mul h2 h3 (approximationNumber_nonneg _ _) (detNumber_nonneg S n)
    _ = hilbertNumber S n * detNumber S n := mul_comm _ _


/-! ### Basis expansions in `ℓ₂ᵏ`

Two routine consequences of linearity: an operator on `ℓ₂ᵏ` is determined by
its values on the standard basis, in the form needed to recognise a column of a
matrix as a combination of the others. -/

/-- Expanding `F z` over the standard basis of `ℓ₂ᵏ`. -/
private lemma clm_apply_eq_sum {k : ℕ} {Z : Type u} [NormedAddCommGroup Z]
    [NormedSpace 𝕜 Z] (F : EuclideanSpace 𝕜 (Fin k) →L[𝕜] Z)
    (z : EuclideanSpace 𝕜 (Fin k)) :
    F z = ∑ j, z j • F (EuclideanSpace.single j (1 : 𝕜)) := by
  classical
  have hz : ∑ j, z j • EuclideanSpace.single j (1 : 𝕜) = z := by
    simpa using (EuclideanSpace.basisFun (Fin k) 𝕜).sum_repr z
  calc F z = F (∑ j, z j • EuclideanSpace.single j (1 : 𝕜)) := by rw [hz]
    _ = ∑ j, z j • F (EuclideanSpace.single j (1 : 𝕜)) := by
        rw [map_sum]
        exact Finset.sum_congr rfl fun j _ => map_smul F _ _

/-- The `i`-th coordinate of `F z` expanded over the standard basis of `ℓ₂ᵏ`:
the matrix of `F` acts on the coordinates of `z`. -/
private lemma coord_apply_eq_sum {k m : ℕ}
    (F : EuclideanSpace 𝕜 (Fin k) →L[𝕜] EuclideanSpace 𝕜 (Fin m))
    (z : EuclideanSpace 𝕜 (Fin k)) (i : Fin m) :
    F z i = ∑ j, z j * (F (EuclideanSpace.single j (1 : 𝕜))) i := by
  have h := clm_apply_eq_sum ((innerSL 𝕜 (EuclideanSpace.single i (1 : 𝕜))).comp F) z
  simp only [ContinuousLinearMap.comp_apply, innerSL_apply_apply,
    EuclideanSpace.inner_single_left, map_one, one_mul, smul_eq_mul] at h
  exact h

/-! ### Rank of an operator factoring through `ℓ₂ᵏ` -/

/-- An operator that factors through the `k`-dimensional space `ℓ₂ᵏ` has rank
at most `k`. This is what makes the approximant `L = SA(BSA)⁻¹BS` below
admissible for `aₖ`. -/
lemma rank_comp_le_of_euclidean {k : ℕ} (F : EuclideanSpace 𝕜 (Fin k) →L[𝕜] Y)
    (G : X →L[𝕜] EuclideanSpace 𝕜 (Fin k)) :
    (F.comp G).rank ≤ (k : Cardinal) := by
  have hdom : Module.rank 𝕜 (EuclideanSpace 𝕜 (Fin k)) = (k : Cardinal) := by
    rw [← Module.finrank_eq_rank, finrank_euclideanSpace_fin]
  calc (F.comp G).rank
      ≤ F.rank := LinearMap.rank_comp_le_left _ _
    _ ≤ Module.rank 𝕜 (EuclideanSpace 𝕜 (Fin k)) := LinearMap.rank_le_domain _
    _ = (k : Cardinal) := hdom

/-! ### The bordered pair

An admissible pair `(A, B)` for `Δₖ` is enlarged to an admissible pair for
`Δₖ₊₁` using a vector `x ∈ B_X` and a functional `b ∈ B_{Y'}`, weighted so that
`λ² + μ² = 1`:

  `A₀(ξ ⊕ τ) = λ·Aξ + μ·τ·x`,   `B₀ y = (λ·By) ⊕ (μ·b y)`.

Contractivity of `A₀` is the two-term Cauchy–Schwarz inequality
`λa + μb ≤ √(a² + b²)`; contractivity of `B₀` is the identity
`‖B₀y‖² = λ²‖By‖² + μ²|b y|²`. -/

section Border

variable {k : ℕ}

/-- The bordered map `A₀(ξ ⊕ τ) = λ·Aξ + μ·τ·x` on `ℓ₂ᵏ⁺¹`, where `ξ` are the
first `k` coordinates and `τ` the last. -/
private noncomputable def borderDom (A : EuclideanSpace 𝕜 (Fin k) →L[𝕜] X) (x : X)
    (lam mu : ℝ) : EuclideanSpace 𝕜 (Fin (k + 1)) →L[𝕜] X :=
  (lam : 𝕜) • (A.comp (projFin (p := 2) (Nat.le_succ k))) +
    (mu : 𝕜) • ((innerSL 𝕜 (EuclideanSpace.single (Fin.last k) (1 : 𝕜))).smulRight x)

/-- The bordered map `B₀ y = (λ·By) ⊕ (μ·b y)` into `ℓ₂ᵏ⁺¹`. -/
private noncomputable def borderCod (B : Y →L[𝕜] EuclideanSpace 𝕜 (Fin k))
    (b : Y →L[𝕜] 𝕜) (lam mu : ℝ) : Y →L[𝕜] EuclideanSpace 𝕜 (Fin (k + 1)) :=
  (lam : 𝕜) • ((padFin (p := 2)).comp B) +
    (mu : 𝕜) • (b.smulRight (EuclideanSpace.single (Fin.last k) (1 : 𝕜)))

/-- `castLE` along `k ≤ k+1` is `castSucc` (both only touch the value). -/
private lemma castLE_succ_eq_castSucc (i : Fin k) :
    Fin.castLE (Nat.le_succ k) i = Fin.castSucc i := rfl

variable (A : EuclideanSpace 𝕜 (Fin k) →L[𝕜] X) (x : X)
  (B : Y →L[𝕜] EuclideanSpace 𝕜 (Fin k)) (b : Y →L[𝕜] 𝕜) (lam mu : ℝ)

private lemma borderDom_apply (v : EuclideanSpace 𝕜 (Fin (k + 1))) :
    borderDom A x lam mu v = (lam : 𝕜) • A (projFin (p := 2) (Nat.le_succ k) v) +
      ((mu : 𝕜) * v (Fin.last k)) • x := by
  rw [borderDom, add_apply, smul_apply, smul_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.smulRight_apply, innerSL_apply_apply,
    EuclideanSpace.inner_single_left, map_one, one_mul, smul_smul]

private lemma borderDom_single_castSucc (j : Fin k) :
    borderDom A x lam mu (EuclideanSpace.single (Fin.castSucc j) (1 : 𝕜))
      = (lam : 𝕜) • A (EuclideanSpace.single j (1 : 𝕜)) := by
  have hproj : projFin (p := 2) (Nat.le_succ k)
      (EuclideanSpace.single (Fin.castSucc j) (1 : 𝕜))
        = EuclideanSpace.single j (1 : 𝕜) := by
    ext i
    rw [projFin_apply, PiLp.single_apply, PiLp.single_apply, castLE_succ_eq_castSucc i]
    exact if_congr Fin.castSucc_inj.symm.symm rfl rfl
  rw [borderDom_apply, hproj, PiLp.single_apply,
    ite_eq_right (Fin.castSucc_lt_last j).ne', mul_zero, zero_smul, add_zero]

private lemma borderDom_single_last :
    borderDom A x lam mu (EuclideanSpace.single (Fin.last k) (1 : 𝕜)) = (mu : 𝕜) • x := by
  have hproj : projFin (p := 2) (Nat.le_succ k)
      (EuclideanSpace.single (Fin.last k) (1 : 𝕜)) = 0 := by
    ext i
    rw [projFin_apply, PiLp.single_apply, castLE_succ_eq_castSucc i, PiLp.zero_apply,
      ite_eq_right (Fin.castSucc_lt_last i).ne]
  rw [borderDom_apply, hproj, map_zero, smul_zero, zero_add, PiLp.single_apply,
    ite_eq_left rfl, mul_one]

private lemma borderCod_castSucc (y : Y) (i : Fin k) :
    (borderCod B b lam mu y) (Fin.castSucc i) = (lam : 𝕜) * (B y) i := by
  rw [borderCod, add_apply, PiLp.add_apply, smul_apply, smul_apply,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.smulRight_apply,
    PiLp.smul_apply, PiLp.smul_apply, PiLp.smul_apply,
    ← castLE_succ_eq_castSucc i, padFin_castLE, PiLp.single_apply,
    ite_eq_right ((Fin.castSucc_lt_last i).ne ∘ (castLE_succ_eq_castSucc i ▸ ·)),
    smul_zero, smul_zero, add_zero, smul_eq_mul]

private lemma borderCod_last (y : Y) :
    (borderCod B b lam mu y) (Fin.last k) = (mu : 𝕜) * b y := by
  rw [borderCod, add_apply, PiLp.add_apply, smul_apply, smul_apply,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.smulRight_apply,
    PiLp.smul_apply, PiLp.smul_apply, PiLp.smul_apply, padFin_apply,
    dite_eq_right (by simp), smul_zero, zero_add, PiLp.single_apply, ite_eq_left rfl,
    smul_eq_mul, smul_eq_mul, mul_one]

/-- In `ℓ₂ᵏ⁺¹`, the squared norm splits as the squared norm of the first `k`
coordinates plus the squared modulus of the last one. -/
private lemma norm_sq_projFin_add_last (v : EuclideanSpace 𝕜 (Fin (k + 1))) :
    ‖projFin (p := 2) (Nat.le_succ k) v‖ ^ 2 + ‖v (Fin.last k)‖ ^ 2 = ‖v‖ ^ 2 := by
  have h1 : ‖v‖ ^ 2 = ∑ i : Fin (k + 1), ‖v i‖ ^ 2 := by
    rw [EuclideanSpace.norm_eq, Real.sq_sqrt (Finset.sum_nonneg fun _ _ => sq_nonneg _)]
  have h2 : ‖projFin (p := 2) (Nat.le_succ k) v‖ ^ 2
      = ∑ i : Fin k, ‖v (Fin.castSucc i)‖ ^ 2 := by
    rw [EuclideanSpace.norm_eq, Real.sq_sqrt (Finset.sum_nonneg fun _ _ => sq_nonneg _)]
    exact Finset.sum_congr rfl fun i _ => by
      rw [projFin_apply, castLE_succ_eq_castSucc i]
  rw [h1, h2, Fin.sum_univ_castSucc]

/-- The bordered domain map is a contraction. -/
private lemma norm_borderDom_le (hA : ‖A‖ ≤ 1) (hx : ‖x‖ ≤ 1)
    (hlam : 0 ≤ lam) (hmu : 0 ≤ mu) (hlm : lam ^ 2 + mu ^ 2 = 1) :
    ‖borderDom A x lam mu‖ ≤ 1 := by
  refine ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun v => ?_
  rw [one_mul, borderDom_apply]
  have h1 : ‖(lam : 𝕜) • A (projFin (p := 2) (Nat.le_succ k) v)‖
      ≤ lam * ‖projFin (p := 2) (Nat.le_succ k) v‖ := by
    rw [norm_smul, RCLike.norm_ofReal, abs_of_nonneg hlam]
    have := (A.le_opNorm (projFin (p := 2) (Nat.le_succ k) v)).trans
      (mul_le_of_le_one_left (norm_nonneg _) hA)
    exact mul_le_mul_of_nonneg_left this hlam
  have h2 : ‖((mu : 𝕜) * v (Fin.last k)) • x‖ ≤ mu * ‖v (Fin.last k)‖ := by
    rw [norm_smul, norm_mul, RCLike.norm_ofReal, abs_of_nonneg hmu, mul_assoc]
    exact mul_le_mul_of_nonneg_left (mul_le_of_le_one_right (norm_nonneg _) hx) hmu
  refine (norm_add_le _ _).trans ((add_le_add h1 h2).trans ?_)
  exact lam_mul_add_mu_mul_le hlm (norm_nonneg v) (norm_sq_projFin_add_last v)

/-- The bordered codomain map is a contraction. -/
private lemma norm_borderCod_le (hB : ‖B‖ ≤ 1) (hb : ‖b‖ ≤ 1)
    (hlam : 0 ≤ lam) (hmu : 0 ≤ mu) (hlm : lam ^ 2 + mu ^ 2 = 1) :
    ‖borderCod B b lam mu‖ ≤ 1 := by
  refine ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun y => ?_
  rw [one_mul]
  have hsq : ‖borderCod B b lam mu y‖ ^ 2
      = lam ^ 2 * ‖B y‖ ^ 2 + mu ^ 2 * ‖b y‖ ^ 2 := by
    have h1 : ‖borderCod B b lam mu y‖ ^ 2
        = ∑ i : Fin (k + 1), ‖(borderCod B b lam mu y) i‖ ^ 2 := by
      rw [EuclideanSpace.norm_eq, Real.sq_sqrt (Finset.sum_nonneg fun _ _ => sq_nonneg _)]
    have h2 : ‖B y‖ ^ 2 = ∑ i : Fin k, ‖(B y) i‖ ^ 2 := by
      rw [EuclideanSpace.norm_eq, Real.sq_sqrt (Finset.sum_nonneg fun _ _ => sq_nonneg _)]
    rw [h1, Fin.sum_univ_castSucc, borderCod_last B b lam mu y]
    have h3 : ∀ i : Fin k, ‖(borderCod B b lam mu y) (Fin.castSucc i)‖ ^ 2
        = lam ^ 2 * ‖(B y) i‖ ^ 2 := by
      intro i
      rw [borderCod_castSucc B b lam mu y i, norm_mul, RCLike.norm_ofReal,
        abs_of_nonneg hlam, mul_pow]
    rw [Finset.sum_congr rfl fun i _ => h3 i, ← Finset.mul_sum, ← h2, norm_mul,
      RCLike.norm_ofReal, abs_of_nonneg hmu, mul_pow]
  have hBy : ‖B y‖ ≤ ‖y‖ :=
    (B.le_opNorm y).trans (mul_le_of_le_one_left (norm_nonneg _) hB)
  have hby : ‖b y‖ ≤ ‖y‖ :=
    (b.le_opNorm y).trans (mul_le_of_le_one_left (norm_nonneg _) hb)
  have hsq2 : ‖borderCod B b lam mu y‖ ^ 2 ≤ ‖y‖ ^ 2 := by
    rw [hsq]
    have e1 : lam ^ 2 * ‖B y‖ ^ 2 ≤ lam ^ 2 * ‖y‖ ^ 2 := by
      have := mul_self_le_mul_self (norm_nonneg (B y)) hBy
      nlinarith [sq_nonneg lam]
    have e2 : mu ^ 2 * ‖b y‖ ^ 2 ≤ mu ^ 2 * ‖y‖ ^ 2 := by
      have := mul_self_le_mul_self (norm_nonneg (b y)) hby
      nlinarith [sq_nonneg mu]
    nlinarith [e1, e2]
  exact le_of_sq_le_sq hsq2 (norm_nonneg _)

end Border

/-! ### The growth lemma

The determinant quantities cannot decay faster than the approximation numbers
allow. This is the new ingredient; the matching upper bound
`Δₙ₊₁ ≤ hₙ·Δₙ` is `detNumber_succ_le_hilbertNumber_mul`. -/

/-- **Growth lemma.** For every `S` and every `k`,

  `(kᵏ/(k+1)^{k+1}) · aₖ(S) · Δₖ(S) ≤ Δₖ₊₁(S)`.

Fix an admissible pair `(A, B)` for `Δₖ(S)` and put `T := B∘S∘A`. If
`det T = 0` there is nothing to prove. Otherwise `T` is invertible, so

  `L := S∘A∘T⁻¹∘B∘S`

factors through `ℓ₂ᵏ`, hence has rank at most `k`, hence `‖S - L‖ ≥ aₖ(S)`.
Pick `x ∈ B_X` with `‖(S - L)x‖` almost `‖S - L‖` and a norming functional
`b ∈ B_{Y'}`, and border the pair by them:

  `A₀(ξ ⊕ τ) = λ·Aξ + μ·τ·x`,   `B₀ y = (λ·By) ⊕ (μ·b y)`,

with `λ² + μ² = 1`, which is again a contraction pair, now for `Δₖ₊₁(S)`. Above
the corner, the last column of the matrix of `B₀SA₀` is the combination of the
first `k` columns with coefficients `(μ/λ)·ζ`, where `ζ := T⁻¹B(Sx)`, so
`Matrix.det_eq_corner_mul_det_submatrix` gives

  `det (B₀SA₀) = λ^{2k}·μ²·b((S - L)x)·det T`.

The weights `λ² = k/(k+1)`, `μ² = 1/(k+1)` maximise `λ^{2k}μ²`, whose value is
then exactly `kᵏ/(k+1)^{k+1}`. -/
lemma approximationNumber_mul_detNumber_le_detNumber_succ (S : X →L[𝕜] Y) (k : ℕ) :
    (k : ℝ) ^ k / ((k : ℝ) + 1) ^ (k + 1) * approximationNumber S k * detNumber S k
      ≤ detNumber S (k + 1) := by
  classical
  set cst : ℝ := (k : ℝ) ^ k / ((k : ℝ) + 1) ^ (k + 1) with hcst
  have hcst0 : 0 ≤ cst := (growth_ratio_pos k).le
  -- Every admissible value `r` for `Δₖ(S)` satisfies `cst · aₖ(S) · r ≤ Δₖ₊₁(S)`.
  have hkey : ∀ r ∈ detSet S k, cst * approximationNumber S k * r
      ≤ detNumber S (k + 1) := by
    rintro r ⟨A, B, hA, hB, rfl⟩
    set T : EuclideanSpace 𝕜 (Fin k) →L[𝕜] EuclideanSpace 𝕜 (Fin k) :=
      B.comp (S.comp A) with hTdef
    have hTapp : ∀ z, T z = B (S (A z)) := fun z => by
      rw [hTdef, ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply]
    set rT : ℝ :=
      ‖LinearMap.det (T : EuclideanSpace 𝕜 (Fin k) →ₗ[𝕜] EuclideanSpace 𝕜 (Fin k))‖ with hrT
    -- A singular compression contributes nothing.
    by_cases hdet0 : LinearMap.det
        (T : EuclideanSpace 𝕜 (Fin k) →ₗ[𝕜] EuclideanSpace 𝕜 (Fin k)) = 0
    · rw [hrT, hdet0, norm_zero, mul_zero]
      exact detNumber_nonneg S (k + 1)
    -- The rank-`k` approximant `L = S∘A∘T⁻¹∘B∘S`.
    set E := T.toContinuousLinearEquivOfDetNeZero hdet0 with hEdef
    have hEapp : ∀ z, E z = T z := fun z => by
      rw [hEdef]
      exact ContinuousLinearMap.toContinuousLinearEquivOfDetNeZero_apply T hdet0 z
    set L : X →L[𝕜] Y := (S.comp A).comp
      ((E.symm : EuclideanSpace 𝕜 (Fin k) →L[𝕜] EuclideanSpace 𝕜 (Fin k)).comp
        (B.comp S)) with hLdef
    have hLrank : L.rank ≤ (k : Cardinal) := by
      rw [hLdef]
      exact rank_comp_le_of_euclidean _ _
    have hSL : approximationNumber S k ≤ ‖S - L‖ :=
      approximationNumber_le_norm_sub hLrank
    -- The main estimate, for every `η` strictly below `‖S - L‖`.
    have hinner : ∀ η : ℝ, 0 ≤ η → η < ‖S - L‖ →
        cst * η * rT ≤ detNumber S (k + 1) := by
      intro η hη0 hηlt
      obtain ⟨x, hx1, hxη⟩ := (S - L).exists_lt_apply_of_lt_opNorm hηlt
      obtain ⟨b, hb1, hbval⟩ := exists_dual_vector'' 𝕜 ((S - L) x)
      have hbη : η < ‖b ((S - L) x)‖ := by
        rw [hbval, RCLike.norm_ofReal, abs_of_nonneg (norm_nonneg _)]
        exact hxη
      -- The optimal weights.
      have hk1 : (0 : ℝ) < (k : ℝ) + 1 := by positivity
      set lam : ℝ := Real.sqrt ((k : ℝ) / ((k : ℝ) + 1)) with hlamdef
      set mu : ℝ := Real.sqrt (1 / ((k : ℝ) + 1)) with hmudef
      have hlam0 : 0 ≤ lam := Real.sqrt_nonneg _
      have hmu0 : 0 ≤ mu := Real.sqrt_nonneg _
      have hlam2 : lam ^ 2 = (k : ℝ) / ((k : ℝ) + 1) := Real.sq_sqrt (by positivity)
      have hmu2 : mu ^ 2 = 1 / ((k : ℝ) + 1) := Real.sq_sqrt (by positivity)
      have hlm : lam ^ 2 + mu ^ 2 = 1 := by rw [hlam2, hmu2]; field_simp
      have hcval : lam ^ (2 * k) * mu ^ 2 = cst := by
        rw [pow_mul, hlam2, hmu2, div_pow, div_mul_div_comm, mul_one, hcst, pow_succ]
      -- `lam` is positive as soon as `k ≥ 1`.
      have hlampos : 0 < k → (lam : 𝕜) ≠ 0 := by
        intro hkpos
        have hkR : (0 : ℝ) < (k : ℝ) := by exact_mod_cast hkpos
        have hpos : 0 < lam := by rw [hlamdef]; exact Real.sqrt_pos.mpr (by positivity)
        simpa only [ne_eq, RCLike.ofReal_eq_zero] using hpos.ne'
      -- The bordered pair and the facts about it proved above.
      set A' := borderDom A x lam mu with hA'def
      set B' := borderCod B b lam mu with hB'def
      have hA'cs : ∀ j : Fin k, A' (EuclideanSpace.single (Fin.castSucc j) (1 : 𝕜))
          = (lam : 𝕜) • A (EuclideanSpace.single j (1 : 𝕜)) := fun j => by
        rw [hA'def]; exact borderDom_single_castSucc A x lam mu j
      have hA'last : A' (EuclideanSpace.single (Fin.last k) (1 : 𝕜)) = (mu : 𝕜) • x := by
        rw [hA'def]; exact borderDom_single_last A x lam mu
      have hB'cs : ∀ (y : Y) (i : Fin k),
          (B' y) (Fin.castSucc i) = (lam : 𝕜) * (B y) i := fun y i => by
        rw [hB'def]; exact borderCod_castSucc B b lam mu y i
      have hB'last : ∀ y : Y, (B' y) (Fin.last k) = (mu : 𝕜) * b y := fun y => by
        rw [hB'def]; exact borderCod_last B b lam mu y
      have hA'norm : ‖A'‖ ≤ 1 := by
        rw [hA'def]; exact norm_borderDom_le A x lam mu hA hx1.le hlam0 hmu0 hlm
      have hB'norm : ‖B'‖ ≤ 1 := by
        rw [hB'def]; exact norm_borderCod_le B b lam mu hB hb1 hlam0 hmu0 hlm
      -- The matrices of the two compositions in the standard bases.
      set bk := EuclideanSpace.basisFun (Fin k) 𝕜 with hbk
      set bk1 := EuclideanSpace.basisFun (Fin (k + 1)) 𝕜 with hbk1
      set Nmat := LinearMap.toMatrix bk.toBasis bk.toBasis
        (T : EuclideanSpace 𝕜 (Fin k) →ₗ[𝕜] EuclideanSpace 𝕜 (Fin k)) with hNmat
      set Mmat := LinearMap.toMatrix bk1.toBasis bk1.toBasis
        (B'.comp (S.comp A') :
          EuclideanSpace 𝕜 (Fin (k + 1)) →ₗ[𝕜] EuclideanSpace 𝕜 (Fin (k + 1)))
        with hMmat
      have hMapp : ∀ i j, Mmat i j
          = (B' (S (A' (EuclideanSpace.single j (1 : 𝕜))))) i := by
        intro i j
        rw [hMmat, LinearMap.toMatrix_apply, OrthonormalBasis.coe_toBasis_repr_apply,
          OrthonormalBasis.coe_toBasis, hbk1, EuclideanSpace.basisFun_repr,
          EuclideanSpace.basisFun_apply, ContinuousLinearMap.coe_coe,
          ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply]
      have hNapp : ∀ i j, Nmat i j
          = (B (S (A (EuclideanSpace.single j (1 : 𝕜))))) i := by
        intro i j
        rw [hNmat, LinearMap.toMatrix_apply, OrthonormalBasis.coe_toBasis_repr_apply,
          OrthonormalBasis.coe_toBasis, hbk, EuclideanSpace.basisFun_repr,
          EuclideanSpace.basisFun_apply, ContinuousLinearMap.coe_coe, hTapp]
      -- The four kinds of entries of the bordered matrix.
      have hMcc : ∀ i j : Fin k, Mmat (Fin.castSucc i) (Fin.castSucc j)
          = (lam : 𝕜) ^ 2 * Nmat i j := by
        intro i j
        rw [hMapp, hA'cs j, map_smul, map_smul, PiLp.smul_apply, hB'cs, hNapp,
          smul_eq_mul]
        ring
      have hMlc : ∀ j : Fin k, Mmat (Fin.last k) (Fin.castSucc j)
          = (lam : 𝕜) * (mu : 𝕜) * b (S (A (EuclideanSpace.single j (1 : 𝕜)))) := by
        intro j
        rw [hMapp, hA'cs j, map_smul, map_smul, PiLp.smul_apply, hB'last, smul_eq_mul]
        ring
      have hMcl : ∀ i : Fin k, Mmat (Fin.castSucc i) (Fin.last k)
          = (lam : 𝕜) * (mu : 𝕜) * (B (S x)) i := by
        intro i
        rw [hMapp, hA'last, map_smul, map_smul, PiLp.smul_apply, hB'cs, smul_eq_mul]
        ring
      have hMll : Mmat (Fin.last k) (Fin.last k) = (mu : 𝕜) ^ 2 * b (S x) := by
        rw [hMapp, hA'last, map_smul, map_smul, PiLp.smul_apply, hB'last, smul_eq_mul]
        ring
      -- The coefficients realising the last column as a combination of the others.
      set ζ : EuclideanSpace 𝕜 (Fin k) := E.symm (B (S x)) with hζdef
      have hTζ : T ζ = B (S x) := by
        rw [hζdef, ← hEapp, E.apply_symm_apply]
      have hLx : L x = S (A ζ) := by
        rw [hLdef, hζdef]
        simp only [ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe]
      have hbdiff : b ((S - L) x) = b (S x) - b (S (A ζ)) := by
        rw [sub_apply, hLx, map_sub]
      set w : Fin k → 𝕜 := fun j => ((mu : 𝕜) / (lam : 𝕜)) * ζ j with hwdef
      -- Above the corner, the last column is the `ζ`-combination of the first `k`.
      have hwrel : ∀ i : Fin k, Mmat i.castSucc (Fin.last k)
          = ∑ j, Mmat i.castSucc j.castSucc * w j := by
        intro i
        have hlamne : (lam : 𝕜) ≠ 0 := hlampos i.pos
        have hcoord : (B (S x)) i
            = ∑ j, ζ j * (B (S (A (EuclideanSpace.single j (1 : 𝕜))))) i := by
          rw [← hTζ]
          simpa only [hTapp] using coord_apply_eq_sum T ζ i
        rw [hMcl i, hcoord, Finset.mul_sum]
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [hMcc i j, hNapp i j, hwdef]
        field_simp
      -- The minor at the corner is `λ²` times the old matrix.
      have hsub : Mmat.submatrix Fin.castSucc Fin.castSucc = ((lam : 𝕜) ^ 2) • Nmat := by
        ext i j
        rw [Matrix.submatrix_apply, hMcc i j, Matrix.smul_apply, smul_eq_mul]
      have hminor : (Mmat.submatrix Fin.castSucc Fin.castSucc).det
          = (lam : 𝕜) ^ (2 * k) * Nmat.det := by
        rw [hsub, Matrix.det_smul, Fintype.card_fin, pow_mul]
      -- The corner entry after the column operation is `μ²·b((S - L)x)`.
      have hcorner : Mmat (Fin.last k) (Fin.last k)
            - ∑ j, Mmat (Fin.last k) j.castSucc * w j
          = (mu : 𝕜) ^ 2 * b ((S - L) x) := by
        rw [hMll, hbdiff, mul_sub]
        congr 1
        rcases Nat.eq_zero_or_pos k with rfl | hkpos
        · -- `ℓ₂⁰` is trivial, so `Aζ = 0` and both sides vanish.
          have hζ0 : ζ = 0 := PiLp.ext fun j => j.elim0
          simp [hζ0]
        · have hlamne : (lam : 𝕜) ≠ 0 := hlampos hkpos
          have hbSAζ : b (S (A ζ))
              = ∑ j, ζ j * b (S (A (EuclideanSpace.single j (1 : 𝕜)))) := by
            simpa only [ContinuousLinearMap.comp_apply, smul_eq_mul] using
              clm_apply_eq_sum (b.comp (S.comp A)) ζ
          rw [hbSAζ, Finset.mul_sum]
          refine Finset.sum_congr rfl fun j _ => ?_
          rw [hMlc j, hwdef]
          field_simp
      -- Hence the determinant identity (∗).
      have hdetM : Mmat.det
          = (lam : 𝕜) ^ (2 * k) * (mu : 𝕜) ^ 2 * b ((S - L) x) * Nmat.det := by
        rw [Matrix.det_eq_corner_mul_det_submatrix Mmat w hwrel, hcorner, hminor]
        ring
      have hnormdet : ‖LinearMap.det (B'.comp (S.comp A') :
            EuclideanSpace 𝕜 (Fin (k + 1)) →ₗ[𝕜] EuclideanSpace 𝕜 (Fin (k + 1)))‖
          = cst * ‖b ((S - L) x)‖ * rT := by
        rw [hrT, ← LinearMap.det_toMatrix bk1.toBasis
            (B'.comp (S.comp A') :
              EuclideanSpace 𝕜 (Fin (k + 1)) →ₗ[𝕜] EuclideanSpace 𝕜 (Fin (k + 1))),
          ← LinearMap.det_toMatrix bk.toBasis
            (T : EuclideanSpace 𝕜 (Fin k) →ₗ[𝕜] EuclideanSpace 𝕜 (Fin k)),
          ← hMmat, ← hNmat, hdetM, norm_mul, norm_mul, norm_mul, norm_pow, norm_pow,
          RCLike.norm_ofReal, RCLike.norm_ofReal, abs_of_nonneg hlam0,
          abs_of_nonneg hmu0, ← hcval]
      calc cst * η * rT
          ≤ cst * ‖b ((S - L) x)‖ * rT := by gcongr
        _ = ‖LinearMap.det (B'.comp (S.comp A') :
              EuclideanSpace 𝕜 (Fin (k + 1)) →ₗ[𝕜] EuclideanSpace 𝕜 (Fin (k + 1)))‖ :=
            hnormdet.symm
        _ ≤ detNumber S (k + 1) := norm_det_le_detNumber S hA'norm hB'norm
    -- Let `η ↗ ‖S - L‖`, which is at least `aₖ(S)`.
    have hrT0 : 0 ≤ rT := by rw [hrT]; exact norm_nonneg _
    have hfin : cst * rT * approximationNumber S k ≤ detNumber S (k + 1) := by
      refine mul_le_of_forall_lt_of_nonneg (by positivity)
        (detNumber_nonneg S (k + 1)) ?_
      intro a' ha'0 ha'lt η hη0 hηlt
      calc a' * η ≤ (cst * rT) * η := by gcongr
        _ = cst * η * rT := by ring
        _ ≤ detNumber S (k + 1) := hinner η hη0 (hηlt.trans_le hSL)
    calc cst * approximationNumber S k * rT
        = cst * rT * approximationNumber S k := by ring
      _ ≤ detNumber S (k + 1) := hfin
  -- Pass to the supremum over the admissible values.
  have hsmul : (cst * approximationNumber S k) • detNumber S k ≤ detNumber S (k + 1) := by
    rw [detNumber,
      ← Real.sSup_smul_of_nonneg (mul_nonneg hcst0 (approximationNumber_nonneg S k))]
    refine csSup_le ((detSet_nonempty S k).smul_set) ?_
    rintro y ⟨r, hr, rfl⟩
    simpa using hkey r hr
  simpa using hsmul

/-! ### Positivity of the determinant quantities -/

/-- **Positivity.** If `aₙ(S) > 0` — equivalently, if `S` has rank `> n` — then
`Δₖ(S) > 0` for all `k ≤ n+1`. Induction from `Δ₀(S) = 1` using the growth
lemma, whose factor `aₖ(S) ≥ aₙ(S)` is positive for `k ≤ n` by antitonicity. -/
lemma detNumber_pos_of_approximationNumber_pos (S : X →L[𝕜] Y) {n : ℕ}
    (h : 0 < approximationNumber S n) : ∀ k, k ≤ n + 1 → 0 < detNumber S k := by
  intro k
  induction k with
  | zero => intro _; rw [detNumber_zero]; exact one_pos
  | succ m ih =>
    intro hm
    have hm' : m ≤ n := Nat.lt_succ_iff.mp hm
    have ham : 0 < approximationNumber S m :=
      h.trans_le (approximationNumber_antitone' hm')
    have hpos : 0 < (m : ℝ) ^ m / ((m : ℝ) + 1) ^ (m + 1) *
        approximationNumber S m * detNumber S m :=
      mul_pos (mul_pos (growth_ratio_pos m) ham) (ih (hm'.trans (Nat.le_succ n)))
    exact hpos.trans_le (approximationNumber_mul_detNumber_le_detNumber_succ S m)

/-! ### The maximal difference theorem -/

/-- **`aₙ(S) ≤ ((n+1)^{n+1}/nⁿ)·hₙ(S)`**, the maximal difference theorem
with the sharp form of the constant.
Chaining the growth lemma at `k = n` with the upper bound
`Δₙ₊₁(S) ≤ hₙ(S)·Δₙ(S)` gives

  `(nⁿ/(n+1)^{n+1})·aₙ(S)·Δₙ(S) ≤ Δₙ₊₁(S) ≤ hₙ(S)·Δₙ(S)`,

and `Δₙ(S) > 0` may be cancelled. -/
theorem approximationNumber_le_mul_hilbertNumber (S : X →L[𝕜] Y) (n : ℕ) :
    approximationNumber S n
      ≤ ((n : ℝ) + 1) ^ (n + 1) / (n : ℝ) ^ n * hilbertNumber S n := by
  rcases le_or_gt (approximationNumber S n) 0 with hle | hpos
  · exact hle.trans (mul_nonneg (div_nonneg (by positivity) (pow_self_pos n).le)
      (hilbertNumber_nonneg S n))
  -- The determinant quantities are positive, so the chain can be divided by `Δₙ(S)`.
  have hΔ : 0 < detNumber S n :=
    detNumber_pos_of_approximationNumber_pos S hpos n (Nat.le_succ n)
  have hchain : (n : ℝ) ^ n / ((n : ℝ) + 1) ^ (n + 1) * approximationNumber S n *
      detNumber S n ≤ hilbertNumber S n * detNumber S n :=
    (approximationNumber_mul_detNumber_le_detNumber_succ S n).trans
      (detNumber_succ_le_hilbertNumber_mul S n)
  have hkey : (n : ℝ) ^ n / ((n : ℝ) + 1) ^ (n + 1) * approximationNumber S n
      ≤ hilbertNumber S n := le_of_mul_le_mul_right hchain hΔ
  -- Rearrange.
  rw [div_mul_eq_mul_div,
    div_le_iff₀ (pow_pos (by positivity : (0 : ℝ) < (n : ℝ) + 1) (n + 1))] at hkey
  rw [div_mul_eq_mul_div, le_div_iff₀ (pow_self_pos n)]
  calc approximationNumber S n * (n : ℝ) ^ n
      = (n : ℝ) ^ n * approximationNumber S n := mul_comm _ _
    _ ≤ hilbertNumber S n * ((n : ℝ) + 1) ^ (n + 1) := hkey
    _ = ((n : ℝ) + 1) ^ (n + 1) * hilbertNumber S n := mul_comm _ _

/-- **Maximal difference theorem.** `aₙ(S) ≤ e·(n+1)·hₙ(S)`: the
approximation numbers — the largest s-numbers — exceed the Hilbert numbers —
the smallest ones — by at most a factor linear in `n`. -/
theorem approximationNumber_le_e_mul_hilbertNumber (S : X →L[𝕜] Y) (n : ℕ) :
    approximationNumber S n ≤ Real.exp 1 * ((n : ℝ) + 1) * hilbertNumber S n :=
  (approximationNumber_le_mul_hilbertNumber S n).trans
    (mul_le_mul_of_nonneg_right (ratio_le_exp_mul n) (hilbertNumber_nonneg S n))

/-- **`aₙ(S) ≤ e·(n+1)·sₙ(S)` for every s-number sequence `s`**, since the
Hilbert numbers are the smallest s-number sequence (`hilbertNumber_le_sn`). -/
theorem approximationNumber_le_e_mul_sn {s : Family 𝕜} (hs : IsSNumberSequence s)
    (S : X →L[𝕜] Y) (n : ℕ) :
    approximationNumber S n ≤ Real.exp 1 * ((n : ℝ) + 1) * s S n :=
  (approximationNumber_le_e_mul_hilbertNumber S n).trans
    (mul_le_mul_of_nonneg_left (hilbertNumber_le_sn hs S n) (by positivity))

/-- **Maximal difference theorem for arbitrary s-numbers.**
`sₙ(S) ≤ e·(n+1)·tₙ(S)`: any two s-number sequences differ at most by a
factor linear in `n`. Bound `s` by the largest s-numbers `aₙ`
(`sn_le_approximationNumber`) and then apply the theorem to `t`. -/
theorem sn_le_e_mul_tn {s t : Family 𝕜} (hs : IsSNumberSequence s)
    (ht : IsSNumberSequence t) (S : X →L[𝕜] Y) (n : ℕ) :
    s S n ≤ Real.exp 1 * ((n : ℝ) + 1) * t S n :=
  (sn_le_approximationNumber hs S n).trans
    (approximationNumber_le_e_mul_sn ht S n)

/-! ### Gelfand and Kolmogorov numbers

The Gelfand and Kolmogorov numbers are s-number sequences, so they are bounded
by the approximation numbers, and the maximal difference theorem specialises
to them. -/

/-- `cₙ(S) ≤ aₙ(S)`: the Gelfand numbers are an s-number sequence, and the
approximation numbers are the largest one (`sn_le_approximationNumber`). -/
lemma gelfandNumber_le_approximationNumber (S : X →L[𝕜] Y) (n : ℕ) :
    gelfandNumber S n ≤ approximationNumber S n :=
  sn_le_approximationNumber isSNumberSequence_gelfandNumber S n

/-- `dₙ(S) ≤ aₙ(S)`: the Kolmogorov numbers are an s-number sequence, and the
approximation numbers are the largest one (`sn_le_approximationNumber`). -/
lemma kolmogorovNumber_le_approximationNumber (S : X →L[𝕜] Y) (n : ℕ) :
    kolmogorovNumber S n ≤ approximationNumber S n :=
  sn_le_approximationNumber isSNumberSequence_kolmogorovNumber S n

/-- **The bound for the Gelfand and Kolmogorov numbers.** Both are s-number
sequences, so both are bounded by `aₙ`, to which
`approximationNumber_le_e_mul_sn` applies:
`max(cₙ(S), dₙ(S)) ≤ e·(n+1)·sₙ(S)` for every s-number sequence `s`. -/
theorem max_gelfandNumber_kolmogorovNumber_le_e_mul_sn {s : Family 𝕜}
    (hs : IsSNumberSequence s) (S : X →L[𝕜] Y) (n : ℕ) :
    max (gelfandNumber S n) (kolmogorovNumber S n)
      ≤ Real.exp 1 * ((n : ℝ) + 1) * s S n :=
  max_le
    ((gelfandNumber_le_approximationNumber S n).trans
      (approximationNumber_le_e_mul_sn hs S n))
    ((kolmogorovNumber_le_approximationNumber S n).trans
      (approximationNumber_le_e_mul_sn hs S n))

/-- `max(cₙ(S), dₙ(S)) ≤ e·(n+1)·hₙ(S)`: the Gelfand and Kolmogorov numbers
exceed the smallest s-numbers `hₙ` by at most a factor linear in `n`. -/
theorem max_gelfandNumber_kolmogorovNumber_le_e_mul_hilbertNumber
    (S : X →L[𝕜] Y) (n : ℕ) :
    max (gelfandNumber S n) (kolmogorovNumber S n)
      ≤ Real.exp 1 * ((n : ℝ) + 1) * hilbertNumber S n :=
  max_gelfandNumber_kolmogorovNumber_le_e_mul_sn
    isSNumberSequence_hilbertNumber S n

/-- **The Mityagin–Henkin conjecture, up to the constant `e`.** The Gelfand
and Kolmogorov numbers are bounded by the Bernstein numbers:
`max(cₙ(S), dₙ(S)) ≤ e·(n+1)·bₙ(S)`. -/
theorem max_gelfandNumber_kolmogorovNumber_le_e_mul_bernsteinNumber
    (S : X →L[𝕜] Y) (n : ℕ) :
    max (gelfandNumber S n) (kolmogorovNumber S n)
      ≤ Real.exp 1 * ((n : ℝ) + 1) * bernsteinNumber S n :=
  max_gelfandNumber_kolmogorovNumber_le_e_mul_sn
    isSNumberSequence_bernsteinNumber S n

end SNumbers

/- Adapted for Lean Pool: module imports and compatibility with its pinned toolchain. -/
