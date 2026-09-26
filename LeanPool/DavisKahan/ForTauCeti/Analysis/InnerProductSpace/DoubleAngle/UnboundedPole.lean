/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, Claude Opus 5
-/
module

public import LeanPool.DavisKahan.ForTauCeti.Analysis.InnerProductSpace.DoubleAngle.UnboundedReflection

/-!
# The pole of `tan 2Θ₀` cannot occur

Let `A` be reduced by `U`, with quadratic form at most `a` on `U` and at least
`b > a` on `Uᗮ`, let `B` be bounded and fully off-diagonal, and let `Z` be a
self-adjoint involution commuting with `A + B` on `D(A)`.  Write

* `C := U.diagonalPart Z`  — blockwise `diag (cos 2Θ₀, -cos 2Θ₁)`;
* `S := U.offDiagonalPart Z` — blockwise the cross block `G`, `|G| = sin 2Θ₀`.

This module proves that the cross block is *uniformly* separated from `1`:

`‖S x‖ ≤ (2‖B‖ / √(δ² + 4‖B‖²)) ‖x‖`   for `x ∈ U`,   `δ := b - a`,

and hence `|cos 2Θ₀| ≥ κ` with the explicit constant

`κ = δ / √(δ² + 4‖B‖²) > 0`.

**The pole at `sin 2Θ₀ = 1` is therefore excluded as a theorem, with an explicit
constant, before `tan 2Θ₀` is ever defined** — the tangent's denominator
`|cos 2Θ₀| = √(1 - G⋆G)` is bounded below from the start rather than by
hypothesis.

## Method

The only place the unboundedness of `A` can hurt is the term `⟪A x, r⟫` produced
when the near-maximiser `x` of `‖S ·‖` fails to be an exact maximiser.  It is
controlled by choosing `x` inside a bounded spectral cutoff `Ω` of `A`: the
leakage `r` is then tested against `Ω r`, whose size is *geometric* (it is
`√(m² - q²)` for `m` the norm on the cutoff and `q = ‖S x‖`), while `‖A x‖ ≤ τ`
is finite.  Freezing `τ` and letting the near-maximisation error go to zero
kills the product; only then is `τ → ∞` taken.  The cutoff data is packaged as
`TauCeti.BoundedCutoff`.

## Main results

* `TauCeti.sylvester_pairing_le`: the engine, equation (7.6) paired with the
  matching left vector at a near-maximiser.
* `TauCeti.norm_sq_cutoff_leak_le`: the leakage of a near-maximiser is purely
  geometric.
* `TauCeti.opNorm_offDiagonalPart_comp_le`: the estimate on a single cutoff.
* `TauCeti.norm_offDiagonalPart_apply_le_of_tendsto`: the estimate on all of
  `U`, after `τ → ∞`.
* `TauCeti.norm_offDiagonalPart_le_of_tendsto` and
  `TauCeti.norm_offDiagonalPart_lt_one_of_tendsto`: the same estimate as a bound
  on the *operator* norm of the cross block, hence `‖S‖ < 1`.  The step from `U`
  to the whole space is adjointness: `S` is self-adjoint and exchanges `U` and
  `Uᗮ`, so its `Uᗮ` block is the adjoint of its `U` block.
* `TauCeti.diagonalBlockBound_mul_le_norm_diagonalPart_apply` and
  `…_of_tendsto`: the pole exclusion `κ ‖x‖ ≤ ‖C x‖`.

## References

* C. Davis and W. M. Kahan, *The rotation of eigenvectors by a perturbation.
  III*, SIAM J. Numer. Anal. 7 (1970), 1--46, Section 7 and the Appendix to
  Section 6.
-/

@[expose] public section

namespace TauCeti

open scoped InnerProductSpace

section ScalarGeneric

variable {𝕜 : Type*} [RCLike 𝕜]
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace 𝕜 H]
  [CompleteSpace H]

/-- **A bounded low-energy cutoff.**  An orthogonal projection whose range lies
in `U` and in `D(A)`, is invariant under `A`, and on which `A` is bounded by
`τ`.

Every field is an identity or an inequality between vectors of `H` and real
numbers, so the structure is stated for an arbitrary `RCLike` scalar field.  The
*construction* of a cutoff from a projection-valued measure is complex-only, but
the data itself is not, and a real cutoff is transported to the complexification
coordinatewise.

The intended instance — `A` self-adjoint, `U = specRange hA (Iic a)`, and
`toProj = specProjection hA (Icc (-τ) a)` — is **not constructed here**; the
results below consume this data rather than produce it.  Its four substantive
fields would come from `specProjection_mem_domain`,
`mem_domain_of_mem_specRange_of_bounded`, `norm_sub_smul_le_of_mem_specRange`
and `specProjection_apply_domain`, with `mem_subspace` from the product rule
for spectral projections. -/
structure BoundedCutoff (A : H →ₗ.[𝕜] H) (U : Submodule 𝕜 H) (τ : ℝ) where
  /-- The underlying projection. -/
  toProj : H →L[𝕜] H
  /-- The projection is self-adjoint. -/
  isSelfAdjoint : IsSelfAdjoint toProj
  /-- The projection is idempotent. -/
  isIdempotentElem : IsIdempotentElem toProj
  /-- Its range lies in `U`. -/
  mem_subspace : ∀ v, toProj v ∈ U
  /-- Its range lies in the domain of `A`. -/
  mem_domain : ∀ v, toProj v ∈ A.domain
  /-- On its range `A` is bounded by `τ`. -/
  norm_apply_le : ∀ v, ‖A ⟨toProj v, mem_domain v⟩‖ ≤ τ * ‖toProj v‖
  /-- Its range is invariant under `A`. -/
  apply_mem_range : ∀ v,
    toProj (A ⟨toProj v, mem_domain v⟩) = A ⟨toProj v, mem_domain v⟩

/-- Self-adjointness of a bounded operator, in inner-product form. -/
theorem inner_swap_of_isSelfAdjoint {T : H →L[𝕜] H} (hT : IsSelfAdjoint T)
    (u v : H) : ⟪T u, v⟫_𝕜 = ⟪u, T v⟫_𝕜 :=
  ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp hT u v

namespace BoundedCutoff

variable {A : H →ₗ.[𝕜] H} {U : Submodule 𝕜 H} {τ : ℝ}

/-- A fixed vector of the cutoff lies in the domain. -/
theorem mem_domain_of_eq (Ω : BoundedCutoff A U τ) {x : H} (hx : Ω.toProj x = x) :
    x ∈ A.domain := hx ▸ Ω.mem_domain x

/-- A fixed vector of the cutoff lies in `U`. -/
theorem mem_subspace_of_eq (Ω : BoundedCutoff A U τ) {x : H}
    (hx : Ω.toProj x = x) : x ∈ U := hx ▸ Ω.mem_subspace x

/-- The cutoff is idempotent, pointwise. -/
theorem toProj_apply_toProj (Ω : BoundedCutoff A U τ) (v : H) :
    Ω.toProj (Ω.toProj v) = Ω.toProj v := by
  have h := congrArg (fun T : H →L[𝕜] H => T v) Ω.isIdempotentElem.eq
  simpa using h

/-- An orthogonal projection is a contraction. -/
theorem norm_toProj_apply_le (Ω : BoundedCutoff A U τ) (v : H) :
    ‖Ω.toProj v‖ ≤ ‖v‖ := by
  rcases eq_or_lt_of_le (norm_nonneg (Ω.toProj v)) with h0 | h0
  · rw [← h0]; exact norm_nonneg v
  · have hsym := inner_swap_of_isSelfAdjoint Ω.isSelfAdjoint
    have hid : ⟪Ω.toProj v, Ω.toProj v⟫_𝕜 = ⟪v, Ω.toProj v⟫_𝕜 := by
      rw [hsym v (Ω.toProj v), Ω.toProj_apply_toProj]
    have h1 : ‖Ω.toProj v‖ ^ 2 = RCLike.re ⟪v, Ω.toProj v⟫_𝕜 := by
      rw [← hid, inner_self_eq_norm_sq]
    have h2 : ‖Ω.toProj v‖ ^ 2 ≤ ‖v‖ * ‖Ω.toProj v‖ := by
      rw [h1]
      exact (RCLike.re_le_norm _).trans (norm_inner_le_norm (𝕜 := 𝕜) v (Ω.toProj v))
    nlinarith [h2, h0]

end BoundedCutoff

end ScalarGeneric

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H]

/-- A self-adjoint involution preserves norms. -/
theorem norm_apply_of_isSelfAdjoint_of_mul_self {Z : H →L[ℂ] H}
    (hZsa : IsSelfAdjoint Z) (hZ2 : Z * Z = 1) (v : H) : ‖Z v‖ = ‖v‖ := by
  have hZsym := inner_swap_of_isSelfAdjoint hZsa
  have hZZ : Z (Z v) = v := by
    have h := congrArg (fun T : H →L[ℂ] H => T v) hZ2
    simpa using h
  have h : ⟪Z v, Z v⟫_ℂ = ⟪v, v⟫_ℂ := by rw [hZsym v (Z v), hZZ]
  rw [inner_self_eq_norm_sq_to_K, inner_self_eq_norm_sq_to_K] at h
  have h2 : ‖Z v‖ ^ 2 = ‖v‖ ^ 2 := by exact_mod_cast h
  rw [← Real.sqrt_sq (norm_nonneg (Z v)), h2, Real.sqrt_sq (norm_nonneg v)]

/-- `√(u + v) ≤ √u + √v`. -/
private theorem sqrt_add_le_sqrt_add_sqrt {u v : ℝ} (hu : 0 ≤ u) (hv : 0 ≤ v) :
    √(u + v) ≤ √u + √v := by
  calc √(u + v) ≤ √((√u + √v) ^ 2) := by
        refine Real.sqrt_le_sqrt ?_
        nlinarith [Real.sq_sqrt hu, Real.sq_sqrt hv, Real.sqrt_nonneg u,
          Real.sqrt_nonneg v]
    _ = √u + √v := Real.sqrt_sq (by positivity)

/-- The pole-exclusion bound on the cross block. -/
noncomputable def crossBlockBound (δ nB : ℝ) : ℝ :=
  2 * nB / √(δ ^ 2 + 4 * nB ^ 2)

/-- The pole-exclusion bound on the diagonal block. -/
noncomputable def diagonalBlockBound (δ nB : ℝ) : ℝ :=
  δ / √(δ ^ 2 + 4 * nB ^ 2)

/-- Unfolding lemma for `crossBlockBound`. -/
theorem crossBlockBound_eq (δ nB : ℝ) :
    crossBlockBound δ nB = 2 * nB / √(δ ^ 2 + 4 * nB ^ 2) := by
  simp only [crossBlockBound]

/-- Unfolding lemma for `diagonalBlockBound`. -/
theorem diagonalBlockBound_eq (δ nB : ℝ) :
    diagonalBlockBound δ nB = δ / √(δ ^ 2 + 4 * nB ^ 2) := by
  simp only [diagonalBlockBound]

/-- The cross-block bound is nonnegative. -/
theorem crossBlockBound_nonneg {δ nB : ℝ} (hnB : 0 ≤ nB) :
    0 ≤ crossBlockBound δ nB := by
  rw [crossBlockBound_eq]
  positivity

/-- **The cross-block bound is a strict contraction.**  `2β < √(δ² + 4β²)` as
soon as the gap `δ` is positive, with no smallness assumption on `β = ‖B‖`: this
is why the pole exclusion never needs a hypothesis relating `‖B‖` to the gap. -/
theorem crossBlockBound_lt_one {δ nB : ℝ} (hδ : 0 < δ) (hnB : 0 ≤ nB) :
    crossBlockBound δ nB < 1 := by
  have hD : (0 : ℝ) < √(δ ^ 2 + 4 * nB ^ 2) := Real.sqrt_pos.mpr (by positivity)
  have hD2 : √(δ ^ 2 + 4 * nB ^ 2) ^ 2 = δ ^ 2 + 4 * nB ^ 2 :=
    Real.sq_sqrt (by positivity)
  rw [crossBlockBound_eq, div_lt_one hD]
  nlinarith [hD, hD2, hnB, hδ]

/-- The scalar step from the cross-block bound to the diagonal-block bound:
`c² + s² = n²` and `s ≤ (2β/D) n` give `(δ/D) n ≤ c`, where `D² = δ² + 4β²`. -/
private theorem diagonalBlockBound_le_of_cross {δ nB s nx nC : ℝ} (hδ : 0 < δ)
    (hnx : 0 ≤ nx) (hs : s ≤ crossBlockBound δ nB * nx) (hs0 : 0 ≤ s)
    (hnC : 0 ≤ nC) (hpy : nC ^ 2 + s ^ 2 = nx ^ 2) :
    diagonalBlockBound δ nB * nx ≤ nC := by
  set D : ℝ := √(δ ^ 2 + 4 * nB ^ 2) with hDdef
  have hDpos : 0 < D := Real.sqrt_pos.mpr (by positivity)
  have hD2 : D ^ 2 = δ ^ 2 + 4 * nB ^ 2 := Real.sq_sqrt (by positivity)
  rw [crossBlockBound_eq, ← hDdef] at hs
  rw [diagonalBlockBound_eq, ← hDdef]
  have hssq : s ^ 2 ≤ 4 * nB ^ 2 / D ^ 2 * nx ^ 2 := by
    have h1 : s ^ 2 ≤ (2 * nB / D * nx) ^ 2 := by gcongr
    have h2 : (2 * nB / D * nx) ^ 2 = 4 * nB ^ 2 / D ^ 2 * nx ^ 2 := by
      rw [mul_pow, div_pow]
      ring
    rw [← h2]
    exact h1
  have hfrac : 4 * nB ^ 2 / D ^ 2 + δ ^ 2 / D ^ 2 = 1 := by
    rw [hD2]
    field_simp
    ring
  have hsplit : 4 * nB ^ 2 / D ^ 2 * nx ^ 2 + δ ^ 2 / D ^ 2 * nx ^ 2 = nx ^ 2 := by
    rw [← add_mul, hfrac, one_mul]
  have hkey : (δ / D * nx) ^ 2 ≤ nC ^ 2 := by
    have hexp : (δ / D * nx) ^ 2 = δ ^ 2 / D ^ 2 * nx ^ 2 := by
      rw [mul_pow, div_pow]
    rw [hexp]
    linarith [hpy, hssq, hsplit]
  calc δ / D * nx = √((δ / D * nx) ^ 2) := (Real.sqrt_sq (by positivity)).symm
    _ ≤ √(nC ^ 2) := Real.sqrt_le_sqrt hkey
    _ = nC := Real.sqrt_sq hnC

/-- **The tangent form of the cross-block bound.**  `c² + s² = n²` together with
`s ≤ (2β/D) n`, `D² = δ² + 4β²`, is *equivalent* to `δ s ≤ 2 β c`: the
pole-exclusion bound and the branch-free double-angle tangent inequality are the
same statement, rearranged.  This is why excluding the pole already proves the
operator-norm case of the `tan 2Θ` theorem. -/
private theorem gap_mul_le_of_cross {δ nB s nx nC : ℝ} (hnB : 0 ≤ nB)
    (hs : s ≤ crossBlockBound δ nB * nx) (hs0 : 0 ≤ s)
    (hnC : 0 ≤ nC) (hpy : nC ^ 2 + s ^ 2 = nx ^ 2) (hδ : 0 < δ) :
    δ * s ≤ 2 * nB * nC := by
  set D : ℝ := √(δ ^ 2 + 4 * nB ^ 2) with hDdef
  have hDpos : 0 < D := Real.sqrt_pos.mpr (by positivity)
  have hD2 : D ^ 2 = δ ^ 2 + 4 * nB ^ 2 := Real.sq_sqrt (by positivity)
  rw [crossBlockBound_eq, ← hDdef] at hs
  have hssq : s ^ 2 ≤ 4 * nB ^ 2 / D ^ 2 * nx ^ 2 := by
    have h1 : s ^ 2 ≤ (2 * nB / D * nx) ^ 2 := by gcongr
    have h2 : (2 * nB / D * nx) ^ 2 = 4 * nB ^ 2 / D ^ 2 * nx ^ 2 := by
      rw [mul_pow, div_pow]
      ring
    rw [← h2]
    exact h1
  have hmul : s ^ 2 * D ^ 2 ≤ 4 * nB ^ 2 * nx ^ 2 := by
    have := mul_le_mul_of_nonneg_right hssq (le_of_lt (by positivity : (0:ℝ) < D ^ 2))
    calc s ^ 2 * D ^ 2 ≤ 4 * nB ^ 2 / D ^ 2 * nx ^ 2 * D ^ 2 := this
      _ = 4 * nB ^ 2 * nx ^ 2 := by field_simp
  have hsq : (δ * s) ^ 2 ≤ (2 * nB * nC) ^ 2 := by
    rw [hD2] at hmul
    nlinarith [hmul, hpy]
  calc δ * s = √((δ * s) ^ 2) := (Real.sqrt_sq (by positivity)).symm
    _ ≤ √((2 * nB * nC) ^ 2) := Real.sqrt_le_sqrt hsq
    _ = 2 * nB * nC := Real.sqrt_sq (by positivity)

section Leak

variable {U : Submodule ℂ H} [U.HasOrthogonalProjection] {A : H →ₗ.[ℂ] H}
  {Z : H →L[ℂ] H} {τ : ℝ}

/-- **The leakage of a near-maximiser is purely geometric.**

If `x` is a unit vector of the cutoff range and `q = ‖S x‖`, then the part of
`r = S y - q x` seen by the cutoff has size at most `√(m² - q²)`, where
`m = ‖S Ω‖` is the largest value of `‖S ·‖` on the cutoff range.  **No bound on
`A` enters**: this is Cauchy--Schwarz for the positive operator `Ω S² Ω` at a
vector where its form is nearly maximal. -/
theorem norm_sq_cutoff_leak_le (hZsa : IsSelfAdjoint Z)
    (Ω : BoundedCutoff A U τ) {x : H} (hxΩ : Ω.toProj x = x) (hx1 : ‖x‖ = 1)
    (hq : 0 < ‖U.offDiagonalPart Z x‖) :
    ‖Ω.toProj (U.offDiagonalPart Z
        (((‖U.offDiagonalPart Z x‖ : ℝ) : ℂ)⁻¹ • U.offDiagonalPart Z x) -
          ((‖U.offDiagonalPart Z x‖ : ℝ) : ℂ) • x)‖ ^ 2 ≤
      ‖U.offDiagonalPart Z ∘L Ω.toProj‖ ^ 2 - ‖U.offDiagonalPart Z x‖ ^ 2 := by
  classical
  set S : H →L[ℂ] H := U.offDiagonalPart Z with hSdef
  set q : ℝ := ‖S x‖ with hqdef
  set y : H := ((q : ℝ) : ℂ)⁻¹ • S x with hydef
  set r : H := S y - ((q : ℝ) : ℂ) • x with hrdef
  set m : ℝ := ‖S ∘L Ω.toProj‖ with hmdef
  have hSsa : IsSelfAdjoint S := isSelfAdjoint_offDiagonalPart hZsa
  have hSsym := inner_swap_of_isSelfAdjoint hSsa
  have hΩsym := inner_swap_of_isSelfAdjoint Ω.isSelfAdjoint
  have hinner_self : ∀ v : H, ⟪v, v⟫_ℂ = ((‖v‖ ^ 2 : ℝ) : ℂ) := by
    intro v
    rw [inner_self_eq_norm_sq_to_K]
    norm_cast
  have hqne : ((q : ℝ) : ℂ) ≠ 0 := by
    simpa only [ne_eq, Complex.ofReal_eq_zero] using hq.ne'
  have hSxy : ((q : ℝ) : ℂ) • y = S x := by rw [hydef, smul_inv_smul₀ hqne]
  -- the compressed operator norm bounds `Ω S`
  have hN : ∀ v : H, ‖S (Ω.toProj v)‖ ≤ m * ‖v‖ := by
    intro v
    have h := (S ∘L Ω.toProj).le_opNorm v
    rwa [ContinuousLinearMap.comp_apply] at h
  have hNadj : ∀ u : H, ‖Ω.toProj (S u)‖ ≤ m * ‖u‖ := by
    intro u
    rcases eq_or_lt_of_le (norm_nonneg (Ω.toProj (S u))) with hw0 | hw0
    · have hm0 : 0 ≤ m := norm_nonneg _
      rw [← hw0]
      positivity
    · have hid : ⟪Ω.toProj (S u), Ω.toProj (S u)⟫_ℂ =
          ⟪u, S (Ω.toProj (Ω.toProj (S u)))⟫_ℂ := by
        rw [hΩsym, ← hSsym u]
      have hbound : ‖Ω.toProj (S u)‖ ^ 2 ≤ ‖u‖ * (m * ‖Ω.toProj (S u)‖) := by
        have h1 : ((‖Ω.toProj (S u)‖ ^ 2 : ℝ) : ℂ) =
            ⟪u, S (Ω.toProj (Ω.toProj (S u)))⟫_ℂ := by rw [← hinner_self, hid]
        have h2 : ‖((‖Ω.toProj (S u)‖ ^ 2 : ℝ) : ℂ)‖ ≤
            ‖u‖ * ‖S (Ω.toProj (Ω.toProj (S u)))‖ := by
          rw [h1]; exact norm_inner_le_norm _ _
        have h3 : ‖S (Ω.toProj (Ω.toProj (S u)))‖ ≤ m * ‖Ω.toProj (S u)‖ :=
          hN (Ω.toProj (S u))
        rw [Complex.norm_real, Real.norm_eq_abs,
          abs_of_nonneg (by positivity : (0:ℝ) ≤ ‖Ω.toProj (S u)‖ ^ 2)] at h2
        exact h2.trans (mul_le_mul_of_nonneg_left h3 (norm_nonneg u))
      nlinarith [hbound, hw0]
  -- the near-eigenvector estimate
  have hw : ⟪Ω.toProj (S (S x)), x⟫_ℂ = ((q ^ 2 : ℝ) : ℂ) := by
    rw [hΩsym, hxΩ, hSsym, hinner_self, ← hqdef]
  have hwnorm : ‖Ω.toProj (S (S x))‖ ≤ m * q := by
    have := hNadj (S x)
    rwa [← hqdef] at this
  have hkey : ((q : ℝ) : ℂ) • Ω.toProj r =
      Ω.toProj (S (S x)) - ((q ^ 2 : ℝ) : ℂ) • x := by
    have e1 : ((q : ℝ) : ℂ) • Ω.toProj (S y) = Ω.toProj (S (S x)) := by
      rw [← map_smul, ← map_smul, hSxy]
    have e2 : ((q : ℝ) : ℂ) • Ω.toProj (((q : ℝ) : ℂ) • x) =
        ((q ^ 2 : ℝ) : ℂ) • x := by
      rw [map_smul, hxΩ, smul_smul]
      congr 1
      push_cast
      ring
    rw [hrdef, map_sub, smul_sub, e1, e2]
  have hexp : ‖Ω.toProj (S (S x)) - ((q ^ 2 : ℝ) : ℂ) • x‖ ^ 2 =
      ‖Ω.toProj (S (S x))‖ ^ 2 - q ^ 4 := by
    have hinner : ⟪Ω.toProj (S (S x)), ((q ^ 2 : ℝ) : ℂ) • x⟫_ℂ =
        ((q ^ 2 * q ^ 2 : ℝ) : ℂ) := by
      rw [inner_smul_right, hw]
      push_cast
      ring
    rw [@norm_sub_sq ℂ, hinner, norm_smul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (by positivity : (0:ℝ) ≤ q ^ 2), hx1, mul_one]
    have hre : RCLike.re ((q ^ 2 * q ^ 2 : ℝ) : ℂ) = q ^ 2 * q ^ 2 :=
      Complex.ofReal_re _
    rw [hre]
    ring
  have hqnorm : ‖((q : ℝ) : ℂ) • Ω.toProj r‖ ^ 2 = q ^ 2 * ‖Ω.toProj r‖ ^ 2 := by
    rw [norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hq, mul_pow]
  have hfinal : q ^ 2 * ‖Ω.toProj r‖ ^ 2 ≤ q ^ 2 * (m ^ 2 - q ^ 2) := by
    rw [← hqnorm, hkey, hexp]
    nlinarith [hwnorm, norm_nonneg (Ω.toProj (S (S x))), hq.le, norm_nonneg S]
  have hq2 : 0 < q ^ 2 := by positivity
  exact le_of_mul_le_mul_left (by linarith [hfinal]) hq2

end Leak

section Estimate

variable {U : Submodule ℂ H} [U.HasOrthogonalProjection] {A : H →ₗ.[ℂ] H}
  {B Z : H →L[ℂ] H} {a b τ : ℝ}

variable (hred : LinearPMap.ReducesSubspace A U) (hB : IsOddFor U B)
  (hZsa : IsSelfAdjoint Z) (hZ2 : Z * Z = 1)
  (hZdom : LinearPMap.MapsDomainTo A A Z)
  (hZcomm : ∀ x : A.domain,
    A ⟨Z (x : H), hZdom x⟩ + B (Z (x : H)) = Z (A x) + Z (B (x : H)))
  (hUa : ∀ x : A.domain, (x : H) ∈ U →
    (⟪A x, (x : H)⟫_ℂ).re ≤ a * ‖(x : H)‖ ^ 2)
  (hUb : ∀ x : A.domain, (x : H) ∈ Uᗮ →
    b * ‖(x : H)‖ ^ 2 ≤ (⟪A x, (x : H)⟫_ℂ).re)

include hred hB hZsa hZ2 hZdom hZcomm hUa hUb

/-- **The engine, at a near-maximising unit vector.**

If `x` is a unit vector fixed by the cutoff and `q = ‖S x‖ > 0`, then

`(b - a) q ≤ 2 ‖B‖ √(1 - q²) + τ ‖Ω r‖`,   `r = S y - q x`,   `y = q⁻¹ S x`.

Every unbounded contribution has been absorbed into the single term `⟪A x, r⟫`,
and that term is tested against `Ω r` because `A x` is fixed by `Ω`. -/
theorem sylvester_pairing_le (Ω : BoundedCutoff A U τ) {x : H}
    (hxΩ : Ω.toProj x = x) (hx1 : ‖x‖ = 1) (hq : 0 < ‖U.offDiagonalPart Z x‖) :
    (b - a) * ‖U.offDiagonalPart Z x‖ ≤
      2 * ‖B‖ * √(1 - ‖U.offDiagonalPart Z x‖ ^ 2) +
        τ * ‖Ω.toProj (U.offDiagonalPart Z
          (((‖U.offDiagonalPart Z x‖ : ℝ) : ℂ)⁻¹ • U.offDiagonalPart Z x) -
            ((‖U.offDiagonalPart Z x‖ : ℝ) : ℂ) • x)‖ := by
  classical
  set S : H →L[ℂ] H := U.offDiagonalPart Z with hSdef
  set C : H →L[ℂ] H := U.diagonalPart Z with hCdef
  set q : ℝ := ‖S x‖ with hqdef
  set y : H := ((q : ℝ) : ℂ)⁻¹ • S x with hydef
  set r : H := S y - ((q : ℝ) : ℂ) • x with hrdef
  have hSsa : IsSelfAdjoint S := isSelfAdjoint_offDiagonalPart hZsa
  have hCsa : IsSelfAdjoint C := isSelfAdjoint_diagonalPart hZsa
  have hinner_self : ∀ v : H, ⟪v, v⟫_ℂ = ((‖v‖ ^ 2 : ℝ) : ℂ) := by
    intro v
    rw [inner_self_eq_norm_sq_to_K]
    norm_cast
  have hSsym := inner_swap_of_isSelfAdjoint hSsa
  have hCsym := inner_swap_of_isSelfAdjoint hCsa
  have hΩsym := inner_swap_of_isSelfAdjoint Ω.isSelfAdjoint
  have hZsym := inner_swap_of_isSelfAdjoint hZsa
  have hZZ : ∀ v : H, Z (Z v) = v := by
    intro v
    have h := congrArg (fun T : H →L[ℂ] H => T v) hZ2
    simpa using h
  have hZnorm : ∀ v : H, ‖Z v‖ = ‖v‖ := by
    intro v
    have h : ⟪Z v, Z v⟫_ℂ = ⟪v, v⟫_ℂ := by rw [hZsym v (Z v), hZZ]
    rw [hinner_self, hinner_self] at h
    have h2 : ‖Z v‖ ^ 2 = ‖v‖ ^ 2 := by exact_mod_cast h
    rw [← Real.sqrt_sq (norm_nonneg (Z v)), h2, Real.sqrt_sq (norm_nonneg v)]
  have hxU : x ∈ U := Ω.mem_subspace_of_eq hxΩ
  have hxdom : x ∈ A.domain := Ω.mem_domain_of_eq hxΩ
  have hSxU : S x ∈ Uᗮ := offDiagonalPart_mem_orthogonal_of_mem U Z hxU
  have hSxdom : S x ∈ A.domain :=
    mem_domain_offDiagonalPart hred hZdom ⟨x, hxdom⟩
  have hqne : ((q : ℝ) : ℂ) ≠ 0 := by
    simpa only [ne_eq, Complex.ofReal_eq_zero] using hq.ne'
  have hSxy : S x = ((q : ℝ) : ℂ) • y := by rw [hydef, smul_inv_smul₀ hqne]
  have hy1 : ‖y‖ = 1 := by
    rw [hydef, norm_smul, norm_inv, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos hq, ← hqdef]
    field_simp
  have hyU : y ∈ Uᗮ := Uᗮ.smul_mem _ hSxU
  have hydom : y ∈ A.domain := A.domain.smul_mem _ hSxdom
  -- the Sylvester identity at `x`, paired with `y`
  have hsyl := sylvester_offDiagonalPart_of_mem hred hB hZdom hZcomm
    ⟨x, hxdom⟩ hxU
  have hAsmul : A ⟨S x, mem_domain_offDiagonalPart hred hZdom ⟨x, hxdom⟩⟩ =
      ((q : ℝ) : ℂ) • A ⟨y, hydom⟩ := by
    rw [← A.map_smul]
    exact congrArg (fun w : A.domain => A w) (Subtype.ext hSxy)
  rw [hAsmul] at hsyl
  have hpair := congrArg (fun w : H => (⟪w, y⟫_ℂ).re) hsyl
  simp only [inner_add_left, Complex.add_re] at hpair
  rw [← hCdef, ← hSdef] at hpair
  -- geometry of the two diagonal blocks
  have hCxnorm : ‖C x‖ ^ 2 = 1 - q ^ 2 := by
    have h := norm_sq_diagonalPart_add_norm_sq_offDiagonalPart_of_mem
      (U := U) hZnorm hxU
    rw [hx1, one_pow, ← hCdef, ← hSdef, ← hqdef] at h
    linarith
  have hSy : S y = ((q : ℝ) : ℂ) • x + r := by rw [hrdef]; abel
  have hxSy : ⟪x, S y⟫_ℂ = ((q : ℝ) : ℂ) := by
    rw [← hSsym x y, hydef, inner_smul_right, hinner_self, ← hqdef]
    field_simp
    push_cast
    ring
  have hrx : ⟪x, r⟫_ℂ = 0 := by
    rw [hrdef, inner_sub_right, hxSy, inner_smul_right, hinner_self, hx1]
    norm_num
  have hSynorm : ‖S y‖ ^ 2 = q ^ 2 + ‖r‖ ^ 2 := by
    have hortho : ⟪((q : ℝ) : ℂ) • x, r⟫_ℂ = 0 := by
      rw [inner_smul_left, hrx, mul_zero]
    have h := norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero
      (((q : ℝ) : ℂ) • x) r hortho
    have hnx : ‖((q : ℝ) : ℂ) • x‖ = q := by
      rw [norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hq, hx1,
        mul_one]
    rw [hSy]
    simp only [sq]
    rw [h, hnx]
  have hCynorm : ‖C y‖ ^ 2 ≤ 1 - q ^ 2 := by
    have h := norm_sq_diagonalPart_add_norm_sq_offDiagonalPart_of_mem_orthogonal
      (U := U) hZnorm hyU
    rw [hy1, one_pow, ← hCdef, ← hSdef] at h
    nlinarith [sq_nonneg ‖r‖, hSynorm]
  have hCxle : ‖C x‖ ≤ √(1 - q ^ 2) := by
    rw [← Real.sqrt_sq (norm_nonneg (C x)), hCxnorm]
  have hCyle : ‖C y‖ ≤ √(1 - q ^ 2) := by
    rw [← Real.sqrt_sq (norm_nonneg (C y))]
    exact Real.sqrt_le_sqrt hCynorm
  -- the two bounded terms
  have hterm2 : |(⟪B (C x), y⟫_ℂ).re| ≤ ‖B‖ * √(1 - q ^ 2) := by
    have h1 : |(⟪B (C x), y⟫_ℂ).re| ≤ ‖B (C x)‖ * ‖y‖ :=
      le_trans (Complex.abs_re_le_norm _) (norm_inner_le_norm _ _)
    rw [hy1, mul_one] at h1
    exact h1.trans ((B.le_opNorm (C x)).trans
      (mul_le_mul_of_nonneg_left hCxle (norm_nonneg B)))
  have hterm4 : |(⟪C (B x), y⟫_ℂ).re| ≤ ‖B‖ * √(1 - q ^ 2) := by
    rw [hCsym (B x) y]
    have h1 : |(⟪B x, C y⟫_ℂ).re| ≤ ‖B x‖ * ‖C y‖ :=
      le_trans (Complex.abs_re_le_norm _) (norm_inner_le_norm _ _)
    have h2 : ‖B x‖ ≤ ‖B‖ := by
      have := B.le_opNorm x
      rwa [hx1, mul_one] at this
    exact h1.trans (mul_le_mul h2 hCyle (norm_nonneg _) (norm_nonneg B))
  -- the single unbounded term
  have hAxfix : Ω.toProj (A ⟨x, hxdom⟩) = A ⟨x, hxdom⟩ := by
    have h := Ω.apply_mem_range x
    have hsub : (⟨Ω.toProj x, Ω.mem_domain x⟩ : A.domain) = ⟨x, hxdom⟩ :=
      Subtype.ext hxΩ
    rwa [hsub] at h
  have hAxnorm : ‖A ⟨x, hxdom⟩‖ ≤ τ := by
    have h := Ω.norm_apply_le x
    have hsub : (⟨Ω.toProj x, Ω.mem_domain x⟩ : A.domain) = ⟨x, hxdom⟩ :=
      Subtype.ext hxΩ
    rw [hsub, hxΩ, hx1, mul_one] at h
    exact h
  have hterm3 : (⟪S (A ⟨x, hxdom⟩), y⟫_ℂ).re ≤ q * a + τ * ‖Ω.toProj r‖ := by
    rw [hSsym (A ⟨x, hxdom⟩) y, hSy, inner_add_right, inner_smul_right,
      Complex.add_re, Complex.re_ofReal_mul]
    have hleak : ⟪A ⟨x, hxdom⟩, r⟫_ℂ = ⟪A ⟨x, hxdom⟩, Ω.toProj r⟫_ℂ := by
      conv_lhs => rw [← hAxfix]
      rw [hΩsym (A ⟨x, hxdom⟩) r]
    have hleakbd : (⟪A ⟨x, hxdom⟩, r⟫_ℂ).re ≤ τ * ‖Ω.toProj r‖ := by
      rw [hleak]
      exact le_trans (le_abs_self _) (le_trans
        (le_trans (Complex.abs_re_le_norm _) (norm_inner_le_norm _ _))
        (mul_le_mul_of_nonneg_right hAxnorm (norm_nonneg _)))
    have hupper : (⟪A ⟨x, hxdom⟩, x⟫_ℂ).re ≤ a := by
      have h := hUa ⟨x, hxdom⟩ hxU
      rwa [hx1, one_pow, mul_one] at h
    have h1 : q * (⟪A ⟨x, hxdom⟩, x⟫_ℂ).re ≤ q * a :=
      mul_le_mul_of_nonneg_left hupper hq.le
    linarith
  -- assemble
  have hterm1 : (⟪((q : ℝ) : ℂ) • A ⟨y, hydom⟩, y⟫_ℂ).re =
      q * (⟪A ⟨y, hydom⟩, y⟫_ℂ).re := by
    rw [inner_smul_left, Complex.conj_ofReal, Complex.re_ofReal_mul]
  have hlow : b ≤ (⟪A ⟨y, hydom⟩, y⟫_ℂ).re := by
    have h := hUb ⟨y, hydom⟩ hyU
    rwa [hy1, one_pow, mul_one] at h
  rw [hterm1] at hpair
  have h2 : -(‖B‖ * √(1 - q ^ 2)) ≤ (⟪B (C x), y⟫_ℂ).re :=
    neg_le_of_abs_le hterm2
  have h4 : (⟪C (B x), y⟫_ℂ).re ≤ ‖B‖ * √(1 - q ^ 2) :=
    le_trans (le_abs_self _) hterm4
  have hq1 : q * b ≤ q * (⟪A ⟨y, hydom⟩, y⟫_ℂ).re :=
    mul_le_mul_of_nonneg_left hlow hq.le
  nlinarith [hpair, hq1, h2, h4, hterm3]
omit hred hB hZsa hZ2 hZdom hZcomm hUa hUb in
/-- The scalar inequality behind the uniform cutoff bound. -/
private theorem le_crossBlockBound_of_mul_le {δ m t : ℝ}
    (hδ : 0 < δ) (hm0 : 0 ≤ m) (hm1 : m ≤ 1) (ht : 0 ≤ t)
    (hmain : δ * m ≤ 2 * t * √(1 - m ^ 2)) :
    m ≤ crossBlockBound δ t := by
  -- close the algebra
  have h1m2 : 0 ≤ 1 - m ^ 2 := by nlinarith [hm1, hm0]
  have hlhs0 : 0 ≤ δ * m := by positivity
  have hrhs : (2 * t * √(1 - m ^ 2)) ^ 2 = 4 * t ^ 2 * (1 - m ^ 2) := by
    rw [mul_pow, Real.sq_sqrt h1m2]
    ring
  have hsq : (δ * m) ^ 2 ≤ 4 * t ^ 2 * (1 - m ^ 2) := by
    rw [← hrhs]
    gcongr
  set D : ℝ := √(δ ^ 2 + 4 * t ^ 2) with hDdef
  have hDpos : 0 < D := Real.sqrt_pos.mpr (by positivity)
  have hD2 : D ^ 2 = δ ^ 2 + 4 * t ^ 2 := Real.sq_sqrt (by positivity)
  have hmDeq : (m * D) ^ 2 = (δ * m) ^ 2 + 4 * t ^ 2 * m ^ 2 := by
    rw [mul_pow, hD2]
    ring
  have hmD : (m * D) ^ 2 ≤ (2 * t) ^ 2 := by
    rw [hmDeq]
    nlinarith [hsq]
  have hfin : m * D ≤ 2 * t :=
    calc m * D = √((m * D) ^ 2) := (Real.sqrt_sq (by positivity)).symm
      _ ≤ √((2 * t) ^ 2) := Real.sqrt_le_sqrt hmD
      _ = 2 * t := Real.sqrt_sq (by positivity)
  rw [crossBlockBound_eq, ← hDdef, le_div_iff₀ hDpos]
  exact hfin

/-- **Pole exclusion on a bounded cutoff.**

`‖S Ω‖ ≤ 2‖B‖ / √(δ² + 4‖B‖²) < 1` with `δ = b - a`.  The bound is uniform in
the cutoff level `τ`, which is what makes the passage `τ → ∞` free. -/
theorem opNorm_offDiagonalPart_comp_le (Ω : BoundedCutoff A U τ) (hτ : 0 ≤ τ)
    (hab : a < b) :
    ‖U.offDiagonalPart Z ∘L Ω.toProj‖ ≤ crossBlockBound (b - a) ‖B‖ := by
  classical
  set S : H →L[ℂ] H := U.offDiagonalPart Z with hSdef
  set m : ℝ := ‖S ∘L Ω.toProj‖ with hmdef
  have hδ : 0 < b - a := by linarith
  have hm0 : 0 ≤ m := norm_nonneg _
  have hZnorm := norm_apply_of_isSelfAdjoint_of_mul_self hZsa hZ2
  have hm1 : m ≤ 1 := by
    rw [hmdef]
    refine ContinuousLinearMap.opNorm_le_bound _ zero_le_one ?_
    intro v
    have hmem : Ω.toProj v ∈ U := Ω.mem_subspace v
    have h := norm_sq_diagonalPart_add_norm_sq_offDiagonalPart_of_mem
      (U := U) hZnorm hmem
    rw [← hSdef] at h
    have hSle : ‖S (Ω.toProj v)‖ ≤ ‖Ω.toProj v‖ := by
      nlinarith [sq_nonneg ‖U.diagonalPart Z (Ω.toProj v)‖,
        norm_nonneg (S (Ω.toProj v)), norm_nonneg (Ω.toProj v)]
    have hcomp : ‖(S ∘L Ω.toProj) v‖ = ‖S (Ω.toProj v)‖ := rfl
    rw [hcomp, one_mul]
    exact hSle.trans (Ω.norm_toProj_apply_le v)
  have hmain : (b - a) * m ≤ 2 * ‖B‖ * √(1 - m ^ 2) := by
    rcases eq_or_lt_of_le hm0 with hm | hm
    · rw [← hm, mul_zero]
      positivity
    refine le_of_forall_pos_le_add ?_
    intro η hη
    set K : ℝ := 2 * ‖B‖ + τ with hKdef
    have hK0 : 0 ≤ K := by rw [hKdef]; linarith [norm_nonneg B]
    have hK1 : (0 : ℝ) < K + 1 := by linarith
    have hden1 : (0 : ℝ) < 2 * (b - a) := by linarith
    have hden2 : (0 : ℝ) < 2 * (K + 1) := by linarith
    have hpos1 : (0 : ℝ) < η / (2 * (b - a)) := div_pos hη hden1
    have hpos2 : (0 : ℝ) < η / (2 * (K + 1)) := div_pos hη hden2
    obtain ⟨ε, hε0, hεm, hεa, hεb⟩ :
        ∃ ε : ℝ, 0 < ε ∧ ε ≤ m ∧ ε ≤ η / (2 * (b - a)) ∧
          ε ≤ (η / (2 * (K + 1))) ^ 2 / 2 :=
      ⟨min m (min (η / (2 * (b - a))) ((η / (2 * (K + 1))) ^ 2 / 2)),
        lt_min hm (lt_min hpos1 (div_pos (pow_pos hpos2 2) two_pos)),
        min_le_left _ _, le_trans (min_le_right _ _) (min_le_left _ _),
        le_trans (min_le_right _ _) (min_le_right _ _)⟩
    have hsqrt2ε : √(2 * ε) ≤ η / (2 * (K + 1)) := by
      rw [show η / (2 * (K + 1)) = √((η / (2 * (K + 1))) ^ 2) from
        (Real.sqrt_sq hpos2.le).symm]
      exact Real.sqrt_le_sqrt (by linarith)
    obtain ⟨v, hv1, hv2⟩ :=
      (S ∘L Ω.toProj).exists_lt_apply_of_lt_opNorm (r := m - ε) (by
        rw [← hmdef]; linarith)
    set x₀ : H := Ω.toProj v with hx₀def
    have hSx₀ : ‖(S ∘L Ω.toProj) v‖ = ‖S x₀‖ := rfl
    rw [hSx₀] at hv2
    have hSx₀pos : 0 < ‖S x₀‖ := lt_of_le_of_lt (by linarith) hv2
    have hx₀ne0 : x₀ ≠ 0 := by
      intro h
      rw [h, map_zero, norm_zero] at hSx₀pos
      exact lt_irrefl 0 hSx₀pos
    have hx₀pos : 0 < ‖x₀‖ := norm_pos_iff.mpr hx₀ne0
    have hx₀le : ‖x₀‖ ≤ 1 :=
      le_of_lt (lt_of_le_of_lt (Ω.norm_toProj_apply_le v) hv1)
    have hx₀ne : ((‖x₀‖ : ℝ) : ℂ) ≠ 0 := by
      simpa only [ne_eq, Complex.ofReal_eq_zero] using hx₀pos.ne'
    set x : H := ((‖x₀‖ : ℝ) : ℂ)⁻¹ • x₀ with hxdef
    have hx1 : ‖x‖ = 1 := by
      rw [hxdef, norm_smul, norm_inv, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos hx₀pos]
      field_simp
    have hxΩ : Ω.toProj x = x := by
      rw [hxdef, map_smul, hx₀def, Ω.toProj_apply_toProj]
    set q : ℝ := ‖S x‖ with hqdef
    have hqval : q = ‖x₀‖⁻¹ * ‖S x₀‖ := by
      rw [hqdef, hxdef, map_smul, norm_smul, norm_inv, Complex.norm_real,
        Real.norm_eq_abs, abs_of_pos hx₀pos]
    have hinv : ‖x₀‖ * ‖x₀‖⁻¹ = 1 := mul_inv_cancel₀ hx₀pos.ne'
    have hinvge : (1 : ℝ) ≤ ‖x₀‖⁻¹ := by
      nlinarith [hinv, hx₀le, hx₀pos, inv_pos.mpr hx₀pos]
    have hqlow : m - ε < q := by
      have h1 : ‖S x₀‖ ≤ q := by
        rw [hqval]
        nlinarith [hinvge, hSx₀pos.le]
      linarith
    have hq0 : 0 < q := lt_of_le_of_lt (by linarith) hqlow
    have hqm : q ≤ m := by
      have h := (S ∘L Ω.toProj).le_opNorm x
      rw [ContinuousLinearMap.comp_apply, hxΩ, hx1, mul_one, ← hmdef,
        ← hqdef] at h
      exact h
    -- engine and leakage at the near-maximiser
    have heng := sylvester_pairing_le hred hB hZsa hZ2 hZdom hZcomm hUa hUb Ω
      hxΩ hx1 (by rw [← hSdef, ← hqdef]; exact hq0)
    have hleak := norm_sq_cutoff_leak_le hZsa Ω hxΩ hx1
      (by rw [← hSdef, ← hqdef]; exact hq0)
    rw [← hSdef, ← hqdef] at heng hleak
    rw [← hmdef] at hleak
    set L : ℝ := ‖Ω.toProj (S (((q : ℝ) : ℂ)⁻¹ • S x) - ((q : ℝ) : ℂ) • x)‖
      with hLdef
    have hL0 : 0 ≤ L := norm_nonneg _
    have hgap : m ^ 2 - q ^ 2 ≤ 2 * ε := by nlinarith [hqlow, hm1, hε0, hm0]
    have hLle : L ≤ √(2 * ε) := by
      rw [← Real.sqrt_sq hL0]
      exact Real.sqrt_le_sqrt (by linarith [hleak])
    have h1m2 : 0 ≤ 1 - m ^ 2 := by nlinarith [hm1, hm0]
    have hqsqrt : √(1 - q ^ 2) ≤ √(1 - m ^ 2) + √(2 * ε) := by
      refine le_trans (Real.sqrt_le_sqrt (by linarith : 1 - q ^ 2 ≤
        (1 - m ^ 2) + 2 * ε)) ?_
      exact sqrt_add_le_sqrt_add_sqrt h1m2 (by linarith)
    have hstep : (b - a) * (m - ε) ≤ 2 * ‖B‖ * √(1 - m ^ 2) + K * √(2 * ε) := by
      have h1 : (b - a) * (m - ε) ≤ (b - a) * q :=
        mul_le_mul_of_nonneg_left hqlow.le hδ.le
      have h2 : 2 * ‖B‖ * √(1 - q ^ 2) ≤
          2 * ‖B‖ * (√(1 - m ^ 2) + √(2 * ε)) :=
        mul_le_mul_of_nonneg_left hqsqrt (by positivity)
      have h3 : τ * L ≤ τ * √(2 * ε) := mul_le_mul_of_nonneg_left hLle hτ
      calc (b - a) * (m - ε) ≤ (b - a) * q := h1
        _ ≤ 2 * ‖B‖ * √(1 - q ^ 2) + τ * L := heng
        _ ≤ 2 * ‖B‖ * (√(1 - m ^ 2) + √(2 * ε)) + τ * √(2 * ε) :=
            add_le_add h2 h3
        _ = 2 * ‖B‖ * √(1 - m ^ 2) + K * √(2 * ε) := by rw [hKdef]; ring
    have herr1 : (b - a) * ε ≤ η / 2 := by
      calc (b - a) * ε ≤ (b - a) * (η / (2 * (b - a))) :=
            mul_le_mul_of_nonneg_left hεa hδ.le
        _ = η / 2 := by field_simp
    have herr2 : K * √(2 * ε) ≤ η / 2 := by
      have heq : K * (η / (2 * (K + 1))) = η / 2 * (K / (K + 1)) := by
        field_simp
      have hle : K / (K + 1) ≤ 1 := by
        rw [div_le_one hK1]
        linarith
      calc K * √(2 * ε) ≤ K * (η / (2 * (K + 1))) :=
            mul_le_mul_of_nonneg_left hsqrt2ε hK0
        _ = η / 2 * (K / (K + 1)) := heq
        _ ≤ η / 2 * 1 := mul_le_mul_of_nonneg_left hle (by linarith)
        _ = η / 2 := mul_one _
    linarith [hstep, herr1, herr2]
  exact le_crossBlockBound_of_mul_le hδ hm0 hm1 (norm_nonneg B) hmain

/-- **The pole is excluded on the cutoff range**, with the explicit constant
`κ = δ / √(δ² + 4‖B‖²) > 0`: `|cos 2Θ₀| ≥ κ`. -/
theorem diagonalBlockBound_mul_le_norm_diagonalPart_apply
    (Ω : BoundedCutoff A U τ) (hτ : 0 ≤ τ) (hab : a < b) {x : H}
    (hxΩ : Ω.toProj x = x) :
    diagonalBlockBound (b - a) ‖B‖ * ‖x‖ ≤ ‖U.diagonalPart Z x‖ := by
  have hδ : 0 < b - a := by linarith
  have hZnorm := norm_apply_of_isSelfAdjoint_of_mul_self hZsa hZ2
  have hxU : x ∈ U := Ω.mem_subspace_of_eq hxΩ
  have hpyth := norm_sq_diagonalPart_add_norm_sq_offDiagonalPart_of_mem
    (U := U) hZnorm hxU
  have hS : ‖U.offDiagonalPart Z x‖ ≤ crossBlockBound (b - a) ‖B‖ * ‖x‖ := by
    have h := (U.offDiagonalPart Z ∘L Ω.toProj).le_opNorm x
    rw [ContinuousLinearMap.comp_apply, hxΩ] at h
    exact h.trans (mul_le_mul_of_nonneg_right
      (opNorm_offDiagonalPart_comp_le hred hB hZsa hZ2 hZdom hZcomm hUa hUb Ω hτ
        hab) (norm_nonneg x))
  exact diagonalBlockBound_le_of_cross hδ (norm_nonneg x) hS (norm_nonneg _)
    (norm_nonneg _) hpyth

/-- **Pole exclusion on the whole of `U`**, after `τ → ∞`.

Given a family of bounded cutoffs whose projections converge strongly to the
identity at `x`, the cross block obeys the same uniform bound at `x`:

`‖S x‖ ≤ (2‖B‖ / √(δ² + 4‖B‖²)) ‖x‖`. -/
theorem norm_offDiagonalPart_apply_le_of_tendsto {ι : Type*} {l : Filter ι}
    [l.NeBot] (τf : ι → ℝ) (Ωf : ∀ i, BoundedCutoff A U (τf i))
    (hτ : ∀ i, 0 ≤ τf i) (hab : a < b) {x : H}
    (hx : Filter.Tendsto (fun i => (Ωf i).toProj x) l (nhds x)) :
    ‖U.offDiagonalPart Z x‖ ≤ crossBlockBound (b - a) ‖B‖ * ‖x‖ := by
  have hbound : ∀ i, ‖U.offDiagonalPart Z ((Ωf i).toProj x)‖ ≤
      crossBlockBound (b - a) ‖B‖ * ‖x‖ := by
    intro i
    have h := (U.offDiagonalPart Z ∘L (Ωf i).toProj).le_opNorm x
    rw [ContinuousLinearMap.comp_apply] at h
    exact h.trans (mul_le_mul_of_nonneg_right
      (opNorm_offDiagonalPart_comp_le hred hB hZsa hZ2 hZdom hZcomm hUa hUb
        (Ωf i) (hτ i) hab) (norm_nonneg x))
  have hlim : Filter.Tendsto
      (fun i => ‖U.offDiagonalPart Z ((Ωf i).toProj x)‖) l
      (nhds ‖U.offDiagonalPart Z x‖) :=
    (continuous_norm.tendsto _).comp
      (((U.offDiagonalPart Z).continuous.tendsto x).comp hx)
  exact le_of_tendsto hlim (Filter.Eventually.of_forall hbound)

/-- **The cross block is a strict contraction on the whole space**, not merely on
the trial subspace.

`S = U.offDiagonalPart Z` is self-adjoint and exchanges `U` and `Uᗮ`, so its
`Uᗮ` block is the adjoint of its `U` block and carries the same bound: for
`y ∈ Uᗮ`, `‖S y‖² = ⟪y, S (S y)⟫ ≤ ‖y‖ ‖S (S y)‖ ≤ c ‖y‖ ‖S y‖` because
`S y ∈ U`.  The two blocks land in orthogonal subspaces, so the bound assembles
by Pythagoras.

This is the hypothesis `‖U.offDiagonalPart Z‖ < 1` that the Ky Fan endpoints of
`DavisKahan/Sources/DavisKahan1970/TanTwoThetaUnboundedGramMiddle.lean` take; see
`norm_offDiagonalPart_lt_one_of_tendsto`. -/
theorem norm_offDiagonalPart_le_of_tendsto {ι : Type*} {l : Filter ι}
    [l.NeBot] (τf : ι → ℝ) (Ωf : ∀ i, BoundedCutoff A U (τf i))
    (hτ : ∀ i, 0 ≤ τf i) (hab : a < b)
    (hconv : ∀ x ∈ U, Filter.Tendsto (fun i => (Ωf i).toProj x) l (nhds x)) :
    ‖U.offDiagonalPart Z‖ ≤ crossBlockBound (b - a) ‖B‖ := by
  have hc0 : 0 ≤ crossBlockBound (b - a) ‖B‖ := crossBlockBound_nonneg (norm_nonneg B)
  have hsym : ∀ u v : H, ⟪U.offDiagonalPart Z u, v⟫_ℂ = ⟪u, U.offDiagonalPart Z v⟫_ℂ :=
    inner_swap_of_isSelfAdjoint (isSelfAdjoint_offDiagonalPart hZsa)
  have hU : ∀ x ∈ U, ‖U.offDiagonalPart Z x‖ ≤ crossBlockBound (b - a) ‖B‖ * ‖x‖ :=
    fun x hx => norm_offDiagonalPart_apply_le_of_tendsto hred hB hZsa hZ2 hZdom
      hZcomm hUa hUb τf Ωf hτ hab (hconv x hx)
  have hUp : ∀ y ∈ Uᗮ, ‖U.offDiagonalPart Z y‖ ≤ crossBlockBound (b - a) ‖B‖ * ‖y‖ := by
    intro y hy
    have hmem : U.offDiagonalPart Z y ∈ U :=
      offDiagonalPart_mem_of_mem_orthogonal U Z hy
    have hval : RCLike.re ⟪y, U.offDiagonalPart Z (U.offDiagonalPart Z y)⟫_ℂ
        = ‖U.offDiagonalPart Z y‖ ^ 2 := by
      rw [← hsym y (U.offDiagonalPart Z y)]
      exact inner_self_eq_norm_sq _
    have hle : ‖U.offDiagonalPart Z y‖ ^ 2
        ≤ ‖y‖ * ‖U.offDiagonalPart Z (U.offDiagonalPart Z y)‖ := by
      rw [← hval]
      exact (RCLike.re_le_norm _).trans (norm_inner_le_norm y _)
    have hinner := hU (U.offDiagonalPart Z y) hmem
    rcases eq_or_lt_of_le (norm_nonneg (U.offDiagonalPart Z y)) with h0 | h0
    · rw [← h0]
      exact mul_nonneg hc0 (norm_nonneg y)
    · nlinarith [hle, hinner, norm_nonneg y, hc0]
  refine ContinuousLinearMap.opNorm_le_bound _ hc0 fun v => ?_
  have hsplit : U.starProjection v + Uᗮ.starProjection v = v := by
    rw [Submodule.starProjection_orthogonal_apply]
    abel
  have hSv : U.offDiagonalPart Z v
      = U.offDiagonalPart Z (U.starProjection v)
        + U.offDiagonalPart Z (Uᗮ.starProjection v) := by
    rw [← map_add, hsplit]
  have hp : U.offDiagonalPart Z (U.starProjection v) ∈ Uᗮ :=
    offDiagonalPart_mem_orthogonal_of_mem U Z (U.starProjection_apply_mem v)
  have hq : U.offDiagonalPart Z (Uᗮ.starProjection v) ∈ U :=
    offDiagonalPart_mem_of_mem_orthogonal U Z (Uᗮ.starProjection_apply_mem v)
  have hqp : ⟪U.offDiagonalPart Z (Uᗮ.starProjection v),
      U.offDiagonalPart Z (U.starProjection v)⟫_ℂ = 0 :=
    hp _ hq
  have hpq : ⟪U.offDiagonalPart Z (U.starProjection v),
      U.offDiagonalPart Z (Uᗮ.starProjection v)⟫_ℂ = 0 := by
    rw [← inner_conj_symm (𝕜 := ℂ), hqp, map_zero]
  have hnormsq : ‖U.offDiagonalPart Z v‖ ^ 2
      = ‖U.offDiagonalPart Z (U.starProjection v)‖ ^ 2
        + ‖U.offDiagonalPart Z (Uᗮ.starProjection v)‖ ^ 2 := by
    rw [hSv, norm_add_sq (𝕜 := ℂ), hpq]
    simp
  have hcross : ⟪U.starProjection v, Uᗮ.starProjection v⟫_ℂ = 0 :=
    (Uᗮ.starProjection_apply_mem v) _ (U.starProjection_apply_mem v)
  have hvsq : ‖v‖ ^ 2 = ‖U.starProjection v‖ ^ 2 + ‖Uᗮ.starProjection v‖ ^ 2 := by
    rw [← hsplit, norm_add_sq (𝕜 := ℂ), hcross]
    simp
  have hpv := hU (U.starProjection v) (U.starProjection_apply_mem v)
  have hqv := hUp (Uᗮ.starProjection v) (Uᗮ.starProjection_apply_mem v)
  have hsq : ‖U.offDiagonalPart Z v‖ ^ 2
      ≤ (crossBlockBound (b - a) ‖B‖ * ‖v‖) ^ 2 := by
    rw [hnormsq, mul_pow, hvsq]
    nlinarith [hpv, hqv, norm_nonneg (U.offDiagonalPart Z (U.starProjection v)),
      norm_nonneg (U.offDiagonalPart Z (Uᗮ.starProjection v)), hc0,
      norm_nonneg (U.starProjection v), norm_nonneg (Uᗮ.starProjection v)]
  have hfin := Real.sqrt_le_sqrt hsq
  rwa [Real.sqrt_sq (norm_nonneg _),
    Real.sqrt_sq (mul_nonneg hc0 (norm_nonneg v))] at hfin

/-- **The cross block is separated from `1` in operator norm**, with no smallness
hypothesis: `‖sin 2Θ₀‖ ≤ 2‖B‖ / √(δ² + 4‖B‖²) < 1`. -/
theorem norm_offDiagonalPart_lt_one_of_tendsto {ι : Type*} {l : Filter ι}
    [l.NeBot] (τf : ι → ℝ) (Ωf : ∀ i, BoundedCutoff A U (τf i))
    (hτ : ∀ i, 0 ≤ τf i) (hab : a < b)
    (hconv : ∀ x ∈ U, Filter.Tendsto (fun i => (Ωf i).toProj x) l (nhds x)) :
    ‖U.offDiagonalPart Z‖ < 1 :=
  lt_of_le_of_lt
    (norm_offDiagonalPart_le_of_tendsto hred hB hZsa hZ2 hZdom hZcomm hUa hUb τf
      Ωf hτ hab hconv)
    (crossBlockBound_lt_one (by linarith) (norm_nonneg B))

/-- **The pole-exclusion theorem.**  For `x` in the trial subspace `U`,

`κ ‖x‖ ≤ ‖cos 2Θ₀ x‖`,   `κ = δ / √(δ² + 4‖B‖²) > 0`,   `δ = b - a`,

so the denominator of `tan 2Θ₀` is bounded below by an explicit positive
constant.  **The pole is excluded before the tangent is defined**, and nothing
about proximity to `π/4` is assumed. -/
theorem diagonalBlockBound_mul_le_norm_diagonalPart_apply_of_tendsto
    {ι : Type*} {l : Filter ι} [l.NeBot] (τf : ι → ℝ)
    (Ωf : ∀ i, BoundedCutoff A U (τf i)) (hτ : ∀ i, 0 ≤ τf i) (hab : a < b)
    {x : H} (hxU : x ∈ U)
    (hx : Filter.Tendsto (fun i => (Ωf i).toProj x) l (nhds x)) :
    diagonalBlockBound (b - a) ‖B‖ * ‖x‖ ≤ ‖U.diagonalPart Z x‖ := by
  have hδ : 0 < b - a := by linarith
  have hZnorm := norm_apply_of_isSelfAdjoint_of_mul_self hZsa hZ2
  have hpyth := norm_sq_diagonalPart_add_norm_sq_offDiagonalPart_of_mem
    (U := U) hZnorm hxU
  exact diagonalBlockBound_le_of_cross hδ (norm_nonneg x)
    (norm_offDiagonalPart_apply_le_of_tendsto hred hB hZsa hZ2 hZdom hZcomm hUa
      hUb τf Ωf hτ hab hx) (norm_nonneg _) (norm_nonneg _) hpyth

/-- **The branch-free `tan 2Θ₀` inequality at the operator norm, unbounded.**

`δ ‖sin 2Θ₀ x‖ ≤ 2 ‖B‖ ‖cos 2Θ₀ x‖` for every `x` in the trial subspace, with
`δ = b - a`.  Dividing by `‖cos 2Θ₀ x‖`, which
`diagonalBlockBound_mul_le_norm_diagonalPart_apply_of_tendsto` bounds below by
`κ ‖x‖ > 0`, this is `δ |tan 2θ| ≤ 2 ‖B‖`.

The constant is the sharp `2` and the right-hand side is the **residual** `B`,
not a perturbation norm.  **Branch-freeness is structural**: the sign of
`cos 2θ` has vanished into `C x` and only its magnitude survives, so no acute or
obtuse branch is selected anywhere. -/
theorem gap_mul_norm_offDiagonalPart_apply_le_of_tendsto {ι : Type*}
    {l : Filter ι} [l.NeBot] (τf : ι → ℝ) (Ωf : ∀ i, BoundedCutoff A U (τf i))
    (hτ : ∀ i, 0 ≤ τf i) (hab : a < b) {x : H} (hxU : x ∈ U)
    (hx : Filter.Tendsto (fun i => (Ωf i).toProj x) l (nhds x)) :
    (b - a) * ‖U.offDiagonalPart Z x‖ ≤ 2 * ‖B‖ * ‖U.diagonalPart Z x‖ := by
  have hδ : 0 < b - a := by linarith
  have hZnorm := norm_apply_of_isSelfAdjoint_of_mul_self hZsa hZ2
  have hpyth := norm_sq_diagonalPart_add_norm_sq_offDiagonalPart_of_mem
    (U := U) hZnorm hxU
  exact gap_mul_le_of_cross (norm_nonneg B)
    (norm_offDiagonalPart_apply_le_of_tendsto hred hB hZsa hZ2 hZdom hZcomm hUa
      hUb τf Ωf hτ hab hx) (norm_nonneg _) (norm_nonneg _) hpyth hδ

end Estimate

end TauCeti
