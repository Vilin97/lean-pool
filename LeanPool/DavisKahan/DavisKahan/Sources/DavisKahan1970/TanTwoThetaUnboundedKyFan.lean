/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, Claude Opus 5
-/
import LeanPool.DavisKahan.DavisKahan.Sources.DavisKahan1970.TanTwoThetaUnboundedResidual
import LeanPool.DavisKahan.DavisKahan.DoubleAngle.KyFanOrthonormal
import LeanPool.DavisKahan.DavisKahan.OperatorIdeal.ApproximationNumbers.ScalarGeneric

/-!
# The unbounded, residual-form `tan 2Θ` theorem at every Ky Fan prefix

`TanTwoThetaUnboundedResidual.lean` proves the unbounded residual `tan 2Θ`
estimate at the operator norm, that is at the Ky Fan prefix `ν = 1`.  This
module proves the prefixes `ν ≥ 2`, on an exact double-angle eigenfamily.

## The route, and why it is the reflection picture

Both proofs start from the same object: the reducing reflection `Z = 2Q - 1` of
the perturbed operator, its even block `C = cos 2Θ` and odd block `S = sin 2Θ`
relative to `𝔛₀ ⊕ 𝔛₁`, and the unbounded Davis--Kahan equation (7.6)

`A (S x) + B (C x) = S (A x) + C (B x)`,   `x ∈ D(A)`,

which is `TauCeti.sylvester_offDiagonalPart_of_mem`.

At the operator norm that equation is paired with a *near-maximiser* of `‖S ·‖`
inside a bounded spectral cutoff, and the leakage term is killed by letting the
near-maximiser improve at a fixed cutoff level.  The device does not survive to
`ν ≥ 2`, because a Ky Fan prefix needs `ν` mutually orthogonal directions rather
than one near-optimal direction.

What replaces it is an exact algebraic cancellation.  Pair (7.6) at `x` with
`S x` rather than with a normalised near-maximiser.  If `S² x = q² x` then

* `Re ⟪A (S x), S x⟫ ≥ b ‖S x‖² = b q²`, because `S x ∈ 𝔛₁ ∩ D(A)`;
* `Re ⟪S (A x), S x⟫ = Re ⟪A x, S² x⟫ = q² Re ⟪A x, x⟫ ≤ a q²`, because `S` is
  self-adjoint and `x` is an eigenvector of `S²`.

**Both unbounded terms are evaluated where the form hypotheses apply directly,
and no residual is ever paired with `A`.**  The coupling between a residual and
a band radius that obstructs the graph-coordinate route does not arise here,
because there is no residual.

## Main results

* `gap_mul_sq_le_paired_of_doubleAngleEigenvector` — equation (7.6) at an exact
  eigenvector of `S²`, with both unbounded terms discharged.
* `doubleAngleEigenvalue_lt_one` — the pole is excluded *for free*: `q < 1`, so
  `cos 2θ ≠ 0`, with no cutoff and no limit.
* `gap_mul_sum_tangent_le_kyFan_of_doubleAngleEigenfamily` — the `ν ≥ 2`
  endpoint `δ ∑ᵢ qᵢ / √(1 - qᵢ²) ≤ 2 · kyFanApproximationGauge n B`.
* `unboundedReflectionTangent` — the genuine `tan 2Θ₀ = sin 2Θ₀ · (cos 2Θ₀)⁻¹`
  of the reflection picture, together with
  `isDoubleAngleTangent_unboundedReflectionTangent_specRange`, which constructs
  it under the standing Davis--Kahan data with no extra hypothesis.
* `sum_tangent_le_kyFan_of_compressedDoubleAngleEigenfamily` — the compression
  sum is a *lower* bound for the genuine tangent's Ky Fan prefix, hence the
  prefix-realisation clause of `IsCompressedDoubleAngleEigenbasis` is the
  reverse of a theorem and can only hold with equality.

The four orthonormal systems the Ky Fan step consumes — `xᵢ`, `S xᵢ / qᵢ`,
`C xᵢ / cᵢ` and `C (S xᵢ) / (qᵢ cᵢ)` — are *exactly* orthonormal, which is again
a consequence of the eigenvector relation together with `C² + S² = 1`.

## References

* C. Davis and W. M. Kahan, *The rotation of eigenvectors by a perturbation.
  III*, SIAM J. Numer. Anal. 7 (1970), 1--46: Section 7 for the `tan 2Θ`
  theorem and the reflection `Z = 2Q - 1`, equation (7.6) for the block system,
  and the Appendix to Section 6 for the unbounded passage.
-/

namespace TauCeti
namespace DavisKahan1970

open TauCeti.DavisKahan.ExactSinTheta

open scoped InnerProductSpace BigOperators


noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H]
variable {U : Submodule ℂ H} [U.HasOrthogonalProjection]
variable {A : H →ₗ.[ℂ] H} {B Z : H →L[ℂ] H} {a b τ : ℝ}

/-- The squared length of the odd block at an exact `S²`-eigenvector is the
eigenvalue. -/
theorem norm_sq_offDiagonalPart_of_doubleAngleEigenvector
    (hZsa : IsSelfAdjoint Z) {x : H} (hx1 : ‖x‖ = 1) {q : ℝ}
    (heig : U.offDiagonalPart Z (U.offDiagonalPart Z x) =
      ((q ^ 2 : ℝ) : ℂ) • x) :
    ‖U.offDiagonalPart Z x‖ ^ 2 = q ^ 2 := by
  have hSsym := TauCeti.inner_swap_of_isSelfAdjoint
    (TauCeti.isSelfAdjoint_offDiagonalPart (U := U) hZsa)
  have h : ⟪U.offDiagonalPart Z x, U.offDiagonalPart Z x⟫_ℂ =
      ((q ^ 2 : ℝ) : ℂ) := by
    rw [hSsym x (U.offDiagonalPart Z x), heig, inner_smul_right,
      inner_self_eq_norm_sq_to_K, hx1]
    norm_num
  have h2 : ((‖U.offDiagonalPart Z x‖ ^ 2 : ℝ) : ℂ) = ((q ^ 2 : ℝ) : ℂ) := by
    rw [← h, inner_self_eq_norm_sq_to_K]
    norm_cast
  exact_mod_cast h2

/-- **Equation (7.6) at an exact double-angle eigenvector.**

If `x` is a unit vector of the trial subspace lying in `D(A)` and `S² x = q² x`
for the odd block `S = U.offDiagonalPart Z`, then

`δ q² ≤ Re ⟪B x, C (S x)⟫ - Re ⟪B (C x), S x⟫`,   `δ = b - a`.

Both terms on the right are bounded: no norm of `A` occurs anywhere.  The proof
pairs the unbounded Davis--Kahan block equation with `S x` and uses the
eigenvector relation once, to replace `S (S x)` by `q² x`, which is what turns
the second unbounded term into the trial-side form bound. -/
theorem gap_mul_sq_le_paired_of_doubleAngleEigenvector
    (hred : TauCeti.LinearPMap.ReducesSubspace A U) (hB : TauCeti.IsOddFor U B)
    (hZsa : IsSelfAdjoint Z)
    (hZdom : TauCeti.LinearPMap.MapsDomainTo A A Z)
    (hZcomm : ∀ x : A.domain,
      A ⟨Z (x : H), hZdom x⟩ + B (Z (x : H)) = Z (A x) + Z (B (x : H)))
    (hUa : ∀ x : A.domain, (x : H) ∈ U →
      RCLike.re ⟪A x, (x : H)⟫_ℂ ≤ a * ‖(x : H)‖ ^ 2)
    (hUb : ∀ x : A.domain, (x : H) ∈ Uᗮ →
      b * ‖(x : H)‖ ^ 2 ≤ RCLike.re ⟪A x, (x : H)⟫_ℂ)
    {x : A.domain} (hxU : (x : H) ∈ U) (hx1 : ‖(x : H)‖ = 1) {q : ℝ}
    (heig : U.offDiagonalPart Z (U.offDiagonalPart Z (x : H)) =
      ((q ^ 2 : ℝ) : ℂ) • (x : H)) :
    (b - a) * q ^ 2 ≤
      RCLike.re ⟪B (x : H),
          U.diagonalPart Z (U.offDiagonalPart Z (x : H))⟫_ℂ -
        RCLike.re ⟪B (U.diagonalPart Z (x : H)),
          U.offDiagonalPart Z (x : H)⟫_ℂ := by
  have hSsym := TauCeti.inner_swap_of_isSelfAdjoint
    (TauCeti.isSelfAdjoint_offDiagonalPart (U := U) hZsa)
  have hCsym := TauCeti.inner_swap_of_isSelfAdjoint
    (TauCeti.isSelfAdjoint_diagonalPart (U := U) hZsa)
  have hSmem : U.offDiagonalPart Z (x : H) ∈ A.domain :=
    TauCeti.mem_domain_offDiagonalPart hred hZdom x
  have hSU : U.offDiagonalPart Z (x : H) ∈ Uᗮ :=
    TauCeti.offDiagonalPart_mem_orthogonal_of_mem U Z hxU
  have hnormS : ‖U.offDiagonalPart Z (x : H)‖ ^ 2 = q ^ 2 :=
    norm_sq_offDiagonalPart_of_doubleAngleEigenvector (U := U) hZsa hx1 heig
  have hsyl := TauCeti.sylvester_offDiagonalPart_of_mem hred hB hZdom hZcomm x hxU
  have hpair := congrArg
    (fun w : H => RCLike.re ⟪w, U.offDiagonalPart Z (x : H)⟫_ℂ) hsyl
  simp only [inner_add_left, map_add] at hpair
  have hlow : b * q ^ 2 ≤
      RCLike.re ⟪A ⟨U.offDiagonalPart Z (x : H), hSmem⟩,
        U.offDiagonalPart Z (x : H)⟫_ℂ := by
    have h := hUb ⟨U.offDiagonalPart Z (x : H), hSmem⟩ hSU
    calc b * q ^ 2 = b * ‖U.offDiagonalPart Z (x : H)‖ ^ 2 := by rw [hnormS]
      _ ≤ _ := h
  have hhigh : RCLike.re ⟪U.offDiagonalPart Z (A x),
      U.offDiagonalPart Z (x : H)⟫_ℂ ≤ a * q ^ 2 := by
    have hswap : ⟪U.offDiagonalPart Z (A x), U.offDiagonalPart Z (x : H)⟫_ℂ =
        ((q ^ 2 : ℝ) : ℂ) * ⟪A x, (x : H)⟫_ℂ := by
      rw [hSsym (A x) (U.offDiagonalPart Z (x : H)), heig, inner_smul_right]
    rw [hswap]
    have hx := hUa x hxU
    rw [hx1, one_pow, mul_one] at hx
    rw [← Complex.real_smul, RCLike.smul_re]
    nlinarith [sq_nonneg q, hx]
  have hmove : RCLike.re ⟪U.diagonalPart Z (B (x : H)),
      U.offDiagonalPart Z (x : H)⟫_ℂ =
      RCLike.re ⟪B (x : H),
        U.diagonalPart Z (U.offDiagonalPart Z (x : H))⟫_ℂ := by
    rw [hCsym (B (x : H)) (U.offDiagonalPart Z (x : H))]
  rw [hmove] at hpair
  linarith [hpair, hlow, hhigh]

/-- The two double-angle Pythagoras identities at an exact `S²`-eigenvector:
`‖C x‖² = 1 - q²` and `‖C (S x)‖² = q² (1 - q²)`. -/
theorem norm_sq_diagonalPart_of_doubleAngleEigenvector
    (hZsa : IsSelfAdjoint Z) (hZ2 : Z * Z = 1)
    {x : H} (hxU : x ∈ U) (hx1 : ‖x‖ = 1) {q : ℝ}
    (heig : U.offDiagonalPart Z (U.offDiagonalPart Z x) =
      ((q ^ 2 : ℝ) : ℂ) • x) :
    ‖U.diagonalPart Z x‖ ^ 2 = 1 - q ^ 2 ∧
      ‖U.diagonalPart Z (U.offDiagonalPart Z x)‖ ^ 2 =
        q ^ 2 * (1 - q ^ 2) := by
  have hZnorm : ∀ v : H, ‖Z v‖ = ‖v‖ :=
    TauCeti.norm_apply_of_isSelfAdjoint_of_mul_self hZsa hZ2
  have hSU : U.offDiagonalPart Z x ∈ Uᗮ :=
    TauCeti.offDiagonalPart_mem_orthogonal_of_mem U Z hxU
  have hnormS : ‖U.offDiagonalPart Z x‖ ^ 2 = q ^ 2 :=
    norm_sq_offDiagonalPart_of_doubleAngleEigenvector (U := U) hZsa hx1 heig
  have hnormSS : ‖U.offDiagonalPart Z (U.offDiagonalPart Z x)‖ ^ 2 =
      q ^ 2 * q ^ 2 := by
    rw [heig, norm_smul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (sq_nonneg q), hx1, mul_one]
    ring
  refine ⟨?_, ?_⟩
  · have h := TauCeti.norm_sq_diagonalPart_add_norm_sq_offDiagonalPart_of_mem
      (U := U) hZnorm hxU
    rw [hx1, one_pow, hnormS] at h
    linarith
  · have h :=
      TauCeti.norm_sq_diagonalPart_add_norm_sq_offDiagonalPart_of_mem_orthogonal
        (U := U) hZnorm hSU
    rw [hnormSS, hnormS] at h
    nlinarith [h]

/-- **The pole is excluded at an exact double-angle eigenvector, for free.**

`q < 1`, so `cos 2θ = √(1 - q²)` is nonzero and the tangent may be formed.  No
cutoff, no limit and no explicit constant are needed: if `q` were `1` then both
even blocks would vanish and equation (7.6) would force `δ ≤ 0`. -/
theorem doubleAngleEigenvalue_lt_one
    (hred : TauCeti.LinearPMap.ReducesSubspace A U) (hB : TauCeti.IsOddFor U B)
    (hZsa : IsSelfAdjoint Z) (hZ2 : Z * Z = 1)
    (hZdom : TauCeti.LinearPMap.MapsDomainTo A A Z)
    (hZcomm : ∀ x : A.domain,
      A ⟨Z (x : H), hZdom x⟩ + B (Z (x : H)) = Z (A x) + Z (B (x : H)))
    (hUa : ∀ x : A.domain, (x : H) ∈ U →
      RCLike.re ⟪A x, (x : H)⟫_ℂ ≤ a * ‖(x : H)‖ ^ 2)
    (hUb : ∀ x : A.domain, (x : H) ∈ Uᗮ →
      b * ‖(x : H)‖ ^ 2 ≤ RCLike.re ⟪A x, (x : H)⟫_ℂ)
    (hab : a < b)
    {x : A.domain} (hxU : (x : H) ∈ U) (hx1 : ‖(x : H)‖ = 1) {q : ℝ}
    (hq : 0 < q)
    (heig : U.offDiagonalPart Z (U.offDiagonalPart Z (x : H)) =
      ((q ^ 2 : ℝ) : ℂ) • (x : H)) :
    q < 1 := by
  obtain ⟨hCx, hCSx⟩ := norm_sq_diagonalPart_of_doubleAngleEigenvector
    (U := U) hZsa hZ2 hxU hx1 heig
  by_contra hcon
  have hcon : 1 ≤ q := not_lt.mp hcon
  have hnn := sq_nonneg ‖U.diagonalPart Z (x : H)‖
  have hq1 : q ^ 2 = 1 := by nlinarith [hCx, hnn]
  have hCx0 : U.diagonalPart Z (x : H) = 0 := by
    refine norm_eq_zero.mp ?_
    nlinarith [norm_nonneg (U.diagonalPart Z (x : H)), hCx, hq1]
  have hCSx0 : U.diagonalPart Z (U.offDiagonalPart Z (x : H)) = 0 := by
    refine norm_eq_zero.mp ?_
    nlinarith [norm_nonneg (U.diagonalPart Z (U.offDiagonalPart Z (x : H))),
      hCSx, hq1]
  have hmain := gap_mul_sq_le_paired_of_doubleAngleEigenvector hred hB hZsa
    hZdom hZcomm hUa hUb hxU hx1 heig
  rw [hCx0, hCSx0] at hmain
  simp only [map_zero, inner_zero_right, inner_zero_left, sub_zero] at hmain
  nlinarith [hmain, hq1, hab]

/-- The Gram identities an orthonormal family of exact `S²`-eigenvectors
satisfies.  Everything the Ky Fan step needs is an exact consequence of
`C² + S² = 1` and the eigenvector relation; nothing here is approximate. -/
theorem inner_of_doubleAngleEigenfamily
    (hZsa : IsSelfAdjoint Z) (hZ2 : Z * Z = 1) {n : ℕ} (x : Fin n → H)
    (hx : Orthonormal ℂ x) {q : Fin n → ℝ}
    (heig : ∀ i, U.offDiagonalPart Z (U.offDiagonalPart Z (x i)) =
      (((q i) ^ 2 : ℝ) : ℂ) • x i)
    (i j : Fin n) :
    ⟪U.offDiagonalPart Z (x i), U.offDiagonalPart Z (x j)⟫_ℂ =
        (((q j) ^ 2 : ℝ) : ℂ) * (if i = j then (1 : ℂ) else 0) ∧
      ⟪U.diagonalPart Z (x i), U.diagonalPart Z (x j)⟫_ℂ =
        ((1 - (q j) ^ 2 : ℝ) : ℂ) * (if i = j then (1 : ℂ) else 0) ∧
      ⟪U.diagonalPart Z (U.offDiagonalPart Z (x i)),
          U.diagonalPart Z (U.offDiagonalPart Z (x j))⟫_ℂ =
        (((q j) ^ 2 * (1 - (q j) ^ 2) : ℝ) : ℂ) *
          (if i = j then (1 : ℂ) else 0) := by
  classical
  have hSsym := TauCeti.inner_swap_of_isSelfAdjoint
    (TauCeti.isSelfAdjoint_offDiagonalPart (U := U) hZsa)
  have hCsym := TauCeti.inner_swap_of_isSelfAdjoint
    (TauCeti.isSelfAdjoint_diagonalPart (U := U) hZsa)
  have hite : ⟪x i, x j⟫_ℂ = if i = j then (1 : ℂ) else 0 :=
    (orthonormal_iff_ite.mp hx) i j
  have hpyth : ∀ v : H, U.diagonalPart Z (U.diagonalPart Z v) +
      U.offDiagonalPart Z (U.offDiagonalPart Z v) = v := by
    intro v
    have h := TauCeti.diagonalPart_sq_add_offDiagonalPart_sq (U := U) hZ2
    have h2 := congrArg (fun T : H →L[ℂ] H => T v) h
    simpa using h2
  have hSS : ⟪U.offDiagonalPart Z (x i), U.offDiagonalPart Z (x j)⟫_ℂ =
      (((q j) ^ 2 : ℝ) : ℂ) * (if i = j then (1 : ℂ) else 0) := by
    rw [hSsym (x i) (U.offDiagonalPart Z (x j)), heig j, inner_smul_right, hite]
  refine ⟨hSS, ?_, ?_⟩
  · have hCC : ⟪U.diagonalPart Z (x i), U.diagonalPart Z (x j)⟫_ℂ =
        ⟪x i, U.diagonalPart Z (U.diagonalPart Z (x j))⟫_ℂ :=
      hCsym (x i) (U.diagonalPart Z (x j))
    have hsplit : U.diagonalPart Z (U.diagonalPart Z (x j)) =
        x j - (((q j) ^ 2 : ℝ) : ℂ) • x j := by
      have h := hpyth (x j)
      rw [heig j] at h
      linear_combination (norm := module) h
    rw [hCC, hsplit, inner_sub_right, inner_smul_right, hite]
    push_cast
    ring
  · have hCC : ⟪U.diagonalPart Z (U.offDiagonalPart Z (x i)),
        U.diagonalPart Z (U.offDiagonalPart Z (x j))⟫_ℂ =
        ⟪U.offDiagonalPart Z (x i),
          U.diagonalPart Z (U.diagonalPart Z
            (U.offDiagonalPart Z (x j)))⟫_ℂ :=
      hCsym _ _
    have hSSS : U.offDiagonalPart Z (U.offDiagonalPart Z
        (U.offDiagonalPart Z (x j))) =
        (((q j) ^ 2 : ℝ) : ℂ) • U.offDiagonalPart Z (x j) := by
      rw [← map_smul, ← heig j]
    have hsplit : U.diagonalPart Z (U.diagonalPart Z
        (U.offDiagonalPart Z (x j))) =
        U.offDiagonalPart Z (x j) -
          (((q j) ^ 2 : ℝ) : ℂ) • U.offDiagonalPart Z (x j) := by
      have h := hpyth (U.offDiagonalPart Z (x j))
      rw [hSSS] at h
      linear_combination (norm := module) h
    rw [hCC, hsplit, inner_sub_right, inner_smul_right, hSS]
    push_cast
    ring

omit [CompleteSpace H] in
/-- Normalising a family whose Gram matrix is `cⱼ²` times the identity gives an
orthonormal family. -/
theorem orthonormal_scaled_of_inner_eq {n : ℕ} {f : Fin n → H}
    {c : Fin n → ℝ} (hc : ∀ i, 0 < c i)
    (h : ∀ i j, ⟪f i, f j⟫_ℂ =
      (((c j) ^ 2 : ℝ) : ℂ) * (if i = j then (1 : ℂ) else 0)) :
    Orthonormal ℂ fun i => (((c i : ℝ) : ℂ)⁻¹ • f i) := by
  classical
  rw [orthonormal_iff_ite]
  intro i j
  rw [inner_smul_left, inner_smul_right, h i j]
  rcases eq_or_ne i j with rfl | hne
  · rw [ite_eq_left rfl, mul_one, ← Complex.ofReal_inv, Complex.conj_ofReal,
      ← Complex.ofReal_mul, ← Complex.ofReal_mul, Complex.ofReal_eq_one]
    have hci := (hc i).ne'
    field_simp
  · simp [hne]

/-- **The unbounded, residual-form `tan 2Θ` theorem at every Ky Fan prefix, on an
exact double-angle eigenfamily.**

`A` is a possibly unbounded self-adjoint operator reduced by the trial subspace
`𝔛₀ = U`, the perturbation `B` is bounded and fully off-diagonal (the source's
residual case `H₀ = H₁ = 0`), `Z` is the reducing reflection `2Q - 1` of
`A + B`, the quadratic form of `A` is at most `a` on `𝔛₀` and at least `b` on
`𝔛₁`, and `δ = b - a > 0`.

If `x₀, …, x_{n-1}` is an orthonormal family in `𝔛₀ ∩ D(A)` of exact
eigenvectors of `sin² 2Θ` with eigenvalues `qᵢ² `, `qᵢ > 0`, then

`δ ∑ᵢ tan 2θᵢ ≤ 2 · kyFanApproximationGauge n B`,  `tan 2θᵢ = qᵢ / √(1 - qᵢ²)`.

The constant is the sharp `2` and the right-hand side is the residual, so this
is `δ N(tan 2Θ₀) ≤ 2 N(R)` at every Ky Fan gauge.

Scope, stated honestly.  At `n = 1` this is *weaker* than
`tanTwoTheta_unbounded_residual_opNorm_complex`, which needs no eigenvector: it bounds
`δ ‖sin 2Θ₀ x‖` against `2 ‖B‖ ‖cos 2Θ₀ x‖` at every trial vector.  What is new
here is `n ≥ 2`, which that theorem does not reach at all; the price is the
eigenfamily hypothesis, and removing it is the remaining work. -/
theorem gap_mul_sum_tangent_le_kyFan_of_doubleAngleEigenfamily
    (hred : TauCeti.LinearPMap.ReducesSubspace A U) (hB : TauCeti.IsOddFor U B)
    (hZsa : IsSelfAdjoint Z) (hZ2 : Z * Z = 1)
    (hZdom : TauCeti.LinearPMap.MapsDomainTo A A Z)
    (hZcomm : ∀ x : A.domain,
      A ⟨Z (x : H), hZdom x⟩ + B (Z (x : H)) = Z (A x) + Z (B (x : H)))
    (hUa : ∀ x : A.domain, (x : H) ∈ U →
      RCLike.re ⟪A x, (x : H)⟫_ℂ ≤ a * ‖(x : H)‖ ^ 2)
    (hUb : ∀ x : A.domain, (x : H) ∈ Uᗮ →
      b * ‖(x : H)‖ ^ 2 ≤ RCLike.re ⟪A x, (x : H)⟫_ℂ)
    (hab : a < b)
    {n : ℕ} (x : Fin n → A.domain)
    (hxU : ∀ i, ((x i : A.domain) : H) ∈ U)
    (hxon : Orthonormal ℂ fun i => ((x i : A.domain) : H))
    {q : Fin n → ℝ} (hq : ∀ i, 0 < q i)
    (heig : ∀ i, U.offDiagonalPart Z (U.offDiagonalPart Z
        ((x i : A.domain) : H)) =
      (((q i) ^ 2 : ℝ) : ℂ) • ((x i : A.domain) : H)) :
    (b - a) * ∑ i, q i / √(1 - (q i) ^ 2) ≤
      2 * kyFanApproximationGauge n B := by
  classical
  have hx1 : ∀ i, ‖((x i : A.domain) : H)‖ = 1 := fun i => hxon.norm_eq_one i
  have hq1 : ∀ i, q i < 1 := fun i =>
    doubleAngleEigenvalue_lt_one hred hB hZsa hZ2 hZdom hZcomm hUa hUb hab
      (hxU i) (hx1 i) (hq i) (heig i)
  have hc0 : ∀ i, 0 < 1 - (q i) ^ 2 := by
    intro i
    nlinarith [hq i, hq1 i]
  have hcpos : ∀ i, 0 < √(1 - (q i) ^ 2) := fun i => Real.sqrt_pos.mpr (hc0 i)
  have hgram := fun i j => inner_of_doubleAngleEigenfamily (U := U) hZsa hZ2
    (fun i => ((x i : A.domain) : H)) hxon heig i j
  -- the three auxiliary orthonormal systems
  have hyon : Orthonormal ℂ fun i =>
      (((q i : ℝ) : ℂ)⁻¹ • U.offDiagonalPart Z ((x i : A.domain) : H)) :=
    orthonormal_scaled_of_inner_eq hq fun i j => (hgram i j).1
  have huon : Orthonormal ℂ fun i =>
      (((√(1 - (q i) ^ 2) : ℝ) : ℂ)⁻¹ •
        U.diagonalPart Z ((x i : A.domain) : H)) :=
    orthonormal_scaled_of_inner_eq hcpos fun i j => by
      rw [Real.sq_sqrt (hc0 j).le]
      exact (hgram i j).2.1
  have hvon : Orthonormal ℂ fun i =>
      ((((q i * √(1 - (q i) ^ 2)) : ℝ) : ℂ)⁻¹ •
        U.diagonalPart Z (U.offDiagonalPart Z ((x i : A.domain) : H))) :=
    orthonormal_scaled_of_inner_eq
      (fun i => mul_pos (hq i) (hcpos i)) fun i j => by
        rw [mul_pow, Real.sq_sqrt (hc0 j).le]
        exact (hgram i j).2.2
  have hnegon : Orthonormal ℂ fun i =>
      -(((q i : ℝ) : ℂ)⁻¹ • U.offDiagonalPart Z ((x i : A.domain) : H)) := by
    have h := orthonormal_signFlip hyon (fun _ => false)
    simpa using h
  -- the per-index estimate, divided by `qᵢ cᵢ`
  have hstep : ∀ i, (b - a) * (q i / √(1 - (q i) ^ 2)) ≤
      RCLike.re ⟪(((q i * √(1 - (q i) ^ 2)) : ℝ) : ℂ)⁻¹ •
          U.diagonalPart Z (U.offDiagonalPart Z ((x i : A.domain) : H)),
        B ((x i : A.domain) : H)⟫_ℂ +
      RCLike.re ⟪-(((q i : ℝ) : ℂ)⁻¹ •
          U.offDiagonalPart Z ((x i : A.domain) : H)),
        B ((((√(1 - (q i) ^ 2) : ℝ) : ℂ)⁻¹ •
          U.diagonalPart Z ((x i : A.domain) : H)))⟫_ℂ := by
    intro i
    have hqc : 0 < q i * √(1 - (q i) ^ 2) := mul_pos (hq i) (hcpos i)
    have hmain := gap_mul_sq_le_paired_of_doubleAngleEigenvector hred hB hZsa
      hZdom hZcomm hUa hUb (hxU i) (hx1 i) (heig i)
    have hterm1 : RCLike.re ⟪(((q i * √(1 - (q i) ^ 2)) : ℝ) : ℂ)⁻¹ •
        U.diagonalPart Z (U.offDiagonalPart Z ((x i : A.domain) : H)),
        B ((x i : A.domain) : H)⟫_ℂ =
        (q i * √(1 - (q i) ^ 2))⁻¹ *
          RCLike.re ⟪B ((x i : A.domain) : H),
            U.diagonalPart Z (U.offDiagonalPart Z
              ((x i : A.domain) : H))⟫_ℂ := by
      rw [inner_smul_left, ← Complex.ofReal_inv, Complex.conj_ofReal,
        ← Complex.real_smul, RCLike.smul_re, inner_re_symm]
    have hterm2 : RCLike.re ⟪-(((q i : ℝ) : ℂ)⁻¹ •
        U.offDiagonalPart Z ((x i : A.domain) : H)),
        B ((((√(1 - (q i) ^ 2) : ℝ) : ℂ)⁻¹ •
          U.diagonalPart Z ((x i : A.domain) : H)))⟫_ℂ =
        -((q i * √(1 - (q i) ^ 2))⁻¹ *
          RCLike.re ⟪B (U.diagonalPart Z ((x i : A.domain) : H)),
            U.offDiagonalPart Z ((x i : A.domain) : H)⟫_ℂ) := by
      rw [mul_inv]
      simp only [map_smul, inner_neg_left, inner_smul_left, inner_smul_right,
        ← Complex.ofReal_inv, Complex.conj_ofReal]
      rw [mul_neg, ← mul_assoc, ← Complex.ofReal_mul, ← Complex.real_smul,
        map_neg, RCLike.smul_re, inner_re_symm]
      ring
    rw [hterm1, hterm2]
    have hdiv : (b - a) * (q i / √(1 - (q i) ^ 2)) =
        (q i * √(1 - (q i) ^ 2))⁻¹ * ((b - a) * (q i) ^ 2) := by
      field_simp
    rw [hdiv]
    have hpos : (0 : ℝ) ≤ (q i * √(1 - (q i) ^ 2))⁻¹ := by positivity
    nlinarith [mul_le_mul_of_nonneg_left hmain hpos]
  have hsum1 : ∑ i, RCLike.re ⟪(((q i * √(1 - (q i) ^ 2)) : ℝ) : ℂ)⁻¹ •
      U.diagonalPart Z (U.offDiagonalPart Z ((x i : A.domain) : H)),
      B ((x i : A.domain) : H)⟫_ℂ ≤ kyFanApproximationGauge n B :=
    sum_le_kyFanApproximationGauge_of_orthonormal B hvon hxon (fun _ => le_rfl)
  have hsum2 : ∑ i, RCLike.re ⟪-(((q i : ℝ) : ℂ)⁻¹ •
      U.offDiagonalPart Z ((x i : A.domain) : H)),
      B ((((√(1 - (q i) ^ 2) : ℝ) : ℂ)⁻¹ •
        U.diagonalPart Z ((x i : A.domain) : H)))⟫_ℂ ≤
      kyFanApproximationGauge n B :=
    sum_le_kyFanApproximationGauge_of_orthonormal B hnegon huon (fun _ => le_rfl)
  calc (b - a) * ∑ i, q i / √(1 - (q i) ^ 2)
      = ∑ i, (b - a) * (q i / √(1 - (q i) ^ 2)) := by rw [Finset.mul_sum]
    _ ≤ ∑ i, (RCLike.re ⟪(((q i * √(1 - (q i) ^ 2)) : ℝ) : ℂ)⁻¹ •
          U.diagonalPart Z (U.offDiagonalPart Z ((x i : A.domain) : H)),
          B ((x i : A.domain) : H)⟫_ℂ +
          RCLike.re ⟪-(((q i : ℝ) : ℂ)⁻¹ •
            U.offDiagonalPart Z ((x i : A.domain) : H)),
            B ((((√(1 - (q i) ^ 2) : ℝ) : ℂ)⁻¹ •
              U.diagonalPart Z ((x i : A.domain) : H)))⟫_ℂ) :=
        Finset.sum_le_sum fun i _ => hstep i
    _ = (∑ i, RCLike.re ⟪(((q i * √(1 - (q i) ^ 2)) : ℝ) : ℂ)⁻¹ •
          U.diagonalPart Z (U.offDiagonalPart Z ((x i : A.domain) : H)),
          B ((x i : A.domain) : H)⟫_ℂ) +
        ∑ i, RCLike.re ⟪-(((q i : ℝ) : ℂ)⁻¹ •
          U.offDiagonalPart Z ((x i : A.domain) : H)),
          B ((((√(1 - (q i) ^ 2) : ℝ) : ℂ)⁻¹ •
            U.diagonalPart Z ((x i : A.domain) : H)))⟫_ℂ :=
        Finset.sum_add_distrib
    _ ≤ 2 * kyFanApproximationGauge n B := by linarith [hsum1, hsum2]

/-- A trial-subspace eigenbasis for `sin² 2Θ` realising the Ky Fan prefixes of a
candidate tangent operator.

`T` is the candidate `tan 2Θ₀`; the last clause says its Ky Fan prefix of length
`k` is realised, from below, by an orthonormal family of exact `sin² 2Θ`
eigenvectors inside `𝔛₀ ∩ D(A)`.  This is the only way the tangent's singular
values enter: nothing about `T` beyond its approximation numbers is used. -/
def IsDoubleAngleEigenbasis (A : H →ₗ.[ℂ] H) (U : Submodule ℂ H)
    [U.HasOrthogonalProjection] (Z T : H →L[ℂ] H) : Prop :=
  ∀ k : ℕ, ∃ (y : Fin k → A.domain) (q : Fin k → ℝ),
    (∀ i, ((y i : A.domain) : H) ∈ U) ∧
      (Orthonormal ℂ fun i => ((y i : A.domain) : H)) ∧
      (∀ i, 0 < q i) ∧
      (∀ i, U.offDiagonalPart Z (U.offDiagonalPart Z ((y i : A.domain) : H)) =
        (((q i) ^ 2 : ℝ) : ℂ) • ((y i : A.domain) : H)) ∧
      kyFanApproximationGauge k T ≤ ∑ i, q i / √(1 - (q i) ^ 2)

/-- **The unbounded residual `tan 2Θ` theorem at every Ky Fan gauge.**

`δ · kyFanApproximationGauge k T ≤ 2 · kyFanApproximationGauge k B` for every
prefix length `k`, whenever `T` is a tangent operator whose prefixes are
realised by exact `sin² 2Θ` eigenfamilies of the trial subspace. -/
theorem gap_mul_kyFan_le_two_mul_kyFan_of_doubleAngleEigenbasis
    (hred : TauCeti.LinearPMap.ReducesSubspace A U) (hB : TauCeti.IsOddFor U B)
    (hZsa : IsSelfAdjoint Z) (hZ2 : Z * Z = 1)
    (hZdom : TauCeti.LinearPMap.MapsDomainTo A A Z)
    (hZcomm : ∀ x : A.domain,
      A ⟨Z (x : H), hZdom x⟩ + B (Z (x : H)) = Z (A x) + Z (B (x : H)))
    (hUa : ∀ x : A.domain, (x : H) ∈ U →
      RCLike.re ⟪A x, (x : H)⟫_ℂ ≤ a * ‖(x : H)‖ ^ 2)
    (hUb : ∀ x : A.domain, (x : H) ∈ Uᗮ →
      b * ‖(x : H)‖ ^ 2 ≤ RCLike.re ⟪A x, (x : H)⟫_ℂ)
    (hab : a < b) {T : H →L[ℂ] H}
    (hT : IsDoubleAngleEigenbasis A U Z T) (k : ℕ) :
    (b - a) * kyFanApproximationGauge k T ≤
      2 * kyFanApproximationGauge k B := by
  obtain ⟨y, q, hyU, hyon, hqpos, hyeig, hle⟩ := hT k
  have hmain := gap_mul_sum_tangent_le_kyFan_of_doubleAngleEigenfamily hred hB
    hZsa hZ2 hZdom hZcomm hUa hUb hab y hyU hyon hqpos hyeig
  have hδ : (0 : ℝ) ≤ b - a := by linarith
  nlinarith [mul_le_mul_of_nonneg_left hle hδ, hmain]

/-- **The unbounded, residual-form `tan 2Θ` theorem at every Fan-dominant
unitarily invariant ideal gauge.**

`δ N(tan 2Θ₀) ≤ 2 N(R)` in the scaled form the repository uses for sharp
constants: the tangent carries the factor `δ / 2` and is compared with the
residual `B` itself, so no gauge of a scalar multiple of `B` is needed.  Ideal
membership of the scaled tangent is concluded, not assumed. -/
theorem mem_and_gauge_le_of_doubleAngleEigenbasis
    (N : KyFanDominantIdealFamily (𝕜 := ℂ))
    (hred : TauCeti.LinearPMap.ReducesSubspace A U) (hB : TauCeti.IsOddFor U B)
    (hZsa : IsSelfAdjoint Z) (hZ2 : Z * Z = 1)
    (hZdom : TauCeti.LinearPMap.MapsDomainTo A A Z)
    (hZcomm : ∀ x : A.domain,
      A ⟨Z (x : H), hZdom x⟩ + B (Z (x : H)) = Z (A x) + Z (B (x : H)))
    (hUa : ∀ x : A.domain, (x : H) ∈ U →
      RCLike.re ⟪A x, (x : H)⟫_ℂ ≤ a * ‖(x : H)‖ ^ 2)
    (hUb : ∀ x : A.domain, (x : H) ∈ Uᗮ →
      b * ‖(x : H)‖ ^ 2 ≤ RCLike.re ⟪A x, (x : H)⟫_ℂ)
    (hab : a < b) {T : H →L[ℂ] H}
    (hT : IsDoubleAngleEigenbasis A U Z T) (hBmem : N.Mem B) :
    N.Mem ((((b - a) / 2 : ℝ) : ℂ) • T) ∧
      N.gauge ((((b - a) / 2 : ℝ) : ℂ) • T) ≤ N.gauge B := by
  refine mem_and_gauge_le_of_all_kyFanApproximationGauge_le
    N.toFanDominantIdealFamily hBmem fun k => ?_
  rw [kyFanApproximationGauge_smul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (by linarith : (0 : ℝ) ≤ (b - a) / 2)]
  have h := gap_mul_kyFan_le_two_mul_kyFan_of_doubleAngleEigenbasis hred hB hZsa
    hZ2 hZdom hZcomm hUa hUb hab hT k
  linarith

/-!
## Approximate double-angle eigenfamilies

Everything above is conditional on an *exact* eigenfamily of `sin² 2Θ` inside
`𝔛₀ ∩ D(A)`, and such a family need not exist: the compressed block
`Ω S² Ω` is a bounded self-adjoint operator and may have empty point spectrum.
What a spectral selection does produce is an *approximate* eigenfamily inside a
bounded cutoff `Ω`, and the results below are the exact-eigenfamily arguments
re-run against one.

Two structural facts make the passage possible and are recorded here because
neither is visible from the exact statements.

* **Only the compressed residual is ever paired with `A`.**  A vector `x` fixed
  by the cutoff has `A x` fixed by the cutoff too, so `⟪A x, S² x⟫ = ⟪A x, Ω S²
  Ω x⟫`.  The defect that has to be small is therefore
  `‖Ω S² Ω x - q² x‖`, not `‖S² x - q² x‖`.
* **Normalisation destroys orthonormality but not contractivity.**  At an exact
  eigenfamily the three systems `S xᵢ / qᵢ`, `C xᵢ / cᵢ` and `C (S xᵢ) / (qᵢ cᵢ)`
  are exactly orthonormal.  At an approximate one they are not, and for the
  third the defect is genuinely *not* controlled by the compressed residual:
  `‖C S g‖² = ‖S g‖² - ‖S² g‖²` and `‖S² g‖ ≥ ‖Ω S² g‖` only one way.  That
  inequality has the favourable sign, so the system is still a contraction, and
  `sum_le_kyFanApproximationGauge_of_contraction` consumes exactly that.
-/

/-- The Gram defect of the odd block at an approximate double-angle
eigenvector: `| ‖S x‖² - q² | ≤ ε`.  Only the *compressed* defect enters,
because `x` is fixed by the cutoff. -/
theorem abs_norm_sq_offDiagonalPart_sub_le_of_approximate
    (hZsa : IsSelfAdjoint Z) (Ω : TauCeti.BoundedCutoff A U τ) {x : H}
    (hxΩ : Ω.toProj x = x) (hx1 : ‖x‖ = 1) {q ε : ℝ}
    (heig : ‖Ω.toProj (U.offDiagonalPart Z (U.offDiagonalPart Z x)) -
      ((q ^ 2 : ℝ) : ℂ) • x‖ ≤ ε) :
    |‖U.offDiagonalPart Z x‖ ^ 2 - q ^ 2| ≤ ε := by
  have hSsym := TauCeti.inner_swap_of_isSelfAdjoint
    (TauCeti.isSelfAdjoint_offDiagonalPart (U := U) hZsa)
  have hΩsym := TauCeti.inner_swap_of_isSelfAdjoint Ω.isSelfAdjoint
  have hd : RCLike.re ⟪x, Ω.toProj (U.offDiagonalPart Z
        (U.offDiagonalPart Z x)) - ((q ^ 2 : ℝ) : ℂ) • x⟫_ℂ =
      ‖U.offDiagonalPart Z x‖ ^ 2 - q ^ 2 := by
    have h1 : ⟪x, Ω.toProj (U.offDiagonalPart Z
        (U.offDiagonalPart Z x))⟫_ℂ =
        ⟪U.offDiagonalPart Z x, U.offDiagonalPart Z x⟫_ℂ := by
      rw [← hΩsym x (U.offDiagonalPart Z (U.offDiagonalPart Z x)), hxΩ,
        ← hSsym x (U.offDiagonalPart Z x)]
    rw [inner_sub_right, inner_smul_right, h1, inner_self_eq_norm_sq_to_K,
      inner_self_eq_norm_sq_to_K, hx1]
    simp [← Complex.ofReal_pow]
  calc |‖U.offDiagonalPart Z x‖ ^ 2 - q ^ 2|
      = |RCLike.re ⟪x, Ω.toProj (U.offDiagonalPart Z
          (U.offDiagonalPart Z x)) - ((q ^ 2 : ℝ) : ℂ) • x⟫_ℂ| := by rw [hd]
    _ ≤ ‖⟪x, Ω.toProj (U.offDiagonalPart Z (U.offDiagonalPart Z x)) -
          ((q ^ 2 : ℝ) : ℂ) • x⟫_ℂ‖ := Complex.abs_re_le_norm _
    _ ≤ ‖x‖ * ‖Ω.toProj (U.offDiagonalPart Z (U.offDiagonalPart Z x)) -
          ((q ^ 2 : ℝ) : ℂ) • x‖ := norm_inner_le_norm _ _
    _ ≤ ε := by rw [hx1, one_mul]; exact heig

/-- **Equation (7.6) at an approximate double-angle eigenvector.**

The exact-eigenvector estimate `gap_mul_sq_le_paired_of_doubleAngleEigenvector`
with the eigenvector relation replaced by the compressed defect bound
`‖Ω S² Ω x - q² x‖ ≤ ε`, at a unit vector `x` fixed by a bounded cutoff of level
`τ`.  The cost is a single additive error `(τ + |b|) ε`:

* `τ ε` from `⟪A x, Ω S² Ω x - q² x⟫`, which is where the unboundedness of `A`
  is met and where the cutoff is used;
* `|b| ε` from replacing `‖S x‖²` by `q²` in the trial-side form bound.

**No norm of `A` occurs**, and no uncompressed residual is ever paired with
`A`. -/
theorem gap_mul_sq_le_paired_of_approximateDoubleAngleEigenvector
    (hred : TauCeti.LinearPMap.ReducesSubspace A U) (hB : TauCeti.IsOddFor U B)
    (hZsa : IsSelfAdjoint Z)
    (hZdom : TauCeti.LinearPMap.MapsDomainTo A A Z)
    (hZcomm : ∀ x : A.domain,
      A ⟨Z (x : H), hZdom x⟩ + B (Z (x : H)) = Z (A x) + Z (B (x : H)))
    (hUa : ∀ x : A.domain, (x : H) ∈ U →
      RCLike.re ⟪A x, (x : H)⟫_ℂ ≤ a * ‖(x : H)‖ ^ 2)
    (hUb : ∀ x : A.domain, (x : H) ∈ Uᗮ →
      b * ‖(x : H)‖ ^ 2 ≤ RCLike.re ⟪A x, (x : H)⟫_ℂ)
    (Ω : TauCeti.BoundedCutoff A U τ) {x : H}
    (hxΩ : Ω.toProj x = x) (hx1 : ‖x‖ = 1) {q ε : ℝ}
    (heig : ‖Ω.toProj (U.offDiagonalPart Z (U.offDiagonalPart Z x)) -
      ((q ^ 2 : ℝ) : ℂ) • x‖ ≤ ε) :
    (b - a) * q ^ 2 ≤ (τ + |b|) * ε +
      (RCLike.re ⟪B x, U.diagonalPart Z (U.offDiagonalPart Z x)⟫_ℂ -
        RCLike.re ⟪B (U.diagonalPart Z x), U.offDiagonalPart Z x⟫_ℂ) := by
  classical
  have hSsym := TauCeti.inner_swap_of_isSelfAdjoint
    (TauCeti.isSelfAdjoint_offDiagonalPart (U := U) hZsa)
  have hCsym := TauCeti.inner_swap_of_isSelfAdjoint
    (TauCeti.isSelfAdjoint_diagonalPart (U := U) hZsa)
  have hΩsym := TauCeti.inner_swap_of_isSelfAdjoint Ω.isSelfAdjoint
  have hxdom : x ∈ A.domain := Ω.mem_domain_of_eq hxΩ
  have hxU : x ∈ U := Ω.mem_subspace_of_eq hxΩ
  have hSmem : U.offDiagonalPart Z x ∈ A.domain :=
    TauCeti.mem_domain_offDiagonalPart hred hZdom ⟨x, hxdom⟩
  have hSU : U.offDiagonalPart Z x ∈ Uᗮ :=
    TauCeti.offDiagonalPart_mem_orthogonal_of_mem U Z hxU
  have hsyl := TauCeti.sylvester_offDiagonalPart_of_mem hred hB hZdom hZcomm
    ⟨x, hxdom⟩ hxU
  have hpair := congrArg
    (fun w : H => RCLike.re ⟪w, U.offDiagonalPart Z x⟫_ℂ) hsyl
  simp only [inner_add_left, map_add] at hpair
  have hlow : b * ‖U.offDiagonalPart Z x‖ ^ 2 ≤
      RCLike.re ⟪A ⟨U.offDiagonalPart Z x, hSmem⟩, U.offDiagonalPart Z x⟫_ℂ :=
    hUb ⟨U.offDiagonalPart Z x, hSmem⟩ hSU
  have hgram : |‖U.offDiagonalPart Z x‖ ^ 2 - q ^ 2| ≤ ε :=
    abs_norm_sq_offDiagonalPart_sub_le_of_approximate hZsa Ω hxΩ hx1 heig
  have hblow : b * q ^ 2 - |b| * ε ≤ b * ‖U.offDiagonalPart Z x‖ ^ 2 := by
    have hkey : |b * (‖U.offDiagonalPart Z x‖ ^ 2 - q ^ 2)| ≤ |b| * ε := by
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_left hgram (abs_nonneg b)
    nlinarith [neg_le_of_abs_le hkey]
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
  have hhigh : RCLike.re ⟪U.offDiagonalPart Z (A ⟨x, hxdom⟩),
      U.offDiagonalPart Z x⟫_ℂ ≤ a * q ^ 2 + τ * ε := by
    have h1 : ⟪U.offDiagonalPart Z (A ⟨x, hxdom⟩),
        U.offDiagonalPart Z x⟫_ℂ =
        ⟪A ⟨x, hxdom⟩, U.offDiagonalPart Z (U.offDiagonalPart Z x)⟫_ℂ :=
      hSsym (A ⟨x, hxdom⟩) (U.offDiagonalPart Z x)
    have h2 : ⟪A ⟨x, hxdom⟩,
        U.offDiagonalPart Z (U.offDiagonalPart Z x)⟫_ℂ =
        ⟪A ⟨x, hxdom⟩,
          Ω.toProj (U.offDiagonalPart Z (U.offDiagonalPart Z x))⟫_ℂ := by
      rw [← hΩsym (A ⟨x, hxdom⟩)
        (U.offDiagonalPart Z (U.offDiagonalPart Z x)), hAxfix]
    have h3 : ⟪A ⟨x, hxdom⟩,
        Ω.toProj (U.offDiagonalPart Z (U.offDiagonalPart Z x))⟫_ℂ =
        ((q ^ 2 : ℝ) : ℂ) * ⟪A ⟨x, hxdom⟩, x⟫_ℂ +
          ⟪A ⟨x, hxdom⟩, Ω.toProj (U.offDiagonalPart Z
            (U.offDiagonalPart Z x)) - ((q ^ 2 : ℝ) : ℂ) • x⟫_ℂ := by
      rw [inner_sub_right, inner_smul_right]
      ring
    rw [h1, h2, h3]
    have hform : RCLike.re ⟪A ⟨x, hxdom⟩, x⟫_ℂ ≤ a := by
      have h := hUa ⟨x, hxdom⟩ hxU
      rwa [hx1, one_pow, mul_one] at h
    have hleak : RCLike.re ⟪A ⟨x, hxdom⟩,
        Ω.toProj (U.offDiagonalPart Z (U.offDiagonalPart Z x)) -
          ((q ^ 2 : ℝ) : ℂ) • x⟫_ℂ ≤ τ * ε := by
      refine le_trans (le_abs_self _) ?_
      refine le_trans (Complex.abs_re_le_norm _) ?_
      refine le_trans (norm_inner_le_norm _ _) ?_
      exact mul_le_mul hAxnorm heig (norm_nonneg _)
        (le_trans (norm_nonneg _) hAxnorm)
    rw [map_add, ← Complex.real_smul, RCLike.smul_re]
    nlinarith [hform, hleak, sq_nonneg q]
  have hmove : RCLike.re ⟪U.diagonalPart Z (B x), U.offDiagonalPart Z x⟫_ℂ =
      RCLike.re ⟪B x, U.diagonalPart Z (U.offDiagonalPart Z x)⟫_ℂ := by
    rw [hCsym (B x) (U.offDiagonalPart Z x)]
  linarith [hpair, hlow, hhigh, hblow, hmove]

/-- The double-angle Pythagoras identity at an arbitrary vector: `‖C v‖² =
‖v‖² - ‖S v‖²`, a consequence of `C² + S² = 1` alone. -/
theorem norm_sq_diagonalPart_apply (hZsa : IsSelfAdjoint Z) (hZ2 : Z * Z = 1)
    (v : H) :
    ‖U.diagonalPart Z v‖ ^ 2 =
      ‖v‖ ^ 2 - ‖U.offDiagonalPart Z v‖ ^ 2 := by
  have hCsym := TauCeti.inner_swap_of_isSelfAdjoint
    (TauCeti.isSelfAdjoint_diagonalPart (U := U) hZsa)
  have hSsym := TauCeti.inner_swap_of_isSelfAdjoint
    (TauCeti.isSelfAdjoint_offDiagonalPart (U := U) hZsa)
  have hpyth : U.diagonalPart Z (U.diagonalPart Z v) +
      U.offDiagonalPart Z (U.offDiagonalPart Z v) = v := by
    have h := TauCeti.diagonalPart_sq_add_offDiagonalPart_sq (U := U) hZ2
    have h2 := congrArg (fun T : H →L[ℂ] H => T v) h
    simpa using h2
  have hCC : ⟪U.diagonalPart Z v, U.diagonalPart Z v⟫_ℂ =
      ⟪v, U.diagonalPart Z (U.diagonalPart Z v)⟫_ℂ := hCsym v _
  have hSS : ⟪U.offDiagonalPart Z v, U.offDiagonalPart Z v⟫_ℂ =
      ⟪v, U.offDiagonalPart Z (U.offDiagonalPart Z v)⟫_ℂ := hSsym v _
  have hsum : ⟪U.diagonalPart Z v, U.diagonalPart Z v⟫_ℂ +
      ⟪U.offDiagonalPart Z v, U.offDiagonalPart Z v⟫_ℂ = ⟪v, v⟫_ℂ := by
    rw [hCC, hSS, ← inner_add_right, hpyth]
  have h := congrArg RCLike.re hsum
  simp only [map_add, inner_self_eq_norm_sq_to_K] at h
  simp [← Complex.ofReal_pow] at h
  linarith

/-- **The compressed Gram estimate on a whole linear combination.**

For an orthonormal family `x` inside the cutoff range with compressed defects
`‖Ω S² Ω xᵢ - qᵢ² xᵢ‖ ≤ ε`, the odd block of `g = ∑ γᵢ xᵢ` satisfies

`| ‖S g‖² - ∑ᵢ |γᵢ|² qᵢ² | ≤ n ε ∑ᵢ |γᵢ|²`.

This is the statement that turns the three normalised systems into contraction
systems, and it is the only place the defect bound is used quantitatively. -/
theorem abs_norm_sq_offDiagonalPart_sum_sub_le
    (hZsa : IsSelfAdjoint Z) (Ω : TauCeti.BoundedCutoff A U τ)
    {n : ℕ} {x : Fin n → H}
    (hx : Orthonormal ℂ x) (hxΩ : ∀ i, Ω.toProj (x i) = x i)
    {q : Fin n → ℝ} {ε : ℝ}
    (heig : ∀ i, ‖Ω.toProj (U.offDiagonalPart Z (U.offDiagonalPart Z (x i))) -
      ((q i ^ 2 : ℝ) : ℂ) • x i‖ ≤ ε)
    (γ : Fin n → ℂ) :
    |‖U.offDiagonalPart Z (∑ i, γ i • x i)‖ ^ 2 -
        ∑ i, ‖γ i‖ ^ 2 * q i ^ 2| ≤
      n * ε * ∑ i, ‖γ i‖ ^ 2 := by
  classical
  set g : H := ∑ i, γ i • x i with hgdef
  set d : Fin n → H := fun i =>
    Ω.toProj (U.offDiagonalPart Z (U.offDiagonalPart Z (x i))) -
      ((q i ^ 2 : ℝ) : ℂ) • x i with hddef
  have hSsym := TauCeti.inner_swap_of_isSelfAdjoint
    (TauCeti.isSelfAdjoint_offDiagonalPart (U := U) hZsa)
  have hΩsym := TauCeti.inner_swap_of_isSelfAdjoint Ω.isSelfAdjoint
  have hgΩ : Ω.toProj g = g := by
    rw [hgdef, map_sum]
    exact Finset.sum_congr rfl fun i _ => by rw [map_smul, hxΩ i]
  have hgnorm : ‖g‖ ^ 2 = ∑ i, ‖γ i‖ ^ 2 :=
    norm_sq_sum_smul_of_orthonormal hx γ
  have hsplit : Ω.toProj (U.offDiagonalPart Z (U.offDiagonalPart Z g)) =
      (∑ i, (γ i * ((q i ^ 2 : ℝ) : ℂ)) • x i) + ∑ i, γ i • d i := by
    rw [hgdef, map_sum, map_sum, map_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_smul, map_smul, map_smul, hddef]
    simp only [smul_sub, smul_smul]
    module
  have hDnorm : ‖∑ i, γ i • d i‖ ≤ n * ε * ‖g‖ := by
    refine le_trans (norm_sum_le _ _) ?_
    have hbd : ∀ i : Fin n, ‖γ i • d i‖ ≤ ‖g‖ * ε := by
      intro i
      rw [norm_smul]
      have hγ : ‖γ i‖ ≤ ‖g‖ := by
        have h1 : ‖γ i‖ ^ 2 ≤ ∑ j, ‖γ j‖ ^ 2 :=
          Finset.single_le_sum (f := fun j => ‖γ j‖ ^ 2)
            (fun j _ => sq_nonneg _) (Finset.mem_univ i)
        nlinarith [norm_nonneg (γ i), norm_nonneg g, hgnorm, h1]
      exact mul_le_mul hγ (heig i) (norm_nonneg _) (norm_nonneg g)
    calc ∑ i, ‖γ i • d i‖ ≤ ∑ _i : Fin n, ‖g‖ * ε :=
          Finset.sum_le_sum fun i _ => hbd i
      _ = n * ε * ‖g‖ := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
          ring
  have hkey : ‖U.offDiagonalPart Z g‖ ^ 2 =
      RCLike.re ⟪g, Ω.toProj (U.offDiagonalPart Z
        (U.offDiagonalPart Z g))⟫_ℂ := by
    have h1 : ⟪g, Ω.toProj (U.offDiagonalPart Z
        (U.offDiagonalPart Z g))⟫_ℂ =
        ⟪U.offDiagonalPart Z g, U.offDiagonalPart Z g⟫_ℂ := by
      rw [← hΩsym g (U.offDiagonalPart Z (U.offDiagonalPart Z g)), hgΩ,
        ← hSsym g (U.offDiagonalPart Z g)]
    rw [h1, inner_self_eq_norm_sq_to_K]
    simp [← Complex.ofReal_pow]
  rw [hkey, hsplit, inner_add_right, map_add]
  have hmain : RCLike.re ⟪g, ∑ i, (γ i * ((q i ^ 2 : ℝ) : ℂ)) • x i⟫_ℂ =
      ∑ i, ‖γ i‖ ^ 2 * q i ^ 2 := by
    have h := hx.inner_sum γ (fun i => γ i * ((q i ^ 2 : ℝ) : ℂ)) Finset.univ
    rw [hgdef, h, map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← mul_assoc, RCLike.conj_mul]
    simp [← Complex.ofReal_pow]
  rw [hmain]
  have herr : |RCLike.re ⟪g, ∑ i, γ i • d i⟫_ℂ| ≤ n * ε * ∑ i, ‖γ i‖ ^ 2 := by
    refine le_trans (Complex.abs_re_le_norm _) ?_
    refine le_trans (norm_inner_le_norm _ _) ?_
    calc ‖g‖ * ‖∑ i, γ i • d i‖ ≤ ‖g‖ * (n * ε * ‖g‖) :=
          mul_le_mul_of_nonneg_left hDnorm (norm_nonneg g)
      _ = n * ε * ‖g‖ ^ 2 := by ring
      _ = n * ε * ∑ i, ‖γ i‖ ^ 2 := by rw [hgnorm]
  simpa using herr

/-!
## Compressed double-angle eigenfamilies

The exact eigenfamily hypothesis asks `S² xᵢ = qᵢ² xᵢ` in all of `H`, and that
is more than the argument uses.  Diagonalising the *compression* `P_W S² P_W` of
`S²` to a finite-dimensional trial space `W ⊆ 𝔛₀ ∩ D(A)` — which is always
possible, `P_W S² P_W` being a self-adjoint operator on a finite-dimensional
space — gives an orthonormal basis `xᵢ` of `W` with

`S² xᵢ = qᵢ² xᵢ + rᵢ`,   `rᵢ ⊥ W`.

Two hypotheses on the leakage `rᵢ` are what the whole argument needs:

* `hgram`, that `rᵢ ⊥ xⱼ` for every `j`, which is the defining property of the
  compression;
* `hres`, that `Re ⟪A xᵢ, rᵢ⟫ ≤ 0`, which holds outright when `W` is
  `A`-invariant, and holds trivially when `rᵢ = 0`.

Both are implied by an exact eigenfamily (`rᵢ = 0`), so everything below is
strictly more general than the corresponding exact statement; see
`isCompressedDoubleAngleEigenbasis_of_isDoubleAngleEigenbasis`.

The Gram identities of the first three auxiliary systems survive *exactly* —
they only ever pair members of `W` — and only the fourth,
`C S xᵢ / (qᵢ cᵢ)`, acquires a defect.  That defect has a favourable sign: its
Gram operator is `1 - D⁻¹ R⋆ R D⁻¹ ≤ 1`, so the system is a contraction system
and `sum_le_kyFanApproximationGauge_of_contraction` applies with constant `1`.
**The sharp factor `2` is therefore untouched.**
-/

/-- The squared length of the odd block, from the diagonal compressed Gram
entry alone.  No eigenvector relation is needed: `‖S x‖² = ⟪x, S² x⟫`. -/
theorem norm_sq_offDiagonalPart_of_compressedDiagonal
    (hZsa : IsSelfAdjoint Z) {x : H} {q : ℝ}
    (hself : ⟪x, U.offDiagonalPart Z (U.offDiagonalPart Z x)⟫_ℂ =
      ((q ^ 2 : ℝ) : ℂ)) :
    ‖U.offDiagonalPart Z x‖ ^ 2 = q ^ 2 := by
  have hSsym := TauCeti.inner_swap_of_isSelfAdjoint
    (TauCeti.isSelfAdjoint_offDiagonalPart (U := U) hZsa)
  have h : ⟪U.offDiagonalPart Z x, U.offDiagonalPart Z x⟫_ℂ =
      ((q ^ 2 : ℝ) : ℂ) := by
    rw [hSsym x (U.offDiagonalPart Z x)]
    exact hself
  have h2 : ((‖U.offDiagonalPart Z x‖ ^ 2 : ℝ) : ℂ) = ((q ^ 2 : ℝ) : ℂ) := by
    rw [← h, inner_self_eq_norm_sq_to_K]
    norm_cast
  exact_mod_cast h2

/-- **Equation (7.6) at a compressed double-angle eigenvector.**

The exact-eigenvector estimate `gap_mul_sq_le_paired_of_doubleAngleEigenvector`
with the global relation `S² x = q² x` replaced by the two compressed facts

* `⟪x, S² x⟫ = q²`, the diagonal Gram entry;
* `Re ⟪A x, S² x - q² x⟫ ≤ 0`, the leakage sign condition.

**No norm of `A` occurs and no error term appears**: the leakage is not
estimated, it is annihilated by the sign condition.  When `x` is an exact
eigenvector the leakage vanishes and both hypotheses are trivial. -/
theorem gap_mul_sq_le_paired_of_compressedDoubleAngleEigenvector
    (hred : TauCeti.LinearPMap.ReducesSubspace A U) (hB : TauCeti.IsOddFor U B)
    (hZsa : IsSelfAdjoint Z)
    (hZdom : TauCeti.LinearPMap.MapsDomainTo A A Z)
    (hZcomm : ∀ x : A.domain,
      A ⟨Z (x : H), hZdom x⟩ + B (Z (x : H)) = Z (A x) + Z (B (x : H)))
    (hUa : ∀ x : A.domain, (x : H) ∈ U →
      RCLike.re ⟪A x, (x : H)⟫_ℂ ≤ a * ‖(x : H)‖ ^ 2)
    (hUb : ∀ x : A.domain, (x : H) ∈ Uᗮ →
      b * ‖(x : H)‖ ^ 2 ≤ RCLike.re ⟪A x, (x : H)⟫_ℂ)
    {x : A.domain} (hxU : (x : H) ∈ U) (hx1 : ‖(x : H)‖ = 1) {q : ℝ}
    (hself : ⟪(x : H), U.offDiagonalPart Z
      (U.offDiagonalPart Z (x : H))⟫_ℂ = ((q ^ 2 : ℝ) : ℂ))
    (hres : RCLike.re ⟪A x, U.offDiagonalPart Z
        (U.offDiagonalPart Z (x : H)) - ((q ^ 2 : ℝ) : ℂ) • (x : H)⟫_ℂ ≤ 0) :
    (b - a) * q ^ 2 ≤
      RCLike.re ⟪B (x : H),
          U.diagonalPart Z (U.offDiagonalPart Z (x : H))⟫_ℂ -
        RCLike.re ⟪B (U.diagonalPart Z (x : H)),
          U.offDiagonalPart Z (x : H)⟫_ℂ := by
  have hSsym := TauCeti.inner_swap_of_isSelfAdjoint
    (TauCeti.isSelfAdjoint_offDiagonalPart (U := U) hZsa)
  have hCsym := TauCeti.inner_swap_of_isSelfAdjoint
    (TauCeti.isSelfAdjoint_diagonalPart (U := U) hZsa)
  have hSmem : U.offDiagonalPart Z (x : H) ∈ A.domain :=
    TauCeti.mem_domain_offDiagonalPart hred hZdom x
  have hSU : U.offDiagonalPart Z (x : H) ∈ Uᗮ :=
    TauCeti.offDiagonalPart_mem_orthogonal_of_mem U Z hxU
  have hnormS : ‖U.offDiagonalPart Z (x : H)‖ ^ 2 = q ^ 2 :=
    norm_sq_offDiagonalPart_of_compressedDiagonal (U := U) hZsa hself
  have hsyl := TauCeti.sylvester_offDiagonalPart_of_mem hred hB hZdom hZcomm x hxU
  have hpair := congrArg
    (fun w : H => RCLike.re ⟪w, U.offDiagonalPart Z (x : H)⟫_ℂ) hsyl
  simp only [inner_add_left, map_add] at hpair
  have hlow : b * q ^ 2 ≤
      RCLike.re ⟪A ⟨U.offDiagonalPart Z (x : H), hSmem⟩,
        U.offDiagonalPart Z (x : H)⟫_ℂ := by
    have h := hUb ⟨U.offDiagonalPart Z (x : H), hSmem⟩ hSU
    calc b * q ^ 2 = b * ‖U.offDiagonalPart Z (x : H)‖ ^ 2 := by rw [hnormS]
      _ ≤ _ := h
  have hhigh : RCLike.re ⟪U.offDiagonalPart Z (A x),
      U.offDiagonalPart Z (x : H)⟫_ℂ ≤ a * q ^ 2 := by
    have hswap : ⟪U.offDiagonalPart Z (A x), U.offDiagonalPart Z (x : H)⟫_ℂ =
        ((q ^ 2 : ℝ) : ℂ) * ⟪A x, (x : H)⟫_ℂ +
          ⟪A x, U.offDiagonalPart Z (U.offDiagonalPart Z (x : H)) -
            ((q ^ 2 : ℝ) : ℂ) • (x : H)⟫_ℂ := by
      rw [hSsym (A x) (U.offDiagonalPart Z (x : H)), inner_sub_right,
        inner_smul_right]
      ring
    rw [hswap, map_add, ← Complex.real_smul, RCLike.smul_re]
    have hx := hUa x hxU
    rw [hx1, one_pow, mul_one] at hx
    nlinarith [sq_nonneg q, hx, hres]
  have hmove : RCLike.re ⟪U.diagonalPart Z (B (x : H)),
      U.offDiagonalPart Z (x : H)⟫_ℂ =
      RCLike.re ⟪B (x : H),
        U.diagonalPart Z (U.offDiagonalPart Z (x : H))⟫_ℂ := by
    rw [hCsym (B (x : H)) (U.offDiagonalPart Z (x : H))]
  rw [hmove] at hpair
  linarith [hpair, hlow, hhigh]

/-- The two double-angle Pythagoras facts at a compressed eigenvector.  The
first is still an identity; the second becomes an *inequality* in the direction
the contraction argument needs, the deficit being the leakage `‖S² x‖² - q⁴`. -/
theorem norm_sq_diagonalPart_of_compressedDiagonal
    (hZsa : IsSelfAdjoint Z) (hZ2 : Z * Z = 1)
    {x : H} (hx1 : ‖x‖ = 1) {q : ℝ}
    (hself : ⟪x, U.offDiagonalPart Z (U.offDiagonalPart Z x)⟫_ℂ =
      ((q ^ 2 : ℝ) : ℂ)) :
    ‖U.diagonalPart Z x‖ ^ 2 = 1 - q ^ 2 ∧
      ‖U.diagonalPart Z (U.offDiagonalPart Z x)‖ ^ 2 ≤
        q ^ 2 * (1 - q ^ 2) := by
  have hnormS : ‖U.offDiagonalPart Z x‖ ^ 2 = q ^ 2 :=
    norm_sq_offDiagonalPart_of_compressedDiagonal (U := U) hZsa hself
  have hCx := norm_sq_diagonalPart_apply (U := U) hZsa hZ2 x
  have hCSx := norm_sq_diagonalPart_apply (U := U) hZsa hZ2
    (U.offDiagonalPart Z x)
  have hbig : q ^ 2 * q ^ 2 ≤
      ‖U.offDiagonalPart Z (U.offDiagonalPart Z x)‖ ^ 2 := by
    have h1 : ‖((q ^ 2 : ℝ) : ℂ)‖ ≤
        ‖x‖ * ‖U.offDiagonalPart Z (U.offDiagonalPart Z x)‖ := by
      rw [← hself]
      exact norm_inner_le_norm _ _
    rw [hx1, one_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (sq_nonneg q)] at h1
    nlinarith [h1, sq_nonneg q,
      norm_nonneg (U.offDiagonalPart Z (U.offDiagonalPart Z x))]
  refine ⟨by rw [hCx, hx1, hnormS]; ring, ?_⟩
  rw [hCSx, hnormS]
  nlinarith [hbig]

/-- **The pole is excluded at a compressed double-angle eigenvector, for
free.**  `q < 1`, exactly as in the exact-eigenvector case: if `q` were `1`
then `‖C x‖² = 0` and `‖C S x‖² ≤ 0`, and equation (7.6) would force
`δ ≤ 0`. -/
theorem compressedDoubleAngleEigenvalue_lt_one
    (hred : TauCeti.LinearPMap.ReducesSubspace A U) (hB : TauCeti.IsOddFor U B)
    (hZsa : IsSelfAdjoint Z) (hZ2 : Z * Z = 1)
    (hZdom : TauCeti.LinearPMap.MapsDomainTo A A Z)
    (hZcomm : ∀ x : A.domain,
      A ⟨Z (x : H), hZdom x⟩ + B (Z (x : H)) = Z (A x) + Z (B (x : H)))
    (hUa : ∀ x : A.domain, (x : H) ∈ U →
      RCLike.re ⟪A x, (x : H)⟫_ℂ ≤ a * ‖(x : H)‖ ^ 2)
    (hUb : ∀ x : A.domain, (x : H) ∈ Uᗮ →
      b * ‖(x : H)‖ ^ 2 ≤ RCLike.re ⟪A x, (x : H)⟫_ℂ)
    (hab : a < b)
    {x : A.domain} (hxU : (x : H) ∈ U) (hx1 : ‖(x : H)‖ = 1) {q : ℝ}
    (hq : 0 < q)
    (hself : ⟪(x : H), U.offDiagonalPart Z
      (U.offDiagonalPart Z (x : H))⟫_ℂ = ((q ^ 2 : ℝ) : ℂ))
    (hres : RCLike.re ⟪A x, U.offDiagonalPart Z
        (U.offDiagonalPart Z (x : H)) - ((q ^ 2 : ℝ) : ℂ) • (x : H)⟫_ℂ ≤ 0) :
    q < 1 := by
  obtain ⟨hCx, hCSx⟩ := norm_sq_diagonalPart_of_compressedDiagonal
    (U := U) hZsa hZ2 hx1 hself
  by_contra hcon
  have hcon : 1 ≤ q := not_lt.mp hcon
  have hnn := sq_nonneg ‖U.diagonalPart Z (x : H)‖
  have hq1 : q ^ 2 = 1 := by nlinarith [hCx, hnn]
  have hCx0 : U.diagonalPart Z (x : H) = 0 := by
    refine norm_eq_zero.mp ?_
    nlinarith [norm_nonneg (U.diagonalPart Z (x : H)), hCx, hq1]
  have hCSx0 : U.diagonalPart Z (U.offDiagonalPart Z (x : H)) = 0 := by
    refine norm_eq_zero.mp ?_
    nlinarith [norm_nonneg (U.diagonalPart Z (U.offDiagonalPart Z (x : H))),
      hCSx, hq1]
  have hmain := gap_mul_sq_le_paired_of_compressedDoubleAngleEigenvector hred hB
    hZsa hZdom hZcomm hUa hUb hxU hx1 hself hres
  rw [hCx0, hCSx0] at hmain
  simp only [map_zero, inner_zero_right, inner_zero_left, sub_zero] at hmain
  nlinarith [hmain, hq1, hab]

/-- `conj z * z = ‖z‖²` in the `Complex.ofReal` spelling.  `RCLike.conj_mul`
states this with the `RCLike.ofReal` coercion and the square outside the cast;
bridging the two by `exact_mod_cast` inside a large context is expensive, so it
is done once here. -/
theorem conj_mul_eq_ofReal_norm_sq (z : ℂ) :
    (starRingEnd ℂ) z * z = ((‖z‖ ^ 2 : ℝ) : ℂ) := by
  exact_mod_cast RCLike.conj_mul z

/-- The Gram identities of the first two auxiliary systems at a *compressed*
eigenfamily.  These are still exact: `⟪S xᵢ, S xⱼ⟫` and `⟪C xᵢ, C xⱼ⟫` pair two
members of the trial space, so the leakage — which is orthogonal to it — never
appears.  Only the third system, handled separately, acquires a defect. -/
theorem inner_of_compressedDoubleAngleEigenfamily
    (hZsa : IsSelfAdjoint Z) (hZ2 : Z * Z = 1) {n : ℕ} (x : Fin n → H)
    (hx : Orthonormal ℂ x) {q : Fin n → ℝ}
    (hgram : ∀ i j, ⟪x j, U.offDiagonalPart Z
        (U.offDiagonalPart Z (x i))⟫_ℂ =
      (((q i) ^ 2 : ℝ) : ℂ) * (if j = i then (1 : ℂ) else 0))
    (i j : Fin n) :
    ⟪U.offDiagonalPart Z (x i), U.offDiagonalPart Z (x j)⟫_ℂ =
        (((q j) ^ 2 : ℝ) : ℂ) * (if i = j then (1 : ℂ) else 0) ∧
      ⟪U.diagonalPart Z (x i), U.diagonalPart Z (x j)⟫_ℂ =
        ((1 - (q j) ^ 2 : ℝ) : ℂ) * (if i = j then (1 : ℂ) else 0) := by
  classical
  have hSsym := TauCeti.inner_swap_of_isSelfAdjoint
    (TauCeti.isSelfAdjoint_offDiagonalPart (U := U) hZsa)
  have hCsym := TauCeti.inner_swap_of_isSelfAdjoint
    (TauCeti.isSelfAdjoint_diagonalPart (U := U) hZsa)
  have hite : ⟪x i, x j⟫_ℂ = if i = j then (1 : ℂ) else 0 :=
    (orthonormal_iff_ite.mp hx) i j
  have hpyth : ∀ v : H, U.diagonalPart Z (U.diagonalPart Z v) +
      U.offDiagonalPart Z (U.offDiagonalPart Z v) = v := by
    intro v
    have h := TauCeti.diagonalPart_sq_add_offDiagonalPart_sq (U := U) hZ2
    have h2 := congrArg (fun T : H →L[ℂ] H => T v) h
    simpa using h2
  have hSS : ⟪U.offDiagonalPart Z (x i), U.offDiagonalPart Z (x j)⟫_ℂ =
      (((q j) ^ 2 : ℝ) : ℂ) * (if i = j then (1 : ℂ) else 0) := by
    rw [hSsym (x i) (U.offDiagonalPart Z (x j))]
    exact hgram j i
  refine ⟨hSS, ?_⟩
  have hCC : ⟪U.diagonalPart Z (x i), U.diagonalPart Z (x j)⟫_ℂ =
      ⟪x i, U.diagonalPart Z (U.diagonalPart Z (x j))⟫_ℂ :=
    hCsym (x i) (U.diagonalPart Z (x j))
  have hsplit : U.diagonalPart Z (U.diagonalPart Z (x j)) =
      x j - U.offDiagonalPart Z (U.offDiagonalPart Z (x j)) := by
    have h := hpyth (x j)
    linear_combination (norm := module) h
  rw [hCC, hsplit, inner_sub_right, hite, hgram j i]
  push_cast
  ring

/-- **The fourth auxiliary system is a contraction system, with constant `1`.**

For a compressed eigenfamily the normalised vectors `C S xᵢ / (qᵢ cᵢ)` are no
longer orthonormal: their Gram operator is `1 - D⁻¹ R⋆ R D⁻¹`, where `R` collects
the leakage vectors `rᵢ = S² xᵢ - qᵢ² xᵢ`.  That defect is *negative
semidefinite*, so every linear combination is still bounded by the Euclidean
norm of its coefficients — which is exactly the hypothesis of
`sum_le_kyFanApproximationGauge_of_contraction` with constant `1`.

The proof needs no Gram matrix.  Writing `g = ∑ᵢ βᵢ xᵢ` for the corresponding
element of the trial space, the combination is `C S g`, and

* `‖C S g‖² = ‖S g‖² - ‖S² g‖²` is the double-angle Pythagoras identity;
* `‖S g‖² = ∑ᵢ |βᵢ|² qᵢ²` is exact, by the first Gram identity;
* `‖S² g‖² ≥ ∑ᵢ |βᵢ|² qᵢ⁴`, because `∑ᵢ βᵢ qᵢ² xᵢ` is the trial-space part of
  `S² g`, and dropping the leakage only decreases the norm.

Subtracting gives `∑ᵢ |βᵢ|² qᵢ² (1 - qᵢ²) = ∑ᵢ |αᵢ|²`. -/
theorem sq_norm_sum_smul_diagonalPart_offDiagonalPart_le_of_compressed
    (hZsa : IsSelfAdjoint Z) (hZ2 : Z * Z = 1) {n : ℕ} (x : Fin n → H)
    (hx : Orthonormal ℂ x) {q : Fin n → ℝ} (hq : ∀ i, 0 < q i)
    (hq1 : ∀ i, q i < 1)
    (hgram : ∀ i j, ⟪x j, U.offDiagonalPart Z
        (U.offDiagonalPart Z (x i))⟫_ℂ =
      (((q i) ^ 2 : ℝ) : ℂ) * (if j = i then (1 : ℂ) else 0))
    (α : Fin n → ℂ) :
    ‖∑ i, α i • ((((q i * √(1 - (q i) ^ 2)) : ℝ) : ℂ)⁻¹ •
        U.diagonalPart Z (U.offDiagonalPart Z (x i)))‖ ^ 2 ≤
      (1 : ℝ) ^ 2 * ∑ i, ‖α i‖ ^ 2 := by
  classical
  have hc0 : ∀ i, 0 < 1 - (q i) ^ 2 := fun i => by nlinarith [hq i, hq1 i]
  have hcpos : ∀ i, 0 < √(1 - (q i) ^ 2) := fun i => Real.sqrt_pos.mpr (hc0 i)
  have hcsq : ∀ i, √(1 - (q i) ^ 2) ^ 2 = 1 - (q i) ^ 2 :=
    fun i => Real.sq_sqrt (hc0 i).le
  have hqcpos : ∀ i, 0 < q i * √(1 - (q i) ^ 2) :=
    fun i => mul_pos (hq i) (hcpos i)
  have hqne : ∀ i, (((q i : ℝ) : ℂ)) ≠ 0 := by
    intro i
    simpa using (hq i).ne'
  have hqcne : ∀ i, ((((q i * √(1 - (q i) ^ 2)) : ℝ) : ℂ)) ≠ 0 := by
    intro i
    simpa using (hqcpos i).ne'
  obtain ⟨β, hβdef⟩ : ∃ β : Fin n → ℂ,
      β = fun i => α i * ((((q i * √(1 - (q i) ^ 2)) : ℝ) : ℂ))⁻¹ := ⟨_, rfl⟩
  obtain ⟨g, hgdef⟩ : ∃ g : H, g = ∑ i, β i • x i := ⟨_, rfl⟩
  -- the combination is `C S g`
  have hcomb : ∑ i, α i • ((((q i * √(1 - (q i) ^ 2)) : ℝ) : ℂ)⁻¹ •
      U.diagonalPart Z (U.offDiagonalPart Z (x i))) =
      U.diagonalPart Z (U.offDiagonalPart Z g) := by
    rw [hgdef, map_sum, map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_smul, map_smul, smul_smul]
    simp only [hβdef]
  -- the first auxiliary system is orthonormal
  have hyon : Orthonormal ℂ fun i =>
      (((q i : ℝ) : ℂ)⁻¹ • U.offDiagonalPart Z (x i)) :=
    orthonormal_scaled_of_inner_eq hq fun i j =>
      (inner_of_compressedDoubleAngleEigenfamily (U := U) hZsa hZ2 x hx
        hgram i j).1
  -- `‖S g‖² = ∑ |βᵢ|² qᵢ²`
  have hSg : U.offDiagonalPart Z g = ∑ i, (β i * ((q i : ℝ) : ℂ)) •
      (((q i : ℝ) : ℂ)⁻¹ • U.offDiagonalPart Z (x i)) := by
    rw [hgdef, map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_smul, smul_smul, mul_assoc, mul_inv_cancel₀ (hqne i), mul_one]
  have hnormSg : ‖U.offDiagonalPart Z g‖ ^ 2 = ∑ i, ‖β i‖ ^ 2 * q i ^ 2 := by
    rw [hSg, norm_sq_sum_smul_of_orthonormal hyon]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (hq i)]
    ring
  -- `‖S² g‖² ≥ ∑ |βᵢ|² qᵢ⁴`
  obtain ⟨p, hpdef⟩ : ∃ p : H, p = ∑ i, (β i * (((q i) ^ 2 : ℝ) : ℂ)) • x i :=
    ⟨_, rfl⟩
  have hpnorm : ‖p‖ ^ 2 = ∑ i, ‖β i‖ ^ 2 * q i ^ 4 := by
    rw [hpdef, norm_sq_sum_smul_of_orthonormal hx]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (sq_nonneg (q i))]
    ring
  have hSSg : U.offDiagonalPart Z (U.offDiagonalPart Z g) =
      ∑ j, β j • U.offDiagonalPart Z (U.offDiagonalPart Z (x j)) := by
    rw [hgdef, map_sum, map_sum]
    exact Finset.sum_congr rfl fun j _ => by rw [map_smul, map_smul]
  have hxi : ∀ i, ⟪x i, U.offDiagonalPart Z (U.offDiagonalPart Z g)⟫_ℂ =
      β i * (((q i) ^ 2 : ℝ) : ℂ) := by
    intro i
    rw [hSSg, inner_sum, Finset.sum_eq_single i]
    · rw [inner_smul_right, hgram i i, ite_eq_left rfl, mul_one]
    · intro j _ hj
      rw [inner_smul_right, hgram j i, ite_eq_right (Ne.symm hj), mul_zero, mul_zero]
    · intro hi
      exact absurd (Finset.mem_univ i) hi
  have hterm : ∀ i : Fin n, ⟪(β i * (((q i) ^ 2 : ℝ) : ℂ)) • x i,
      U.offDiagonalPart Z (U.offDiagonalPart Z g)⟫_ℂ =
      ((‖β i‖ ^ 2 * q i ^ 4 : ℝ) : ℂ) := by
    intro i
    have hnz : ‖β i * (((q i) ^ 2 : ℝ) : ℂ)‖ ^ 2 = ‖β i‖ ^ 2 * q i ^ 4 := by
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (sq_nonneg (q i))]
      ring
    rw [inner_smul_left, hxi i, conj_mul_eq_ofReal_norm_sq, hnz]
  have hinner : ⟪p, U.offDiagonalPart Z (U.offDiagonalPart Z g)⟫_ℂ =
      ((‖p‖ ^ 2 : ℝ) : ℂ) := by
    rw [hpnorm, hpdef, sum_inner, Finset.sum_congr rfl fun i _ => hterm i]
    push_cast
    ring
  have hple : ‖p‖ ≤ ‖U.offDiagonalPart Z (U.offDiagonalPart Z g)‖ := by
    have hre : ‖p‖ ^ 2 ≤
        ‖p‖ * ‖U.offDiagonalPart Z (U.offDiagonalPart Z g)‖ := by
      have h1 : ((‖p‖ ^ 2 : ℝ) : ℂ) =
          ⟪p, U.offDiagonalPart Z (U.offDiagonalPart Z g)⟫_ℂ := hinner.symm
      have h2 : ‖((‖p‖ ^ 2 : ℝ) : ℂ)‖ ≤
          ‖p‖ * ‖U.offDiagonalPart Z (U.offDiagonalPart Z g)‖ := by
        rw [h1]
        exact norm_inner_le_norm _ _
      rwa [Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (sq_nonneg _)] at h2
    rcases (norm_nonneg p).lt_or_eq with h | h
    · exact le_of_mul_le_mul_left (by linarith [hre]) h
    · rw [← h]
      exact norm_nonneg _
  have hSSglow : ∑ i, ‖β i‖ ^ 2 * q i ^ 4 ≤
      ‖U.offDiagonalPart Z (U.offDiagonalPart Z g)‖ ^ 2 := by
    rw [← hpnorm]
    have := mul_self_le_mul_self (norm_nonneg p) hple
    nlinarith [this]
  -- assemble
  have hpythg := norm_sq_diagonalPart_apply (U := U) hZsa hZ2
    (U.offDiagonalPart Z g)
  have hfinal : ∑ i, ‖β i‖ ^ 2 * q i ^ 2 - ∑ i, ‖β i‖ ^ 2 * q i ^ 4 =
      ∑ i, ‖α i‖ ^ 2 := by
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    have hinvnorm : ‖((((q i * √(1 - (q i) ^ 2)) : ℝ) : ℂ))⁻¹‖ =
        (q i * √(1 - (q i) ^ 2))⁻¹ := by
      rw [norm_inv, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos (hqcpos i)]
    have hnβ : ‖β i‖ = ‖α i‖ * (q i * √(1 - (q i) ^ 2))⁻¹ := by
      simp only [hβdef, norm_mul, hinvnorm]
    have hqc2 : (q i * √(1 - (q i) ^ 2)) ^ 2 = q i ^ 2 * (1 - (q i) ^ 2) := by
      rw [mul_pow, hcsq i]
    have hd : q i ^ 2 * (1 - (q i) ^ 2) ≠ 0 :=
      ne_of_gt (mul_pos (pow_pos (hq i) 2) (hc0 i))
    have hkey : ‖β i‖ ^ 2 * (q i ^ 2 * (1 - (q i) ^ 2)) = ‖α i‖ ^ 2 := by
      rw [hnβ, mul_pow, inv_pow, hqc2, mul_assoc, inv_mul_cancel₀ hd, mul_one]
    linear_combination hkey
  rw [hcomb, hpythg, hnormSg, one_pow, one_mul]
  linarith [hSSglow, hfinal]

omit [CompleteSpace H] in
/-- **The leakage condition is automatic on an `A`-invariant trial space.**

If `A xᵢ` lies in the span of the family — which is what it means for the trial
space to be `A`-invariant — then the leakage pairs with it to *exactly* zero,
because the leakage is orthogonal to every member of the family.  No norm of `A`
and no cutoff level enter.

This is the reason the compressed hypothesis is reachable: on a
finite-dimensional `A`-invariant subspace `W ⊆ 𝔛₀ ∩ D(A)`, the compression
`P_W S² P_W` is a self-adjoint operator on a finite-dimensional space, so it
*always* has an orthonormal eigenbasis, and this lemma supplies the second
condition for free.  Nothing about the point spectrum of `S²` is needed. -/
theorem re_inner_compressedResidual_eq_zero_of_apply_eq_sum
    {n : ℕ} (x : Fin n → A.domain)
    (hxon : Orthonormal ℂ fun i => ((x i : A.domain) : H))
    {q : Fin n → ℝ}
    (hgram : ∀ i j, ⟪((x j : A.domain) : H), U.offDiagonalPart Z
        (U.offDiagonalPart Z ((x i : A.domain) : H))⟫_ℂ =
      (((q i) ^ 2 : ℝ) : ℂ) * (if j = i then (1 : ℂ) else 0))
    {i : Fin n} {γ : Fin n → ℂ}
    (hA : A (x i) = ∑ j, γ j • ((x j : A.domain) : H)) :
    RCLike.re ⟪A (x i), U.offDiagonalPart Z
        (U.offDiagonalPart Z ((x i : A.domain) : H)) -
          (((q i) ^ 2 : ℝ) : ℂ) • ((x i : A.domain) : H)⟫_ℂ = 0 := by
  classical
  have hz : ⟪A (x i), U.offDiagonalPart Z
      (U.offDiagonalPart Z ((x i : A.domain) : H)) -
        (((q i) ^ 2 : ℝ) : ℂ) • ((x i : A.domain) : H)⟫_ℂ = 0 := by
    rw [hA, sum_inner]
    refine Finset.sum_eq_zero fun j _ => ?_
    rw [inner_smul_left, inner_sub_right, inner_smul_right, hgram i j,
      (orthonormal_iff_ite.mp hxon) j i]
    ring
  rw [hz, map_zero]

/-- **The unbounded, residual-form `tan 2Θ` theorem at every Ky Fan prefix, on a
compressed double-angle eigenfamily.**

Identical in hypotheses and conclusion to
`gap_mul_sum_tangent_le_kyFan_of_doubleAngleEigenfamily` except that the exact
eigenvector relation `S² xᵢ = qᵢ² xᵢ` is weakened to the two compression
conditions `hgram` and `hres`.  The conclusion, **including the sharp constant
`2`**, is unchanged.

The constant survives because the defect is one-sided.  Three of the four
auxiliary systems are still exactly orthonormal and contribute
`kyFanApproximationGauge n B` each, exactly as before; the fourth is a
contraction system with constant `1`, and
`sum_le_kyFanApproximationGauge_of_contraction` charges `1 * 1` for it.  Nothing
anywhere is multiplied by `1 + ε`. -/
theorem gap_mul_sum_tangent_le_kyFan_of_compressedDoubleAngleEigenfamily
    (hred : TauCeti.LinearPMap.ReducesSubspace A U) (hB : TauCeti.IsOddFor U B)
    (hZsa : IsSelfAdjoint Z) (hZ2 : Z * Z = 1)
    (hZdom : TauCeti.LinearPMap.MapsDomainTo A A Z)
    (hZcomm : ∀ x : A.domain,
      A ⟨Z (x : H), hZdom x⟩ + B (Z (x : H)) = Z (A x) + Z (B (x : H)))
    (hUa : ∀ x : A.domain, (x : H) ∈ U →
      RCLike.re ⟪A x, (x : H)⟫_ℂ ≤ a * ‖(x : H)‖ ^ 2)
    (hUb : ∀ x : A.domain, (x : H) ∈ Uᗮ →
      b * ‖(x : H)‖ ^ 2 ≤ RCLike.re ⟪A x, (x : H)⟫_ℂ)
    (hab : a < b)
    {n : ℕ} (x : Fin n → A.domain)
    (hxU : ∀ i, ((x i : A.domain) : H) ∈ U)
    (hxon : Orthonormal ℂ fun i => ((x i : A.domain) : H))
    {q : Fin n → ℝ} (hq : ∀ i, 0 < q i)
    (hgram : ∀ i j, ⟪((x j : A.domain) : H), U.offDiagonalPart Z
        (U.offDiagonalPart Z ((x i : A.domain) : H))⟫_ℂ =
      (((q i) ^ 2 : ℝ) : ℂ) * (if j = i then (1 : ℂ) else 0))
    (hres : ∀ i, RCLike.re ⟪A (x i), U.offDiagonalPart Z
        (U.offDiagonalPart Z ((x i : A.domain) : H)) -
          (((q i) ^ 2 : ℝ) : ℂ) • ((x i : A.domain) : H)⟫_ℂ ≤ 0) :
    (b - a) * ∑ i, q i / √(1 - (q i) ^ 2) ≤
      2 * kyFanApproximationGauge n B := by
  classical
  have hx1 : ∀ i, ‖((x i : A.domain) : H)‖ = 1 := fun i => hxon.norm_eq_one i
  have hself : ∀ i, ⟪((x i : A.domain) : H), U.offDiagonalPart Z
      (U.offDiagonalPart Z ((x i : A.domain) : H))⟫_ℂ =
      (((q i) ^ 2 : ℝ) : ℂ) := fun i => by
    rw [hgram i i, ite_eq_left rfl, mul_one]
  have hq1 : ∀ i, q i < 1 := fun i =>
    compressedDoubleAngleEigenvalue_lt_one hred hB hZsa hZ2 hZdom hZcomm hUa hUb
      hab (hxU i) (hx1 i) (hq i) (hself i) (hres i)
  have hc0 : ∀ i, 0 < 1 - (q i) ^ 2 := by
    intro i
    nlinarith [hq i, hq1 i]
  have hcpos : ∀ i, 0 < √(1 - (q i) ^ 2) := fun i => Real.sqrt_pos.mpr (hc0 i)
  have hgram2 := fun i j => inner_of_compressedDoubleAngleEigenfamily (U := U)
    hZsa hZ2 (fun i => ((x i : A.domain) : H)) hxon hgram i j
  -- the two exactly orthonormal auxiliary systems
  have hyon : Orthonormal ℂ fun i =>
      (((q i : ℝ) : ℂ)⁻¹ • U.offDiagonalPart Z ((x i : A.domain) : H)) :=
    orthonormal_scaled_of_inner_eq hq fun i j => (hgram2 i j).1
  have huon : Orthonormal ℂ fun i =>
      (((√(1 - (q i) ^ 2) : ℝ) : ℂ)⁻¹ •
        U.diagonalPart Z ((x i : A.domain) : H)) :=
    orthonormal_scaled_of_inner_eq hcpos fun i j => by
      rw [Real.sq_sqrt (hc0 j).le]
      exact (hgram2 i j).2
  have hnegon : Orthonormal ℂ fun i =>
      -(((q i : ℝ) : ℂ)⁻¹ • U.offDiagonalPart Z ((x i : A.domain) : H)) := by
    have h := orthonormal_signFlip hyon (fun _ => false)
    simpa using h
  -- the one contraction system
  have hcontr := sq_norm_sum_smul_diagonalPart_offDiagonalPart_le_of_compressed
    (U := U) hZsa hZ2 (fun i => ((x i : A.domain) : H)) hxon hq hq1 hgram
  -- the per-index estimate, divided by `qᵢ cᵢ`
  have hstep : ∀ i, (b - a) * (q i / √(1 - (q i) ^ 2)) ≤
      RCLike.re ⟪(((q i * √(1 - (q i) ^ 2)) : ℝ) : ℂ)⁻¹ •
          U.diagonalPart Z (U.offDiagonalPart Z ((x i : A.domain) : H)),
        B ((x i : A.domain) : H)⟫_ℂ +
      RCLike.re ⟪-(((q i : ℝ) : ℂ)⁻¹ •
          U.offDiagonalPart Z ((x i : A.domain) : H)),
        B ((((√(1 - (q i) ^ 2) : ℝ) : ℂ)⁻¹ •
          U.diagonalPart Z ((x i : A.domain) : H)))⟫_ℂ := by
    intro i
    have hqc : 0 < q i * √(1 - (q i) ^ 2) := mul_pos (hq i) (hcpos i)
    have hmain := gap_mul_sq_le_paired_of_compressedDoubleAngleEigenvector hred
      hB hZsa hZdom hZcomm hUa hUb (hxU i) (hx1 i) (hself i) (hres i)
    have hterm1 : RCLike.re ⟪(((q i * √(1 - (q i) ^ 2)) : ℝ) : ℂ)⁻¹ •
        U.diagonalPart Z (U.offDiagonalPart Z ((x i : A.domain) : H)),
        B ((x i : A.domain) : H)⟫_ℂ =
        (q i * √(1 - (q i) ^ 2))⁻¹ *
          RCLike.re ⟪B ((x i : A.domain) : H),
            U.diagonalPart Z (U.offDiagonalPart Z
              ((x i : A.domain) : H))⟫_ℂ := by
      rw [inner_smul_left, ← Complex.ofReal_inv, Complex.conj_ofReal,
        ← Complex.real_smul, RCLike.smul_re, inner_re_symm]
    have hterm2 : RCLike.re ⟪-(((q i : ℝ) : ℂ)⁻¹ •
        U.offDiagonalPart Z ((x i : A.domain) : H)),
        B ((((√(1 - (q i) ^ 2) : ℝ) : ℂ)⁻¹ •
          U.diagonalPart Z ((x i : A.domain) : H)))⟫_ℂ =
        -((q i * √(1 - (q i) ^ 2))⁻¹ *
          RCLike.re ⟪B (U.diagonalPart Z ((x i : A.domain) : H)),
            U.offDiagonalPart Z ((x i : A.domain) : H)⟫_ℂ) := by
      rw [mul_inv]
      simp only [map_smul, inner_neg_left, inner_smul_left, inner_smul_right,
        ← Complex.ofReal_inv, Complex.conj_ofReal]
      rw [mul_neg, ← mul_assoc, ← Complex.ofReal_mul, ← Complex.real_smul,
        map_neg, RCLike.smul_re, inner_re_symm]
      ring
    rw [hterm1, hterm2]
    have hdiv : (b - a) * (q i / √(1 - (q i) ^ 2)) =
        (q i * √(1 - (q i) ^ 2))⁻¹ * ((b - a) * (q i) ^ 2) := by
      field_simp
    rw [hdiv]
    have hpos : (0 : ℝ) ≤ (q i * √(1 - (q i) ^ 2))⁻¹ := by positivity
    nlinarith [mul_le_mul_of_nonneg_left hmain hpos]
  have hsum1 : ∑ i, RCLike.re ⟪(((q i * √(1 - (q i) ^ 2)) : ℝ) : ℂ)⁻¹ •
      U.diagonalPart Z (U.offDiagonalPart Z ((x i : A.domain) : H)),
      B ((x i : A.domain) : H)⟫_ℂ ≤ kyFanApproximationGauge n B := by
    have h := sum_le_kyFanApproximationGauge_of_contraction B zero_le_one
      zero_le_one hcontr
      (fun α => sq_norm_sum_smul_le_of_orthonormal hxon (le_refl (1 : ℝ)) α)
      (fun _ => le_rfl)
    simpa using h
  have hsum2 : ∑ i, RCLike.re ⟪-(((q i : ℝ) : ℂ)⁻¹ •
      U.offDiagonalPart Z ((x i : A.domain) : H)),
      B ((((√(1 - (q i) ^ 2) : ℝ) : ℂ)⁻¹ •
        U.diagonalPart Z ((x i : A.domain) : H)))⟫_ℂ ≤
      kyFanApproximationGauge n B :=
    sum_le_kyFanApproximationGauge_of_orthonormal B hnegon huon (fun _ => le_rfl)
  calc (b - a) * ∑ i, q i / √(1 - (q i) ^ 2)
      = ∑ i, (b - a) * (q i / √(1 - (q i) ^ 2)) := by rw [Finset.mul_sum]
    _ ≤ ∑ i, (RCLike.re ⟪(((q i * √(1 - (q i) ^ 2)) : ℝ) : ℂ)⁻¹ •
          U.diagonalPart Z (U.offDiagonalPart Z ((x i : A.domain) : H)),
          B ((x i : A.domain) : H)⟫_ℂ +
          RCLike.re ⟪-(((q i : ℝ) : ℂ)⁻¹ •
            U.offDiagonalPart Z ((x i : A.domain) : H)),
            B ((((√(1 - (q i) ^ 2) : ℝ) : ℂ)⁻¹ •
              U.diagonalPart Z ((x i : A.domain) : H)))⟫_ℂ) :=
        Finset.sum_le_sum fun i _ => hstep i
    _ = (∑ i, RCLike.re ⟪(((q i * √(1 - (q i) ^ 2)) : ℝ) : ℂ)⁻¹ •
          U.diagonalPart Z (U.offDiagonalPart Z ((x i : A.domain) : H)),
          B ((x i : A.domain) : H)⟫_ℂ) +
        ∑ i, RCLike.re ⟪-(((q i : ℝ) : ℂ)⁻¹ •
          U.offDiagonalPart Z ((x i : A.domain) : H)),
          B ((((√(1 - (q i) ^ 2) : ℝ) : ℂ)⁻¹ •
            U.diagonalPart Z ((x i : A.domain) : H)))⟫_ℂ :=
        Finset.sum_add_distrib
    _ ≤ 2 * kyFanApproximationGauge n B := by linarith [hsum1, hsum2]

/-- A trial-subspace *compressed* eigenbasis for `sin² 2Θ` realising the Ky Fan
prefixes of a candidate tangent operator.

Exactly `IsDoubleAngleEigenbasis` with the global eigenvector relation replaced
by the two compression conditions: the leakage
`rᵢ = S² yᵢ - qᵢ² yᵢ` is orthogonal to the family, and pairs non-positively with
`A yᵢ`.  Both hold whenever `rᵢ = 0`, and both hold whenever the span of the
family is `A`-invariant and `qᵢ²` are the eigenvalues of the compression of `S²`
to it — which a finite-dimensional space always supplies. -/
def IsCompressedDoubleAngleEigenbasis (A : H →ₗ.[ℂ] H) (U : Submodule ℂ H)
    [U.HasOrthogonalProjection] (Z T : H →L[ℂ] H) : Prop :=
  ∀ k : ℕ, ∃ (y : Fin k → A.domain) (q : Fin k → ℝ),
    (∀ i, ((y i : A.domain) : H) ∈ U) ∧
      (Orthonormal ℂ fun i => ((y i : A.domain) : H)) ∧
      (∀ i, 0 < q i) ∧
      (∀ i j, ⟪((y j : A.domain) : H), U.offDiagonalPart Z
          (U.offDiagonalPart Z ((y i : A.domain) : H))⟫_ℂ =
        (((q i) ^ 2 : ℝ) : ℂ) * (if j = i then (1 : ℂ) else 0)) ∧
      (∀ i, RCLike.re ⟪A (y i), U.offDiagonalPart Z
          (U.offDiagonalPart Z ((y i : A.domain) : H)) -
            (((q i) ^ 2 : ℝ) : ℂ) • ((y i : A.domain) : H)⟫_ℂ ≤ 0) ∧
      kyFanApproximationGauge k T ≤ ∑ i, q i / √(1 - (q i) ^ 2)

omit [CompleteSpace H] in
/-- **An exact eigenbasis is a compressed one.**  The leakage vanishes
identically, so both compression conditions are trivial.  This is what makes
every compressed endpoint below at least as strong as its exact counterpart. -/
theorem isCompressedDoubleAngleEigenbasis_of_isDoubleAngleEigenbasis
    {T : H →L[ℂ] H} (hT : IsDoubleAngleEigenbasis A U Z T) :
    IsCompressedDoubleAngleEigenbasis A U Z T := by
  classical
  intro k
  obtain ⟨y, q, hyU, hyon, hqpos, hyeig, hle⟩ := hT k
  refine ⟨y, q, hyU, hyon, hqpos, ?_, ?_, hle⟩
  · intro i j
    rw [hyeig i, inner_smul_right]
    congr 1
    exact (orthonormal_iff_ite.mp hyon) j i
  · intro i
    rw [hyeig i, sub_self, inner_zero_right]
    simp

/-- **The unbounded residual `tan 2Θ` theorem at every Ky Fan gauge, on a
compressed eigenbasis.**  `δ · kyFanApproximationGauge k T ≤
2 · kyFanApproximationGauge k B` for every prefix length `k`. -/
theorem gap_mul_kyFan_le_two_mul_kyFan_of_compressedDoubleAngleEigenbasis
    (hred : TauCeti.LinearPMap.ReducesSubspace A U) (hB : TauCeti.IsOddFor U B)
    (hZsa : IsSelfAdjoint Z) (hZ2 : Z * Z = 1)
    (hZdom : TauCeti.LinearPMap.MapsDomainTo A A Z)
    (hZcomm : ∀ x : A.domain,
      A ⟨Z (x : H), hZdom x⟩ + B (Z (x : H)) = Z (A x) + Z (B (x : H)))
    (hUa : ∀ x : A.domain, (x : H) ∈ U →
      RCLike.re ⟪A x, (x : H)⟫_ℂ ≤ a * ‖(x : H)‖ ^ 2)
    (hUb : ∀ x : A.domain, (x : H) ∈ Uᗮ →
      b * ‖(x : H)‖ ^ 2 ≤ RCLike.re ⟪A x, (x : H)⟫_ℂ)
    (hab : a < b) {T : H →L[ℂ] H}
    (hT : IsCompressedDoubleAngleEigenbasis A U Z T) (k : ℕ) :
    (b - a) * kyFanApproximationGauge k T ≤
      2 * kyFanApproximationGauge k B := by
  obtain ⟨y, q, hyU, hyon, hqpos, hygram, hyres, hle⟩ := hT k
  have hmain := gap_mul_sum_tangent_le_kyFan_of_compressedDoubleAngleEigenfamily
    hred hB hZsa hZ2 hZdom hZcomm hUa hUb hab y hyU hyon hqpos hygram hyres
  have hδ : (0 : ℝ) ≤ b - a := by linarith
  nlinarith [mul_le_mul_of_nonneg_left hle hδ, hmain]

/-- **The exact-eigenbasis Ky Fan endpoint, re-derived from the compressed
one.**

The statement is *verbatim* that of
`gap_mul_kyFan_le_two_mul_kyFan_of_doubleAngleEigenbasis` — same hypotheses,
same conclusion, same constant `2` — and the proof uses nothing but the
compressed endpoint.  This is the machine-checked demonstration that removing
the exact eigenvector relation lost no strength. -/
theorem gap_mul_kyFan_le_two_mul_kyFan_of_doubleAngleEigenbasis_via_compressed
    (hred : TauCeti.LinearPMap.ReducesSubspace A U) (hB : TauCeti.IsOddFor U B)
    (hZsa : IsSelfAdjoint Z) (hZ2 : Z * Z = 1)
    (hZdom : TauCeti.LinearPMap.MapsDomainTo A A Z)
    (hZcomm : ∀ x : A.domain,
      A ⟨Z (x : H), hZdom x⟩ + B (Z (x : H)) = Z (A x) + Z (B (x : H)))
    (hUa : ∀ x : A.domain, (x : H) ∈ U →
      RCLike.re ⟪A x, (x : H)⟫_ℂ ≤ a * ‖(x : H)‖ ^ 2)
    (hUb : ∀ x : A.domain, (x : H) ∈ Uᗮ →
      b * ‖(x : H)‖ ^ 2 ≤ RCLike.re ⟪A x, (x : H)⟫_ℂ)
    (hab : a < b) {T : H →L[ℂ] H}
    (hT : IsDoubleAngleEigenbasis A U Z T) (k : ℕ) :
    (b - a) * kyFanApproximationGauge k T ≤
      2 * kyFanApproximationGauge k B :=
  gap_mul_kyFan_le_two_mul_kyFan_of_compressedDoubleAngleEigenbasis hred hB hZsa
    hZ2 hZdom hZcomm hUa hUb hab
    (isCompressedDoubleAngleEigenbasis_of_isDoubleAngleEigenbasis hT) k

/-- **The unbounded, residual-form `tan 2Θ` theorem at every Fan-dominant
unitarily invariant ideal gauge, on a compressed eigenbasis.**

`δ N(tan 2Θ₀) ≤ 2 N(R)` in the repository's scaled form.  Ideal membership of
the scaled tangent is concluded, not assumed. -/
theorem mem_and_gauge_le_of_compressedDoubleAngleEigenbasis
    (N : KyFanDominantIdealFamily (𝕜 := ℂ))
    (hred : TauCeti.LinearPMap.ReducesSubspace A U) (hB : TauCeti.IsOddFor U B)
    (hZsa : IsSelfAdjoint Z) (hZ2 : Z * Z = 1)
    (hZdom : TauCeti.LinearPMap.MapsDomainTo A A Z)
    (hZcomm : ∀ x : A.domain,
      A ⟨Z (x : H), hZdom x⟩ + B (Z (x : H)) = Z (A x) + Z (B (x : H)))
    (hUa : ∀ x : A.domain, (x : H) ∈ U →
      RCLike.re ⟪A x, (x : H)⟫_ℂ ≤ a * ‖(x : H)‖ ^ 2)
    (hUb : ∀ x : A.domain, (x : H) ∈ Uᗮ →
      b * ‖(x : H)‖ ^ 2 ≤ RCLike.re ⟪A x, (x : H)⟫_ℂ)
    (hab : a < b) {T : H →L[ℂ] H}
    (hT : IsCompressedDoubleAngleEigenbasis A U Z T) (hBmem : N.Mem B) :
    N.Mem ((((b - a) / 2 : ℝ) : ℂ) • T) ∧
      N.gauge ((((b - a) / 2 : ℝ) : ℂ) • T) ≤ N.gauge B := by
  refine mem_and_gauge_le_of_all_kyFanApproximationGauge_le
    N.toFanDominantIdealFamily hBmem fun k => ?_
  rw [kyFanApproximationGauge_smul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (by linarith : (0 : ℝ) ≤ (b - a) / 2)]
  have h := gap_mul_kyFan_le_two_mul_kyFan_of_compressedDoubleAngleEigenbasis
    hred hB hZsa hZ2 hZdom hZcomm hUa hUb hab hT k
  linarith

/-!
## Discharging the compressed hypothesis on an `A`-invariant trial space

Everything above is conditional on a family with two compression properties.
This section removes the *spectral* content of that hypothesis entirely.

The observation is that both compression conditions are properties of the
**compression** `P_W S² P_W` of `S² = sin² 2Θ` to a finite-dimensional subspace
`W ⊆ 𝔛₀ ∩ D(A)`, not of `S²` itself.  That compression is a self-adjoint
operator on a finite-dimensional space, so it *always* has an orthonormal
eigenbasis — Mathlib's `LinearMap.IsSymmetric.eigenvectorBasis` — and its
eigenvalues are automatically nonnegative, being `‖S yᵢ‖²`.  The Gram condition
is then the eigen-relation of that compression, and the leakage condition is
supplied for free by `re_inner_compressedResidual_eq_zero_of_apply_eq_sum` as
soon as `W` is `A`-invariant.

**Nothing about the point spectrum of `S²` is used, and no cutoff, limit or
error term appears.**  The hypothesis has moved off the unknown rotation `Θ` and
onto the given operator `A`: what must be supplied is a finite-dimensional
`A`-invariant subspace of `𝔛₀ ∩ D(A)`, and that is a statement about `A` alone.

Two honest limits of the passage, both visible in the statements below.

* A zero eigenvalue of the compression is *not* excluded, and the family
  endpoint requires `qᵢ > 0`.  It costs nothing: the vanishing eigenvalues
  contribute `0` to `∑ qᵢ / √(1 - qᵢ²)`, so the sum is unchanged by dropping
  them, and the Ky Fan gauge of the residual only grows with the prefix length.
  `gap_mul_sum_tangent_le_kyFan_of_invariantSubspace` therefore carries **no**
  positivity hypothesis at all.
* The last clause of `IsCompressedDoubleAngleEigenbasis` — that the prefix
  `kyFanApproximationGauge k T` is realised from below by the tangent sum — is
  the *only* place the candidate tangent `T` is linked to the geometry, and it
  is not produced by any subspace construction: `T` is an arbitrary operator in
  these statements.  It survives as `HasInvariantDoubleAngleFiltration`, whose
  every other clause is about `A`, `W` and `Z` only.
-/

/-- The compression of `S² = sin² 2Θ` to a subspace `W`, as a linear map of `W`:
`w ↦ P_W (S (S w))` for the odd block `S = U.offDiagonalPart Z`. -/
def offDiagonalSqCompression (U : Submodule ℂ H) [U.HasOrthogonalProjection]
    (Z : H →L[ℂ] H) (W : Submodule ℂ H) [W.HasOrthogonalProjection] :
    W →ₗ[ℂ] W :=
  (W.orthogonalProjectionOnto.comp
    ((U.offDiagonalPart Z).comp
      ((U.offDiagonalPart Z).comp W.subtypeL))).toLinearMap

omit [CompleteSpace H] in
/-- Pointwise form of the compression. -/
theorem offDiagonalSqCompression_apply (W : Submodule ℂ H)
    [W.HasOrthogonalProjection] (w : W) :
    offDiagonalSqCompression U Z W w =
      W.orthogonalProjectionOnto
        (U.offDiagonalPart Z (U.offDiagonalPart Z (w : H))) := rfl

/-- **The compression of `S²` is symmetric.**  `S` is self-adjoint because `Z`
is, and an orthogonal projection is self-adjoint, so the compression of a
self-adjoint operator to any subspace is self-adjoint on that subspace.  This is
the whole reason the finite-dimensional spectral theorem applies. -/
theorem isSymmetric_offDiagonalSqCompression (hZsa : IsSelfAdjoint Z)
    (W : Submodule ℂ H) [W.HasOrthogonalProjection] :
    (offDiagonalSqCompression U Z W).IsSymmetric := by
  have hSsym := TauCeti.inner_swap_of_isSelfAdjoint
    (TauCeti.isSelfAdjoint_offDiagonalPart (U := U) hZsa)
  intro w w'
  rw [offDiagonalSqCompression_apply, offDiagonalSqCompression_apply,
    Submodule.inner_orthogonalProjectionOnto_eq_of_mem_right,
    Submodule.inner_orthogonalProjectionOnto_eq_of_mem_left]
  rw [hSsym (U.offDiagonalPart Z (w : H)) (w' : H),
    hSsym (w : H) (U.offDiagonalPart Z (w' : H))]

/-- **The construction term: a compressed double-angle eigenfamily on any
finite-dimensional `A`-invariant trial subspace.**

Let `W ⊆ 𝔛₀ ∩ D(A)` be a finite-dimensional subspace mapped into itself by `A`.
Then an orthonormal basis of `W` diagonalising the compression `P_W S² P_W`
satisfies *both* compression conditions of `IsCompressedDoubleAngleEigenbasis`,
with `qᵢ² ` the eigenvalues of that compression:

* the Gram clause is the eigen-relation of the compression, read through
  `Submodule.inner_orthogonalProjectionOnto_eq_of_mem_left`;
* the leakage clause holds with **equality**, by
  `re_inner_compressedResidual_eq_zero_of_apply_eq_sum`, because `A yᵢ` lies in
  the span of the family.

The eigenvalues are nonnegative for free, `qᵢ² = ‖S yᵢ‖²`; they are *not* shown
to be positive, and need not be.  Nothing here is approximate and nothing about
the point spectrum of `S²` is assumed. -/
theorem exists_compressedDoubleAngleEigenfamily_of_invariantSubspace
    (hZsa : IsSelfAdjoint Z)
    {W : Submodule ℂ H} [FiniteDimensional ℂ W]
    (hWdom : W ≤ A.domain) (hWU : W ≤ U)
    (hWinv : ∀ w : A.domain, (w : H) ∈ W → A w ∈ W)
    {k : ℕ} (hk : Module.finrank ℂ W = k) :
    ∃ (y : Fin k → A.domain) (q : Fin k → ℝ),
      (∀ i, ((y i : A.domain) : H) ∈ W) ∧
        (∀ i, ((y i : A.domain) : H) ∈ U) ∧
        (Orthonormal ℂ fun i => ((y i : A.domain) : H)) ∧
        (∀ i, 0 ≤ q i) ∧
        (∀ i j, ⟪((y j : A.domain) : H), U.offDiagonalPart Z
            (U.offDiagonalPart Z ((y i : A.domain) : H))⟫_ℂ =
          (((q i) ^ 2 : ℝ) : ℂ) * (if j = i then (1 : ℂ) else 0)) ∧
        (∀ i, RCLike.re ⟪A (y i), U.offDiagonalPart Z
            (U.offDiagonalPart Z ((y i : A.domain) : H)) -
              (((q i) ^ 2 : ℝ) : ℂ) • ((y i : A.domain) : H)⟫_ℂ = 0) := by
  classical
  have hsym := isSymmetric_offDiagonalSqCompression (U := U) (Z := Z) hZsa W
  set e := hsym.eigenvectorBasis hk with he
  set μ := hsym.eigenvalues hk with hμ
  have hSsym := TauCeti.inner_swap_of_isSelfAdjoint
    (TauCeti.isSelfAdjoint_offDiagonalPart (U := U) hZsa)
  have hgram0 : ∀ i j, ⟪((e j : W) : H), U.offDiagonalPart Z
      (U.offDiagonalPart Z ((e i : W) : H))⟫_ℂ =
      ((μ i : ℝ) : ℂ) * (if j = i then (1 : ℂ) else 0) := by
    intro i j
    have h1 : ⟪((e j : W) : H), U.offDiagonalPart Z
        (U.offDiagonalPart Z ((e i : W) : H))⟫_ℂ =
        ⟪e j, offDiagonalSqCompression U Z W (e i)⟫_ℂ := by
      rw [offDiagonalSqCompression_apply,
        Submodule.inner_orthogonalProjectionOnto_eq_of_mem_left]
    rw [h1, he, hμ, LinearMap.IsSymmetric.apply_eigenvectorBasis,
      inner_smul_right, (orthonormal_iff_ite.mp (e.orthonormal)) j i]
    norm_cast
  have hμnn : ∀ i, 0 ≤ μ i := by
    intro i
    have h := hgram0 i i
    rw [ite_eq_left rfl, mul_one] at h
    rw [← hSsym ((e i : W) : H) (U.offDiagonalPart Z ((e i : W) : H))] at h
    have h2 : ((‖U.offDiagonalPart Z ((e i : W) : H)‖ ^ 2 : ℝ) : ℂ) =
        ((μ i : ℝ) : ℂ) := by
      rw [← h, inner_self_eq_norm_sq_to_K]
      norm_cast
    have h3 : ‖U.offDiagonalPart Z ((e i : W) : H)‖ ^ 2 = μ i := by
      exact_mod_cast h2
    rw [← h3]
    positivity
  have hsq : ∀ i, (√(μ i)) ^ 2 = μ i := fun i => Real.sq_sqrt (hμnn i)
  have hyon : Orthonormal ℂ fun i => ((e i : W) : H) := by
    have h := (e.orthonormal).comp_linearIsometry W.subtypeₗᵢ
    simpa [Function.comp_def] using h
  have hgramq : ∀ i j, ⟪((e j : W) : H), U.offDiagonalPart Z
      (U.offDiagonalPart Z ((e i : W) : H))⟫_ℂ =
      (((√(μ i)) ^ 2 : ℝ) : ℂ) * (if j = i then (1 : ℂ) else 0) := by
    intro i j
    rw [hsq i]
    exact hgram0 i j
  refine ⟨fun i => ⟨((e i : W) : H), hWdom (e i).2⟩, fun i => √(μ i),
    fun i => (e i).2, fun i => hWU (e i).2, hyon,
    fun i => Real.sqrt_nonneg _, hgramq, ?_⟩
  intro i
  have hAmem : (A ⟨((e i : W) : H), hWdom (e i).2⟩) ∈ W :=
    hWinv ⟨((e i : W) : H), hWdom (e i).2⟩ (e i).2
  have hsum : A ⟨((e i : W) : H), hWdom (e i).2⟩ =
      ∑ j, (e.repr ⟨A ⟨((e i : W) : H), hWdom (e i).2⟩, hAmem⟩ j) •
        ((e j : W) : H) := by
    have h := e.sum_repr ⟨A ⟨((e i : W) : H), hWdom (e i).2⟩, hAmem⟩
    have h2 := congrArg (fun w : W => (w : H)) h
    simpa using h2.symm
  exact re_inner_compressedResidual_eq_zero_of_apply_eq_sum
    (U := U) (Z := Z) (fun i => ⟨((e i : W) : H), hWdom (e i).2⟩) hyon hgramq
    hsum

/-- **The unbounded, residual-form `tan 2Θ` estimate on an `A`-invariant trial
subspace, with no hypothesis on `Θ` whatsoever.**

`W` ranges over finite-dimensional `A`-invariant subspaces of `𝔛₀ ∩ D(A)`; the
`qᵢ` are the sines of the principal angles the compression of `sin² 2Θ` to `W`
sees, pinned by `‖S yᵢ‖² = qᵢ²`, and the conclusion is

`δ ∑ᵢ qᵢ / √(1 - qᵢ²) ≤ 2 · kyFanApproximationGauge k B`

with **the sharp constant `2`**.  There is no eigenfamily hypothesis, no
positivity hypothesis, no cutoff and no error term: the only input beyond the
standing block data is a finite-dimensional `A`-invariant subspace, which is a
statement about `A`.

The pole is still excluded for free, `qᵢ < 1`, and the vanishing `qᵢ` are
allowed: they are dropped from the family before
`gap_mul_sum_tangent_le_kyFan_of_compressedDoubleAngleEigenfamily` is applied,
which shortens the Ky Fan prefix from `k` to the number of positive eigenvalues
and is absorbed by monotonicity of the gauge in the prefix length. -/
theorem gap_mul_sum_tangent_le_kyFan_of_invariantSubspace
    (hred : TauCeti.LinearPMap.ReducesSubspace A U) (hB : TauCeti.IsOddFor U B)
    (hZsa : IsSelfAdjoint Z) (hZ2 : Z * Z = 1)
    (hZdom : TauCeti.LinearPMap.MapsDomainTo A A Z)
    (hZcomm : ∀ x : A.domain,
      A ⟨Z (x : H), hZdom x⟩ + B (Z (x : H)) = Z (A x) + Z (B (x : H)))
    (hUa : ∀ x : A.domain, (x : H) ∈ U →
      RCLike.re ⟪A x, (x : H)⟫_ℂ ≤ a * ‖(x : H)‖ ^ 2)
    (hUb : ∀ x : A.domain, (x : H) ∈ Uᗮ →
      b * ‖(x : H)‖ ^ 2 ≤ RCLike.re ⟪A x, (x : H)⟫_ℂ)
    (hab : a < b)
    {W : Submodule ℂ H} [FiniteDimensional ℂ W]
    (hWdom : W ≤ A.domain) (hWU : W ≤ U)
    (hWinv : ∀ w : A.domain, (w : H) ∈ W → A w ∈ W)
    {k : ℕ} (hk : Module.finrank ℂ W = k) :
    ∃ (y : Fin k → A.domain) (q : Fin k → ℝ),
      (∀ i, ((y i : A.domain) : H) ∈ W) ∧
        (Orthonormal ℂ fun i => ((y i : A.domain) : H)) ∧
        (∀ i, ‖U.offDiagonalPart Z ((y i : A.domain) : H)‖ ^ 2 = q i ^ 2) ∧
        (∀ i, 0 ≤ q i) ∧ (∀ i, q i < 1) ∧
        (b - a) * ∑ i, q i / √(1 - (q i) ^ 2) ≤
          2 * kyFanApproximationGauge k B := by
  classical
  obtain ⟨y, q, hyW, hyU, hyon, hqnn, hgram, hres⟩ :=
    exists_compressedDoubleAngleEigenfamily_of_invariantSubspace (U := U)
      (A := A) (Z := Z) hZsa hWdom hWU hWinv hk
  have hx1 : ∀ i, ‖((y i : A.domain) : H)‖ = 1 := fun i => hyon.norm_eq_one i
  have hself : ∀ i, ⟪((y i : A.domain) : H), U.offDiagonalPart Z
      (U.offDiagonalPart Z ((y i : A.domain) : H))⟫_ℂ =
      (((q i) ^ 2 : ℝ) : ℂ) := fun i => by rw [hgram i i, ite_eq_left rfl, mul_one]
  have hnorm : ∀ i, ‖U.offDiagonalPart Z ((y i : A.domain) : H)‖ ^ 2 =
      (q i) ^ 2 := fun i =>
    norm_sq_offDiagonalPart_of_compressedDiagonal (U := U) hZsa (hself i)
  have hq1 : ∀ i, q i < 1 := by
    intro i
    rcases lt_or_eq_of_le (hqnn i) with hpos | hzero
    · exact compressedDoubleAngleEigenvalue_lt_one hred hB hZsa hZ2 hZdom hZcomm
        hUa hUb hab (hyU i) (hx1 i) hpos (hself i) (le_of_eq (hres i))
    · rw [← hzero]
      norm_num
  refine ⟨y, q, hyW, hyon, hnorm, hqnn, hq1, ?_⟩
  set s : Finset (Fin k) := Finset.univ.filter (fun i => 0 < q i) with hs
  have hsmem : ∀ i, i ∈ s ↔ 0 < q i := by
    intro i
    rw [hs]
    simp
  set m : ℕ := s.card with hm
  set σ : Fin m → Fin k := fun j => ((s.equivFin.symm j : {x // x ∈ s}) : Fin k)
    with hσ
  have hσinj : Function.Injective σ := by
    intro j j' h
    have hsub : (s.equivFin.symm j : {x // x ∈ s}) = s.equivFin.symm j' :=
      Subtype.ext h
    simpa using hsub
  have hσmem : ∀ j, 0 < q (σ j) := fun j =>
    (hsmem _).mp (s.equivFin.symm j).2
  have hgram' : ∀ i j, ⟪((y (σ j) : A.domain) : H), U.offDiagonalPart Z
      (U.offDiagonalPart Z ((y (σ i) : A.domain) : H))⟫_ℂ =
      (((q (σ i)) ^ 2 : ℝ) : ℂ) * (if j = i then (1 : ℂ) else 0) := by
    intro i j
    rw [hgram (σ i) (σ j)]
    congr 1
    by_cases hji : j = i
    · rw [ite_eq_left hji, ite_eq_left (congrArg σ hji)]
    · rw [ite_eq_right hji, ite_eq_right (fun h => hji (hσinj h))]
  have hmain := gap_mul_sum_tangent_le_kyFan_of_compressedDoubleAngleEigenfamily
    hred hB hZsa hZ2 hZdom hZcomm hUa hUb hab (fun j => y (σ j))
    (fun j => hyU (σ j)) (hyon.comp σ hσinj) hσmem hgram'
    (fun j => le_of_eq (hres (σ j)))
  have hsumeq : ∑ i, q i / √(1 - (q i) ^ 2) =
      ∑ j, q (σ j) / √(1 - (q (σ j)) ^ 2) := by
    have h1 : ∑ j, q (σ j) / √(1 - (q (σ j)) ^ 2) =
        ∑ x : {x // x ∈ s}, q (x : Fin k) / √(1 - (q (x : Fin k)) ^ 2) :=
      Equiv.sum_comp s.equivFin.symm
        (fun x : {x // x ∈ s} => q (x : Fin k) / √(1 - (q (x : Fin k)) ^ 2))
    rw [h1, Finset.sum_coe_sort s (fun i => q i / √(1 - (q i) ^ 2))]
    refine (Finset.sum_subset (Finset.subset_univ s) ?_).symm
    intro i _ hnot
    have hzero : q i = 0 :=
      le_antisymm (not_lt.mp fun hc => hnot ((hsmem i).mpr hc)) (hqnn i)
    rw [hzero]
    simp
  have hmono : kyFanApproximationGauge m B ≤ kyFanApproximationGauge k B := by
    have hmk : m ≤ k := by
      rw [hm]
      simpa using Finset.card_le_card (Finset.subset_univ s)
    simp only [kyFanApproximationGauge_eq_kyFanGauge,
      ContinuousLinearMap.kyFanGauge]
    refine Finset.sum_le_sum_of_subset_of_nonneg
      (fun x hx => Finset.mem_range.mpr
        (lt_of_lt_of_le (Finset.mem_range.mp hx) hmk))
      (fun i _ _ => B.approximationNumber_nonneg i)
  rw [hsumeq]
  linarith [hmain, hmono, (by linarith : (0 : ℝ) ≤ b - a)]

/-- A filtration of `𝔛₀ ∩ D(A)` by finite-dimensional `A`-invariant subspaces
whose compressed principal angles realise the Ky Fan prefixes of a candidate
tangent operator `T`.

Every clause except the last is about `A`, `W` and `Z` alone — no eigenvector of
`sin² 2Θ` is asked for, and no point-spectrum assumption is made.  The last
clause is the *prefix-realisation* clause of `IsCompressedDoubleAngleEigenbasis`
transported to this setting: it is the only link between `T` and the geometry,
and it is quantified over every orthonormal family diagonalising the compression
of `S²` to `W`, which pins it to the compression spectrum rather than to a
choice of basis. -/
def HasInvariantDoubleAngleFiltration (A : H →ₗ.[ℂ] H) (U : Submodule ℂ H)
    [U.HasOrthogonalProjection] (Z T : H →L[ℂ] H) : Prop :=
  ∀ k : ℕ, ∃ (W : Submodule ℂ H) (_ : FiniteDimensional ℂ W),
    Module.finrank ℂ W = k ∧ W ≤ A.domain ∧ W ≤ U ∧
      (∀ w : A.domain, (w : H) ∈ W → A w ∈ W) ∧
      ∀ (y : Fin k → A.domain) (q : Fin k → ℝ),
        (∀ i, ((y i : A.domain) : H) ∈ W) →
        (Orthonormal ℂ fun i => ((y i : A.domain) : H)) →
        (∀ i, 0 ≤ q i) →
        (∀ i j, ⟪((y j : A.domain) : H), U.offDiagonalPart Z
            (U.offDiagonalPart Z ((y i : A.domain) : H))⟫_ℂ =
          (((q i) ^ 2 : ℝ) : ℂ) * (if j = i then (1 : ℂ) else 0)) →
        (∀ i, 0 < q i) ∧
          kyFanApproximationGauge k T ≤ ∑ i, q i / √(1 - (q i) ^ 2)

/-- **An invariant filtration supplies a compressed double-angle eigenbasis.**

This is the discharge: the eigen-part of `IsCompressedDoubleAngleEigenbasis` is
produced outright by
`exists_compressedDoubleAngleEigenfamily_of_invariantSubspace`, and only the
prefix-realisation clause is read off the filtration.  Self-adjointness of `Z`
is the sole analytic input. -/
theorem isCompressedDoubleAngleEigenbasis_of_hasInvariantDoubleAngleFiltration
    (hZsa : IsSelfAdjoint Z) {T : H →L[ℂ] H}
    (hfil : HasInvariantDoubleAngleFiltration A U Z T) :
    IsCompressedDoubleAngleEigenbasis A U Z T := by
  intro k
  obtain ⟨W, hWfd, hk, hWdom, hWU, hWinv, hreal⟩ := hfil k
  obtain ⟨y, q, hyW, hyU, hyon, hqnn, hgram, hres⟩ :=
    exists_compressedDoubleAngleEigenfamily_of_invariantSubspace (U := U)
      (A := A) (Z := Z) hZsa hWdom hWU hWinv hk
  obtain ⟨hqpos, hle⟩ := hreal y q hyW hyon hqnn hgram
  exact ⟨y, q, hyU, hyon, hqpos, hgram, fun i => le_of_eq (hres i), hle⟩

/-- **The unbounded residual `tan 2Θ` theorem at every Ky Fan gauge, on an
invariant filtration.**  `δ · kyFanApproximationGauge k T ≤
2 · kyFanApproximationGauge k B`, with the sharp constant `2`, and with no
hypothesis about the point spectrum of `sin² 2Θ`. -/
theorem gap_mul_kyFan_le_two_mul_kyFan_of_invariantDoubleAngleFiltration
    (hred : TauCeti.LinearPMap.ReducesSubspace A U) (hB : TauCeti.IsOddFor U B)
    (hZsa : IsSelfAdjoint Z) (hZ2 : Z * Z = 1)
    (hZdom : TauCeti.LinearPMap.MapsDomainTo A A Z)
    (hZcomm : ∀ x : A.domain,
      A ⟨Z (x : H), hZdom x⟩ + B (Z (x : H)) = Z (A x) + Z (B (x : H)))
    (hUa : ∀ x : A.domain, (x : H) ∈ U →
      RCLike.re ⟪A x, (x : H)⟫_ℂ ≤ a * ‖(x : H)‖ ^ 2)
    (hUb : ∀ x : A.domain, (x : H) ∈ Uᗮ →
      b * ‖(x : H)‖ ^ 2 ≤ RCLike.re ⟪A x, (x : H)⟫_ℂ)
    (hab : a < b) {T : H →L[ℂ] H}
    (hT : HasInvariantDoubleAngleFiltration A U Z T) (k : ℕ) :
    (b - a) * kyFanApproximationGauge k T ≤
      2 * kyFanApproximationGauge k B :=
  gap_mul_kyFan_le_two_mul_kyFan_of_compressedDoubleAngleEigenbasis hred hB hZsa
    hZ2 hZdom hZcomm hUa hUb hab
    (isCompressedDoubleAngleEigenbasis_of_hasInvariantDoubleAngleFiltration
      hZsa hT) k

/-- **The unbounded, residual-form `tan 2Θ` theorem at every Fan-dominant
unitarily invariant ideal gauge, on an invariant filtration.**

`δ N(tan 2Θ₀) ≤ 2 N(R)` in the repository's scaled form, with ideal membership
of the scaled tangent concluded rather than assumed, and with the eigenbasis
hypothesis replaced throughout by finite-dimensional `A`-invariance. -/
theorem mem_and_gauge_le_of_invariantDoubleAngleFiltration
    (N : KyFanDominantIdealFamily (𝕜 := ℂ))
    (hred : TauCeti.LinearPMap.ReducesSubspace A U) (hB : TauCeti.IsOddFor U B)
    (hZsa : IsSelfAdjoint Z) (hZ2 : Z * Z = 1)
    (hZdom : TauCeti.LinearPMap.MapsDomainTo A A Z)
    (hZcomm : ∀ x : A.domain,
      A ⟨Z (x : H), hZdom x⟩ + B (Z (x : H)) = Z (A x) + Z (B (x : H)))
    (hUa : ∀ x : A.domain, (x : H) ∈ U →
      RCLike.re ⟪A x, (x : H)⟫_ℂ ≤ a * ‖(x : H)‖ ^ 2)
    (hUb : ∀ x : A.domain, (x : H) ∈ Uᗮ →
      b * ‖(x : H)‖ ^ 2 ≤ RCLike.re ⟪A x, (x : H)⟫_ℂ)
    (hab : a < b) {T : H →L[ℂ] H}
    (hT : HasInvariantDoubleAngleFiltration A U Z T) (hBmem : N.Mem B) :
    N.Mem ((((b - a) / 2 : ℝ) : ℂ) • T) ∧
      N.gauge ((((b - a) / 2 : ℝ) : ℂ) • T) ≤ N.gauge B :=
  mem_and_gauge_le_of_compressedDoubleAngleEigenbasis N hred hB hZsa hZ2 hZdom
    hZcomm hUa hUb hab
    (isCompressedDoubleAngleEigenbasis_of_hasInvariantDoubleAngleFiltration
      hZsa hT) hBmem

/-!
## Tying the candidate `T` to the actual `tan 2Θ₀`

Everything above quantifies over an *arbitrary* `T : H →L[ℂ] H`, linked to the
geometry by the single prefix-realisation clause
`kyFanApproximationGauge k T ≤ ∑ᵢ qᵢ / √(1 - qᵢ²)`.  This section replaces that
free variable by the genuine tangent and then measures exactly what the clause
asks for.

The genuine object is fixed by the same defining identity the bounded theory
uses (`directedTanTwoAngleOperatorC_comp_cosTwoAngleExtendedC`): a **double-angle
tangent** is an operator `T` with `T (C x) = S x` on the trial subspace, for
`C = cos 2Θ₀` and `S = sin 2Θ₀` the even and odd blocks of `Z` relative to
`𝔛₀ ⊕ 𝔛₁`.  Such a `T` exists **unconditionally** in the Davis--Kahan setting:
the operator-norm pole exclusion already proved in
`TauCeti.norm_offDiagonalPart_apply_le_specRange` makes `S` a strict contraction
with the explicit constant `2‖B‖ / √(δ² + 4‖B‖²) < 1`, so `C² = 1 - S²` is a
Neumann unit and `tan 2Θ₀ = S · C⁻¹` is a bounded operator.

**The direction of the prefix-realisation clause is the obstruction, and it is
the reverse of a theorem.**  For *any* double-angle tangent `T` and *any*
compressed eigenfamily, the four exactly orthonormal auxiliary systems already
built above pair to give

`∑ᵢ qᵢ / √(1 - qᵢ²) ≤ kyFanApproximationGauge k T`,

which is `sum_tangent_le_kyFan_of_compressedDoubleAngleEigenfamily` below.  The
compression eigenvalues therefore *never* dominate the tangent's prefix; they
are dominated by it.  Consequently, when `T` is the genuine tangent, the clause
`kyFanApproximationGauge k T ≤ ∑ᵢ qᵢ / √(1 - qᵢ²)` is equivalent to **equality**
— `kyFan_eq_sum_tangent_of_isCompressedDoubleAngleEigenbasis` — that is, to the
compression being Ky Fan *extremal* for `sin² 2Θ`.  Finite-dimensional
`A`-invariance of `W` says nothing about extremality for `S²`, so
`exists_compressedDoubleAngleEigenfamily_of_invariantSubspace` cannot supply it:
`sum_tangent_le_kyFan_of_invariantSubspace` records that what the construction
does supply is precisely the opposite inequality.

The endpoints are therefore stated at the genuine tangent below, but they remain
conditional on that extremality clause, and this section makes the residual
hypothesis exact rather than hiding it in a free operator.
-/

/-- `T` is a **double-angle tangent** for the reflection `Z` relative to the trial
subspace `U`: composing it with the even block `C = cos 2Θ₀` returns the odd
block `S = sin 2Θ₀` there.  This is the reflection-picture analogue of
`directedTanTwoAngleOperatorC_comp_cosTwoAngleExtendedC`, and it is what makes an
operator *the* `tan 2Θ₀` rather than a free variable. -/
def IsDoubleAngleTangent (U : Submodule ℂ H) [U.HasOrthogonalProjection]
    (Z T : H →L[ℂ] H) : Prop :=
  ∀ x ∈ U, T (U.diagonalPart Z x) = U.offDiagonalPart Z x

/-- A trial-subspace contraction bound for the odd block transfers to `Uᗮ`.
`S` is self-adjoint and carries `Uᗮ` into `U`, so `‖S x‖² = ⟪x, S (S x)⟫` may be
estimated with the bound applied at `S x ∈ U`. -/
theorem norm_offDiagonalPart_apply_le_of_mem_orthogonal
    (hZsa : IsSelfAdjoint Z) {g : ℝ} (hg0 : 0 ≤ g)
    (hgU : ∀ y ∈ U, ‖U.offDiagonalPart Z y‖ ≤ g * ‖y‖)
    {x : H} (hx : x ∈ Uᗮ) :
    ‖U.offDiagonalPart Z x‖ ≤ g * ‖x‖ := by
  have hSsym := TauCeti.inner_swap_of_isSelfAdjoint
    (TauCeti.isSelfAdjoint_offDiagonalPart (U := U) hZsa)
  have hSxU : U.offDiagonalPart Z x ∈ U :=
    TauCeti.offDiagonalPart_mem_of_mem_orthogonal U Z hx
  have h1 : ⟪U.offDiagonalPart Z x, U.offDiagonalPart Z x⟫_ℂ =
      ⟪x, U.offDiagonalPart Z (U.offDiagonalPart Z x)⟫_ℂ :=
    hSsym x (U.offDiagonalPart Z x)
  have hn : ‖U.offDiagonalPart Z x‖ ^ 2 =
      ‖⟪U.offDiagonalPart Z x, U.offDiagonalPart Z x⟫_ℂ‖ := by
    rw [inner_self_eq_norm_sq_to_K, norm_pow, RCLike.norm_ofReal,
      abs_of_nonneg (norm_nonneg _)]
  have h2 : ‖U.offDiagonalPart Z x‖ ^ 2 ≤
      ‖x‖ * ‖U.offDiagonalPart Z (U.offDiagonalPart Z x)‖ := by
    rw [hn, h1]
    exact norm_inner_le_norm _ _
  have h3 : ‖U.offDiagonalPart Z (U.offDiagonalPart Z x)‖ ≤
      g * ‖U.offDiagonalPart Z x‖ := hgU _ hSxU
  by_contra hcon
  rw [not_le] at hcon
  have hXn : ‖x‖ * ‖U.offDiagonalPart Z (U.offDiagonalPart Z x)‖ ≤
      ‖x‖ * (g * ‖U.offDiagonalPart Z x‖) :=
    mul_le_mul_of_nonneg_left h3 (norm_nonneg x)
  have hnpos : 0 < ‖U.offDiagonalPart Z x‖ :=
    lt_of_le_of_lt (mul_nonneg hg0 (norm_nonneg x)) hcon
  nlinarith [hnpos, hXn, h2, hcon]

/-- A trial-subspace contraction bound for the odd block is an ambient one: the
two halves of the orthogonal splitting land in orthogonal subspaces, so the two
squared bounds add with no cross term and **no factor is lost**. -/
theorem norm_offDiagonalPart_apply_le
    (hZsa : IsSelfAdjoint Z) {g : ℝ} (hg0 : 0 ≤ g)
    (hgU : ∀ y ∈ U, ‖U.offDiagonalPart Z y‖ ≤ g * ‖y‖) (x : H) :
    ‖U.offDiagonalPart Z x‖ ≤ g * ‖x‖ := by
  set p := U.starProjection x with hp
  set r := Uᗮ.starProjection x with hr
  have hpU : p ∈ U := U.starProjection_apply_mem x
  have hrU : r ∈ Uᗮ := Uᗮ.starProjection_apply_mem x
  have hsum : p + r = x :=
    Submodule.starProjection_add_starProjection_orthogonal x
  have hpr : ⟪p, r⟫_ℂ = 0 := (Submodule.mem_orthogonal U r).mp hrU p hpU
  have hSp : U.offDiagonalPart Z p ∈ Uᗮ :=
    TauCeti.offDiagonalPart_mem_orthogonal_of_mem U Z hpU
  have hSr : U.offDiagonalPart Z r ∈ U :=
    TauCeti.offDiagonalPart_mem_of_mem_orthogonal U Z hrU
  have hSpr : ⟪U.offDiagonalPart Z p, U.offDiagonalPart Z r⟫_ℂ = 0 := by
    have h := (Submodule.mem_orthogonal U (U.offDiagonalPart Z p)).mp hSp
      (U.offDiagonalPart Z r) hSr
    exact inner_eq_zero_symm.mp h
  have hxsq : ‖x‖ * ‖x‖ = ‖p‖ * ‖p‖ + ‖r‖ * ‖r‖ := by
    rw [← hsum]
    exact norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero p r hpr
  have hSxeq : U.offDiagonalPart Z x =
      U.offDiagonalPart Z p + U.offDiagonalPart Z r := by
    rw [← hsum, map_add]
  have hSsq : ‖U.offDiagonalPart Z x‖ * ‖U.offDiagonalPart Z x‖ =
      ‖U.offDiagonalPart Z p‖ * ‖U.offDiagonalPart Z p‖ +
        ‖U.offDiagonalPart Z r‖ * ‖U.offDiagonalPart Z r‖ := by
    rw [hSxeq]
    exact norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero _ _ hSpr
  have hbp : ‖U.offDiagonalPart Z p‖ ≤ g * ‖p‖ := hgU p hpU
  have hbr : ‖U.offDiagonalPart Z r‖ ≤ g * ‖r‖ :=
    norm_offDiagonalPart_apply_le_of_mem_orthogonal hZsa hg0 hgU hrU
  have hsp : ‖U.offDiagonalPart Z p‖ * ‖U.offDiagonalPart Z p‖ ≤
      (g * ‖p‖) * (g * ‖p‖) := mul_self_le_mul_self (norm_nonneg _) hbp
  have hsr : ‖U.offDiagonalPart Z r‖ * ‖U.offDiagonalPart Z r‖ ≤
      (g * ‖r‖) * (g * ‖r‖) := mul_self_le_mul_self (norm_nonneg _) hbr
  have hgx : (g * ‖x‖) * (g * ‖x‖) =
      (g * ‖p‖) * (g * ‖p‖) + (g * ‖r‖) * (g * ‖r‖) := by
    linear_combination (g * g) * hxsq
  have hfin : ‖U.offDiagonalPart Z x‖ * ‖U.offDiagonalPart Z x‖ ≤
      (g * ‖x‖) * (g * ‖x‖) := by rw [hgx, hSsq]; linarith [hsp, hsr]
  by_contra hcon
  rw [not_le] at hcon
  have hnpos : 0 < ‖U.offDiagonalPart Z x‖ :=
    lt_of_le_of_lt (mul_nonneg hg0 (norm_nonneg x)) hcon
  nlinarith [hfin, hcon, hnpos, mul_nonneg hg0 (norm_nonneg x)]

/-- Operator-norm form of the ambient contraction bound. -/
theorem norm_offDiagonalPart_le
    (hZsa : IsSelfAdjoint Z) {g : ℝ} (hg0 : 0 ≤ g)
    (hgU : ∀ y ∈ U, ‖U.offDiagonalPart Z y‖ ≤ g * ‖y‖) :
    ‖U.offDiagonalPart Z‖ ≤ g :=
  ContinuousLinearMap.opNorm_le_bound _ hg0
    (norm_offDiagonalPart_apply_le hZsa hg0 hgU)

/-- **The pole is excluded in operator form.**  `C² = 1 - S²` is a Neumann unit as
soon as `S²` is a strict contraction, so `cos 2Θ₀` is boundedly invertible and
the tangent is a bounded operator. -/
theorem isUnit_diagonalPart_sq (hZ2 : Z * Z = 1)
    (h : ‖U.offDiagonalPart Z * U.offDiagonalPart Z‖ < 1) :
    IsUnit (U.diagonalPart Z * U.diagonalPart Z) := by
  have hsum := TauCeti.diagonalPart_sq_add_offDiagonalPart_sq (U := U) hZ2
  have hCC : U.diagonalPart Z * U.diagonalPart Z =
      1 - U.offDiagonalPart Z * U.offDiagonalPart Z := by
    rw [← hsum]; abel
  rw [hCC]
  exact ⟨Units.oneSub _ h, rfl⟩

/-- **The tangent of the unbounded reflection picture**,
`tan 2Θ₀ = sin 2Θ₀ · (cos 2Θ₀)⁻¹`, written so that the definition is total: the
inverse is taken of `cos² 2Θ₀` through `Ring.inverse`, and the remaining
`cos 2Θ₀` is kept on the right.  No hypothesis is attached to the definition;
`isUnit_diagonalPart_sq` is what makes it the intended operator.

The body is block algebra in the ring `H →L[𝕜] H`, so the definition is stated
for an arbitrary `RCLike` scalar field; only the *theorems* about it below are
complex. -/
def unboundedReflectionTangent {𝕜 : Type*} [RCLike 𝕜] {G : Type*}
    [NormedAddCommGroup G] [InnerProductSpace 𝕜 G]
    (U : Submodule 𝕜 G) [U.HasOrthogonalProjection]
    (Z : G →L[𝕜] G) : G →L[𝕜] G :=
  U.offDiagonalPart Z *
    Ring.inverse (U.diagonalPart Z * U.diagonalPart Z) * U.diagonalPart Z

omit [CompleteSpace H] in
/-- **The defining identity of the tangent**: `tan 2Θ₀ ∘ cos 2Θ₀ = sin 2Θ₀`. -/
theorem unboundedReflectionTangent_comp_diagonalPart
    (hCC : IsUnit (U.diagonalPart Z * U.diagonalPart Z)) :
    unboundedReflectionTangent U Z ∘L U.diagonalPart Z =
      U.offDiagonalPart Z := by
  have hinv := Ring.inverse_mul_cancel _ hCC
  have hassoc : unboundedReflectionTangent U Z * U.diagonalPart Z =
      U.offDiagonalPart Z *
        (Ring.inverse (U.diagonalPart Z * U.diagonalPart Z) *
          (U.diagonalPart Z * U.diagonalPart Z)) := by
    rw [unboundedReflectionTangent]
    noncomm_ring
  show unboundedReflectionTangent U Z * U.diagonalPart Z = _
  rw [hassoc, hinv, mul_one]

omit [CompleteSpace H] in
/-- The constructed operator really is a double-angle tangent. -/
theorem isDoubleAngleTangent_unboundedReflectionTangent
    (hCC : IsUnit (U.diagonalPart Z * U.diagonalPart Z)) :
    IsDoubleAngleTangent U Z (unboundedReflectionTangent U Z) := by
  intro x _
  exact congrArg (fun T : H →L[ℂ] H => T x)
    (unboundedReflectionTangent_comp_diagonalPart hCC)

/-- The cross-block bound `2‖B‖ / √(δ² + 4‖B‖²)` is a strict contraction as soon
as the gap `δ` is positive. -/
theorem crossBlockBound_lt_one {δ nB : ℝ} (hδ : 0 < δ) (hnB : 0 ≤ nB) :
    TauCeti.crossBlockBound δ nB < 1 := by
  rw [TauCeti.crossBlockBound_eq]
  have hpos : 0 < √(δ ^ 2 + 4 * nB ^ 2) := Real.sqrt_pos.mpr (by positivity)
  rw [div_lt_one hpos]
  have hsq : (2 * nB) ^ 2 < (√(δ ^ 2 + 4 * nB ^ 2)) ^ 2 := by
    rw [Real.sq_sqrt (by positivity)]
    nlinarith
  nlinarith [hpos, hsq]

/-- **The pole is excluded from a trial-subspace contraction bound alone.** -/
theorem isUnit_diagonalPart_sq_of_forall_mem
    (hZsa : IsSelfAdjoint Z) (hZ2 : Z * Z = 1) {g : ℝ} (hg0 : 0 ≤ g)
    (hg1 : g < 1) (hgU : ∀ y ∈ U, ‖U.offDiagonalPart Z y‖ ≤ g * ‖y‖) :
    IsUnit (U.diagonalPart Z * U.diagonalPart Z) := by
  have hS : ‖U.offDiagonalPart Z‖ ≤ g := norm_offDiagonalPart_le hZsa hg0 hgU
  have hmul : ‖U.offDiagonalPart Z * U.offDiagonalPart Z‖ ≤
      ‖U.offDiagonalPart Z‖ * ‖U.offDiagonalPart Z‖ := norm_mul_le _ _
  refine isUnit_diagonalPart_sq hZ2 ?_
  nlinarith [hmul, hS, norm_nonneg (U.offDiagonalPart Z)]

section GenuineTangentExists

variable {c : ℝ}

/-- **The genuine unbounded `tan 2Θ₀` exists, with no extra hypothesis.**

Under exactly the standing Davis--Kahan data of `tanTwoTheta_unbounded_residual_opNorm_complex`
— `A` self-adjoint and possibly unbounded, `𝔛₀ = 1_{(-∞, c]}(A)`, `B` bounded and
fully off-diagonal, `Z` the reducing reflection `2Q - 1`, and the form separation
`a < b` — the operator `unboundedReflectionTangent 𝔛₀ Z` satisfies the defining
identity `T (cos 2Θ₀ x) = sin 2Θ₀ x` on the trial subspace.

This is what removes the free variable: from here on, `tan 2Θ₀` is a constructed
operator and not a hypothesis. -/
theorem isDoubleAngleTangent_unboundedReflectionTangent_specRange
    (hA : IsSelfAdjoint A)
    (hB : TauCeti.IsOddFor
      (TauCeti.LinearPMap.specRange hA (Set.Iic c) measurableSet_Iic) B)
    (hZsa : IsSelfAdjoint Z) (hZ2 : Z * Z = 1)
    (hZdom : TauCeti.LinearPMap.MapsDomainTo A A Z)
    (hZcomm : ∀ x : A.domain,
      A ⟨Z (x : H), hZdom x⟩ + B (Z (x : H)) = Z (A x) + Z (B (x : H)))
    (hUa : ∀ x : A.domain,
      (x : H) ∈ TauCeti.LinearPMap.specRange hA (Set.Iic c) measurableSet_Iic →
      RCLike.re ⟪A x, (x : H)⟫_ℂ ≤ a * ‖(x : H)‖ ^ 2)
    (hUb : ∀ x : A.domain,
      (x : H) ∈
        (TauCeti.LinearPMap.specRange hA (Set.Iic c) measurableSet_Iic)ᗮ →
      b * ‖(x : H)‖ ^ 2 ≤ RCLike.re ⟪A x, (x : H)⟫_ℂ)
    (hab : a < b) :
    IsDoubleAngleTangent
      (TauCeti.LinearPMap.specRange hA (Set.Iic c) measurableSet_Iic) Z
      (unboundedReflectionTangent
        (TauCeti.LinearPMap.specRange hA (Set.Iic c) measurableSet_Iic) Z) := by
  have hgU : ∀ y ∈ TauCeti.LinearPMap.specRange hA (Set.Iic c) measurableSet_Iic,
      ‖(TauCeti.LinearPMap.specRange hA (Set.Iic c)
          measurableSet_Iic).offDiagonalPart Z y‖ ≤
        TauCeti.crossBlockBound (b - a) ‖B‖ * ‖y‖ := fun y hy =>
    TauCeti.norm_offDiagonalPart_apply_le_specRange hA hB hZsa hZ2 hZdom
      hZcomm hUa hUb hab hy
  exact isDoubleAngleTangent_unboundedReflectionTangent
    (isUnit_diagonalPart_sq_of_forall_mem hZsa hZ2
      (TauCeti.crossBlockBound_nonneg (norm_nonneg B))
      (crossBlockBound_lt_one (by linarith) (norm_nonneg B)) hgU)

end GenuineTangentExists

/-- **The compression sum is a *lower* bound for the tangent's Ky Fan prefix.**

For any double-angle tangent `T` and any compressed eigenfamily with `0 < qᵢ < 1`,

`∑ᵢ qᵢ / √(1 - qᵢ²) ≤ kyFanApproximationGauge n T`.

The two systems `S xᵢ / qᵢ` and `C xᵢ / cᵢ`, `cᵢ = √(1 - qᵢ²)`, are exactly
orthonormal at a compressed eigenfamily — this is
`inner_of_compressedDoubleAngleEigenfamily`, whose Gram identities never see the
leakage — and the defining identity sends the second to the first:
`T (C xᵢ / cᵢ) = S xᵢ / cᵢ`.  Pairing gives `qᵢ² / (qᵢ cᵢ) = qᵢ / cᵢ` exactly,
and `sum_le_kyFanApproximationGauge_of_orthonormal` sums it.

**This is the reverse of the prefix-realisation clause of
`IsCompressedDoubleAngleEigenbasis`**, so for a genuine tangent that clause can
only ever hold with equality. -/
theorem sum_tangent_le_kyFan_of_compressedDoubleAngleEigenfamily
    (hZsa : IsSelfAdjoint Z) (hZ2 : Z * Z = 1)
    {T : H →L[ℂ] H} (hT : IsDoubleAngleTangent U Z T)
    {n : ℕ} (x : Fin n → H) (hxU : ∀ i, x i ∈ U)
    (hxon : Orthonormal ℂ x) {q : Fin n → ℝ}
    (hq : ∀ i, 0 < q i) (hq1 : ∀ i, q i < 1)
    (hgram : ∀ i j, ⟪x j, U.offDiagonalPart Z
        (U.offDiagonalPart Z (x i))⟫_ℂ =
      (((q i) ^ 2 : ℝ) : ℂ) * (if j = i then (1 : ℂ) else 0)) :
    ∑ i, q i / √(1 - (q i) ^ 2) ≤ kyFanApproximationGauge n T := by
  classical
  have hcarg : ∀ i, (0 : ℝ) < 1 - (q i) ^ 2 := by
    intro i; nlinarith [hq i, hq1 i]
  have hcpos : ∀ i, (0 : ℝ) < √(1 - (q i) ^ 2) := fun i =>
    Real.sqrt_pos.mpr (hcarg i)
  have hcsq : ∀ i, (√(1 - (q i) ^ 2)) ^ 2 = 1 - (q i) ^ 2 := fun i =>
    Real.sq_sqrt (hcarg i).le
  have hG := fun i j => inner_of_compressedDoubleAngleEigenfamily
    (U := U) hZsa hZ2 x hxon hgram i j
  have hu : Orthonormal ℂ fun i =>
      (((q i : ℝ) : ℂ)⁻¹ • U.offDiagonalPart Z (x i)) :=
    orthonormal_scaled_of_inner_eq hq (fun i j => (hG i j).1)
  have hv : Orthonormal ℂ fun i =>
      (((√(1 - (q i) ^ 2) : ℝ) : ℂ)⁻¹ • U.diagonalPart Z (x i)) := by
    refine orthonormal_scaled_of_inner_eq hcpos ?_
    intro i j
    rw [(hG i j).2, hcsq j]
  refine sum_le_kyFanApproximationGauge_of_orthonormal T hu hv ?_
  intro i
  have hTv : T (((√(1 - (q i) ^ 2) : ℝ) : ℂ)⁻¹ • U.diagonalPart Z (x i)) =
      ((√(1 - (q i) ^ 2) : ℝ) : ℂ)⁻¹ • U.offDiagonalPart Z (x i) := by
    rw [map_smul, hT (x i) (hxU i)]
  rw [hTv, inner_smul_left, inner_smul_right, (hG i i).1]
  rw [ite_eq_left rfl, mul_one]
  have hqi := (hq i).ne'
  have hci := (hcpos i).ne'
  rw [← Complex.ofReal_inv, ← Complex.ofReal_inv, Complex.conj_ofReal]
  rw [← Complex.ofReal_mul, ← Complex.ofReal_mul]
  have hval : (q i)⁻¹ * ((√(1 - (q i) ^ 2))⁻¹ * (q i) ^ 2) =
      q i / √(1 - (q i) ^ 2) := by
    field_simp
  rw [hval, RCLike.re_to_complex, Complex.ofReal_re]

/-- **What the `A`-invariant construction actually supplies, at the genuine
tangent: the opposite inequality.**

Run `exists_compressedDoubleAngleEigenfamily_of_invariantSubspace` on a
finite-dimensional `A`-invariant `W ⊆ 𝔛₀ ∩ D(A)` and pair the resulting family
against any double-angle tangent `T`.  The conclusion is

`∑ᵢ qᵢ / √(1 - qᵢ²) ≤ kyFanApproximationGauge k T`,

with the vanishing `qᵢ` dropped exactly as in
`gap_mul_sum_tangent_le_kyFan_of_invariantSubspace` — which only shortens the
prefix and is absorbed by monotonicity of the gauge, in the same direction.

**This is why the endpoints below cannot be made unconditional along this
route.**  What `IsCompressedDoubleAngleEigenbasis` asks for is
`kyFanApproximationGauge k T ≤ ∑ᵢ qᵢ / √(1 - qᵢ²)`; the construction proves the
reverse.  The two together force equality, i.e. Ky Fan extremality of the
compression of `sin² 2Θ` to `W`, and finite-dimensional `A`-invariance of `W`
carries no information about that. -/
theorem sum_tangent_le_kyFan_of_invariantSubspace
    (hred : TauCeti.LinearPMap.ReducesSubspace A U) (hB : TauCeti.IsOddFor U B)
    (hZsa : IsSelfAdjoint Z) (hZ2 : Z * Z = 1)
    (hZdom : TauCeti.LinearPMap.MapsDomainTo A A Z)
    (hZcomm : ∀ x : A.domain,
      A ⟨Z (x : H), hZdom x⟩ + B (Z (x : H)) = Z (A x) + Z (B (x : H)))
    (hUa : ∀ x : A.domain, (x : H) ∈ U →
      RCLike.re ⟪A x, (x : H)⟫_ℂ ≤ a * ‖(x : H)‖ ^ 2)
    (hUb : ∀ x : A.domain, (x : H) ∈ Uᗮ →
      b * ‖(x : H)‖ ^ 2 ≤ RCLike.re ⟪A x, (x : H)⟫_ℂ)
    (hab : a < b) {T : H →L[ℂ] H} (hTtan : IsDoubleAngleTangent U Z T)
    {W : Submodule ℂ H} [FiniteDimensional ℂ W]
    (hWdom : W ≤ A.domain) (hWU : W ≤ U)
    (hWinv : ∀ w : A.domain, (w : H) ∈ W → A w ∈ W)
    {k : ℕ} (hk : Module.finrank ℂ W = k) :
    ∃ (y : Fin k → A.domain) (q : Fin k → ℝ),
      (∀ i, ((y i : A.domain) : H) ∈ W) ∧
        (Orthonormal ℂ fun i => ((y i : A.domain) : H)) ∧
        (∀ i, ‖U.offDiagonalPart Z ((y i : A.domain) : H)‖ ^ 2 = q i ^ 2) ∧
        (∀ i, 0 ≤ q i) ∧ (∀ i, q i < 1) ∧
        ∑ i, q i / √(1 - (q i) ^ 2) ≤ kyFanApproximationGauge k T := by
  classical
  obtain ⟨y, q, hyW, hyU, hyon, hqnn, hgram, hres⟩ :=
    exists_compressedDoubleAngleEigenfamily_of_invariantSubspace (U := U)
      (A := A) (Z := Z) hZsa hWdom hWU hWinv hk
  have hx1 : ∀ i, ‖((y i : A.domain) : H)‖ = 1 := fun i => hyon.norm_eq_one i
  have hself : ∀ i, ⟪((y i : A.domain) : H), U.offDiagonalPart Z
      (U.offDiagonalPart Z ((y i : A.domain) : H))⟫_ℂ =
      (((q i) ^ 2 : ℝ) : ℂ) := fun i => by rw [hgram i i, ite_eq_left rfl, mul_one]
  have hnorm : ∀ i, ‖U.offDiagonalPart Z ((y i : A.domain) : H)‖ ^ 2 =
      (q i) ^ 2 := fun i =>
    norm_sq_offDiagonalPart_of_compressedDiagonal (U := U) hZsa (hself i)
  have hq1 : ∀ i, q i < 1 := by
    intro i
    rcases lt_or_eq_of_le (hqnn i) with hpos | hzero
    · exact compressedDoubleAngleEigenvalue_lt_one hred hB hZsa hZ2 hZdom hZcomm
        hUa hUb hab (hyU i) (hx1 i) hpos (hself i) (le_of_eq (hres i))
    · rw [← hzero]
      norm_num
  refine ⟨y, q, hyW, hyon, hnorm, hqnn, hq1, ?_⟩
  set s : Finset (Fin k) := Finset.univ.filter (fun i => 0 < q i) with hs
  have hsmem : ∀ i, i ∈ s ↔ 0 < q i := by
    intro i
    rw [hs]
    simp
  set m : ℕ := s.card with hm
  set σ : Fin m → Fin k := fun j => ((s.equivFin.symm j : {x // x ∈ s}) : Fin k)
    with hσ
  have hσinj : Function.Injective σ := by
    intro j j' h
    have hsub : (s.equivFin.symm j : {x // x ∈ s}) = s.equivFin.symm j' :=
      Subtype.ext h
    simpa using hsub
  have hσmem : ∀ j, 0 < q (σ j) := fun j =>
    (hsmem _).mp (s.equivFin.symm j).2
  have hgram' : ∀ i j, ⟪((y (σ j) : A.domain) : H), U.offDiagonalPart Z
      (U.offDiagonalPart Z ((y (σ i) : A.domain) : H))⟫_ℂ =
      (((q (σ i)) ^ 2 : ℝ) : ℂ) * (if j = i then (1 : ℂ) else 0) := by
    intro i j
    rw [hgram (σ i) (σ j)]
    congr 1
    by_cases hji : j = i
    · rw [ite_eq_left hji, ite_eq_left (congrArg σ hji)]
    · rw [ite_eq_right hji, ite_eq_right (fun h => hji (hσinj h))]
  have hmain := sum_tangent_le_kyFan_of_compressedDoubleAngleEigenfamily
    hZsa hZ2 hTtan (fun j => ((y (σ j) : A.domain) : H))
    (fun j => hyU (σ j)) (hyon.comp σ hσinj) hσmem (fun j => hq1 (σ j)) hgram'
  have hsumeq : ∑ i, q i / √(1 - (q i) ^ 2) =
      ∑ j, q (σ j) / √(1 - (q (σ j)) ^ 2) := by
    have h1 : ∑ j, q (σ j) / √(1 - (q (σ j)) ^ 2) =
        ∑ x : {x // x ∈ s}, q (x : Fin k) / √(1 - (q (x : Fin k)) ^ 2) :=
      Equiv.sum_comp s.equivFin.symm
        (fun x : {x // x ∈ s} => q (x : Fin k) / √(1 - (q (x : Fin k)) ^ 2))
    rw [h1, Finset.sum_coe_sort s (fun i => q i / √(1 - (q i) ^ 2))]
    refine (Finset.sum_subset (Finset.subset_univ s) ?_).symm
    intro i _ hnot
    have hzero : q i = 0 :=
      le_antisymm (not_lt.mp fun hc => hnot ((hsmem i).mpr hc)) (hqnn i)
    rw [hzero]
    simp
  have hmono : kyFanApproximationGauge m T ≤ kyFanApproximationGauge k T := by
    have hmk : m ≤ k := by
      rw [hm]
      simpa using Finset.card_le_card (Finset.subset_univ s)
    simp only [kyFanApproximationGauge_eq_kyFanGauge,
      ContinuousLinearMap.kyFanGauge]
    refine Finset.sum_le_sum_of_subset_of_nonneg
      (fun x hx => Finset.mem_range.mpr
        (lt_of_lt_of_le (Finset.mem_range.mp hx) hmk))
      (fun i _ _ => T.approximationNumber_nonneg i)
  rw [hsumeq]
  linarith [hmain, hmono]

/-- **At the genuine tangent, the prefix-realisation clause is an equality.**

`IsCompressedDoubleAngleEigenbasis A U Z T` asserts an inequality
`kyFanApproximationGauge k T ≤ ∑ᵢ qᵢ / √(1 - qᵢ²)` whose converse is a theorem
whenever `T` is a double-angle tangent.  So for the genuine `tan 2Θ₀` that
hypothesis says exactly that the compression of `sin² 2Θ` to the family's span
**attains** the Ky Fan prefix — a Ky Fan extremality property of the family, not
a property that any subspace construction supplies. -/
theorem kyFan_eq_sum_tangent_of_isCompressedDoubleAngleEigenbasis
    (hred : TauCeti.LinearPMap.ReducesSubspace A U) (hB : TauCeti.IsOddFor U B)
    (hZsa : IsSelfAdjoint Z) (hZ2 : Z * Z = 1)
    (hZdom : TauCeti.LinearPMap.MapsDomainTo A A Z)
    (hZcomm : ∀ x : A.domain,
      A ⟨Z (x : H), hZdom x⟩ + B (Z (x : H)) = Z (A x) + Z (B (x : H)))
    (hUa : ∀ x : A.domain, (x : H) ∈ U →
      RCLike.re ⟪A x, (x : H)⟫_ℂ ≤ a * ‖(x : H)‖ ^ 2)
    (hUb : ∀ x : A.domain, (x : H) ∈ Uᗮ →
      b * ‖(x : H)‖ ^ 2 ≤ RCLike.re ⟪A x, (x : H)⟫_ℂ)
    (hab : a < b) {T : H →L[ℂ] H} (hTtan : IsDoubleAngleTangent U Z T)
    (hT : IsCompressedDoubleAngleEigenbasis A U Z T) (k : ℕ) :
    ∃ (y : Fin k → A.domain) (q : Fin k → ℝ),
      (∀ i, ((y i : A.domain) : H) ∈ U) ∧
        (Orthonormal ℂ fun i => ((y i : A.domain) : H)) ∧
        (∀ i, 0 < q i) ∧ (∀ i, q i < 1) ∧
        kyFanApproximationGauge k T = ∑ i, q i / √(1 - (q i) ^ 2) := by
  obtain ⟨y, q, hyU, hyon, hqpos, hygram, hyres, hle⟩ := hT k
  have hx1 : ∀ i, ‖((y i : A.domain) : H)‖ = 1 := fun i => hyon.norm_eq_one i
  have hself : ∀ i, ⟪((y i : A.domain) : H), U.offDiagonalPart Z
      (U.offDiagonalPart Z ((y i : A.domain) : H))⟫_ℂ =
      (((q i) ^ 2 : ℝ) : ℂ) := fun i => by
    rw [hygram i i, ite_eq_left rfl, mul_one]
  have hq1 : ∀ i, q i < 1 := fun i =>
    compressedDoubleAngleEigenvalue_lt_one hred hB hZsa hZ2 hZdom hZcomm hUa hUb
      hab (hyU i) (hx1 i) (hqpos i) (hself i) (hyres i)
  refine ⟨y, q, hyU, hyon, hqpos, hq1, le_antisymm hle ?_⟩
  exact sum_tangent_le_kyFan_of_compressedDoubleAngleEigenfamily hZsa hZ2 hTtan
    (fun i => ((y i : A.domain) : H)) hyU hyon hqpos hq1 hygram

/-- **The Ky Fan endpoint, stated at the genuine `tan 2Θ₀`.**

`δ · kyFanApproximationGauge k (tan 2Θ₀) ≤ 2 · kyFanApproximationGauge k B`, with
the sharp constant `2`, for the constructed operator rather than a free `T`.

It is **not** unconditional: the surviving hypothesis is
`IsCompressedDoubleAngleEigenbasis A U Z (unboundedReflectionTangent U Z)`, which
by `kyFan_eq_sum_tangent_of_isCompressedDoubleAngleEigenbasis` is exactly the
statement that some compressed eigenfamily *attains* the prefix.  The gain over
`gap_mul_kyFan_le_two_mul_kyFan_of_compressedDoubleAngleEigenbasis` is that the
conclusion is now about a constructed operator; the two statements are otherwise
the same theorem, and this one is its specialisation at `T = tan 2Θ₀`. -/
theorem gap_mul_kyFan_le_two_mul_kyFan_unboundedReflectionTangent
    (hred : TauCeti.LinearPMap.ReducesSubspace A U) (hB : TauCeti.IsOddFor U B)
    (hZsa : IsSelfAdjoint Z) (hZ2 : Z * Z = 1)
    (hZdom : TauCeti.LinearPMap.MapsDomainTo A A Z)
    (hZcomm : ∀ x : A.domain,
      A ⟨Z (x : H), hZdom x⟩ + B (Z (x : H)) = Z (A x) + Z (B (x : H)))
    (hUa : ∀ x : A.domain, (x : H) ∈ U →
      RCLike.re ⟪A x, (x : H)⟫_ℂ ≤ a * ‖(x : H)‖ ^ 2)
    (hUb : ∀ x : A.domain, (x : H) ∈ Uᗮ →
      b * ‖(x : H)‖ ^ 2 ≤ RCLike.re ⟪A x, (x : H)⟫_ℂ)
    (hab : a < b)
    (hT : IsCompressedDoubleAngleEigenbasis A U Z
      (unboundedReflectionTangent U Z)) (k : ℕ) :
    (b - a) * kyFanApproximationGauge k (unboundedReflectionTangent U Z) ≤
      2 * kyFanApproximationGauge k B :=
  gap_mul_kyFan_le_two_mul_kyFan_of_compressedDoubleAngleEigenbasis hred hB hZsa
    hZ2 hZdom hZcomm hUa hUb hab hT k

/-- **The Fan-dominant ideal endpoint, stated at the genuine `tan 2Θ₀`.**

`δ N(tan 2Θ₀) ≤ 2 N(R)` in the repository's scaled form, for the constructed
tangent.  The same honest caveat as for the Ky Fan form applies: the surviving
hypothesis is the attainment clause, not a hypothesis about `A` alone. -/
theorem mem_and_gauge_le_unboundedReflectionTangent
    (N : KyFanDominantIdealFamily (𝕜 := ℂ))
    (hred : TauCeti.LinearPMap.ReducesSubspace A U) (hB : TauCeti.IsOddFor U B)
    (hZsa : IsSelfAdjoint Z) (hZ2 : Z * Z = 1)
    (hZdom : TauCeti.LinearPMap.MapsDomainTo A A Z)
    (hZcomm : ∀ x : A.domain,
      A ⟨Z (x : H), hZdom x⟩ + B (Z (x : H)) = Z (A x) + Z (B (x : H)))
    (hUa : ∀ x : A.domain, (x : H) ∈ U →
      RCLike.re ⟪A x, (x : H)⟫_ℂ ≤ a * ‖(x : H)‖ ^ 2)
    (hUb : ∀ x : A.domain, (x : H) ∈ Uᗮ →
      b * ‖(x : H)‖ ^ 2 ≤ RCLike.re ⟪A x, (x : H)⟫_ℂ)
    (hab : a < b)
    (hT : IsCompressedDoubleAngleEigenbasis A U Z
      (unboundedReflectionTangent U Z)) (hBmem : N.Mem B) :
    N.Mem ((((b - a) / 2 : ℝ) : ℂ) • unboundedReflectionTangent U Z) ∧
      N.gauge ((((b - a) / 2 : ℝ) : ℂ) • unboundedReflectionTangent U Z) ≤
        N.gauge B :=
  mem_and_gauge_le_of_compressedDoubleAngleEigenbasis N hred hB hZsa hZ2 hZdom
    hZcomm hUa hUb hab hT hBmem

/-!
## A witness that the compressed hypothesis is strictly weaker

`isCompressedDoubleAngleEigenbasis_of_isDoubleAngleEigenbasis` shows the
compressed hypothesis is *no stronger* than the exact one.  Nothing so far shows
it is genuinely *weaker*, and a weakening that is only cosmetic would be worth
knowing about.  This section exhibits a three-dimensional model in which

* every standing hypothesis of the endpoints holds — `Z` is a self-adjoint
  involution, `B` is odd for the trial subspace, `A` is reduced by it with form
  bounds `a = 0` on `𝔛₀` and `b = 1` on `𝔛₁`, and the block system holds;
* the compressed conditions hold at a unit trial vector with `q = 2/3`;
* the **exact** relation `S² x = q² x` fails at that same vector.

The model is the reflection through the diagonal line `ℂ (e₀ + e₁ + e₂)` in
`ℂ³`, with `𝔛₀` the plane `ℂ e₂` is orthogonal to.  The compression of `S²` to
the `A`-invariant line `ℂ e₀` is the scalar `4/9`, while `S² e₀ = (4/9)(e₀+e₁)`
leaves that line.  The last theorem runs
`gap_mul_sum_tangent_le_kyFan_of_invariantSubspace` on the model, so the
unconditional endpoint is exhibited as non-vacuous on data satisfying every
hypothesis of the theorem it strengthens.
-/

namespace CompressedStrictness

/-- The ambient space of the witness. -/
abbrev Model : Type := EuclideanSpace ℂ (Fin 3)

/-- The standard unit vectors of the model. -/
def unitVector (i : Fin 3) : Model := EuclideanSpace.single i (1 : ℂ)

/-- The diagonal line the model's reflection fixes. -/
def axis : Model := unitVector 0 + unitVector 1 + unitVector 2

/-- The reducing reflection of the model: `2 P_axis - 1`, written out so that no
projection API is needed to evaluate it. -/
def reflectionZ : Model →L[ℂ] Model :=
  ((2 / 3 : ℂ) • ((innerSL ℂ axis).smulRight axis)) -
    ContinuousLinearMap.id ℂ Model

/-- The trial subspace `𝔛₀` of the model: the plane orthogonal to `e₂`. -/
def trial : Submodule ℂ Model := (ℂ ∙ unitVector 2)ᗮ

/-- Pointwise form of the model's reflection. -/
theorem reflectionZ_apply (w : Model) :
    reflectionZ w = (2 / 3 : ℂ) • (⟪axis, w⟫_ℂ • axis) - w := by
  simp [reflectionZ]

/-- The unit vectors are orthonormal. -/
theorem inner_unitVector (i j : Fin 3) :
    ⟪unitVector i, unitVector j⟫_ℂ = if i = j then 1 else 0 := by
  simp [unitVector, EuclideanSpace.inner_single_left, PiLp.single_apply]

/-- The unit vectors have norm one. -/
theorem norm_unitVector (i : Fin 3) : ‖unitVector i‖ = 1 := by
  simp [unitVector, PiLp.norm_single]

/-- The axis pairs to one with every unit vector. -/
theorem inner_axis_unitVector (i : Fin 3) : ⟪axis, unitVector i⟫_ℂ = 1 := by
  rw [axis, inner_add_left, inner_add_left, inner_unitVector, inner_unitVector,
    inner_unitVector]
  fin_cases i <;> simp

/-- The axis pairs to one with every unit vector, on the other side. -/
theorem inner_unitVector_axis (i : Fin 3) : ⟪unitVector i, axis⟫_ℂ = 1 := by
  rw [axis, inner_add_right, inner_add_right, inner_unitVector,
    inner_unitVector, inner_unitVector]
  fin_cases i <;> simp

/-- The squared length of the axis. -/
theorem inner_axis_axis : ⟪axis, axis⟫_ℂ = 3 := by
  nth_rewrite 2 [axis]
  rw [inner_add_right, inner_add_right, inner_axis_unitVector,
    inner_axis_unitVector, inner_axis_unitVector]
  norm_num

/-- The model's reflection is self-adjoint. -/
theorem isSelfAdjoint_reflectionZ : IsSelfAdjoint reflectionZ := by
  rw [ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric]
  intro x y
  show ⟪reflectionZ x, y⟫_ℂ = ⟪x, reflectionZ y⟫_ℂ
  rw [reflectionZ_apply, reflectionZ_apply, inner_sub_left, inner_sub_right,
    inner_smul_left, inner_smul_left, inner_smul_right, inner_smul_right,
    ← inner_conj_symm axis x]
  simp only [map_div₀, map_ofNat, RCLike.conj_conj]
  ring

/-- The model's reflection is an involution. -/
theorem reflectionZ_mul_self : reflectionZ * reflectionZ = 1 := by
  refine ContinuousLinearMap.ext fun w => ?_
  show reflectionZ (reflectionZ w) = w
  rw [reflectionZ_apply w, reflectionZ_apply, inner_sub_right, inner_smul_right,
    inner_smul_right, inner_axis_axis]
  module

/-- Projection onto the line the trial subspace is orthogonal to. -/
theorem starProjection_span_unitVector_two (w : Model) :
    (ℂ ∙ unitVector 2).starProjection w = ⟪unitVector 2, w⟫_ℂ • unitVector 2 := by
  rw [Submodule.starProjection_singleton, norm_unitVector]
  norm_num

/-- Projection onto the trial subspace. -/
theorem trial_starProjection (w : Model) :
    trial.starProjection w = w - ⟪unitVector 2, w⟫_ℂ • unitVector 2 := by
  simp [trial, starProjection_span_unitVector_two]

/-- Projection onto the orthogonal complement of the trial subspace. -/
theorem trial_orthogonal_starProjection (w : Model) :
    trialᗮ.starProjection w = ⟪unitVector 2, w⟫_ℂ • unitVector 2 := by
  refine Submodule.eq_starProjection_of_mem_of_inner_eq_zero ?_ ?_
  · exact Submodule.smul_mem _ _ (Submodule.le_orthogonal_orthogonal _
      (Submodule.mem_span_singleton_self _))
  · intro z hz
    have hmem : w - ⟪unitVector 2, w⟫_ℂ • unitVector 2 ∈ trialᗮᗮ := by
      rw [Submodule.orthogonal_orthogonal]
      have hzero : ⟪unitVector 2,
          w - ⟪unitVector 2, w⟫_ℂ • unitVector 2⟫_ℂ = 0 := by
        rw [inner_sub_right, inner_smul_right, inner_unitVector]
        simp
      exact (Submodule.mem_orthogonal_singleton_iff_inner_right).mpr hzero
    exact inner_eq_zero_symm.mp (hmem z hz)

/-- The orthogonal complement of the trial subspace is the third coordinate
line. -/
theorem trial_orthogonal_eq : trialᗮ = ℂ ∙ unitVector 2 :=
  Submodule.orthogonal_orthogonal _

/-- Membership in the trial subspace is a single orthogonality condition. -/
theorem mem_trial_iff (x : Model) : x ∈ trial ↔ ⟪unitVector 2, x⟫_ℂ = 0 :=
  Submodule.mem_orthogonal_singleton_iff_inner_right

/-- The third unit vector lies in the complement of the trial subspace. -/
theorem unitVector_two_mem_trial_orthogonal : unitVector 2 ∈ trialᗮ := by
  rw [trial_orthogonal_eq]
  exact Submodule.mem_span_singleton_self _

/-- The first unit vector lies in the trial subspace. -/
theorem unitVector_zero_mem_trial : unitVector 0 ∈ trial := by
  refine (mem_trial_iff _).mpr ?_
  rw [inner_unitVector]
  simp

/-- The reflection at a unit vector. -/
theorem reflectionZ_unitVector (i : Fin 3) :
    reflectionZ (unitVector i) = (2 / 3 : ℂ) • axis - unitVector i := by
  rw [reflectionZ_apply, inner_axis_unitVector, one_smul]

/-- The odd block sends `e₀` to `(2/3) e₂`. -/
theorem offDiagonalPart_unitVector_zero :
    trial.offDiagonalPart reflectionZ (unitVector 0) =
      (2 / 3 : ℂ) • unitVector 2 := by
  have hU0 : trial.starProjection (unitVector 0) = unitVector 0 := by
    rw [trial_starProjection, inner_unitVector]
    simp
  have hP0 : trialᗮ.starProjection (unitVector 0) = 0 := by
    rw [trial_orthogonal_starProjection, inner_unitVector]
    simp
  have hin : ⟪unitVector 2,
      (2 / 3 : ℂ) • axis - unitVector 0⟫_ℂ = (2 / 3 : ℂ) := by
    rw [inner_sub_right, inner_smul_right, inner_unitVector_axis,
      inner_unitVector]
    simp
  rw [Submodule.offDiagonalPart_apply, Submodule.diagonalPart_apply, hU0, hP0,
    map_zero, map_zero, reflectionZ_unitVector, trial_starProjection, hin]
  module

/-- The odd block sends `e₂` to `(2/3)(e₀ + e₁)`. -/
theorem offDiagonalPart_unitVector_two :
    trial.offDiagonalPart reflectionZ (unitVector 2) =
      (2 / 3 : ℂ) • (unitVector 0 + unitVector 1) := by
  have hU2 : trial.starProjection (unitVector 2) = 0 := by
    rw [trial_starProjection, inner_unitVector]
    simp
  have hP2 : trialᗮ.starProjection (unitVector 2) = unitVector 2 := by
    rw [trial_orthogonal_starProjection, inner_unitVector]
    simp
  have hin : ⟪unitVector 2,
      (2 / 3 : ℂ) • axis - unitVector 2⟫_ℂ = (-1 / 3 : ℂ) := by
    rw [inner_sub_right, inner_smul_right, inner_unitVector_axis,
      inner_unitVector]
    norm_num
  rw [Submodule.offDiagonalPart_apply, Submodule.diagonalPart_apply, hU2, hP2,
    map_zero, map_zero, reflectionZ_unitVector,
    trial_orthogonal_starProjection, hin, axis]
  module

/-- `S² e₀ = (4/9)(e₀ + e₁)`: the square of the odd block leaves the line
`ℂ e₀`. -/
theorem offDiagonalPart_sq_unitVector_zero :
    trial.offDiagonalPart reflectionZ
        (trial.offDiagonalPart reflectionZ (unitVector 0)) =
      (4 / 9 : ℂ) • (unitVector 0 + unitVector 1) := by
  rw [offDiagonalPart_unitVector_zero, map_smul, offDiagonalPart_unitVector_two,
    smul_smul]
  norm_num

/-- **The compressed diagonal Gram condition holds at `e₀` with `q = 2/3`.** -/
theorem inner_unitVector_zero_offDiagonalPart_sq :
    ⟪unitVector 0, trial.offDiagonalPart reflectionZ
        (trial.offDiagonalPart reflectionZ (unitVector 0))⟫_ℂ =
      ((((2 : ℝ) / 3) ^ 2 : ℝ) : ℂ) := by
  rw [offDiagonalPart_sq_unitVector_zero, inner_smul_right, inner_add_right,
    inner_unitVector, inner_unitVector]
  norm_num

/-- **The exact double-angle eigenvector relation fails at the same vector.**
This is the witness that the compressed hypothesis is a real weakening. -/
theorem not_doubleAngleEigenvector_unitVector_zero :
    trial.offDiagonalPart reflectionZ
        (trial.offDiagonalPart reflectionZ (unitVector 0)) ≠
      ((((2 : ℝ) / 3) ^ 2 : ℝ) : ℂ) • unitVector 0 := by
  rw [offDiagonalPart_sq_unitVector_zero]
  intro h
  have h1 : (4 / 9 : ℂ) • unitVector 1 = 0 := by
    have hcast : ((((2 : ℝ) / 3) ^ 2 : ℝ) : ℂ) = (4 / 9 : ℂ) := by norm_num
    rw [hcast] at h
    linear_combination (norm := module) h
  have h2 : unitVector 1 = 0 := by
    rcases smul_eq_zero.mp h1 with h3 | h3
    · exact absurd h3 (by norm_num)
    · exact h3
  have hn := norm_unitVector 1
  rw [h2] at hn
  simp at hn

/-- The unperturbed operator of the model, as a bounded map: the rank-one
projection onto `ℂ e₂`. -/
def unperturbedMap : Model →L[ℂ] Model :=
  (innerSL ℂ (unitVector 2)).smulRight (unitVector 2)

/-- The residual of the model: the off-diagonal completion that makes `A + B`
commute with the reflection. -/
def residual : Model →L[ℂ] Model :=
  -(((innerSL ℂ (unitVector 0)).smulRight (unitVector 2)) +
      ((innerSL ℂ (unitVector 1)).smulRight (unitVector 2)) +
      ((innerSL ℂ (unitVector 2)).smulRight (unitVector 0)) +
      ((innerSL ℂ (unitVector 2)).smulRight (unitVector 1)))

/-- The unperturbed operator of the model as a partial map, everywhere
defined. -/
def unperturbed : Model →ₗ.[ℂ] Model :=
  (unperturbedMap : Model →ₗ[ℂ] Model).toPMap ⊤

/-- The perturbed operator of the model. -/
def perturbed : Model →L[ℂ] Model := unperturbedMap + residual

/-- Pointwise form of the unperturbed operator. -/
theorem unperturbedMap_apply (w : Model) :
    unperturbedMap w = ⟪unitVector 2, w⟫_ℂ • unitVector 2 := rfl

/-- Pointwise form of the residual. -/
theorem residual_apply (w : Model) :
    residual w = -(⟪unitVector 0, w⟫_ℂ • unitVector 2 +
      ⟪unitVector 1, w⟫_ℂ • unitVector 2 +
      ⟪unitVector 2, w⟫_ℂ • unitVector 0 +
      ⟪unitVector 2, w⟫_ℂ • unitVector 1) := rfl

/-- The partial map agrees with the bounded one. -/
theorem unperturbed_apply (x : unperturbed.domain) :
    unperturbed x = unperturbedMap (x : Model) := rfl

/-- Pointwise form of the perturbed operator. -/
theorem perturbed_apply (w : Model) :
    perturbed w = unperturbedMap w + residual w := rfl

/-- The axis is an eigenvector of the perturbed operator, with eigenvalue
`-1`. -/
theorem perturbed_axis : perturbed axis = -axis := by
  rw [perturbed_apply, unperturbedMap_apply, residual_apply,
    inner_unitVector_axis, inner_unitVector_axis, inner_unitVector_axis, axis]
  module

/-- The perturbed operator reverses the axis in the pairing as well, which is
all that the commutation with the reflection needs. -/
theorem inner_axis_perturbed (w : Model) :
    ⟪axis, perturbed w⟫_ℂ = -⟪axis, w⟫_ℂ := by
  rw [perturbed_apply, unperturbedMap_apply, residual_apply, inner_add_right,
    inner_smul_right, inner_neg_right, inner_add_right, inner_add_right,
    inner_add_right, inner_smul_right, inner_smul_right, inner_smul_right,
    inner_smul_right, inner_axis_unitVector, inner_axis_unitVector,
    inner_axis_unitVector, axis, inner_add_left, inner_add_left]
  ring

/-- **The perturbed operator commutes with the reflection.** -/
theorem perturbed_comm_reflectionZ (w : Model) :
    perturbed (reflectionZ w) = reflectionZ (perturbed w) := by
  rw [reflectionZ_apply w, map_sub, map_smul, map_smul, perturbed_axis,
    reflectionZ_apply, inner_axis_perturbed]
  module

/-- **The trial subspace reduces the unperturbed operator.** -/
theorem reducesSubspace_unperturbed :
    TauCeti.LinearPMap.ReducesSubspace unperturbed trial := by
  refine ⟨fun _ => Submodule.mem_top, fun _ => Submodule.mem_top, ?_, ?_⟩
  · intro x hx
    rw [unperturbed_apply, unperturbedMap_apply, (mem_trial_iff _).mp hx,
      zero_smul]
    exact Submodule.zero_mem _
  · intro x _
    rw [unperturbed_apply, unperturbedMap_apply]
    exact Submodule.smul_mem _ _ unitVector_two_mem_trial_orthogonal

/-- **The residual is odd for the trial subspace.** -/
theorem isOddFor_residual : TauCeti.IsOddFor trial residual := by
  constructor
  · intro x hx
    rw [residual_apply, (mem_trial_iff _).mp hx, zero_smul, zero_smul]
    refine Submodule.neg_mem _ ?_
    simpa using Submodule.add_mem _
      (Submodule.add_mem _
        (Submodule.smul_mem _ _ unitVector_two_mem_trial_orthogonal)
        (Submodule.smul_mem _ _ unitVector_two_mem_trial_orthogonal))
      (Submodule.zero_mem _)
  · intro x hx
    rw [trial_orthogonal_eq, Submodule.mem_span_singleton] at hx
    obtain ⟨c, rfl⟩ := hx
    rw [mem_trial_iff, residual_apply]
    simp [inner_unitVector, inner_smul_right, inner_add_right, inner_neg_right]

/-- The reflection preserves the domain of the unperturbed operator. -/
theorem mapsDomainTo_reflectionZ :
    TauCeti.LinearPMap.MapsDomainTo unperturbed unperturbed reflectionZ :=
  fun _ => Submodule.mem_top

/-- **The unbounded Davis--Kahan block system holds in the model.** -/
theorem reflectionZ_comm (x : unperturbed.domain) :
    unperturbed ⟨reflectionZ (x : Model), mapsDomainTo_reflectionZ x⟩ +
        residual (reflectionZ (x : Model)) =
      reflectionZ (unperturbed x) + reflectionZ (residual (x : Model)) := by
  show unperturbedMap (reflectionZ (x : Model)) +
      residual (reflectionZ (x : Model)) =
    reflectionZ (unperturbedMap (x : Model)) +
      reflectionZ (residual (x : Model))
  rw [← map_add reflectionZ]
  exact perturbed_comm_reflectionZ (x : Model)

/-- **The form of the unperturbed operator vanishes on the trial subspace**, so
`a = 0` is admissible. -/
theorem form_le_zero_on_trial (x : unperturbed.domain) (hx : (x : Model) ∈ trial) :
    RCLike.re ⟪unperturbed x, (x : Model)⟫_ℂ ≤ (0 : ℝ) * ‖(x : Model)‖ ^ 2 := by
  rw [unperturbed_apply, unperturbedMap_apply, (mem_trial_iff _).mp hx,
    zero_smul, inner_zero_left, map_zero]
  simp

/-- **The form of the unperturbed operator is the identity form on the
complement**, so `b = 1` is admissible. -/
theorem one_le_form_on_trial_orthogonal (x : unperturbed.domain)
    (hx : (x : Model) ∈ trialᗮ) :
    (1 : ℝ) * ‖(x : Model)‖ ^ 2 ≤ RCLike.re ⟪unperturbed x, (x : Model)⟫_ℂ := by
  rw [trial_orthogonal_eq, Submodule.mem_span_singleton] at hx
  obtain ⟨c, hc⟩ := hx
  have hAx : unperturbedMap (x : Model) = (x : Model) := by
    rw [← hc, unperturbedMap_apply, inner_smul_right, inner_unitVector]
    simp
  rw [unperturbed_apply, hAx, inner_self_eq_norm_sq_to_K, ← RCLike.ofReal_pow,
    RCLike.ofReal_re, one_mul]

/-- The first unit vector is nonzero. -/
theorem unitVector_zero_ne_zero : unitVector 0 ≠ 0 := by
  intro h
  have hn := norm_unitVector 0
  rw [h] at hn
  simp at hn

/-- **The unconditional endpoint, run on the model.**

`ℂ e₀` is a one-dimensional `A`-invariant subspace of `𝔛₀ ∩ D(A)`, so
`gap_mul_sum_tangent_le_kyFan_of_invariantSubspace` applies to data satisfying
every standing hypothesis of the conditional endpoints.  Together with
`not_doubleAngleEigenvector_unitVector_zero` — which says the family the
construction produces on this very subspace is *not* an exact `sin² 2Θ`
eigenfamily — this is the demonstration that the unconditional route reaches
data the exact-eigenbasis route does not. -/
theorem gap_mul_sum_tangent_le_kyFan_on_model :
    ∃ (y : Fin 1 → unperturbed.domain) (q : Fin 1 → ℝ),
      (∀ i, ((y i : unperturbed.domain) : Model) ∈ (ℂ ∙ unitVector 0)) ∧
        (Orthonormal ℂ fun i => ((y i : unperturbed.domain) : Model)) ∧
        (∀ i, ‖trial.offDiagonalPart reflectionZ
          ((y i : unperturbed.domain) : Model)‖ ^ 2 = q i ^ 2) ∧
        (∀ i, 0 ≤ q i) ∧ (∀ i, q i < 1) ∧
        ((1 : ℝ) - 0) * ∑ i, q i / √(1 - (q i) ^ 2) ≤
          2 * kyFanApproximationGauge 1 residual := by
  refine gap_mul_sum_tangent_le_kyFan_of_invariantSubspace
    reducesSubspace_unperturbed isOddFor_residual isSelfAdjoint_reflectionZ
    reflectionZ_mul_self mapsDomainTo_reflectionZ reflectionZ_comm
    form_le_zero_on_trial one_le_form_on_trial_orthogonal (by norm_num) le_top
    (Submodule.span_le.mpr
      (Set.singleton_subset_iff.mpr unitVector_zero_mem_trial)) ?_ ?_
  · intro w hw
    rw [Submodule.mem_span_singleton] at hw
    obtain ⟨c, hc⟩ := hw
    rw [unperturbed_apply, ← hc, unperturbedMap_apply, inner_smul_right,
      inner_unitVector]
    simp
  · exact finrank_span_singleton unitVector_zero_ne_zero

end CompressedStrictness

end

end DavisKahan1970
end TauCeti
