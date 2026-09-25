/-
Copyright (c) 2026 Jon Crall, Edward Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, Edward Wang
-/
module


/-
Staged for Mathlib: additions to `Mathlib/Analysis/InnerProductSpace/` (new file
`TanTheta.lean`).

Formalized by Claude Fable 5 (claude-fable-5[1m]), plan steps G3.0 (statement
gate) and G3 (proof) of the July 2026 completion campaign.

The proof is an elementary, coordinate-free vectorization of Nakatsukasa's
argument (LAA 436 (2012), 1528–1534), discovered while planning: no CS
decomposition, no graph operators, no `cos Θ` inverse.  The tangent bound is
first proved on the complementary pair — for `u ∈ Vᗮ`, at a maximizer `u₀` of
`‖P_Z u‖` on the unit sphere of `Vᗮ`, the coercivity of the compression, the
strip bound for `T − c` on `Vᗮ`, and the residual bound combine into the
one-line chain `(e + δ)·a ≤ e·a + ρ·b` — and is then transported to the test
side by a two-line Cauchy–Schwarz duality (`‖u‖² = re ⟪x, P_Z u⟫` for
`u = x − P_V x`, `x ∈ Z`), which replaces the classical `∠(Z,V) = ∠(Zᗮ,Vᗮ)`
angle symmetry.

The Davis–Kahan tan Θ theorem: one symmetric operator, one exact invariant
subspace `V` whose complementary spectrum sits in a strip `[α, β]`, one
arbitrary test subspace `Z` of the same dimension whose compression has
spectrum at distance `≥ (β−α)/2 + δ` from the strip's midpoint; conclusion
`tan ∠(Z, V) ≤ ‖residual‖ / δ`, stated per test vector so that the tangent's
pole never appears.
**Read this before staging it for Mathlib: the repository proves the same theorem without
`[FiniteDimensional 𝕜 E]`.**  `TauCeti.DavisKahanExt.tan_theta_le'` in
`DavisKahan/TanTheta/Vector.lean` has a statement identical to `tan_theta_le` below,
hypothesis for hypothesis and conclusion for conclusion, over a complete space with no
dimension assumption.  Its proof replaces the maximizer used here — which is where finite
dimensionality enters, through compactness of the unit sphere of `Vᗮ` — with the operator
norm of the compressed projection `P_Z|_{Vᗮ}` and an approximate-supremum limit.

**So the module to submit is that one, not this one.**  Proposing the finite-dimensional
form while the dimension-free form is proved two directories away is a weaker contribution
and an obvious review finding.

This file is kept deliberately, and not as a duplicate: the argument below is a different
one, elementary and coordinate-free, and
`DavisKahan/Alternative/FiniteDimensional/API/ClassicalProseLike.lean` consumes it on
purpose, the way the rest of `Alternative/` keeps a second presentation of a result.  What
was missing was this paragraph — the two files shared three statements and only one of them
named the other.

To be re-authored per Mathlib's AI-contribution policy at PR time.
-/

public import LeanPool.DavisKahan.ForTauCeti.Analysis.InnerProductSpace.PrincipalAngles
public import LeanPool.DavisKahan.ForTauCeti.Analysis.InnerProductSpace.DoubleAngle.Vector
public import LeanPool.DavisKahan.ForTauCeti.Analysis.InnerProductSpace.Sylvester.Bound
public import LeanPool.DavisKahan.ForTauCeti.Analysis.InnerProductSpace.ReducingSubspace
public import LeanPool.DavisKahan.ForTauCeti.Analysis.InnerProductSpace.Projection.Geometry

/-! # The Davis–Kahan tan Θ theorem (gated statement)

## Statement cross-check (statement-first gate, plan step G3.0)

The tan Θ theorem is recorded in finite-dimensional, matrix-precise form in
A. K. Motovilov, *Comment on 'The tan θ theorem with relaxed conditions', by
Y. Nakatsukasa* (arXiv:1204.4441), Propositions 1 and 4, which we quote:

*Proposition 1 (KMM 2005, Thm 2).*  Let the Hermitian `L = [[A₁, Bᴴ], [B, A₂]]`
be block-partitioned with `A₁ ∈ ℂᵏˣᵏ`.  Let `spec(A₁) ⊆ (−∞, α−δ] ∪ [β+δ, ∞)`
with `α ≤ β`, `δ > 0`.  Let `L₁, L₂` be complementary orthogonal reducing
subspaces of `L` with `dim L₁ = k` and `spec(L|_{L₂}) ⊆ [α, β]`, and let `𝒜₁`
be the first-`k`-coordinates subspace.  Then `tan ∠(𝒜₁, L₁) ≤ ‖B‖/δ`.

*Proposition 4 (Nakatsukasa's Theorem 1; residual form, equivalent).*  For a
Hermitian `A`, orthonormal `Q₁ ∈ ℂⁿˣᵏ`, `A₁ := Q₁ᴴAQ₁`,
`R := AQ₁ − Q₁A₁`; if `spec(A₁) ⊆ (−∞, α−δ] ∪ [β+δ, ∞)` and the complementary
exact spectrum `spec(Λ₂) ⊆ [α, β]`, then `tan ∠(ran Q₁, ran X₁) ≤ ‖R‖/δ`.

Points the gate had to settle, and how the sources settle them:

* **`cos Θ` invertibility (`∠ < π/2`) is a *conclusion*, not a hypothesis**:
  Motovilov's Lemma 3 shows `𝒜₁ ∩ L₂ = 𝒜₂ ∩ L₁ = {0}` follows from the
  spectral hypotheses in finite dimension (via
  `‖(L − c)y‖ ≥ ((β−α)/2 + δ)‖y‖` on `𝒜₁` against `≤ (β−α)/2 ‖y‖` on `L₂`).
  Our per-vector encoding absorbs this: `δ ‖x − P_V x‖ ≤ ρ ‖P_V x‖` for
  `x ∈ Z` forces `P_V x = 0 → x = 0`, so no inverse or tangent operator is
  ever formed and the pole never appears.
* **Two-sided outside condition**: the test compression's spectrum may sit on
  *both* sides of the strip (Nakatsukasa's relaxation); as Motovilov shows it
  is already contained in KMM 2005 for the spectral norm.  We adopt it: the
  hypothesis is coercivity of `A₁ − c` at distance `(β−α)/2 + δ` from the
  midpoint `c := (α+β)/2`, not a one-sided bound.
* **Which subspace is exact**: `V` (the `L₁`) is exactly invariant for `T`,
  with the *complementary* spectrum confined to the strip; the test subspace
  `Z` is arbitrary of the same finite rank.  `dim Z = dim V` is essential.
* **Norms**: spectral norm (the largest principal angle).  A
  unitarily-invariant-norm version is not part of the record checked here
  and is not asserted.
* The per-vector conclusion `∀ x ∈ Z, δ ‖x − P_V x‖ ≤ ρ ‖P_V x‖` is
  equivalent to `tan θ_max ≤ ρ/δ` (for equal dimensions,
  `sin θ_max = max_{x ∈ Z, unit} ‖(1 − P_V)x‖` and the vectorwise
  angle-to-`V` is maximized at `θ_max`); `ρ` bounds the residual columnwise,
  `‖T x − P_Z (T x)‖ ≤ ρ ‖x‖` on `Z`, which is `‖B‖ ≤ ρ` in Proposition 1's
  block notation and `‖R‖ ≤ ρ` in Proposition 4's.

## Main results

* `TauCeti.tan_theta_le` (plan step G3): the tan Θ theorem in the
  per-vector, pole-free form.
* `TauCeti.norm_map_sub_midpoint_smul_le`: a symmetric operator whose form
  on an invariant subspace lies in `[α, β]` moves vectors of that subspace at
  most `(β − α)/2` per unit norm away from the midpoint scaling.
* `TauCeti.norm_starProjection_map_le_of_mem_orthogonal`: the columnwise
  residual bound on `Z` transfers to the adjoint block, `‖P_Z (T w)‖ ≤ ρ ‖w‖`
  for `w ⊥ Z`.

## References

* C. Davis and W. M. Kahan, *The rotation of eigenvectors by a
  perturbation. III*, SIAM J. Numer. Anal. 7 (1970), 1–46.
* V. Kostrykin, K. A. Makarov, A. K. Motovilov, *On the existence of solutions
  to the operator Riccati equation and the tan θ theorem*, Integr. Equ. Oper.
  Theory 51 (2005), 121–140.
* Y. Nakatsukasa, *The tan θ theorem with relaxed conditions*, Linear Algebra
  Appl. 436 (2012), 1528–1534.
* A. K. Motovilov, *Comment on 'The tan θ theorem with relaxed conditions'*,
  arXiv:1204.4441.
-/

@[expose] public section

namespace TauCeti

open TauCeti
open scoped InnerProductSpace
open Module (finrank)

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  [FiniteDimensional 𝕜 E] [CompleteSpace E] {T : E →ₗ[𝕜] E}

omit [CompleteSpace E] in
/-- **The strip bound on an invariant subspace.**  If the quadratic form of the
symmetric operator `T` lies in `[α, β]` on a `T`-invariant subspace `W`, then on
`W` the operator `T − (α+β)/2` has norm at most the strip half-width:
`‖T u − ((α+β)/2) • u‖ ≤ (β−α)/2 · ‖u‖` for `u ∈ W`.

The subspace-restricted statement is transported to the full space by the
sandwich `C := P_W ∘ (T − (α+β)/2) ∘ P_W`, which is symmetric with
`|re ⟪C x, x⟫| ≤ (β−α)/2 · ‖x‖²` everywhere, hence has norm at most `(β−α)/2`;
on `W` it agrees with `T − (α+β)/2` by invariance. -/
theorem norm_map_sub_midpoint_smul_le (hT : T.IsSymmetric) {W : Submodule 𝕜 E}
    [W.HasOrthogonalProjection] (hW : ∀ x ∈ W, T x ∈ W) {α β : ℝ} (hαβ : α ≤ β)
    (ha : ∀ x ∈ W, α * ‖x‖ ^ 2 ≤ RCLike.re ⟪T x, x⟫_𝕜)
    (hb : ∀ x ∈ W, RCLike.re ⟪T x, x⟫_𝕜 ≤ β * ‖x‖ ^ 2)
    {u : E} (hu : u ∈ W) :
    ‖T u - (((α + β) / 2 : ℝ) : 𝕜) • u‖ ≤ (β - α) / 2 * ‖u‖ := by
  have he0 : (0 : ℝ) ≤ (β - α) / 2 := by linarith
  set S : E →ₗ[𝕜] E := T - (((α + β) / 2 : ℝ) : 𝕜) • LinearMap.id with hS
  have hSapp : ∀ y, S y = T y - (((α + β) / 2 : ℝ) : 𝕜) • y := fun y => rfl
  have hSsym : S.IsSymmetric := hT.sub fun x y => by
    simp only [LinearMap.smul_apply, LinearMap.id_apply, inner_smul_left, inner_smul_right,
      RCLike.conj_ofReal]
  have hSW : ∀ y ∈ W, S y ∈ W := fun y hy => by
    rw [hSapp]
    exact Submodule.sub_mem _ (hW y hy) (W.smul_mem _ hy)
  set C : E →L[𝕜] E :=
    W.starProjection ∘L S.toContinuousLinearMap ∘L W.starProjection with hC
  have hCapp : ∀ y, C y = W.starProjection (S (W.starProjection y)) := fun y => rfl
  have hCsym : (C : E →ₗ[𝕜] E).IsSymmetric := fun x y => by
    change ⟪W.starProjection (S (W.starProjection x)), y⟫_𝕜
        = ⟪x, W.starProjection (S (W.starProjection y))⟫_𝕜
    rw [W.inner_starProjection_left_eq_right, hSsym, ← W.inner_starProjection_left_eq_right]
  have hform : ∀ y, |RCLike.re ⟪C y, y⟫_𝕜| ≤ (β - α) / 2 * ‖y‖ ^ 2 := by
    intro y
    have hmove : ⟪C y, y⟫_𝕜 = ⟪S (W.starProjection y), W.starProjection y⟫_𝕜 := by
      rw [hCapp, W.inner_starProjection_left_eq_right]
    have hval : RCLike.re ⟪S (W.starProjection y), W.starProjection y⟫_𝕜
        = RCLike.re ⟪T (W.starProjection y), W.starProjection y⟫_𝕜
          - (α + β) / 2 * ‖W.starProjection y‖ ^ 2 := by
      simp only [hSapp, inner_sub_left, inner_smul_left, RCLike.conj_ofReal, map_sub,
        RCLike.re_ofReal_mul, inner_self_eq_norm_sq]
    have hPy := W.starProjection_apply_mem y
    have h1 := ha _ hPy
    have h2 := hb _ hPy
    have h3 : ‖W.starProjection y‖ ^ 2 ≤ ‖y‖ ^ 2 :=
      pow_le_pow_left₀ (norm_nonneg _) (W.norm_starProjection_apply_le y) 2
    have h4 : (β - α) / 2 * ‖W.starProjection y‖ ^ 2 ≤ (β - α) / 2 * ‖y‖ ^ 2 :=
      mul_le_mul_of_nonneg_left h3 he0
    rw [hmove, hval, abs_le]
    constructor <;> nlinarith [h1, h2, h4]
  have hnorm : ‖C‖ ≤ (β - α) / 2 :=
    ContinuousLinearMap.norm_le_of_abs_re_inner_map_self_le hCsym he0 hform
  have hCu : C u = S u := by
    rw [hCapp, Submodule.starProjection_eq_self_iff.mpr hu,
      Submodule.starProjection_eq_self_iff.mpr (hSW u hu)]
  calc ‖T u - (((α + β) / 2 : ℝ) : 𝕜) • u‖ = ‖C u‖ := by rw [hCu, hSapp]
    _ ≤ ‖C‖ * ‖u‖ := C.le_opNorm u
    _ ≤ (β - α) / 2 * ‖u‖ := by gcongr

omit [FiniteDimensional 𝕜 E] [CompleteSpace E] in
/-- **The residual bound transfers to the adjoint block.**  If
`‖T x − P_Z (T x)‖ ≤ ρ ‖x‖` for every `x ∈ Z` (a columnwise bound on the
off-diagonal block of the symmetric `T` with respect to `Z ⊕ Zᗮ`), then the
mirrored block obeys the same bound: `‖P_Z (T w)‖ ≤ ρ ‖w‖` for `w ∈ Zᗮ`.

Elementary: `‖P_Z (T w)‖² = re ⟪w, T z − P_Z (T z)⟫` for `z := P_Z (T w)`, by
symmetry of `T` and self-adjointness of the projection, and Cauchy–Schwarz
finishes. -/
theorem norm_starProjection_map_le_of_mem_orthogonal (hT : T.IsSymmetric)
    {Z : Submodule 𝕜 E} [Z.HasOrthogonalProjection] {ρ : ℝ} (hρ0 : 0 ≤ ρ)
    (hρ : ∀ x ∈ Z, ‖T x - Z.starProjection (T x)‖ ≤ ρ * ‖x‖)
    {w : E} (hw : w ∈ Zᗮ) : ‖Z.starProjection (T w)‖ ≤ ρ * ‖w‖ :=
  _root_.LinearMap.norm_starProjection_apply_le_of_mem_orthogonal hT hρ0 hρ hw

omit [CompleteSpace E] in
/-- **The Davis–Kahan tan Θ theorem (plan step G3).**  `T` symmetric; `V` a
`T`-invariant subspace whose complementary form sits in the strip `[α, β]`;
`Z` a test subspace with `dim Z = dim V` whose compression `A₁ := P_Z T|_Z`
is coercive at distance `(β−α)/2 + δ` from the strip's midpoint; `ρ` a
columnwise bound on the residual `T x − P_Z (T x)` over `Z`.  Then every test
vector satisfies `δ ‖x − P_V x‖ ≤ ρ ‖P_V x‖` — the per-vector, pole-free form
of `tan ∠(Z, V) ≤ ρ/δ`, which in particular forces `Z ∩ Vᗮ = 0` (Motovilov's
Lemma 3).  See the module docstring for the literature cross-check.

No dimension comparison between `Z` and `V` is assumed (matching
Nakatsukasa's generalized Theorem 2, where `dim Z ≤ dim V` suffices — an
inequality the remaining hypotheses force anyway, since the conclusion
forces `Z ∩ Vᗮ = 0`).  The classical record of the theorem carries an
equal-rank hypothesis, but the proof never consumes one.

Proof: on `Vᗮ`, at a maximizer `u₀` of `u ↦ ‖P_Z u‖` on the unit sphere with
`a := ‖P_Z u₀‖`, `b := ‖u₀ − P_Z u₀‖`, the identity
`(M − c)(P_Z u₀) = P_Z ((T − c) u₀) − P_Z (T (u₀ − P_Z u₀))` gives
`(e + δ) a ≤ e a + ρ b` — coercivity on the left; the strip bound
`norm_map_sub_midpoint_smul_le` and maximality for the first term, the adjoint
residual bound `norm_starProjection_map_le_of_mem_orthogonal` for the second —
so `δ a ≤ ρ b`, and by maximality `δ ‖P_Z u‖ ≤ ρ ‖u − P_Z u‖` for every
`u ∈ Vᗮ`.  For `x ∈ Z` the conclusion follows from this at `u := x − P_V x`
via `‖u‖² = re ⟪x, P_Z u⟫ ≤ ‖x‖ ‖P_Z u‖` (Cauchy–Schwarz duality) and two
Pythagoras identities. -/
theorem tan_theta_le (hT : T.IsSymmetric)
    {Z V : Submodule 𝕜 E} [Z.HasOrthogonalProjection] [V.HasOrthogonalProjection]
    (hVinv : ∀ x ∈ V, T x ∈ V)
    {α β δ ρ : ℝ} (hαβ : α ≤ β) (hδ : 0 < δ) (hρ0 : 0 ≤ ρ)
    (hZ : ∀ x ∈ Z, ((β - α) / 2 + δ) * ‖x‖
      ≤ ‖Z.starProjection (T x) - (((α + β) / 2 : ℝ) : 𝕜) • x‖)
    (hVa : ∀ x ∈ Vᗮ, α * ‖x‖ ^ 2 ≤ RCLike.re ⟪T x, x⟫_𝕜)
    (hVb : ∀ x ∈ Vᗮ, RCLike.re ⟪T x, x⟫_𝕜 ≤ β * ‖x‖ ^ 2)
    (hρ : ∀ x ∈ Z, ‖T x - Z.starProjection (T x)‖ ≤ ρ * ‖x‖) :
    ∀ x ∈ Z, δ * ‖x - V.starProjection x‖ ≤ ρ * ‖V.starProjection x‖ := by
  -- `Vᗮ` is `T`-invariant, and `T − c` contracts it to the strip half-width.
  have hVperp : ∀ u ∈ Vᗮ, T u ∈ Vᗮ := fun u hu =>
    map_mem_orthogonal_of_forall_map_mem hT hVinv hu
  have hstrip : ∀ u ∈ Vᗮ, ‖T u - (((α + β) / 2 : ℝ) : 𝕜) • u‖ ≤ (β - α) / 2 * ‖u‖ :=
    fun u hu => norm_map_sub_midpoint_smul_le hT hVperp hαβ hVa hVb hu
  -- The complementary-side tangent bound: `δ ‖P_Z u‖ ≤ ρ ‖u − P_Z u‖` on `Vᗮ`.
  have hkey : ∀ u ∈ Vᗮ, δ * ‖Z.starProjection u‖ ≤ ρ * ‖u - Z.starProjection u‖ := by
    intro u huV
    rcases eq_or_ne u 0 with rfl | hu0
    · simp
    -- a maximizer of the sine on the unit sphere of `Vᗮ`
    have : ProperSpace E := FiniteDimensional.proper_rclike 𝕜 E
    have hKc : IsCompact (Metric.sphere (0 : E) 1 ∩ (Vᗮ : Set E)) :=
      (isCompact_sphere 0 1).inter_right Vᗮ.closed_of_finiteDimensional
    have hKne : (Metric.sphere (0 : E) 1 ∩ (Vᗮ : Set E)).Nonempty := by
      refine ⟨((‖u‖⁻¹ : ℝ) : 𝕜) • u, ?_, Vᗮ.smul_mem _ huV⟩
      rw [mem_sphere_zero_iff_norm, norm_smul, RCLike.norm_ofReal,
        abs_of_nonneg (by positivity), inv_mul_cancel₀ (norm_ne_zero_iff.mpr hu0)]
    obtain ⟨u₀, hu₀K, hu₀max⟩ := hKc.exists_isMaxOn hKne
      Z.starProjection.continuous.norm.continuousOn
    obtain ⟨hu₀s, hu₀V'⟩ := hu₀K
    have hu₀V : u₀ ∈ Vᗮ := hu₀V'
    have hu₀n : ‖u₀‖ = 1 := mem_sphere_zero_iff_norm.mp hu₀s
    -- maximality, scaled off the sphere
    have hmax : ∀ v ∈ Vᗮ, ‖Z.starProjection v‖ ≤ ‖Z.starProjection u₀‖ * ‖v‖ := by
      intro v hv
      rcases eq_or_ne v 0 with rfl | hv0
      · simp
      · have hvK : ((‖v‖⁻¹ : ℝ) : 𝕜) • v ∈ Metric.sphere (0 : E) 1 ∩ (Vᗮ : Set E) := by
          refine ⟨?_, Vᗮ.smul_mem _ hv⟩
          rw [mem_sphere_zero_iff_norm, norm_smul, RCLike.norm_ofReal,
            abs_of_nonneg (by positivity), inv_mul_cancel₀ (norm_ne_zero_iff.mpr hv0)]
        have h : ‖Z.starProjection (((‖v‖⁻¹ : ℝ) : 𝕜) • v)‖ ≤ ‖Z.starProjection u₀‖ :=
          hu₀max hvK
        rw [map_smul, norm_smul, RCLike.norm_ofReal,
          abs_of_nonneg (inv_nonneg.mpr (norm_nonneg v))] at h
        calc ‖Z.starProjection v‖ = ‖v‖ * (‖v‖⁻¹ * ‖Z.starProjection v‖) := by
              field_simp
          _ ≤ ‖v‖ * ‖Z.starProjection u₀‖ := by
              have hv0' : (0 : ℝ) ≤ ‖v‖ := norm_nonneg v
              exact mul_le_mul_of_nonneg_left h hv0'
          _ = ‖Z.starProjection u₀‖ * ‖v‖ := mul_comm _ _
    -- the chain at the maximizer
    have hpy₀ : ‖Z.starProjection u₀‖ ^ 2 + ‖u₀ - Z.starProjection u₀‖ ^ 2 = 1 := by
      rw [norm_sq_starProjection_add_norm_sq_sub Z u₀, hu₀n, one_pow]
    have hchain := hZ (Z.starProjection u₀) (Z.starProjection_apply_mem u₀)
    have hsplit : Z.starProjection (T (Z.starProjection u₀))
          - (((α + β) / 2 : ℝ) : 𝕜) • Z.starProjection u₀
        = Z.starProjection (T u₀ - (((α + β) / 2 : ℝ) : 𝕜) • u₀)
          - Z.starProjection (T (u₀ - Z.starProjection u₀)) := by
      simp only [map_sub, map_smul]
      abel
    have h2 : ‖Z.starProjection (T u₀ - (((α + β) / 2 : ℝ) : 𝕜) • u₀)‖
        ≤ ‖Z.starProjection u₀‖ * ((β - α) / 2) := by
      have hin : T u₀ - (((α + β) / 2 : ℝ) : 𝕜) • u₀ ∈ Vᗮ :=
        Submodule.sub_mem _ (hVperp u₀ hu₀V) (Vᗮ.smul_mem _ hu₀V)
      calc ‖Z.starProjection (T u₀ - (((α + β) / 2 : ℝ) : 𝕜) • u₀)‖
          ≤ ‖Z.starProjection u₀‖ * ‖T u₀ - (((α + β) / 2 : ℝ) : 𝕜) • u₀‖ := hmax _ hin
        _ ≤ ‖Z.starProjection u₀‖ * ((β - α) / 2 * ‖u₀‖) := by
            have := hstrip u₀ hu₀V
            gcongr
        _ = ‖Z.starProjection u₀‖ * ((β - α) / 2) := by rw [hu₀n, mul_one]
    have h3 : ‖Z.starProjection (T (u₀ - Z.starProjection u₀))‖
        ≤ ρ * ‖u₀ - Z.starProjection u₀‖ :=
      norm_starProjection_map_le_of_mem_orthogonal hT hρ0 hρ
        (Z.sub_starProjection_mem_orthogonal u₀)
    have hab : δ * ‖Z.starProjection u₀‖ ≤ ρ * ‖u₀ - Z.starProjection u₀‖ := by
      have hup : ‖Z.starProjection (T (Z.starProjection u₀))
            - (((α + β) / 2 : ℝ) : 𝕜) • Z.starProjection u₀‖
          ≤ ‖Z.starProjection u₀‖ * ((β - α) / 2) + ρ * ‖u₀ - Z.starProjection u₀‖ := by
        rw [hsplit]
        exact (norm_sub_le _ _).trans (add_le_add h2 h3)
      have := hchain.trans hup
      linarith
    -- transfer to `u` by monotonicity of `t ↦ t/√(1−t²)`, kept in squares
    have hPu : ‖Z.starProjection u‖ ≤ ‖Z.starProjection u₀‖ * ‖u‖ := hmax u huV
    have hpyu : ‖Z.starProjection u‖ ^ 2 + ‖u - Z.starProjection u‖ ^ 2 = ‖u‖ ^ 2 :=
      norm_sq_starProjection_add_norm_sq_sub Z u
    have hsq : (δ * ‖Z.starProjection u‖) ^ 2 ≤ (ρ * ‖u - Z.starProjection u‖) ^ 2 := by
      have h1 : ‖Z.starProjection u‖ ^ 2 ≤ ‖Z.starProjection u₀‖ ^ 2 * ‖u‖ ^ 2 := by
        have := pow_le_pow_left₀ (norm_nonneg _) hPu 2
        calc ‖Z.starProjection u‖ ^ 2 ≤ (‖Z.starProjection u₀‖ * ‖u‖) ^ 2 := this
          _ = ‖Z.starProjection u₀‖ ^ 2 * ‖u‖ ^ 2 := by ring
      have h2 : (δ * ‖Z.starProjection u₀‖) ^ 2 ≤ (ρ * ‖u₀ - Z.starProjection u₀‖) ^ 2 :=
        pow_le_pow_left₀ (mul_nonneg hδ.le (norm_nonneg _)) hab 2
      calc (δ * ‖Z.starProjection u‖) ^ 2 = δ ^ 2 * ‖Z.starProjection u‖ ^ 2 := by ring
        _ ≤ δ ^ 2 * (‖Z.starProjection u₀‖ ^ 2 * ‖u‖ ^ 2) :=
            mul_le_mul_of_nonneg_left h1 (sq_nonneg δ)
        _ = (δ * ‖Z.starProjection u₀‖) ^ 2 * ‖u‖ ^ 2 := by ring
        _ ≤ (ρ * ‖u₀ - Z.starProjection u₀‖) ^ 2 * ‖u‖ ^ 2 :=
            mul_le_mul_of_nonneg_right h2 (sq_nonneg _)
        _ = ρ ^ 2 * ‖u₀ - Z.starProjection u₀‖ ^ 2 * ‖u‖ ^ 2 := by ring
        _ = ρ ^ 2 * ‖u‖ ^ 2 - ρ ^ 2 * (‖Z.starProjection u₀‖ ^ 2 * ‖u‖ ^ 2) := by
            rw [show ‖u₀ - Z.starProjection u₀‖ ^ 2 = 1 - ‖Z.starProjection u₀‖ ^ 2 by
              linarith [hpy₀]]
            ring
        _ ≤ ρ ^ 2 * ‖u‖ ^ 2 - ρ ^ 2 * ‖Z.starProjection u‖ ^ 2 := by
            have := mul_le_mul_of_nonneg_left h1 (sq_nonneg ρ)
            linarith
        _ = (ρ * ‖u - Z.starProjection u‖) ^ 2 := by
            rw [show (ρ * ‖u - Z.starProjection u‖) ^ 2
                = ρ ^ 2 * ‖u - Z.starProjection u‖ ^ 2 from by ring,
              show ‖u - Z.starProjection u‖ ^ 2 = ‖u‖ ^ 2 - ‖Z.starProjection u‖ ^ 2 by
                linarith [hpyu]]
            ring
    have := Real.sqrt_le_sqrt hsq
    rwa [Real.sqrt_sq (mul_nonneg hδ.le (norm_nonneg _)),
      Real.sqrt_sq (mul_nonneg hρ0 (norm_nonneg _))] at this
  -- Cauchy–Schwarz duality back to the test side.
  intro x hxZ
  have huV : x - V.starProjection x ∈ Vᗮ := V.sub_starProjection_mem_orthogonal x
  rcases eq_or_ne (x - V.starProjection x) 0 with h0 | h0
  · rw [h0, norm_zero, mul_zero]
    positivity
  · have hCS : ‖x - V.starProjection x‖ ^ 2
        ≤ ‖x‖ * ‖Z.starProjection (x - V.starProjection x)‖ := by
      have e1 : ⟪x - V.starProjection x, x - V.starProjection x⟫_𝕜
          = ⟪x, x - V.starProjection x⟫_𝕜 := by
        conv_lhs => rw [inner_sub_left]
        rw [Submodule.inner_right_of_mem_orthogonal (V.starProjection_apply_mem x) huV,
          sub_zero]
      have e2 : ⟪x, x - V.starProjection x⟫_𝕜
          = ⟪x, Z.starProjection (x - V.starProjection x)⟫_𝕜 := by
        rw [← Z.inner_starProjection_left_eq_right,
          Submodule.starProjection_eq_self_iff.mpr hxZ]
      calc ‖x - V.starProjection x‖ ^ 2
          = RCLike.re ⟪x - V.starProjection x, x - V.starProjection x⟫_𝕜 :=
            (inner_self_eq_norm_sq _).symm
        _ = RCLike.re ⟪x, Z.starProjection (x - V.starProjection x)⟫_𝕜 := by rw [e1, e2]
        _ ≤ ‖⟪x, Z.starProjection (x - V.starProjection x)⟫_𝕜‖ := RCLike.re_le_norm _
        _ ≤ ‖x‖ * ‖Z.starProjection (x - V.starProjection x)‖ := norm_inner_le_norm _ _
    have hk := hkey _ huV
    have hpyZu : ‖Z.starProjection (x - V.starProjection x)‖ ^ 2
          + ‖(x - V.starProjection x) - Z.starProjection (x - V.starProjection x)‖ ^ 2
        = ‖x - V.starProjection x‖ ^ 2 :=
      norm_sq_starProjection_add_norm_sq_sub Z _
    have hpyVx : ‖V.starProjection x‖ ^ 2 + ‖x - V.starProjection x‖ ^ 2 = ‖x‖ ^ 2 :=
      norm_sq_starProjection_add_norm_sq_sub V x
    have hq : (0 : ℝ) < ‖x - V.starProjection x‖ := norm_pos_iff.mpr h0
    set q : ℝ := ‖x - V.starProjection x‖ with hqdef
    set pz : ℝ := ‖Z.starProjection (x - V.starProjection x)‖ with hpzdef
    set pw : ℝ := ‖(x - V.starProjection x) - Z.starProjection (x - V.starProjection x)‖
      with hpwdef
    set pv : ℝ := ‖V.starProjection x‖ with hpvdef
    have hfin : (δ * q) ^ 2 ≤ (ρ * pv) ^ 2 := by
      have hA : (δ * pz) ^ 2 ≤ (ρ * pw) ^ 2 :=
        pow_le_pow_left₀ (mul_nonneg hδ.le (norm_nonneg _)) hk 2
      have hB : (q ^ 2) ^ 2 ≤ (‖x‖ * pz) ^ 2 :=
        pow_le_pow_left₀ (sq_nonneg _) hCS 2
      have hC : δ ^ 2 * (q ^ 2) ^ 2 ≤ ρ ^ 2 * pv ^ 2 * (q ^ 2) := by
        calc δ ^ 2 * (q ^ 2) ^ 2
            ≤ δ ^ 2 * (‖x‖ * pz) ^ 2 := mul_le_mul_of_nonneg_left hB (sq_nonneg δ)
          _ = ‖x‖ ^ 2 * (δ * pz) ^ 2 := by ring
          _ ≤ ‖x‖ ^ 2 * (ρ * pw) ^ 2 := mul_le_mul_of_nonneg_left hA (sq_nonneg _)
          _ = ρ ^ 2 * ‖x‖ ^ 2 * pw ^ 2 := by ring
          _ = ρ ^ 2 * ‖x‖ ^ 2 * q ^ 2 - ρ ^ 2 * (‖x‖ ^ 2 * pz ^ 2) := by
              rw [show pw ^ 2 = q ^ 2 - pz ^ 2 by linarith [hpyZu]]
              ring
          _ ≤ ρ ^ 2 * ‖x‖ ^ 2 * q ^ 2 - ρ ^ 2 * (q ^ 2) ^ 2 := by
              have h5 : ρ ^ 2 * (q ^ 2) ^ 2 ≤ ρ ^ 2 * (‖x‖ * pz) ^ 2 :=
                mul_le_mul_of_nonneg_left hB (sq_nonneg ρ)
              have h6 : ρ ^ 2 * (‖x‖ * pz) ^ 2 = ρ ^ 2 * (‖x‖ ^ 2 * pz ^ 2) := by ring
              linarith
          _ = ρ ^ 2 * (‖x‖ ^ 2 - q ^ 2) * q ^ 2 := by ring
          _ = ρ ^ 2 * pv ^ 2 * q ^ 2 := by
              rw [show ‖x‖ ^ 2 - q ^ 2 = pv ^ 2 by linarith [hpyVx]]
      have hq2 : (0 : ℝ) < q ^ 2 := by positivity
      nlinarith [hC, hq2]
    have := Real.sqrt_le_sqrt hfin
    rwa [Real.sqrt_sq (mul_nonneg hδ.le (norm_nonneg _)),
      Real.sqrt_sq (mul_nonneg hρ0 (norm_nonneg _))] at this

end TauCeti
