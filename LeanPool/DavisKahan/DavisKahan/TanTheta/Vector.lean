/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, Claude Fable 5
-/
module

public import LeanPool.DavisKahan.ForTauCeti.Analysis.InnerProductSpace.Sylvester.Bound
public import LeanPool.DavisKahan.ForTauCeti.Analysis.InnerProductSpace.ReducingSubspace
public import LeanPool.DavisKahan.ForTauCeti.Analysis.InnerProductSpace.DoubleAngle.Vector
public import Mathlib.Analysis.InnerProductSpace.Symmetric
public import Mathlib.Analysis.InnerProductSpace.Projection.Basic
public import Mathlib.Analysis.Normed.Operator.NNNorm
public import LeanPool.DavisKahan.ForTauCeti.Analysis.InnerProductSpace.Projection.Geometry
public import LeanPool.DavisKahan.ForTauCeti.Analysis.InnerProductSpace.BoundedOperator.Projector
public import LeanPool.DavisKahan.ForTauCeti.Analysis.InnerProductSpace.Projection.Blocks
public import LeanPool.DavisKahan.DavisKahan.BoundedOperator.Problem

/-!
# The Davis--Kahan `tan Θ` theorem on infinite-dimensional Hilbert spaces

The per-vector, pole-free `tan Θ` theorem: `T` symmetric on a complete
space; `V` a `T`-invariant subspace whose complementary quadratic form sits
in the strip `[α, β]`; `Z` a test subspace whose compression is coercive at
distance `(β-α)/2 + δ` from the strip's midpoint; `ρ` a columnwise residual
bound over `Z`.  Then `δ ‖x - P_V x‖ ≤ ρ ‖P_V x‖` for every `x ∈ Z` — the
per-vector form of `tan ∠(Z, V) ≤ ρ/δ`, forcing `Z ∩ Vᗮ = 0`.

This is the infinite-dimensional form of the finite-dimensional theorem in
`DavisKahan.FiniteDimensional.TanTheta.Vector`.  The finite proof evaluates
the key complementary-side inequality at a maximizer of the sine on the
compact unit sphere of `Vᗮ`; here the maximizer is replaced by the operator
norm `κ` of the compressed projection `P_Z|_{Vᗮ}` together with an
approximate-supremum limit: near-maximizing vectors give
`(e + δ)(κ - ε) ≤ κ e + ρ √(1 - (κ - ε)²)` for every small `ε > 0`, and
continuity in `ε` yields the exact bound `δ κ ≤ ρ √(1 - κ²)`, after which
the transfer to arbitrary vectors and the Cauchy--Schwarz duality back to
the test side proceed exactly as in finite dimensions.

**This is the version to submit upstream.**  The finite file is the one marked *staged for
Mathlib*, but its statement is this one plus `[FiniteDimensional 𝕜 E]`; that file now says
so too.  Both are kept — the finite proof is a different argument with its own consumer in
`Alternative/` — and the primes on the names here are the only thing distinguishing the two
sets of declarations, which is why a name-based duplicate check never saw the pair.
-/

@[expose] public section

namespace TauCeti

open TauCeti
namespace DavisKahanExt

open DavisKahan

open scoped InnerProductSpace

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E]
  [InnerProductSpace 𝕜 E] [CompleteSpace E] {T : E →ₗ[𝕜] E}

/-- **The strip bound on an invariant subspace.**  If the quadratic form of
the symmetric operator `T` lies in `[α, β]` on a `T`-invariant subspace
`W`, then on `W` the operator `T − (α+β)/2` has norm at most the strip
half-width. -/
theorem norm_map_sub_midpoint_smul_le' (hT : T.IsSymmetric)
    {W : Submodule 𝕜 E}
    [W.HasOrthogonalProjection] (hW : ∀ x ∈ W, T x ∈ W) {α β : ℝ}
    (hαβ : α ≤ β)
    (ha : ∀ x ∈ W, α * ‖x‖ ^ 2 ≤ RCLike.re ⟪T x, x⟫_𝕜)
    (hb : ∀ x ∈ W, RCLike.re ⟪T x, x⟫_𝕜 ≤ β * ‖x‖ ^ 2)
    {u : E} (hu : u ∈ W) :
    ‖T u - (((α + β) / 2 : ℝ) : 𝕜) • u‖ ≤ (β - α) / 2 * ‖u‖ := by
  have he0 : (0 : ℝ) ≤ (β - α) / 2 := by linarith
  set S : E →ₗ[𝕜] E := T - (((α + β) / 2 : ℝ) : 𝕜) • LinearMap.id with hS
  have hSapp : ∀ y, S y = T y - (((α + β) / 2 : ℝ) : 𝕜) • y := fun y => rfl
  have hSsym : S.IsSymmetric := hT.sub fun x y => by
    simp only [LinearMap.smul_apply, LinearMap.id_apply, inner_smul_left,
      inner_smul_right, RCLike.conj_ofReal]
  have hSW : ∀ y ∈ W, S y ∈ W := fun y hy => by
    rw [hSapp]
    exact Submodule.sub_mem _ (hW y hy) (W.smul_mem _ hy)
  set Scont : E →L[𝕜] E := ⟨S, hSsym.continuous⟩ with hScont
  set C : E →L[𝕜] E := W.starProjection ∘L Scont ∘L W.starProjection with hC
  have hCapp : ∀ y, C y = W.starProjection (S (W.starProjection y)) :=
    fun y => rfl
  have hCsym : (C : E →ₗ[𝕜] E).IsSymmetric := fun x y => by
    change ⟪W.starProjection (S (W.starProjection x)), y⟫_𝕜
        = ⟪x, W.starProjection (S (W.starProjection y))⟫_𝕜
    rw [W.inner_starProjection_left_eq_right, hSsym,
      ← W.inner_starProjection_left_eq_right]
  have hform : ∀ y, |RCLike.re ⟪C y, y⟫_𝕜| ≤ (β - α) / 2 * ‖y‖ ^ 2 := by
    intro y
    have hmove : ⟪C y, y⟫_𝕜
        = ⟪S (W.starProjection y), W.starProjection y⟫_𝕜 := by
      rw [hCapp, W.inner_starProjection_left_eq_right]
    have hval : RCLike.re ⟪S (W.starProjection y), W.starProjection y⟫_𝕜
        = RCLike.re ⟪T (W.starProjection y), W.starProjection y⟫_𝕜
          - (α + β) / 2 * ‖W.starProjection y‖ ^ 2 := by
      simp only [hSapp, inner_sub_left, inner_smul_left, RCLike.conj_ofReal,
        map_sub, RCLike.re_ofReal_mul, inner_self_eq_norm_sq]
    have hPy := W.starProjection_apply_mem y
    have h1 := ha _ hPy
    have h2 := hb _ hPy
    have h3 : ‖W.starProjection y‖ ^ 2 ≤ ‖y‖ ^ 2 :=
      pow_le_pow_left₀ (norm_nonneg _) (W.norm_starProjection_apply_le y) 2
    have h4 : (β - α) / 2 * ‖W.starProjection y‖ ^ 2 ≤
        (β - α) / 2 * ‖y‖ ^ 2 :=
      mul_le_mul_of_nonneg_left h3 he0
    rw [hmove, hval, abs_le]
    constructor <;> nlinarith [h1, h2, h4]
  have hnorm : ‖C‖ ≤ (β - α) / 2 :=
    TauCeti.ContinuousLinearMap.norm_le_of_abs_re_inner_map_self_le
      hCsym he0 hform
  have hCu : C u = S u := by
    rw [hCapp, Submodule.starProjection_eq_self_iff.mpr hu,
      Submodule.starProjection_eq_self_iff.mpr (hSW u hu)]
  calc ‖T u - (((α + β) / 2 : ℝ) : 𝕜) • u‖ = ‖C u‖ := by rw [hCu, hSapp]
    _ ≤ ‖C‖ * ‖u‖ := C.le_opNorm u
    _ ≤ (β - α) / 2 * ‖u‖ := by gcongr

omit [CompleteSpace E] in
/-- **The residual bound transfers to the adjoint block.** -/
theorem norm_starProjection_map_le_of_mem_orthogonal' (hT : T.IsSymmetric)
    {Z : Submodule 𝕜 E} [Z.HasOrthogonalProjection] {ρ : ℝ} (hρ0 : 0 ≤ ρ)
    (hρ : ∀ x ∈ Z, ‖T x - Z.starProjection (T x)‖ ≤ ρ * ‖x‖)
    {w : E} (hw : w ∈ Zᗮ) : ‖Z.starProjection (T w)‖ ≤ ρ * ‖w‖ :=
  _root_.LinearMap.norm_starProjection_apply_le_of_mem_orthogonal hT hρ0 hρ hw

omit [CompleteSpace E] in
/-- **The exact supremum bound `δ κ ≤ ρ √(1 - κ²)`**, by approximation.

Abstracted over the strip half-width so the bounded and unbounded per-vector
theorems share it: the bounded one supplies `(β - α) / 2`, the unbounded one its
own `halfWidth`.  Both wrote out the same fifty-four lines. -/
theorem mul_le_mul_sqrt_one_sub_sq_of_chain
    {Z V : Submodule 𝕜 E} [Z.HasOrthogonalProjection]
    (Wop : (↥Vᗮ) →L[𝕜] E) {κ halfWidth δ ρ : ℝ}
    (hκdef : κ = ‖Wop‖) (hκ0 : 0 ≤ κ) (hhalf : 0 ≤ halfWidth)
    (hδ : 0 < δ) (hρ0 : 0 ≤ ρ)
    (hWopapp : ∀ x : (↥Vᗮ), Wop x = Z.starProjection (x : E))
    (hchain : ∀ u₀ ∈ Vᗮ, ‖u₀‖ ≤ 1 →
      (halfWidth + δ) * ‖Z.starProjection u₀‖ ≤
        κ * halfWidth + ρ * ‖u₀ - Z.starProjection u₀‖) :
    δ * κ ≤ ρ * Real.sqrt (1 - κ ^ 2) := by
  rcases eq_or_lt_of_le hκ0 with hκz | hκpos
  · rw [← hκz, mul_zero]
    positivity
  · have hev : ∀ ε ∈ Set.Ioo (0 : ℝ) κ,
        δ * κ ≤ (halfWidth + δ) * ε +
          ρ * Real.sqrt (1 - (κ - ε) ^ 2) := by
      intro ε hε
      obtain ⟨x, hx1, hxlt⟩ :=
        Wop.exists_lt_apply_of_lt_opNorm (r := κ - ε)
          (by rw [hκdef] at hε ⊢; linarith [hε.1])
      have hu₀V : (x : E) ∈ Vᗮ := x.2
      have hu₀n : ‖(x : E)‖ ≤ 1 := le_of_lt hx1
      have halt : κ - ε < ‖Z.starProjection (x : E)‖ := by
        rwa [hWopapp] at hxlt
      have hεκ : (0 : ℝ) ≤ κ - ε := by linarith [hε.2]
      have ha1 : ‖Z.starProjection (x : E)‖ ≤ 1 :=
        le_trans (Z.norm_starProjection_apply_le _) hu₀n
      have hpy := norm_sq_starProjection_add_norm_sq_sub Z (x : E)
      have hb : ‖(x : E) - Z.starProjection (x : E)‖ ≤
          Real.sqrt (1 - (κ - ε) ^ 2) := by
        have hb2 : ‖(x : E) - Z.starProjection (x : E)‖ ^ 2 ≤
            1 - (κ - ε) ^ 2 := by
          have hn1 : ‖(x : E)‖ ^ 2 ≤ 1 :=
            pow_le_one₀ (norm_nonneg _) hu₀n
          have h2 : (κ - ε) ^ 2 ≤ ‖Z.starProjection (x : E)‖ ^ 2 := by
            nlinarith [halt, hεκ]
          linarith
        calc ‖(x : E) - Z.starProjection (x : E)‖
            = Real.sqrt (‖(x : E) - Z.starProjection (x : E)‖ ^ 2) :=
              (Real.sqrt_sq (norm_nonneg _)).symm
          _ ≤ Real.sqrt (1 - (κ - ε) ^ 2) := Real.sqrt_le_sqrt hb2
      have hstep := hchain (x : E) hu₀V hu₀n
      have hbρ : ρ * ‖(x : E) - Z.starProjection (x : E)‖ ≤
          ρ * Real.sqrt (1 - (κ - ε) ^ 2) :=
        mul_le_mul_of_nonneg_left hb hρ0
      have hlhs : (halfWidth + δ) * (κ - ε) ≤
          (halfWidth + δ) * ‖Z.starProjection (x : E)‖ := by
        have hpos : (0 : ℝ) ≤ halfWidth + δ := by linarith
        nlinarith [halt]
      nlinarith [hstep, hbρ, hlhs]
    have hcont : ContinuousWithinAt
        (fun ε : ℝ => (halfWidth + δ) * ε +
          ρ * Real.sqrt (1 - (κ - ε) ^ 2))
        (Set.Ioo 0 κ) 0 := by
      apply Continuous.continuousWithinAt
      exact (continuous_const.mul continuous_id).add
        (continuous_const.mul (Real.continuous_sqrt.comp
          (continuous_const.sub
            ((continuous_const.sub continuous_id).pow 2))))
    have hne : (nhdsWithin (0 : ℝ) (Set.Ioo 0 κ)).NeBot := by
      rw [← mem_closure_iff_nhdsWithin_neBot, closure_Ioo hκpos.ne]
      exact ⟨le_refl 0, hκpos.le⟩
    have hlim := ge_of_tendsto hcont
      (by filter_upwards [self_mem_nhdsWithin] with ε hε using hev ε hε)
    simpa using hlim

omit [CompleteSpace E] in
/-- **The per-vector tangent bound from a compression bound.**

If `‖P_Z u‖ ≤ κ‖u‖` on `Vᗮ` and `δ κ ≤ ρ √(1 - κ²)`, then
`δ ‖P_Z u‖ ≤ ρ ‖u - P_Z u‖` there.  Pythagoras turns the compression bound
into the tangent bound; the hypothesis is what
`mul_le_mul_sqrt_one_sub_sq_of_chain` supplies.

Shared by the bounded and unbounded per-vector theorems, which had it
character-for-character apart from two local hypothesis names. -/
theorem mul_norm_starProjection_le_of_compression_bound
    {Z V : Submodule 𝕜 E} [Z.HasOrthogonalProjection] {κ δ ρ : ℝ}
    (hκ0 : 0 ≤ κ) (hκ1 : κ ≤ 1) (hδ : 0 < δ) (hρ0 : 0 ≤ ρ)
    (hmax : ∀ v ∈ Vᗮ, ‖Z.starProjection v‖ ≤ κ * ‖v‖)
    (hκineq : δ * κ ≤ ρ * Real.sqrt (1 - κ ^ 2)) :
    ∀ u ∈ Vᗮ, δ * ‖Z.starProjection u‖ ≤ ρ * ‖u - Z.starProjection u‖ := by
  intro u huV
  have hPu : ‖Z.starProjection u‖ ≤ κ * ‖u‖ := hmax u huV
  have hpyu : ‖Z.starProjection u‖ ^ 2 + ‖u - Z.starProjection u‖ ^ 2 =
      ‖u‖ ^ 2 := norm_sq_starProjection_add_norm_sq_sub Z u
  have h1κ2 : (0 : ℝ) ≤ 1 - κ ^ 2 := by nlinarith [hκ1, hκ0]
  have hsq : (δ * ‖Z.starProjection u‖) ^ 2 ≤
      (ρ * ‖u - Z.starProjection u‖) ^ 2 := by
    have hδκsq : (δ * κ) ^ 2 ≤ ρ ^ 2 * (1 - κ ^ 2) := by
      calc (δ * κ) ^ 2
          ≤ (ρ * Real.sqrt (1 - κ ^ 2)) ^ 2 :=
            pow_le_pow_left₀ (mul_nonneg hδ.le hκ0) hκineq 2
        _ = ρ ^ 2 * Real.sqrt (1 - κ ^ 2) ^ 2 := by ring
        _ = ρ ^ 2 * (1 - κ ^ 2) := by rw [Real.sq_sqrt h1κ2]
    have hPu2 : ‖Z.starProjection u‖ ^ 2 ≤ κ ^ 2 * ‖u‖ ^ 2 := by
      nlinarith [hPu, norm_nonneg (Z.starProjection u), norm_nonneg u,
        hκ0]
    calc (δ * ‖Z.starProjection u‖) ^ 2
        = δ ^ 2 * ‖Z.starProjection u‖ ^ 2 := by ring
      _ ≤ δ ^ 2 * (κ ^ 2 * ‖u‖ ^ 2) :=
          mul_le_mul_of_nonneg_left hPu2 (sq_nonneg δ)
      _ = (δ * κ) ^ 2 * ‖u‖ ^ 2 := by ring
      _ ≤ ρ ^ 2 * (1 - κ ^ 2) * ‖u‖ ^ 2 :=
          mul_le_mul_of_nonneg_right hδκsq (sq_nonneg _)
      _ = ρ ^ 2 * ‖u‖ ^ 2 - ρ ^ 2 * (κ ^ 2 * ‖u‖ ^ 2) := by ring
      _ ≤ ρ ^ 2 * ‖u‖ ^ 2 - ρ ^ 2 * ‖Z.starProjection u‖ ^ 2 := by
          have := mul_le_mul_of_nonneg_left hPu2 (sq_nonneg ρ)
          linarith
      _ = ρ ^ 2 * (‖u‖ ^ 2 - ‖Z.starProjection u‖ ^ 2) := by ring
      _ = ρ ^ 2 * ‖u - Z.starProjection u‖ ^ 2 := by
          rw [show ‖u - Z.starProjection u‖ ^ 2 =
            ‖u‖ ^ 2 - ‖Z.starProjection u‖ ^ 2 by linarith [hpyu]]
      _ = (ρ * ‖u - Z.starProjection u‖) ^ 2 := by ring
  have := Real.sqrt_le_sqrt hsq
  rwa [Real.sqrt_sq (mul_nonneg hδ.le (norm_nonneg _)),
    Real.sqrt_sq (mul_nonneg hρ0 (norm_nonneg _))] at this

/-- **The Davis--Kahan `tan Θ` theorem on an infinite-dimensional Hilbert
space** (per-vector, pole-free form).  `T` symmetric; `V` a `T`-invariant
subspace with the complementary quadratic form in the strip `[α, β]`; `Z` a
test subspace whose compression is coercive at distance `(β-α)/2 + δ` from
the strip's midpoint; `ρ` a columnwise residual bound over `Z`.  Then
`δ ‖x − P_V x‖ ≤ ρ ‖P_V x‖` for every `x ∈ Z` — in particular the
hypotheses force `Z ∩ Vᗮ = 0`, and no dimension comparison between `Z` and
`V` is assumed. -/
theorem tan_theta_le' (hT : T.IsSymmetric)
    {Z V : Submodule 𝕜 E} [Z.HasOrthogonalProjection]
    [V.HasOrthogonalProjection]
    (hVinv : ∀ x ∈ V, T x ∈ V)
    {α β δ ρ : ℝ} (hαβ : α ≤ β) (hδ : 0 < δ) (hρ0 : 0 ≤ ρ)
    (hZ : ∀ x ∈ Z, ((β - α) / 2 + δ) * ‖x‖
      ≤ ‖Z.starProjection (T x) - (((α + β) / 2 : ℝ) : 𝕜) • x‖)
    (hVa : ∀ x ∈ Vᗮ, α * ‖x‖ ^ 2 ≤ RCLike.re ⟪T x, x⟫_𝕜)
    (hVb : ∀ x ∈ Vᗮ, RCLike.re ⟪T x, x⟫_𝕜 ≤ β * ‖x‖ ^ 2)
    (hρ : ∀ x ∈ Z, ‖T x - Z.starProjection (T x)‖ ≤ ρ * ‖x‖) :
    ∀ x ∈ Z, δ * ‖x - V.starProjection x‖ ≤ ρ * ‖V.starProjection x‖ := by
  have he0 : (0 : ℝ) ≤ (β - α) / 2 := by linarith
  -- `Vᗮ` is `T`-invariant, and `T − c` contracts it to the strip half-width.
  have hVperp : ∀ u ∈ Vᗮ, T u ∈ Vᗮ := fun u hu =>
    map_mem_orthogonal_of_forall_map_mem hT hVinv hu
  have hstrip : ∀ u ∈ Vᗮ,
      ‖T u - (((α + β) / 2 : ℝ) : 𝕜) • u‖ ≤ (β - α) / 2 * ‖u‖ :=
    fun u hu => norm_map_sub_midpoint_smul_le' hT hVperp hαβ hVa hVb hu
  -- the compressed projection and its norm
  set Wop : (↥Vᗮ) →L[𝕜] E := Z.starProjection ∘L Vᗮ.subtypeL with hWop
  set κ : ℝ := ‖Wop‖ with hκdef
  have hκ0 : 0 ≤ κ := norm_nonneg _
  have hmax : ∀ v ∈ Vᗮ, ‖Z.starProjection v‖ ≤ κ * ‖v‖ := fun v hv =>
    Wop.le_opNorm ⟨v, hv⟩
  have hκ1 : κ ≤ 1 := by
    refine ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun v => ?_
    rw [one_mul]
    exact Z.norm_starProjection_apply_le (v : E)
  -- the chain inequality at an arbitrary near-maximizing vector
  have hchain : ∀ u₀ ∈ Vᗮ, ‖u₀‖ ≤ 1 →
      ((β - α) / 2 + δ) * ‖Z.starProjection u₀‖ ≤
        κ * ((β - α) / 2) + ρ * ‖u₀ - Z.starProjection u₀‖ := by
    intro u₀ hu₀V hu₀n
    have h1 := hZ (Z.starProjection u₀) (Z.starProjection_apply_mem u₀)
    have hsplit : Z.starProjection (T (Z.starProjection u₀))
          - (((α + β) / 2 : ℝ) : 𝕜) • Z.starProjection u₀
        = Z.starProjection (T u₀ - (((α + β) / 2 : ℝ) : 𝕜) • u₀)
          - Z.starProjection (T (u₀ - Z.starProjection u₀)) := by
      simp only [map_sub, map_smul]
      abel
    have h2 : ‖Z.starProjection (T u₀ - (((α + β) / 2 : ℝ) : 𝕜) • u₀)‖
        ≤ κ * ((β - α) / 2) := by
      have hin : T u₀ - (((α + β) / 2 : ℝ) : 𝕜) • u₀ ∈ Vᗮ :=
        Submodule.sub_mem _ (hVperp u₀ hu₀V) (Vᗮ.smul_mem _ hu₀V)
      calc ‖Z.starProjection (T u₀ - (((α + β) / 2 : ℝ) : 𝕜) • u₀)‖
          ≤ κ * ‖T u₀ - (((α + β) / 2 : ℝ) : 𝕜) • u₀‖ := hmax _ hin
        _ ≤ κ * ((β - α) / 2 * ‖u₀‖) := by
            have := hstrip u₀ hu₀V
            gcongr
        _ ≤ κ * ((β - α) / 2 * 1) := by gcongr
        _ = κ * ((β - α) / 2) := by ring
    have h3 : ‖Z.starProjection (T (u₀ - Z.starProjection u₀))‖
        ≤ ρ * ‖u₀ - Z.starProjection u₀‖ :=
      norm_starProjection_map_le_of_mem_orthogonal' hT hρ0 hρ
        (Z.sub_starProjection_mem_orthogonal u₀)
    calc ((β - α) / 2 + δ) * ‖Z.starProjection u₀‖
        ≤ ‖Z.starProjection (T (Z.starProjection u₀))
            - (((α + β) / 2 : ℝ) : 𝕜) • Z.starProjection u₀‖ := h1
      _ = ‖Z.starProjection (T u₀ - (((α + β) / 2 : ℝ) : 𝕜) • u₀)
            - Z.starProjection (T (u₀ - Z.starProjection u₀))‖ := by
          rw [hsplit]
      _ ≤ ‖Z.starProjection (T u₀ - (((α + β) / 2 : ℝ) : 𝕜) • u₀)‖
            + ‖Z.starProjection (T (u₀ - Z.starProjection u₀))‖ :=
          norm_sub_le _ _
      _ ≤ κ * ((β - α) / 2) + ρ * ‖u₀ - Z.starProjection u₀‖ :=
          add_le_add h2 h3
  -- the exact supremum bound `δ κ ≤ ρ √(1 − κ²)` by approximation
  have hκineq : δ * κ ≤ ρ * Real.sqrt (1 - κ ^ 2) :=
    mul_le_mul_sqrt_one_sub_sq_of_chain Wop hκdef hκ0 (by linarith) hδ hρ0
      (fun x => rfl) hchain
  -- the complementary-side tangent bound on all of `Vᗮ`
  have hkey : ∀ u ∈ Vᗮ,
      δ * ‖Z.starProjection u‖ ≤ ρ * ‖u - Z.starProjection u‖ :=
    mul_norm_starProjection_le_of_compression_bound hκ0 hκ1 hδ hρ0 hmax hκineq
  -- Cauchy–Schwarz duality back to the test side.
  intro x hxZ
  have huV : x - V.starProjection x ∈ Vᗮ :=
    V.sub_starProjection_mem_orthogonal x
  rcases eq_or_ne (x - V.starProjection x) 0 with h0 | h0
  · rw [h0, norm_zero, mul_zero]
    positivity
  · have hCS : ‖x - V.starProjection x‖ ^ 2
        ≤ ‖x‖ * ‖Z.starProjection (x - V.starProjection x)‖ := by
      have e1 : ⟪x - V.starProjection x, x - V.starProjection x⟫_𝕜
          = ⟪x, x - V.starProjection x⟫_𝕜 := by
        conv_lhs => rw [inner_sub_left]
        rw [Submodule.inner_right_of_mem_orthogonal
          (V.starProjection_apply_mem x) huV, sub_zero]
      have e2 : ⟪x, x - V.starProjection x⟫_𝕜
          = ⟪x, Z.starProjection (x - V.starProjection x)⟫_𝕜 := by
        rw [← Z.inner_starProjection_left_eq_right,
          Submodule.starProjection_eq_self_iff.mpr hxZ]
      calc ‖x - V.starProjection x‖ ^ 2
          = RCLike.re ⟪x - V.starProjection x, x - V.starProjection x⟫_𝕜 :=
            (inner_self_eq_norm_sq _).symm
        _ = RCLike.re ⟪x, Z.starProjection (x - V.starProjection x)⟫_𝕜 := by
            rw [e1, e2]
        _ ≤ ‖⟪x, Z.starProjection (x - V.starProjection x)⟫_𝕜‖ :=
            RCLike.re_le_norm _
        _ ≤ ‖x‖ * ‖Z.starProjection (x - V.starProjection x)‖ :=
            norm_inner_le_norm _ _
    have hk := hkey _ huV
    have hpyZu : ‖Z.starProjection (x - V.starProjection x)‖ ^ 2
          + ‖(x - V.starProjection x)
              - Z.starProjection (x - V.starProjection x)‖ ^ 2
        = ‖x - V.starProjection x‖ ^ 2 :=
      norm_sq_starProjection_add_norm_sq_sub Z _
    have hpyVx : ‖V.starProjection x‖ ^ 2 + ‖x - V.starProjection x‖ ^ 2 =
        ‖x‖ ^ 2 :=
      norm_sq_starProjection_add_norm_sq_sub V x
    have hq : (0 : ℝ) < ‖x - V.starProjection x‖ := norm_pos_iff.mpr h0
    set q : ℝ := ‖x - V.starProjection x‖ with hqdef
    set pz : ℝ := ‖Z.starProjection (x - V.starProjection x)‖ with hpzdef
    set pw : ℝ := ‖(x - V.starProjection x)
      - Z.starProjection (x - V.starProjection x)‖ with hpwdef
    set pv : ℝ := ‖V.starProjection x‖ with hpvdef
    have hfin : (δ * q) ^ 2 ≤ (ρ * pv) ^ 2 := by
      have hA : (δ * pz) ^ 2 ≤ (ρ * pw) ^ 2 :=
        pow_le_pow_left₀ (mul_nonneg hδ.le (norm_nonneg _)) hk 2
      have hB : (q ^ 2) ^ 2 ≤ (‖x‖ * pz) ^ 2 :=
        pow_le_pow_left₀ (sq_nonneg _) hCS 2
      have hC : δ ^ 2 * (q ^ 2) ^ 2 ≤ ρ ^ 2 * pv ^ 2 * (q ^ 2) := by
        calc δ ^ 2 * (q ^ 2) ^ 2
            ≤ δ ^ 2 * (‖x‖ * pz) ^ 2 :=
              mul_le_mul_of_nonneg_left hB (sq_nonneg δ)
          _ = ‖x‖ ^ 2 * (δ * pz) ^ 2 := by ring
          _ ≤ ‖x‖ ^ 2 * (ρ * pw) ^ 2 :=
              mul_le_mul_of_nonneg_left hA (sq_nonneg _)
          _ = ρ ^ 2 * ‖x‖ ^ 2 * pw ^ 2 := by ring
          _ = ρ ^ 2 * ‖x‖ ^ 2 * q ^ 2 - ρ ^ 2 * (‖x‖ ^ 2 * pz ^ 2) := by
              rw [show pw ^ 2 = q ^ 2 - pz ^ 2 by linarith [hpyZu]]
              ring
          _ ≤ ρ ^ 2 * ‖x‖ ^ 2 * q ^ 2 - ρ ^ 2 * (q ^ 2) ^ 2 := by
              have h5 : ρ ^ 2 * (q ^ 2) ^ 2 ≤ ρ ^ 2 * (‖x‖ * pz) ^ 2 :=
                mul_le_mul_of_nonneg_left hB (sq_nonneg ρ)
              have h6 : ρ ^ 2 * (‖x‖ * pz) ^ 2 =
                  ρ ^ 2 * (‖x‖ ^ 2 * pz ^ 2) := by ring
              linarith
          _ = ρ ^ 2 * (‖x‖ ^ 2 - q ^ 2) * q ^ 2 := by ring
          _ = ρ ^ 2 * pv ^ 2 * q ^ 2 := by
              rw [show ‖x‖ ^ 2 - q ^ 2 = pv ^ 2 by linarith [hpyVx]]
      have hq2 : (0 : ℝ) < q ^ 2 := by positivity
      nlinarith [hC, hq2]
    have := Real.sqrt_le_sqrt hfin
    rwa [Real.sqrt_sq (mul_nonneg hδ.le (norm_nonneg _)),
      Real.sqrt_sq (mul_nonneg hρ0 (norm_nonneg _))] at this

end DavisKahanExt
end TauCeti
