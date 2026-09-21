/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, Claude Opus 5
-/
module

public import LeanPool.DavisKahan.ForTauCeti.Analysis.InnerProductSpace.Sylvester.Group

/-!
# The generator of the Sylvester flow is `Z ↦ A Z - Z B`

`SylvesterGroup.lean` shows that `W t Z = U t ∘ Z ∘ (V t)⋆` is a one-parameter
unitary group on the Hilbert–Schmidt space and that its generator is
self-adjoint.  This module identifies what that generator *is*.

`generator_sylvesterGroup_apply` — if `z` lies in the domain of
`generator (sylvesterGroup U V b)` and `x` lies in the domain of `generator V`,
then `Z x` lies in the domain of `generator U`, and

`A (Z x) - Z (B x) = C x`

where `Z` is the operator represented by `z`, `C` the one represented by
`generator (sylvesterGroup U V b) z`, and `A`, `B` the generators of `U`, `V`.

## Only one direction, on purpose

The converse — a characterisation of the generator's domain — is the theorem
that the generator is the closure of `A ⊗ 1 - 1 ⊗ B`, and nothing in the tree
needs it.  The defect-first Sylvester theorem consumes exactly the direction
proved here, and it consumes it in this shape *because* the conclusion
**produces** the domain membership `Z x ∈ dom A` instead of assuming it.  That
is what lets the paper theorem avoid assuming its solution is Hilbert–Schmidt
before proving that it is.

## The argument

Split the difference quotient of the flow at a vector `x`:

`(U t (Z (V (-t) x)) - Z x)/(i t) = U t ((Z (V (-t) x) - Z x)/(i t)) + (U t (Z x) - Z x)/(i t)`

The left-hand side converges to `C x`, because `z` is in the generator domain
and `ℓ²` convergence dominates pointwise convergence — the operator norm of
`ofLp b h` is at most `‖h‖`.  The first right-hand term converges to `-Z (B x)`,
because `Z` is bounded and `U t → 1` strongly.  So the *second* term converges,
and that is precisely the assertion that `Z x` lies in the domain of `A`, with
the value `C x + Z (B x)`.

## Sources

That the generator of the Sylvester flow is `Z ↦ A Z - Z B` is the semigroup form
of Rosenblum's argument, and the `π / 2` mass that makes it sharp is distilled in
`prose/distilled_literature/AlbeverioMakarovMotovilov2001_sylvester_fourier_pi_over_two.tex`.
The donor derived the same equation from a tensor factorisation of the flow; none
of that is used here, as the provenance note records.

## Provenance

*New.*  The donor derives the same equation from the tensor factorisation of the
flow; nothing of that is used.

Moved from
`ForTauCeti/Analysis/InnerProductSpace/SylvesterGenerator.lean` to
`ForTauCeti/Analysis/InnerProductSpace/Sylvester/Generator.lean`.  The `Sylvester/`
directory already held `Basic`, `Interval`, `SpectralDistance` and `Internal/`, while
six siblings of the same family used a flat `Sylvester*` prefix in the directory above;
one family now has one convention.  Path change and import repoint only — no statement,
signature, proof, attribute, declaration name or namespace changed.
-/

public section

open scoped ENNReal NNReal
open Filter Topology Complex

namespace TauCeti
namespace HilbertSchmidt

open TauCeti.OneParameterUnitaryGroup

variable {𝕜 : Type*} [RCLike 𝕜]
variable {ι : Type*} {E F : Type*}
variable [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
variable [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [CompleteSpace F]

omit [CompleteSpace F] in
/-- **`ℓ²` convergence dominates pointwise convergence.** -/

theorem tendsto_ofLp_apply {α : Type*} {l : Filter α} (b : HilbertBasis ι 𝕜 F)
    (g : α → lp (fun _ : ι => E) 2) (g₀ : lp (fun _ : ι => E) 2)
    (h : Tendsto g l (𝓝 g₀)) (x : F) :
    Tendsto (fun a => ofLp b (g a) x) l (𝓝 (ofLp b g₀ x)) := by
  rw [tendsto_iff_norm_sub_tendsto_zero]
  refine squeeze_zero (fun a => norm_nonneg _) (fun a => ?_)
    (by simpa using (tendsto_iff_norm_sub_tendsto_zero.mp h).mul_const ‖x‖)
  calc ‖ofLp b (g a) x - ofLp b g₀ x‖
      = ‖ofLp b (g a - g₀) x‖ := by rw [ofLp_sub]; rfl
    _ ≤ ‖ofLp b (g a - g₀)‖ * ‖x‖ := ContinuousLinearMap.le_opNorm _ _
    _ ≤ ‖g a - g₀‖ * ‖x‖ := by gcongr; exact norm_ofLp_le b _

section Sylvester

variable {ι : Type*} {E F : Type*}
variable [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
variable [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
variable (U : OneParameterUnitaryGroup E) (V : OneParameterUnitaryGroup F)
variable (b : HilbertBasis ι ℂ F)

/-- A convergent family carried along a strongly continuous unitary group, with
the time going to zero, converges to the same limit. -/
@[simp]
theorem tendsto_U_apply {α : Type*} {l : Filter α} (τ : α → ℝ)
    (hτ : Tendsto τ l (𝓝 0)) (w : α → E) (w₀ : E) (hw : Tendsto w l (𝓝 w₀)) :
    Tendsto (fun a => U.U (τ a) (w a)) l (𝓝 w₀) := by
  have hgroup : Tendsto (fun a => U.U (τ a) w₀) l (𝓝 w₀) := by
    have hcont : Continuous fun t : ℝ => U.U t w₀ := U.strong_continuous w₀
    have h0 : Tendsto (fun t : ℝ => U.U t w₀) (𝓝 (0 : ℝ)) (𝓝 (U.U 0 w₀)) := hcont.tendsto 0
    rw [show U.U (0 : ℝ) w₀ = w₀ by rw [U.identity]; rfl] at h0
    exact h0.comp hτ
  have hsum : Tendsto (fun a => ‖w a - w₀‖ + ‖U.U (τ a) w₀ - w₀‖) l (𝓝 0) := by
    simpa using (tendsto_iff_norm_sub_tendsto_zero.mp hw).add
      (tendsto_iff_norm_sub_tendsto_zero.mp hgroup)
  rw [tendsto_iff_norm_sub_tendsto_zero]
  refine squeeze_zero (fun a => norm_nonneg _) (fun a => ?_) hsum
  calc ‖U.U (τ a) (w a) - w₀‖
      = ‖U.U (τ a) (w a - w₀) + (U.U (τ a) w₀ - w₀)‖ := by rw [map_sub]; congr 1; abel
    _ ≤ ‖U.U (τ a) (w a - w₀)‖ + ‖U.U (τ a) w₀ - w₀‖ := norm_add_le _ _
    _ = ‖w a - w₀‖ + ‖U.U (τ a) w₀ - w₀‖ := by rw [norm_preserving]

/-- The negated, time-reversed difference quotient converges to the generator. -/
theorem tendsto_genDiffQuot_neg_time (x : (generator V).domain) :
    Tendsto (fun t : ℝ => ((I * (t : ℂ))⁻¹) • (V.U (-t) (x : F) - (x : F)))
      (𝓝[≠] (0 : ℝ)) (𝓝 (-(generator V x))) := by
  have hneg : Tendsto (fun t : ℝ => -t) (𝓝[≠] (0 : ℝ)) (𝓝[≠] (0 : ℝ)) := by
    exact (continuous_neg.tendsto' 0 0 neg_zero).inf
      (tendsto_principal_principal.2 fun t ht => by simpa using ht)
  refine (((generator_tendsto V x).comp hneg).neg).congr fun t => ?_
  rw [Function.comp_apply, genDiffQuot_apply, ← neg_smul]
  congr 1
  push_cast
  rw [mul_neg, inv_neg, neg_neg]

/-- **The generator of the Sylvester flow satisfies the Sylvester equation.**

If `z` is in the domain of the flow's generator and `x` is in the domain of
`generator V`, then `Z x` is in the domain of `generator U` and

`A (Z x) - Z (B x) = C x`,

with `Z` and `C` the operators represented by `z` and by the generator applied
to `z`.  The domain membership is a *conclusion*, not a hypothesis. -/

theorem generator_sylvesterGroup_apply
    (z : (generator (sylvesterGroup U V b)).domain) (x : (generator V).domain) :
    ∃ hmem : ofLp b (z : lp (fun _ : ι => E) 2) (x : F) ∈ (generator U).domain,
      generator U ⟨ofLp b (z : lp (fun _ : ι => E) 2) (x : F), hmem⟩
          - ofLp b (z : lp (fun _ : ι => E) 2) (generator V x)
        = ofLp b (generator (sylvesterGroup U V b) z) (x : F) := by
  set Z := ofLp b (z : lp (fun _ : ι => E) 2) with hZ
  set C := ofLp b (generator (sylvesterGroup U V b) z) with hC
  -- (1) the flow's difference quotient, evaluated at `x`, converges to `C x`
  have hquot : Tendsto
      (fun t : ℝ =>
        ofLp b (genDiffQuot (sylvesterGroup U V b) (z : lp (fun _ : ι => E) 2) t) (x : F))
      (𝓝[≠] (0 : ℝ)) (𝓝 (C (x : F))) :=
    tendsto_ofLp_apply b _ _ (generator_tendsto (sylvesterGroup U V b) z) (x : F)
  -- (2) that quotient splits into the two pieces of the Sylvester expression
  have hsplit : ∀ t : ℝ,
      ofLp b (genDiffQuot (sylvesterGroup U V b) (z : lp (fun _ : ι => E) 2) t) (x : F)
        = U.U t (Z (((I * (t : ℂ))⁻¹) • (V.U (-t) (x : F) - (x : F))))
          + genDiffQuot U (Z (x : F)) t := by
    intro t
    simp only [genDiffQuot_apply, ofLp_smul, ofLp_sub, sylvesterGroup_apply, sylvesterOp_apply,
      ofLp_sylvesterFun, conjOp, genDiffQuot_apply]
    simp only [smul_apply, sub_apply, ContinuousLinearMap.comp_apply, map_smul, map_sub, ← hZ]
    rw [← smul_add]
    congr 1
    abel
  -- (3) the first piece converges to `-Z (B x)`
  have hfirst : Tendsto
      (fun t : ℝ => U.U t (Z (((I * (t : ℂ))⁻¹) • (V.U (-t) (x : F) - (x : F)))))
      (𝓝[≠] (0 : ℝ)) (𝓝 (-(Z (generator V x)))) := by
    refine tendsto_U_apply U (fun t : ℝ => t) ?_ _ _ ?_
    · exact tendsto_id.mono_left nhdsWithin_le_nhds
    · have h := (Z.continuous.tendsto (-(generator V x))).comp (tendsto_genDiffQuot_neg_time V x)
      simpa [Function.comp_def, map_neg] using h
  -- (4) hence the second piece converges, which is the domain membership
  have hsecond : Tendsto (fun t : ℝ => genDiffQuot U (Z (x : F)) t) (𝓝[≠] (0 : ℝ))
      (𝓝 (C (x : F) + Z (generator V x))) := by
    have hdiff : Tendsto (fun t : ℝ =>
        ofLp b (genDiffQuot (sylvesterGroup U V b) (z : lp (fun _ : ι => E) 2) t) (x : F)
          - U.U t (Z (((I * (t : ℂ))⁻¹) • (V.U (-t) (x : F) - (x : F)))))
        (𝓝[≠] (0 : ℝ)) (𝓝 (C (x : F) + Z (generator V x))) := by
      simpa [sub_neg_eq_add] using hquot.sub hfirst
    refine hdiff.congr fun t => ?_
    rw [hsplit t]
    abel
  have hmem : Z (x : F) ∈ (generator U).domain := ⟨_, hsecond⟩
  refine ⟨hmem, ?_⟩
  have hval : generator U ⟨Z (x : F), hmem⟩ = C (x : F) + Z (generator V x) :=
    tendsto_nhds_unique (generator_tendsto U ⟨Z (x : F), hmem⟩) hsecond
  rw [hval]
  abel

end Sylvester

end HilbertSchmidt
end TauCeti
