/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, Claude Fable 5
-/
module


public import LeanPool.DavisKahan.DavisKahan.TanTheta.Theorem63TrialData
public import LeanPool.DavisKahan.DavisKahan.TanTheta.UnboundedSpectrum
public import LeanPool.DavisKahan.DavisKahan.SpectralTheory.ReflectionRestriction
public import LeanPool.DavisKahan.ForTauCeti.Analysis.OperatorIdeal.ApproximationNumber.GramSpectralRank

/-! # Theorem63Unbounded -/

@[expose] public section

open TauCeti.DavisKahan.Sylvester

/-!
# Theorem 6.3 for unbounded self-adjoint operators

Davis--Kahan's Section 2 claims the four angle theorems for unbounded self-adjoint
operators, with the extra work concentrated in Theorem 5.2 and the Appendix to Section 6.
For the single-angle tangent family that claim is at **arbitrary unitarily invariant
norm**, and the compiled unbounded coverage was an operator-norm graph-angle companion.

This module closes the gap by instantiating the abstract chain of
`DavisKahan/TanTheta/Theorem63TrialData.lean` at an `BoundedCompressionTrialBlock`.

## Why the abstract chain applies

The tangent argument never evaluates the ambient operator anywhere except

* on the trial subspace, where an `BoundedCompressionTrialBlock` bundles the action, its
  compression and its residual as *bounded* maps, and
* at vectors `P_{Vᗮ} z` with `z` in the trial subspace, through the crossed quadratic
  form.

Both are available for an unbounded operator whose domain contains the trial subspace and
whose `V` is a spectral subspace: spectral projections preserve the domain
(`selfAdjointSpectralProjection_mem_domain`) and commute with the operator there
(`selfAdjoint_apply_spectralProjection`), so `P_{Vᗮ} z` lies in the domain and
`P_{Vᗮ} (A z) = A (P_{Vᗮ} z)`.  Nothing asks for a bounded ambient operator, and nothing
asks for the quadratic form at a vector where it is undefined.

## The gap hypothesis

`V` is the spectral subspace of `Set.Iic α`, and the lower form bound on `Vᗮ` is the
paper's spectral gap: no spectrum in `Set.Ioo α (α + δ)`.  A vector of `Vᗮ` then has no
spectral mass in `Set.Iic c` for any `c < α + δ`, so the vector-local energy bound applies
at every such `c`, and the constant `α + δ` follows by taking `c` up to it.  The endpoint
`α + δ` itself is allowed to carry spectrum, which is why the argument goes through `c`
rather than applying the bound once.
-/

open scoped InnerProductSpace BigOperators

namespace TauCeti
namespace DavisKahan
namespace TanTheta

open ExactSinTheta
open TanTheta
open Module (finrank)

universe u

section ScalarGeneric

variable {𝕜 : Type*} [RCLike 𝕜]
variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace 𝕜 H]

/-- **Trial-block data from an unbounded trial block.**  The action is reassembled from
the bundled compression and residual, so every field is a bounded map even though the
ambient operator is not.

Both the source bundle and the target bundle are bounded data, so this construction is
scalar-generic. -/
noncomputable def Theorem63TrialData.ofUnbounded
    {A : H →ₗ.[𝕜] H} {Z : Submodule 𝕜 H}
    [Z.HasOrthogonalProjection] [CompleteSpace Z]
    (D : BoundedCompressionTrialBlock A Z) (V : Submodule 𝕜 H) [V.HasOrthogonalProjection] :
    Theorem63TrialData Z V where
  action := Z.subtypeL ∘L D.operator + D.residual
  compression := D.operator
  residual := D.residual
  compression_isSymmetric := by
    intro x y
    have h := D.operator_selfAdjoint
    rw [ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric] at h
    exact h x y
  action_eq := fun z => rfl
  residual_orthogonal := fun z z' =>
    Submodule.inner_left_of_mem_orthogonal z'.2 (D.residual_mem_orthogonal z)

/-- The action of the unbounded trial data is the operator's own action. -/
theorem Theorem63TrialData.ofUnbounded_action
    {A : H →ₗ.[𝕜] H} {Z : Submodule 𝕜 H}
    [Z.HasOrthogonalProjection] [CompleteSpace Z]
    (D : BoundedCompressionTrialBlock A Z) (V : Submodule 𝕜 H) [V.HasOrthogonalProjection]
    (z : Z) :
    (Theorem63TrialData.ofUnbounded D V).action z =
      A ⟨(z : H), D.domain_le z.property⟩ := by
  have h := D.residual_apply z
  change ((D.operator z : Z) : H) + D.residual z = _
  rw [h]
  abel

/-- **The crossed form bound for an arbitrary reducing subspace.**

This is the printed hypothesis of Davis--Kahan's generalized `tan Θ` theorem, and nothing
more.  `V` is a *chosen* subspace reducing the ambient operator — its orthogonal projection
preserves the domain (`hVdom`) and commutes with the operator there (`hVcomm`) — and the
operator's quadratic form on `Vᗮ` is bounded below by `α + δ` (`hlower`).  In the paper's
notation `V` is the range of `F₀`, `Vᗮ` is the range of `F₁`, and `hlower` is
`α + δ ≤ Λ₁ = F₁* (A + H) F₁`.

Nothing whatever is assumed about the operator on `V` itself — the paper's `Λ₀` is
unconstrained — and in particular no interval of the ambient spectrum is required to be
empty.  `crossed_lower_of_spectralGap` below is the special case `V = specSubspace(Iic α)`,
where the reducing hypotheses come from spectral commutation and the form bound comes from
a spectral gap.

The argument is pure block algebra on the domain, so it is scalar-generic: the only
property of the scalars used is that the real part of an inner product is symmetric. -/
theorem crossed_lower_of_reducing
    (A : H →ₗ.[𝕜] H)
    {Z : Submodule 𝕜 H} [Z.HasOrthogonalProjection] [CompleteSpace Z]
    (D : BoundedCompressionTrialBlock A Z)
    (V : Submodule 𝕜 H) [V.HasOrthogonalProjection]
    {α δ : ℝ}
    (hVdom : ∀ x : A.domain, Vᗮ.starProjection ((x : H)) ∈ A.domain)
    (hVcomm : ∀ x : A.domain,
      Vᗮ.starProjection (A x) =
        A ⟨Vᗮ.starProjection ((x : H)), hVdom x⟩)
    (hlower : ∀ y ∈ Vᗮ, ∀ hy : y ∈ A.domain,
      (α + δ) * ‖y‖ ^ 2 ≤ RCLike.re ⟪A ⟨y, hy⟩, y⟫_𝕜)
    (z : Z) :
    (α + δ) * ‖Vᗮ.starProjection ((z : Z) : H)‖ ^ 2 ≤
      RCLike.re ⟪Vᗮ.starProjection ((z : Z) : H),
        Vᗮ.starProjection ((Theorem63TrialData.ofUnbounded D V).action z)⟫_𝕜 := by
  have hzdom : ((z : Z) : H) ∈ A.domain := D.domain_le z.property
  have hswap : ∀ a b : H, RCLike.re ⟪a, b⟫_𝕜 = RCLike.re ⟪b, a⟫_𝕜 := by
    intro a b
    conv_lhs => rw [← inner_conj_symm]
    rw [RCLike.conj_re]
  have haction : Vᗮ.starProjection ((Theorem63TrialData.ofUnbounded D V).action z) =
      A ⟨Vᗮ.starProjection ((z : Z) : H),
        hVdom ⟨((z : Z) : H), hzdom⟩⟩ := by
    rw [Theorem63TrialData.ofUnbounded_action D V z]
    exact hVcomm ⟨((z : Z) : H), hzdom⟩
  rw [haction]
  exact (hlower (Vᗮ.starProjection ((z : Z) : H)) (Vᗮ.starProjection_apply_mem _)
    (hVdom ⟨((z : Z) : H), hzdom⟩)).trans_eq (hswap _ _)

end ScalarGeneric

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H]

section SpectralGap

variable (A : H →ₗ.[ℂ] H) (hA : IsSelfAdjoint A)

/-- A spectral projection of a subset of a null set is null. -/
theorem specProjection_eq_zero_of_subset {S T : Set ℝ}
    (hS : MeasurableSet S) (hT : MeasurableSet T) (hST : S ⊆ T)
    (hzero : TauCeti.LinearPMap.specProjection hA T hT = 0) :
    TauCeti.LinearPMap.specProjection hA S hS = 0 := by
  have hinter : S ∩ T = S := Set.inter_eq_left.mpr hST
  have hmul := (TauCeti.LinearPMap.spectralPVM hA).proj_inter S T hS hT
  rw [(TauCeti.LinearPMap.spectralPVM hA).proj_congr hinter (hS.inter hT) hS] at hmul
  have hzero' : (TauCeti.LinearPMap.spectralPVM hA).proj T hT = 0 := by
    rw [← TauCeti.LinearPMap.specProjection_def]
    exact hzero
  rw [TauCeti.LinearPMap.specProjection_def, ← hmul, hzero', mul_zero]

/-- **A vector of `Vᗮ` carries no spectral mass below the gap.**

`V` is the spectral subspace of `Set.Iic α`, so `Vᗮ` is the spectral range of
`Set.Ioi α`; intersecting with `Set.Iic c` for `c < α + δ` lands inside the gap. -/
theorem specProjection_Iic_apply_eq_zero_of_gap
    {α δ : ℝ}
    (hgap : TauCeti.LinearPMap.specProjection hA (Set.Ioo α (α + δ))
      measurableSet_Ioo = 0)
    {c : ℝ} (hc : c < α + δ) (x : H) :
    TauCeti.LinearPMap.specProjection hA (Set.Iic c) measurableSet_Iic
      (TauCeti.LinearPMap.specProjection hA (Set.Iic α)ᶜ measurableSet_Iic.compl x)
      = 0 := by
  have hmul := (TauCeti.LinearPMap.spectralPVM hA).proj_inter
    (Set.Iic c) (Set.Iic α)ᶜ measurableSet_Iic measurableSet_Iic.compl
  have hset : Set.Iic c ∩ (Set.Iic α)ᶜ = Set.Ioc α c := by
    ext t
    simp only [Set.mem_inter_iff, Set.mem_Iic, Set.mem_compl_iff, Set.mem_Ioc,
      not_le]
    exact ⟨fun h => ⟨h.2, h.1⟩, fun h => ⟨h.2, h.1⟩⟩
  have hsub : Set.Ioc α c ⊆ Set.Ioo α (α + δ) := by
    intro t ht
    exact ⟨ht.1, lt_of_le_of_lt ht.2 hc⟩
  have hzero : TauCeti.LinearPMap.specProjection hA (Set.Ioc α c)
      measurableSet_Ioc = 0 :=
    specProjection_eq_zero_of_subset A hA measurableSet_Ioc measurableSet_Ioo hsub hgap
  have hcomp : (TauCeti.LinearPMap.spectralPVM hA).proj (Set.Iic c) measurableSet_Iic *
      (TauCeti.LinearPMap.spectralPVM hA).proj (Set.Iic α)ᶜ measurableSet_Iic.compl = 0 := by
    rw [hmul, (TauCeti.LinearPMap.spectralPVM hA).proj_congr hset
      (measurableSet_Iic.inter measurableSet_Iic.compl) measurableSet_Ioc]
    rw [← TauCeti.LinearPMap.specProjection_def]
    exact hzero
  have happ := congrArg (fun L : H →L[ℂ] H => L x) hcomp
  simpa [TauCeti.LinearPMap.specProjection_def] using happ

/-! ### A spectral subspace reduces its operator

The three facts the abstract reducing hypotheses ask for, at `V = specSubspace B`: the
complementary projection is the spectral projection of `Bᶜ`, it preserves the domain, and
it commutes with the operator there. -/

/-- The orthogonal complement of a spectral subspace projects with the spectral projection
of the complementary set. -/
theorem starProjection_orthogonal_selfAdjointSpectralSubspace
    (B : Set ℝ) (hB : MeasurableSet B) :
    (selfAdjointSpectralSubspace A hA B hB)ᗮ.starProjection =
      selfAdjointSpectralProjection A hA Bᶜ hB.compl := by
  change _ = TauCeti.LinearPMap.specProjection hA Bᶜ hB.compl
  rw [Submodule.starProjection_orthogonal',
    ← selfAdjointSpectralProjection_eq_starProjection A hA B hB,
    TauCeti.LinearPMap.specProjection_def,
    (TauCeti.LinearPMap.spectralPVM hA).proj_compl B hB]
  rfl

/-- **A spectral subspace reduces its operator, domain half.**  The projection onto the
complement of a spectral subspace preserves the operator domain. -/
theorem orthogonal_selfAdjointSpectralSubspace_starProjection_mem_domain
    (B : Set ℝ) (hB : MeasurableSet B) (x : A.domain) :
    (selfAdjointSpectralSubspace A hA B hB)ᗮ.starProjection ((x : H)) ∈ A.domain := by
  rw [starProjection_orthogonal_selfAdjointSpectralSubspace A hA B hB]
  exact selfAdjointSpectralProjection_mem_domain A hA hB.compl x

/-- **A spectral subspace reduces its operator, commutation half.** -/
theorem selfAdjoint_apply_orthogonal_selfAdjointSpectralSubspace_starProjection
    (B : Set ℝ) (hB : MeasurableSet B) (x : A.domain) :
    (selfAdjointSpectralSubspace A hA B hB)ᗮ.starProjection (A x) =
      A ⟨(selfAdjointSpectralSubspace A hA B hB)ᗮ.starProjection ((x : H)),
        orthogonal_selfAdjointSpectralSubspace_starProjection_mem_domain A hA B hB x⟩ := by
  have hproj := starProjection_orthogonal_selfAdjointSpectralSubspace A hA B hB
  have hcoe : (⟨(selfAdjointSpectralSubspace A hA B hB)ᗮ.starProjection ((x : H)),
        orthogonal_selfAdjointSpectralSubspace_starProjection_mem_domain A hA B hB x⟩
          : A.domain) =
      ⟨selfAdjointSpectralProjection A hA Bᶜ hB.compl ((x : H)),
        selfAdjointSpectralProjection_mem_domain A hA hB.compl x⟩ :=
    Subtype.ext (congrArg (fun L : H →L[ℂ] H => L ((x : H))) hproj)
  rw [hcoe, selfAdjoint_apply_spectralProjection A hA hB.compl x, hproj]

/-- **The form lower bound off a lower spectral subspace.**  A domain vector orthogonal to
the spectral subspace of `Set.Iic c` has quadratic form at least `c ‖y‖²`.

This is the printed `c ≤ Λ₁` for the canonical choice `V = specSubspace (Iic c)`, and it
holds with no gap hypothesis whatever: it is the definition of the spectral cut. -/
theorem le_re_inner_of_mem_orthogonal_selfAdjointSpectralSubspace_Iic
    {c : ℝ} (y : H)
    (hy : y ∈ (selfAdjointSpectralSubspace A hA (Set.Iic c) measurableSet_Iic)ᗮ)
    (hydom : y ∈ A.domain) :
    c * ‖y‖ ^ 2 ≤ RCLike.re ⟪A ⟨y, hydom⟩, y⟫_ℂ := by
  rw [RCLike.re_to_complex]
  refine TauCeti.LinearPMap.le_re_inner_of_specProjection_Iic_apply_eq_zero
    hA (c := c) ⟨y, hydom⟩ ?_
  have h0 : (selfAdjointSpectralSubspace A hA (Set.Iic c)
      measurableSet_Iic).starProjection y = 0 :=
    (Submodule.starProjection_apply_eq_zero_iff _).mpr hy
  rw [← selfAdjointSpectralProjection_eq_starProjection A hA (Set.Iic c)
    measurableSet_Iic] at h0
  exact h0

/-- **The printed spectral gap supplies the form lower bound on the unwanted subspace.**

`V` is the spectral subspace of `Set.Iic α` and the operator has no spectrum in
`Set.Ioo α (α + δ)`.  Then at every domain vector orthogonal to `V` the quadratic form is
at least `α + δ` — the paper's `α + δ ≤ Λ₁`.

The argument goes through a threshold `c < α + δ` rather than applying the energy bound
once, because the gap is the *open* interval: the endpoint `α + δ` is allowed to carry
spectrum, so `P_{Iic (α+δ)} y` need not vanish, while `P_{Iic c} y` does for every
`c < α + δ`. -/
theorem le_re_inner_of_mem_orthogonal_selfAdjointSpectralSubspace_of_gap
    {α δ : ℝ}
    (hgap : TauCeti.LinearPMap.specProjection hA (Set.Ioo α (α + δ))
      measurableSet_Ioo = 0)
    (y : H)
    (hyV : y ∈ (selfAdjointSpectralSubspace A hA (Set.Iic α) measurableSet_Iic)ᗮ)
    (hy : y ∈ A.domain) :
    (α + δ) * ‖y‖ ^ 2 ≤ RCLike.re ⟪A ⟨y, hy⟩, y⟫_ℂ := by
  classical
  have hprojV' : (selfAdjointSpectralSubspace A hA (Set.Iic α)
      measurableSet_Iic)ᗮ.starProjection =
      TauCeti.LinearPMap.specProjection hA (Set.Iic α)ᶜ measurableSet_Iic.compl :=
    starProjection_orthogonal_selfAdjointSpectralSubspace A hA (Set.Iic α)
      measurableSet_Iic
  have hfix : TauCeti.LinearPMap.specProjection hA (Set.Iic α)ᶜ
      measurableSet_Iic.compl y = y := by
    rw [← hprojV']
    exact Submodule.starProjection_eq_self_iff.mpr hyV
  -- The energy bound, at every threshold strictly below the gap.
  have hstep : ∀ c : ℝ, c < α + δ →
      c * ‖y‖ ^ 2 ≤ (⟪A ⟨y, hy⟩, y⟫_ℂ).re := by
    intro c hc
    refine TauCeti.LinearPMap.le_re_inner_of_specProjection_Iic_apply_eq_zero
      hA (c := c) ⟨y, hy⟩ ?_
    have h0 := specProjection_Iic_apply_eq_zero_of_gap A hA hgap hc y
    rwa [hfix] at h0
  -- Take `c` up to `α + δ`.
  have hfinal : (α + δ) * ‖y‖ ^ 2 ≤ (⟪A ⟨y, hy⟩, y⟫_ℂ).re := by
    by_contra hcon
    push Not at hcon
    rcases eq_or_lt_of_le (sq_nonneg ‖y‖) with hzero | hpos
    · rw [← hzero, mul_zero] at hcon
      have hy0 : y = 0 := by
        have hsq : ‖y‖ ^ 2 = 0 := hzero.symm
        simpa using pow_eq_zero_iff (n := 2) (by norm_num) |>.mp hsq
      simp only [hy0, inner_zero_right, Complex.zero_re] at hcon
      exact absurd hcon (lt_irrefl 0)
    · obtain ⟨c, hc1, hc2⟩ := exists_between
        (show (⟪A ⟨y, hy⟩, y⟫_ℂ).re / ‖y‖ ^ 2 < α + δ by
          rw [div_lt_iff₀ hpos]
          exact hcon)
      have h := hstep c hc2
      rw [div_lt_iff₀ hpos] at hc1
      linarith
  rw [RCLike.re_to_complex]
  exact hfinal

end SpectralGap

/-- **The crossed form bound for an unbounded self-adjoint operator.**

`V` is the spectral subspace of `Iic α`; the gap hypothesis says the operator has no
spectrum in `Ioo α (α + δ)`.  Then on `Vᗮ` the quadratic form is bounded below by
`α + δ`, which is exactly the hypothesis the abstract chain consumes.

This is the corollary of `crossed_lower_of_reducing` at that choice of `V`: the spectral
projection of `(Iic α)ᶜ` preserves the domain and commutes with the operator there, and the
gap supplies the form bound on `Vᗮ` at every vector of the domain, not merely at the
projected trial vectors. -/
theorem crossed_lower_of_spectralGap
    (A : H →ₗ.[ℂ] H) (hA : IsSelfAdjoint A)
    {Z : Submodule ℂ H} [Z.HasOrthogonalProjection] [CompleteSpace Z]
    (D : BoundedCompressionTrialBlock A Z)
    {α δ : ℝ}
    (hgap : TauCeti.LinearPMap.specProjection hA (Set.Ioo α (α + δ))
      measurableSet_Ioo = 0)
    (z : Z) :
    (α + δ) * ‖(selfAdjointSpectralSubspace A hA (Set.Iic α)
        measurableSet_Iic)ᗮ.starProjection ((z : Z) : H)‖ ^ 2 ≤
      RCLike.re ⟪(selfAdjointSpectralSubspace A hA (Set.Iic α)
          measurableSet_Iic)ᗮ.starProjection ((z : Z) : H),
        (selfAdjointSpectralSubspace A hA (Set.Iic α)
          measurableSet_Iic)ᗮ.starProjection
            ((Theorem63TrialData.ofUnbounded D
              (selfAdjointSpectralSubspace A hA (Set.Iic α)
                measurableSet_Iic)).action z)⟫_ℂ :=
  crossed_lower_of_reducing A D
    (selfAdjointSpectralSubspace A hA (Set.Iic α) measurableSet_Iic)
    (orthogonal_selfAdjointSpectralSubspace_starProjection_mem_domain A hA
      (Set.Iic α) measurableSet_Iic)
    (selfAdjoint_apply_orthogonal_selfAdjointSpectralSubspace_starProjection A hA
      (Set.Iic α) measurableSet_Iic)
    (le_re_inner_of_mem_orthogonal_selfAdjointSpectralSubspace_of_gap A hA hgap) z


/-! ### The unbounded Section 2 tangent theorem -/

/-- **Davis--Kahan Theorem 6.3 for an unbounded self-adjoint operator, at arbitrary
Fan-dominant unitarily invariant ideal gauge.**

`V` is the spectral subspace of `Set.Iic α`; the operator has no spectrum in the gap
`Set.Ioo α (α + δ)`; the Ritz compression of the trial subspace is bounded above by `α`.
The conclusion is the paper's tangent bound `δ · N(tan Θ₀) ≤ N(R)` for **every**
Fan-dominant unitarily invariant ideal gauge, not merely the operator norm.

This is the Section 2 scope claim for the single-angle tangent family: the ambient
operator is closed, unbounded and self-adjoint, and nothing in the statement or the proof
requires it to be bounded. -/
theorem theorem6_3_unbounded_ideal
    (N : ExactSinTheta.KyFanDominantIdealFamily (𝕜 := ℂ))
    (A : H →ₗ.[ℂ] H) (hA : IsSelfAdjoint A)
    {Z : Submodule ℂ H} [Z.HasOrthogonalProjection] [CompleteSpace Z]
    [FiniteDimensional ℂ Z]
    (D : BoundedCompressionTrialBlock A Z)
    {α δ : ℝ} (hδ : 0 < δ)
    (hgap : TauCeti.LinearPMap.specProjection hA (Set.Ioo α (α + δ))
      measurableSet_Ioo = 0)
    (hCompression : ∀ z : Z, RCLike.re ⟪D.operator z, z⟫_ℂ ≤ α * ‖z‖ ^ 2)
    (tanTheta0 : Z →L[ℂ] H)
    (htan : HasTheorem63DirectedTangentApproximationNumbers Z
      (selfAdjointSpectralSubspace A hA (Set.Iic α) measurableSet_Iic) tanTheta0)
    (hResidual : N.Mem D.residual) :
    N.Mem tanTheta0 ∧ δ * N.gauge tanTheta0 ≤ N.gauge D.residual :=
  Theorem63TrialData.ideal_of_formBounds
    (Theorem63TrialData.ofUnbounded D
      (selfAdjointSpectralSubspace A hA (Set.Iic α) measurableSet_Iic))
    N hδ hCompression (crossed_lower_of_spectralGap A hA D hgap) tanTheta0 htan
    hResidual

/-- **The unbounded tangent theorem with the representative exhibited.**

The tangent representative is the one `Theorem63FiniteSource` constructs — diagonal in the
right singular basis of the directed sine block, with entries `tan (arcsin sᵢ)` — and the
`sᵢ < 1` it needs is derived from the same spectral gap, not assumed.  So this carries no
hypothesis the printed theorem does not. -/
theorem theorem6_3_unbounded_ideal_directedTangent
    (N : ExactSinTheta.KyFanDominantIdealFamily (𝕜 := ℂ))
    (A : H →ₗ.[ℂ] H) (hA : IsSelfAdjoint A)
    {Z : Submodule ℂ H} [Z.HasOrthogonalProjection] [CompleteSpace Z]
    [FiniteDimensional ℂ Z]
    (D : BoundedCompressionTrialBlock A Z)
    {α δ : ℝ} (hδ : 0 < δ)
    (hgap : TauCeti.LinearPMap.specProjection hA (Set.Ioo α (α + δ))
      measurableSet_Ioo = 0)
    (hCompression : ∀ z : Z, RCLike.re ⟪D.operator z, z⟫_ℂ ≤ α * ‖z‖ ^ 2)
    (hResidual : N.Mem D.residual) :
    N.Mem (theorem63DirectedTangent Z
        (selfAdjointSpectralSubspace A hA (Set.Iic α) measurableSet_Iic)) ∧
      δ * N.gauge (theorem63DirectedTangent Z
        (selfAdjointSpectralSubspace A hA (Set.Iic α) measurableSet_Iic)) ≤
        N.gauge D.residual := by
  refine theorem6_3_unbounded_ideal N A hA D hδ hgap hCompression _ ?_ hResidual
  exact hasTheorem63DirectedTangentApproximationNumbers_theorem63DirectedTangent
    Z (selfAdjointSpectralSubspace A hA (Set.Iic α) measurableSet_Iic)
    (fun i => Theorem63TrialData.sine_lt_one_of_formBounds
      (Theorem63TrialData.ofUnbounded D
        (selfAdjointSpectralSubspace A hA (Set.Iic α) measurableSet_Iic))
      hδ hCompression (crossed_lower_of_spectralGap A hA D hgap) i)

/-! ### The printed hypothesis: a chosen reducing subspace

Theorem 6.3 as printed does **not** ask for a spectrum-free interval of the ambient
operator.  It asks for a *chosen* pair of complementary reducing subspaces
`Range F₀ ⊕ Range F₁`, a bound `A₀ ≤ α` on the trial compression, and a bound
`α + δ ≤ Λ₁ = F₁* (A + H) F₁` on the compression to `Range F₁ = Vᗮ`.  The compression
`Λ₀ = F₀* (A + H) F₀` to the chosen subspace is left entirely free.

Taking `V = specSubspace(Iic α)` — the *minimal* subspace whose complement carries only
spectrum above `α` — and then demanding that it already have the required lower bound is
strictly stronger: it forces the whole operator to have no spectrum in `(α, α + δ)`.  With
`spec A = {0, 5, 10}`, `α = 1` and `δ = 9`, the choice `V = specSubspace(Iic 5)` satisfies
the printed hypotheses (`spec Λ₁ = {10} ⊆ [10, ∞)`) while the spectral-gap form does not
apply, because `5 ∈ spec A ∩ (1, 10)`.

The two theorems below are the printed statements. -/

/-- **Davis--Kahan Theorem 6.3 for an unbounded self-adjoint operator with a chosen
reducing subspace, at arbitrary Fan-dominant unitarily invariant ideal gauge.**

The hypothesis list is the printed one (transcription, Theorem 6.3):

* `hVdom`, `hVcomm` — the ranges of `F₀` and `F₁ = ` the complement are invariant
  subspaces of `A + H`, here the closed operator `A`;
* `hCompression` — `A₀ = E₀* (A + H) E₀ ≤ α`, the upper end of the printed
  `β ≤ A₀ ≤ α` (the lower end `β` is never used, in the paper or here);
* `hUnwanted` — `α + δ ≤ Λ₁ = F₁* (A + H) F₁`, read as a form bound on `Vᗮ`;
* `hδ` — the printed `α < α + δ`.

The compression of `A` to `V` itself is unconstrained, exactly as in the source.  The
conclusion is the paper's `δ ‖tan Θ₀‖ ≤ ‖R‖` for every Fan-dominant unitarily invariant
ideal gauge. -/
theorem theorem6_3_unbounded_ideal_of_reducing
    (N : ExactSinTheta.KyFanDominantIdealFamily (𝕜 := ℂ))
    (A : H →ₗ.[ℂ] H)
    {Z : Submodule ℂ H} [Z.HasOrthogonalProjection] [CompleteSpace Z]
    [FiniteDimensional ℂ Z]
    (D : BoundedCompressionTrialBlock A Z)
    (V : Submodule ℂ H) [V.HasOrthogonalProjection]
    {α δ : ℝ} (hδ : 0 < δ)
    (hVdom : ∀ x : A.domain, Vᗮ.starProjection ((x : H)) ∈ A.domain)
    (hVcomm : ∀ x : A.domain,
      Vᗮ.starProjection (A x) =
        A ⟨Vᗮ.starProjection ((x : H)), hVdom x⟩)
    (hCompression : ∀ z : Z, RCLike.re ⟪D.operator z, z⟫_ℂ ≤ α * ‖z‖ ^ 2)
    (hUnwanted : ∀ y ∈ Vᗮ, ∀ hy : y ∈ A.domain,
      (α + δ) * ‖y‖ ^ 2 ≤ RCLike.re ⟪A ⟨y, hy⟩, y⟫_ℂ)
    (tanTheta0 : Z →L[ℂ] H)
    (htan : HasTheorem63DirectedTangentApproximationNumbers Z V tanTheta0)
    (hResidual : N.Mem D.residual) :
    N.Mem tanTheta0 ∧ δ * N.gauge tanTheta0 ≤ N.gauge D.residual :=
  Theorem63TrialData.ideal_of_formBounds (Theorem63TrialData.ofUnbounded D V) N hδ
    hCompression (crossed_lower_of_reducing A D V hVdom hVcomm hUnwanted) tanTheta0
    htan hResidual

/-- **The printed Theorem 6.3 with the tangent representative exhibited.**

Same hypotheses as `theorem6_3_unbounded_ideal_of_reducing`; the tangent is the
representative `Theorem63FiniteSource` constructs, diagonal in the right singular basis of
the directed sine block, and the `sᵢ < 1` it needs is derived from the two form bounds
rather than assumed. -/
theorem theorem6_3_unbounded_ideal_directedTangent_of_reducing
    (N : ExactSinTheta.KyFanDominantIdealFamily (𝕜 := ℂ))
    (A : H →ₗ.[ℂ] H)
    {Z : Submodule ℂ H} [Z.HasOrthogonalProjection] [CompleteSpace Z]
    [FiniteDimensional ℂ Z]
    (D : BoundedCompressionTrialBlock A Z)
    (V : Submodule ℂ H) [V.HasOrthogonalProjection]
    {α δ : ℝ} (hδ : 0 < δ)
    (hVdom : ∀ x : A.domain, Vᗮ.starProjection ((x : H)) ∈ A.domain)
    (hVcomm : ∀ x : A.domain,
      Vᗮ.starProjection (A x) =
        A ⟨Vᗮ.starProjection ((x : H)), hVdom x⟩)
    (hCompression : ∀ z : Z, RCLike.re ⟪D.operator z, z⟫_ℂ ≤ α * ‖z‖ ^ 2)
    (hUnwanted : ∀ y ∈ Vᗮ, ∀ hy : y ∈ A.domain,
      (α + δ) * ‖y‖ ^ 2 ≤ RCLike.re ⟪A ⟨y, hy⟩, y⟫_ℂ)
    (hResidual : N.Mem D.residual) :
    N.Mem (theorem63DirectedTangent Z V) ∧
      δ * N.gauge (theorem63DirectedTangent Z V) ≤ N.gauge D.residual := by
  refine theorem6_3_unbounded_ideal_of_reducing N A D V hδ hVdom hVcomm hCompression
    hUnwanted _ ?_ hResidual
  exact hasTheorem63DirectedTangentApproximationNumbers_theorem63DirectedTangent Z V
    (fun i => Theorem63TrialData.sine_lt_one_of_formBounds
      (Theorem63TrialData.ofUnbounded D V) hδ hCompression
      (crossed_lower_of_reducing A D V hVdom hVcomm hUnwanted) i)

end TanTheta
end DavisKahan
end TauCeti
