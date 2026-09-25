/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, Claude Opus 5
-/
module

public import LeanPool.DavisKahan.DavisKahan.Sources.DavisKahan1970.AmbientBlockVocabulary
public import LeanPool.DavisKahan.DavisKahan.Geometry.Angle.OperatorAngleComplex
public import LeanPool.DavisKahan.DavisKahan.Sylvester.Spectrum
public import LeanPool.DavisKahan.ForTauCeti.Analysis.InnerProductSpace.BoundedOperator.Projector
public import LeanPool.DavisKahan.ForTauCeti.Analysis.InnerProductSpace.Projection.Blocks
public import LeanPool.DavisKahan.DavisKahan.BoundedOperator.Problem
public import LeanPool.DavisKahan.ForTauCeti.Analysis.InnerProductSpace.Spectral.GapProjection
public import LeanPool.DavisKahan.ForTauCeti.Analysis.InnerProductSpace.PrincipalSineSequence

/-! # Section10Functional Calculus -/

@[expose] public section

open TauCeti.DavisKahan.Angle


open TauCeti.DavisKahan.Sylvester

/-!
# Davis--Kahan 1970, Question 10.4: the established step-function specialization

Question 10.4 asks for bounds on `f(A + H) − f(A)` for useful classes of real `f`, and that
general question is genuinely open.  But the block that poses it is not open throughout.
Before asking it, Davis and Kahan work a model case all the way out: they take the step
function

```
f(ξ) = 1  for ξ ≤ α,        f(ξ) = 0  for α + δ ≤ ξ,
```

state that under the `tan 2θ` hypotheses `f(A) = P`, `f(A + H) = Q` and `f(A₀) = 1`, and
deduce from those three identities that

```
‖f(A + H) − f(A)‖      = ‖Q − P‖   = ‖sin Θ‖,
‖(f(A + H) − f(A))E₀‖  = ‖Q^⊥E₀‖  = ‖sin Θ₀‖,
```

before applying the already-proved `tan 2θ` estimates to the right-hand sides.  Those are
deductions, not conjectures, so this repository owes them Lean statements; only the closing
"analogous bounds for more general `f` would be valuable" is an open question.

## The identities are proved here as operator equations

Each of the two displayed norm identities is recorded as an *operator* identity, which is
strictly stronger and covers every unitarily invariant norm rather than only the operator
norm the source displays:

```
f(A + H) − f(A)              = Q − P                     (ambient)
(f(A + H) − f(A)) ∘ E₀       = −P_{Q^⊥}|_U               (directed)
```

The second is the source's `‖Q^⊥E₀‖ = ‖sin Θ₀‖` because `P_{Q^⊥}|_U` — Lean spelling
`TauCeti.principalSineOperator U V` — *is* the repository's directed sine operator, by
definition; and the middle member of the source's chain, `f(A+H)E₀ − E₀f(A₀)`, is recovered
by `Question10_4_directed_functionalCalculusResidual_complex` using `f(A₀) = 1`.

## Where the source is doing more than it says, and what this file assumes instead

`f(A) = P` needs the two blocks of `A` to sit on opposite sides of the gap, and that is
exactly the `tan 2θ` hypothesis `spectrum A₀ ⊆ [β, α]`, `spectrum A₁ ⊆ [α + δ, ∞)`.

`f(A + H) = Q` needs the same of `A + H` and `Q` — that is, `spectrum Λ₀ ⊆ (-∞, α]` and
`spectrum Λ₁ ⊆ [α + δ, ∞)`.  **The printed `tan 2θ` hypotheses do not say this.**  Section 1
is explicit that "no demand has been made that the reducing projectors `P` and `Q` be
spectral projectors", and with an arbitrary reducing `Q` the assertion `f(A + H) = Q` is
false — `Q = 0` reduces `A + H` and is not `f(A + H)`.  The sentence is therefore read the
only way it can be read: in Question 10.4, `Q` is the spectral projection of `A + H` at the
same cut.  That reading is stated as an explicit hypothesis below rather than smuggled in,
so a reviewer can see precisely what the printed sentence needs.

The off-diagonality hypotheses `H₀ = H₁ = 0` are carried for source correspondence even
though these identities do not consume them; they are what the `tan 2θ` estimates applied to
the right-hand sides require.

## Provenance

Davis, C. and Kahan, W. M., *The rotation of eigenvectors by a perturbation. III*,
SIAM J. Numer. Anal. **7** (1970) 1--46, Question 10.4.
-/

namespace TauCeti
namespace DavisKahan1970

open scoped InnerProductSpace

open TauCeti.DavisKahan
open scoped TauCeti.CompleteSubspace

noncomputable section

universe v

variable {E : Type v} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

-- The continuous functional calculus on a block `↥U →L[ℂ] ↥U` needs `CStarAlgebra` of that
-- algebra, which needs `CompleteSpace ↥U`; that is one nesting level past the default budget.
/-! ### The block presentation the gap theorem consumes -/

/-- On an invariant subspace the compression intertwines with the inclusion, which is the
paper's relation `A E₀ = E₀ A₀`.  Scalar-generic: it is projection geometry, with no functional
calculus in it, so the real branch below reuses it unchanged. -/
theorem subtypeL_comp_compressOperator_of_invariant
    {𝕜 : Type*} [RCLike 𝕜] {G : Type*} [NormedAddCommGroup G] [InnerProductSpace 𝕜 G]
    (A : G →L[𝕜] G) (U : Submodule 𝕜 G) [U.HasOrthogonalProjection]
    (hAU : ∀ x ∈ U, A x ∈ U) :
    U.subtypeL ∘L compressOperator U A = A ∘L U.subtypeL := by
  refine ContinuousLinearMap.ext fun x => ?_
  simp only [ContinuousLinearMap.comp_apply, compressOperator, Submodule.subtypeL_apply]
  exact Submodule.starProjection_eq_self_iff.mpr (hAU (x : G) x.2)

/-- **The gap step function of a reduced self-adjoint operator is its reducing projection.**

This is `TauCeti.SpectralGap.cfc_eq_starProjection_of_blockGap` presented in the paper's
block vocabulary: `U` reduces `A`, the two blocks are the compressions `A₀` and `A₁`, and
their spectra are separated by the gap `(α, α + δ)`. -/
theorem cfc_gapStep_eq_starProjection_complex
    {A : E →L[ℂ] E} (hA : IsSelfAdjoint A)
    (U : Submodule ℂ E) [U.HasOrthogonalProjection]
    (hAU : ∀ x ∈ U, A x ∈ U)
    {α δ : ℝ} (hδ : 0 < δ)
    (hA0spec : spectrum ℝ (compressOperator U A) ⊆ Set.Iic α)
    (hA1spec : spectrum ℝ (compressOperator Uᗮ A) ⊆ Set.Ici (α + δ))
    {f : ℝ → ℝ} (hf1 : ∀ t ≤ α, f t = 1) (hf0 : ∀ t, α + δ ≤ t → f t = 0) :
    cfc f A = U.starProjection := by
  have hAred : A.Reduces U :=
    ContinuousLinearMap.IsSymmetric.reduces_of_invariant
      (ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp hA) hAU
  exact TauCeti.SpectralGap.cfc_eq_starProjection_of_blockGap hA
    (subtypeL_comp_compressOperator_of_invariant A U hAU)
    (subtypeL_comp_compressOperator_of_invariant A Uᗮ hAred.2)
    hδ hA0spec hA1spec hf1 hf0

/-! ### The three identities of Question 10.4 -/

variable (U V : Submodule ℂ E) [U.HasOrthogonalProjection] [V.HasOrthogonalProjection]

/-- **Davis--Kahan 1970, Question 10.4: `f(A) = P`.**

Under the `tan 2θ` spectral hypotheses on the blocks of `A`, the gap step function returns
the reducing projection `P`. -/
theorem Question10_4_stepFunction_unperturbed_complex
    {A H : E →L[ℂ] E} (hA : IsSelfAdjoint A) (_hH : IsSelfAdjoint H)
    (hAU : ∀ x ∈ U, A x ∈ U)
    {β α δ : ℝ} (hδ : 0 < δ)
    (hA0spec : spectrum ℝ (compressOperator U A) ⊆ Set.Icc β α)
    (hA1spec : spectrum ℝ (compressOperator Uᗮ A) ⊆ Set.Ici (α + δ))
    (_hHU : ∀ x ∈ U, H x ∈ Uᗮ) (_hHUperp : ∀ x ∈ Uᗮ, H x ∈ U)
    {f : ℝ → ℝ} (hf1 : ∀ t ≤ α, f t = 1) (hf0 : ∀ t, α + δ ≤ t → f t = 0) :
    cfc f A = U.starProjection :=
  cfc_gapStep_eq_starProjection_complex hA U hAU hδ (fun _ hr => (hA0spec hr).2) hA1spec hf1 hf0

/-- **Davis--Kahan 1970, Question 10.4: `f(A + H) = Q`.**

The perturbed half of the same identity.  Its hypotheses place the blocks `Λ₀`, `Λ₁` of
`A + H` on opposite sides of the same gap; see the module docstring for why the printed
`tan 2θ` hypotheses do not supply this and the sentence has to be read as making `Q`
the spectral projection of `A + H` at the cut. -/
theorem Question10_4_stepFunction_perturbed_complex
    {A H : E →L[ℂ] E} (hA : IsSelfAdjoint A) (hH : IsSelfAdjoint H)
    (hAplusH_V : ∀ x ∈ V, (A + H) x ∈ V)
    {α δ : ℝ} (hδ : 0 < δ)
    (hL0spec : spectrum ℝ (compressOperator V (A + H)) ⊆ Set.Iic α)
    (hL1spec : spectrum ℝ (compressOperator Vᗮ (A + H)) ⊆ Set.Ici (α + δ))
    {f : ℝ → ℝ} (hf1 : ∀ t ≤ α, f t = 1) (hf0 : ∀ t, α + δ ≤ t → f t = 0) :
    cfc f (A + H) = V.starProjection :=
  cfc_gapStep_eq_starProjection_complex (hA.add hH) V hAplusH_V hδ hL0spec hL1spec hf1 hf0

/-- **Davis--Kahan 1970, Question 10.4: `f(A₀) = 1`.**

The trial block `A₀` has its whole spectrum at or below `α`, where `f` is `1`, so the
functional calculus returns the identity.  This is the one of the three identities that needs
no gap: only that `f` is constantly `1` where `A₀`'s spectrum lives. -/
theorem Question10_4_stepFunction_trialBlock_complex
    {A : E →L[ℂ] E} (hA : IsSelfAdjoint A) {β α : ℝ}
    (hA0spec : spectrum ℝ (compressOperator U A) ⊆ Set.Icc β α)
    {f : ℝ → ℝ} (hf1 : ∀ t ≤ α, f t = 1) :
    cfc f (compressOperator U A) = 1 := by
  have hA0sa : IsSelfAdjoint (compressOperator U A) := isSelfAdjoint_compressOperator hA U
  rw [cfc_congr (g := fun _ : ℝ => (1 : ℝ)) (a := compressOperator U A)
    fun t ht => hf1 t (hA0spec ht).2]
  exact cfc_one ℝ (compressOperator U A)

/-! ### The two functional-change identities

Both are consequences of the three identities above, and both are recorded as operator
equations so that every unitarily invariant norm — not only the operator norm the source
displays — reads off the same value. -/

/-- **Davis--Kahan 1970, Question 10.4: the ambient functional change is the projector
difference.**

`f(A + H) − f(A) = Q − P`, whence `‖f(A+H) − f(A)‖ = ‖Q − P‖ = ‖sin Θ‖` in every unitarily
invariant norm.  The source's `tan 2θ` bound `δ‖tan 2Θ‖ ≤ 2‖H‖` then applies to the right
side; it is already proved as `tanTwoTheta_ambient_bounded_spectralGap_symmetricNorming_complex`. -/
theorem Question10_4_ambient_functionalChange_complex
    {A H : E →L[ℂ] E} (hA : IsSelfAdjoint A) (hH : IsSelfAdjoint H)
    (hAU : ∀ x ∈ U, A x ∈ U) (hAplusH_V : ∀ x ∈ V, (A + H) x ∈ V)
    {β α δ : ℝ} (hδ : 0 < δ)
    (hA0spec : spectrum ℝ (compressOperator U A) ⊆ Set.Icc β α)
    (hA1spec : spectrum ℝ (compressOperator Uᗮ A) ⊆ Set.Ici (α + δ))
    (hL0spec : spectrum ℝ (compressOperator V (A + H)) ⊆ Set.Iic α)
    (hL1spec : spectrum ℝ (compressOperator Vᗮ (A + H)) ⊆ Set.Ici (α + δ))
    (hHU : ∀ x ∈ U, H x ∈ Uᗮ) (hHUperp : ∀ x ∈ Uᗮ, H x ∈ U)
    {f : ℝ → ℝ} (hf1 : ∀ t ≤ α, f t = 1) (hf0 : ∀ t, α + δ ≤ t → f t = 0) :
    cfc f (A + H) - cfc f A = projectorDifference U V := by
  rw [Question10_4_stepFunction_perturbed_complex V hA hH hAplusH_V hδ hL0spec hL1spec hf1 hf0,
    Question10_4_stepFunction_unperturbed_complex U hA hH hAU hδ hA0spec hA1spec hHU hHUperp hf1
      hf0]
  rfl

/-- **The source's displayed ambient chain**, `‖f(A+H) − f(A)‖ = ‖Q − P‖ = ‖sin Θ‖`, in the
operator norm. -/
theorem Question10_4_ambient_norm_eq_sinTheta_complex
    {A H : E →L[ℂ] E} (hA : IsSelfAdjoint A) (hH : IsSelfAdjoint H)
    (hAU : ∀ x ∈ U, A x ∈ U) (hAplusH_V : ∀ x ∈ V, (A + H) x ∈ V)
    {β α δ : ℝ} (hδ : 0 < δ)
    (hA0spec : spectrum ℝ (compressOperator U A) ⊆ Set.Icc β α)
    (hA1spec : spectrum ℝ (compressOperator Uᗮ A) ⊆ Set.Ici (α + δ))
    (hL0spec : spectrum ℝ (compressOperator V (A + H)) ⊆ Set.Iic α)
    (hL1spec : spectrum ℝ (compressOperator Vᗮ (A + H)) ⊆ Set.Ici (α + δ))
    (hHU : ∀ x ∈ U, H x ∈ Uᗮ) (hHUperp : ∀ x ∈ Uᗮ, H x ∈ U)
    {f : ℝ → ℝ} (hf1 : ∀ t ≤ α, f t = 1) (hf0 : ∀ t, α + δ ≤ t → f t = 0) :
    ‖cfc f (A + H) - cfc f A‖ = ‖projectorDifference U V‖ ∧
      ‖projectorDifference U V‖ = ‖sinAngleOperatorC U V‖ := by
  refine ⟨by rw [Question10_4_ambient_functionalChange_complex U V hA hH hAU hAplusH_V hδ hA0spec
      hA1spec hL0spec hL1spec hHU hHUperp hf1 hf0], ?_⟩
  rw [sinAngleOperatorC, ContinuousLinearMap.norm_modulus, projectorDifference,
    ← norm_neg (U.starProjection - V.starProjection)]
  congr 1
  abel

/-- **Davis--Kahan 1970, Question 10.4: the directed functional change is the directed
sine.**

`(f(A + H) − f(A))E₀ = −P_{Q^⊥}|_U`, whose norm is the source's `‖Q^⊥E₀‖ = ‖sin Θ₀‖` —
`TauCeti.principalSineOperator U V` is the directed sine operator by definition.  The source's
`tan 2θ` residual bound `δ‖tan 2Θ₀‖ ≤ 2‖R‖` applies to the right side and is already proved
as `tanTwoTheta_directed_boundedResidual_blockRepresentative_spectralGap_symmetricNorming_complex`. -/
theorem Question10_4_directed_functionalChange_complex
    {A H : E →L[ℂ] E} (hA : IsSelfAdjoint A) (hH : IsSelfAdjoint H)
    (hAU : ∀ x ∈ U, A x ∈ U) (hAplusH_V : ∀ x ∈ V, (A + H) x ∈ V)
    {β α δ : ℝ} (hδ : 0 < δ)
    (hA0spec : spectrum ℝ (compressOperator U A) ⊆ Set.Icc β α)
    (hA1spec : spectrum ℝ (compressOperator Uᗮ A) ⊆ Set.Ici (α + δ))
    (hL0spec : spectrum ℝ (compressOperator V (A + H)) ⊆ Set.Iic α)
    (hL1spec : spectrum ℝ (compressOperator Vᗮ (A + H)) ⊆ Set.Ici (α + δ))
    (hHU : ∀ x ∈ U, H x ∈ Uᗮ) (hHUperp : ∀ x ∈ Uᗮ, H x ∈ U)
    {f : ℝ → ℝ} (hf1 : ∀ t ≤ α, f t = 1) (hf0 : ∀ t, α + δ ≤ t → f t = 0) :
    (cfc f (A + H) - cfc f A) ∘L U.subtypeL = -TauCeti.principalSineOperator U V := by
  rw [Question10_4_ambient_functionalChange_complex U V hA hH hAU hAplusH_V hδ hA0spec hA1spec
    hL0spec hL1spec hHU hHUperp hf1 hf0]
  refine ContinuousLinearMap.ext fun x => ?_
  have hx : U.starProjection (x : E) = (x : E) :=
    Submodule.starProjection_eq_self_iff.mpr x.2
  simp only [ContinuousLinearMap.comp_apply, Submodule.subtypeL_apply,
    projectorDifference, sub_apply, hx,
    neg_apply, TauCeti.principalSineOperator_apply,
    Submodule.starProjection_orthogonal_val]
  abel

/-- **The source's displayed directed chain**, in the paper's own middle spelling.

`(f(A+H) − f(A))E₀ = f(A+H)E₀ − E₀f(A₀) = −Q^⊥E₀`.  The middle equality is where `f(A₀) = 1`
is used, exactly as in the source. -/
theorem Question10_4_directed_functionalCalculusResidual_complex
    {A H : E →L[ℂ] E} (hA : IsSelfAdjoint A) (hH : IsSelfAdjoint H)
    (hAU : ∀ x ∈ U, A x ∈ U) (hAplusH_V : ∀ x ∈ V, (A + H) x ∈ V)
    {β α δ : ℝ} (hδ : 0 < δ)
    (hA0spec : spectrum ℝ (compressOperator U A) ⊆ Set.Icc β α)
    (hA1spec : spectrum ℝ (compressOperator Uᗮ A) ⊆ Set.Ici (α + δ))
    (hL0spec : spectrum ℝ (compressOperator V (A + H)) ⊆ Set.Iic α)
    (hL1spec : spectrum ℝ (compressOperator Vᗮ (A + H)) ⊆ Set.Ici (α + δ))
    (hHU : ∀ x ∈ U, H x ∈ Uᗮ) (hHUperp : ∀ x ∈ Uᗮ, H x ∈ U)
    {f : ℝ → ℝ} (hf1 : ∀ t ≤ α, f t = 1) (hf0 : ∀ t, α + δ ≤ t → f t = 0) :
    (cfc f (A + H)) ∘L U.subtypeL -
        U.subtypeL ∘L cfc f (compressOperator U A) =
      -TauCeti.principalSineOperator U V := by
  have hP := Question10_4_stepFunction_unperturbed_complex U hA hH hAU hδ hA0spec hA1spec hHU
    hHUperp hf1 hf0
  have h1 := Question10_4_stepFunction_trialBlock_complex U hA hA0spec hf1
  have hmid : U.subtypeL ∘L cfc f (compressOperator U A) = (cfc f A) ∘L U.subtypeL := by
    rw [h1, hP]
    refine ContinuousLinearMap.ext fun x => ?_
    simp [Submodule.starProjection_eq_self_iff.mpr x.2]
  rw [hmid, ← ContinuousLinearMap.sub_comp]
  exact Question10_4_directed_functionalChange_complex U V hA hH hAU hAplusH_V hδ hA0spec hA1spec
    hL0spec hL1spec hHU hHUperp hf1 hf0

/-! ## The real branch

Davis and Kahan work on a real *or* complex Hilbert space, and the `tan 2θ` estimates these
identities feed into already have real endpoints
(`tanTwoTheta_ambient_bounded_spectralGap_symmetricNorming_real` and the directed sibling).  The
  same five
claims over `ℝ`, on `TauCeti.SpectralGap.cfc_eq_starProjection_of_blockGap`.

The ambient identity is stated as `Q − P` directly rather than through
`projectorDifference`, which is a complex-only definition; the norm form then reads
`‖Q − P‖ = ‖sin Θ‖` through `TauCeti.DavisKahan.Angle.Real.sinAngleOperatorRC`, the real sine
operator evaluated in the canonical complexification. -/

section RealScalars

variable {E : Type v} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-- **The gap step function of a reduced real self-adjoint operator is its reducing
projection.**  Real twin of `cfc_gapStep_eq_starProjection_complex`. -/
theorem cfc_gapStep_eq_starProjection_real
    {A : E →L[ℝ] E} (hA : IsSelfAdjoint A)
    (U : Submodule ℝ E) [U.HasOrthogonalProjection]
    (hAU : ∀ x ∈ U, A x ∈ U)
    {α δ : ℝ} (hδ : 0 < δ)
    (hA0spec : spectrum ℝ (compressOperator U A) ⊆ Set.Iic α)
    (hA1spec : spectrum ℝ (compressOperator Uᗮ A) ⊆ Set.Ici (α + δ))
    {f : ℝ → ℝ} (hf1 : ∀ t ≤ α, f t = 1) (hf0 : ∀ t, α + δ ≤ t → f t = 0) :
    cfc f A = U.starProjection := by
  have hAred : A.Reduces U :=
    ContinuousLinearMap.IsSymmetric.reduces_of_invariant
      (ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp hA) hAU
  exact TauCeti.SpectralGap.cfc_eq_starProjection_of_blockGap hA
    (subtypeL_comp_compressOperator_of_invariant A U hAU)
    (subtypeL_comp_compressOperator_of_invariant A Uᗮ hAred.2)
    hδ hA0spec hA1spec hf1 hf0

variable (U V : Submodule ℝ E) [U.HasOrthogonalProjection] [V.HasOrthogonalProjection]

/-- **Question 10.4 over `ℝ`: `f(A) = P`.** -/
theorem Question10_4_stepFunction_unperturbed_real
    {A H : E →L[ℝ] E} (hA : IsSelfAdjoint A) (_hH : IsSelfAdjoint H)
    (hAU : ∀ x ∈ U, A x ∈ U)
    {β α δ : ℝ} (hδ : 0 < δ)
    (hA0spec : spectrum ℝ (compressOperator U A) ⊆ Set.Icc β α)
    (hA1spec : spectrum ℝ (compressOperator Uᗮ A) ⊆ Set.Ici (α + δ))
    (_hHU : ∀ x ∈ U, H x ∈ Uᗮ) (_hHUperp : ∀ x ∈ Uᗮ, H x ∈ U)
    {f : ℝ → ℝ} (hf1 : ∀ t ≤ α, f t = 1) (hf0 : ∀ t, α + δ ≤ t → f t = 0) :
    cfc f A = U.starProjection :=
  cfc_gapStep_eq_starProjection_real hA U hAU hδ (fun _ hr => (hA0spec hr).2) hA1spec hf1 hf0

/-- **Question 10.4 over `ℝ`: `f(A + H) = Q`.**  Same reading of `Q` as the complex branch;
see the module docstring. -/
theorem Question10_4_stepFunction_perturbed_real
    {A H : E →L[ℝ] E} (hA : IsSelfAdjoint A) (hH : IsSelfAdjoint H)
    (hAplusH_V : ∀ x ∈ V, (A + H) x ∈ V)
    {α δ : ℝ} (hδ : 0 < δ)
    (hL0spec : spectrum ℝ (compressOperator V (A + H)) ⊆ Set.Iic α)
    (hL1spec : spectrum ℝ (compressOperator Vᗮ (A + H)) ⊆ Set.Ici (α + δ))
    {f : ℝ → ℝ} (hf1 : ∀ t ≤ α, f t = 1) (hf0 : ∀ t, α + δ ≤ t → f t = 0) :
    cfc f (A + H) = V.starProjection :=
  cfc_gapStep_eq_starProjection_real (hA.add hH) V hAplusH_V hδ hL0spec hL1spec hf1 hf0

/-- **Question 10.4 over `ℝ`: `f(A₀) = 1`.** -/
theorem Question10_4_stepFunction_trialBlock_real
    {A : E →L[ℝ] E} (hA : IsSelfAdjoint A) {β α : ℝ}
    (hA0spec : spectrum ℝ (compressOperator U A) ⊆ Set.Icc β α)
    {f : ℝ → ℝ} (hf1 : ∀ t ≤ α, f t = 1) :
    cfc f (compressOperator U A) = 1 := by
  have hA0sa : IsSelfAdjoint (compressOperator U A) := isSelfAdjoint_compressOperator hA U
  rw [cfc_congr (g := fun _ : ℝ => (1 : ℝ)) (a := compressOperator U A)
    fun t ht => hf1 t (hA0spec ht).2]
  exact cfc_one ℝ (compressOperator U A)

/-- **Question 10.4 over `ℝ`: the ambient functional change is the projector difference.** -/
theorem Question10_4_ambient_functionalChange_real
    {A H : E →L[ℝ] E} (hA : IsSelfAdjoint A) (hH : IsSelfAdjoint H)
    (hAU : ∀ x ∈ U, A x ∈ U) (hAplusH_V : ∀ x ∈ V, (A + H) x ∈ V)
    {β α δ : ℝ} (hδ : 0 < δ)
    (hA0spec : spectrum ℝ (compressOperator U A) ⊆ Set.Icc β α)
    (hA1spec : spectrum ℝ (compressOperator Uᗮ A) ⊆ Set.Ici (α + δ))
    (hL0spec : spectrum ℝ (compressOperator V (A + H)) ⊆ Set.Iic α)
    (hL1spec : spectrum ℝ (compressOperator Vᗮ (A + H)) ⊆ Set.Ici (α + δ))
    (hHU : ∀ x ∈ U, H x ∈ Uᗮ) (hHUperp : ∀ x ∈ Uᗮ, H x ∈ U)
    {f : ℝ → ℝ} (hf1 : ∀ t ≤ α, f t = 1) (hf0 : ∀ t, α + δ ≤ t → f t = 0) :
    cfc f (A + H) - cfc f A = V.starProjection - U.starProjection := by
  rw [Question10_4_stepFunction_perturbed_real V hA hH hAplusH_V hδ hL0spec hL1spec hf1 hf0,
    Question10_4_stepFunction_unperturbed_real U hA hH hAU hδ hA0spec hA1spec hHU hHUperp
      hf1 hf0]

/-- **The source's displayed ambient chain over `ℝ`**, `‖f(A+H) − f(A)‖ = ‖Q − P‖ = ‖sin Θ‖`. -/
theorem Question10_4_ambient_norm_eq_sinTheta_real
    {A H : E →L[ℝ] E} (hA : IsSelfAdjoint A) (hH : IsSelfAdjoint H)
    (hAU : ∀ x ∈ U, A x ∈ U) (hAplusH_V : ∀ x ∈ V, (A + H) x ∈ V)
    {β α δ : ℝ} (hδ : 0 < δ)
    (hA0spec : spectrum ℝ (compressOperator U A) ⊆ Set.Icc β α)
    (hA1spec : spectrum ℝ (compressOperator Uᗮ A) ⊆ Set.Ici (α + δ))
    (hL0spec : spectrum ℝ (compressOperator V (A + H)) ⊆ Set.Iic α)
    (hL1spec : spectrum ℝ (compressOperator Vᗮ (A + H)) ⊆ Set.Ici (α + δ))
    (hHU : ∀ x ∈ U, H x ∈ Uᗮ) (hHUperp : ∀ x ∈ Uᗮ, H x ∈ U)
    {f : ℝ → ℝ} (hf1 : ∀ t ≤ α, f t = 1) (hf0 : ∀ t, α + δ ≤ t → f t = 0) :
    ‖cfc f (A + H) - cfc f A‖ = ‖V.starProjection - U.starProjection‖ ∧
      ‖V.starProjection - U.starProjection‖ =
        ‖TauCeti.DavisKahan.Angle.Real.sinAngleOperatorRC U V‖ := by
  refine ⟨by rw [Question10_4_ambient_functionalChange_real U V hA hH hAU hAplusH_V hδ
      hA0spec hA1spec hL0spec hL1spec hHU hHUperp hf1 hf0], ?_⟩
  rw [TauCeti.DavisKahan.Angle.Real.norm_sinAngleOperatorRC U V]
  show ‖V.starProjection - U.starProjection‖ = U.projectionGap V
  rw [Submodule.projectionGap,
    show V.starProjection - U.starProjection = -(U.starProjection - V.starProjection) by abel,
    norm_neg]

/-- **Question 10.4 over `ℝ`: the directed functional change is the directed sine.** -/
theorem Question10_4_directed_functionalChange_real
    {A H : E →L[ℝ] E} (hA : IsSelfAdjoint A) (hH : IsSelfAdjoint H)
    (hAU : ∀ x ∈ U, A x ∈ U) (hAplusH_V : ∀ x ∈ V, (A + H) x ∈ V)
    {β α δ : ℝ} (hδ : 0 < δ)
    (hA0spec : spectrum ℝ (compressOperator U A) ⊆ Set.Icc β α)
    (hA1spec : spectrum ℝ (compressOperator Uᗮ A) ⊆ Set.Ici (α + δ))
    (hL0spec : spectrum ℝ (compressOperator V (A + H)) ⊆ Set.Iic α)
    (hL1spec : spectrum ℝ (compressOperator Vᗮ (A + H)) ⊆ Set.Ici (α + δ))
    (hHU : ∀ x ∈ U, H x ∈ Uᗮ) (hHUperp : ∀ x ∈ Uᗮ, H x ∈ U)
    {f : ℝ → ℝ} (hf1 : ∀ t ≤ α, f t = 1) (hf0 : ∀ t, α + δ ≤ t → f t = 0) :
    (cfc f (A + H) - cfc f A) ∘L U.subtypeL = -TauCeti.principalSineOperator U V := by
  rw [Question10_4_ambient_functionalChange_real U V hA hH hAU hAplusH_V hδ hA0spec hA1spec
    hL0spec hL1spec hHU hHUperp hf1 hf0]
  refine ContinuousLinearMap.ext fun x => ?_
  have hx : U.starProjection (x : E) = (x : E) :=
    Submodule.starProjection_eq_self_iff.mpr x.2
  simp only [ContinuousLinearMap.comp_apply, Submodule.subtypeL_apply, sub_apply, hx,
    neg_apply, TauCeti.principalSineOperator_apply,
    Submodule.starProjection_orthogonal_val]
  abel

/-- **The source's displayed directed chain over `ℝ`**, in the paper's own middle spelling. -/
theorem Question10_4_directed_functionalCalculusResidual_real
    {A H : E →L[ℝ] E} (hA : IsSelfAdjoint A) (hH : IsSelfAdjoint H)
    (hAU : ∀ x ∈ U, A x ∈ U) (hAplusH_V : ∀ x ∈ V, (A + H) x ∈ V)
    {β α δ : ℝ} (hδ : 0 < δ)
    (hA0spec : spectrum ℝ (compressOperator U A) ⊆ Set.Icc β α)
    (hA1spec : spectrum ℝ (compressOperator Uᗮ A) ⊆ Set.Ici (α + δ))
    (hL0spec : spectrum ℝ (compressOperator V (A + H)) ⊆ Set.Iic α)
    (hL1spec : spectrum ℝ (compressOperator Vᗮ (A + H)) ⊆ Set.Ici (α + δ))
    (hHU : ∀ x ∈ U, H x ∈ Uᗮ) (hHUperp : ∀ x ∈ Uᗮ, H x ∈ U)
    {f : ℝ → ℝ} (hf1 : ∀ t ≤ α, f t = 1) (hf0 : ∀ t, α + δ ≤ t → f t = 0) :
    (cfc f (A + H)) ∘L U.subtypeL -
        U.subtypeL ∘L cfc f (compressOperator U A) =
      -TauCeti.principalSineOperator U V := by
  have hP := Question10_4_stepFunction_unperturbed_real U hA hH hAU hδ hA0spec hA1spec hHU
    hHUperp hf1 hf0
  have h1 := Question10_4_stepFunction_trialBlock_real U hA hA0spec hf1
  have hmid : U.subtypeL ∘L cfc f (compressOperator U A) = (cfc f A) ∘L U.subtypeL := by
    rw [h1, hP]
    refine ContinuousLinearMap.ext fun x => ?_
    simp [Submodule.starProjection_eq_self_iff.mpr x.2]
  rw [hmid, ← ContinuousLinearMap.sub_comp]
  exact Question10_4_directed_functionalChange_real U V hA hH hAU hAplusH_V hδ hA0spec
    hA1spec hL0spec hL1spec hHU hHUperp hf1 hf0

end RealScalars

end

end DavisKahan1970
end TauCeti
