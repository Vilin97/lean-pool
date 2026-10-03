/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, GPT 5.6 High
-/
module

public import LeanPool.DavisKahan.ForTauCeti.Analysis.InnerProductSpace.Spectral.Subspace
public import LeanPool.DavisKahan.ForTauCeti.Analysis.InnerProductSpace.Spectral.Gap
public import LeanPool.DavisKahan.ForTauCeti.Analysis.InnerProductSpace.Sylvester.Bound

/-!
# Finite-dimensional Sylvester equations

The Sylvester operator, spectral-separation predicates, injectivity, and the
canonical finite-dimensional solution.

## Sources

Solvability of `A X - X B = C` under separated spectra is Rosenblum's theorem, and
the norm estimate under a spectral gap is Bhatia--Davis--McIntosh; both are
distilled in
`prose/distilled_literature/BhatiaDavisMcIntosh1983_spectral_subspaces_sylvester.tex`.

## Provenance

*Moved, not restated.*  This file was
`DavisKahan/FiniteDimensional/Sylvester/Basic.lean`
before the whole remaining sin-Θ closure moved into
the staging layer.  Statements, proofs, signatures and namespaces are unchanged;
the declarations already lived in `TauCeti.*`, so the move was a path change and
an import repoint.

Y3(b2) and Y3(b3) are what made it possible: before them this file's import
closure crossed `ForMathlib`, which the `ForTauCeti` layer rule forbids.

-/

@[expose] public section

namespace TauCeti

open TauCeti

open scoped InnerProductSpace BigOperators

variable {𝕜 : Type*} [RCLike 𝕜]
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  [FiniteDimensional 𝕜 E]
variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace 𝕜 F]
  [FiniteDimensional 𝕜 F]
/-- Sylvester operator `X ↦ A X - X B`. -/
noncomputable def sylvesterOperator (A : F →ₗ[𝕜] F) (B : E →ₗ[𝕜] E) :
    (E →ₗ[𝕜] F) →ₗ[𝕜] (E →ₗ[𝕜] F) where
  toFun X := A ∘ₗ X - X ∘ₗ B
  map_add' X Y := by
    ext x
    simp only [LinearMap.comp_apply, LinearMap.add_apply, LinearMap.sub_apply,
      map_add]
    module
  map_smul' c X := by
    ext x
    simp only [LinearMap.comp_apply, LinearMap.smul_apply, LinearMap.sub_apply,
      map_smul, smul_sub, RingHom.id_apply]

/-- Ordered spectral separation for the Sylvester equation. -/
def OrderedSylvesterGap (A : F →ₗ[𝕜] F) (B : E →ₗ[𝕜] E)
    (δ : ℝ) : Prop :=
  OrderedGap B ⊤ A ⊤ δ ∨ OrderedGap A ⊤ B ⊤ δ

/-- Interval/exterior separation with the spectrum of `B` in `[a,b]` and the
spectrum of `A` outside `(a-δ,b+δ)`. -/
def IntervalSylvesterGap (A : F →ₗ[𝕜] F) (B : E →ₗ[𝕜] E)
    (a b δ : ℝ) : Prop :=
  PointSpectrumIn B ⊤ (Set.Icc a b) ∧
    PointSpectrumIn A ⊤ {lam | lam ∉ Set.Ioo (a - δ) (b + δ)}

/-- Interval/exterior separation in either orientation.  The first branch has
the spectrum of `B` in `[a,b]` and that of `A` outside the enlarged interval;
the second branch reverses those roles. -/
def UnorderedIntervalSylvesterGap (A : F →ₗ[𝕜] F) (B : E →ₗ[𝕜] E)
    (a b δ : ℝ) : Prop :=
  IntervalSylvesterGap A B a b δ ∨ IntervalSylvesterGap B A a b δ

/-- The Sylvester operator is injective under positive spectral separation.

The proof is coordinate-free at the API boundary but uses the canonical
self-adjoint eigenbases internally.  Testing `A X - X B = 0` against an
`A`-eigenvector after evaluating at a `B`-eigenvector gives
`(α - β) * ⟪X eβ, eα⟫ = 0`; separation makes the scalar factor nonzero, and
two basis-extensionality steps force `X = 0`.
-/
theorem sylvesterOperator_injective {A : F →ₗ[𝕜] F} {B : E →ₗ[𝕜] E}
    (hA : A.IsSymmetric) (hB : B.IsSymmetric) {δ : ℝ} (hδ : 0 < δ)
    (hgap : PointSpectraSeparated A ⊤ B ⊤ δ) :
    Function.Injective (sylvesterOperator A B) := by
  intro X Y hXY
  have hker : sylvesterOperator A B (X - Y) = 0 := by
    rw [map_sub, hXY, sub_self]
  apply sub_eq_zero.mp
  apply (hB.eigenvectorBasis rfl).toBasis.ext
  intro j
  apply InnerProductSpace.ext_inner_right_basis (hA.eigenvectorBasis rfl).toBasis
  intro i
  let α : ℝ := hA.eigenvalues rfl i
  let β : ℝ := hB.eigenvalues rfl j
  have hα : α ∈ restrictedPointSpectrum A ⊤ :=
    mem_restrictedPointSpectrum Submodule.mem_top
      ((hA.eigenvectorBasis rfl).orthonormal.ne_zero i)
      (by dsimp [α]; exact hA.apply_eigenvectorBasis rfl i)
  have hβ : β ∈ restrictedPointSpectrum B ⊤ :=
    mem_restrictedPointSpectrum Submodule.mem_top
      ((hB.eigenvectorBasis rfl).orthonormal.ne_zero j)
      (by dsimp [β]; exact hB.apply_eigenvectorBasis rfl j)
  have hαβ : α ≠ β := by
    have habs : 0 < |α - β| := lt_of_lt_of_le hδ (hgap α β hα hβ)
    exact sub_ne_zero.mp (abs_pos.mp habs)
  have hαβ𝕜 : (α : 𝕜) ≠ (β : 𝕜) := fun h =>
    hαβ (RCLike.ofReal_injective h)
  have hpoint := LinearMap.congr_fun hker (hB.eigenvectorBasis rfl j)
  -- states the goal with the definition unfolded, in the shape the next step needs;
  -- there is no `_apply` lemma to rewrite with here.
  change A ((X - Y) (hB.eigenvectorBasis rfl j)) -
      (X - Y) (B (hB.eigenvectorBasis rfl j)) = 0 at hpoint
  have heq : A ((X - Y) (hB.eigenvectorBasis rfl j)) =
      (X - Y) (B (hB.eigenvectorBasis rfl j)) :=
    sub_eq_zero.mp hpoint
  have hinner :
      ⟪(X - Y) (hB.eigenvectorBasis rfl j),
          A (hA.eigenvectorBasis rfl i)⟫_𝕜 =
        ⟪(X - Y) (B (hB.eigenvectorBasis rfl j)),
          hA.eigenvectorBasis rfl i⟫_𝕜 := by
    calc
      _ = ⟪A ((X - Y) (hB.eigenvectorBasis rfl j)),
          hA.eigenvectorBasis rfl i⟫_𝕜 :=
        (hA ((X - Y) (hB.eigenvectorBasis rfl j))
          (hA.eigenvectorBasis rfl i)).symm
      _ = _ := congrArg (fun z : F => ⟪z, hA.eigenvectorBasis rfl i⟫_𝕜) heq
  have hscalar :
      (α : 𝕜) * ⟪(X - Y) (hB.eigenvectorBasis rfl j),
          hA.eigenvectorBasis rfl i⟫_𝕜 =
        (β : 𝕜) * ⟪(X - Y) (hB.eigenvectorBasis rfl j),
          hA.eigenvectorBasis rfl i⟫_𝕜 := by
    simpa only [α, β, hA.apply_eigenvectorBasis rfl i,
      hB.apply_eigenvectorBasis rfl j, map_smul, inner_smul_left,
      inner_smul_right, RCLike.conj_ofReal] using hinner
  have hmul :
      ((α : 𝕜) - (β : 𝕜)) *
          ⟪(X - Y) (hB.eigenvectorBasis rfl j),
            hA.eigenvectorBasis rfl i⟫_𝕜 = 0 := by
    rw [sub_mul, hscalar, sub_self]
  have hcoeff := (mul_eq_zero.mp hmul).resolve_left (sub_ne_zero.mpr hαβ𝕜)
  simpa using hcoeff

/-- Unique solution of the finite-dimensional Sylvester equation.

The definition is total: when the Sylvester operator is bijective it uses the
inverse linear equivalence, and otherwise it returns zero.  All computation
lemmas enter the bijective branch explicitly. -/
noncomputable def solveSylvester (A : F →ₗ[𝕜] F) (B : E →ₗ[𝕜] E)
    (C : E →ₗ[𝕜] F) : E →ₗ[𝕜] F := by
  classical
  exact if h : Function.Bijective (sylvesterOperator A B) then
    (LinearEquiv.ofBijective (sylvesterOperator A B) h).symm C
  else
    0

omit [FiniteDimensional 𝕜 E] [FiniteDimensional 𝕜 F] in
private theorem solveSylvester_eq_of_bijective
    (A : F →ₗ[𝕜] F) (B : E →ₗ[𝕜] E) (C : E →ₗ[𝕜] F)
    (h : Function.Bijective (sylvesterOperator A B)) :
    solveSylvester A B C =
      (LinearEquiv.ofBijective (sylvesterOperator A B) h).symm C := by
  classical
  simp only [solveSylvester, dite_eq_left h]

/-- The chosen solution satisfies the Sylvester equation under separation.

Injectivity above implies surjectivity because the Sylvester operator is an
endomorphism of the finite-dimensional map space.  The result is therefore
the `apply_symm_apply` identity of the linear equivalence built from that
bijection; no second coordinate calculation is needed.
-/
theorem sylvesterOperator_solveSylvester {A : F →ₗ[𝕜] F}
    {B : E →ₗ[𝕜] E} (hA : A.IsSymmetric) (hB : B.IsSymmetric)
    {δ : ℝ} (hδ : 0 < δ) (hgap : PointSpectraSeparated A ⊤ B ⊤ δ)
    (C : E →ₗ[𝕜] F) :
    A ∘ₗ solveSylvester A B C - solveSylvester A B C ∘ₗ B = C := by
  have hinj : Function.Injective (sylvesterOperator A B) :=
    sylvesterOperator_injective hA hB hδ hgap
  have hbij : Function.Bijective (sylvesterOperator A B) :=
    ⟨hinj, LinearMap.injective_iff_surjective.mp hinj⟩
  -- states the goal with the definition unfolded, in the shape the next step needs;
  -- there is no `_apply` lemma to rewrite with here.
  change sylvesterOperator A B (solveSylvester A B C) = C
  rw [solveSylvester_eq_of_bijective A B C hbij]
  exact (LinearEquiv.ofBijective (sylvesterOperator A B) hbij).apply_symm_apply C

end TauCeti
