/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, GPT 5.6 High
-/
module

public import LeanPool.DavisKahan.ForTauCeti.Analysis.InnerProductSpace.Spectral.Subspace
public import LeanPool.DavisKahan.ForTauCeti.Analysis.InnerProductSpace.Spectral.Gap
public import LeanPool.DavisKahan.ForTauCeti.Analysis.InnerProductSpace.Residual.Ritz
public import LeanPool.DavisKahan.ForTauCeti.Analysis.InnerProductSpace.AngleGeometry
public import LeanPool.DavisKahan.ForTauCeti.Analysis.InnerProductSpace.Sylvester.Interval
public import LeanPool.DavisKahan.ForTauCeti.Analysis.InnerProductSpace.Sylvester.SpectralDistance
public import LeanPool.DavisKahan.ForTauCeti.Analysis.InnerProductSpace.Residual.AngleEmbedding
public import LeanPool.DavisKahan.ForTauCeti.Analysis.InnerProductSpace.UnitarilyInvariantSeminorm
public import LeanPool.DavisKahan.ForTauCeti.Analysis.InnerProductSpace.RectangularSingularValues
public import LeanPool.DavisKahan.ForTauCeti.Analysis.InnerProductSpace.SinTheta.UnitarilyInvariant
public import LeanPool.DavisKahan.ForTauCeti.Analysis.InnerProductSpace.SinTheta.OperatorNorm
public import LeanPool.DavisKahan.ForTauCeti.Analysis.InnerProductSpace.BoundedOperator.SinTheta
public import LeanPool.DavisKahan.ForTauCeti.Analysis.InnerProductSpace.BoundedOperator.Projector

/-!
# Davis--Kahan `sin Θ`: residual, directed and projector-difference bounds

The three families of `sin Θ` bound that need no domain transport, in increasing
strength of conclusion:

* **Residual form** — `δ ‖sin Θ‖ ≤ ‖R‖` for `R = A X - X M`, in every unitarily
  invariant norm, with the ordered-gap and spectral-distance variants;
* **Directed form** — the one-sided operator-norm and UI-norm bounds on
  `‖(pointSpectralSubspace B t)ᗮ.starProjection ∘L (pointSpectralSubspace A s).starProjection‖`;
* **Two-sided form** — the projector-difference bounds
  `‖P_A - P_B‖ ≤ ε / g` and its factor-two companion.

The **perturbation** wrappers that state these against an operator difference
`B - A`, together with the six private lemmas transporting them across the
canonical isometric inclusion of a subspace, are in the sibling module
`ForTauCeti.Analysis.InnerProductSpace.SinTheta.Perturbation`, which imports this
one.  The seam is exactly that transport: nothing here mentions a domain
isometry, and everything there does.

## Provenance

*Split, not restated.*  This module was the first three sections of
`ForTauCeti/Analysis/InnerProductSpace/SinTheta/Perturbation.lean` until
the point that 1110-line file was divided at its
`## Perturbation form` seam — Tau Ceti's stated limit for a new file is 1000 lines
(`ForTauCeti/README.md` §4), and this was the last module in the library over it.
**No statement, signature, proof, attribute or declaration name changed.**

That file in turn was `DavisKahan/FiniteDimensional/SinTheta/Perturbation.lean`
before the sin-Θ closure moved into the staging layer.
-/

@[expose] public section

namespace TauCeti

open scoped InnerProductSpace BigOperators
open Module (finrank)

variable {𝕜 : Type*} [RCLike 𝕜]
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  [FiniteDimensional 𝕜 E]
variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace 𝕜 F]
  [FiniteDimensional 𝕜 F]

/-! ## Residual form -/

omit [FiniteDimensional 𝕜 F] in
/-- **The projected Sylvester equation, with the coercions discharged.**

`sylvester_sinThetaEmbedding_eq_projectedResidual` states the identity
pointwise; this is the operator form the norm estimates use, and both
`sinTheta_residual_le_of_sylvester` here and
`frobenius_sinTheta_residual_le_of_spectralDistance` in `Perturbation.lean`
unfolded it the same way. -/
theorem sylvester_projectedResidual_eq {A : E →ₗ[𝕜] E} (hA : A.IsSymmetric)
    {U : Submodule 𝕜 E} (hU : IsInvariant A U)
    (hUperp : IsInvariant A Uᗮ) (X : F →ₗᵢ[𝕜] E) (M : F →ₗ[𝕜] F) :
    (A.restrict hUperp) ∘ₗ
        (Uᗮ.orthogonalProjectionOnto.toLinearMap ∘ₗ X.toLinearMap) -
      (Uᗮ.orthogonalProjectionOnto.toLinearMap ∘ₗ X.toLinearMap) ∘ₗ M =
      Uᗮ.orthogonalProjectionOnto.toLinearMap ∘ₗ residual A X M := by
  ext x
  have hx := LinearMap.congr_fun
    (sylvester_sinThetaEmbedding_eq_projectedResidual hA hU X M) x
  simpa [sinThetaEmbedding, complementaryProjection, projection,
    LinearMap.comp_apply] using hx

/-- **The residual `sin Θ` reduction, with the Sylvester estimate as a
hypothesis.**

Every residual `sin Θ` theorem in this file does the same forty-seven lines
before it does anything specific: restrict `A` to `Uᗮ`, compress the isometry
and the residual to that block, transport the norm along `Uᗮ.subtypeₗᵢ`, check
the Sylvester equation, and bound the compression of the residual by the
residual.  What distinguishes them is only *which* Sylvester estimate closes the
last step, so that estimate is the hypothesis here.

The constant `c` is a parameter rather than `1` because the general
disjoint-spectrum form carries `π / 2`; without it this lemma would serve two of
the three theorems and look like the shape was wrong. -/
private theorem sinTheta_residual_le_of_sylvester
    (N : UnitarilyInvariantSeminorm 𝕜 F E)
    {A : E →ₗ[𝕜] E} (hA : A.IsSymmetric) {U : Submodule 𝕜 E}
    [U.HasOrthogonalProjection] (hU : IsInvariant A U)
    (X : F →ₗᵢ[𝕜] E) {M : F →ₗ[𝕜] F} {δ c : ℝ} (hc : 0 ≤ c)
    (hsylv : ∀ Y C : F →ₗ[𝕜] (Uᗮ : Submodule 𝕜 E),
      A.restrict (isInvariant_orthogonal_of_isSymmetric hA hU) ∘ₗ Y - Y ∘ₗ M = C →
        δ * (N.codomainIsometryTransport Uᗮ.subtypeₗᵢ) Y
          ≤ c * (N.codomainIsometryTransport Uᗮ.subtypeₗᵢ) C) :
    δ * N (sinThetaEmbedding U X) ≤ c * N (residual A X M) := by
  have hUperp : IsInvariant A Uᗮ := isInvariant_orthogonal_of_isSymmetric hA hU
  let AU : Uᗮ →ₗ[𝕜] Uᗮ := A.restrict hUperp
  let Y : F →ₗ[𝕜] Uᗮ :=
    Uᗮ.orthogonalProjectionOnto.toLinearMap ∘ₗ X.toLinearMap
  let C : F →ₗ[𝕜] Uᗮ :=
    Uᗮ.orthogonalProjectionOnto.toLinearMap ∘ₗ residual A X M
  let NU : UnitarilyInvariantSeminorm 𝕜 F Uᗮ :=
    N.codomainIsometryTransport Uᗮ.subtypeₗᵢ
  have hAU : AU.IsSymmetric := hA.restrict_invariant hUperp
  have hEq : AU ∘ₗ Y - Y ∘ₗ M = C :=
    sylvester_projectedResidual_eq hA hU hUperp X M
  have hY : NU Y = N (sinThetaEmbedding U X) := by
    -- states the goal with the local norm `NU` unfolded, which is the form `congr 1`
    -- can close. `simp only [NU]` normalises further and leaves goals `congr` no
    -- longer discharges -- tried, and it fails here.
    change N (Uᗮ.subtypeₗᵢ.toLinearMap ∘ₗ Y) = N (sinThetaEmbedding U X)
    congr 1
  have hC : NU C =
      N (complementaryProjection U ∘ₗ residual A X M) := by
    -- states the goal with the local norm `NU` unfolded, which is the form `congr 1`
    -- can close. `simp only [NU]` normalises further and leaves goals `congr` no
    -- longer discharges -- tried, and it fails here.
    change N (Uᗮ.subtypeₗᵢ.toLinearMap ∘ₗ C) =
      N (complementaryProjection U ∘ₗ residual A X M)
    congr 1
  have hproj : ‖(complementaryProjection U).toContinuousLinearMap‖ ≤ 1 := by
    refine (complementaryProjection U).toContinuousLinearMap.opNorm_le_bound
      zero_le_one fun x => ?_
    -- names the projection application so the operator-norm bound applies directly.
    change ‖Uᗮ.starProjection x‖ ≤ 1 * ‖x‖
    simpa using Uᗮ.norm_starProjection_apply_le x
  have hC_le : NU C ≤ N (residual A X M) := by
    rw [hC]
    calc
      N (complementaryProjection U ∘ₗ residual A X M)
          ≤ ‖(complementaryProjection U).toContinuousLinearMap‖ *
              N (residual A X M) :=
        N.comp_le_opNorm_mul _ _
      _ ≤ 1 * N (residual A X M) :=
        mul_le_mul_of_nonneg_right hproj (N.nonneg _)
      _ = N (residual A X M) := one_mul _
  have hS := hsylv Y C hEq
  rw [hY] at hS
  exact hS.trans (mul_le_mul_of_nonneg_left hC_le hc)

/-- **Davis--Kahan `sin Θ`, residual form, every UI norm.**

The spectrum of the approximate coordinate operator `M` lies in `[a,b]`, the
unwanted spectrum of `A` on `Uᗮ` lies outside `(a-δ,b+δ)`, and `R = AX-XM`.
Then `δ ‖sin Θ‖ ≤ ‖R‖`.
-/
theorem sinTheta_residual_le
    (N : UnitarilyInvariantSeminorm 𝕜 F E)
    {A : E →ₗ[𝕜] E} (hA : A.IsSymmetric) {U : Submodule 𝕜 E}
    [U.HasOrthogonalProjection] (hU : IsInvariant A U)
    (X : F →ₗᵢ[𝕜] E) {M : F →ₗ[𝕜] F} (hM : M.IsSymmetric)
    {a b δ : ℝ} (hδ : 0 < δ)
    (hMspec : PointSpectrumIn M ⊤ (Set.Icc a b))
    (hAspec : PointSpectrumIn A Uᗮ {lam | lam ∉ Set.Ioo (a - δ) (b + δ)}) :
    δ * N (sinThetaEmbedding U X) ≤ N (residual A X M) := by
  refine (sinTheta_residual_le_of_sylvester (c := 1) N hA hU X zero_le_one
    ?_).trans_eq (one_mul _)
  intro Y C hEq
  have hgap : IntervalSylvesterGap
      (A.restrict (isInvariant_orthogonal_of_isSymmetric hA hU)) M a b δ := by
    refine ⟨hMspec, ?_⟩
    exact (pointSpectrumIn_restrict_iff A (isInvariant_orthogonal_of_isSymmetric hA hU) _).2 hAspec
  exact (uiNorm_sylvester_le_of_intervalGap (N.codomainIsometryTransport Uᗮ.subtypeₗᵢ)
    (hA.restrict_invariant (isInvariant_orthogonal_of_isSymmetric hA hU)) hM hδ hgap
    hEq).trans_eq (one_mul _).symm

/-- Ordered half-line residual form.
-/
theorem sinTheta_residual_le_of_orderedGap
    (N : UnitarilyInvariantSeminorm 𝕜 F E)
    {A : E →ₗ[𝕜] E} (hA : A.IsSymmetric) {U : Submodule 𝕜 E}
    [U.HasOrthogonalProjection] (hU : IsInvariant A U)
    (X : F →ₗᵢ[𝕜] E) {M : F →ₗ[𝕜] F} (hM : M.IsSymmetric)
    {δ : ℝ} (hδ : 0 < δ) (hgap : OrderedGap M ⊤ A Uᗮ δ) :
    δ * N (sinThetaEmbedding U X) ≤ N (residual A X M) := by
  refine (sinTheta_residual_le_of_sylvester (c := 1) N hA hU X zero_le_one
    ?_).trans_eq (one_mul _)
  intro Y C hEq
  have hUperp := isInvariant_orthogonal_of_isSymmetric hA hU
  have hgap' : OrderedSylvesterGap (A.restrict hUperp) M δ := by
    left
    intro lam μ hlam hμ
    apply hgap lam μ hlam
    -- restates the spectrum membership through the restriction, the form the
    -- following step matches.
    change μ ∈ restrictedPointSpectrum (A.restrict hUperp) ⊤ at hμ
    rw [restrictedPointSpectrum_restrict A hUperp] at hμ
    exact hμ
  exact (uiNorm_sylvester_le_of_orderedGap (N.codomainIsometryTransport Uᗮ.subtypeₗᵢ)
    (hA.restrict_invariant hUperp) hM hδ hgap' hEq).trans_eq (one_mul _).symm

/-- General disjoint-spectrum residual form.  The `π/2` loss is the
Bhatia--Davis--McIntosh extension, not the sharp interval/exterior theorem.
The restriction and projection proof below is complete; the only open input is
`kyFan_sylvester_le_of_spectralDistance` in the Sylvester layer.
-/
theorem sinTheta_residual_le_of_spectralDistance
    (N : UnitarilyInvariantSeminorm 𝕜 F E)
    {A : E →ₗ[𝕜] E} (hA : A.IsSymmetric) {U : Submodule 𝕜 E}
    [U.HasOrthogonalProjection] (hU : IsInvariant A U)
    (X : F →ₗᵢ[𝕜] E) {M : F →ₗ[𝕜] F} (hM : M.IsSymmetric)
    {δ : ℝ} (hδ : 0 < δ)
    (hgap : PointSpectraSeparated M ⊤ A Uᗮ δ) :
    δ * N (sinThetaEmbedding U X) ≤ (Real.pi / 2) * N (residual A X M) := by
  refine sinTheta_residual_le_of_sylvester (c := Real.pi / 2) N hA hU X
    (by positivity) ?_
  intro Y C hEq
  have hUperp := isInvariant_orthogonal_of_isSymmetric hA hU
  have hgap' : PointSpectraSeparated (A.restrict hUperp) ⊤ M ⊤ δ := by
    intro lam μ hlam hμ
    have hlam' : lam ∈ restrictedPointSpectrum A Uᗮ := by
      rw [← restrictedPointSpectrum_restrict A hUperp]
      exact hlam
    have hsep := hgap μ lam hμ hlam'
    simpa [abs_sub_comm] using hsep
  exact uiNorm_sylvester_le_of_spectralDistance
    (N.codomainIsometryTransport Uᗮ.subtypeₗᵢ)
    (hA.restrict_invariant hUperp) hM hδ hgap' hEq

/-- **One-sided operator-norm Davis--Kahan `sin Θ` theorem (spectral-hypothesis
form).**  If `A, B` are symmetric, `U` reduces `A` with `U`-carried spectrum
`≥ c + g`, `V` reduces `B` with `V`-carried spectrum `≤ c`, and
`‖(B − A) x‖ ≤ ε ‖x‖`, then

`‖P_V ∘ P_U‖ ≤ ε / g`.

`‖P_V P_U‖` is the sine of the directed angle between the high `A`-block `U` and
the high `B`-block `Vᗮ`.  **The finite result is dispatched from the
arbitrary-dimension lemma** `Submodule.sinTheta_directed_coercive`: the finite
operators are converted to bounded operators, and the *only* finite-dimensional
ingredient is the eigenbasis spectrum ⟹ coercivity bridge
(`lowerFormBound_of_pointSpectrumIn` / `upperFormBound_of_pointSpectrumIn`).  The whole sin-Θ
construction and Sylvester estimate are the dimension-free infinite-dimensional
core. -/
theorem opNorm_directed_sinTheta_le {A B : E →ₗ[𝕜] E}
    (hA : A.IsSymmetric) (hB : B.IsSymmetric)
    {U V : Submodule 𝕜 E} [U.HasOrthogonalProjection] [V.HasOrthogonalProjection]
    (hU : IsInvariant A U) (hV : IsInvariant B V)
    {c g ε : ℝ} (hg : 0 < g)
    (hUspec : PointSpectrumIn A U (Set.Ici (c + g)))
    (hVspec : PointSpectrumIn B V (Set.Iic c))
    (hε0 : 0 ≤ ε) (hε : ∀ x, ‖(B - A) x‖ ≤ ε * ‖x‖) :
    ‖(V.starProjection ∘L U.starProjection : E →L[𝕜] E)‖ ≤ ε / g := by
  have : CompleteSpace E := FiniteDimensional.complete 𝕜 E
  set Ac : E →L[𝕜] E := A.toContinuousLinearMap with hAc
  set Bc : E →L[𝕜] E := B.toContinuousLinearMap with hBc
  have hApp : ∀ x, Ac x = A x := fun _ => rfl
  have hBpp : ∀ x, Bc x = B x := fun _ => rfl
  have hAself : Ac.IsSymmetric := fun x y => hA x y
  have hBself : Bc.IsSymmetric := fun x y => hB x y
  have hUperp : IsInvariant A Uᗮ := isInvariant_orthogonal_of_isSymmetric hA hU
  have hVperp : IsInvariant B Vᗮ := isInvariant_orthogonal_of_isSymmetric hB hV
  have hUred : Ac.Reduces U := ⟨fun x hx => hU x hx, fun x hx => hUperp x hx⟩
  have hVred : Bc.Reduces V := ⟨fun x hx => hV x hx, fun x hx => hVperp x hx⟩
  have hUc : ∀ x ∈ U, (c + g) * ‖x‖ ^ 2 ≤ RCLike.re ⟪Ac x, x⟫_𝕜 :=
    fun x hx => lowerFormBound_of_pointSpectrumIn hA hU hUspec x hx
  have hVc : ∀ x ∈ V, RCLike.re ⟪Bc x, x⟫_𝕜 ≤ c * ‖x‖ ^ 2 :=
    fun x hx => upperFormBound_of_pointSpectrumIn hB hV hVspec x hx
  have hExt := Submodule.sinTheta_directed_coercive hAself hBself hUred hVred hg hUc hVc
  have hnorm : ‖(Bc - Ac : E →L[𝕜] E)‖ ≤ ε := by
    refine ContinuousLinearMap.opNorm_le_bound _ hε0 fun x => ?_
    have hsub : (Bc - Ac) x = (B - A) x := by
      simp only [sub_apply, LinearMap.sub_apply, hApp, hBpp]
    rw [hsub]; exact hε x
  calc ‖(V.starProjection ∘L U.starProjection : E →L[𝕜] E)‖
      ≤ ‖(Bc - Ac : E →L[𝕜] E)‖ / g := hExt
    _ ≤ ε / g := by gcongr

/-- **Spectral-projection directed operator-norm `sin Θ` theorem.**  The canonical
spectral subspaces automatically reduce their operators, so the one-sided bound
holds for `‖P_{spec B t} ∘ P_{spec A s}‖` under the corresponding spectral-gap
hypotheses.  This is the directed operator-norm form of the canonical
spectral-projector Davis--Kahan theorem.

Related Lean work: `YuanheZ/lean-stat-learning-theory`,
`SLT/MatrixInfra/Perturb.lean` at commit
`216e578c9576bab6b0abc3ba6c65762536768e96`, proves a closely matching
interval/set-separated cross-projection estimate named
`davisKahan_spectralProjection_hdp`.  That proof is finite-dimensional and
centered-shift based; this theorem instead exposes the local `PointSpectrumIn` API
and dispatches through the dimension-free coercive Sylvester core. -/
theorem opNorm_pointSpectralSubspace_directed_sinTheta_le {A B : E →ₗ[𝕜] E}
    (hA : A.IsSymmetric) (hB : B.IsSymmetric) {s t : Set ℝ}
    {c g ε : ℝ} (hg : 0 < g)
    (hUspec : PointSpectrumIn A (pointSpectralSubspace A s) (Set.Ici (c + g)))
    (hVspec : PointSpectrumIn B (pointSpectralSubspace B t) (Set.Iic c))
    (hε0 : 0 ≤ ε) (hε : ∀ x, ‖(B - A) x‖ ≤ ε * ‖x‖) :
    ‖((pointSpectralSubspace B t).starProjection ∘L
        (pointSpectralSubspace A s).starProjection : E →L[𝕜] E)‖ ≤ ε / g :=
  opNorm_directed_sinTheta_le hA hB (isInvariant_pointSpectralSubspace A s)
    (isInvariant_pointSpectralSubspace B t) hg hUspec hVspec hε0 hε

/-- **Every-unitarily-invariant-norm directed `sin Θ` theorem, spectral
hypothesis form.**  If `A, B` are symmetric, `U` reduces `A` with `U`-carried
spectrum `≥ c + g`, and `V` reduces `B` with `V`-carried spectrum `≤ c`, then
`N (P_V ∘ P_U) ≤ N (B − A) / g` for every unitarily invariant norm `N`.
The quadratic-form hypotheses of the invariant-subspace theorem are supplied
by the spectral coercivity bridges. -/
theorem uiNorm_directed_sinTheta_le (N : UnitarilyInvariantSeminorm 𝕜 E E)
    {A B : E →ₗ[𝕜] E} (hA : A.IsSymmetric) (hB : B.IsSymmetric)
    {U V : Submodule 𝕜 E} [U.HasOrthogonalProjection] [V.HasOrthogonalProjection]
    (hU : IsInvariant A U) (hV : IsInvariant B V)
    {c g : ℝ} (hg : 0 < g)
    (hUspec : PointSpectrumIn A U (Set.Ici (c + g)))
    (hVspec : PointSpectrumIn B V (Set.Iic c)) :
    N ((V.starProjection ∘L U.starProjection : E →L[𝕜] E) : E →ₗ[𝕜] E)
      ≤ N (B - A) / g := by
  have : CompleteSpace E := FiniteDimensional.complete 𝕜 E
  exact UnitarilyInvariantSeminorm.apply_starProjection_comp_starProjection_le N
    hA hB hU hV hg
    (fun x hx => lowerFormBound_of_pointSpectrumIn hA hU hUspec x hx)
    (fun x hx => upperFormBound_of_pointSpectrumIn hB hV hVspec x hx)

/-- **Every-unitarily-invariant-norm directed `sin Θ` theorem for the
canonical spectral subspaces.**  The canonical spectral subspaces reduce
their operators automatically, so the full unitarily-invariant-norm `sin Θ`
bound holds for `N (P_{spec B t} ∘ P_{spec A s})` under the spectral-gap
hypotheses alone. -/
theorem uiNorm_pointSpectralSubspace_directed_sinTheta_le
    (N : UnitarilyInvariantSeminorm 𝕜 E E)
    {A B : E →ₗ[𝕜] E} (hA : A.IsSymmetric) (hB : B.IsSymmetric) {s t : Set ℝ}
    {c g : ℝ} (hg : 0 < g)
    (hUspec : PointSpectrumIn A (pointSpectralSubspace A s) (Set.Ici (c + g)))
    (hVspec : PointSpectrumIn B (pointSpectralSubspace B t) (Set.Iic c)) :
    N (((pointSpectralSubspace B t).starProjection ∘L
        (pointSpectralSubspace A s).starProjection : E →L[𝕜] E) : E →ₗ[𝕜] E)
      ≤ N (B - A) / g :=
  uiNorm_directed_sinTheta_le N hA hB (isInvariant_pointSpectralSubspace A s)
    (isInvariant_pointSpectralSubspace B t) hg hUspec hVspec

/-! ## Two-sided projector-difference operator-norm form

The generic `RCLike` projector theorem now supplies the sharp factor-one bound
without an equal-rank hypothesis.  Finite-dimensional spectral decomposition is
used only to turn the four `PointSpectrumIn` assumptions into quadratic-form bounds;
all projection geometry and Sylvester analysis are inherited from the supported
dimension-free core. -/

/-- **Sharp finite-dimensional operator-norm Davis--Kahan projector theorem.**
With two-sided spectral gaps for the selected and complementary blocks of both
operators,

`‖P_U - P_W‖ ≤ ε / g`.

This is a finite spectral specialization of
`Submodule.opNorm_starProjection_sub_le_of_coercive`.  In particular, there is
no rank hypothesis and no factor-two loss. -/
theorem opNorm_starProjection_sub_le {A B : E →ₗ[𝕜] E}
    (hA : A.IsSymmetric) (hB : B.IsSymmetric)
    {U W : Submodule 𝕜 E} [U.HasOrthogonalProjection] [W.HasOrthogonalProjection]
    (hU : IsInvariant A U) (hW : IsInvariant B W)
    {c g ε : ℝ} (hg : 0 < g)
    (hUhi : PointSpectrumIn A U (Set.Ici (c + g)))
    (hUlo : PointSpectrumIn A Uᗮ (Set.Iic c))
    (hWhi : PointSpectrumIn B W (Set.Ici (c + g)))
    (hWlo : PointSpectrumIn B Wᗮ (Set.Iic c))
    (hε0 : 0 ≤ ε) (hε : ∀ x, ‖(B - A) x‖ ≤ ε * ‖x‖) :
    ‖(U.starProjection - W.starProjection : E →L[𝕜] E)‖ ≤ ε / g := by
  have : CompleteSpace E := FiniteDimensional.complete 𝕜 E
  let Ac : E →L[𝕜] E := A.toContinuousLinearMap
  let Bc : E →L[𝕜] E := B.toContinuousLinearMap
  have hAself : Ac.IsSymmetric := by
    intro x y
    -- states the symmetry goal as the inner-product identity the structure field
    -- expects.
    change ⟪A x, y⟫_𝕜 = ⟪x, A y⟫_𝕜
    exact hA x y
  have hBself : Bc.IsSymmetric := by
    intro x y
    -- states the symmetry goal as the inner-product identity the structure field
    -- expects.
    change ⟪B x, y⟫_𝕜 = ⟪x, B y⟫_𝕜
    exact hB x y
  have hUperp : IsInvariant A Uᗮ := isInvariant_orthogonal_of_isSymmetric hA hU
  have hWperp : IsInvariant B Wᗮ := isInvariant_orthogonal_of_isSymmetric hB hW
  have hUred : Ac.Reduces U :=
    ⟨fun x hx => by simpa [Ac] using hU x hx,
      fun x hx => by simpa [Ac] using hUperp x hx⟩
  have hWred : Bc.Reduces W :=
    ⟨fun x hx => by simpa [Bc] using hW x hx,
      fun x hx => by simpa [Bc] using hWperp x hx⟩
  have hUhiForm : ∀ x ∈ U,
      (c + g) * ‖x‖ ^ 2 ≤ RCLike.re ⟪Ac x, x⟫_𝕜 :=
    fun x hx => by simpa [Ac] using lowerFormBound_of_pointSpectrumIn hA hU hUhi x hx
  have hUloForm : ∀ x ∈ Uᗮ,
      RCLike.re ⟪Ac x, x⟫_𝕜 ≤ c * ‖x‖ ^ 2 :=
    fun x hx => by simpa [Ac] using upperFormBound_of_pointSpectrumIn hA hUperp hUlo x hx
  have hWhiForm : ∀ x ∈ W,
      (c + g) * ‖x‖ ^ 2 ≤ RCLike.re ⟪Bc x, x⟫_𝕜 :=
    fun x hx => by simpa [Bc] using lowerFormBound_of_pointSpectrumIn hB hW hWhi x hx
  have hWloForm : ∀ x ∈ Wᗮ,
      RCLike.re ⟪Bc x, x⟫_𝕜 ≤ c * ‖x‖ ^ 2 :=
    fun x hx => by simpa [Bc] using upperFormBound_of_pointSpectrumIn hB hWperp hWlo x hx
  have hcore := Submodule.opNorm_starProjection_sub_le_of_coercive
    hAself hBself hUred hWred hg hUhiForm hUloForm hWhiForm hWloForm
  have hnorm : ‖(Bc - Ac : E →L[𝕜] E)‖ ≤ ε := by
    refine ContinuousLinearMap.opNorm_le_bound _ hε0 fun x => ?_
    simpa [Ac, Bc] using hε x
  exact hcore.trans (by gcongr)

/-- Compatibility corollary with the older factor-two right-hand side.
The sharp theorem `opNorm_starProjection_sub_le` is strictly stronger. -/
theorem opNorm_starProjection_sub_le_two {A B : E →ₗ[𝕜] E}
    (hA : A.IsSymmetric) (hB : B.IsSymmetric)
    {U W : Submodule 𝕜 E} [U.HasOrthogonalProjection] [W.HasOrthogonalProjection]
    (hU : IsInvariant A U) (hW : IsInvariant B W)
    {c g ε : ℝ} (hg : 0 < g)
    (hUhi : PointSpectrumIn A U (Set.Ici (c + g))) (hUlo : PointSpectrumIn A Uᗮ (Set.Iic c))
    (hWhi : PointSpectrumIn B W (Set.Ici (c + g))) (hWlo : PointSpectrumIn B Wᗮ (Set.Iic c))
    (hε0 : 0 ≤ ε) (hε : ∀ x, ‖(B - A) x‖ ≤ ε * ‖x‖) :
    ‖(U.starProjection - W.starProjection : E →L[𝕜] E)‖ ≤ 2 * (ε / g) := by
  have hsharp := opNorm_starProjection_sub_le hA hB hU hW hg
    hUhi hUlo hWhi hWlo hε0 hε
  have hnonneg : 0 ≤ ε / g := div_nonneg hε0 hg.le
  nlinarith

/-- **Sharp spectral-subspace projector theorem.**  Canonical finite
spectral subspaces reduce their operators automatically, so the sharp
factor-one theorem applies directly.

The cross-projection endpoint in
`YuanheZ/lean-stat-learning-theory/SLT/MatrixInfra/Perturb.lean` is related but
does not replace this projector-difference theorem: the present result uses
both selected and complementary gaps and inherits the factor-one identity from
the generic projection geometry. -/
theorem opNorm_pointSpectralSubspace_sub_le {A B : E →ₗ[𝕜] E}
    (hA : A.IsSymmetric) (hB : B.IsSymmetric) {s t : Set ℝ}
    {c g ε : ℝ} (hg : 0 < g)
    (hAhi : PointSpectrumIn A (pointSpectralSubspace A s) (Set.Ici (c + g)))
    (hAlo : PointSpectrumIn A (pointSpectralSubspace A s)ᗮ (Set.Iic c))
    (hBhi : PointSpectrumIn B (pointSpectralSubspace B t) (Set.Ici (c + g)))
    (hBlo : PointSpectrumIn B (pointSpectralSubspace B t)ᗮ (Set.Iic c))
    (hε0 : 0 ≤ ε) (hε : ∀ x, ‖(B - A) x‖ ≤ ε * ‖x‖) :
    ‖((pointSpectralSubspace A s).starProjection
        - (pointSpectralSubspace B t).starProjection : E →L[𝕜] E)‖ ≤ ε / g :=
  opNorm_starProjection_sub_le hA hB (isInvariant_pointSpectralSubspace A s)
    (isInvariant_pointSpectralSubspace B t) hg hAhi hAlo hBhi hBlo hε0 hε

/-- **Two-sided operator-norm spectral-projector Davis--Kahan theorem.**  The
projector-difference bound for the canonical spectral subspaces (they reduce
their operators automatically). -/
theorem opNorm_pointSpectralSubspace_sub_le_two {A B : E →ₗ[𝕜] E}
    (hA : A.IsSymmetric) (hB : B.IsSymmetric) {s t : Set ℝ}
    {c g ε : ℝ} (hg : 0 < g)
    (hAhi : PointSpectrumIn A (pointSpectralSubspace A s) (Set.Ici (c + g)))
    (hAlo : PointSpectrumIn A (pointSpectralSubspace A s)ᗮ (Set.Iic c))
    (hBhi : PointSpectrumIn B (pointSpectralSubspace B t) (Set.Ici (c + g)))
    (hBlo : PointSpectrumIn B (pointSpectralSubspace B t)ᗮ (Set.Iic c))
    (hε0 : 0 ≤ ε) (hε : ∀ x, ‖(B - A) x‖ ≤ ε * ‖x‖) :
    ‖((pointSpectralSubspace A s).starProjection
        - (pointSpectralSubspace B t).starProjection : E →L[𝕜] E)‖ ≤ 2 * (ε / g) :=
  opNorm_starProjection_sub_le_two hA hB (isInvariant_pointSpectralSubspace A s)
    (isInvariant_pointSpectralSubspace B t) hg hAhi hAlo hBhi hBlo hε0 hε

end TauCeti
