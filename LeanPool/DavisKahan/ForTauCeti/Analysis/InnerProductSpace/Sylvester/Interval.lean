/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, GPT 5.6 High
-/
module

public import LeanPool.DavisKahan.ForTauCeti.Analysis.InnerProductSpace.Sylvester.Basic
public import LeanPool.DavisKahan.ForTauCeti.Analysis.InnerProductSpace.Sylvester.Internal.SpectralBounds
public import LeanPool.DavisKahan.ForTauCeti.Analysis.InnerProductSpace.UnitarilyInvariantSeminorm
public import LeanPool.DavisKahan.ForTauCeti.Analysis.InnerProductSpace.Sylvester.Bound

/-!
# Ordered and interval/exterior Sylvester estimates

Sharp constant-one operator and rectangular unitarily invariant norm bounds
under ordered or interval/exterior spectral separation.

## Sources

The interval and exterior forms of the Sylvester estimate follow
Bhatia--Davis--McIntosh
(`prose/distilled_literature/BhatiaDavisMcIntosh1983_spectral_subspaces_sylvester.tex`);
the sharp `π / 2` constant and its Fourier route are distilled in
`prose/distilled_literature/AlbeverioMakarovMotovilov2001_sylvester_fourier_pi_over_two.tex`.

## Provenance

*Moved, not restated.*  This file was
`DavisKahan/FiniteDimensional/Sylvester/Interval.lean`
before the whole remaining sin-Θ closure moved into
the staging layer.  Statements, proofs, signatures and namespaces are unchanged;
the declarations already lived in `TauCeti.*`, so the move was a path change and
an import repoint.

Y3(b2) and Y3(b3) are what made it possible: before them this file's import
closure crossed `ForMathlib`, which the `ForTauCeti` layer rule forbids.

-/

public section

namespace TauCeti

open TauCeti

open scoped InnerProductSpace BigOperators

variable {𝕜 : Type*} [RCLike 𝕜]
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  [FiniteDimensional 𝕜 E]
variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace 𝕜 F]
  [FiniteDimensional 𝕜 F]
omit [FiniteDimensional 𝕜 E] [FiniteDimensional 𝕜 F] in
/-- **A Sylvester equation is invariant under a common scalar shift.**  Replacing
`A` and `B` by `A - m` and `B - m` leaves `A ∘ₗ X - X ∘ₗ B` unchanged, because
the two `m • X` terms cancel.

It is the opening move of every shift-and-invert argument here, and was inlined
in each of them.  Since 2026-07-30 the operator-norm interval/exterior estimate
is the unitarily-invariant one at `opNorm` rather than a parallel proof, so the
remaining consumers are `uiNorm_sylvester_le_of_intervalGap` and its
ordered-gap sibling. -/
private theorem sylvester_sub_smul_id (A : F →ₗ[𝕜] F) (B : E →ₗ[𝕜] E)
    (X C : E →ₗ[𝕜] F) (m : 𝕜) (hEq : A ∘ₗ X - X ∘ₗ B = C) :
    (A - m • LinearMap.id) ∘ₗ X - X ∘ₗ (B - m • LinearMap.id) = C := by
  ext x
  have hx := LinearMap.congr_fun hEq x
  simp only [LinearMap.comp_apply, LinearMap.sub_apply,
    LinearMap.smul_apply, LinearMap.id_apply, map_sub, map_smul]
  simp only [LinearMap.comp_apply, LinearMap.sub_apply] at hx
  rw [← hx]
  module

/-- **A positive symmetric operator bounded below in norm has its eigenvalues
bounded below.**  If `‖H y‖ ≥ c ‖y‖` for every `y` and `H` is positive, then every
eigenvalue of `H` is at least `c`.

The statement is about `TauCeti.operatorAbs`, not about Sylvester equations, and it is
used by both interval-gap bounds below. -/
private theorem le_eigenvalues_of_norm_lower_bound {H : F →ₗ[𝕜] F}
    (hpos : H.IsPositive) (hHsym : H.IsSymmetric) {c : ℝ}
    (hlow : ∀ y, c * ‖y‖ ≤ ‖H y‖) (i : Fin (Module.finrank 𝕜 F)) :
    c ≤ hHsym.eigenvalues rfl i := by
  have hi : c * ‖hHsym.eigenvectorBasis rfl i‖ ≤ ‖H (hHsym.eigenvectorBasis rfl i)‖ :=
    hlow (hHsym.eigenvectorBasis rfl i)
  have hnonneg := hpos.nonneg_eigenvalues rfl i
  simp only [hHsym.apply_eigenvectorBasis rfl i, norm_smul, RCLike.norm_ofReal,
    abs_of_nonneg hnonneg,
    (hHsym.eigenvectorBasis rfl).orthonormal.norm_eq_one, mul_one, mul_one] at hi
  exact hi

omit [FiniteDimensional 𝕜 E] in
/-- **A norm lower bound on `S` becomes a quadratic-form lower bound on `|S|`.**
`c ‖y‖ ≤ ‖S y‖` for every `y` gives `c ‖y‖² ≤ re ⟪|S| y, y⟫`, through the
eigenvalues of the positive symmetric `|S|`.

Both interval-gap bounds below need exactly this, and each was deriving it in
four steps. -/
private theorem le_re_inner_operatorAbs_self_of_norm_lower_bound
    {S : F →ₗ[𝕜] F} {c : ℝ} (hlow : ∀ y, c * ‖y‖ ≤ ‖S y‖) :
    ∀ y, c * ‖y‖ ^ 2 ≤ RCLike.re ⟪TauCeti.operatorAbs S y, y⟫_𝕜 := by
  have hsym : (TauCeti.operatorAbs S).IsSymmetric := (TauCeti.isPositive_operatorAbs S).isSymmetric
  refine le_re_inner_of_le_eigenvalues hsym
    (le_eigenvalues_of_norm_lower_bound (TauCeti.isPositive_operatorAbs S) hsym ?_)
  intro y
  rw [TauCeti.norm_operatorAbs_apply]
  exact hlow y

/-- **The adjoint of a Sylvester equation, in the sign the norm bounds want.**

From `A X − X B = C` with `A`, `B` symmetric, taking adjoints gives
`X⋆ A − B X⋆ = C⋆`; negating puts it in the orientation the interval-gap
estimates apply.  Both of them derived this in seven lines. -/
private theorem sylvester_adjoint_neg {A : F →ₗ[𝕜] F} {B : E →ₗ[𝕜] E}
    {X C : E →ₗ[𝕜] F} (hA : A.IsSymmetric) (hB : B.IsSymmetric)
    (hEq : A ∘ₗ X - X ∘ₗ B = C) :
    B ∘ₗ X.adjoint - X.adjoint ∘ₗ A = -C.adjoint := by
  have hadj : X.adjoint ∘ₗ A - B ∘ₗ X.adjoint = C.adjoint := by
    simpa only [map_sub, LinearMap.adjoint_comp, hA.adjoint_eq, hB.adjoint_eq] using
      congrArg (fun T : E →ₗ[𝕜] F => T.adjoint) hEq
  calc
    B ∘ₗ X.adjoint - X.adjoint ∘ₗ A
        = -(X.adjoint ∘ₗ A - B ∘ₗ X.adjoint) := by abel
    _ = -C.adjoint := congrArg Neg.neg hadj

omit [FiniteDimensional 𝕜 E] in
/-- **A Sylvester equation transports along the polar decomposition.**  Writing
`S = U |S|`, the equation `S X - X T = C` becomes `|S| X - (U⁻¹X) T = U⁻¹C`:
apply `U⁻¹` throughout and use `U⁻¹ (S x) = |S| x`.

The two interval-gap bounds below each built this transport inline; naming it
also names the only place the polar unitary is used. -/
private theorem abs_comp_sub_comp_of_sylvester
    {S : F →ₗ[𝕜] F} {T : E →ₗ[𝕜] E} {X C : E →ₗ[𝕜] F}
    (hShift : S ∘ₗ X - X ∘ₗ T = C) :
    TauCeti.operatorAbs S ∘ₗ X -
        ((choosePolarUnitary S).symm.toLinearMap ∘ₗ X) ∘ₗ T =
      (choosePolarUnitary S).symm.toLinearMap ∘ₗ C := by
  ext x
  have hx := LinearMap.congr_fun hShift x
  have hSX : (choosePolarUnitary S).symm (S (X x)) = TauCeti.operatorAbs S (X x) := by
    have hp := LinearMap.congr_fun
      (polar_decomposition_choosePolarUnitary S) (X x)
    -- `congr_fun` leaves the polar identity as a raw function application; naming it as
    -- the operator equation is what lets `symm_apply_apply` fire.
    change S (X x) = choosePolarUnitary S (TauCeti.operatorAbs S (X x)) at hp
    rw [hp, (choosePolarUnitary S).symm_apply_apply]
  -- both sides are the same term once the composites are unfolded; written out because
  -- the `← hSX` rewrite has to match this spelling.
  change TauCeti.operatorAbs S (X x) - (choosePolarUnitary S).symm (X (T x)) =
    (choosePolarUnitary S).symm (C x)
  rw [← hSX, ← map_sub]
  exact congrArg (choosePolarUnitary S).symm hx

private theorem uiNorm_sylvester_le_of_form_bounds_aux
    (N : UnitarilyInvariantSeminorm 𝕜 E F)
    {A : F →ₗ[𝕜] F} {B : E →ₗ[𝕜] E} {X C : E →ₗ[𝕜] F}
    (hA : A.IsSymmetric) (hB : B.IsSymmetric) {c δ : ℝ} (hδ : 0 < δ)
    (hAform : ∀ y, (c + δ) * ‖y‖ ^ 2 ≤ RCLike.re ⟪A y, y⟫_𝕜)
    (hBform : ∀ x, RCLike.re ⟪B x, x⟫_𝕜 ≤ c * ‖x‖ ^ 2)
    (hEq : A ∘ₗ X - X ∘ₗ B = C) :
    δ * N X ≤ N C := by
  let A' : F →L[𝕜] F := A.toContinuousLinearMap
  let B' : E →L[𝕜] E := B.toContinuousLinearMap
  let X' : E →L[𝕜] F := X.toContinuousLinearMap
  let C' : E →L[𝕜] F := C.toContinuousLinearMap
  let N' : (E →L[𝕜] F) → ℝ := fun T => N T.toLinearMap
  have hA' : A'.IsSymmetric := fun x y => hA x y
  have hB' : B'.IsSymmetric := fun x y => hB x y
  have hadd : ∀ f g : E →L[𝕜] F, N' (f + g) ≤ N' f + N' g := by
    intro f g
    simp only [N', ContinuousLinearMap.toLinearMap_add]
    exact N.add_le _ _
  have hsmul : ∀ (a : 𝕜) (f : E →L[𝕜] F), N' (a • f) = ‖a‖ * N' f := by
    intro a f
    simp only [N', ContinuousLinearMap.toLinearMap_smul]
    exact N.smul_eq _ _
  have hidealL : ∀ D : F →L[𝕜] F, ∀ T : E →L[𝕜] F,
      N' (D ∘L T) ≤ ‖D‖ * N' T := by
    intro D T
    -- `N'` is `N` precomposed with `toLinearMap`. The goal is stated over `∘L` on bundled
    -- maps and `N`'s ideal API over `∘ₗ` on the underlying ones; the two are the same term,
    -- so this `change` is the entire translation between the two spellings.
    change N (D.toLinearMap ∘ₗ T.toLinearMap) ≤ ‖D‖ * N T.toLinearMap
    have h := N.comp_le_opNorm_mul D.toLinearMap T.toLinearMap
    have hD : D.toLinearMap.toContinuousLinearMap = D := by
      ext x
      rfl
    rwa [hD] at h
  have hidealR : ∀ T : E →L[𝕜] F, ∀ D : E →L[𝕜] E,
      N' (T ∘L D) ≤ N' T * ‖D‖ := by
    intro T D
    -- As `hidealL`: the same `∘L` / `∘ₗ` translation, on the other side.
    change N (T.toLinearMap ∘ₗ D.toLinearMap) ≤ N T.toLinearMap * ‖D‖
    have h := N.comp_le_mul_opNorm T.toLinearMap D.toLinearMap
    have hD : D.toLinearMap.toContinuousLinearMap = D := by
      ext x
      rfl
    rwa [hD] at h
  have hEq' : A' ∘L X' - X' ∘L B' = C' := by
    ext x
    simpa [A', B', X', C', ContinuousLinearMap.comp_apply] using
      LinearMap.congr_fun hEq x
  have hbound : N' X' ≤ N' C' / δ :=
    TauCeti.ContinuousLinearMap.le_div_of_comp_sub_comp_eq_rectangular
      hadd hsmul hidealL hidealR hA' hB' hδ hAform hBform hEq'
  have hbound' : N X ≤ N C / δ := by
    simpa [N', X', C'] using hbound
  rw [le_div_iff₀ hδ] at hbound'
  simpa [mul_comm] using hbound'


/-- Sharp constant-one ordered Sylvester estimate in every rectangular UI
norm.

The proof first extends the integral-free absorption argument from square to
rectangular operator seminorms.  In either ordered orientation, the largest
eigenvalue of the lower block supplies a cut `c`; eigenbasis expansion then
gives the global upper and lower quadratic-form bounds.  The reverse
orientation is reduced to the first by taking adjoints and transporting the
rectangular UI norm.
-/
theorem uiNorm_sylvester_le_of_orderedGap
    (N : UnitarilyInvariantSeminorm 𝕜 E F)
    {A : F →ₗ[𝕜] F} {B : E →ₗ[𝕜] E} {X C : E →ₗ[𝕜] F}
    (hA : A.IsSymmetric) (hB : B.IsSymmetric) {δ : ℝ} (hδ : 0 < δ)
    (hgap : OrderedSylvesterGap A B δ)
    (hEq : A ∘ₗ X - X ∘ₗ B = C) :
    δ * N X ≤ N C := by
  rcases subsingleton_or_nontrivial E with _ | _
  · have hX0 : X = 0 := by
      ext x
      have hx : x = 0 := Subsingleton.elim _ _
      subst x
      simp
    have hC0 : C = 0 := by
      ext x
      have hx : x = 0 := Subsingleton.elim _ _
      subst x
      simp
    simp [hX0, hC0, N.apply_zero]
  rcases subsingleton_or_nontrivial F with _ | _
  · have hX0 : X = 0 := by
      ext x
      exact Subsingleton.elim _ _
    have hC0 : C = 0 := by
      ext x
      exact Subsingleton.elim _ _
    simp [hX0, hC0, N.apply_zero]
  let : NeZero (Module.finrank 𝕜 E) := ⟨Nat.ne_of_gt Module.finrank_pos⟩
  let : NeZero (Module.finrank 𝕜 F) := ⟨Nat.ne_of_gt Module.finrank_pos⟩
  rcases hgap with hBA | hAB
  · let j₀ : Fin (Module.finrank 𝕜 E) := ⟨0, Module.finrank_pos⟩
    let c : ℝ := hB.eigenvalues rfl j₀
    have hBform : ∀ x, RCLike.re ⟪B x, x⟫_𝕜 ≤ c * ‖x‖ ^ 2 :=
      re_inner_le_of_eigenvalues_le hB (fun j =>
        hB.eigenvalues_antitone rfl (Fin.zero_le j))
    have hAform : ∀ y, (c + δ) * ‖y‖ ^ 2 ≤ RCLike.re ⟪A y, y⟫_𝕜 :=
      le_re_inner_of_le_eigenvalues hA fun i =>
        hBA c (hA.eigenvalues rfl i)
          (eigenvalue_mem_restrictedPointSpectrum_top hB j₀)
          (eigenvalue_mem_restrictedPointSpectrum_top hA i)
    exact uiNorm_sylvester_le_of_form_bounds_aux N hA hB hδ hAform hBform hEq
  · let i₀ : Fin (Module.finrank 𝕜 F) := ⟨0, Module.finrank_pos⟩
    let c : ℝ := hA.eigenvalues rfl i₀
    have hAform : ∀ y, RCLike.re ⟪A y, y⟫_𝕜 ≤ c * ‖y‖ ^ 2 :=
      re_inner_le_of_eigenvalues_le hA (fun i =>
        hA.eigenvalues_antitone rfl (Fin.zero_le i))
    have hBform : ∀ x, (c + δ) * ‖x‖ ^ 2 ≤ RCLike.re ⟪B x, x⟫_𝕜 :=
      le_re_inner_of_le_eigenvalues hB fun j =>
        hAB c (hB.eigenvalues rfl j)
          (eigenvalue_mem_restrictedPointSpectrum_top hA i₀)
          (eigenvalue_mem_restrictedPointSpectrum_top hB j)
    have hEqAdj : B ∘ₗ X.adjoint - X.adjoint ∘ₗ A = -C.adjoint :=
      sylvester_adjoint_neg hA hB hEq
    have hbound := uiNorm_sylvester_le_of_form_bounds_aux
      (UnitarilyInvariantSeminorm.adjointTransport N)
      hB hA hδ hBform hAform hEqAdj
    rw [UnitarilyInvariantSeminorm.adjointTransport_apply,
      UnitarilyInvariantSeminorm.adjointTransport_neg_adjoint_apply] at hbound
    exact hbound

/-- Sharp constant-one interval/exterior Sylvester estimate in every
rectangular UI norm.

The proof follows the dimension-free polar-absorption route used for the
operator norm.  Shift the interval to its midpoint, replace the exterior
operator by its absolute value, and absorb the polar unitary into the unknown
and right-hand side.  The abstract rectangular seminorm theorem in
`SylvesterBound` applies because every rectangular UI norm is subadditive,
absolutely homogeneous, and satisfies both operator-ideal inequalities.
Unitary invariance identifies the rotated norms with the original ones.
-/
theorem uiNorm_sylvester_le_of_intervalGap
    (N : UnitarilyInvariantSeminorm 𝕜 E F)
    {A : F →ₗ[𝕜] F} {B : E →ₗ[𝕜] E} {X C : E →ₗ[𝕜] F}
    (hA : A.IsSymmetric) (hB : B.IsSymmetric)
    {a b δ : ℝ} (hδ : 0 < δ) (hgap : IntervalSylvesterGap A B a b δ)
    (hEq : A ∘ₗ X - X ∘ₗ B = C) :
    δ * N X ≤ N C := by
  rcases subsingleton_or_nontrivial E with _ | _
  · have hX0 : X = 0 := by
      ext x
      have hx : x = 0 := Subsingleton.elim _ _
      subst x
      simp
    rw [hX0, N.apply_zero, mul_zero]
    exact N.nonneg C
  rcases subsingleton_or_nontrivial F with _ | _
  · have hX0 : X = 0 := by
      ext x
      exact Subsingleton.elim _ _
    rw [hX0, N.apply_zero, mul_zero]
    exact N.nonneg C
  let : NeZero (Module.finrank 𝕜 E) :=
    ⟨Nat.ne_of_gt Module.finrank_pos⟩
  let : NeZero (Module.finrank 𝕜 F) :=
    ⟨Nat.ne_of_gt Module.finrank_pos⟩
  let j₀ : Fin (Module.finrank 𝕜 E) := ⟨0, Module.finrank_pos⟩
  have hj₀ := hgap.1 (eigenvalue_mem_restrictedPointSpectrum_top hB j₀)
  have hab : a ≤ b := hj₀.1.trans hj₀.2
  let m : ℝ := (a + b) / 2
  let r : ℝ := (b - a) / 2
  let S : F →ₗ[𝕜] F := A - (m : 𝕜) • LinearMap.id
  let T : E →ₗ[𝕜] E := B - (m : 𝕜) • LinearMap.id
  let H : F →ₗ[𝕜] F := TauCeti.operatorAbs S
  let U : F ≃ₗᵢ[𝕜] F := choosePolarUnitary S
  let Z : E →ₗ[𝕜] F := U.symm.toLinearMap ∘ₗ X
  let Y : E →ₗ[𝕜] F := U.symm.toLinearMap ∘ₗ C
  have hr : 0 ≤ r := by simp only [r]; linarith
  have hTnorm : ‖T.toContinuousLinearMap‖ ≤ r := by
    simpa [T, m, r] using opNorm_shift_le_of_pointSpectrumIn_Icc hB hab hgap.1
  have hSlower : ∀ y, (r + δ) * ‖y‖ ≤ ‖S y‖ := by
    simpa [S, m, r] using
      norm_shift_lower_of_spectrumOutside hA hab hδ hgap.2
  have hHsym : H.IsSymmetric := (TauCeti.isPositive_operatorAbs S).isSymmetric
  have hHform : ∀ y, (r + δ) * ‖y‖ ^ 2 ≤ RCLike.re ⟪H y, y⟫_𝕜 :=
    le_re_inner_operatorAbs_self_of_norm_lower_bound hSlower
  have hShift : S ∘ₗ X - X ∘ₗ T = C :=
    sylvester_sub_smul_id A B X C (m : 𝕜) hEq
  have hPolar : H ∘ₗ X - Z ∘ₗ T = Y :=
    abs_comp_sub_comp_of_sylvester hShift
  have hZnorm : N Z = N X := by
    -- `Z` is definitionally `U.symm.toLinearMap ∘ₗ X`, and `N.invariant` is stated over that
    -- composite; the goal has to be in that form before the lemma can be cited.
    change N (U.symm.toLinearMap ∘ₗ X) = N X
    have h := N.invariant U.symm (LinearIsometryEquiv.refl 𝕜 E) X
    have hcomp : U.symm.toLinearMap ∘ₗ X ∘ₗ
        (LinearIsometryEquiv.refl 𝕜 E).toLinearMap =
        U.symm.toLinearMap ∘ₗ X := by
      ext x
      rfl
    rwa [hcomp] at h
  have hYnorm : N Y = N C := by
    -- `Y` is definitionally `U.symm.toLinearMap ∘ₗ C`; same step as `hZnorm`.
    change N (U.symm.toLinearMap ∘ₗ C) = N C
    have h := N.invariant U.symm (LinearIsometryEquiv.refl 𝕜 E) C
    have hcomp : U.symm.toLinearMap ∘ₗ C ∘ₗ
        (LinearIsometryEquiv.refl 𝕜 E).toLinearMap =
        U.symm.toLinearMap ∘ₗ C := by
      ext x
      rfl
    rwa [hcomp] at h
  let H' : F →L[𝕜] F := H.toContinuousLinearMap
  let T' : E →L[𝕜] E := T.toContinuousLinearMap
  let X' : E →L[𝕜] F := X.toContinuousLinearMap
  let Z' : E →L[𝕜] F := Z.toContinuousLinearMap
  let Y' : E →L[𝕜] F := Y.toContinuousLinearMap
  let N' : (E →L[𝕜] F) → ℝ := fun Q => N Q.toLinearMap
  have hadd : ∀ f g : E →L[𝕜] F, N' (f + g) ≤ N' f + N' g := by
    intro f g
    simp only [N', ContinuousLinearMap.toLinearMap_add]
    exact N.add_le _ _
  have hsmul : ∀ (q : 𝕜) (f : E →L[𝕜] F), N' (q • f) = ‖q‖ * N' f := by
    intro q f
    simp only [N', ContinuousLinearMap.toLinearMap_smul]
    exact N.smul_eq _ _
  have hidealL : ∀ D : F →L[𝕜] F, ∀ Q : E →L[𝕜] F,
      N' (D ∘L Q) ≤ ‖D‖ * N' Q := by
    intro D Q
    -- `N'` is `N` precomposed with `toLinearMap`. The goal is stated over `∘L` on bundled
    -- maps and `N`'s ideal API over `∘ₗ` on the underlying ones; the two are the same term,
    -- so this `change` is the entire translation between the two spellings.
    change N (D.toLinearMap ∘ₗ Q.toLinearMap) ≤ ‖D‖ * N Q.toLinearMap
    have h := N.comp_le_opNorm_mul D.toLinearMap Q.toLinearMap
    have hD : D.toLinearMap.toContinuousLinearMap = D := by ext x; rfl
    rwa [hD] at h
  have hidealR : ∀ Q : E →L[𝕜] F, ∀ D : E →L[𝕜] E,
      N' (Q ∘L D) ≤ N' Q * ‖D‖ := by
    intro Q D
    -- As `hidealL`: the same `∘L` / `∘ₗ` translation, on the other side.
    change N (Q.toLinearMap ∘ₗ D.toLinearMap) ≤ N Q.toLinearMap * ‖D‖
    have h := N.comp_le_mul_opNorm Q.toLinearMap D.toLinearMap
    have hD : D.toLinearMap.toContinuousLinearMap = D := by ext x; rfl
    rwa [hD] at h
  have hPolar' : H' ∘L X' - Z' ∘L T' = Y' := by
    ext x
    simpa [H', T', X', Z', Y', ContinuousLinearMap.comp_apply] using
      LinearMap.congr_fun hPolar x
  have hZX' : N' Z' = N' X' := by
    simpa [N', X', Z'] using hZnorm
  have hbound := ContinuousLinearMap.gap_mul_le_of_comp_sub_comp_eq_rectangular
    hadd hsmul hidealL hidealR (fun x y => hHsym x y) hr hδ hHform
    hTnorm hZX' hPolar'
  have hbound' : δ * N X ≤ N Y := by
    simpa [N', X', Y'] using hbound
  rwa [hYnorm] at hbound'

/-- **Sharp constant-one interval/exterior Sylvester estimate in the operator
norm.**  If the spectrum of `A` lies in `Icc a b` and that of `B` avoids
`Ioo (a - δ) (b + δ)`, then `A ∘ₗ X - X ∘ₗ B = C` forces
`δ ‖X‖ ≤ ‖C‖`.

The operator norm is a rectangular unitarily invariant norm
(`UnitarilyInvariantSeminorm.opNorm`, whose application is `‖·‖` by
`rfl`), so this is the theorem directly above at that norm.  It was a separate
82-line proof until 2026-07-30 — the same shift-and-invert argument, the same
two `Subsingleton` cases, the same Neumann bound — placed *before* the general
version in the file, which is why the specialisation was not visible. -/
theorem opNorm_sylvester_le_of_intervalGap
    {A : F →ₗ[𝕜] F} {B : E →ₗ[𝕜] E} {X C : E →ₗ[𝕜] F}
    (hA : A.IsSymmetric) (hB : B.IsSymmetric)
    {a b δ : ℝ} (hδ : 0 < δ) (hgap : IntervalSylvesterGap A B a b δ)
    (hEq : A ∘ₗ X - X ∘ₗ B = C) :
    δ * ‖X.toContinuousLinearMap‖ ≤ ‖C.toContinuousLinearMap‖ :=
  uiNorm_sylvester_le_of_intervalGap UnitarilyInvariantSeminorm.opNorm
    hA hB hδ hgap hEq

/-- Sharp constant-one interval/exterior Sylvester estimate in either
orientation.

The forward branch is `uiNorm_sylvester_le_of_intervalGap`.  In the reverse
branch, take adjoints, negate the resulting Sylvester equation, and transport
the rectangular UI norm across adjoint. -/
theorem uiNorm_sylvester_le_of_unorderedIntervalGap
    (N : UnitarilyInvariantSeminorm 𝕜 E F)
    {A : F →ₗ[𝕜] F} {B : E →ₗ[𝕜] E} {X C : E →ₗ[𝕜] F}
    (hA : A.IsSymmetric) (hB : B.IsSymmetric)
    {a b δ : ℝ} (hδ : 0 < δ)
    (hgap : UnorderedIntervalSylvesterGap A B a b δ)
    (hEq : A ∘ₗ X - X ∘ₗ B = C) :
    δ * N X ≤ N C := by
  rcases hgap with hforward | hreverse
  · exact uiNorm_sylvester_le_of_intervalGap N hA hB hδ hforward hEq
  · have hEqAdj : B ∘ₗ X.adjoint - X.adjoint ∘ₗ A = -C.adjoint :=
      sylvester_adjoint_neg hA hB hEq
    have hbound := uiNorm_sylvester_le_of_intervalGap
      (UnitarilyInvariantSeminorm.adjointTransport N)
      hB hA hδ hreverse hEqAdj
    rw [UnitarilyInvariantSeminorm.adjointTransport_apply,
      UnitarilyInvariantSeminorm.adjointTransport_neg_adjoint_apply] at hbound
    exact hbound

/-- Ky Fan specialization of the sharp interval/exterior Sylvester
estimate.  The hard work is already contained in
`uiNorm_sylvester_le_of_intervalGap`; evaluating the concrete Ky Fan norm gives
this singular-value prefix-sum form directly.
-/
theorem kyFan_sylvester_le_of_intervalGap
    {A : F →ₗ[𝕜] F} {B : E →ₗ[𝕜] E} {X C : E →ₗ[𝕜] F}
    (hA : A.IsSymmetric) (hB : B.IsSymmetric)
    {a b δ : ℝ} (hδ : 0 < δ) (hgap : IntervalSylvesterGap A B a b δ)
    (hEq : A ∘ₗ X - X ∘ₗ B = C) (k : ℕ) :
    δ * TauCeti.kyFanSum k X ≤
      TauCeti.kyFanSum k C := by
  have h := uiNorm_sylvester_le_of_intervalGap
    (UnitarilyInvariantSeminorm.kyFan k) hA hB hδ hgap hEq
  simpa only [UnitarilyInvariantSeminorm.kyFan_apply] using h

/-- Ordered positivity/coercivity form used by the existing integral-free
proof.
-/
theorem uiNorm_sylvester_le_of_form_bounds
    (N : UnitarilyInvariantSeminorm 𝕜 E F)
    {A : F →ₗ[𝕜] F} {B : E →ₗ[𝕜] E} {X C : E →ₗ[𝕜] F}
    (hA : A.IsSymmetric) (hB : B.IsSymmetric) {c δ : ℝ} (hδ : 0 < δ)
    (hAform : ∀ y, (c + δ) * ‖y‖ ^ 2 ≤ RCLike.re ⟪A y, y⟫_𝕜)
    (hBform : ∀ x, RCLike.re ⟪B x, x⟫_𝕜 ≤ c * ‖x‖ ^ 2)
    (hEq : A ∘ₗ X - X ∘ₗ B = C) :
    δ * N X ≤ N C := by
  exact uiNorm_sylvester_le_of_form_bounds_aux N hA hB hδ hAform hBform hEq

end TauCeti
