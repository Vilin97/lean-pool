/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, Claude Opus 5
-/
import LeanPool.DavisKahan.DavisKahan.InfiniteDimensional.TanTwoTheta.OffDiagonalSpectralRepulsion
import LeanPool.DavisKahan.DavisKahan.SpectralTheory.GapResolvent
import LeanPool.DavisKahan.DavisKahan.SinTheta.BoundedPerturbation

/-!
# Off-diagonal spectral repulsion for an unbounded ambient operator

Davis--Kahan 1970 Section 8 asserts that a perturbation entirely off-diagonal
with respect to the source splitting cannot move spectrum into the open gap.
`OffDiagonalSpectralRepulsion.lean` proves this for a bounded ambient `A`.  The
source scope is an unbounded self-adjoint `A` with a bounded residual, so the
bounded statement is a specialization rather than the theorem.

The bounded proof reaches invertibility of `J (A + H - lam)` through
`isUnit_of_coercive`, which requires `A` to be everywhere defined.  That is the
one step that does not survive, and
`TauCeti.LinearPMap.mem_resolventSet_of_coercive_comp` replaces it: coercivity
against a norm-preserving `J` gives a norm lower bound, and a norm lower bound at
a real point already puts that point in the resolvent set.

Nothing else about the bounded argument changes.  Writing `J` for the reflection
through `U`:

* the ordered form bounds make `J (A - lam)` coercive by
  `eps = min (lam - a) (b - lam)`, because reflection flips the sign on `Uᗮ`
  exactly where the form inequality points the other way -- proved here for a
  partial map, where the two orthogonal pieces of a domain vector stay in the
  domain because `U` *reduces* `A`;
* full off-diagonality gives `J H = - H J`, so `J H` is skew-adjoint and
  contributes nothing to the real part.  `H` is still bounded, so this half is
  reused verbatim from the bounded development.

No compactness, no discreteness, no norm-attaining eigenvector, and no
boundedness of `A`.
-/

namespace TauCeti
namespace DavisKahan

open scoped InnerProductSpace
open TauCeti.LinearPMap

noncomputable section

universe u

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [CompleteSpace E]

omit [CompleteSpace E] in
private theorem re_inner_real_smul_self (r : ℝ) (y : E) :
    RCLike.re ⟪((r : ℝ) : ℂ) • y, y⟫_ℂ = r * ‖y‖ ^ 2 := by
  rw [inner_smul_left, Complex.conj_ofReal, inner_self_eq_norm_sq_to_K]
  simp [RCLike.re_to_complex, pow_two]

omit [CompleteSpace E] in
/-- **The reflected centered partial map is coercive by half the ordered gap.**

This is `reflected_centered_form_lower` for an unbounded `A`.  The hypotheses
that were "`U` is invariant" in the bounded statement become "`U` reduces `A`":
that is what keeps `P x` and `P^⊥ x` inside the domain, so the two ordered form
bounds can be applied to them at all. -/
theorem reflected_centered_form_lower_pmap
    (A : E →ₗ.[ℂ] E) (U : Submodule ℂ E) [U.HasOrthogonalProjection]
    (hred : TauCeti.LinearPMap.ReducesSubspace A U)
    {a b : ℝ}
    (hUhigh : ∀ x : A.domain, (x : E) ∈ U →
      b * ‖(x : E)‖ ^ 2 ≤ RCLike.re ⟪A x, (x : E)⟫_ℂ)
    (hUperpLow : ∀ x : A.domain, (x : E) ∈ Uᗮ →
      RCLike.re ⟪A x, (x : E)⟫_ℂ ≤ a * ‖(x : E)‖ ^ 2)
    (x : A.domain) :
    (b - a) / 2 * ‖(x : E)‖ ^ 2 ≤
      RCLike.re ⟪U.reflectionOperator
        (A x - (((a + b) / 2 : ℝ) : ℂ) • (x : E)), (x : E)⟫_ℂ := by
  set c : ℂ := (((a + b) / 2 : ℝ) : ℂ) with hcdef
  have hpm : U.starProjection (x : E) ∈ A.domain :=
    hred.projection_mem_domain x
  have hmm : Uᗮ.starProjection (x : E) ∈ A.domain :=
    hred.orthogonalProjection_mem_domain x
  set p : A.domain := ⟨U.starProjection (x : E), hpm⟩ with hpdef
  set m : A.domain := ⟨Uᗮ.starProjection (x : E), hmm⟩ with hmdef
  have hpU : (p : E) ∈ U := U.starProjection_apply_mem _
  have hmU : (m : E) ∈ Uᗮ := Uᗮ.starProjection_apply_mem _
  have hsum : (p : E) + (m : E) = (x : E) :=
    U.starProjection_add_starProjection_orthogonal (x : E)
  have hxpm : p + m = x := Subtype.ext hsum
  have hAsum : A p + A m = A x := by rw [← A.map_add, hxpm]
  have hApU : A p ∈ U := hred.invariant p hpU
  have hAmU : A m ∈ Uᗮ := hred.orthogonal_invariant m hmU
  have hu : A p - c • (p : E) ∈ U := U.sub_mem hApU (U.smul_mem _ hpU)
  have hv : A m - c • (m : E) ∈ Uᗮ := Uᗮ.sub_mem hAmU (Uᗮ.smul_mem _ hmU)
  have hsplit : A x - c • (x : E)
      = (A p - c • (p : E)) + (A m - c • (m : E)) := by
    rw [← hAsum, ← hsum]
    module
  have hJu : U.reflectionOperator (A p - c • (p : E)) = A p - c • (p : E) :=
    Submodule.reflectionOperator_apply_of_mem U hu
  have hJv : U.reflectionOperator (A m - c • (m : E)) = -(A m - c • (m : E)) := by
    rw [Submodule.reflectionOperator_apply,
      (Submodule.starProjection_apply_eq_zero_iff U).mpr hv]
    module
  have hrefl : U.reflectionOperator (A x - c • (x : E))
      = (A p - c • (p : E)) - (A m - c • (m : E)) := by
    rw [hsplit, map_add, hJu, hJv]
    module
  have h1 : ⟪A p - c • (p : E), (m : E)⟫_ℂ = 0 :=
    Submodule.inner_right_of_mem_orthogonal hu hmU
  have h2 : ⟪A m - c • (m : E), (p : E)⟫_ℂ = 0 :=
    Submodule.inner_left_of_mem_orthogonal hpU hv
  have hpyth : ‖(p : E)‖ ^ 2 + ‖(m : E)‖ ^ 2 = ‖(x : E)‖ ^ 2 := by
    have horth : ⟪(p : E), (m : E)⟫_ℂ = 0 :=
      Submodule.inner_right_of_mem_orthogonal hpU hmU
    calc
      ‖(p : E)‖ ^ 2 + ‖(m : E)‖ ^ 2 = ‖(p : E) + (m : E)‖ ^ 2 := by
        rw [norm_add_sq (𝕜 := ℂ), horth, map_zero]
        ring
      _ = ‖(x : E)‖ ^ 2 := by rw [hsum]
  rw [hrefl, ← hpyth, ← hsum, inner_sub_left, inner_add_right, inner_add_right,
    h1, h2]
  simp only [add_zero, zero_add, inner_sub_left, map_sub]
  rw [hcdef, re_inner_real_smul_self, re_inner_real_smul_self]
  have hpb := hUhigh p hpU
  have hma := hUperpLow m hmU
  nlinarith [hpb, hma]

/-- **Spectral repulsion for an unbounded ambient operator.**

`A` is self-adjoint and possibly unbounded, `U` reduces `A`, the form of `A` is
at least `b` on the domain part of `U` and at most `a` on the domain part of
`Uᗮ`, and the bounded self-adjoint `H` is fully off-diagonal.  Then no point of
the open interval `(a, b)` is in the spectrum of `A + H`.

This is stated in exactly the shape `twoSidedShiftedInverseBound_of_spectrum_gap`
consumes, which is how the Section 8 argument uses it. -/
theorem notMem_spectrum_addBounded_of_offDiagonal_form_gap
    (A : E →ₗ.[ℂ] E) (Hop : E →L[ℂ] E)
    (U : Submodule ℂ E) [U.HasOrthogonalProjection]
    {a b : ℝ}
    (hA : IsSelfAdjoint A)
    (hH : IsSelfAdjoint Hop)
    (hred : TauCeti.LinearPMap.ReducesSubspace A U)
    (hUhigh : ∀ x : A.domain, (x : E) ∈ U →
      b * ‖(x : E)‖ ^ 2 ≤ RCLike.re ⟪A x, (x : E)⟫_ℂ)
    (hUperpLow : ∀ x : A.domain, (x : E) ∈ Uᗮ →
      RCLike.re ⟪A x, (x : E)⟫_ℂ ≤ a * ‖(x : E)‖ ^ 2)
    (hHU : ∀ x ∈ U, Hop x ∈ Uᗮ)
    (hHUperp : ∀ x ∈ Uᗮ, Hop x ∈ U)
    {lam : ℝ} (hlam : lam ∈ Set.Ioo a b) :
    ((lam : ℝ) : ℂ) ∉ TauCeti.LinearPMap.spectrum
      (TauCeti.LinearPMap.addBounded A Hop) := by
  obtain ⟨hla, hlb⟩ := hlam
  set ε : ℝ := min (lam - a) (b - lam) with hεdef
  have hε : 0 < ε := lt_min (by linarith) (by linarith)
  have hεa : a ≤ lam - ε := by
    have : ε ≤ lam - a := min_le_left _ _
    linarith
  have hεb : lam + ε ≤ b := by
    have : ε ≤ b - lam := min_le_right _ _
    linarith
  -- Shrink the ordered form gap so that it is centred at `lam`.
  have hUhigh' : ∀ x : A.domain, (x : E) ∈ U →
      (lam + ε) * ‖(x : E)‖ ^ 2 ≤ RCLike.re ⟪A x, (x : E)⟫_ℂ := by
    intro x hx
    exact le_trans (mul_le_mul_of_nonneg_right hεb (sq_nonneg ‖(x : E)‖))
      (hUhigh x hx)
  have hUperpLow' : ∀ x : A.domain, (x : E) ∈ Uᗮ →
      RCLike.re ⟪A x, (x : E)⟫_ℂ ≤ (lam - ε) * ‖(x : E)‖ ^ 2 := by
    intro x hx
    exact le_trans (hUperpLow x hx)
      (mul_le_mul_of_nonneg_right hεa (sq_nonneg ‖(x : E)‖))
  have hkey : ∀ x : A.domain, ε * ‖(x : E)‖ ^ 2 ≤
      RCLike.re ⟪U.reflectionOperator
        (A x - ((lam : ℝ) : ℂ) • (x : E)), (x : E)⟫_ℂ := by
    intro x
    have h := reflected_centered_form_lower_pmap A U hred
      (a := lam - ε) (b := lam + ε) hUhigh' hUperpLow' x
    have e1 : (lam - ε + (lam + ε)) / 2 = lam := by ring
    have e2 : (lam + ε - (lam - ε)) / 2 = ε := by ring
    rw [e1, e2] at h
    exact h
  have hskew := re_inner_reflection_comp_offDiagonal_eq_zero Hop U hH hHU hHUperp
  have hAH : IsSelfAdjoint (TauCeti.LinearPMap.addBounded A Hop) :=
    TauCeti.DavisKahan.addBounded_isSelfAdjoint A hA Hop
      (ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp hH)
  have hcoer : ∀ x : (TauCeti.LinearPMap.addBounded A Hop).domain,
      ε * ‖(x : E)‖ ^ 2 ≤
        (⟪U.reflectionOperator (TauCeti.LinearPMap.addBounded A Hop x -
          ((lam : ℝ) : ℂ) • (x : E)), (x : E)⟫_ℂ).re := by
    intro x
    have hx : ((x : E)) ∈ A.domain := x.2
    have hsplit : TauCeti.LinearPMap.addBounded A Hop x -
        ((lam : ℝ) : ℂ) • (x : E)
        = (A ⟨(x : E), hx⟩ - ((lam : ℝ) : ℂ) • (x : E)) + Hop (x : E) := by
      have hap : TauCeti.LinearPMap.addBounded A Hop x
          = A ⟨(x : E), hx⟩ + Hop (x : E) := rfl
      rw [hap]
      abel
    rw [hsplit, map_add, inner_add_left]
    have h0 : RCLike.re ⟪(U.reflectionOperator ∘L Hop) (x : E), (x : E)⟫_ℂ = 0 :=
      hskew (x : E)
    simp only [ContinuousLinearMap.comp_apply] at h0
    have hgoal := hkey ⟨(x : E), hx⟩
    simp only [RCLike.re_to_complex] at hgoal h0
    simp only [Complex.add_re]
    linarith [hgoal, h0]
  have hres := TauCeti.LinearPMap.mem_resolventSet_of_coercive_comp hAH
    (J := U.reflectionOperator) (Submodule.reflectionOperator_norm_map U) hε hcoer
  simpa [TauCeti.LinearPMap.spectrum] using hres

end

end DavisKahan
end TauCeti
