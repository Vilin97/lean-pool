/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, Claude Opus 5
-/
import LeanPool.DavisKahan.DavisKahan.InfiniteDimensional.TanTwoTheta.OffDiagonalSpectralRepulsionUnbounded
import LeanPool.DavisKahan.DavisKahan.TanTheta.RitzPair
import LeanPool.DavisKahan.ForTauCeti.Analysis.InnerProductSpace.LyapunovPositivity
import LeanPool.DavisKahan.DavisKahan.Geometry.Angle.DoubleAngleGapBound
import LeanPool.DavisKahan.DavisKahan.Geometry.Halmos.CrossedDefectGap
import LeanPool.DavisKahan.DavisKahan.Sources.DavisKahan1970.Section8.Theorem81

/-!
# The quarter angle for an unbounded ambient operator

Davis--Kahan's Theorem 8.1 concludes `Θ ≤ π/4` -- non-strict, and pointwise in
the principal angle: equation (8.2) "excludes `θ = π/4` and then `θ > π/4`".

`isQuarterAcute_of_orderedFormGap` proves the strictly stronger supremum bound
`‖P_U − P_V‖ < √2/2`, and pays for the strictness with the constant
`α = δ / (1 + ‖C‖)`, which degenerates as `‖A‖ → ∞`.  That is not a
formalization artifact: with a fixed gap and outer scale tending to infinity the
angles may increase to `π/4` without reaching it, so the supremum-strict
statement is simply unavailable at unbounded scope -- and Davis and Kahan do not
claim it.

This module proves the printed conclusion, without any constant surviving into
it, by routing through two theorems that are each free of Davis--Kahan
vocabulary:

* `TauCeti.ContinuousLinearMap.nonneg_of_lyapunov_nonneg` -- `X` self-adjoint,
  `G ≥ 0` injective and `X G + G X ≥ 0` force `0 ≤ X`;
* `subspaceGap_le_of_reflectionProduct_form_nonneg` -- `K J + J K ≥ 0` forces
  `‖P_U − P_V‖ ≤ √2/2`.

The middle is the Lyapunov structure of Section 8, read through the bounded
inverse `G = C⁻¹` that Section 6.2 supplies.  Writing `S = A + H − c`,
`J`, `K` for the reflections through `U`, `V`, and `W = K J`:

* the *`U`-side* ordered gap makes `J S` coercive by `δ` -- the reflection flips
  the sign on `Uᗮ` exactly where the form inequality points the other way, and
  the off-diagonal `H` contributes nothing to the real part;
* the *`V`-side* ordered gap makes `C = K S` coercive by `δ`, hence invertible
  with `‖C⁻¹‖ ≤ δ⁻¹`, positive, injective and self-adjoint;
* substituting `x = G y` in the `U`-side coercivity gives `W G + G W* ≥ 0`, and
  conjugating by the unitary `W` gives `G W + W* G ≥ 0`;
* adding them is `X G + G X ≥ 0` for `X = W + W*`, and `X = 2 − 4 (P_U − P_V)²`.
-/

namespace TauCeti
namespace DavisKahan

open scoped InnerProductSpace
open TauCeti.LinearPMap

noncomputable section

universe u

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [CompleteSpace E]

/-- An orthogonal reflection is self-adjoint for the Hilbert space inner product. -/
private theorem reflectionOperator_inner_swap (U : Submodule ℂ E) [U.HasOrthogonalProjection] :
    ∀ y z : E, ⟪U.reflectionOperator y, z⟫_ℂ = ⟪y, U.reflectionOperator z⟫_ℂ := by
  intro y z
  have hU : star U.reflectionOperator = U.reflectionOperator :=
    TauCeti.DavisKahan.star_reflectionOperator_complex U
  conv_lhs => rw [← hU]
  rw [ContinuousLinearMap.star_eq_adjoint, ContinuousLinearMap.adjoint_inner_left]

/-- A positive operator has strictly positive form when its mixed form controls an injective map. -/
private theorem form_pos_of_injective_mixed_margin
    (X G : E →L[ℂ] E) {δ : ℝ} (hδpos : 0 < δ)
    (hXnonneg : (0 : E →L[ℂ] E) ≤ X) (hGinj : Function.Injective G)
    (hXadj : ∀ y z : E, ⟪X y, z⟫_ℂ = ⟪y, X z⟫_ℂ)
    (hXGquant : ∀ y : E, δ * ‖G y‖ ^ 2 ≤ RCLike.re ⟪X (G y), y⟫_ℂ) :
    ∀ y : E, y ≠ 0 → 0 < RCLike.re ⟪X y, y⟫_ℂ := by
  have hXnn : ∀ z : E, 0 ≤ RCLike.re ⟪X z, z⟫_ℂ := by
    intro z
    have h := ((ContinuousLinearMap.nonneg_iff_isPositive (f := X)).mp hXnonneg).2 z
    rwa [ContinuousLinearMap.reApplyInnerSelf_apply] at h
  -- **Pointwise strictness.**  A null vector of the form `⟪X ·, ·⟫` would be
  -- orthogonal to the whole range of `X`, and in particular would annihilate
  -- the `δ ‖G y‖²` margin that `hXGquant` keeps.
  intro y hy
  rcases (hXnn y).lt_or_eq with hlt | heq
  · exact hlt
  · exfalso
    have hre : ∀ (r : ℝ) (z : ℂ), RCLike.re ((r : ℂ) * z) = r * RCLike.re z := by
      intro r z
      simp
    have hzero : ∀ v : E, RCLike.re ⟪X v, y⟫_ℂ = 0 := by
      intro v
      by_contra hne
      have hquad : ∀ t : ℝ,
          0 ≤ RCLike.re ⟪X v, v⟫_ℂ + 2 * t * RCLike.re ⟪X v, y⟫_ℂ := by
        intro t
        have hexp : ⟪X (v + (t : ℂ) • y), v + (t : ℂ) • y⟫_ℂ
            = ⟪X v, v⟫_ℂ + (t : ℂ) * ⟪X v, y⟫_ℂ + (t : ℂ) * ⟪X y, v⟫_ℂ
              + (t : ℂ) * ((t : ℂ) * ⟪X y, y⟫_ℂ) := by
          simp only [map_add, ContinuousLinearMap.map_smul, inner_add_left,
            inner_add_right, inner_smul_left, inner_smul_right,
            Complex.conj_ofReal]
          ring
        have hsymm : RCLike.re ⟪X y, v⟫_ℂ = RCLike.re ⟪X v, y⟫_ℂ := by
          rw [hXadj y v]
          exact inner_re_symm y (X v)
        have hb := hXnn (v + (t : ℂ) • y)
        rw [hexp] at hb
        simp only [map_add, hre] at hb
        rw [hsymm, ← heq] at hb
        simp only [mul_zero, add_zero] at hb
        linarith
      have hval : RCLike.re ⟪X v, v⟫_ℂ
          + 2 * (-(RCLike.re ⟪X v, v⟫_ℂ + 1) / (2 * RCLike.re ⟪X v, y⟫_ℂ))
            * RCLike.re ⟪X v, y⟫_ℂ = -1 := by
        field_simp
        ring
      linarith [hquad (-(RCLike.re ⟪X v, v⟫_ℂ + 1) / (2 * RCLike.re ⟪X v, y⟫_ℂ)), hval]
    have hGy : G y ≠ 0 := by
      intro hcon
      exact hy (hGinj (by rw [hcon, map_zero]))
    have hpos : 0 < δ * ‖G y‖ ^ 2 :=
      mul_pos hδpos (pow_pos (norm_pos_iff.mpr hGy) 2)
    linarith [hXGquant y, hzero (G y)]

/-- **Davis--Kahan 1970, Theorem 8.1's printed angle conclusion, at unbounded
ambient scope.**

`A` is self-adjoint and possibly unbounded, `U` reduces `A`, the bounded
self-adjoint `H` is fully off-diagonal for `U`, and `V` reduces `A + H`.  Both
subspaces carry the printed ordered form gap with the same `a < b`.  Then the
reflection product `K J + J K` has *strictly* positive form on every nonzero
vector.

Strictness is pointwise, and deliberately not uniform: `hXGquant` keeps the
`δ ‖G y‖²` margin that the non-strict statement discards, and `‖G y‖` has no
positive lower bound over the unit sphere when `A` is unbounded.  This is the
distinction Section 8 turns on -- the printed `Θ ≤ π/4` is the supremum
statement, and the converse half of the printed `iff` needs exactly this
pointwise strictness and nothing stronger. -/
theorem reflectionProduct_form_pos_of_orderedFormGap_unbounded
    (A : E →ₗ.[ℂ] E) (Hop : E →L[ℂ] E)
    (U V : Submodule ℂ E) [U.HasOrthogonalProjection] [V.HasOrthogonalProjection]
    {a b : ℝ}
    (hA : IsSelfAdjoint A) (hH : IsSelfAdjoint Hop)
    (hred : TauCeti.LinearPMap.ReducesSubspace A U)
    (hV : TauCeti.LinearPMap.ReducesSubspace (TauCeti.LinearPMap.addBounded A Hop) V)
    (hUhigh : ∀ x : A.domain, (x : E) ∈ U →
      b * ‖(x : E)‖ ^ 2 ≤ RCLike.re ⟪A x, (x : E)⟫_ℂ)
    (hUperpLow : ∀ x : A.domain, (x : E) ∈ Uᗮ →
      RCLike.re ⟪A x, (x : E)⟫_ℂ ≤ a * ‖(x : E)‖ ^ 2)
    (hVhigh : ∀ x : (TauCeti.LinearPMap.addBounded A Hop).domain, (x : E) ∈ V →
      b * ‖(x : E)‖ ^ 2 ≤
        RCLike.re ⟪TauCeti.LinearPMap.addBounded A Hop x, (x : E)⟫_ℂ)
    (hVperpLow : ∀ x : (TauCeti.LinearPMap.addBounded A Hop).domain, (x : E) ∈ Vᗮ →
      RCLike.re ⟪TauCeti.LinearPMap.addBounded A Hop x, (x : E)⟫_ℂ ≤
        a * ‖(x : E)‖ ^ 2)
    (hHU : ∀ x ∈ U, Hop x ∈ Uᗮ) (hHUperp : ∀ x ∈ Uᗮ, Hop x ∈ U)
    (hab : a < b) :
    ∀ y : E, y ≠ 0 → 0 < RCLike.re ⟪(V.reflectionOperator * U.reflectionOperator
      + U.reflectionOperator * V.reflectionOperator) y, y⟫_ℂ := by
  classical
  set Aop : E →ₗ.[ℂ] E := TauCeti.LinearPMap.addBounded A Hop with hAopdef
  set J : E →L[ℂ] E := U.reflectionOperator with hJdef
  set K : E →L[ℂ] E := V.reflectionOperator with hKdef
  set c : ℝ := (a + b) / 2 with hcdef
  set δ : ℝ := (b - a) / 2 with hδdef
  have hδpos : 0 < δ := by rw [hδdef]; linarith
  have hAop : IsSelfAdjoint Aop :=
    TauCeti.DavisKahan.addBounded_isSelfAdjoint A hA Hop
      (ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp hH)
  -- the two coercivity statements
  have hcoerU : ∀ x : Aop.domain,
      δ * ‖(x : E)‖ ^ 2 ≤
        RCLike.re ⟪J (Aop x - ((c : ℝ) : ℂ) • (x : E)), (x : E)⟫_ℂ := by
    intro x
    have hx : ((x : E)) ∈ A.domain := x.2
    have hbase : δ * ‖(x : E)‖ ^ 2 ≤
        RCLike.re ⟪J (A ⟨(x : E), hx⟩ - ((c : ℝ) : ℂ) • (x : E)), (x : E)⟫_ℂ := by
      simpa [hJdef, hcdef, hδdef] using
        reflected_centered_form_lower_pmap A U hred hUhigh hUperpLow ⟨(x : E), hx⟩
    have hskew := re_inner_reflection_comp_offDiagonal_eq_zero Hop U hH hHU hHUperp (x : E)
    simp only [ContinuousLinearMap.comp_apply] at hskew
    have hsplit : Aop x - ((c : ℝ) : ℂ) • (x : E)
        = (A ⟨(x : E), hx⟩ - ((c : ℝ) : ℂ) • (x : E)) + Hop (x : E) := by
      have hap : Aop x = A ⟨(x : E), hx⟩ + Hop (x : E) := rfl
      rw [hap]
      abel
    rw [hsplit, map_add, inner_add_left, map_add]
    simp only [hJdef] at hskew ⊢
    linarith [hbase, hskew]
  have hcoerV : ∀ x : Aop.domain,
      δ * ‖(x : E)‖ ^ 2 ≤
        RCLike.re ⟪K (Aop x - ((c : ℝ) : ℂ) • (x : E)), (x : E)⟫_ℂ :=
    reflected_centered_form_lower_pmap Aop V hV hVhigh hVperpLow
  -- the bounded inverse of the shifted operator
  obtain ⟨R, hRdom, hRleft, hRright, hRnorm⟩ :=
    TauCeti.DavisKahan.twoSidedShiftedInverseBound_of_coercive_comp hAop
      (J := J) (by rw [hJdef]; exact Submodule.reflectionOperator_norm_map U) hδpos hcoerU
  -- `K` is an involution and preserves the domain, commuting with the shift
  have hKK : ∀ y : E, K (K y) = y := by
    intro y
    have := congrArg (fun T : E →L[ℂ] E => T y) (Submodule.reflectionOperator_involutive V)
    simpa [hKdef] using this
  have hKadj : ∀ y z : E, ⟪K y, z⟫_ℂ = ⟪y, K z⟫_ℂ := by
    simpa only [hKdef] using reflectionOperator_inner_swap V
  have hRI : ReflectionIntertwines A Hop V := ReflectionIntertwines.ofReducesSubspace hV
  have hKdom : ∀ x : Aop.domain, K (x : E) ∈ Aop.domain := fun x => hRI.mapsDomain ⟨(x : E), x.2⟩
  have hKcomm : ∀ x : Aop.domain, Aop ⟨K (x : E), hKdom x⟩ = K (Aop x) := by
    intro x
    have hx := hRI.commutes ⟨(x : E), x.2⟩
    have hl : Aop ⟨K (x : E), hKdom x⟩ = A ⟨K (x : E), hRI.mapsDomain ⟨(x : E), x.2⟩⟩
        + Hop (K (x : E)) := rfl
    have hr : K (Aop x) = K (A ⟨(x : E), x.2⟩ + Hop (x : E)) := rfl
    rw [hl, hr, map_add]
    simpa [hKdef] using hx
  have hsym : TauCeti.LinearPMap.IsSymmetric Aop :=
    TauCeti.LinearPMap.isSymmetric_of_isSelfAdjoint hAop
  -- the bounded inverse of `C = K (Aop - c)`
  set G : E →L[ℂ] E := R ∘L K with hGdef
  have hGdom : ∀ y : E, G y ∈ Aop.domain := fun y => hRdom (K y)
  have hCG : ∀ y : E, K (Aop ⟨G y, hGdom y⟩ - ((c : ℝ) : ℂ) • G y) = y := by
    intro y
    have h1 : Aop ⟨G y, hGdom y⟩ - ((c : ℝ) : ℂ) • G y = K y := hRright (K y)
    rw [h1, hKK y]
  -- `G` is self-adjoint, positive and injective
  have hGsa : ∀ y z : E, ⟪G y, z⟫_ℂ = ⟪y, G z⟫_ℂ := by
    intro y z
    have hy : y = K (Aop ⟨G y, hGdom y⟩ - ((c : ℝ) : ℂ) • G y) := (hCG y).symm
    have hz : z = K (Aop ⟨G z, hGdom z⟩ - ((c : ℝ) : ℂ) • G z) := (hCG z).symm
    calc ⟪G y, z⟫_ℂ
        = ⟪G y, K (Aop ⟨G z, hGdom z⟩ - ((c : ℝ) : ℂ) • G z)⟫_ℂ := by rw [← hz]
      _ = ⟪K (G y), Aop ⟨G z, hGdom z⟩ - ((c : ℝ) : ℂ) • G z⟫_ℂ := (hKadj _ _).symm
      _ = ⟪Aop ⟨K (G y), hKdom ⟨G y, hGdom y⟩⟩ - ((c : ℝ) : ℂ) • K (G y), G z⟫_ℂ := by
          rw [inner_sub_left, inner_sub_right, inner_smul_left, inner_smul_right,
            hsym ⟨K (G y), hKdom ⟨G y, hGdom y⟩⟩ ⟨G z, hGdom z⟩]
          simp
      _ = ⟪K (Aop ⟨G y, hGdom y⟩ - ((c : ℝ) : ℂ) • G y), G z⟫_ℂ := by
          rw [hKcomm ⟨G y, hGdom y⟩, map_sub, map_smul]
      _ = ⟪y, G z⟫_ℂ := by rw [← hy]
  have hGpos : ∀ y : E, δ * ‖G y‖ ^ 2 ≤ RCLike.re ⟪G y, y⟫_ℂ := by
    intro y
    have hy : y = K (Aop ⟨G y, hGdom y⟩ - ((c : ℝ) : ℂ) • G y) := (hCG y).symm
    have := hcoerV ⟨G y, hGdom y⟩
    calc δ * ‖G y‖ ^ 2 ≤
          RCLike.re ⟪K (Aop ⟨G y, hGdom y⟩ - ((c : ℝ) : ℂ) • G y), G y⟫_ℂ := this
      _ = RCLike.re ⟪G y, K (Aop ⟨G y, hGdom y⟩ - ((c : ℝ) : ℂ) • G y)⟫_ℂ :=
          inner_re_symm _ _
      _ = RCLike.re ⟪G y, y⟫_ℂ := by rw [← hy]
  have hGnonneg : (0 : E →L[ℂ] E) ≤ G := by
    rw [ContinuousLinearMap.nonneg_iff_isPositive]
    refine ⟨fun y z => ?_, fun y => ?_⟩
    · exact hGsa y z
    · rw [ContinuousLinearMap.reApplyInnerSelf_apply]
      exact le_trans (by positivity) (hGpos y)
  have hGinj : Function.Injective G := by
    intro y z hyz
    have hy := hCG y
    have hz := hCG z
    rw [← hy, ← hz]
    have hpt : (⟨G y, hGdom y⟩ : Aop.domain) = ⟨G z, hGdom z⟩ := Subtype.ext hyz
    rw [hpt, hyz]
  -- the unitary `W`
  set W : E →L[ℂ] E := K ∘L J with hWdef
  have hJK : ∀ y : E, J (J y) = y := by
    intro y
    have := congrArg (fun T : E →L[ℂ] E => T y) (Submodule.reflectionOperator_involutive U)
    simpa [hJdef] using this
  have hJadj : ∀ y z : E, ⟪J y, z⟫_ℂ = ⟪y, J z⟫_ℂ := by
    simpa only [hJdef] using reflectionOperator_inner_swap U
  have hWadj : ∀ y z : E, ⟪W y, z⟫_ℂ = ⟪y, J (K z)⟫_ℂ := by
    intro y z
    change ⟪K (J y), z⟫_ℂ = _
    rw [hKadj (J y) z, hJadj y (K z)]
  have hWiso : ∀ y : E, J (K (W y)) = y := by
    intro y
    change J (K (K (J y))) = y
    rw [hKK (J y), hJK y]
  have hKiso : ∀ u z : E, ⟪K u, K z⟫_ℂ = ⟪u, z⟫_ℂ := by
    intro u z
    rw [hKadj u (K z), hKK z]
  -- the key inequality: `W G + G W* ≥ 0`, quantitatively
  have hWG : ∀ y : E, δ * ‖G y‖ ^ 2 ≤ RCLike.re ⟪W (G y), y⟫_ℂ := by
    intro y
    have hy : y = K (Aop ⟨G y, hGdom y⟩ - ((c : ℝ) : ℂ) • G y) := (hCG y).symm
    have hu := hcoerU ⟨G y, hGdom y⟩
    have hWu : W (G y) = K (J (G y)) := rfl
    calc δ * ‖G y‖ ^ 2 ≤
          RCLike.re ⟪J (Aop ⟨G y, hGdom y⟩ - ((c : ℝ) : ℂ) • G y), G y⟫_ℂ := hu
      _ = RCLike.re ⟪G y, J (Aop ⟨G y, hGdom y⟩ - ((c : ℝ) : ℂ) • G y)⟫_ℂ :=
          inner_re_symm _ _
      _ = RCLike.re ⟪J (G y), Aop ⟨G y, hGdom y⟩ - ((c : ℝ) : ℂ) • G y⟫_ℂ := by
          rw [hJadj (G y) (Aop ⟨G y, hGdom y⟩ - ((c : ℝ) : ℂ) • G y)]
      _ = RCLike.re ⟪K (J (G y)), K (Aop ⟨G y, hGdom y⟩ - ((c : ℝ) : ℂ) • G y)⟫_ℂ := by
          rw [hKiso]
      _ = RCLike.re ⟪W (G y), y⟫_ℂ := by rw [hWu, ← hy]
  -- the Lyapunov hypothesis
  set X : E →L[ℂ] E := W + ContinuousLinearMap.adjoint W with hXdef
  have hXsa : IsSelfAdjoint X := by
    change star X = X
    rw [hXdef, ← ContinuousLinearMap.star_eq_adjoint, star_add, star_star]
    abel
  have hXadj : ∀ y z : E, ⟪X y, z⟫_ℂ = ⟪y, X z⟫_ℂ := by
    intro y z
    conv_lhs => rw [← hXsa.star_eq]
    rw [ContinuousLinearMap.star_eq_adjoint, ContinuousLinearMap.adjoint_inner_left]
  have hJiso : ∀ u z : E, ⟪J u, J z⟫_ℂ = ⟪u, z⟫_ℂ := by
    intro u z
    rw [hJadj u (J z), hJK z]
  have hWiso2 : ∀ u z : E, ⟪W u, W z⟫_ℂ = ⟪u, z⟫_ℂ := by
    intro u z
    change ⟪K (J u), K (J z)⟫_ℂ = _
    rw [hKiso, hJiso]
  -- the two halves of the Lyapunov form are equal
  have hswap : ∀ y : E, RCLike.re ⟪G (X y), y⟫_ℂ = RCLike.re ⟪X (G y), y⟫_ℂ := by
    intro y
    rw [hGsa (X y) y, hXadj y (G y)]
    exact inner_re_symm y (X (G y))
  have hXG : ∀ y : E, RCLike.re ⟪X (G y), y⟫_ℂ
      = RCLike.re ⟪W (G y), y⟫_ℂ + RCLike.re ⟪W (G (W y)), W y⟫_ℂ := by
    intro y
    have hXu : X (G y) = W (G y) + ContinuousLinearMap.adjoint W (G y) := rfl
    rw [hXu, inner_add_left, map_add]
    congr 1
    rw [ContinuousLinearMap.adjoint_inner_left, hWiso2 (G (W y)) y, hGsa (W y) y]
    exact inner_re_symm _ _
  -- the Lyapunov bound, with the `δ` margin retained rather than discarded
  have hXGquant : ∀ y : E, δ * ‖G y‖ ^ 2 ≤ RCLike.re ⟪X (G y), y⟫_ℂ := by
    intro y
    rw [hXG y]
    have h1 := hWG y
    have h2 := hWG (W y)
    nlinarith [sq_nonneg ‖G (W y)‖, hδpos]
  have hform : ∀ y : E, RCLike.re ⟪(X * G + G * X) y, y⟫_ℂ
      = 2 * RCLike.re ⟪X (G y), y⟫_ℂ := by
    intro y
    have hsplit : (X * G + G * X) y = X (G y) + G (X y) := rfl
    rw [hsplit, inner_add_left, map_add, hswap y]
    ring
  have hlyap : (0 : E →L[ℂ] E) ≤ X * G + G * X := by
    rw [ContinuousLinearMap.nonneg_iff_isPositive]
    constructor
    · intro y z
      change ⟪X (G y) + G (X y), z⟫_ℂ = ⟪y, X (G z) + G (X z)⟫_ℂ
      rw [inner_add_left, inner_add_right, hXadj (G y) z, hGsa y (X z),
        hGsa (X y) z, hXadj y (G z)]
      ring
    · intro y
      rw [ContinuousLinearMap.reApplyInnerSelf_apply, hform y]
      nlinarith [hXGquant y, sq_nonneg ‖G y‖, hδpos]
  have hXnonneg : (0 : E →L[ℂ] E) ≤ X :=
    TauCeti.ContinuousLinearMap.nonneg_of_lyapunov_nonneg hXsa hGnonneg hGinj hlyap
  have hXstrict : ∀ y : E, y ≠ 0 → 0 < RCLike.re ⟪X y, y⟫_ℂ :=
    form_pos_of_injective_mixed_margin X G hδpos hXnonneg hGinj hXadj hXGquant
  intro y hy
  have hXeq : V.reflectionOperator * U.reflectionOperator
      + U.reflectionOperator * V.reflectionOperator = X := by
    rw [hXdef, hWdef, hJdef, hKdef]
    congr 1
    refine ContinuousLinearMap.ext fun z => ?_
    refine ext_inner_right ℂ fun w => ?_
    rw [ContinuousLinearMap.adjoint_inner_left]
    change ⟪U.reflectionOperator (V.reflectionOperator z), w⟫_ℂ
      = ⟪z, V.reflectionOperator (U.reflectionOperator w)⟫_ℂ
    rw [← hJdef, ← hKdef, hJadj (K z) w, hKadj z (J w)]
  rw [hXeq]
  exact hXstrict y hy

/-- **The pointwise strict quarter-angle bound at unbounded scope.**

Under the printed ordered form gap on both subspaces, every nonzero vector
satisfies `‖P_U y − P_V y‖ < ‖y‖/√2` *strictly*.  No supremum bound follows --
`isQuarterAcute_of_orderedFormGap`'s uniform version costs the constant
`δ / (1 + ‖C‖)`, which degenerates as `‖A‖ → ∞` -- and none is needed: the
uniqueness half of Theorem 8.1's printed `iff` tests one vector at a time. -/
theorem norm_starProjection_sub_sq_lt_of_orderedFormGap_unbounded
    (A : E →ₗ.[ℂ] E) (Hop : E →L[ℂ] E)
    (U V : Submodule ℂ E) [U.HasOrthogonalProjection] [V.HasOrthogonalProjection]
    {a b : ℝ}
    (hA : IsSelfAdjoint A) (hH : IsSelfAdjoint Hop)
    (hred : TauCeti.LinearPMap.ReducesSubspace A U)
    (hV : TauCeti.LinearPMap.ReducesSubspace (TauCeti.LinearPMap.addBounded A Hop) V)
    (hUhigh : ∀ x : A.domain, (x : E) ∈ U →
      b * ‖(x : E)‖ ^ 2 ≤ RCLike.re ⟪A x, (x : E)⟫_ℂ)
    (hUperpLow : ∀ x : A.domain, (x : E) ∈ Uᗮ →
      RCLike.re ⟪A x, (x : E)⟫_ℂ ≤ a * ‖(x : E)‖ ^ 2)
    (hVhigh : ∀ x : (TauCeti.LinearPMap.addBounded A Hop).domain, (x : E) ∈ V →
      b * ‖(x : E)‖ ^ 2 ≤
        RCLike.re ⟪TauCeti.LinearPMap.addBounded A Hop x, (x : E)⟫_ℂ)
    (hVperpLow : ∀ x : (TauCeti.LinearPMap.addBounded A Hop).domain, (x : E) ∈ Vᗮ →
      RCLike.re ⟪TauCeti.LinearPMap.addBounded A Hop x, (x : E)⟫_ℂ ≤
        a * ‖(x : E)‖ ^ 2)
    (hHU : ∀ x ∈ U, Hop x ∈ Uᗮ) (hHUperp : ∀ x ∈ Uᗮ, Hop x ∈ U)
    (hab : a < b) :
    ∀ y : E, y ≠ 0 →
      ‖U.starProjection y - V.starProjection y‖ ^ 2 < (1 / 2 : ℝ) * ‖y‖ ^ 2 := by
  intro y hy
  exact norm_starProjection_sub_sq_lt_of_reflectionProduct_form_pos U V
    (reflectionProduct_form_pos_of_orderedFormGap_unbounded A Hop U V
      hA hH hred hV hUhigh hUperpLow hVhigh hVperpLow hHU hHUperp hab y hy)

/-- **Davis--Kahan 1970, Theorem 8.1's printed angle conclusion, at unbounded
ambient scope.**

`A` is self-adjoint and possibly unbounded, `U` reduces `A`, the bounded
self-adjoint `H` is fully off-diagonal for `U`, and `V` reduces `A + H`.  Both
subspaces carry the printed ordered form gap with the same `a < b`.  Then the
maximal principal angle between `U` and `V` is at most `π/4`.

The non-strict form, which is what the supremum bound `‖P_U − P_V‖ ≤ √2/2` and
the printed `Θ ≤ π/4` consume. -/
theorem reflectionProduct_form_nonneg_of_orderedFormGap_unbounded
    (A : E →ₗ.[ℂ] E) (Hop : E →L[ℂ] E)
    (U V : Submodule ℂ E) [U.HasOrthogonalProjection] [V.HasOrthogonalProjection]
    {a b : ℝ}
    (hA : IsSelfAdjoint A) (hH : IsSelfAdjoint Hop)
    (hred : TauCeti.LinearPMap.ReducesSubspace A U)
    (hV : TauCeti.LinearPMap.ReducesSubspace (TauCeti.LinearPMap.addBounded A Hop) V)
    (hUhigh : ∀ x : A.domain, (x : E) ∈ U →
      b * ‖(x : E)‖ ^ 2 ≤ RCLike.re ⟪A x, (x : E)⟫_ℂ)
    (hUperpLow : ∀ x : A.domain, (x : E) ∈ Uᗮ →
      RCLike.re ⟪A x, (x : E)⟫_ℂ ≤ a * ‖(x : E)‖ ^ 2)
    (hVhigh : ∀ x : (TauCeti.LinearPMap.addBounded A Hop).domain, (x : E) ∈ V →
      b * ‖(x : E)‖ ^ 2 ≤
        RCLike.re ⟪TauCeti.LinearPMap.addBounded A Hop x, (x : E)⟫_ℂ)
    (hVperpLow : ∀ x : (TauCeti.LinearPMap.addBounded A Hop).domain, (x : E) ∈ Vᗮ →
      RCLike.re ⟪TauCeti.LinearPMap.addBounded A Hop x, (x : E)⟫_ℂ ≤
        a * ‖(x : E)‖ ^ 2)
    (hHU : ∀ x ∈ U, Hop x ∈ Uᗮ) (hHUperp : ∀ x ∈ Uᗮ, Hop x ∈ U)
    (hab : a < b) :
    ∀ y : E, 0 ≤ RCLike.re ⟪(V.reflectionOperator * U.reflectionOperator
      + U.reflectionOperator * V.reflectionOperator) y, y⟫_ℂ := by
  intro y
  rcases eq_or_ne y 0 with rfl | hy
  · simp
  · exact le_of_lt (reflectionProduct_form_pos_of_orderedFormGap_unbounded A Hop U V
      hA hH hred hV hUhigh hUperpLow hVhigh hVperpLow hHU hHUperp hab y hy)

/-- **Theorem 8.1's angle conclusion at unbounded scope.**  `Theta <= pi/4` for
the pair carrying the ordered form gap. -/
theorem maximalAngle_le_pi_div_four_of_orderedFormGap_unbounded
    (A : E →ₗ.[ℂ] E) (Hop : E →L[ℂ] E)
    (U V : Submodule ℂ E) [U.HasOrthogonalProjection] [V.HasOrthogonalProjection]
    {a b : ℝ}
    (hA : IsSelfAdjoint A) (hH : IsSelfAdjoint Hop)
    (hred : TauCeti.LinearPMap.ReducesSubspace A U)
    (hV : TauCeti.LinearPMap.ReducesSubspace (TauCeti.LinearPMap.addBounded A Hop) V)
    (hUhigh : ∀ x : A.domain, (x : E) ∈ U →
      b * ‖(x : E)‖ ^ 2 ≤ RCLike.re ⟪A x, (x : E)⟫_ℂ)
    (hUperpLow : ∀ x : A.domain, (x : E) ∈ Uᗮ →
      RCLike.re ⟪A x, (x : E)⟫_ℂ ≤ a * ‖(x : E)‖ ^ 2)
    (hVhigh : ∀ x : (TauCeti.LinearPMap.addBounded A Hop).domain, (x : E) ∈ V →
      b * ‖(x : E)‖ ^ 2 ≤
        RCLike.re ⟪TauCeti.LinearPMap.addBounded A Hop x, (x : E)⟫_ℂ)
    (hVperpLow : ∀ x : (TauCeti.LinearPMap.addBounded A Hop).domain, (x : E) ∈ Vᗮ →
      RCLike.re ⟪TauCeti.LinearPMap.addBounded A Hop x, (x : E)⟫_ℂ ≤
        a * ‖(x : E)‖ ^ 2)
    (hHU : ∀ x ∈ U, Hop x ∈ Uᗮ) (hHUperp : ∀ x ∈ Uᗮ, Hop x ∈ U)
    (hab : a < b) :
    TauCeti.DavisKahanExt.maximalAngle U V ≤ Real.pi / 4 :=
  maximalAngle_le_pi_div_four_of_reflectionProduct_form_nonneg U V
    (reflectionProduct_form_nonneg_of_orderedFormGap_unbounded A Hop U V hA hH hred hV
      hUhigh hUperpLow hVhigh hVperpLow hHU hHUperp hab)

/-- **Theorem 8.1's projector-gap conclusion at unbounded scope**, the same
statement before `arcsin`.  This is the shape Theorem 8.2's bootstrap comparison
consumes. -/
theorem subspaceGap_le_of_orderedFormGap_unbounded
    (A : E →ₗ.[ℂ] E) (Hop : E →L[ℂ] E)
    (U V : Submodule ℂ E) [U.HasOrthogonalProjection] [V.HasOrthogonalProjection]
    {a b : ℝ}
    (hA : IsSelfAdjoint A) (hH : IsSelfAdjoint Hop)
    (hred : TauCeti.LinearPMap.ReducesSubspace A U)
    (hV : TauCeti.LinearPMap.ReducesSubspace (TauCeti.LinearPMap.addBounded A Hop) V)
    (hUhigh : ∀ x : A.domain, (x : E) ∈ U →
      b * ‖(x : E)‖ ^ 2 ≤ RCLike.re ⟪A x, (x : E)⟫_ℂ)
    (hUperpLow : ∀ x : A.domain, (x : E) ∈ Uᗮ →
      RCLike.re ⟪A x, (x : E)⟫_ℂ ≤ a * ‖(x : E)‖ ^ 2)
    (hVhigh : ∀ x : (TauCeti.LinearPMap.addBounded A Hop).domain, (x : E) ∈ V →
      b * ‖(x : E)‖ ^ 2 ≤
        RCLike.re ⟪TauCeti.LinearPMap.addBounded A Hop x, (x : E)⟫_ℂ)
    (hVperpLow : ∀ x : (TauCeti.LinearPMap.addBounded A Hop).domain, (x : E) ∈ Vᗮ →
      RCLike.re ⟪TauCeti.LinearPMap.addBounded A Hop x, (x : E)⟫_ℂ ≤
        a * ‖(x : E)‖ ^ 2)
    (hHU : ∀ x ∈ U, Hop x ∈ Uᗮ) (hHUperp : ∀ x ∈ Uᗮ, Hop x ∈ U)
    (hab : a < b) :
    U.projectionGap V ≤ Real.sqrt 2 / 2 :=
  subspaceGap_le_of_reflectionProduct_form_nonneg U V
    (reflectionProduct_form_nonneg_of_orderedFormGap_unbounded A Hop U V hA hH hred hV
      hUhigh hUperpLow hVhigh hVperpLow hHU hHUperp hab)

/-- **Theorem 8.1's projector-gap conclusion in the paper's own orientation, at
unbounded scope.**  The angle form below, before `arcsin`; this is what Theorem
8.2's bootstrap comparison consumes. -/
theorem subspaceGap_le_of_orderedFormGap_unbounded_printed
    (A : E →ₗ.[ℂ] E) (Hop : E →L[ℂ] E)
    (P Q : Submodule ℂ E) [P.HasOrthogonalProjection] [Q.HasOrthogonalProjection]
    {alpha delta : ℝ}
    (hA : IsSelfAdjoint A) (hH : IsSelfAdjoint Hop)
    (hredP : TauCeti.LinearPMap.ReducesSubspace A Pᗮ)
    (hQ : TauCeti.LinearPMap.ReducesSubspace (TauCeti.LinearPMap.addBounded A Hop) Qᗮ)
    (hPlow : ∀ x : A.domain, (x : E) ∈ P →
      RCLike.re ⟪A x, (x : E)⟫_ℂ ≤ alpha * ‖(x : E)‖ ^ 2)
    (hPhigh : ∀ x : A.domain, (x : E) ∈ Pᗮ →
      (alpha + delta) * ‖(x : E)‖ ^ 2 ≤ RCLike.re ⟪A x, (x : E)⟫_ℂ)
    (hQlow : ∀ x : (TauCeti.LinearPMap.addBounded A Hop).domain, (x : E) ∈ Q →
      RCLike.re ⟪TauCeti.LinearPMap.addBounded A Hop x, (x : E)⟫_ℂ ≤
        alpha * ‖(x : E)‖ ^ 2)
    (hQhigh : ∀ x : (TauCeti.LinearPMap.addBounded A Hop).domain, (x : E) ∈ Qᗮ →
      (alpha + delta) * ‖(x : E)‖ ^ 2 ≤
        RCLike.re ⟪TauCeti.LinearPMap.addBounded A Hop x, (x : E)⟫_ℂ)
    (hHP : ∀ x ∈ P, Hop x ∈ Pᗮ) (hHPperp : ∀ x ∈ Pᗮ, Hop x ∈ P)
    (hdelta : 0 < delta) :
    P.projectionGap Q ≤ Real.sqrt 2 / 2 := by
  have hPperpperp : (Pᗮ)ᗮ = P := Submodule.orthogonal_orthogonal P
  have hQperpperp : (Qᗮ)ᗮ = Q := Submodule.orthogonal_orthogonal Q
  have hcompl := subspaceGap_le_of_orderedFormGap_unbounded A Hop Pᗮ Qᗮ
    (a := alpha) (b := alpha + delta) hA hH hredP hQ
    hPhigh (by
      intro x hx
      rw [hPperpperp] at hx
      exact hPlow x hx)
    hQhigh (by
      intro x hx
      rw [hQperpperp] at hx
      exact hQlow x hx)
    (by
      intro x hx
      rw [hPperpperp]
      exact hHPperp x hx)
    (by
      intro x hx
      rw [hPperpperp] at hx
      exact hHP x hx)
    (by linarith)
  have hgap : Pᗮ.projectionGap Qᗮ = P.projectionGap Q :=
    TauCeti.DavisKahan.subspaceGap_orthogonal P Q
  rw [← hgap]
  exact hcompl

/-- **Theorem 8.1's angle conclusion in the paper's own orientation, at unbounded
scope.**

Davis and Kahan write the hypotheses on `P` and `Q` themselves -- the form of `A`
at most `alpha` on `P` and at least `alpha + delta` on `P^perp`, and the same for
`A + H` on `Q` -- and conclude `Theta <= pi/4` for the pair `(P, Q)`.  The
previous theorem is stated on the complements, which is where the reflection
argument runs; the projector gap does not see the flip, so the two are the same
statement. -/
theorem maximalAngle_le_pi_div_four_of_orderedFormGap_unbounded_printed
    (A : E →ₗ.[ℂ] E) (Hop : E →L[ℂ] E)
    (P Q : Submodule ℂ E) [P.HasOrthogonalProjection] [Q.HasOrthogonalProjection]
    {alpha delta : ℝ}
    (hA : IsSelfAdjoint A) (hH : IsSelfAdjoint Hop)
    (hredP : TauCeti.LinearPMap.ReducesSubspace A Pᗮ)
    (hQ : TauCeti.LinearPMap.ReducesSubspace (TauCeti.LinearPMap.addBounded A Hop) Qᗮ)
    (hPlow : ∀ x : A.domain, (x : E) ∈ P →
      RCLike.re ⟪A x, (x : E)⟫_ℂ ≤ alpha * ‖(x : E)‖ ^ 2)
    (hPhigh : ∀ x : A.domain, (x : E) ∈ Pᗮ →
      (alpha + delta) * ‖(x : E)‖ ^ 2 ≤ RCLike.re ⟪A x, (x : E)⟫_ℂ)
    (hQlow : ∀ x : (TauCeti.LinearPMap.addBounded A Hop).domain, (x : E) ∈ Q →
      RCLike.re ⟪TauCeti.LinearPMap.addBounded A Hop x, (x : E)⟫_ℂ ≤
        alpha * ‖(x : E)‖ ^ 2)
    (hQhigh : ∀ x : (TauCeti.LinearPMap.addBounded A Hop).domain, (x : E) ∈ Qᗮ →
      (alpha + delta) * ‖(x : E)‖ ^ 2 ≤
        RCLike.re ⟪TauCeti.LinearPMap.addBounded A Hop x, (x : E)⟫_ℂ)
    (hHP : ∀ x ∈ P, Hop x ∈ Pᗮ) (hHPperp : ∀ x ∈ Pᗮ, Hop x ∈ P)
    (hdelta : 0 < delta) :
    TauCeti.DavisKahanExt.maximalAngle P Q ≤ Real.pi / 4 := by
  have hPperpperp : (Pᗮ)ᗮ = P := Submodule.orthogonal_orthogonal P
  have hQperpperp : (Qᗮ)ᗮ = Q := Submodule.orthogonal_orthogonal Q
  have hcompl := maximalAngle_le_pi_div_four_of_orderedFormGap_unbounded A Hop Pᗮ Qᗮ
    (a := alpha) (b := alpha + delta) hA hH hredP hQ
    hPhigh (by
      intro x hx
      rw [hPperpperp] at hx
      exact hPlow x hx)
    hQhigh (by
      intro x hx
      rw [hQperpperp] at hx
      exact hQlow x hx)
    (by
      intro x hx
      rw [hPperpperp]
      exact hHPperp x hx)
    (by
      intro x hx
      rw [hPperpperp] at hx
      exact hHP x hx)
    (by linarith)
  have hgap : Pᗮ.projectionGap Qᗮ = P.projectionGap Q :=
    TauCeti.DavisKahan.subspaceGap_orthogonal P Q
  change Real.arcsin (P.projectionGap Q) ≤ Real.pi / 4
  rw [← hgap]
  exact hcompl

/-- **The pointwise strict quarter-angle bound in the paper's own orientation.**

The complement statement restated on `P` and `Q` themselves: the projector
difference does not see the flip, so the two are the same inequality. -/
theorem norm_starProjection_sub_sq_lt_of_orderedFormGap_unbounded_printed
    (A : E →ₗ.[ℂ] E) (Hop : E →L[ℂ] E)
    (P Q : Submodule ℂ E) [P.HasOrthogonalProjection] [Q.HasOrthogonalProjection]
    {alpha delta : ℝ}
    (hA : IsSelfAdjoint A) (hH : IsSelfAdjoint Hop)
    (hredP : TauCeti.LinearPMap.ReducesSubspace A Pᗮ)
    (hQ : TauCeti.LinearPMap.ReducesSubspace (TauCeti.LinearPMap.addBounded A Hop) Qᗮ)
    (hPlow : ∀ x : A.domain, (x : E) ∈ P →
      RCLike.re ⟪A x, (x : E)⟫_ℂ ≤ alpha * ‖(x : E)‖ ^ 2)
    (hPhigh : ∀ x : A.domain, (x : E) ∈ Pᗮ →
      (alpha + delta) * ‖(x : E)‖ ^ 2 ≤ RCLike.re ⟪A x, (x : E)⟫_ℂ)
    (hQlow : ∀ x : (TauCeti.LinearPMap.addBounded A Hop).domain, (x : E) ∈ Q →
      RCLike.re ⟪TauCeti.LinearPMap.addBounded A Hop x, (x : E)⟫_ℂ ≤
        alpha * ‖(x : E)‖ ^ 2)
    (hQhigh : ∀ x : (TauCeti.LinearPMap.addBounded A Hop).domain, (x : E) ∈ Qᗮ →
      (alpha + delta) * ‖(x : E)‖ ^ 2 ≤
        RCLike.re ⟪TauCeti.LinearPMap.addBounded A Hop x, (x : E)⟫_ℂ)
    (hHP : ∀ x ∈ P, Hop x ∈ Pᗮ) (hHPperp : ∀ x ∈ Pᗮ, Hop x ∈ P)
    (hdelta : 0 < delta) :
    ∀ y : E, y ≠ 0 →
      ‖P.starProjection y - Q.starProjection y‖ ^ 2 < (1 / 2 : ℝ) * ‖y‖ ^ 2 := by
  intro y hy
  have hPperpperp : (Pᗮ)ᗮ = P := Submodule.orthogonal_orthogonal P
  have hQperpperp : (Qᗮ)ᗮ = Q := Submodule.orthogonal_orthogonal Q
  have hcompl := norm_starProjection_sub_sq_lt_of_orderedFormGap_unbounded A Hop Pᗮ Qᗮ
    (a := alpha) (b := alpha + delta) hA hH hredP hQ
    hPhigh (by
      intro x hx
      rw [hPperpperp] at hx
      exact hPlow x hx)
    hQhigh (by
      intro x hx
      rw [hQperpperp] at hx
      exact hQlow x hx)
    (by
      intro x hx
      rw [hPperpperp]
      exact hHPperp x hx)
    (by
      intro x hx
      rw [hPperpperp] at hx
      exact hHP x hx)
    (by linarith) y hy
  have hnorm : ‖Pᗮ.starProjection y - Qᗮ.starProjection y‖
      = ‖P.starProjection y - Q.starProjection y‖ := by
    rw [Submodule.starProjection_orthogonal_apply,
      Submodule.starProjection_orthogonal_apply,
      show y - P.starProjection y - (y - Q.starProjection y)
        = Q.starProjection y - P.starProjection y by abel, norm_sub_rev]
  rwa [hnorm] at hcompl

/-- **From the closed quarter branch to the open one.**

Davis--Kahan's Theorem 8.2 concludes `Theta < pi/4`, strictly, where Theorem 8.1
concludes `Theta <= pi/4`.  The strictness comes from the double-angle bound, not
from a second branch argument: on the *closed* branch the double-angle sine
dominates `sqrt 2` times the directed gap, so a strict contraction there forces
the gap strictly below `sqrt 2 / 2`.

This is why unbounded Theorem 8.2's acute conclusion does not need a homotopy or
a Riesz projection.  Theorem 8.1 at unbounded scope supplies the closed branch;
the unbounded `sin 2Theta` estimate supplies `‖sin 2Theta‖ <= 2‖H‖/delta < 1`
under the printed smallness hypothesis; and this lemma closes the gap. -/
theorem subspaceGap_lt_of_le_of_norm_sinTwoAngle_lt_one
    (U V : Submodule ℂ E)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection]
    (hcross : TauCeti.DavisKahan.CrossedDefectsEquivalent V U)
    (hle : U.projectionGap V ≤ Real.sqrt 2 / 2)
    (hsin : ‖DavisKahanExt.sinTwoAngleOperator U V‖ < 1) :
    U.projectionGap V < Real.sqrt 2 / 2 := by
  have hsym : U.projectionGap V = V.projectionGap U := by
    change ‖U.starProjection - V.starProjection‖ = ‖V.starProjection - U.starProjection‖
    rw [← norm_neg]
    congr 1
    abel
  have hdir : V.projectionGap U = V.directedProjectionGap U :=
    TauCeti.DavisKahan.subspaceGap_eq_directedGap_of_crossedDefectsEquivalent V U hcross
  have hclose : V.directedProjectionGap U ≤ Real.sqrt 2 / 2 := by
    rw [← hdir, ← hsym]
    exact hle
  have hboot := TauCeti.DavisKahan.Angle.sqrt_two_mul_directedGap_le_norm_sinTwoAngleOperator
    U V hclose
  have hs2 : (0 : ℝ) < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
  have h2 : Real.sqrt 2 * Real.sqrt 2 = 2 := Real.mul_self_sqrt (by norm_num)
  have hstrict : V.directedProjectionGap U < Real.sqrt 2 / 2 := by nlinarith [hboot, hsin, hs2]
  rw [hsym, hdir]
  exact hstrict

/-- The same, in the printed angle form. -/
theorem maximalAngle_lt_pi_div_four_of_le_of_norm_sinTwoAngle_lt_one
    (U V : Submodule ℂ E)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection]
    (hcross : TauCeti.DavisKahan.CrossedDefectsEquivalent V U)
    (hle : U.projectionGap V ≤ Real.sqrt 2 / 2)
    (hsin : ‖DavisKahanExt.sinTwoAngleOperator U V‖ < 1) :
    TauCeti.DavisKahanExt.maximalAngle U V < Real.pi / 4 :=
  (TauCeti.DavisKahan1970.Section8.maximalAngle_lt_pi_div_four_iff U V).2
    (subspaceGap_lt_of_le_of_norm_sinTwoAngle_lt_one U V hcross hle hsin)

end

end DavisKahan
end TauCeti
