/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, OpenAI GPT-5.6 Thinking, Claude Opus 5
-/

import LeanPool.DavisKahan.DavisKahan.Sources.DavisKahan1970.Section8.Theorem81
import LeanPool.DavisKahan.DavisKahan.InfiniteDimensional.SinTheta.Continuation.CircleWitness
import LeanPool.DavisKahan.DavisKahan.Geometry.Angle.DoubleAngleGapBound
import LeanPool.DavisKahan.DavisKahan.SpectralTheory.CentralBand
import LeanPool.DavisKahan.DavisKahan.BoundedOperator.TrialResidual
import LeanPool.DavisKahan.ForTauCeti.Analysis.InnerProductSpace.Polar.SelfAdjointCompletion

/-! # Theorem82Branch -/

open TauCeti.DavisKahan.Angle


open TauCeti.DavisKahan.Sylvester

/-!
# Davis--Kahan 1970, Theorem 8.2: branch selection under either smallness hypothesis

Theorem 8.2 offers two alternatives, `‖H‖ < δ/2` *or* `‖R‖ < δ/2`.  This module
proves both from the printed hypotheses alone.  Nothing quantitative is supplied
by the caller: no contour, no continuation witness, no projection-Lipschitz
constant, no half-gap bridge, no Krein completion, no alternative perturbation.
All of those are proof internals, and the machinery that carries them lives
outside this module:

* the canonical gap circle, the separating-circle construction from a spectral
  gap, and the continuation witness it produces --
  `InfiniteDimensional/SinTheta/Continuation/CircleWitness.lean`;
* the central band and its identification from the printed spectral hypotheses
  -- `SpectralTheory/CentralBand.lean`;
* the reverse comparison `‖sin 2Θ‖ ≥ √2 · directedGap` on the closed quarter
  branch -- `Geometry/Angle/DoubleAngleGapBound.lean`;
* Krein's ambient self-adjoint completion with the exact restriction norm --
  `ForTauCeti/Analysis/InnerProductSpace/Polar/SelfAdjointCompletion.lean`;
* the invariance-only residual identity `R = K E₀` --
  `BoundedOperator/TrialResidual.lean`.

## The residual alternative

The printed proof of the second alternative is one sentence:

> If instead `‖R‖₁ < δ/2`, we use the fact that, without changing `A₁ + H₁`,
> `R`, or the `Λⱼ`, one may change `H₁`.  A theorem of Krein gives a choice
> with `‖H‖₁ = ‖R‖₁`, reducing the argument to the preceding case.

Both halves of that sentence are theorems here, so the residual capstone is
exactly the reduction.  The paper's residual is equation (1.8),
`R = (A + H) E₀ - E₀ A₀`, and the source also records `R⋆ R = H₀² + B⋆ B`, so
`R` is the *first block column* `(H₀, B)` of the perturbation rather than its
off-diagonal corner.  That is what makes the reduction exact: Krein's theorem
completes a column to a self-adjoint operator of the *same* norm, so
`‖H'‖ = ‖R‖` on the nose.  With `H' := K'` the completion and
`A' := A + K - K'`,

```
A' + K' = A + K          -- every perturbed datum is literally unchanged
A'|P    = A|P            -- every unperturbed datum on P is literally unchanged
K'|P    = K|P  = R       -- the residual itself is unchanged
‖K'‖    = ‖R‖            -- Krein, with the exact norm
```

and only the `Pᗮ` diagonal block `H₁` moves, which is precisely the freedom the
printed sentence uses.
-/

open scoped InnerProductSpace
open Set

namespace TauCeti
namespace DavisKahan1970
namespace Section8


open DavisKahanExt
open TauCeti.DavisKahan
open TauCeti.DavisKahan.Foundation
open TauCeti.DavisKahan.RieszCircle

universe u

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H]

/-! ## Spectral data on `P` only sees the operator on `P` -/

omit [CompleteSpace H] in
/-- **`SpectrumIn` transfers along agreement on the subspace.**

`restrictedSpectrum` is the spectrum of an honest restriction, so two operators
agreeing pointwise on `P` have the same `P`-block and therefore the same
`P`-spectrum.  This is what makes the Krein replacement free on the unperturbed
side: `A'` and `A` agree on `P`, so the printed placement of `A₀` transfers
literally rather than being re-derived. -/
theorem spectrumIn_of_eqOn {A B : H →L[ℂ] H} {P : Submodule ℂ H} {s : Set ℝ}
    (heq : ∀ x ∈ P, A x = B x) (h : SpectrumIn A P s) : SpectrumIn B P s := by
  have hinv : InvariantFor B P := by
    intro x hx
    rw [← heq x hx]
    exact h.1 x hx
  refine ⟨hinv, ?_⟩
  have hres : B.restrict hinv = A.restrict h.1 := by
    apply ContinuousLinearMap.ext
    intro u
    apply Subtype.ext
    change B (u : H) = A (u : H)
    exact (heq (u : H) u.2).symm
  rw [restrictedSpectrum_eq_restrictionSpectrum B P hinv, hres,
    ← restrictedSpectrum_eq_restrictionSpectrum A P h.1]
  exact h.2


/-! ## The perturbation-norm alternative -/

section PerturbationAlternative

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H]

/-- **Davis--Kahan 1970, Theorem 8.2, perturbation alternative: the branch is
strictly inside the quarter turn.**

The hypotheses are exactly the printed ones.  `A` and `K` are self-adjoint
(`K` is the paper's `H`); `Q` is a reducing subspace of `A + K` carrying the
`sin 2Θ` spectral placement -- `Λ₀` inside `[β, α]`, `Λ₁` outside
`(β - δ, α + δ)`; `P` is a reducing subspace of `A` whose block `A₀` has
spectrum in the enlarged central interval `[β - δ/2, α + δ/2]`, which is the
extra hypothesis Theorem 8.2 adds; and `‖K‖ < δ/2` is the printed
perturbation alternative.

No contour, no continuation witness, no projection-Lipschitz constant and no
half-gap bridge appears among the hypotheses: they are all constructed inside
the proof, following the printed connectedness bootstrap.

The conclusion is the printed `Θ < π/4` in its directed form: every unit vector
of `P H` makes an angle strictly below `π/4` with `Q H`.  See the module
docstring for why the symmetric projector gap is *not* what the printed
statement can mean. -/
theorem theorem8_2_perturbationHalfGap_complex
    {A K : H →L[ℂ] H} (hA : A.IsSymmetric) (hK : K.IsSymmetric)
    {P Q : Submodule ℂ H} [P.HasOrthogonalProjection] [Q.HasOrthogonalProjection]
    {alpha beta delta : ℝ} (hdelta : 0 < delta) (hab : beta ≤ alpha)
    (hQ : SpectrumIn (A + K) Q (Set.Icc beta alpha))
    (hQperp : SpectrumIn (A + K) Qᗮ (gapExterior beta alpha delta))
    (hPred : A.Reduces P)
    (hP : SpectrumIn A P (Set.Icc (beta - delta / 2) (alpha + delta / 2)))
    (hsmall : ‖K‖ < delta / 2) :
    P.directedProjectionGap Q < Real.sqrt 2 / 2 := by
  classical
  set gam : ℝ := ‖K‖ with hgamdef
  have hgam0 : (0 : ℝ) ≤ gam := norm_nonneg K
  set l : ℝ := beta - gam with hldef
  set rr : ℝ := alpha + gam with hrdef
  set d : ℝ := delta - 2 * gam with hddef
  have hd : 0 < d := by rw [hddef]; linarith
  have hlr : l ≤ rr := by rw [hldef, hrdef]; linarith
  -- the path
  set A0 : H →L[ℂ] H := A + K with hA0def
  have hA0 : A0.IsSymmetric := hA.add hK
  set E : H →L[ℂ] H := -K with hEdef
  have hE : E.IsSymmetric := by
    intro x y
    change ⟪-(K x), y⟫_ℂ = ⟪x, -(K y)⟫_ℂ
    have h : ⟪K x, y⟫_ℂ = ⟪x, K y⟫_ℂ := hK x y
    rw [inner_neg_left, inner_neg_right, h]
  have hBself : ∀ t : ℝ, (A0 + t • E).IsSymmetric := fun t =>
    isSelfAdjointOperator_path hA0 hE t
  have hB0 : A0 + (0 : ℝ) • E = A0 := by simp
  have hB1 : A0 + (1 : ℝ) • E = A := by
    rw [one_smul, hA0def, hEdef]; abel
  have hnormE : ∀ t : ℝ, t ∈ Set.Icc (0 : ℝ) 1 → ‖(t • E : H →L[ℂ] H)‖ = t * gam := by
    intro t ht
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg ht.1, hEdef, norm_neg]
  -- the ambient gap at the start of the path, from the printed `sin 2Θ` data
  have hQred : A0.Reduces Q := ⟨hQ.invariant, hQperp.invariant⟩
  have hgap0 : realSpectrum A0 ⊆
      Set.Icc beta alpha ∪ gapExterior beta alpha delta :=
    realSpectrum_subset_union_of_reduces hA0 hQred hQ hQperp
  have hgapt : ∀ t : ℝ, t ∈ Set.Icc (0 : ℝ) 1 →
      realSpectrum (A0 + t • E) ⊆ Set.Icc l rr ∪ gapExterior l rr d := by
    intro t ht
    refine realSpectrum_add_subset_of_gap hA0 hab hdelta hgam0 (by linarith) ?_ hgap0
    rw [hnormE t ht]
    nlinarith [ht.1, ht.2]
  -- the moving band subspace and its Riesz representation
  set cen : ℝ := gapCenter l rr with hcendef
  set rad : ℝ := (rr - l + d) / 2 with hraddef
  have hradpos : 0 < rad := by rw [hraddef]; linarith
  have hsep : ∀ t : ℝ, t ∈ Set.Icc (0 : ℝ) 1 →
      CircleSeparatesRealSpectrum (A0 + t • E) (hBself t) (centralBand l rr d)
        cen rad := fun t ht => circleSeparates_of_gap (hBself t) hlr hd (hgapt t ht)
  set R : ℝ → Submodule ℂ H := fun t =>
    centralBandSubspace (A0 + t • E) (hBself t) (l := l) (r := rr) (d := d) with hRdef
  have hproj : ∀ t : ℝ, t ∈ Set.Icc (0 : ℝ) 1 →
      (R t).starProjection = circleRieszProjection (A0 + t • E) cen rad := by
    intro t ht
    change (centralBandSubspace (A0 + t • E) (hBself t)
      (l := l) (r := rr) (d := d)).starProjection = _
    rw [starProjection_centralBandSubspace]
    exact (circleRieszProjection_eq_boundedSelfAdjointSpectralProjection
      (A0 + t • E) (hBself t) (centralBand l rr d)
      (measurableSet_centralBand l rr d) cen rad (hsep t ht)).symm
  -- norm continuity of the moving projection
  have hunit : ∀ t : ℝ, t ∈ Set.Icc (0 : ℝ) 1 → ∀ z : ℂ,
      ‖z - (cen : ℂ)‖ = rad → IsUnit (z • (1 : H →L[ℂ] H) - (A0 + t • E)) := by
    intro t ht z hz
    have hnot := (hsep t ht).contour_resolvent z hz
    have h := spectrum.notMem_iff.mp hnot
    rwa [Algebra.algebraMap_eq_smul_one] at h
  have hcontRiesz : ContinuousOn
      (fun t : ℝ => circleRieszProjection (A0 + t • E) cen rad)
      (Set.Icc 0 1) :=
    continuous_circleRieszProjection_path A0 E cen rad hradpos.le hunit
  set f : ℝ → ℝ := fun t => Submodule.directedProjectionGap (R t) Q with hfdef
  have hfeq : ∀ t : ℝ, t ∈ Set.Icc (0 : ℝ) 1 →
      f t = ‖Qᗮ.starProjection ∘L
        circleRieszProjection (A0 + t • E) cen rad‖ := by
    intro t ht
    change ‖Qᗮ.starProjection ∘L (R t).starProjection‖ = _
    rw [hproj t ht]
  have hfcont : ContinuousOn f (Set.Icc 0 1) := by
    refine ContinuousOn.congr ?_ (fun t ht => hfeq t ht)
    exact (continuous_norm.comp
      (ContinuousLinearMap.compL ℂ H H H Qᗮ.starProjection).continuous).comp_continuousOn
      hcontRiesz
  -- the exterior placement, weakened to the shrunken configuration
  have hextmono : gapExterior beta alpha delta ⊆ gapExterior l rr d := by
    rintro x (hx | hx)
    · exact Or.inl (by rw [hldef, hddef]; linarith)
    · exact Or.inr (by rw [hrdef, hddef]; linarith)
  -- `R 0 ≤ Q`
  have hR0 : R 0 ≤ Q := by
    have hQperp' : SpectrumIn (A0 + (0 : ℝ) • E) Qᗮ (gapExterior l rr d) := by
      rw [hB0]; exact hQperp.mono hextmono
    have hQred' : ContinuousLinearMap.Reduces (A0 + (0 : ℝ) • E) Q := by rw [hB0]; exact hQred
    exact centralBandSubspace_le_of_spectrumIn_gapExterior _ (hBself 0) hd hlr
      (hgapt 0 ⟨le_rfl, zero_le_one⟩) hQred' hQperp'
  have hf0 : f 0 = 0 := by
    change ‖Qᗮ.starProjection ∘L (R 0).starProjection‖ = 0
    rw [norm_eq_zero]
    ext x
    have hmem : (R 0).starProjection x ∈ Q := hR0 ((R 0).starProjection_apply_mem x)
    change Qᗮ.starProjection ((R 0).starProjection x) = 0
    rw [Submodule.starProjection_orthogonal_apply,
      Submodule.starProjection_eq_self_iff.mpr hmem, sub_self]
  -- `P ≤ R 1`
  have hR1 : P ≤ R 1 := by
    have hPred' : ContinuousLinearMap.Reduces (A0 + (1 : ℝ) • E) P := by rw [hB1]; exact hPred
    have hP' : SpectrumIn (A0 + (1 : ℝ) • E) P
        (Set.Icc (beta - delta / 2) (alpha + delta / 2)) := by rw [hB1]; exact hP
    refine le_centralBandSubspace_of_spectrumIn_Icc _ (hBself 1) hd hlr
      (by linarith) (hgapt 1 ⟨zero_le_one, le_rfl⟩) hPred' hP' ?_ ?_
    · rw [gapCenter, gapCenter, hldef, hrdef]; ring
    · rw [hldef, hrdef, hddef]; linarith
  -- the bootstrap: closed quarter angle forces strict quarter angle
  have hboot : ∀ t : ℝ, t ∈ Set.Icc (0 : ℝ) 1 → f t ≤ Real.sqrt 2 / 2 →
      f t < Real.sqrt 2 / 2 := by
    intro t ht hclose
    have hfinite : FiniteGapConfiguration A0 Q delta := ⟨beta, alpha, hab, hQ, hQperp⟩
    have hVred : ContinuousLinearMap.Reduces (A0 + t • E) (R t) :=
      centralBandSubspace_reduces (A0 + t • E) (hBself t)
    have hsin := sinTwoTheta_perturbation (A := A0) (B := A0 + t • E)
      hA0 (U := Q) (V := R t) hQred hVred hdelta hfinite
    have hdiff : ‖(A0 + t • E) - A0‖ = t * gam := by
      rw [show (A0 + t • E) - A0 = t • E by abel]
      exact hnormE t ht
    rw [hdiff] at hsin
    have hlowbnd : Real.sqrt 2 * f t ≤ ‖sinTwoAngleOperator Q (R t)‖ :=
      sqrt_two_mul_directedGap_le_norm_sinTwoAngleOperator Q (R t) hclose
    have h2 : Real.sqrt 2 * f t * delta ≤ 2 * (t * gam) := by nlinarith [hsin, hlowbnd]
    have htg : t * gam ≤ gam := by nlinarith [ht.1, ht.2, hgam0]
    have hstrict : Real.sqrt 2 * f t * delta < delta := by nlinarith [h2, htg, hsmall]
    have hlt : Real.sqrt 2 * f t < 1 := by
      by_contra hcon
      rw [not_lt] at hcon
      nlinarith [hstrict, hdelta]
    have hs2 : Real.sqrt 2 * (Real.sqrt 2 / 2) = 1 := by
      rw [show Real.sqrt 2 * (Real.sqrt 2 / 2) = Real.sqrt 2 ^ 2 / 2 by ring,
        Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
      norm_num
    have hpos2 : (0 : ℝ) < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
    by_contra hcon
    rw [not_lt] at hcon
    nlinarith [hlt, hs2, hpos2, hcon]
  -- connectedness: `f` never reaches the quarter turn
  have hall : ∀ t : ℝ, t ∈ Set.Icc (0 : ℝ) 1 → f t < Real.sqrt 2 / 2 := by
    intro s hs
    by_contra hcon
    rw [not_lt] at hcon
    have hsub : Set.Icc (0 : ℝ) s ⊆ Set.Icc (0 : ℝ) 1 :=
      Set.Icc_subset_Icc le_rfl hs.2
    have hcont' : ContinuousOn f (Set.Icc 0 s) := hfcont.mono hsub
    have hmem : Real.sqrt 2 / 2 ∈ Set.Icc (f 0) (f s) := by
      rw [hf0]
      exact ⟨sqrt_two_div_two_pos.le, hcon⟩
    obtain ⟨t, htmem, hft⟩ :=
      intermediate_value_Icc hs.1 hcont' hmem
    have ht1 : t ∈ Set.Icc (0 : ℝ) 1 := hsub htmem
    have := hboot t ht1 (le_of_eq hft)
    rw [hft] at this
    exact lt_irrefl _ this
  -- transport to the source pair
  have hfixP : (R 1).starProjection ∘L P.starProjection = P.starProjection := by
    ext x
    change (R 1).starProjection (P.starProjection x) = P.starProjection x
    exact Submodule.starProjection_eq_self_iff.mpr
      (hR1 (P.starProjection_apply_mem x))
  have hle : P.directedProjectionGap Q ≤ f 1 := by
    change ‖Qᗮ.starProjection ∘L P.starProjection‖ ≤
      ‖Qᗮ.starProjection ∘L (R 1).starProjection‖
    calc ‖Qᗮ.starProjection ∘L P.starProjection‖
        = ‖(Qᗮ.starProjection ∘L (R 1).starProjection) ∘L P.starProjection‖ := by
          rw [ContinuousLinearMap.comp_assoc, hfixP]
      _ ≤ ‖Qᗮ.starProjection ∘L (R 1).starProjection‖ * ‖P.starProjection‖ :=
          ContinuousLinearMap.opNorm_comp_le _ _
      _ ≤ ‖Qᗮ.starProjection ∘L (R 1).starProjection‖ * 1 := by
          have := P.starProjection_norm_le
          nlinarith [norm_nonneg (Qᗮ.starProjection ∘L (R 1).starProjection)]
      _ = ‖Qᗮ.starProjection ∘L (R 1).starProjection‖ := mul_one _
  exact lt_of_le_of_lt hle (hall 1 ⟨zero_le_one, le_rfl⟩)

/-- **The same conclusion in the printed scalar form.**  The directed angle
from `P H` into `Q H` is strictly below `π / 4`. -/
theorem theorem8_2_perturbationHalfGap_angle_lt
    {A K : H →L[ℂ] H} (hA : A.IsSymmetric) (hK : K.IsSymmetric)
    {P Q : Submodule ℂ H} [P.HasOrthogonalProjection] [Q.HasOrthogonalProjection]
    {alpha beta delta : ℝ} (hdelta : 0 < delta) (hab : beta ≤ alpha)
    (hQ : SpectrumIn (A + K) Q (Set.Icc beta alpha))
    (hQperp : SpectrumIn (A + K) Qᗮ (gapExterior beta alpha delta))
    (hPred : A.Reduces P)
    (hP : SpectrumIn A P (Set.Icc (beta - delta / 2) (alpha + delta / 2)))
    (hsmall : ‖K‖ < delta / 2) :
    Real.arcsin (P.directedProjectionGap Q) < Real.pi / 4 := by
  have h := theorem8_2_perturbationHalfGap_complex hA hK hdelta hab hQ hQperp hPred hP
    hsmall
  have h0 : (0 : ℝ) ≤ P.directedProjectionGap Q := norm_nonneg _
  rw [← DavisKahan1970.Section8.arcsin_sqrt_two_div_two]
  refine Real.arcsin_lt_arcsin (by linarith) h ?_
  have : Real.sqrt 2 ≤ 2 := by
    nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2), Real.sqrt_nonneg 2]
  linarith

end PerturbationAlternative

/-! ## The residual alternative -/

section ResidualAlternative

/-- **Davis--Kahan 1970, Theorem 8.2, residual alternative: the branch is
strictly inside the quarter turn.**

The hypotheses are the printed ones, identical to
`theorem8_2_perturbationHalfGap_complex` except that the smallness assumption is
the printed residual condition `‖R‖ < δ/2` in place of `‖H‖ < δ/2`.  `R` is the
source residual (1.8), `R = (A + K) E₀ - E₀ A₀`.

No caller-supplied certificate appears: no `ResidualHalfGapBridge`, no
`SpectralContinuationWitness`, no Krein completion, no alternative perturbation
`A'`, no branch-selection datum.  All of those are proof internals.

The proof is the printed reduction.  Krein's theorem
(`TauCeti.exists_selfAdjoint_completion_eq_norm_restriction`) replaces `K` by a
self-adjoint `K'` with the same first column and with `‖K'‖ = ‖R‖`; setting
`A' := A + K - K'` leaves `A' + K' = A + K` and `A'|P = A|P`, so every printed
hypothesis transfers verbatim and
`theorem8_2_perturbationHalfGap_complex` applies to `(A', K')`. -/
theorem theorem8_2_residualHalfGap_complex
    {A K : H →L[ℂ] H} (hA : A.IsSymmetric) (hK : K.IsSymmetric)
    {P Q : Submodule ℂ H} [P.HasOrthogonalProjection] [Q.HasOrthogonalProjection]
    {alpha beta delta : ℝ} (hdelta : 0 < delta) (hab : beta ≤ alpha)
    (hQ : SpectrumIn (A + K) Q (Set.Icc beta alpha))
    (hQperp : SpectrumIn (A + K) Qᗮ (gapExterior beta alpha delta))
    (hPred : A.Reduces P)
    (hP : SpectrumIn A P (Set.Icc (beta - delta / 2) (alpha + delta / 2)))
    (hRsmall : ‖residual (A + K) P.subtypeL (compressOperator P A)‖ < delta / 2) :
    P.directedProjectionGap Q < Real.sqrt 2 / 2 := by
  classical
  let : CompleteSpace P :=
    (P.isComplete_coe_of_hasOrthogonalProjection).completeSpace_coe
  -- the printed residual is the first block column of the perturbation
  have hRcol : residual (A + K) P.subtypeL (compressOperator P A) = K ∘L P.subtypeL :=
    BoundedOperator.residual_eq_comp_subtypeL A K P hPred.1
  rw [hRcol, TauCeti.norm_comp_subtypeL_eq_norm_comp_starProjection] at hRsmall
  -- Krein's replacement: same first column, norm exactly the residual norm
  obtain ⟨K', hK'sa, hK'col, hK'norm⟩ :=
    TauCeti.exists_selfAdjoint_completion_eq_norm_restriction K
      (ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mpr hK) P
  have hK'sym : K'.IsSymmetric :=
    ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp hK'sa
  -- `‖H'‖ = ‖R‖ < δ/2`
  have hK'small : ‖K'‖ < delta / 2 := by rw [hK'norm]; exact hRsmall
  -- `H'|P = H|P`: the residual data is unchanged
  have hK'P : ∀ x ∈ P, K' x = K x := by
    intro x hx
    have hfix : P.starProjection x = x := Submodule.starProjection_eq_self_iff.mpr hx
    have h := congrArg (fun M : H →L[ℂ] H => M x) hK'col
    simpa only [ContinuousLinearMap.comp_apply, hfix] using h
  -- the replacement problem
  set A' : H →L[ℂ] H := A + K - K' with hA'def
  -- (1) the perturbed operator is literally unchanged
  have htotal : A' + K' = A + K := by rw [hA'def]; abel
  have hA'sym : A'.IsSymmetric := by
    intro x y
    have hAxy : ⟪A x, y⟫_ℂ = ⟪x, A y⟫_ℂ := hA x y
    have hKxy : ⟪K x, y⟫_ℂ = ⟪x, K y⟫_ℂ := hK x y
    have hK'xy : ⟪K' x, y⟫_ℂ = ⟪x, K' y⟫_ℂ := hK'sym x y
    change ⟪A x + K x - K' x, y⟫_ℂ = ⟪x, A y + K y - K' y⟫_ℂ
    rw [inner_sub_left, inner_add_left, inner_sub_right, inner_add_right,
      hAxy, hKxy, hK'xy]
  -- (2) the unperturbed operator is unchanged on `P`
  have hA'P : ∀ x ∈ P, A' x = A x := by
    intro x hx
    change A x + K x - K' x = A x
    rw [hK'P x hx]
    abel
  have hA'inv : ∀ x ∈ P, A' x ∈ P := by
    intro x hx
    rw [hA'P x hx]
    exact hPred.1 x hx
  have hA'red : A'.Reduces P := ContinuousLinearMap.IsSymmetric.reduces_of_invariant hA'sym hA'inv
  -- the printed placement of `A₀` transfers, because `A'` and `A` agree on `P`
  have hA'spec : SpectrumIn A' P (Set.Icc (beta - delta / 2) (alpha + delta / 2)) :=
    spectrumIn_of_eqOn (fun x hx => (hA'P x hx).symm) hP
  -- every perturbed hypothesis transfers by rewriting along `A' + K' = A + K`
  have hQ' : SpectrumIn (A' + K') Q (Set.Icc beta alpha) := by rw [htotal]; exact hQ
  have hQperp' : SpectrumIn (A' + K') Qᗮ (gapExterior beta alpha delta) := by
    rw [htotal]; exact hQperp
  -- the printed reduction to the perturbation-norm case
  exact theorem8_2_perturbationHalfGap_complex hA'sym hK'sym hdelta hab hQ' hQperp'
    hA'red hA'spec hK'small

/-- **The residual alternative in the printed scalar form.** -/
theorem theorem8_2_residualHalfGap_angle_lt
    {A K : H →L[ℂ] H} (hA : A.IsSymmetric) (hK : K.IsSymmetric)
    {P Q : Submodule ℂ H} [P.HasOrthogonalProjection] [Q.HasOrthogonalProjection]
    {alpha beta delta : ℝ} (hdelta : 0 < delta) (hab : beta ≤ alpha)
    (hQ : SpectrumIn (A + K) Q (Set.Icc beta alpha))
    (hQperp : SpectrumIn (A + K) Qᗮ (gapExterior beta alpha delta))
    (hPred : A.Reduces P)
    (hP : SpectrumIn A P (Set.Icc (beta - delta / 2) (alpha + delta / 2)))
    (hRsmall : ‖residual (A + K) P.subtypeL (compressOperator P A)‖ < delta / 2) :
    Real.arcsin (P.directedProjectionGap Q) < Real.pi / 4 := by
  have h := theorem8_2_residualHalfGap_complex hA hK hdelta hab hQ hQperp hPred hP
    hRsmall
  have h0 : (0 : ℝ) ≤ P.directedProjectionGap Q := norm_nonneg _
  rw [← DavisKahan1970.Section8.arcsin_sqrt_two_div_two]
  refine Real.arcsin_lt_arcsin (by linarith) h ?_
  have : Real.sqrt 2 ≤ 2 := by
    nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2), Real.sqrt_nonneg 2]
  linarith

/-- **Theorem 8.2's printed disjunction.**  Either half-gap alternative --
small perturbation norm *or* small residual norm -- gives the strict quarter
angle.  Dispatch only; both branches are already theorems. -/
theorem theorem8_2_branch
    {A K : H →L[ℂ] H} (hA : A.IsSymmetric) (hK : K.IsSymmetric)
    {P Q : Submodule ℂ H} [P.HasOrthogonalProjection] [Q.HasOrthogonalProjection]
    {alpha beta delta : ℝ} (hdelta : 0 < delta) (hab : beta ≤ alpha)
    (hQ : SpectrumIn (A + K) Q (Set.Icc beta alpha))
    (hQperp : SpectrumIn (A + K) Qᗮ (gapExterior beta alpha delta))
    (hPred : A.Reduces P)
    (hP : SpectrumIn A P (Set.Icc (beta - delta / 2) (alpha + delta / 2)))
    (hsmall : ‖K‖ < delta / 2 ∨
      ‖residual (A + K) P.subtypeL (compressOperator P A)‖ < delta / 2) :
    P.directedProjectionGap Q < Real.sqrt 2 / 2 := by
  rcases hsmall with h | h
  · exact theorem8_2_perturbationHalfGap_complex hA hK hdelta hab hQ hQperp hPred hP h
  · exact theorem8_2_residualHalfGap_complex hA hK hdelta hab hQ hQperp hPred hP h

end ResidualAlternative

end Section8
end DavisKahan1970
end TauCeti
