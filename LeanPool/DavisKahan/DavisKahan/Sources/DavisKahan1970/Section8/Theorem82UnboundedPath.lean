/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, Claude Opus 5
-/
import LeanPool.DavisKahan.DavisKahan.SpectralTheory.UnboundedBandLipschitz
import LeanPool.DavisKahan.DavisKahan.Sources.DavisKahan1970.Section8.Theorem82Unbounded
import LeanPool.DavisKahan.DavisKahan.Geometry.Angle.DoubleAngleGapBound
import LeanPool.DavisKahan.DavisKahan.SpectralTheory.ReducingSpectrumUnion
import LeanPool.DavisKahan.DavisKahan.SpectralTheory.Complexification.ReducingRestrictionDescent
import LeanPool.DavisKahan.ForTauCeti.Analysis.InnerProductSpace.Polar.SelfAdjointCompletion

/-!
# The homotopy path for Theorem 8.2 at unbounded scope

Step (d) of the plan in `GOAL.md` §10.4: the bounded proof's constant-threshold
bootstrap, with its Riesz-projection continuity replaced by the unbounded
`sin Θ` Lipschitz estimate.

Along `B t = A + (1 − t) H` the moving branch is the band spectral range
`R t = bandSubspace (B t) l r` with `l = β − γ`, `r = α + γ`, `d = δ − 2γ` and
`γ = ‖H‖`.  Three facts drive the argument and none of them needs a contour:

* every `B t` has its spectrum in `[l, r] ∪ exterior(l, r, d)`, by
  `spectrum_addBounded_subset_of_gap`;
* `t ↦ directedGap (R t) Q` is Lipschitz, by `subspaceGap_bandSubspace_le` and
  `abs_directedGap_sub_directedGap_le`;
* at each `t` the `sin 2Θ` estimate is instantiated at `A := B t`,
  `Hop := t H`, which keeps the *printed* gap `δ` at `Q` because
  `B t + t H = A + H`.

The two endpoints come from `le_of_band_exterior_spectra`.
-/

open scoped InnerProductSpace

namespace TauCeti
namespace DavisKahan1970
namespace Section8

open DavisKahan
open TauCeti.DavisKahan.Sylvester

noncomputable section

universe v

variable {Hc : Type v} [NormedAddCommGroup Hc] [InnerProductSpace ℂ Hc]
  [CompleteSpace Hc]

/-! ### Two bookkeeping facts about bounded perturbations -/

omit [CompleteSpace Hc] in
/-- Two successive bounded perturbations add. -/
theorem addBounded_addBounded (A : Hc →ₗ.[ℂ] Hc) (V W : Hc →L[ℂ] Hc) :
    TauCeti.LinearPMap.addBounded (TauCeti.LinearPMap.addBounded A V) W
      = TauCeti.LinearPMap.addBounded A (V + W) := by
  refine LinearPMap.ext rfl ?_
  intro x y hxy
  simp only [TauCeti.LinearPMap.addBounded_apply, add_apply]
  change (A ⟨x, y⟩ : Hc) + V x + W x = (A ⟨x, hxy⟩ : Hc) + (V x + W x)
  abel

omit [CompleteSpace Hc] in
/-- A real multiple of a self-adjoint operator is self-adjoint. -/
theorem isSelfAdjointOperator_realSmul {V : Hc →L[ℂ] Hc}
    (hV : V.IsSymmetric) (c : ℝ) :
    ((c : ℂ) • V).IsSymmetric := by
  intro x y
  change ⟪(c : ℂ) • V x, y⟫_ℂ = ⟪x, (c : ℂ) • V y⟫_ℂ
  rw [inner_smul_left, inner_smul_right, Complex.conj_ofReal]
  exact congrArg (fun z : ℂ => (c : ℂ) * z) (hV x y)

omit [CompleteSpace Hc] in
/-- The norm of a real multiple. -/
theorem norm_realSmul (V : Hc →L[ℂ] Hc) (c : ℝ) :
    ‖(c : ℝ) • V‖ = |c| * ‖V‖ := by
  rw [norm_smul, Real.norm_eq_abs]

/-! ### The path -/

/-- The homotopy `B t = A + (1 − t) H`: at `t = 0` the perturbed operator, at
`t = 1` the unperturbed one. -/
def pathOperator (A : Hc →ₗ.[ℂ] Hc) (Hop : Hc →L[ℂ] Hc) (t : ℝ) : Hc →ₗ.[ℂ] Hc :=
  TauCeti.LinearPMap.addBounded A (((1 : ℝ) - t : ℝ) • Hop)

/-- Every operator on the path is self-adjoint. -/
theorem isSelfAdjoint_pathOperator {A : Hc →ₗ.[ℂ] Hc} (hA : IsSelfAdjoint A)
    {Hop : Hc →L[ℂ] Hc} (hHop : Hop.IsSymmetric) (t : ℝ) :
    IsSelfAdjoint (pathOperator A Hop t) :=
  DavisKahan.addBounded_isSelfAdjoint A hA _ (isSelfAdjointOperator_realSmul hHop _)

omit [CompleteSpace Hc] in
/-- Completing the path perturbation returns the perturbed operator. -/
theorem addBounded_pathOperator (A : Hc →ₗ.[ℂ] Hc) (Hop : Hc →L[ℂ] Hc) (t : ℝ) :
    TauCeti.LinearPMap.addBounded (pathOperator A Hop t) (((t : ℝ)) • Hop)
      = TauCeti.LinearPMap.addBounded A Hop := by
  rw [pathOperator, addBounded_addBounded]
  congr 1
  module

omit [CompleteSpace Hc] in
/-- At the far endpoint the path is the unperturbed operator. -/
theorem pathOperator_one (A : Hc →ₗ.[ℂ] Hc) (Hop : Hc →L[ℂ] Hc) :
    pathOperator A Hop 1 = A := by
  rw [pathOperator, show ((1 : ℝ) - (1 : ℝ) : ℝ) • Hop = 0 by simp]
  exact addBounded_zero A

omit [CompleteSpace Hc] in
/-- At the near endpoint the path is the perturbed operator. -/
theorem pathOperator_zero (A : Hc →ₗ.[ℂ] Hc) (Hop : Hc →L[ℂ] Hc) :
    pathOperator A Hop 0 = TauCeti.LinearPMap.addBounded A Hop := by
  rw [pathOperator]
  congr 1
  module

/-- The band subspace along the path. -/
def pathBand {A : Hc →ₗ.[ℂ] Hc} (hA : IsSelfAdjoint A) {Hop : Hc →L[ℂ] Hc}
    (hHop : Hop.IsSymmetric) (l r : ℝ) (t : ℝ) : Submodule ℂ Hc :=
  DavisKahan.bandSubspace (isSelfAdjoint_pathOperator hA hHop t) l r

/-- The path band, unfolded. -/
theorem pathBand_def {A : Hc →ₗ.[ℂ] Hc} (hA : IsSelfAdjoint A) {Hop : Hc →L[ℂ] Hc}
    (hHop : Hop.IsSymmetric) (l r : ℝ) (t : ℝ) :
    pathBand hA hHop l r t
      = DavisKahan.bandSubspace (isSelfAdjoint_pathOperator hA hHop t) l r := rfl

/-- The path band is a spectral range, hence orthogonally complemented. -/
instance pathBand_hasOrthogonalProjection {A : Hc →ₗ.[ℂ] Hc} (hA : IsSelfAdjoint A)
    {Hop : Hc →L[ℂ] Hc} (hHop : Hop.IsSymmetric) (l r : ℝ) (t : ℝ) :
    (pathBand hA hHop l r t).HasOrthogonalProjection :=
  DavisKahan.bandSubspace_hasOrthogonalProjection _ _ _

/-- The path band reduces the operator at its own parameter. -/
theorem reducesSubspace_pathBand {A : Hc →ₗ.[ℂ] Hc} (hA : IsSelfAdjoint A)
    {Hop : Hc →L[ℂ] Hc} (hHop : Hop.IsSymmetric) (l r : ℝ) (t : ℝ) :
    TauCeti.LinearPMap.ReducesSubspace (pathOperator A Hop t) (pathBand hA hHop l r t) :=
  DavisKahan.reducesSubspace_bandSubspace _ _ _

omit [CompleteSpace Hc] in
/-- Equal operators have the same reducing-restriction spectrum.  The proof
arguments differ, and proof irrelevance is what makes this `rfl` after `subst`. -/
theorem realSpectrum_reducingRestriction_congr {A B : Hc →ₗ.[ℂ] Hc} (h : A = B)
    {U : Submodule ℂ Hc} [U.HasOrthogonalProjection]
    (hA : TauCeti.LinearPMap.ReducesSubspace A U)
    (hB : TauCeti.LinearPMap.ReducesSubspace B U) :
    TauCeti.LinearPMap.realSpectrum (TauCeti.LinearPMap.reducingRestriction A U hA)
      = TauCeti.LinearPMap.realSpectrum
        (TauCeti.LinearPMap.reducingRestriction B U hB) := by
  subst h
  rfl

/-! ### The per-parameter `sin 2Θ` estimate -/

/-- **The `sin 2Θ` estimate at a path parameter.**

Stated with the perturbed operator as a variable linked by an equation, which is
what lets `subst` put it in the shape
`norm_sinTwoAngleOperator_le_of_perturbedGap_unbounded_complex` consumes. -/
theorem norm_sinTwoAngle_path_le

    {B0 Bt : Hc →ₗ.[ℂ] Hc} (hBt : IsSelfAdjoint Bt)
    (K : Hc →L[ℂ] Hc) (hK : K.IsSymmetric)
    (hlink : B0 = TauCeti.LinearPMap.addBounded Bt K)
    {R Q : Submodule ℂ Hc} [R.HasOrthogonalProjection] [Q.HasOrthogonalProjection]
    (hRred : TauCeti.LinearPMap.ReducesSubspace Bt R)
    (hQred : TauCeti.LinearPMap.ReducesSubspace B0 Q)
    {δ : ℝ} (hδ : 0 < δ)
    (hgap : FormBoundedSylvesterGap
      (TauCeti.LinearPMap.reducingRestriction B0 Q hQred)
      (TauCeti.LinearPMap.reducingRestriction B0 Qᗮ hQred.orthogonal) δ) :
    δ * ‖TauCeti.DavisKahanExt.sinTwoAngleOperator Q R‖ ≤ 2 * ‖K‖ := by
  subst hlink
  have h := norm_sinTwoAngleOperator_le_of_perturbedGap_unbounded_complex
    hBt K hK hRred hQred hδ hgap
  have hcomm : ‖TauCeti.DavisKahan.Angle.sinTwoAngleOperator R Q‖
      = ‖TauCeti.DavisKahanExt.sinTwoAngleOperator Q R‖ := by
    rw [show TauCeti.DavisKahan.Angle.sinTwoAngleOperator R Q
        = TauCeti.DavisKahan.Angle.sinTwoAngleOperator Q R from
      TauCeti.DavisKahan.Angle.sinTwoAngleOperator_comm Q R,
      norm_sinTwoAngleOperator_eq_norm_block Q R]
  rwa [hcomm] at h

/-! ### Theorem 8.2's perturbation branch at unbounded scope -/

/-- The scaled quarter-angle inequality is equivalent to the usual square-root threshold. -/
private theorem lt_sqrt_two_half_of_mul_lt {z : ℝ} (hlt : Real.sqrt 2 * z < 1) :
    z < Real.sqrt 2 / 2 := by
  have hs2 : Real.sqrt 2 * (Real.sqrt 2 / 2) = 1 := by
    rw [show Real.sqrt 2 * (Real.sqrt 2 / 2) = Real.sqrt 2 ^ 2 / 2 by ring,
      Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
    norm_num
  have hpos2 : (0 : ℝ) < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
  by_contra hcon
  rw [not_lt] at hcon
  nlinarith [hlt, hs2, hpos2, hcon]

/-- A uniform scaled Lipschitz estimate gives continuity along the unit interval. -/
private theorem continuousOn_unitInterval_of_gap_bound (f : ℝ → ℝ) {gam d : ℝ}
    (hgam0 : 0 ≤ gam) (hd : 0 < d)
    (hlip : ∀ s t : ℝ, s ∈ Set.Icc (0 : ℝ) 1 → t ∈ Set.Icc (0 : ℝ) 1 →
      |f s - f t| ≤ |s - t| * gam / d) : ContinuousOn f (Set.Icc 0 1) := by
  rw [Metric.continuousOn_iff]
  intro t ht ε hε
  refine ⟨ε * d / (gam + 1), by positivity, fun s hs hst => ?_⟩
  have h1 := hlip s t hs ht
  have h2 : |s - t| < ε * d / (gam + 1) := by
    simpa [Real.dist_eq] using hst
  have hgp : (0 : ℝ) < gam + 1 := by linarith
  have h3 : |s - t| * gam / d < ε := by
    rw [div_lt_iff₀ hd]
    have h4 : |s - t| * gam ≤ (ε * d / (gam + 1)) * gam := by
      nlinarith [abs_nonneg (s - t), h2, hgam0]
    have h5 : (ε * d / (gam + 1)) * gam < ε * d := by
      rw [div_mul_eq_mul_div, div_lt_iff₀ hgp]
      nlinarith [hε, hd, hgam0]
    linarith
  calc dist (f s) (f t) = |f s - f t| := Real.dist_eq _ _
    _ ≤ |s - t| * gam / d := h1
    _ < ε := h3

/-- **Davis--Kahan 1970, Theorem 8.2, perturbation alternative, at unbounded
ambient scope, in its directed form.**

`directedGap P Q < √2/2` from the printed hypotheses: `A` self-adjoint with `P`
reducing and block spectrum in `[β − δ/2, α + δ/2]`; `A + H` with `Q` reducing,
block spectrum in `[β, α]` and complementary block spectrum off
`(β − δ, α + δ)`; and `‖H‖ < δ/2`.

Every hypothesis is printed.  The ambient placement of `A + H` that the proof
needs is derived from the two block placements by
`realSpectrum_subset_union_of_reduces`, and the separation `hQgap` is the two
block placements read as an interval/exterior gap. -/
theorem theorem8_2_perturbationHalfGap_unbounded_complex

    {A : Hc →ₗ.[ℂ] Hc} (hA : IsSelfAdjoint A)
    (Hop : Hc →L[ℂ] Hc) (hHop : Hop.IsSymmetric)
    {P Q : Submodule ℂ Hc} [P.HasOrthogonalProjection] [Q.HasOrthogonalProjection]
    {alpha beta delta : ℝ} (hdelta : 0 < delta) (hab : beta ≤ alpha)
    (hPred : TauCeti.LinearPMap.ReducesSubspace A P)
    (hQred : TauCeti.LinearPMap.ReducesSubspace
      (TauCeti.LinearPMap.addBounded A Hop) Q)
    (hQspec : TauCeti.LinearPMap.realSpectrum
      (TauCeti.LinearPMap.reducingRestriction (TauCeti.LinearPMap.addBounded A Hop) Q hQred)
      ⊆ Set.Icc beta alpha)
    (hQperp : TauCeti.LinearPMap.realSpectrum
      (TauCeti.LinearPMap.reducingRestriction (TauCeti.LinearPMap.addBounded A Hop) Qᗮ
        hQred.orthogonal) ⊆ bandExterior beta alpha delta)
    (hPspec : TauCeti.LinearPMap.realSpectrum
      (TauCeti.LinearPMap.reducingRestriction A P hPred)
      ⊆ Set.Icc (beta - delta / 2) (alpha + delta / 2))
    (hsmall : ‖Hop‖ < delta / 2) :
    P.directedProjectionGap Q < Real.sqrt 2 / 2 := by
  classical
  have hQgap : FormBoundedSylvesterGap
      (TauCeti.LinearPMap.reducingRestriction (TauCeti.LinearPMap.addBounded A Hop) Q hQred)
      (TauCeti.LinearPMap.reducingRestriction (TauCeti.LinearPMap.addBounded A Hop) Qᗮ
        hQred.orthogonal) delta :=
    .intervalExterior hab (Or.inl ⟨hQspec, hQperp⟩)
  have hB0spec : TauCeti.LinearPMap.realSpectrum (TauCeti.LinearPMap.addBounded A Hop)
      ⊆ Set.Icc beta alpha ∪ bandExterior beta alpha delta := by
    intro x hx
    rcases DavisKahan.realSpectrum_subset_union_of_reduces hQred hx with h | h
    · exact Or.inl (hQspec h)
    · exact Or.inr (hQperp h)
  obtain ⟨gam, hgamdef⟩ : ∃ g, g = ‖Hop‖ := ⟨_, rfl⟩
  have hgam0 : 0 ≤ gam := hgamdef ▸ norm_nonneg Hop
  have hgamlt : 2 * gam < delta := by rw [hgamdef]; linarith
  have hsmallg : gam < delta / 2 := by rw [hgamdef]; exact hsmall
  obtain ⟨l, hldef⟩ : ∃ x, x = beta - gam := ⟨_, rfl⟩
  obtain ⟨r, hrdef⟩ : ∃ x, x = alpha + gam := ⟨_, rfl⟩
  obtain ⟨d, hddef⟩ : ∃ x, x = delta - 2 * gam := ⟨_, rfl⟩
  have hd : 0 < d := by rw [hddef]; linarith
  have hlr : l ≤ r := by rw [hldef, hrdef]; linarith
  have hB0 : IsSelfAdjoint (TauCeti.LinearPMap.addBounded A Hop) :=
    DavisKahan.addBounded_isSelfAdjoint A hA Hop hHop
  -- the path, and its spectral placement
  have hpath : ∀ t : ℝ, pathOperator A Hop t
      = TauCeti.LinearPMap.addBounded (TauCeti.LinearPMap.addBounded A Hop)
        (((-t : ℝ)) • Hop) := by
    intro t
    rw [pathOperator, addBounded_addBounded]
    congr 1
    module
  have hspec : ∀ t : ℝ, t ∈ Set.Icc (0 : ℝ) 1 →
      TauCeti.LinearPMap.realSpectrum (pathOperator A Hop t)
        ⊆ Set.Icc l r ∪ bandExterior l r d := by
    intro t ht
    have hnorm : ‖((-t : ℝ)) • Hop‖ ≤ gam := by
      rw [norm_realSmul, hgamdef, abs_neg, abs_of_nonneg ht.1]
      nlinarith [ht.2, norm_nonneg Hop]
    have hstab := realSpectrum_addBounded_subset_of_gap hB0 (((-t : ℝ)) • Hop) hab hdelta
      hnorm hgamlt hB0spec
    rw [hpath t, hldef, hrdef, hddef]
    exact hstab
  -- the moving branch and the tracked quantity
  obtain ⟨f, hfdef⟩ : ∃ f : ℝ → ℝ,
      ∀ t, f t = Submodule.directedProjectionGap (pathBand hA hHop l r t) Q :=
    ⟨fun t => Submodule.directedProjectionGap (pathBand hA hHop l r t) Q, fun _ => rfl⟩
  -- Lipschitz continuity, from the band estimate
  have hlip : ∀ s t : ℝ, s ∈ Set.Icc (0 : ℝ) 1 → t ∈ Set.Icc (0 : ℝ) 1 →
      |f s - f t| ≤ |s - t| * gam / d := by
    intro s t hs ht
    have hlink : pathOperator A Hop t
        = TauCeti.LinearPMap.addBounded (pathOperator A Hop s) (((s - t : ℝ)) • Hop) := by
      rw [pathOperator, pathOperator, addBounded_addBounded]
      congr 1
      module
    have hsa : (((s - t : ℝ)) • Hop).IsSymmetric :=
      isSelfAdjointOperator_realSmul hHop _
    have hband := DavisKahan.subspaceGap_bandSubspace_le
      (isSelfAdjoint_pathOperator hA hHop s) (isSelfAdjoint_pathOperator hA hHop t)
      (((s - t : ℝ)) • Hop) hsa hlink hlr hd (hspec s hs) (hspec t ht)
    rw [norm_realSmul, ← hgamdef] at hband
    have hband' : d * Submodule.projectionGap (pathBand hA hHop l r s)
        (pathBand hA hHop l r t) ≤ |s - t| * gam := hband
    have hcomp : |f s - f t| ≤ Submodule.projectionGap (pathBand hA hHop l r s)
        (pathBand hA hHop l r t) := by
      rw [hfdef s, hfdef t]
      exact DavisKahan.abs_directedGap_sub_directedGap_le _ _ _
    rw [le_div_iff₀ hd]
    nlinarith [hcomp, hband', hd]
  have hcont : ContinuousOn f (Set.Icc 0 1) :=
    continuousOn_unitInterval_of_gap_bound f hgam0 hd hlip
  -- the two endpoints
  have hextsub : bandExterior beta alpha delta ⊆ bandExterior l r d := by
    rintro x (hx | hx)
    · exact Or.inl (by rw [hldef, hddef]; linarith)
    · exact Or.inr (by rw [hrdef, hddef]; linarith)
  have hf0 : f 0 = 0 := by
    have hB0path : pathOperator A Hop 0 = TauCeti.LinearPMap.addBounded A Hop :=
      pathOperator_zero A Hop
    have hQred' : TauCeti.LinearPMap.ReducesSubspace (pathOperator A Hop 0) Q := by
      rw [hB0path]; exact hQred
    have hQperp' : TauCeti.LinearPMap.realSpectrum
        (TauCeti.LinearPMap.reducingRestriction (pathOperator A Hop 0) Qᗮ
          hQred'.orthogonal) ⊆ bandExterior l r d := by
      rw [realSpectrum_reducingRestriction_congr hB0path hQred'.orthogonal hQred.orthogonal]
      exact fun x hx => hextsub (hQperp hx)
    have hbandspec : TauCeti.LinearPMap.realSpectrum
        (TauCeti.LinearPMap.reducingRestriction (pathOperator A Hop 0)
          (pathBand hA hHop l r 0) (reducesSubspace_pathBand hA hHop l r 0))
        ⊆ Set.Icc l r :=
      DavisKahan.realSpectrum_reducingRestriction_band_subset _ rfl _
    have hle : pathBand hA hHop l r 0 ≤ Q :=
      DavisKahan.le_of_band_exterior_spectra (isSelfAdjoint_pathOperator hA hHop 0)
        (DavisKahan.addBounded_zero _).symm (reducesSubspace_pathBand hA hHop l r 0)
        hQred' hlr hd hbandspec hQperp'
    rw [hfdef 0]
    change ‖Qᗮ.starProjection ∘L (pathBand hA hHop l r 0).starProjection‖ = 0
    rw [norm_eq_zero]
    ext x
    have hmem : (pathBand hA hHop l r 0).starProjection x ∈ Q :=
      hle ((pathBand hA hHop l r 0).starProjection_apply_mem x)
    change Qᗮ.starProjection ((pathBand hA hHop l r 0).starProjection x) = 0
    rw [Submodule.starProjection_orthogonal_apply,
      Submodule.starProjection_eq_self_iff.mpr hmem, sub_self]
  have hR1 : P ≤ pathBand hA hHop l r 1 := by
    have hApath : pathOperator A Hop 1 = A := pathOperator_one A Hop
    have hPred' : TauCeti.LinearPMap.ReducesSubspace (pathOperator A Hop 1) P := by
      rw [hApath]; exact hPred
    have hWred : TauCeti.LinearPMap.ReducesSubspace (pathOperator A Hop 1)
      (pathBand hA hHop l r 1) := reducesSubspace_pathBand hA hHop l r 1
    have hd' : 0 < delta / 2 - gam := by rw [hgamdef]; linarith
    have hlr' : beta - delta / 2 ≤ alpha + delta / 2 := by linarith
    have hPspec' : TauCeti.LinearPMap.realSpectrum
        (TauCeti.LinearPMap.reducingRestriction (pathOperator A Hop 1) P hPred')
        ⊆ Set.Icc (beta - delta / 2) (alpha + delta / 2) := by
      rw [realSpectrum_reducingRestriction_congr hApath hPred' hPred]
      exact hPspec
    have hWperp : (pathBand hA hHop l r 1)ᗮ =
        TauCeti.LinearPMap.specRange (isSelfAdjoint_pathOperator hA hHop 1)
          (bandExterior l r d) (DavisKahan.measurableSet_bandExterior l r d) :=
      (DavisKahan.specRange_bandExterior_eq_orthogonal
        (isSelfAdjoint_pathOperator hA hHop 1) hlr hd (hspec 1 ⟨zero_le_one, le_rfl⟩)).symm
    have hWspec : TauCeti.LinearPMap.realSpectrum
        (TauCeti.LinearPMap.reducingRestriction (pathOperator A Hop 1)
          (pathBand hA hHop l r 1)ᗮ hWred.orthogonal)
        ⊆ bandExterior (beta - delta / 2) (alpha + delta / 2) (delta / 2 - gam) := by
      intro x hx
      have hx' := DavisKahan.realSpectrum_reducingRestriction_bandExterior_subset
        (isSelfAdjoint_pathOperator hA hHop 1) hWperp hWred.orthogonal hx
      rcases hx' with h | h
      · exact Or.inl (by rw [hldef, hddef] at h; linarith)
      · exact Or.inr (by rw [hrdef, hddef] at h; linarith)
    exact DavisKahan.le_of_band_exterior_spectra (isSelfAdjoint_pathOperator hA hHop 1)
      (DavisKahan.addBounded_zero _).symm hPred' hWred hlr' hd' hPspec' hWspec
  -- the bootstrap: the closed quarter branch forces the strict one
  have hboot : ∀ t : ℝ, t ∈ Set.Icc (0 : ℝ) 1 → f t ≤ Real.sqrt 2 / 2 →
      f t < Real.sqrt 2 / 2 := by
    intro t ht hclose
    have hsa : (((t : ℝ)) • Hop).IsSymmetric :=
      isSelfAdjointOperator_realSmul hHop _
    have hlink : TauCeti.LinearPMap.addBounded A Hop
        = TauCeti.LinearPMap.addBounded (pathOperator A Hop t) (((t : ℝ)) • Hop) :=
      (addBounded_pathOperator A Hop t).symm
    have hsin := norm_sinTwoAngle_path_le (isSelfAdjoint_pathOperator hA hHop t)
      (((t : ℝ)) • Hop) hsa hlink (reducesSubspace_pathBand hA hHop l r t) hQred
      hdelta hQgap
    rw [norm_realSmul, ← hgamdef, abs_of_nonneg ht.1] at hsin
    have hclose' : Submodule.directedProjectionGap (pathBand hA hHop l r t) Q ≤ Real.sqrt 2 / 2 :=
      by
      rw [← hfdef t]; exact hclose
    have hlowbnd := DavisKahan.Angle.sqrt_two_mul_directedGap_le_norm_sinTwoAngleOperator
      Q (pathBand hA hHop l r t) hclose'
    rw [← hfdef t] at hlowbnd
    have htg : t * gam ≤ gam := by nlinarith [ht.1, ht.2, hgam0]
    have h2 : Real.sqrt 2 * f t * delta ≤ 2 * (t * gam) := by nlinarith [hsin, hlowbnd]
    have hstrict : Real.sqrt 2 * f t * delta < delta := by
      nlinarith [h2, htg, hsmallg]
    have hlt : Real.sqrt 2 * f t < 1 := by
      by_contra hcon
      rw [not_lt] at hcon
      nlinarith [hstrict, hdelta]
    exact lt_sqrt_two_half_of_mul_lt hlt
  -- connectedness
  have hsqrtpos : (0 : ℝ) < Real.sqrt 2 / 2 := by
    have := Real.sqrt_pos.mpr (by norm_num : (0 : ℝ) < 2)
    linarith
  have hall : ∀ t : ℝ, t ∈ Set.Icc (0 : ℝ) 1 → f t < Real.sqrt 2 / 2 := by
    intro u hu
    by_contra hcon
    rw [not_lt] at hcon
    have hsub : Set.Icc (0 : ℝ) u ⊆ Set.Icc (0 : ℝ) 1 := Set.Icc_subset_Icc le_rfl hu.2
    have hcont' : ContinuousOn f (Set.Icc 0 u) := hcont.mono hsub
    have hmem : Real.sqrt 2 / 2 ∈ Set.Icc (f 0) (f u) := by
      rw [hf0]
      exact ⟨hsqrtpos.le, hcon⟩
    obtain ⟨t, htmem, hft⟩ := intermediate_value_Icc hu.1 hcont' hmem
    have ht1 : t ∈ Set.Icc (0 : ℝ) 1 := hsub htmem
    have hlt := hboot t ht1 (le_of_eq hft)
    rw [hft] at hlt
    exact lt_irrefl _ hlt
  -- transport to the source pair
  have hfixP : (pathBand hA hHop l r 1).starProjection ∘L P.starProjection
      = P.starProjection := by
    ext x
    change (pathBand hA hHop l r 1).starProjection (P.starProjection x) = P.starProjection x
    exact Submodule.starProjection_eq_self_iff.mpr (hR1 (P.starProjection_apply_mem x))
  have hle : P.directedProjectionGap Q ≤ f 1 := by
    rw [hfdef 1]
    change ‖Qᗮ.starProjection ∘L P.starProjection‖ ≤
      ‖Qᗮ.starProjection ∘L (pathBand hA hHop l r 1).starProjection‖
    calc ‖Qᗮ.starProjection ∘L P.starProjection‖
        = ‖(Qᗮ.starProjection ∘L (pathBand hA hHop l r 1).starProjection) ∘L
            P.starProjection‖ := by
          rw [ContinuousLinearMap.comp_assoc, hfixP]
      _ ≤ ‖Qᗮ.starProjection ∘L (pathBand hA hHop l r 1).starProjection‖ *
            ‖P.starProjection‖ := ContinuousLinearMap.opNorm_comp_le _ _
      _ ≤ ‖Qᗮ.starProjection ∘L (pathBand hA hHop l r 1).starProjection‖ * 1 := by
          have := P.starProjection_norm_le
          nlinarith [norm_nonneg (Qᗮ.starProjection ∘L
            (pathBand hA hHop l r 1).starProjection)]
      _ = ‖Qᗮ.starProjection ∘L (pathBand hA hHop l r 1).starProjection‖ := mul_one _
  exact lt_of_le_of_lt hle (hall 1 ⟨zero_le_one, le_rfl⟩)

/-- **Theorem 8.2's printed conclusion `Θ < π/4` at unbounded ambient scope,
perturbation alternative.**

The directed bound above, converted by Section 3's standing assumption (3.5) in
its constructive form.  No finite-dimensionality and no rank hypothesis. -/
theorem theorem8_2_perturbationHalfGap_maximalAngle_lt_unbounded_complex

    {A : Hc →ₗ.[ℂ] Hc} (hA : IsSelfAdjoint A)
    (Hop : Hc →L[ℂ] Hc) (hHop : Hop.IsSymmetric)
    {P Q : Submodule ℂ Hc} [P.HasOrthogonalProjection] [Q.HasOrthogonalProjection]
    {alpha beta delta : ℝ} (hdelta : 0 < delta) (hab : beta ≤ alpha)
    (hPred : TauCeti.LinearPMap.ReducesSubspace A P)
    (hQred : TauCeti.LinearPMap.ReducesSubspace
      (TauCeti.LinearPMap.addBounded A Hop) Q)
    (hQspec : TauCeti.LinearPMap.realSpectrum
      (TauCeti.LinearPMap.reducingRestriction (TauCeti.LinearPMap.addBounded A Hop) Q hQred)
      ⊆ Set.Icc beta alpha)
    (hQperp : TauCeti.LinearPMap.realSpectrum
      (TauCeti.LinearPMap.reducingRestriction (TauCeti.LinearPMap.addBounded A Hop) Qᗮ
        hQred.orthogonal) ⊆ bandExterior beta alpha delta)
    (hPspec : TauCeti.LinearPMap.realSpectrum
      (TauCeti.LinearPMap.reducingRestriction A P hPred)
      ⊆ Set.Icc (beta - delta / 2) (alpha + delta / 2))
    (hcross : DavisKahan.CrossedDefectsEquivalent P Q)
    (hsmall : ‖Hop‖ < delta / 2) :
    TauCeti.DavisKahanExt.maximalAngle P Q < Real.pi / 4 := by
  refine (maximalAngle_lt_pi_div_four_iff P Q).2 ?_
  change P.projectionGap Q < Real.sqrt 2 / 2
  rw [DavisKahan.subspaceGap_eq_directedGap_of_crossedDefectsEquivalent P Q hcross]
  exact theorem8_2_perturbationHalfGap_unbounded_complex hA Hop hHop hdelta hab
    hPred hQred hQspec hQperp hPspec hsmall

/-! ### Theorem 8.2's residual branch at unbounded scope -/

/-- A subspace admitting an orthogonal projection inside a complete ambient
space is itself complete. -/
noncomputable local instance instCompleteSpaceCoeResidual
    (U : Submodule ℂ Hc) [U.HasOrthogonalProjection] : CompleteSpace U :=
  (Submodule.isComplete_coe_of_hasOrthogonalProjection U).completeSpace_coe

/-- **Davis--Kahan 1970, Theorem 8.2, residual alternative, at unbounded ambient
scope, in its directed form.**

The hypotheses are the printed ones, identical to the perturbation branch except
that the smallness assumption is the printed residual condition `‖R‖ < δ/2` in
place of `‖H‖ < δ/2`.  `R` is the source residual (1.8), which for a reducing `P`
is the first block column `H E₀` of the perturbation.

The proof is the printed reduction.  Krein's theorem
(`exists_selfAdjoint_completion_eq_norm_restriction`) replaces `H` by a
self-adjoint `H'` with the same first column and `‖H'‖ = ‖R‖`; setting
`A' := A + (H − H')` leaves `A' + H' = A + H` and `A'|P = A|P`, so every printed
hypothesis transfers and the perturbation branch applies to `(A', H')`.

The public type carries `‖R‖ < δ/2` and does **not** acquire `‖H‖ < δ/2`. -/
theorem theorem8_2_residualHalfGap_unbounded_complex

    {A : Hc →ₗ.[ℂ] Hc} (hA : IsSelfAdjoint A)
    (Hop : Hc →L[ℂ] Hc) (hHop : Hop.IsSymmetric)
    {P Q : Submodule ℂ Hc} [P.HasOrthogonalProjection] [Q.HasOrthogonalProjection]
    {alpha beta delta : ℝ} (hdelta : 0 < delta) (hab : beta ≤ alpha)
    (hPred : TauCeti.LinearPMap.ReducesSubspace A P)
    (hQred : TauCeti.LinearPMap.ReducesSubspace
      (TauCeti.LinearPMap.addBounded A Hop) Q)
    (hQspec : TauCeti.LinearPMap.realSpectrum
      (TauCeti.LinearPMap.reducingRestriction (TauCeti.LinearPMap.addBounded A Hop) Q hQred)
      ⊆ Set.Icc beta alpha)
    (hQperp : TauCeti.LinearPMap.realSpectrum
      (TauCeti.LinearPMap.reducingRestriction (TauCeti.LinearPMap.addBounded A Hop) Qᗮ
        hQred.orthogonal) ⊆ bandExterior beta alpha delta)
    (hPspec : TauCeti.LinearPMap.realSpectrum
      (TauCeti.LinearPMap.reducingRestriction A P hPred)
      ⊆ Set.Icc (beta - delta / 2) (alpha + delta / 2))
    (hRsmall : ‖Hop ∘L (P.subtypeL : P →L[ℂ] Hc)‖ < delta / 2) :
    P.directedProjectionGap Q < Real.sqrt 2 / 2 := by
  classical
  rw [TauCeti.norm_comp_subtypeL_eq_norm_comp_starProjection] at hRsmall
  obtain ⟨K', hK'sa, hK'col, hK'norm⟩ :=
    TauCeti.exists_selfAdjoint_completion_eq_norm_restriction Hop
      (ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mpr hHop) P
  have hK'sym : K'.IsSymmetric :=
    ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp hK'sa
  have hK'small : ‖K'‖ < delta / 2 := by rw [hK'norm]; exact hRsmall
  have hK'P : ∀ x ∈ P, K' x = Hop x := by
    intro x hx
    have hfix : P.starProjection x = x := Submodule.starProjection_eq_self_iff.mpr hx
    have h := congrArg (fun M : Hc →L[ℂ] Hc => M x) hK'col
    simpa only [ContinuousLinearMap.comp_apply, hfix] using h
  obtain ⟨D, hDdef⟩ : ∃ D : Hc →L[ℂ] Hc, D = Hop - K' := ⟨_, rfl⟩
  have hDsym : D.IsSymmetric := by
    intro x y
    have h1 : ⟪Hop x, y⟫_ℂ = ⟪x, Hop y⟫_ℂ := hHop x y
    have h2 : ⟪K' x, y⟫_ℂ = ⟪x, K' y⟫_ℂ := hK'sym x y
    rw [hDdef]
    change ⟪Hop x - K' x, y⟫_ℂ = ⟪x, Hop y - K' y⟫_ℂ
    rw [inner_sub_left, inner_sub_right, h1, h2]
  have hDP : ∀ x ∈ P, D x = 0 := by
    intro x hx
    rw [hDdef]
    change Hop x - K' x = 0
    rw [hK'P x hx, sub_self]
  have hA'sa : IsSelfAdjoint (TauCeti.LinearPMap.addBounded A D) :=
    DavisKahan.addBounded_isSelfAdjoint A hA D hDsym
  have hPred' : TauCeti.LinearPMap.ReducesSubspace (TauCeti.LinearPMap.addBounded A D) P := by
    refine DavisKahan.reducesSubspace_of_isSelfAdjoint_of_invariant hA'sa
      (fun x => hPred.projection_mem_domain x) ?_
    intro x hx
    change (A ⟨(x : Hc), x.2⟩ : Hc) + D (x : Hc) ∈ P
    rw [hDP _ hx, add_zero]
    exact hPred.invariant ⟨(x : Hc), x.2⟩ hx
  have hrestr : TauCeti.LinearPMap.reducingRestriction A P hPred
      = TauCeti.LinearPMap.reducingRestriction (TauCeti.LinearPMap.addBounded A D) P
        hPred' := by
    refine LinearPMap.ext rfl ?_
    intro x y hxy
    refine Subtype.ext ?_
    change (A ⟨((x : P) : Hc), y⟩ : Hc)
      = (A ⟨((x : P) : Hc), hxy⟩ : Hc) + D ((x : P) : Hc)
    rw [hDP ((x : P) : Hc) x.2, add_zero]
  have htotal : TauCeti.LinearPMap.addBounded (TauCeti.LinearPMap.addBounded A D) K'
      = TauCeti.LinearPMap.addBounded A Hop := by
    rw [addBounded_addBounded, hDdef]
    congr 1
    abel
  have hQred' : TauCeti.LinearPMap.ReducesSubspace
      (TauCeti.LinearPMap.addBounded (TauCeti.LinearPMap.addBounded A D) K') Q := by
    rw [htotal]; exact hQred
  have hQspec' : TauCeti.LinearPMap.realSpectrum
      (TauCeti.LinearPMap.reducingRestriction
        (TauCeti.LinearPMap.addBounded (TauCeti.LinearPMap.addBounded A D) K') Q hQred')
      ⊆ Set.Icc beta alpha := by
    rw [realSpectrum_reducingRestriction_congr htotal hQred' hQred]
    exact hQspec
  have hQperp' : TauCeti.LinearPMap.realSpectrum
      (TauCeti.LinearPMap.reducingRestriction
        (TauCeti.LinearPMap.addBounded (TauCeti.LinearPMap.addBounded A D) K') Qᗮ
        hQred'.orthogonal) ⊆ bandExterior beta alpha delta := by
    rw [realSpectrum_reducingRestriction_congr htotal hQred'.orthogonal hQred.orthogonal]
    exact hQperp
  have hPspec' : TauCeti.LinearPMap.realSpectrum
      (TauCeti.LinearPMap.reducingRestriction (TauCeti.LinearPMap.addBounded A D) P hPred')
      ⊆ Set.Icc (beta - delta / 2) (alpha + delta / 2) := by
    rw [← hrestr]
    exact hPspec
  exact theorem8_2_perturbationHalfGap_unbounded_complex hA'sa K' hK'sym hdelta hab
    hPred' hQred' hQspec' hQperp' hPspec' hK'small

/-- **Theorem 8.2's printed conclusion `Θ < π/4` at unbounded ambient scope,
residual alternative.** -/
theorem theorem8_2_residualHalfGap_maximalAngle_lt_unbounded_complex

    {A : Hc →ₗ.[ℂ] Hc} (hA : IsSelfAdjoint A)
    (Hop : Hc →L[ℂ] Hc) (hHop : Hop.IsSymmetric)
    {P Q : Submodule ℂ Hc} [P.HasOrthogonalProjection] [Q.HasOrthogonalProjection]
    {alpha beta delta : ℝ} (hdelta : 0 < delta) (hab : beta ≤ alpha)
    (hPred : TauCeti.LinearPMap.ReducesSubspace A P)
    (hQred : TauCeti.LinearPMap.ReducesSubspace
      (TauCeti.LinearPMap.addBounded A Hop) Q)
    (hQspec : TauCeti.LinearPMap.realSpectrum
      (TauCeti.LinearPMap.reducingRestriction (TauCeti.LinearPMap.addBounded A Hop) Q hQred)
      ⊆ Set.Icc beta alpha)
    (hQperp : TauCeti.LinearPMap.realSpectrum
      (TauCeti.LinearPMap.reducingRestriction (TauCeti.LinearPMap.addBounded A Hop) Qᗮ
        hQred.orthogonal) ⊆ bandExterior beta alpha delta)
    (hPspec : TauCeti.LinearPMap.realSpectrum
      (TauCeti.LinearPMap.reducingRestriction A P hPred)
      ⊆ Set.Icc (beta - delta / 2) (alpha + delta / 2))
    (hcross : DavisKahan.CrossedDefectsEquivalent P Q)
    (hRsmall : ‖Hop ∘L (P.subtypeL : P →L[ℂ] Hc)‖ < delta / 2) :
    TauCeti.DavisKahanExt.maximalAngle P Q < Real.pi / 4 := by
  refine (maximalAngle_lt_pi_div_four_iff P Q).2 ?_
  change P.projectionGap Q < Real.sqrt 2 / 2
  rw [DavisKahan.subspaceGap_eq_directedGap_of_crossedDefectsEquivalent P Q hcross]
  exact theorem8_2_residualHalfGap_unbounded_complex hA Hop hHop hdelta hab
    hPred hQred hQspec hQperp hPspec hRsmall

/-! ### The real endpoints, by complexification

The real theorems are the complex ones run on complexified data.  Every datum
transports: the operator by `complexifyReal`, the perturbation by `complexify`,
the subspaces by `complexifySubmodule`, the printed spectral placements by
`realSpectrum_reducingRestriction_complexifyReal`, and the conclusion back by
`directedGap_complexifySubmodule`.  Separate exact real and complex endpoints,
not an `RCLike` generalization: the moving band lives in the complex spectral
measure. -/

open TauCeti.RealComplexification in
/-- **Davis--Kahan 1970, Theorem 8.2, perturbation alternative, at unbounded
ambient scope over a real Hilbert space, directed form.** -/
theorem theorem8_2_perturbationHalfGap_unbounded_real
    {Er : Type v} [NormedAddCommGroup Er] [InnerProductSpace ℝ Er] [CompleteSpace Er]
    [TopologicalSpace.SeparableSpace Er]
    {A : Er →ₗ.[ℝ] Er} (hA : IsSelfAdjoint A)
    (Hop : Er →L[ℝ] Er) (hHop : Hop.IsSymmetric)
    {P Q : Submodule ℝ Er} [P.HasOrthogonalProjection] [Q.HasOrthogonalProjection]
    {alpha beta delta : ℝ} (hdelta : 0 < delta) (hab : beta ≤ alpha)
    (hPred : TauCeti.LinearPMap.ReducesSubspace A P)
    (hQred : TauCeti.LinearPMap.ReducesSubspace
      (TauCeti.LinearPMap.addBounded A Hop) Q)
    (hQspec : TauCeti.LinearPMap.realSpectrum
      (TauCeti.LinearPMap.reducingRestriction (TauCeti.LinearPMap.addBounded A Hop) Q hQred)
      ⊆ Set.Icc beta alpha)
    (hQperp : TauCeti.LinearPMap.realSpectrum
      (TauCeti.LinearPMap.reducingRestriction (TauCeti.LinearPMap.addBounded A Hop) Qᗮ
        hQred.orthogonal) ⊆ bandExterior beta alpha delta)
    (hPspec : TauCeti.LinearPMap.realSpectrum
      (TauCeti.LinearPMap.reducingRestriction A P hPred)
      ⊆ Set.Icc (beta - delta / 2) (alpha + delta / 2))
    (hsmall : ‖Hop‖ < delta / 2) :
    P.directedProjectionGap Q < Real.sqrt 2 / 2 := by
  classical
  have hsep : TopologicalSpace.SeparableSpace (TauCeti.RealComplexification Er) :=
    DavisKahan.Foundation.RealComplexification.separableSpace_realComplexification
  have hAC : IsSelfAdjoint (TauCeti.LinearPMap.complexifyReal A) :=
    TauCeti.LinearPMap.isSelfAdjoint_complexifyReal hA
  have hHC : (complexify Hop).IsSymmetric :=
    (TauCeti.RealComplexification.complexify_isSymmetric_iff Hop).mpr hHop
  have hPredC : TauCeti.LinearPMap.ReducesSubspace (TauCeti.LinearPMap.complexifyReal A)
      (DavisKahan.Foundation.RealComplexification.complexifySubmodule P) :=
    TauCeti.DavisKahan1970.reducesSubspace_complexifyReal hPred
  have hsum : TauCeti.LinearPMap.addBounded (TauCeti.LinearPMap.complexifyReal A)
      (complexify Hop)
      = TauCeti.LinearPMap.complexifyReal (TauCeti.LinearPMap.addBounded A Hop) :=
    (TauCeti.DavisKahan1970.complexifyReal_addBounded A Hop).symm
  have hQredC : TauCeti.LinearPMap.ReducesSubspace
      (TauCeti.LinearPMap.addBounded (TauCeti.LinearPMap.complexifyReal A) (complexify Hop))
      (DavisKahan.Foundation.RealComplexification.complexifySubmodule Q) := by
    rw [hsum]
    exact TauCeti.DavisKahan1970.reducesSubspace_complexifyReal hQred
  have hQspecC : TauCeti.LinearPMap.realSpectrum
      (TauCeti.LinearPMap.reducingRestriction
        (TauCeti.LinearPMap.addBounded (TauCeti.LinearPMap.complexifyReal A) (complexify Hop))
        (DavisKahan.Foundation.RealComplexification.complexifySubmodule Q) hQredC)
      ⊆ Set.Icc beta alpha := by
    rw [realSpectrum_reducingRestriction_congr hsum hQredC
      (TauCeti.DavisKahan1970.reducesSubspace_complexifyReal hQred),
      DavisKahan.Foundation.RealComplexification.realSpectrum_reducingRestriction_complexifyReal
        hQred _]
    exact hQspec
  have hQperpC : TauCeti.LinearPMap.realSpectrum
      (TauCeti.LinearPMap.reducingRestriction
        (TauCeti.LinearPMap.addBounded (TauCeti.LinearPMap.complexifyReal A) (complexify Hop))
        (DavisKahan.Foundation.RealComplexification.complexifySubmodule Q)ᗮ
        hQredC.orthogonal) ⊆ bandExterior beta alpha delta := by
    rw [realSpectrum_reducingRestriction_congr hsum hQredC.orthogonal
      ((TauCeti.DavisKahan1970.reducesSubspace_complexifyReal
        hQred).orthogonal)]
    rw [DavisKahan.Foundation.RealComplexification.realSpectrum_reducingRestriction_complexifyReal_of_eq
      (DavisKahan.Foundation.RealComplexification.complexifySubmodule_orthogonal Q).symm
      hQred.orthogonal _]
    exact hQperp
  have hPspecC : TauCeti.LinearPMap.realSpectrum
      (TauCeti.LinearPMap.reducingRestriction (TauCeti.LinearPMap.complexifyReal A)
        (DavisKahan.Foundation.RealComplexification.complexifySubmodule P) hPredC)
      ⊆ Set.Icc (beta - delta / 2) (alpha + delta / 2) := by
    rw [DavisKahan.Foundation.RealComplexification.realSpectrum_reducingRestriction_complexifyReal
      hPred hPredC]
    exact hPspec
  have hsmallC : ‖complexify Hop‖ < delta / 2 := by
    rw [TauCeti.RealComplexification.norm_complexify]
    exact hsmall
  have hmain := theorem8_2_perturbationHalfGap_unbounded_complex hAC (complexify Hop) hHC
    hdelta hab hPredC hQredC hQspecC hQperpC hPspecC hsmallC
  rwa [DavisKahan.Foundation.RealComplexification.directedGap_complexifySubmodule] at hmain

/-- A real subspace admitting an orthogonal projection inside a complete ambient
space is itself complete. -/
noncomputable local instance instCompleteSpaceCoeRealResidual
    {Er : Type v} [NormedAddCommGroup Er] [InnerProductSpace ℝ Er] [CompleteSpace Er]
    (U : Submodule ℝ Er) [U.HasOrthogonalProjection] : CompleteSpace U :=
  (Submodule.isComplete_coe_of_hasOrthogonalProjection U).completeSpace_coe

open TauCeti.RealComplexification in
/-- **Davis--Kahan 1970, Theorem 8.2, residual alternative, at unbounded ambient
scope over a real Hilbert space, directed form.**

The public type carries `‖R‖ < δ/2` and does not acquire `‖H‖ < δ/2`. -/
theorem theorem8_2_residualHalfGap_unbounded_real
    {Er : Type v} [NormedAddCommGroup Er] [InnerProductSpace ℝ Er] [CompleteSpace Er]
    [TopologicalSpace.SeparableSpace Er]
    {A : Er →ₗ.[ℝ] Er} (hA : IsSelfAdjoint A)
    (Hop : Er →L[ℝ] Er) (hHop : Hop.IsSymmetric)
    {P Q : Submodule ℝ Er} [P.HasOrthogonalProjection] [Q.HasOrthogonalProjection]
    {alpha beta delta : ℝ} (hdelta : 0 < delta) (hab : beta ≤ alpha)
    (hPred : TauCeti.LinearPMap.ReducesSubspace A P)
    (hQred : TauCeti.LinearPMap.ReducesSubspace
      (TauCeti.LinearPMap.addBounded A Hop) Q)
    (hQspec : TauCeti.LinearPMap.realSpectrum
      (TauCeti.LinearPMap.reducingRestriction (TauCeti.LinearPMap.addBounded A Hop) Q hQred)
      ⊆ Set.Icc beta alpha)
    (hQperp : TauCeti.LinearPMap.realSpectrum
      (TauCeti.LinearPMap.reducingRestriction (TauCeti.LinearPMap.addBounded A Hop) Qᗮ
        hQred.orthogonal) ⊆ bandExterior beta alpha delta)
    (hPspec : TauCeti.LinearPMap.realSpectrum
      (TauCeti.LinearPMap.reducingRestriction A P hPred)
      ⊆ Set.Icc (beta - delta / 2) (alpha + delta / 2))
    (hRsmall : ‖Hop ∘L (P.subtypeL : P →L[ℝ] Er)‖ < delta / 2) :
    P.directedProjectionGap Q < Real.sqrt 2 / 2 := by
  classical
  have hsep : TopologicalSpace.SeparableSpace (TauCeti.RealComplexification Er) :=
    DavisKahan.Foundation.RealComplexification.separableSpace_realComplexification
  have hAC : IsSelfAdjoint (TauCeti.LinearPMap.complexifyReal A) :=
    TauCeti.LinearPMap.isSelfAdjoint_complexifyReal hA
  have hHC : (complexify Hop).IsSymmetric :=
    (TauCeti.RealComplexification.complexify_isSymmetric_iff Hop).mpr hHop
  have hPredC : TauCeti.LinearPMap.ReducesSubspace (TauCeti.LinearPMap.complexifyReal A)
      (DavisKahan.Foundation.RealComplexification.complexifySubmodule P) :=
    TauCeti.DavisKahan1970.reducesSubspace_complexifyReal hPred
  have hsum : TauCeti.LinearPMap.addBounded (TauCeti.LinearPMap.complexifyReal A)
      (complexify Hop)
      = TauCeti.LinearPMap.complexifyReal (TauCeti.LinearPMap.addBounded A Hop) :=
    (TauCeti.DavisKahan1970.complexifyReal_addBounded A Hop).symm
  have hQredC : TauCeti.LinearPMap.ReducesSubspace
      (TauCeti.LinearPMap.addBounded (TauCeti.LinearPMap.complexifyReal A) (complexify Hop))
      (DavisKahan.Foundation.RealComplexification.complexifySubmodule Q) := by
    rw [hsum]
    exact TauCeti.DavisKahan1970.reducesSubspace_complexifyReal hQred
  have hQspecC : TauCeti.LinearPMap.realSpectrum
      (TauCeti.LinearPMap.reducingRestriction
        (TauCeti.LinearPMap.addBounded (TauCeti.LinearPMap.complexifyReal A) (complexify Hop))
        (DavisKahan.Foundation.RealComplexification.complexifySubmodule Q) hQredC)
      ⊆ Set.Icc beta alpha := by
    rw [realSpectrum_reducingRestriction_congr hsum hQredC
      (TauCeti.DavisKahan1970.reducesSubspace_complexifyReal hQred),
      DavisKahan.Foundation.RealComplexification.realSpectrum_reducingRestriction_complexifyReal
        hQred _]
    exact hQspec
  have hQperpC : TauCeti.LinearPMap.realSpectrum
      (TauCeti.LinearPMap.reducingRestriction
        (TauCeti.LinearPMap.addBounded (TauCeti.LinearPMap.complexifyReal A) (complexify Hop))
        (DavisKahan.Foundation.RealComplexification.complexifySubmodule Q)ᗮ
        hQredC.orthogonal) ⊆ bandExterior beta alpha delta := by
    rw [realSpectrum_reducingRestriction_congr hsum hQredC.orthogonal
      ((TauCeti.DavisKahan1970.reducesSubspace_complexifyReal hQred).orthogonal)]
    rw [DavisKahan.Foundation.RealComplexification.realSpectrum_reducingRestriction_complexifyReal_of_eq
      (DavisKahan.Foundation.RealComplexification.complexifySubmodule_orthogonal Q).symm
      hQred.orthogonal _]
    exact hQperp
  have hPspecC : TauCeti.LinearPMap.realSpectrum
      (TauCeti.LinearPMap.reducingRestriction (TauCeti.LinearPMap.complexifyReal A)
        (DavisKahan.Foundation.RealComplexification.complexifySubmodule P) hPredC)
      ⊆ Set.Icc (beta - delta / 2) (alpha + delta / 2) := by
    rw [DavisKahan.Foundation.RealComplexification.realSpectrum_reducingRestriction_complexifyReal
      hPred hPredC]
    exact hPspec
  have hRsmallC : ‖complexify Hop ∘L
      ((DavisKahan.Foundation.RealComplexification.complexifySubmodule P).subtypeL :
        DavisKahan.Foundation.RealComplexification.complexifySubmodule P →L[ℂ]
          TauCeti.RealComplexification Er)‖ < delta / 2 := by
    rw [DavisKahan.Foundation.RealComplexification.norm_complexify_comp_subtypeL]
    exact hRsmall
  have hmain := theorem8_2_residualHalfGap_unbounded_complex hAC (complexify Hop) hHC
    hdelta hab hPredC hQredC hQspecC hQperpC hPspecC hRsmallC
  rwa [DavisKahan.Foundation.RealComplexification.directedGap_complexifySubmodule] at hmain

/-- **Theorem 8.2's printed conclusion `Θ < π/4` at unbounded ambient scope over
a real Hilbert space, perturbation alternative.** -/
theorem theorem8_2_perturbationHalfGap_maximalAngle_lt_unbounded_real
    {Er : Type v} [NormedAddCommGroup Er] [InnerProductSpace ℝ Er] [CompleteSpace Er]
    [TopologicalSpace.SeparableSpace Er]
    {A : Er →ₗ.[ℝ] Er} (hA : IsSelfAdjoint A)
    (Hop : Er →L[ℝ] Er) (hHop : Hop.IsSymmetric)
    {P Q : Submodule ℝ Er} [P.HasOrthogonalProjection] [Q.HasOrthogonalProjection]
    {alpha beta delta : ℝ} (hdelta : 0 < delta) (hab : beta ≤ alpha)
    (hPred : TauCeti.LinearPMap.ReducesSubspace A P)
    (hQred : TauCeti.LinearPMap.ReducesSubspace
      (TauCeti.LinearPMap.addBounded A Hop) Q)
    (hQspec : TauCeti.LinearPMap.realSpectrum
      (TauCeti.LinearPMap.reducingRestriction (TauCeti.LinearPMap.addBounded A Hop) Q hQred)
      ⊆ Set.Icc beta alpha)
    (hQperp : TauCeti.LinearPMap.realSpectrum
      (TauCeti.LinearPMap.reducingRestriction (TauCeti.LinearPMap.addBounded A Hop) Qᗮ
        hQred.orthogonal) ⊆ bandExterior beta alpha delta)
    (hPspec : TauCeti.LinearPMap.realSpectrum
      (TauCeti.LinearPMap.reducingRestriction A P hPred)
      ⊆ Set.Icc (beta - delta / 2) (alpha + delta / 2))
    (hcross : DavisKahan.CrossedDefectsEquivalent P Q)
    (hsmall : ‖Hop‖ < delta / 2) :
    TauCeti.DavisKahanExt.maximalAngle P Q < Real.pi / 4 := by
  refine (maximalAngle_lt_pi_div_four_iff P Q).2 ?_
  change P.projectionGap Q < Real.sqrt 2 / 2
  rw [DavisKahan.subspaceGap_eq_directedGap_of_crossedDefectsEquivalent P Q hcross]
  exact theorem8_2_perturbationHalfGap_unbounded_real hA Hop hHop hdelta hab
    hPred hQred hQspec hQperp hPspec hsmall

/-- **Theorem 8.2's printed conclusion `Θ < π/4` at unbounded ambient scope over
a real Hilbert space, residual alternative.** -/
theorem theorem8_2_residualHalfGap_maximalAngle_lt_unbounded_real
    {Er : Type v} [NormedAddCommGroup Er] [InnerProductSpace ℝ Er] [CompleteSpace Er]
    [TopologicalSpace.SeparableSpace Er]
    {A : Er →ₗ.[ℝ] Er} (hA : IsSelfAdjoint A)
    (Hop : Er →L[ℝ] Er) (hHop : Hop.IsSymmetric)
    {P Q : Submodule ℝ Er} [P.HasOrthogonalProjection] [Q.HasOrthogonalProjection]
    {alpha beta delta : ℝ} (hdelta : 0 < delta) (hab : beta ≤ alpha)
    (hPred : TauCeti.LinearPMap.ReducesSubspace A P)
    (hQred : TauCeti.LinearPMap.ReducesSubspace
      (TauCeti.LinearPMap.addBounded A Hop) Q)
    (hQspec : TauCeti.LinearPMap.realSpectrum
      (TauCeti.LinearPMap.reducingRestriction (TauCeti.LinearPMap.addBounded A Hop) Q hQred)
      ⊆ Set.Icc beta alpha)
    (hQperp : TauCeti.LinearPMap.realSpectrum
      (TauCeti.LinearPMap.reducingRestriction (TauCeti.LinearPMap.addBounded A Hop) Qᗮ
        hQred.orthogonal) ⊆ bandExterior beta alpha delta)
    (hPspec : TauCeti.LinearPMap.realSpectrum
      (TauCeti.LinearPMap.reducingRestriction A P hPred)
      ⊆ Set.Icc (beta - delta / 2) (alpha + delta / 2))
    (hcross : DavisKahan.CrossedDefectsEquivalent P Q)
    (hRsmall : ‖Hop ∘L (P.subtypeL : P →L[ℝ] Er)‖ < delta / 2) :
    TauCeti.DavisKahanExt.maximalAngle P Q < Real.pi / 4 := by
  refine (maximalAngle_lt_pi_div_four_iff P Q).2 ?_
  change P.projectionGap Q < Real.sqrt 2 / 2
  rw [DavisKahan.subspaceGap_eq_directedGap_of_crossedDefectsEquivalent P Q hcross]
  exact theorem8_2_residualHalfGap_unbounded_real hA Hop hHop hdelta hab
    hPred hQred hQspec hQperp hPspec hRsmall

/-! ### Theorem 8.2's printed disjunction -/

/-- **Davis--Kahan 1970, Theorem 8.2, at unbounded ambient scope over `ℂ`.**

The printed statement: add to the `sin 2Θ` theorem's hypotheses *either*
`‖H‖ < δ/2` *or* `‖R‖ < δ/2`, together with `spec(A₀) ⊆ [β − δ/2, α + δ/2]`, and
conclude `Θ < π/4`.  Section 3's standing assumption (3.5) is what turns the
directed conclusion into the printed symmetric one. -/
theorem theorem8_2_branch_maximalAngle_lt_unbounded_source_complex
    [TopologicalSpace.SeparableSpace Hc]
    {A : Hc →ₗ.[ℂ] Hc} (hA : IsSelfAdjoint A)
    (Hop : Hc →L[ℂ] Hc) (hHop : Hop.IsSymmetric)
    {P Q : Submodule ℂ Hc} [P.HasOrthogonalProjection] [Q.HasOrthogonalProjection]
    {alpha beta delta : ℝ} (hdelta : 0 < delta) (hab : beta ≤ alpha)
    (hPred : TauCeti.LinearPMap.ReducesSubspace A P)
    (hQred : TauCeti.LinearPMap.ReducesSubspace
      (TauCeti.LinearPMap.addBounded A Hop) Q)
    (hQspec : TauCeti.LinearPMap.realSpectrum
      (TauCeti.LinearPMap.reducingRestriction (TauCeti.LinearPMap.addBounded A Hop) Q hQred)
      ⊆ Set.Icc beta alpha)
    (hQperp : TauCeti.LinearPMap.realSpectrum
      (TauCeti.LinearPMap.reducingRestriction (TauCeti.LinearPMap.addBounded A Hop) Qᗮ
        hQred.orthogonal) ⊆ bandExterior beta alpha delta)
    (hPspec : TauCeti.LinearPMap.realSpectrum
      (TauCeti.LinearPMap.reducingRestriction A P hPred)
      ⊆ Set.Icc (beta - delta / 2) (alpha + delta / 2))
    (hcross : DavisKahan.CrossedDefectsEquivalent P Q)
    (hsmall : ‖Hop‖ < delta / 2 ∨
      ‖Hop ∘L (P.subtypeL : P →L[ℂ] Hc)‖ < delta / 2) :
    TauCeti.DavisKahanExt.maximalAngle P Q < Real.pi / 4 := by
  rcases hsmall with h | h
  · exact theorem8_2_perturbationHalfGap_maximalAngle_lt_unbounded_complex hA Hop hHop
      hdelta hab hPred hQred hQspec hQperp hPspec hcross h
  · exact theorem8_2_residualHalfGap_maximalAngle_lt_unbounded_complex hA Hop hHop
      hdelta hab hPred hQred hQspec hQperp hPspec hcross h

/-- **Davis--Kahan 1970, Theorem 8.2, at unbounded ambient scope over `ℝ`.** -/
theorem theorem8_2_branch_maximalAngle_lt_unbounded_source_real
    {Er : Type v} [NormedAddCommGroup Er] [InnerProductSpace ℝ Er] [CompleteSpace Er]
    [TopologicalSpace.SeparableSpace Er]
    {A : Er →ₗ.[ℝ] Er} (hA : IsSelfAdjoint A)
    (Hop : Er →L[ℝ] Er) (hHop : Hop.IsSymmetric)
    {P Q : Submodule ℝ Er} [P.HasOrthogonalProjection] [Q.HasOrthogonalProjection]
    {alpha beta delta : ℝ} (hdelta : 0 < delta) (hab : beta ≤ alpha)
    (hPred : TauCeti.LinearPMap.ReducesSubspace A P)
    (hQred : TauCeti.LinearPMap.ReducesSubspace
      (TauCeti.LinearPMap.addBounded A Hop) Q)
    (hQspec : TauCeti.LinearPMap.realSpectrum
      (TauCeti.LinearPMap.reducingRestriction (TauCeti.LinearPMap.addBounded A Hop) Q hQred)
      ⊆ Set.Icc beta alpha)
    (hQperp : TauCeti.LinearPMap.realSpectrum
      (TauCeti.LinearPMap.reducingRestriction (TauCeti.LinearPMap.addBounded A Hop) Qᗮ
        hQred.orthogonal) ⊆ bandExterior beta alpha delta)
    (hPspec : TauCeti.LinearPMap.realSpectrum
      (TauCeti.LinearPMap.reducingRestriction A P hPred)
      ⊆ Set.Icc (beta - delta / 2) (alpha + delta / 2))
    (hcross : DavisKahan.CrossedDefectsEquivalent P Q)
    (hsmall : ‖Hop‖ < delta / 2 ∨
      ‖Hop ∘L (P.subtypeL : P →L[ℝ] Er)‖ < delta / 2) :
    TauCeti.DavisKahanExt.maximalAngle P Q < Real.pi / 4 := by
  rcases hsmall with h | h
  · exact theorem8_2_perturbationHalfGap_maximalAngle_lt_unbounded_real hA Hop hHop
      hdelta hab hPred hQred hQspec hQperp hPspec hcross h
  · exact theorem8_2_residualHalfGap_maximalAngle_lt_unbounded_real hA Hop hHop
      hdelta hab hPred hQred hQspec hQperp hPspec hcross h

end

end Section8
end DavisKahan1970
end TauCeti
