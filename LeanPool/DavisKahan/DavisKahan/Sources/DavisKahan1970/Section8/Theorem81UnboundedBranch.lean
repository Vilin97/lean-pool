/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, Claude Opus 5
-/
module

public import LeanPool.DavisKahan.DavisKahan.SpectralTheory.UnboundedCentralBand
public import LeanPool.DavisKahan.DavisKahan.InfiniteDimensional.TanTwoTheta.OffDiagonalSpectralRepulsionUnbounded
public import LeanPool.DavisKahan.DavisKahan.InfiniteDimensional.TanTwoTheta.QuarterAngleUnbounded

/-!
# Theorem 8.1's canonical branch at unbounded scope

Davis and Kahan say that for fixed `A`, `P`, `H` there *exists* a reducing
projector `Q` with `Λ₀ ≤ α` and `Λ₁ ≥ α + δ` — "take the spectral projector of
`A + H` on the appropriate side of `α`".  This module takes it, at the paper's
inherited unbounded scope.

The branch is `specRange (A + H) (Iic α)`.  Its two ordered form bounds are the
pointwise half-line energy bounds of the spectral measure, applied through a
one-sided limit:

* a vector of the branch has no spectral mass above `α`, so its form is at most
  `c ‖x‖²` for **every** `c > α`, hence at most `α ‖x‖²`;
* a vector of the complement has no spectral mass at or below `α`, and the
  spectral repulsion of an off-diagonal perturbation removes the open gap
  `(α, α + δ)` as well, so its form is at least `c ‖x‖²` for every
  `c < α + δ`, hence at least `(α + δ) ‖x‖²`.

The repulsion is `notMem_spectrum_addBounded_of_offDiagonal_form_gap`, which is
the unbounded half already proved; nothing here re-derives it.
-/

@[expose] public section

open scoped InnerProductSpace

namespace TauCeti
namespace DavisKahan1970
namespace Section8

open DavisKahan

noncomputable section

universe v

variable {H : Type v} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H]

/-- **Theorem 8.1's canonical branch at unbounded scope**: the spectral subspace
of the perturbed operator for the closed half-line `Iic α`. -/
def canonicalLowBranchUnbounded {B : H →ₗ.[ℂ] H} (hB : IsSelfAdjoint B) (alpha : ℝ) :
    Submodule ℂ H :=
  TauCeti.LinearPMap.specRange hB (Set.Iic alpha) measurableSet_Iic

/-- The branch is a spectral range, hence orthogonally complemented. -/
instance canonicalLowBranchUnbounded_hasOrthogonalProjection
    {B : H →ₗ.[ℂ] H} (hB : IsSelfAdjoint B) (alpha : ℝ) :
    (canonicalLowBranchUnbounded hB alpha).HasOrthogonalProjection :=
  TauCeti.LinearPMap.instHasOrthogonalProjection_specRange hB _ _

/-- The branch reduces the perturbed operator. -/
theorem canonicalLowBranchUnbounded_reduces
    {B : H →ₗ.[ℂ] H} (hB : IsSelfAdjoint B) (alpha : ℝ) :
    TauCeti.LinearPMap.ReducesSubspace B (canonicalLowBranchUnbounded hB alpha) :=
  TauCeti.LinearPMap.reducesSubspace_specRange hB _ _

/-- The complement of the branch is the spectral range of the open upper
half-line. -/
theorem canonicalLowBranchUnbounded_orthogonal
    {B : H →ₗ.[ℂ] H} (hB : IsSelfAdjoint B) (alpha : ℝ) :
    (canonicalLowBranchUnbounded hB alpha)ᗮ
      = TauCeti.LinearPMap.specRange hB (Set.Ioi alpha) measurableSet_Ioi := by
  rw [canonicalLowBranchUnbounded,
    ← TauCeti.LinearPMap.specRange_compl hB (Set.Iic alpha) measurableSet_Iic]
  congr 1
  exact (Set.compl_Iic (a := alpha))

/-- **The sharp upper form bound on the branch.**  `Λ₀ ≤ α`. -/
theorem re_inner_le_of_mem_canonicalLowBranchUnbounded
    {B : H →ₗ.[ℂ] H} (hB : IsSelfAdjoint B) (alpha : ℝ) (x : B.domain)
    (hx : (x : H) ∈ canonicalLowBranchUnbounded hB alpha) :
    (⟪B x, (x : H)⟫_ℂ).re ≤ alpha * ‖(x : H)‖ ^ 2 := by
  have hIoi : TauCeti.LinearPMap.specProjection hB (Set.Ioi alpha) measurableSet_Ioi
      (x : H) = 0 := by
    have hfix : TauCeti.LinearPMap.specProjection hB (Set.Iic alpha) measurableSet_Iic
        (x : H) = (x : H) :=
      (TauCeti.LinearPMap.mem_specRange_iff hB _ _ _).mp hx
    have hsum := TauCeti.LinearPMap.specProjection_add_compl_apply hB
      (B := Set.Iic alpha) measurableSet_Iic (x : H)
    rw [hfix] at hsum
    have hzero : TauCeti.LinearPMap.specProjection hB ((Set.Iic alpha)ᶜ)
        measurableSet_Iic.compl (x : H) = 0 := by
      linear_combination (norm := module) hsum
    rw [← hzero]
    exact (TauCeti.LinearPMap.specProjection_apply_congr hB
      (Set.compl_Iic (a := alpha)).symm measurableSet_Ioi measurableSet_Iic.compl (x : H))
  have hall : ∀ c : ℝ, alpha < c →
      (⟪B x, (x : H)⟫_ℂ).re ≤ c * ‖(x : H)‖ ^ 2 := by
    intro c hc
    have hsub : Set.Ici c ⊆ Set.Ioi alpha := fun s hs => lt_of_lt_of_le hc hs
    have hIci : TauCeti.LinearPMap.specProjection hB (Set.Ici c) measurableSet_Ici
        (x : H) = 0 :=
      TauCeti.LinearPMap.specProjection_apply_eq_zero_of_subset hB measurableSet_Ici
        measurableSet_Ioi hsub hIoi
    exact TauCeti.LinearPMap.re_inner_le_of_specProjection_Ici_apply_eq_zero hB x hIci
  by_contra hcon
  push Not at hcon
  rcases le_or_gt ‖(x : H)‖ 0 with hn | hn
  · have hz : ‖(x : H)‖ ^ 2 = 0 := by
      have hx0 : ‖(x : H)‖ = 0 := le_antisymm hn (norm_nonneg _)
      rw [hx0]; ring
    have h1 := hall (alpha + 1) (by linarith)
    rw [hz, mul_zero] at h1
    rw [hz, mul_zero] at hcon
    linarith
  · set r : ℝ := ‖(x : H)‖ ^ 2 with hr
    have hrpos : 0 < r := by rw [hr]; positivity
    obtain ⟨c, hc1, hc2⟩ : ∃ c : ℝ, alpha < c ∧ c * r < (⟪B x, (x : H)⟫_ℂ).re := by
      refine ⟨alpha + ((⟪B x, (x : H)⟫_ℂ).re - alpha * r) / (2 * r), ?_, ?_⟩
      · have : 0 < (⟪B x, (x : H)⟫_ℂ).re - alpha * r := by linarith
        have h2r : 0 < 2 * r := by linarith
        nlinarith [div_pos this h2r]
      · field_simp
        nlinarith [hcon, hrpos]
    exact absurd (hall c hc1) (by linarith)

/-- **The sharp lower form bound on the complement.**  `Λ₁ ≥ α + δ`.

The complement carries no spectral mass at or below `α`, and the spectral
repulsion of an off-diagonal perturbation removes the open gap `(α, α + δ)` as
well, so the form is at least `c ‖x‖²` for every `c < α + δ`. -/
theorem le_re_inner_of_mem_canonicalLowBranchUnbounded_orthogonal
    {B : H →ₗ.[ℂ] H} (hB : IsSelfAdjoint B) {alpha delta : ℝ} (_hdelta : 0 < delta)
    (hrep : ∀ lam ∈ Set.Ioo alpha (alpha + delta),
      ((lam : ℝ) : ℂ) ∉ TauCeti.LinearPMap.spectrum B)
    (x : B.domain) (hx : (x : H) ∈ (canonicalLowBranchUnbounded hB alpha)ᗮ) :
    (alpha + delta) * ‖(x : H)‖ ^ 2 ≤ (⟪B x, (x : H)⟫_ℂ).re := by
  have hgapzero : TauCeti.LinearPMap.specProjection hB
      (Set.Ioo alpha (alpha + delta)) measurableSet_Ioo = 0 := by
    refine TauCeti.LinearPMap.specProjection_eq_zero_of_subset_resolventSet hB _ _ ?_
    intro lam hlam
    have := hrep lam hlam
    rw [TauCeti.LinearPMap.notMem_spectrum_iff] at this
    exact this
  have hxIoi : (x : H) ∈ TauCeti.LinearPMap.specRange hB (Set.Ioi alpha)
      measurableSet_Ioi := by
    rw [← canonicalLowBranchUnbounded_orthogonal hB alpha]
    exact hx
  have hfix : TauCeti.LinearPMap.specProjection hB (Set.Ioi alpha) measurableSet_Ioi
      (x : H) = (x : H) :=
    (TauCeti.LinearPMap.mem_specRange_iff hB _ _ _).mp hxIoi
  have hall : ∀ c : ℝ, c < alpha + delta →
      c * ‖(x : H)‖ ^ 2 ≤ (⟪B x, (x : H)⟫_ℂ).re := by
    intro c hc
    have hinter := TauCeti.LinearPMap.specProjection_apply_specProjection hB
      (B := Set.Iic c) (C := Set.Ioi alpha) measurableSet_Iic measurableSet_Ioi (x : H)
    rw [hfix] at hinter
    have hsub : Set.Iic c ∩ Set.Ioi alpha ⊆ Set.Ioo alpha (alpha + delta) := by
      rintro s ⟨hs1, hs2⟩
      exact ⟨hs2, lt_of_le_of_lt hs1 hc⟩
    have hzero : TauCeti.LinearPMap.specProjection hB (Set.Iic c ∩ Set.Ioi alpha)
        (measurableSet_Iic.inter measurableSet_Ioi) (x : H) = 0 :=
      TauCeti.LinearPMap.specProjection_apply_eq_zero_of_subset hB
        (measurableSet_Iic.inter measurableSet_Ioi) measurableSet_Ioo hsub
        (by rw [hgapzero]; rfl)
    have hIic : TauCeti.LinearPMap.specProjection hB (Set.Iic c) measurableSet_Iic
        (x : H) = 0 := by rw [hinter]; exact hzero
    exact TauCeti.LinearPMap.le_re_inner_of_specProjection_Iic_apply_eq_zero hB x hIic
  by_contra hcon
  push Not at hcon
  rcases le_or_gt ‖(x : H)‖ 0 with hn | hn
  · have hz : ‖(x : H)‖ ^ 2 = 0 := by
      have hx0 : ‖(x : H)‖ = 0 := le_antisymm hn (norm_nonneg _)
      rw [hx0]; ring
    have h1 := hall (alpha + delta - 1) (by linarith)
    rw [hz, mul_zero] at h1
    rw [hz, mul_zero] at hcon
    linarith
  · set r : ℝ := ‖(x : H)‖ ^ 2 with hr
    have hrpos : 0 < r := by rw [hr]; positivity
    obtain ⟨c, hc1, hc2⟩ : ∃ c : ℝ, c < alpha + delta ∧
        (⟪B x, (x : H)⟫_ℂ).re < c * r := by
      refine ⟨alpha + delta - ((alpha + delta) * r - (⟪B x, (x : H)⟫_ℂ).re) / (2 * r),
        ?_, ?_⟩
      · have hpos : 0 < (alpha + delta) * r - (⟪B x, (x : H)⟫_ℂ).re := by linarith
        have h2r : 0 < 2 * r := by linarith
        nlinarith [div_pos hpos h2r]
      · field_simp
        nlinarith [hcon, hrpos]
    exact absurd (hall c hc1) (by linarith)

/-! ### Theorem 8.1's branch, at the printed hypotheses

`A` is self-adjoint with the ordered form gap across `P`, and `H` is a bounded
self-adjoint operator that is *fully off-diagonal* with respect to `P` — the
`tan 2θ` theorem's hypotheses, which Theorem 8.1 inherits.  The branch is the
spectral subspace of `A + H` for `Iic α`, and the three statements below are the
paper's: it reduces `A + H`, it carries the ordered form bounds `Λ₀ ≤ α` and
`Λ₁ ≥ α + δ`, and `Θ(P, Q) ≤ π/4`. -/

variable {A : H →ₗ.[ℂ] H} {Hop : H →L[ℂ] H} {P : Submodule ℂ H}
  [P.HasOrthogonalProjection] {alpha delta : ℝ}

/-- The perturbed operator of Theorem 8.1. -/
theorem isSelfAdjoint_perturbed (hA : IsSelfAdjoint A)
    (hH : Hop.IsSymmetric) :
    IsSelfAdjoint (TauCeti.LinearPMap.addBounded A Hop) :=
  DavisKahan.addBounded_isSelfAdjoint A hA Hop hH

/-- **Theorem 8.1's branch carries the printed ordered form bounds, at unbounded
scope.**

The repulsion is `notMem_spectrum_addBounded_of_offDiagonal_form_gap`; the two
bounds are the half-line energy bounds of the spectral measure. -/
theorem theorem8_1_canonicalBranchUnbounded_form
    (hA : IsSelfAdjoint A) (hH : Hop.IsSymmetric)
    (hredP : TauCeti.LinearPMap.ReducesSubspace A P)
    (hPhigh : ∀ x : A.domain, (x : H) ∈ P →
      (alpha + delta) * ‖(x : H)‖ ^ 2 ≤ RCLike.re ⟪A x, (x : H)⟫_ℂ)
    (hPperpLow : ∀ x : A.domain, (x : H) ∈ Pᗮ →
      RCLike.re ⟪A x, (x : H)⟫_ℂ ≤ alpha * ‖(x : H)‖ ^ 2)
    (hHP : ∀ x ∈ P, Hop x ∈ Pᗮ) (hHPperp : ∀ x ∈ Pᗮ, Hop x ∈ P)
    (hdelta : 0 < delta) :
    (∀ x : (TauCeti.LinearPMap.addBounded A Hop).domain,
        (x : H) ∈ canonicalLowBranchUnbounded (isSelfAdjoint_perturbed hA hH) alpha →
        RCLike.re ⟪TauCeti.LinearPMap.addBounded A Hop x, (x : H)⟫_ℂ ≤
          alpha * ‖(x : H)‖ ^ 2) ∧
      ∀ x : (TauCeti.LinearPMap.addBounded A Hop).domain,
        (x : H) ∈ (canonicalLowBranchUnbounded (isSelfAdjoint_perturbed hA hH) alpha)ᗮ →
        (alpha + delta) * ‖(x : H)‖ ^ 2 ≤
          RCLike.re ⟪TauCeti.LinearPMap.addBounded A Hop x, (x : H)⟫_ℂ := by
  have hHsa : IsSelfAdjoint Hop :=
    ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mpr hH
  have hrep : ∀ lam ∈ Set.Ioo alpha (alpha + delta),
      ((lam : ℝ) : ℂ) ∉ TauCeti.LinearPMap.spectrum
        (TauCeti.LinearPMap.addBounded A Hop) := by
    intro lam hlam
    exact DavisKahan.notMem_spectrum_addBounded_of_offDiagonal_form_gap A Hop P hA hHsa
      hredP hPhigh hPperpLow hHP hHPperp hlam
  refine ⟨fun x hx => ?_, fun x hx => ?_⟩
  · exact re_inner_le_of_mem_canonicalLowBranchUnbounded (isSelfAdjoint_perturbed hA hH)
      alpha x hx
  · exact le_re_inner_of_mem_canonicalLowBranchUnbounded_orthogonal
      (isSelfAdjoint_perturbed hA hH) hdelta hrep x hx

/-- A subspace admitting an orthogonal projection inside a complete ambient space
is itself complete. -/
noncomputable local instance instCompleteSpaceCoeBranch
    (U : Submodule ℂ H) [U.HasOrthogonalProjection] : CompleteSpace U :=
  (Submodule.isComplete_coe_of_hasOrthogonalProjection U).completeSpace_coe

/-- **Theorem 8.1's branch in the paper's own orientation, at unbounded scope.**

`A` is at most `α` on `P` and at least `α + δ` on `Pᗮ`, and `H` is fully
off-diagonal.  The branch `Q` reduces `A + H`, carries `Λ₀ ≤ α` and
`Λ₁ ≥ α + δ`, and satisfies the printed `Θ(P, Q) ≤ π/4`. -/
theorem theorem8_1_canonicalBranchUnbounded_printed
    (hA : IsSelfAdjoint A) (hH : Hop.IsSymmetric)
    (hredPperp : TauCeti.LinearPMap.ReducesSubspace A Pᗮ)
    (hPlow : ∀ x : A.domain, (x : H) ∈ P →
      RCLike.re ⟪A x, (x : H)⟫_ℂ ≤ alpha * ‖(x : H)‖ ^ 2)
    (hPhigh : ∀ x : A.domain, (x : H) ∈ Pᗮ →
      (alpha + delta) * ‖(x : H)‖ ^ 2 ≤ RCLike.re ⟪A x, (x : H)⟫_ℂ)
    (hHP : ∀ x ∈ P, Hop x ∈ Pᗮ) (hHPperp : ∀ x ∈ Pᗮ, Hop x ∈ P)
    (hdelta : 0 < delta) :
    TauCeti.LinearPMap.ReducesSubspace (TauCeti.LinearPMap.addBounded A Hop)
        (canonicalLowBranchUnbounded (isSelfAdjoint_perturbed hA hH) alpha) ∧
      (∀ x : (TauCeti.LinearPMap.addBounded A Hop).domain,
        (x : H) ∈ canonicalLowBranchUnbounded (isSelfAdjoint_perturbed hA hH) alpha →
        RCLike.re ⟪TauCeti.LinearPMap.addBounded A Hop x, (x : H)⟫_ℂ ≤
          alpha * ‖(x : H)‖ ^ 2) ∧
      (∀ x : (TauCeti.LinearPMap.addBounded A Hop).domain,
        (x : H) ∈ (canonicalLowBranchUnbounded (isSelfAdjoint_perturbed hA hH) alpha)ᗮ →
        (alpha + delta) * ‖(x : H)‖ ^ 2 ≤
          RCLike.re ⟪TauCeti.LinearPMap.addBounded A Hop x, (x : H)⟫_ℂ) ∧
      TauCeti.DavisKahanExt.maximalAngle P
        (canonicalLowBranchUnbounded (isSelfAdjoint_perturbed hA hH) alpha)
        ≤ Real.pi / 4 := by
  have hHsa : IsSelfAdjoint Hop :=
    ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mpr hH
  have hPP : (Pᗮ)ᗮ = P := Submodule.orthogonal_orthogonal P
  have hform := theorem8_1_canonicalBranchUnbounded_form (A := A) (Hop := Hop) (P := Pᗮ)
    (alpha := alpha) (delta := delta) hA hH hredPperp hPhigh
    (by rw [hPP]; exact hPlow)
    (by rw [hPP]; exact hHPperp) (by rw [hPP]; exact hHP) hdelta
  refine ⟨canonicalLowBranchUnbounded_reduces _ _, hform.1, hform.2, ?_⟩
  exact DavisKahan.maximalAngle_le_pi_div_four_of_orderedFormGap_unbounded_printed
    A Hop P _ hA hHsa hredPperp
    (canonicalLowBranchUnbounded_reduces (isSelfAdjoint_perturbed hA hH) alpha).orthogonal
    hPlow hPhigh hform.1 hform.2 hHP hHPperp hdelta

/-! ### The printed characterization, forward direction

Davis and Kahan state Theorem 8.1's characterization with the *spectral*
placements `Λ₀ ≤ α` and `Λ₁ ≥ α + δ`.  The direction that says those force
`Θ ≤ π/4` is available at unbounded scope: half-line spectrum gives the form
bound, and the form bound is what the unbounded quarter-angle theorem takes. -/

/-- **Theorem 8.1's characterization, the direction from the spectral placement,
at unbounded scope.**

For a reducing subspace `M` of `A + H` whose blocks are placed as the paper
prescribes — `Λ₀ ⊆ (-∞, α]` and `Λ₁ ⊆ [α + δ, ∞)` — the pair is inside the
closed quarter turn.  The hypotheses on `A` and `H` are the `tan 2θ` theorem's,
which Theorem 8.1 inherits, and they too are given spectrally. -/
theorem theorem8_1_maximalAngle_le_of_spectrumIn_unbounded
    (hA : IsSelfAdjoint A) (hHsa : IsSelfAdjoint Hop)
    (hredPperp : TauCeti.LinearPMap.ReducesSubspace A Pᗮ)
    (hPspec : TauCeti.LinearPMap.realSpectrum
      (TauCeti.LinearPMap.reducingRestriction A P
        (by simpa only [Submodule.orthogonal_orthogonal] using hredPperp.orthogonal))
      ⊆ Set.Iic alpha)
    (hPperpSpec : TauCeti.LinearPMap.realSpectrum
      (TauCeti.LinearPMap.reducingRestriction A Pᗮ hredPperp)
      ⊆ Set.Ici (alpha + delta))
    {M : Submodule ℂ H} [M.HasOrthogonalProjection]
    (hM : TauCeti.LinearPMap.ReducesSubspace (TauCeti.LinearPMap.addBounded A Hop) M)
    (hMspec : TauCeti.LinearPMap.realSpectrum
      (TauCeti.LinearPMap.reducingRestriction (TauCeti.LinearPMap.addBounded A Hop) M hM)
      ⊆ Set.Iic alpha)
    (hMperpSpec : TauCeti.LinearPMap.realSpectrum
      (TauCeti.LinearPMap.reducingRestriction (TauCeti.LinearPMap.addBounded A Hop) Mᗮ
        hM.orthogonal) ⊆ Set.Ici (alpha + delta))
    (hHP : ∀ x ∈ P, Hop x ∈ Pᗮ) (hHPperp : ∀ x ∈ Pᗮ, Hop x ∈ P)
    (hdelta : 0 < delta) :
    TauCeti.DavisKahanExt.maximalAngle P M ≤ Real.pi / 4 := by
  have hredP : TauCeti.LinearPMap.ReducesSubspace A P := by
    simpa only [Submodule.orthogonal_orthogonal] using hredPperp.orthogonal
  have hB : IsSelfAdjoint (TauCeti.LinearPMap.addBounded A Hop) :=
    DavisKahan.addBounded_isSelfAdjoint A hA Hop
      (ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp hHsa)
  exact DavisKahan.maximalAngle_le_pi_div_four_of_orderedFormGap_unbounded_printed
    A Hop P M hA hHsa hredPperp hM.orthogonal
    (fun x hx => DavisKahan.re_inner_le_of_reducingRestriction_realSpectrum_subset_Iic
      hA hredP hPspec x hx)
    (fun x hx => DavisKahan.le_re_inner_of_reducingRestriction_realSpectrum_subset_Ici
      hA hredPperp hPperpSpec x hx)
    (fun x hx => DavisKahan.re_inner_le_of_reducingRestriction_realSpectrum_subset_Iic
      hB hM hMspec x hx)
    (fun x hx => DavisKahan.le_re_inner_of_reducingRestriction_realSpectrum_subset_Ici
      hB hM.orthogonal hMperpSpec x hx)
    hHP hHPperp hdelta

end

end Section8
end DavisKahan1970
end TauCeti
