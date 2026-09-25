/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, OpenAI GPT-5.6 Thinking
-/
module

public import LeanPool.DavisKahan.ForTauCeti.Analysis.OperatorIdeal.ApproximationNumber.GramSpectralRank
public import LeanPool.DavisKahan.ForTauCeti.Analysis.OperatorIdeal.ApproximationNumber.FinitePVMSelection
public import LeanPool.DavisKahan.ForTauCeti.Analysis.InnerProductSpace.Polar.PartialIsometry

/-!
# Narrow Gram bands and the polar partial isometry

This file contains the analytic part of spectral selection.  Vectors in a
positive narrow spectral band for `X†X` lie in the polar initial space.  The
band width controls the Gram residual, and a positive Gram residual controls
the corresponding modulus residual.  The polar partial isometry then gives
both approximate singular equations.

## Provenance

*Moved, not restated.*  Written in the `FinishTanTwoTheta` completion workspace and
promoted here directly, like the `FinitePVMSelection` it imports.  **All three of its
imports are `ForTauCeti` modules and none is from `DavisKahan`** — one of them only became
so when `FinitePVMSelection` was promoted immediately before this, which is the argument
for emptying that workspace bottom-up: each promotion turns the next module into a leaf.
Statements and proofs are unchanged; the namespace moved from `TauCeti.FinishTanTwoTheta`
to `TauCeti.ApproximationNumber`, matching its siblings.
-/

@[expose] public section

namespace TauCeti
namespace ApproximationNumber

open ApproximationNumber
open scoped InnerProductSpace
open Set

noncomputable section

universe u v

variable {E0 : Type u} [NormedAddCommGroup E0] [InnerProductSpace ℂ E0]
  [CompleteSpace E0]
variable {E1 : Type v} [NormedAddCommGroup E1] [InnerProductSpace ℂ E1]
  [CompleteSpace E1]

/-- A vector in a strictly positive Gram band is orthogonal to `ker X`, hence
belongs to the polar initial space. -/
theorem mem_polarInitial_of_mem_gramBand
    (X : E0 →L[ℂ] E1) {lo hi : ℝ} (hlo : 0 < lo)
    {x : E0}
    (hx : x ∈ ((gramSpectralPVM X).proj (Set.Icc lo hi)
      measurableSet_Icc).range) :
    x ∈ X.polarInitial := by
  rw [← Submodule.orthogonal_orthogonal X.polarInitial,
    X.polarInitial_orthogonal_eq_ker]
  rw [Submodule.mem_orthogonal]
  intro z hz
  have hzX : X z = 0 := hz
  have hzGram : gramOperator X z = 0 := by
    unfold gramOperator
    rw [ContinuousLinearMap.comp_apply, hzX, map_zero]
  let P : E0 →L[ℂ] E0 :=
    (gramSpectralPVM X).proj (Set.Icc lo hi) measurableSet_Icc
  have hzDom : z ∈ (gramLinearPMap X).domain := by
    rw [gramLinearPMap_domain]
    exact Submodule.mem_top
  have hPzDom : P z ∈ (gramLinearPMap X).domain := by
    rw [gramLinearPMap_domain]
    exact Submodule.mem_top
  have hgramPz : gramOperator X (P z) = 0 := by
    have hcomm := LinearPMap.specProjection_apply_domain
      (gramLinearPMap_isSelfAdjoint X) (Set.Icc lo hi) measurableSet_Icc
      (⟨z, hzDom⟩ : (gramLinearPMap X).domain)
    simp only [gramLinearPMap_apply, ← gramSpectralPVM_proj_eq_specProjection] at hcomm
    rw [hzGram, map_zero] at hcomm
    exact hcomm
  have hPzRange : P z ∈ LinearPMap.specRange
      (gramLinearPMap_isSelfAdjoint X) (Set.Icc lo hi) measurableSet_Icc := by
    rw [show P = TauCeti.LinearPMap.specProjection (gramLinearPMap_isSelfAdjoint X)
        (Set.Icc lo hi) measurableSet_Icc from
      gramSpectralPVM_proj_eq_specProjection X _ _]
    exact LinearPMap.specProjection_mem_specRange _ _ _ z
  have hform := (LinearPMap.re_inner_apply_bounds_of_subset_Icc
    (gramLinearPMap_isSelfAdjoint X) (Set.Icc lo hi) measurableSet_Icc
    (β := lo) (α := hi) Set.Subset.rfl hPzRange hPzDom).1
  have hform0 : lo * ‖P z‖ ^ 2 ≤ 0 := by
    change lo * ‖P z‖ ^ 2 ≤
      RCLike.re ⟪gramOperator X (P z), P z⟫_ℂ at hform
    simpa only [hgramPz, inner_zero_left, map_zero] using hform
  have hprod : lo * ‖P z‖ ^ 2 = 0 := by
    apply le_antisymm hform0
    exact mul_nonneg (le_of_lt hlo) (sq_nonneg ‖P z‖)
  have hnormSq : ‖P z‖ ^ 2 = 0 :=
    (mul_eq_zero.mp hprod).resolve_left (ne_of_gt hlo)
  have hnorm : ‖P z‖ = 0 := sq_eq_zero_iff.mp hnormSq
  have hPz : P z = 0 := norm_eq_zero.mp hnorm
  rcases hx with ⟨x₀, rfl⟩
  have hself : ContinuousLinearMap.adjoint P = P := by
    have h := (gramSpectralPVM X).isSelfAdjoint_proj
      (Set.Icc lo hi) measurableSet_Icc
    change IsSelfAdjoint P at h
    rwa [ContinuousLinearMap.isSelfAdjoint_iff'] at h
  calc
    ⟪z, P x₀⟫_ℂ = ⟪z, ContinuousLinearMap.adjoint P x₀⟫_ℂ := by rw [hself]
    _ = ⟪P z, x₀⟫_ℂ := ContinuousLinearMap.adjoint_inner_right _ _ _
    _ = 0 := by rw [hPz, inner_zero_left]

/-- Spectral localization in a narrow Gram band. -/
theorem gram_residual_le_of_mem_band
    (X : E0 →L[ℂ] E1) {lam η ε : ℝ}
    (hη0 : 0 < η) (hηlam : η < lam) (hηε : η < ε / 16)
    {x : E0} (hxnorm : ‖x‖ = 1)
    (hx : x ∈ ((gramSpectralPVM X).proj
      (Set.Icc ((lam - η) ^ 2) ((lam + η) ^ 2)) measurableSet_Icc).range) :
    ‖gramOperator X x - ((lam ^ 2 : ℝ) : ℂ) • x‖ ≤ ε * lam / 4 := by
  let a : ℝ := (lam - η) ^ 2
  let b : ℝ := (lam + η) ^ 2
  let c : ℝ := lam ^ 2
  let r : ℝ := max (c - a) (b - c)
  have hac : a ≤ c := by dsimp only [a, c]; nlinarith
  have hcb : c ≤ b := by dsimp only [b, c]; nlinarith
  have hbnd : ∀ s ∈ Set.Icc a b, |s| ≤ max |a| |b| := by
    intro s hs
    rw [abs_le]
    constructor
    · have hna : -|a| ≤ a := neg_abs_le a
      have hmax : |a| ≤ max |a| |b| := le_max_left _ _
      linarith [hs.1]
    · have hbabs : b ≤ |b| := le_abs_self b
      have hmax : |b| ≤ max |a| |b| := le_max_right _ _
      linarith [hs.2]
  have hr0 : 0 ≤ r := by
    exact (sub_nonneg.mpr hac).trans (le_max_left _ _)
  have hcr : ∀ s ∈ Set.Icc a b, |s - c| ≤ r := by
    intro s hs
    rw [abs_le]
    constructor
    · have hleft : c - a ≤ r := le_max_left _ _
      linarith [hs.1]
    · have hright : b - c ≤ r := le_max_right _ _
      linarith [hs.2]
  have hxRange : x ∈ LinearPMap.specRange
      (gramLinearPMap_isSelfAdjoint X) (Set.Icc a b) measurableSet_Icc := by
    obtain ⟨y, rfl⟩ := (by simpa only [a, b] using hx :
      x ∈ ((gramSpectralPVM X).proj (Set.Icc a b) measurableSet_Icc).range)
    rw [show ((gramSpectralPVM X).proj (Set.Icc a b) measurableSet_Icc)
        = TauCeti.LinearPMap.specProjection (gramLinearPMap_isSelfAdjoint X)
          (Set.Icc a b) measurableSet_Icc from
      gramSpectralPVM_proj_eq_specProjection X _ _]
    exact LinearPMap.specProjection_mem_specRange _ _ _ y
  have hxDom : x ∈ (gramLinearPMap X).domain := by
    rw [gramLinearPMap_domain]
    exact Submodule.mem_top
  have hloc := LinearPMap.norm_sub_smul_le_of_mem_specRange
    (gramLinearPMap_isSelfAdjoint X) (Set.Icc a b) measurableSet_Icc
    hbnd hr0 hcr hxRange hxDom
  change ‖gramOperator X x - (c : ℂ) • x‖ ≤ r * ‖x‖ at hloc
  rw [hxnorm, mul_one] at hloc
  have hleft : c - a ≤ 3 * lam * η := by
    dsimp only [a, c]
    nlinarith
  have hright : b - c ≤ 3 * lam * η := by
    dsimp only [b, c]
    nlinarith
  have hmax : r ≤ 3 * lam * η := by
    dsimp only [r]
    exact max_le hleft hright
  calc
    ‖gramOperator X x - ((lam ^ 2 : ℝ) : ℂ) • x‖ =
        ‖gramOperator X x - (c : ℂ) • x‖ := by rfl
    _ ≤ r := hloc
    _ ≤ 3 * lam * η := hmax
    _ ≤ ε * lam / 4 := by
      have hlam0 : 0 < lam := hη0.trans hηlam
      nlinarith

/-- The polar partial isometry is norm non-increasing on the whole source. -/
theorem norm_polarPartial_apply_le (X : E0 →L[ℂ] E1) (x : E0) :
    ‖X.polarPartial x‖ ≤ ‖x‖ := by
  rw [X.polarPartial_apply, X.norm_polarInitialMap_apply]
  exact X.polarInitial.norm_orthogonalProjectionOnto_apply_le x

/-- A positive Gram residual bounds the corresponding modulus residual. -/
theorem modulus_residual_le_of_gram_residual
    (X : E0 →L[ℂ] E1) {x : E0} {lam δ : ℝ}
    (hlam : 0 < lam) (hδ : 0 ≤ δ)
    (hgram :
      ‖gramOperator X x - ((lam ^ 2 : ℝ) : ℂ) • x‖ ≤ δ * lam) :
    ‖X.modulus x - (lam : ℂ) • x‖ ≤ δ := by
  let w : E0 := X.modulus x - (lam : ℂ) • x
  by_cases hw : w = 0
  · simp only [w, hw, norm_zero, hδ]
  have hwpos : 0 < ‖w‖ := norm_pos_iff.mpr hw
  have hmodpos : 0 ≤ RCLike.re ⟪X.modulus w, w⟫_ℂ :=
    ((ContinuousLinearMap.nonneg_iff_isPositive (f := X.modulus)).mp X.modulus_nonneg).2 w
  have hfactor :
      X.modulus w + (lam : ℂ) • w =
        gramOperator X x - ((lam ^ 2 : ℝ) : ℂ) • x := by
    have hsquare : X.modulus (X.modulus x) = X.adjoint (X x) := by
      change (X.modulus * X.modulus) x = (X.adjoint ∘L X) x
      rw [X.modulus_mul_self]
    have hlamSq : ((lam ^ 2 : ℝ) : ℂ) = (lam : ℂ) * (lam : ℂ) := by
      norm_num [pow_two]
    calc
      X.modulus w + (lam : ℂ) • w =
          X.modulus (X.modulus x) - (lam : ℂ) • X.modulus x +
            ((lam : ℂ) • X.modulus x -
              ((lam : ℂ) * (lam : ℂ)) • x) := by
        unfold w
        rw [map_sub, map_smul, smul_sub, smul_smul]
      _ = X.adjoint (X x) - ((lam : ℂ) * (lam : ℂ)) • x := by
        rw [hsquare]
        abel_nf
      _ = gramOperator X x - ((lam ^ 2 : ℝ) : ℂ) • x := by
        unfold gramOperator
        rw [ContinuousLinearMap.comp_apply, hlamSq]
  have hscalar :
      RCLike.re ⟪(lam : ℂ) • w, w⟫_ℂ = lam * ‖w‖ ^ 2 := by
    rw [inner_smul_left, inner_self_eq_norm_sq_to_K]
    simp [← Complex.ofReal_pow]
  have hlower :
      lam * ‖w‖ ^ 2 ≤
        RCLike.re ⟪X.modulus w + (lam : ℂ) • w, w⟫_ℂ := by
    calc
      lam * ‖w‖ ^ 2 ≤
          RCLike.re ⟪X.modulus w, w⟫_ℂ + lam * ‖w‖ ^ 2 :=
        le_add_of_nonneg_left hmodpos
      _ = RCLike.re ⟪X.modulus w + (lam : ℂ) • w, w⟫_ℂ := by
        rw [inner_add_left, map_add, hscalar]
  have hcauchy :
      RCLike.re ⟪X.modulus w + (lam : ℂ) • w, w⟫_ℂ ≤
        ‖X.modulus w + (lam : ℂ) • w‖ * ‖w‖ := by
    exact (RCLike.re_le_norm _).trans (norm_inner_le_norm _ _)
  have hgramMul :
      ‖gramOperator X x - ((lam ^ 2 : ℝ) : ℂ) • x‖ * ‖w‖ ≤
        (δ * lam) * ‖w‖ :=
    mul_le_mul_of_nonneg_right hgram (norm_nonneg w)
  rw [hfactor] at hlower hcauchy
  have hmain := hlower.trans (hcauchy.trans hgramMul)
  have hcancel :
      (lam * ‖w‖) * ‖w‖ ≤ (lam * ‖w‖) * δ := by
    simpa [pow_two, mul_assoc, mul_left_comm, mul_comm] using hmain
  have hwle : ‖w‖ ≤ δ :=
    le_of_mul_le_mul_left hcancel (mul_pos hlam hwpos)
  simpa only [w] using hwle

end

end ApproximationNumber
end TauCeti
