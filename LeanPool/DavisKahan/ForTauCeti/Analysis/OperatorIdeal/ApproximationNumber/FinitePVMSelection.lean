/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, OpenAI GPT-5.6 Thinking
-/
module

public import LeanPool.DavisKahan.ForTauCeti.Analysis.OperatorIdeal.ApproximationNumber.GramSpectralRank
public import Mathlib.Analysis.InnerProductSpace.Projection.Basic

/-!
# Finite selection from spectral projection ranges

Tau Ceti supplies the native projection-valued measure and projection algebra,
but not the finite-dimensional selection wrapper needed by the approximation-
number argument.  This file supplies that wrapper without tactic search.

## Provenance

*Moved, not restated.*  Written in the `FinishTanTwoTheta` completion workspace and
promoted here directly, without the intermediate stop in `DavisKahan` that
`FinishTanTwoTheta.ApproximationNumber.GramSpectralRank` made: this module imports one
`ForTauCeti` leaf and one Mathlib file and **nothing from `DavisKahan`**, so the paper
library was never on its dependency path and routing it through would only have created a
second move to undo.  Statements and proofs are unchanged; the namespace moved from
`TauCeti.FinishTanTwoTheta` to `TauCeti.ApproximationNumber`, matching the sibling it
imports.
-/

@[expose] public section

namespace TauCeti
namespace ApproximationNumber

open scoped InnerProductSpace
open Set

noncomputable section

universe u

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H]

/-- A natural-number rank lower bound on a PVM projection yields an orthonormal
family of that length inside its range. -/
theorem exists_orthonormal_mem_pvmRange_of_natCast_le_rank
    (P : TauCeti.ProjValMeasure H) (B : Set ℝ) (hB : MeasurableSet B)
    (m : ℕ) (hm : (m : Cardinal) ≤ (P.proj B hB).rank) :
    ∃ v : Fin m → H, Orthonormal ℂ v ∧
      ∀ i, v i ∈ (P.proj B hB).range := by
  classical
  let W : Submodule ℂ H := (P.proj B hB).range
  have hmW : (m : Cardinal) ≤ Module.rank ℂ W := by
    change (m : Cardinal) ≤ (P.proj B hB).rank
    exact hm
  obtain ⟨g, hg⟩ := (Module.le_rank_iff).1 hmW
  let V : Submodule ℂ W := Submodule.span ℂ (Set.range g)
  let b : Module.Basis (Fin m) ℂ V := Module.Basis.span hg
  let : FiniteDimensional ℂ V := b.finiteDimensional_of_finite
  have hfinrank : Module.finrank ℂ V = m := by
    rw [Module.finrank_eq_card_basis b, Fintype.card_fin]
  let bV := stdOrthonormalBasis ℂ V
  let v : Fin m → H := fun i =>
    ((((bV (Fin.cast hfinrank.symm i) : V) : W) : H))
  have hv : Orthonormal ℂ v := by
    rw [orthonormal_iff_ite]
    intro i j
    change
      ⟪bV (Fin.cast hfinrank.symm i), bV (Fin.cast hfinrank.symm j)⟫_ℂ =
        if i = j then 1 else 0
    rw [orthonormal_iff_ite.mp bV.orthonormal]
    simp only [Fin.cast_inj]
  refine ⟨v, hv, ?_⟩
  intro i
  change (((bV (Fin.cast hfinrank.symm i) : V) : W) : H) ∈ W
  exact (((bV (Fin.cast hfinrank.symm i) : V) : W)).property

/-- Vectors selected from disjoint PVM ranges are orthogonal. -/
theorem inner_eq_zero_of_mem_disjoint_pvmRanges
    (P : TauCeti.ProjValMeasure H)
    {B₁ B₂ : Set ℝ} (hB₁ : MeasurableSet B₁) (hB₂ : MeasurableSet B₂)
    (hdisj : Disjoint B₁ B₂) {x y : H}
    (hx : x ∈ (P.proj B₁ hB₁).range)
    (hy : y ∈ (P.proj B₂ hB₂).range) :
    ⟪x, y⟫_ℂ = 0 := by
  rcases hx with ⟨x₀, rfl⟩
  rcases hy with ⟨y₀, rfl⟩
  have hinter : B₁ ∩ B₂ = (∅ : Set ℝ) := Set.disjoint_iff_inter_eq_empty.mp hdisj
  have hcomp : P.proj B₁ hB₁ (P.proj B₂ hB₂ y₀) = 0 := by
    have hmul := congrArg (fun T : H →L[ℂ] H => T y₀)
      (P.proj_inter B₁ B₂ hB₁ hB₂)
    rw [mul_apply_eq_comp] at hmul
    rw [hmul, P.proj_congr hinter (hB₁.inter hB₂) MeasurableSet.empty,
      P.proj_empty, zero_apply]
  have hadj : ContinuousLinearMap.adjoint (P.proj B₁ hB₁) = P.proj B₁ hB₁ := by
    have h := P.isSelfAdjoint_proj B₁ hB₁
    rwa [ContinuousLinearMap.isSelfAdjoint_iff'] at h
  calc
    ⟪P.proj B₁ hB₁ x₀, P.proj B₂ hB₂ y₀⟫_ℂ =
        ⟪x₀, ContinuousLinearMap.adjoint (P.proj B₁ hB₁)
          (P.proj B₂ hB₂ y₀)⟫_ℂ :=
      (ContinuousLinearMap.adjoint_inner_right _ _ _).symm
    _ = ⟪x₀, P.proj B₁ hB₁ (P.proj B₂ hB₂ y₀)⟫_ℂ := by rw [hadj]
    _ = 0 := by rw [hcomp, inner_zero_right]


/-- Subtracting two cumulative spectral-rank bounds gives a rank lower bound
for the intervening closed band.  The proof embeds the lower-cutoff range into
the product of the upper and band ranges using finite additivity of the PVM. -/
theorem natCast_sub_le_rank_pvm_Icc_of_cutoff_bounds
    (P : TauCeti.ProjValMeasure H) {lo hi : ℝ} (hlohi : lo ≤ hi)
    (p q : ℕ)
    (hlower : (q : Cardinal) ≤ (P.proj (Set.Ici lo) measurableSet_Ici).rank)
    (hupper : (P.proj (Set.Ioi hi) measurableSet_Ioi).rank ≤ (p : Cardinal)) :
    ((q - p : ℕ) : Cardinal) ≤
      (P.proj (Set.Icc lo hi) measurableSet_Icc).rank := by
  classical
  let L : Submodule ℂ H := (P.proj (Set.Ici lo) measurableSet_Ici).range
  let U : Submodule ℂ H := (P.proj (Set.Ioi hi) measurableSet_Ioi).range
  let B : Submodule ℂ H := (P.proj (Set.Icc lo hi) measurableSet_Icc).range
  have hdisj : Disjoint (Set.Ioi hi) (Set.Icc lo hi) := by
    rw [Set.disjoint_left]
    intro x hxU hxB
    exact (not_lt_of_ge hxB.2) hxU
  have hunion : Set.Ioi hi ∪ Set.Icc lo hi = Set.Ici lo := by
    ext x
    simp only [Set.mem_union, Set.mem_Ioi, Set.mem_Icc, Set.mem_Ici]
    constructor
    · rintro (hx | hx)
      · exact hlohi.trans hx.le
      · exact hx.1
    · intro hx
      by_cases hxh : hi < x
      · exact Or.inl hxh
      · exact Or.inr ⟨hx, le_of_not_gt hxh⟩
  have hsplit :
      P.proj (Set.Ici lo) measurableSet_Ici =
        P.proj (Set.Ioi hi) measurableSet_Ioi +
          P.proj (Set.Icc lo hi) measurableSet_Icc := by
    calc
      P.proj (Set.Ici lo) measurableSet_Ici =
          P.proj (Set.Ioi hi ∪ Set.Icc lo hi)
            (measurableSet_Ioi.union measurableSet_Icc) :=
        P.proj_congr hunion.symm measurableSet_Ici
          (measurableSet_Ioi.union measurableSet_Icc)
      _ = P.proj (Set.Ioi hi) measurableSet_Ioi +
          P.proj (Set.Icc lo hi) measurableSet_Icc :=
        P.proj_union measurableSet_Ioi measurableSet_Icc hdisj
  let f : L →ₗ[ℂ] U × B :=
    { toFun := fun x =>
        (⟨P.proj (Set.Ioi hi) measurableSet_Ioi x,
            ⟨x, rfl⟩⟩,
          ⟨P.proj (Set.Icc lo hi) measurableSet_Icc x,
            ⟨x, rfl⟩⟩)
      map_add' := by
        intro x y
        apply Prod.ext <;> apply Subtype.ext <;> simp
      map_smul' := by
        intro c x
        apply Prod.ext <;> apply Subtype.ext <;> simp }
  have hf : Function.Injective f := by
    intro x y hxy
    apply Subtype.ext
    let z : H := (x : H) - (y : H)
    have hzL : z ∈ L := L.sub_mem x.property y.property
    have hUz : P.proj (Set.Ioi hi) measurableSet_Ioi z = 0 := by
      have h := congrArg (fun w : U × B => (w.1 : H)) hxy
      change P.proj (Set.Ioi hi) measurableSet_Ioi (x : H) =
        P.proj (Set.Ioi hi) measurableSet_Ioi (y : H) at h
      simpa only [z, map_sub, sub_eq_zero] using h
    have hBz : P.proj (Set.Icc lo hi) measurableSet_Icc z = 0 := by
      have h := congrArg (fun w : U × B => (w.2 : H)) hxy
      change P.proj (Set.Icc lo hi) measurableSet_Icc (x : H) =
        P.proj (Set.Icc lo hi) measurableSet_Icc (y : H) at h
      simpa only [z, map_sub, sub_eq_zero] using h
    have hzfix : P.proj (Set.Ici lo) measurableSet_Ici z = z := by
      rcases hzL with ⟨z₀, hz₀⟩
      rw [← hz₀]
      change P.proj (Set.Ici lo) measurableSet_Ici
          (P.proj (Set.Ici lo) measurableSet_Ici z₀) =
        P.proj (Set.Ici lo) measurableSet_Ici z₀
      simpa only [mul_apply_eq_comp] using
        congrArg (fun T : H →L[ℂ] H => T z₀)
          (P.proj_idem (Set.Ici lo) measurableSet_Ici)
    have hz0 : P.proj (Set.Ici lo) measurableSet_Ici z = 0 := by
      rw [hsplit, add_apply, hUz, hBz, add_zero]
    have : z = 0 := by simpa only [hzfix] using hz0
    exact sub_eq_zero.mp this
  have hrank : Module.rank ℂ L ≤ Module.rank ℂ (U × B) := by
    calc
      Module.rank ℂ L = Module.rank ℂ (LinearMap.range f) :=
        (LinearEquiv.ofInjective f hf).rank_eq
      _ ≤ Module.rank ℂ (U × B) := Submodule.rank_le _
  change (q : Cardinal) ≤ Module.rank ℂ L at hlower
  change Module.rank ℂ U ≤ (p : Cardinal) at hupper
  change ((q - p : ℕ) : Cardinal) ≤ Module.rank ℂ B
  have hq : (q : Cardinal) ≤ (p : Cardinal) + Module.rank ℂ B := by
    calc
      (q : Cardinal) ≤ Module.rank ℂ L := hlower
      _ ≤ Module.rank ℂ (U × B) := hrank
      _ = Module.rank ℂ U + Module.rank ℂ B := rank_prod'
      _ ≤ (p : Cardinal) + Module.rank ℂ B :=
        add_le_add hupper le_rfl
  by_cases hBfin : Module.rank ℂ B < Cardinal.aleph0
  · have hBcast : ((Module.rank ℂ B).toNat : Cardinal) = Module.rank ℂ B :=
      Cardinal.cast_toNat_of_lt_aleph0 hBfin
    rw [← hBcast] at hq ⊢
    norm_cast at hq ⊢
    omega
  · have haleph : Cardinal.aleph0 ≤ Module.rank ℂ B := le_of_not_gt hBfin
    have hfinite : ((q - p : ℕ) : Cardinal) < Cardinal.aleph0 :=
      Cardinal.natCast_lt_aleph0
    exact hfinite.le.trans haleph

end

end ApproximationNumber
end TauCeti
