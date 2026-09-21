/-
Copyright (c) 2026 Dmitrii Zakharov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dmitrii Zakharov
-/

import LeanPool.ErdosGinzburgZiv.EGZ.Expansion.Relative
import LeanPool.ErdosGinzburgZiv.EGZ.Decomposition.MinimalRepresentation
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.Algebra.Field.ZMod

/-!
# Coordinates adapted to an affine projection

The coordinate change used in the final expansion argument is proved here.
An affine surjection from an affine subspace becomes first-coordinate
projection after choosing coordinates on its kernel.
-/

open scoped BigOperators

namespace EGZ
namespace Expansion

/-- Coordinates on an affine subspace in which `φ` is first-coordinate
projection followed by translation by `c`. -/
structure AffineModel {p d r : ℕ}
    (V : AffineSubspace (ZMod p) (FpCoord p d))
    (φ : FpCoord p d →ᵃ[ZMod p] FpCoord p r) (c : FpCoord p r) (t : ℕ) where
  /-- The injective affine chart from model coordinates onto the ambient affine set. -/
  chart : FpCoord p (r + t) →ᵃ[ZMod p] FpCoord p d
  injective : Function.Injective chart
  range_chart : Set.range chart = V
  projection : ∀ q, φ (chart q) = Coord.first r t q + c

theorem exists_affineModel {p d r : ℕ} [Fact p.Prime]
    (V : AffineSubspace (ZMod p) (FpCoord p d))
    (φ : FpCoord p d →ᵃ[ZMod p] FpCoord p r)
    (hφ : Set.SurjOn φ V Set.univ) (c : FpCoord p r) :
    ∃ t, r + t ≤ d ∧ Nonempty (AffineModel V φ c t) := by
  classical
  obtain ⟨o, ho, hoc⟩ := hφ (Set.mem_univ c)
  let F : V.direction →ₗ[ZMod p] FpCoord p r :=
    φ.linear.comp V.direction.subtype
  have hF : Function.Surjective F := by
    intro q
    obtain ⟨v, hv, hvq⟩ := hφ (Set.mem_univ (q + c))
    refine ⟨⟨v - o, V.vsub_mem_direction hv ho⟩, ?_⟩
    change φ.linear (v - o) = q
    have hh := φ.linearMap_vsub v o
    change φ.linear (v - o) = φ v - φ o at hh
    rw [hh, hvq, hoc, add_sub_cancel_right]
  obtain ⟨s, hs⟩ := F.exists_rightInverse_of_surjective (LinearMap.range_eq_top.mpr hF)
  have hs' (q : FpCoord p r) : F (s q) = q := LinearMap.congr_fun hs q
  let t := Module.finrank (ZMod p) F.ker
  let B : F.ker ≃ₗ[ZMod p] FpCoord p t := (Module.finBasis (ZMod p) F.ker).equivFun
  let L : FpCoord p (r + t) →ₗ[ZMod p] V.direction :=
    s.comp (Coord.first r t) + F.ker.subtype.comp (B.symm.toLinearMap.comp (Coord.last r t))
  have hL (q : FpCoord p (r + t)) : F (L q) = Coord.first r t q := by
    change F (s (Coord.first r t q) + (B.symm (Coord.last r t q) : F.ker)) = _
    rw [map_add, hs']
    simp
  have hLi : Function.Injective L := by
    intro q u hqu
    have hf : Coord.first r t q = Coord.first r t u := by
      rw [← hL q, ← hL u, hqu]
    apply Coord.ext_first_last hf
    apply B.symm.injective
    apply Subtype.ext
    change s (Coord.first r t q) + (B.symm (Coord.last r t q) : V.direction) =
      s (Coord.first r t u) + (B.symm (Coord.last r t u) : V.direction) at hqu
    rw [hf] at hqu
    exact add_left_cancel hqu
  have hLs : Function.Surjective L := by
    intro v
    let z : F.ker := ⟨v - s (F v), by simp only [LinearMap.mem_ker, map_sub, hs', sub_self]⟩
    refine ⟨Fin.append (F v) (B z), ?_⟩
    have hf : Coord.first r t (Fin.append (F v) (B z)) = F v := by ext i; simp
    have hl : Coord.last r t (Fin.append (F v) (B z)) = B z := by ext i; simp
    change s (Coord.first r t (Fin.append (F v) (B z))) +
      (B.symm (Coord.last r t (Fin.append (F v) (B z))) : V.direction) = v
    rw [hf, hl, B.symm_apply_apply]
    change s (F v) + (v - s (F v)) = v
    abel
  let A : FpCoord p (r + t) →ᵃ[ZMod p] FpCoord p d :=
    (V.direction.subtype.comp L).toAffineMap + AffineMap.const (ZMod p) _ o
  have hAi : Function.Injective A := by
    intro q u hqu
    apply hLi
    apply Subtype.ext
    exact add_right_cancel hqu
  have hAr : Set.range A = V := by
    ext v
    constructor
    · rintro ⟨q, rfl⟩
      exact V.vadd_mem_of_mem_direction (L q).property ho
    · intro hv
      obtain ⟨q, hq⟩ := hLs ⟨v - o, V.vsub_mem_direction hv ho⟩
      refine ⟨q, ?_⟩
      change (L q : FpCoord p d) + o = v
      rw [hq]
      exact sub_add_cancel v o
  have hAp (q : FpCoord p (r + t)) : φ (A q) = Coord.first r t q + c := by
    change φ ((L q : FpCoord p d) + o) = _
    have hh := φ.map_vadd o (L q : FpCoord p d)
    change φ ((L q : FpCoord p d) + o) = φ.linear (L q : FpCoord p d) + φ o at hh
    rw [hh, hoc]
    change F (L q) + c = _
    rw [hL]
  refine ⟨t, ?_, ⟨⟨A, hAi, hAr, hAp⟩⟩⟩
  have hdim := LinearMap.finrank_le_finrank_of_injective (A.linear_injective_iff.mpr hAi)
  simpa using hdim

/-- Relative thickness restricted to the affine space carrying the weight. -/
def IsThickRelativeOn {p d r : ℕ} [NeZero p]
    (w : FpCoord p d → ℕ) (V : Set (FpCoord p d))
    (φ : FpCoord p d → FpCoord p r) (T : ℕ) (δ : ℝ) : Prop :=
  ∀ ξ : FpCoord p d →ᵃ[ZMod p] ZMod p,
    (∃ v u, v ∈ V ∧ u ∈ V ∧ φ v = φ u ∧ ξ v ≠ ξ u) →
      IsThickAlong w ξ T δ

namespace AffineModel

variable {p d r t : ℕ} [NeZero p] [Fact p.Prime]
  {V : AffineSubspace (ZMod p) (FpCoord p d)}
  {φ : FpCoord p d →ᵃ[ZMod p] FpCoord p r} {c : FpCoord p r}
  (M : AffineModel V φ c t) (w : FpCoord p d → ℕ)
  (hw : ∀ v, w v ≠ 0 → v ∈ V)

omit [NeZero p] in
theorem chart_mem (q : FpCoord p (r + t)) : M.chart q ∈ V := by
  change M.chart q ∈ (V : Set (FpCoord p d))
  rw [← M.range_chart]
  exact ⟨q, rfl⟩

include hw

theorem pushWeight_weight : pushWeight M.chart (w ∘ M.chart) = w :=
  pushWeight_pullback M.chart M.injective w (fun v hv ↦ M.range_chart.symm ▸ hw v hv)

theorem fibreWeight (q : FpCoord p r) :
    pushWeight (Coord.first r t) (w ∘ M.chart) (q - c) = pushWeight φ w q := by
  classical
  calc
    _ = pushWeight (φ ∘ M.chart) (w ∘ M.chart) q := by
      simp only [pushWeight, Function.comp_apply, M.projection, eq_sub_iff_add_eq]
    _ = pushWeight φ (pushWeight M.chart (w ∘ M.chart)) q := by rw [pushWeight_comp]
    _ = _ := by rw [M.pushWeight_weight w hw]

theorem thickRelative {T : ℕ} {δ : ℝ}
    (h : IsThickRelativeOn w V φ T δ) :
    IsThickRelative (w ∘ M.chart) (Coord.first r t) T δ := by
  intro ξ hξ
  let B := affineLeftInverse M.chart
  have hBA (q : FpCoord p (r + t)) : B (M.chart q) = q :=
    affineLeftInverse_apply M.chart M.injective q
  have hnon : ∃ v u, v ∈ V ∧ u ∈ V ∧ φ v = φ u ∧
      (ξ.comp B) v ≠ (ξ.comp B) u := by
    obtain ⟨v, u, hfirst, hne⟩ := hξ
    refine ⟨M.chart v, M.chart u, M.chart_mem v, M.chart_mem u, ?_, ?_⟩
    · rw [M.projection, M.projection, hfirst]
    · simpa only [AffineMap.comp_apply, hBA] using hne
  have ht := h (ξ.comp B) hnon
  rw [isThickAlong_iff_compl] at ht ⊢
  have hm := natMass_pushWeight M.chart (w ∘ M.chart)
  rw [M.pushWeight_weight w hw] at hm
  have hon := natMassOn_pushWeight M.chart (w ∘ M.chart) (slab (ξ.comp B) T)ᶜ
  rw [M.pushWeight_weight w hw] at hon
  have hset : M.chart ⁻¹' (slab (ξ.comp B) T)ᶜ = (slab ξ T)ᶜ := by
    ext q
    simp only [Set.mem_preimage, Set.mem_compl_iff, slab, Set.mem_ofPred_eq,
      AffineMap.comp_apply, hBA]
  rw [hset] at hon
  simpa only [hm, hon] using ht

theorem hasZeroSumMultiplicity_of_coordinates
    (h : HasZeroSumMultiplicity (w ∘ M.chart)) : HasZeroSumMultiplicity w := by
  have ht := hasZeroSumMultiplicity_pushWeight M.chart h
  rwa [M.pushWeight_weight w hw] at ht

end AffineModel

end Expansion
end EGZ
