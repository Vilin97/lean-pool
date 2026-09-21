/-
Copyright (c) 2026 Dmitrii Zakharov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dmitrii Zakharov
-/

import LeanPool.ErdosGinzburgZiv.EGZ.Convex.FaceCombinations
import Mathlib.Analysis.LocallyConvex.Separation
import Mathlib.Analysis.LocallyConvex.HahnBanach

/-!
# Least exposed faces and relative interior

This module proves the converse to
`Face.isLeastFaceAt_of_mem_relInterior`.  The proof works inside the affine
span of a face.  If the point is on the relative boundary, Hahn--Banach gives
a nonconstant supporting functional there.  After extension to the ambient
space, a finite lexicographic perturbation of the functional exposing the
original face produces a strictly smaller exposed face through the point,
contradicting leastness.
-/

namespace EGZ.RationalPolytope.Face

/-- A least exposed face containing `q` contains `q` in its relative
interior. -/
theorem IsLeastFaceAt.mem_relInterior {d : ℕ} {P : RationalPolytope d}
    {q : RealCoord d} {F : P.Face} (hleast : IsLeastFaceAt P q F) :
    q ∈ F.relInterior := by
  classical
  by_contra hqrel
  have hqF : q ∈ F.carrier := hleast.1
  let A : AffineSubspace ℝ (RealCoord d) := affineSpan ℝ F.carrier
  let qA : A := ⟨q, by
    dsimp [A]
    exact subset_affineSpan ℝ F.carrier hqF⟩
  letI : Nonempty A := ⟨qA⟩
  letI : Nonempty F.carrier := ⟨⟨q, hqF⟩⟩
  let C : Set A := ((↑) : A → RealCoord d) ⁻¹' F.carrier
  have hCint : (interior C).Nonempty := by
    obtain ⟨r, hr⟩ := F.nonempty.intrinsicInterior F.convex
    rw [mem_intrinsicInterior] at hr
    exact ⟨hr.choose, hr.choose_spec.1⟩
  let e : A.direction ≃ᵃⁱ[ℝ] A := AffineIsometryEquiv.vaddConst ℝ qA
  let S : Set A.direction := e ⁻¹' C
  have hSconvex : Convex ℝ S := by
    change Convex ℝ
      ((A.subtype.comp e.toAffineEquiv.toAffineMap) ⁻¹' F.carrier)
    exact F.convex.affine_preimage
      (A.subtype.comp e.toAffineEquiv.toAffineMap)
  have hpreInterior :
      e ⁻¹' interior C = interior (e ⁻¹' C) := by
    simpa only [AffineIsometryEquiv.coe_toHomeomorph] using
      e.toHomeomorph.preimage_interior C
  have hSint : (interior S).Nonempty := by
    obtain ⟨y, hy⟩ := hCint
    refine ⟨e.symm y, ?_⟩
    have hy' : e.symm y ∈ e ⁻¹' interior C := by simpa
    rw [hpreInterior] at hy'
    exact hy'
  have h0not : (0 : A.direction) ∉ interior S := by
    intro h0
    apply hqrel
    change q ∈ intrinsicInterior ℝ F.carrier
    rw [mem_intrinsicInterior]
    refine ⟨qA, ?_, rfl⟩
    have h0' : (0 : A.direction) ∈ e ⁻¹' interior C := by
      rw [hpreInterior]
      exact h0
    have he0 : e 0 = qA := by simp [e]
    change e 0 ∈ interior C at h0'
    rw [he0] at h0'
    exact h0'
  have h0S : (0 : A.direction) ∈ S := by
    change (e 0 : RealCoord d) ∈ F.carrier
    have he0 : e 0 = qA := by simp [e]
    rw [he0]
    exact hqF
  obtain ⟨g, hgne, hgmax⟩ :=
    geometric_hahn_banach_of_nonempty_interior_point
      hSconvex h0not hSint
  have hSspan : affineSpan ℝ S = ⊤ :=
    (hSconvex.interior_nonempty_iff_affineSpan_eq_top).1 hSint
  have hstrict : ∃ u ∈ S, g u < 0 := by
    by_contra hnone
    have hzeroMap : g.toLinearMap.toAffineMap =
        (0 : A.direction →ᵃ[ℝ] ℝ) := by
      apply AffineMap.ext_on hSspan
      intro u hu
      have hle : g u ≤ 0 := by simpa using hgmax u hu
      have hge : 0 ≤ g u := by
        exact not_lt.mp (fun hlt ↦ hnone ⟨u, hu, hlt⟩)
      change g u = 0
      exact le_antisymm hle hge
    apply hgne
    apply ContinuousLinearMap.ext
    intro u
    have hu := DFunLike.congr_fun hzeroMap u
    simpa using hu
  obtain ⟨u, huS, hgu⟩ := hstrict
  let xA : A := e u
  let x : RealCoord d := xA
  have hxF : x ∈ F.carrier := by
    change (e u : RealCoord d) ∈ F.carrier at huS
    exact huS
  obtain ⟨gext, hgext⟩ := StrongDual.exists_extension A.direction g
  have hg_le (y : RealCoord d) (hyF : y ∈ F.carrier) :
      gext y ≤ gext q := by
    let yA : A := ⟨y, by
      dsimp [A]
      exact subset_affineSpan ℝ F.carrier hyF⟩
    let v : A.direction := yA -ᵥ qA
    have hvS : v ∈ S := by
      change e v ∈ C
      have hev : e v = yA := by simp [e, v]
      rw [hev]
      exact hyF
    have hgv : g v ≤ 0 := by simpa using hgmax v hvS
    have hvcoe : ((v : A.direction) : RealCoord d) = y - q := by
      simp [v, yA, qA]
    have hdiff : gext (y - q) ≤ 0 := by
      rw [← hvcoe, hgext v]
      exact hgv
    simpa only [map_sub, sub_nonpos] using hdiff
  have hg_strict : gext x < gext q := by
    have hxsub : x - q = ((u : A.direction) : RealCoord d) := by
      simp [x, xA, e, qA]
    have hdiff : gext (x - q) < 0 := by
      rw [hxsub, hgext u]
      exact hgu
    simpa only [map_sub, sub_neg] using hdiff
  obtain ⟨f, level, hfle, hFcarrier⟩ := F.is_exposed
  have hfq : f q = level := by
    rw [hFcarrier] at hqF
    exact hqF.2
  have hfx : f x = level := by
    rw [hFcarrier] at hxF
    exact hxF.2
  let ψ : RealCoord d →ᵃ[ℝ] ℝ := gext.toLinearMap.toAffineMap
  let ratio : RealCoord d → ℝ := fun y ↦
    (ψ y - ψ q) / (level - f y)
  let bound : ℝ := P.generators.sup' P.generators_nonempty ratio
  let scale : ℝ := max bound 0 + 1
  have hbound_lt_scale : bound < scale := by
    dsimp [scale]
    linarith [le_max_left bound 0]
  let perturbed : RealCoord d →ᵃ[ℝ] ℝ := scale • f + ψ
  let perturbedLevel : ℝ := scale * level + ψ q
  have hgen_le : ∀ y ∈ P.generators,
      perturbed y ≤ perturbedLevel := by
    intro y hygen
    have hyP : y ∈ P.carrier := by
      rw [P.carrier_eq_convexHull]
      exact subset_convexHull ℝ _ hygen
    have hfy_le : f y ≤ level := hfle y hyP
    by_cases hyF : y ∈ F.carrier
    · have hfy : f y = level := by
        rw [hFcarrier] at hyF
        exact hyF.2
      have hgy : ψ y ≤ ψ q := by
        exact hg_le y hyF
      change scale * f y + ψ y ≤ scale * level + ψ q
      rw [hfy]
      linarith
    · have hfy_ne : f y ≠ level := by
        intro hfy
        apply hyF
        rw [hFcarrier]
        exact ⟨hyP, hfy⟩
      have hdelta : 0 < level - f y := by
        exact sub_pos.mpr (lt_of_le_of_ne hfy_le hfy_ne)
      have hratio_le : ratio y ≤ bound := by
        dsimp [bound]
        exact Finset.le_sup' ratio hygen
      have hratio_lt : ratio y < scale :=
        hratio_le.trans_lt hbound_lt_scale
      have hdiff : ψ y - ψ q < scale * (level - f y) := by
        exact (div_lt_iff₀ hdelta).mp hratio_lt
      change scale * f y + ψ y ≤ scale * level + ψ q
      exact le_of_lt (by linarith)
  have hP_le : ∀ y ∈ P.carrier, perturbed y ≤ perturbedLevel := by
    intro y hyP
    rw [P.carrier_eq_convexHull] at hyP
    apply convexHull_min (𝕜 := ℝ)
        (s := (↑P.generators : Set (RealCoord d)))
        (t := {z | perturbed z ≤ perturbedLevel})
    · intro z hz
      exact hgen_le z hz
    · exact (convex_Iic perturbedLevel).affine_preimage perturbed
    · exact hyP
  have hqP : q ∈ P.carrier := F.subset_polytope hleast.1
  have hqPerturbed : perturbed q = perturbedLevel := by
    change scale * f q + ψ q = scale * level + ψ q
    rw [hfq]
  let G : P.Face := {
    carrier := {y | y ∈ P.carrier ∧ perturbed y = perturbedLevel}
    is_exposed := ⟨perturbed, perturbedLevel, hP_le, rfl⟩
    nonempty := ⟨q, hqP, hqPerturbed⟩
  }
  have hqG : q ∈ G.carrier := ⟨hqP, hqPerturbed⟩
  have hxG : x ∈ G.carrier := (hleast.2 G hqG) hxF
  have hxPerturbed : perturbed x = perturbedLevel := hxG.2
  have hxPerturbed_lt : perturbed x < perturbedLevel := by
    have hψstrict : ψ x < ψ q := by
      exact hg_strict
    change scale * f x + ψ x < scale * level + ψ q
    rw [hfx]
    linarith
  exact (ne_of_lt hxPerturbed_lt) hxPerturbed

end EGZ.RationalPolytope.Face
