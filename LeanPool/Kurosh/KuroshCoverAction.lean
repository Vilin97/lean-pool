/-
Copyright (c) 2026 Arthur Freitas Ramos et al. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arthur Freitas Ramos, David Barros Hulak, Ruy J. G. B. de Queiroz
-/
module

public import LeanPool.Kurosh.KuroshRawPathValue
public import Mathlib.Combinatorics.Quiver.Covering

/-!
# Kurosh Cover Action

Adapted for Lean Pool from Arthur742Ramos/KuroshSubgroupTheorem,
commit `911707126c8b9bb0c764bf853008fe1053c0aad9`: imports, API compatibility,
and proof organization were revised.
-/

public section

open Set Function
open CategoryTheory
open scoped Pointwise
noncomputable section

/-- Classical equality used locally in this part of the Kurosh construction. -/
local instance GraphCoveringTheory.Kurosh.kuroshCoverActionDecidableEq
    (α : Type*) : DecidableEq α := Classical.decEq α

universe u v w

namespace GraphCoveringTheory.Kurosh

open Monoid.CoprodI

theorem Internal.rightCosetMk_mul_out_mk {P : Type u} [Group P]
    (K : Subgroup P) (p r : P) :
    rightCosetMk K (p * Quotient.out (rightCosetMk K r)) =
      rightCosetMk K (p * r) := by
  have hc : rightCosetMk K (Quotient.out (rightCosetMk K r)) =
      rightCosetMk K r := Quotient.out_eq _
  rcases (rightCosetMk_eq_iff K _ _).1 hc with ⟨k, hk⟩
  apply (rightCosetMk_eq_iff K _ _).2
  refine ⟨k, ?_⟩
  calc
    p * Quotient.out (rightCosetMk K r) * (k : P) =
        p * (Quotient.out (rightCosetMk K r) * (k : P)) := by
          rw [mul_assoc]
    _ = p * r := by rw [hk]

theorem Internal.coverEdgeSource_smul {ι : Type v}
    (G : ι → Type u) [∀ i, Group (G i)] (H : Subgroup (FreeProduct G))
    (p q : CoverSource G H) (e : CoverEdge G H) :
    coverEdgeSource G H (p * q, e) =
      p • coverEdgeSource G H (q, e) := by
  apply congrArg (Sigma.mk e.1)
  change rightCosetMk
      (MonoidHom.range (treeKuroshVertexInclusion G H e.1)) (p * q) =
    rightCosetMk (MonoidHom.range
      (treeKuroshVertexInclusion G H e.1))
      (p * Quotient.out (rightCosetMk
        (MonoidHom.range (treeKuroshVertexInclusion G H e.1)) q))
  exact (Internal.rightCosetMk_mul_out_mk _ _ _).symm

theorem Internal.coverEdgeTarget_smul {ι : Type v}
    (G : ι → Type u) [∀ i, Group (G i)] (H : Subgroup (FreeProduct G))
    (p q : CoverSource G H) (e : CoverEdge G H) :
    coverEdgeTarget G H (p * q, e) =
      p • coverEdgeTarget G H (q, e) := by
  apply congrArg (Sigma.mk e.2.1)
  change rightCosetMk
      (MonoidHom.range (treeKuroshVertexInclusion G H e.2.1))
      ((p * q) * (coverEdgeLetter G H e)⁻¹) =
    rightCosetMk (MonoidHom.range
      (treeKuroshVertexInclusion G H e.2.1))
      (p * Quotient.out (rightCosetMk
        (MonoidHom.range (treeKuroshVertexInclusion G H e.2.1))
        (q * (coverEdgeLetter G H e)⁻¹)))
  rw [mul_assoc]
  exact (Internal.rightCosetMk_mul_out_mk _ _ _).symm

/-- Translate an auxiliary covering edge by a covering-group element. -/
noncomputable def coverEdgeAction {ι : Type v}
    (G : ι → Type u) [∀ i, Group (G i)] (H : Subgroup (FreeProduct G))
    (p : CoverSource G H) {x y : CoverVertex G H}
    (d : @Quiver.Hom (CoverVertex G H) (coverQuiver G H) x y) :
    @Quiver.Hom (CoverVertex G H) (coverQuiver G H) (p • x) (p • y) := by
  refine ⟨(p * d.1.1, d.1.2), ?_, ?_⟩
  · calc
      coverEdgeSource G H (p * d.1.1, d.1.2) =
          p • coverEdgeSource G H d.1 :=
        Internal.coverEdgeSource_smul G H p d.1.1 d.1.2
      _ = p • x := congrArg (fun z => p • z) d.2.1
  · calc
      coverEdgeTarget G H (p * d.1.1, d.1.2) =
          p • coverEdgeTarget G H d.1 :=
        Internal.coverEdgeTarget_smul G H p d.1.1 d.1.2
      _ = p • y := congrArg (fun z => p • z) d.2.2

/-- Translation by a covering-group element as a quiver prefunctor. -/
noncomputable def coverActionPrefunctor {ι : Type v}
    (G : ι → Type u) [∀ i, Group (G i)] (H : Subgroup (FreeProduct G))
    (p : CoverSource G H) : CoverVertex G H ⥤q CoverVertex G H where
  obj := fun x => p • x
  map := coverEdgeAction G H p

/-- Extend covering-group translation to both edge orientations. -/
noncomputable def coverActionSymmPrefunctor {ι : Type v}
    (G : ι → Type u) [∀ i, Group (G i)] (H : Subgroup (FreeProduct G))
    (p : CoverSource G H) :
    Quiver.Symmetrify (CoverVertex G H) ⥤q
      Quiver.Symmetrify (CoverVertex G H) :=
  (coverActionPrefunctor G H p).symmetrify

/-- Translate a symmetrified path in the auxiliary covering graph. -/
noncomputable def coverPathAction {ι : Type v}
    (G : ι → Type u) [∀ i, Group (G i)] (H : Subgroup (FreeProduct G))
    (p : CoverSource G H) {x y : CoverVertex G H}
    (q : @Quiver.Path (Quiver.Symmetrify (CoverVertex G H)) _ x y) :
    @Quiver.Path (Quiver.Symmetrify (CoverVertex G H)) _ (p • x) (p • y) :=
  (coverActionSymmPrefunctor G H p).mapPath q

theorem Internal.coverPathAction_nil {ι : Type v}
    (G : ι → Type u) [∀ i, Group (G i)] (H : Subgroup (FreeProduct G))
    (p : CoverSource G H) (x : CoverVertex G H) :
    coverPathAction G H p
      (Quiver.Path.nil : @Quiver.Path
        (Quiver.Symmetrify (CoverVertex G H)) _ x x) = Quiver.Path.nil := by
  rfl

theorem Internal.coverVertex_action_root {ι : Type v}
    (G : ι → Type u) [∀ i, Group (G i)] (H : Subgroup (FreeProduct G))
    (p : CoverSource G H) :
    p • coverVertexMk G H (rawBassSerreOrbitRoot G H) 1 =
      coverVertexMk G H (rawBassSerreOrbitRoot G H) p := by
  apply congrArg (Sigma.mk (rawBassSerreOrbitRoot G H))
  change rightCosetMk
      (MonoidHom.range (treeKuroshVertexInclusion G H
        (rawBassSerreOrbitRoot G H)))
      (p * Quotient.out (rightCosetMk
        (MonoidHom.range (treeKuroshVertexInclusion G H
          (rawBassSerreOrbitRoot G H))) 1)) =
    rightCosetMk (MonoidHom.range (treeKuroshVertexInclusion G H
      (rawBassSerreOrbitRoot G H))) p
  simpa using Internal.rightCosetMk_mul_out_mk
    (MonoidHom.range (treeKuroshVertexInclusion G H
      (rawBassSerreOrbitRoot G H))) p 1

theorem Internal.coverVertexRange_action_one {ι : Type v}
    (G : ι → Type u) [∀ i, Group (G i)] (H : Subgroup (FreeProduct G))
    (a : RawBassSerreOrbitVertex G H)
    (k : treeVertexStabilizer G H a) :
    treeKuroshVertexInclusion G H a k • coverVertexMk G H a 1 =
      coverVertexMk G H a 1 := by
  apply congrArg (Sigma.mk a)
  change rightCosetMk (MonoidHom.range
      (treeKuroshVertexInclusion G H a))
      (treeKuroshVertexInclusion G H a k * Quotient.out
        (rightCosetMk (MonoidHom.range
          (treeKuroshVertexInclusion G H a)) 1)) =
    rightCosetMk (MonoidHom.range
      (treeKuroshVertexInclusion G H a)) 1
  rw [Internal.rightCosetMk_mul_out_mk]
  apply (rightCosetMk_eq_iff
    (MonoidHom.range (treeKuroshVertexInclusion G H a)) _ _).2
  let kk : MonoidHom.range (treeKuroshVertexInclusion G H a) :=
    ⟨treeKuroshVertexInclusion G H a k, ⟨k, rfl⟩⟩
  refine ⟨kk⁻¹, ?_⟩
  change treeKuroshVertexInclusion G H a k * (↑kk : CoverSource G H)⁻¹ = 1
  have hkk : (↑kk : CoverSource G H) =
      treeKuroshVertexInclusion G H a k := rfl
  rw [hkk, mul_inv_cancel]

theorem Internal.coverFactorLoopPath {ι : Type v}
    (G : ι → Type u) [∀ i, Group (G i)] (H : Subgroup (FreeProduct G))
    (a : RawBassSerreOrbitVertex G H)
    (k : treeVertexStabilizer G H a) :
    Nonempty (@Quiver.Path (Quiver.Symmetrify (CoverVertex G H)) _
      (coverVertexMk G H (rawBassSerreOrbitRoot G H) 1)
      (coverVertexMk G H (rawBassSerreOrbitRoot G H)
        (treeKuroshVertexInclusion G H a k))) := by
  let q := rawTreePathMap G H (rawTreePathAtRoot G H a)
  let lp := coverPathLift G H (1 : CoverSource G H) q
  have hr : lp.1 = 1 := by
    dsimp [lp, q]
    rw [coverPathLift_value, Internal.coverPathValue_rawTree]
    simp
  let p₀ : @Quiver.Path (Quiver.Symmetrify (CoverVertex G H)) _
      (coverVertexMk G H (rawBassSerreOrbitRoot G H) 1)
      (coverVertexMk G H a 1) :=
    lp.2.cast rfl (congrArg (coverVertexMk G H a) hr)
  let s : CoverSource G H := treeKuroshVertexInclusion G H a k
  let p₁ := coverPathAction G H s p₀.reverse
  have hs : s • coverVertexMk G H a 1 = coverVertexMk G H a 1 := by
    exact Internal.coverVertexRange_action_one G H a k
  have hroot : s • coverVertexMk G H (rawBassSerreOrbitRoot G H) 1 =
      coverVertexMk G H (rawBassSerreOrbitRoot G H) s := by
    exact Internal.coverVertex_action_root G H s
  refine ⟨p₀.comp (p₁.cast hs hroot)⟩

theorem Internal.coverFactorLoopPath_value {ι : Type v}
    (G : ι → Type u) [∀ i, Group (G i)] (H : Subgroup (FreeProduct G))
    (a : RawBassSerreOrbitVertex G H)
    (k : treeVertexStabilizer G H a) :
    Nonempty (@Quiver.Path (Quiver.Symmetrify (CoverVertex G H)) _
      (coverVertexMk G H (rawBassSerreOrbitRoot G H) 1)
      (coverVertexMk G H (rawBassSerreOrbitRoot G H)
        (treeKuroshVertexInclusion G H a k))) :=
  Internal.coverFactorLoopPath G H a k

end GraphCoveringTheory.Kurosh
