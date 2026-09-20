/-
Copyright (c) 2026 Arthur Freitas Ramos et al. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arthur Freitas Ramos, David Barros Hulak, Ruy J. G. B. de Queiroz
-/
import LeanPool.Kurosh.KuroshCoverAction
import LeanPool.Kurosh.KuroshFreeFiber

/-!
# Kurosh Cover Connected

Adapted for Lean Pool from Arthur742Ramos/KuroshSubgroupTheorem,
commit `911707126c8b9bb0c764bf853008fe1053c0aad9`: imports, API compatibility,
and proof organization were revised.
-/

open Set Function
open CategoryTheory
open scoped Pointwise
noncomputable section

/-- Classical equality used locally in this part of the Kurosh construction. -/
local instance GraphCoveringTheory.Kurosh.kuroshCoverConnectedDecidableEq
    (α : Type*) : DecidableEq α := Classical.decEq α

universe u v

namespace GraphCoveringTheory.Kurosh

theorem Internal.coverFreeFactorLoopPath {ι : Type v}
    (G : ι → Type u) [∀ i, Group (G i)] (H : Subgroup (FreeProduct G))
    (x : KuroshFreePart G H) :
    Nonempty (@Quiver.Path (Quiver.Symmetrify (CoverVertex G H)) _
      (coverVertexMk G H (rawBassSerreOrbitRoot G H) 1)
    (coverVertexMk G H (rawBassSerreOrbitRoot G H)
        (treeKuroshFreeInclusion G H x))) := by
  let z : KuroshFreePart G H := x⁻¹
  obtain ⟨q, hq⟩ := Internal.coverFreePath_exists G H
    (a := rawBassSerreOrbitRoot G H)
    (b := rawBassSerreOrbitRoot G H) z
  have hloop : coverPathFreeLoop G H q = x⁻¹ := by
    unfold coverPathFreeLoop
    rw [coverQuotientTreePathHom_root]
    simp only [Groupoid.inv_eq_inv]
    simp only [IsIso.inv_id, Category.comp_id]
    exact hq
  have hvalue : coverPathValue G H q =
      treeKuroshFreeInclusion G H x := by
    calc
      coverPathValue G H q =
          (treeKuroshFreeInclusion G H
            (coverPathFreeLoop G H q))⁻¹ :=
        coverPathValue_formula G H q
      _ = (treeKuroshFreeInclusion G H (x⁻¹))⁻¹ := by rw [hloop]
      _ = treeKuroshFreeInclusion G H x := by simp
  let lp := coverPathLift G H (1 : CoverSource G H) q
  have hp : lp.1 = treeKuroshFreeInclusion G H x := by
    dsimp [lp]
    rw [coverPathLift_value, hvalue]
    simp
  refine ⟨lp.2.cast rfl (congrArg
    (coverVertexMk G H (rawBassSerreOrbitRoot G H)) hp)⟩

theorem Internal.coverFactorLoopPath_rawTree {ι : Type v}
    (G : ι → Type u) [∀ i, Group (G i)] (H : Subgroup (FreeProduct G))
    (a : RawBassSerreOrbitVertex G H)
    (k : treeVertexStabilizer G H a) :
    Nonempty (@Quiver.Path (Quiver.Symmetrify (CoverVertex G H)) _
      (coverVertexMk G H (rawBassSerreOrbitRoot G H) 1)
      (coverVertexMk G H (rawBassSerreOrbitRoot G H)
        (treeKuroshVertexInclusion G H a k))) :=
  Internal.coverFactorLoopPath G H a k

theorem Internal.coverRootFiberPath {ι : Type v}
    (G : ι → Type u) [∀ i, Group (G i)] (H : Subgroup (FreeProduct G))
    (p : CoverSource G H) :
    Nonempty (@Quiver.Path (Quiver.Symmetrify (CoverVertex G H)) _
      (coverVertexMk G H (rawBassSerreOrbitRoot G H) 1)
      (coverVertexMk G H (rawBassSerreOrbitRoot G H) p)) := by
  induction p using Monoid.CoprodI.induction_on with
  | one =>
      exact ⟨Quiver.Path.nil⟩
  | of i m =>
      cases i using Sum.casesOn with
      | inl a =>
          cases m with
          | up k =>
              simpa [treeKuroshVertexInclusion] using
                Internal.coverFactorLoopPath_rawTree G H a k
      | inr i =>
          cases i
          cases m with
          | up x =>
              simpa [treeKuroshFreeInclusion] using
                Internal.coverFreeFactorLoopPath G H x
  | mul x y hx hy =>
      rcases hx with ⟨px⟩
      rcases hy with ⟨py⟩
      have hstart :
          x • coverVertexMk G H (rawBassSerreOrbitRoot G H) 1 =
            coverVertexMk G H (rawBassSerreOrbitRoot G H) x := by
        exact Internal.coverVertex_action_root G H x
      have htarget :
          x • coverVertexMk G H (rawBassSerreOrbitRoot G H) y =
            coverVertexMk G H (rawBassSerreOrbitRoot G H) (x * y) := by
        calc
          x • coverVertexMk G H (rawBassSerreOrbitRoot G H) y =
              x • (y • coverVertexMk G H (rawBassSerreOrbitRoot G H) 1) := by
                rw [Internal.coverVertex_action_root G H y]
          _ = (x * y) •
              coverVertexMk G H (rawBassSerreOrbitRoot G H) 1 :=
            (mul_smul x y _).symm
          _ = coverVertexMk G H (rawBassSerreOrbitRoot G H) (x * y) :=
            Internal.coverVertex_action_root G H (x * y)
      exact ⟨px.comp ((coverPathAction G H x py).cast hstart htarget)⟩

theorem Internal.coverSource_rootedConnected {ι : Type v}
    (G : ι → Type u) [∀ i, Group (G i)] (H : Subgroup (FreeProduct G)) :
    Quiver.RootedConnected
      (show Quiver.Symmetrify (CoverVertex G H) from
        coverVertexMk G H (rawBassSerreOrbitRoot G H) 1) := by
  constructor
  intro x
  cases x with
  | mk a c =>
      let q := rawTreePathMap G H (rawTreePathAtRoot G H a)
      let p : CoverSource G H := Quotient.out c
      let lp := coverPathLift G H p q
      have hcoord : lp.1 = p := by
        dsimp [lp, q]
        rw [coverPathLift_value, Internal.coverPathValue_rawTree]
        simp [p]
      have hend : coverVertexMk G H a lp.1 = ⟨a, c⟩ := by
        apply congrArg (Sigma.mk a)
        rw [hcoord]
        exact Quotient.out_eq c
      rcases Internal.coverRootFiberPath G H p with ⟨rp⟩
      exact ⟨rp.comp (lp.2.cast rfl hend)⟩

end GraphCoveringTheory.Kurosh
