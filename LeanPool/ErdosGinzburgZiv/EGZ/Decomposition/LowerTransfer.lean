/-
Copyright (c) 2026 Dmitrii Zakharov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dmitrii Zakharov
-/

import LeanPool.ErdosGinzburgZiv.EGZ.Decomposition.FaceRefinement
import LeanPool.ErdosGinzburgZiv.EGZ.Decomposition.ReducedRepresentative

/-!
# Moving all local mass below an anchor to a lower layer

After slab pruning, the completeness refinement transfers every surviving
local summand below the anchor to the lower layer. The lower anchor keeps
the same cumulative function, while its upper copy ceases to be reduced.
-/

open Classical

namespace EGZ.FlagDecomposition.LowerTransfer

variable {p d : ℕ} [NeZero p] {f : FpCoord p d → ℕ}
    (Φ : FlagDecomposition p d f) (anchor : Φ.flag.Node) (hp : Odd p)

noncomputable abbrev decomposition : FlagDecomposition p d f :=
  FaceRefinement.decomposition Φ anchor (fun _ ↦ True) hp

noncomputable abbrev upper (x : Φ.flag.Node) :=
  FaceRefinement.upper Φ anchor (fun _ ↦ True) hp x

theorem active_lowerAnchor :
    ((FaceRefinement.splitWeights Φ anchor (fun _ ↦ True)).rebuildData hp).Active
      (TwoLayer.lower anchor anchor le_rfl) := by
  obtain ⟨q, hq⟩ := Φ.liftedSupport_nonempty anchor
  obtain ⟨_, v, _, hv⟩ := (Φ.originalWeights.hat_ne_zero_iff anchor q).mp
    ((Φ.liftedSupport_spec anchor q).mp hq)
  exact FaceRefinement.active_lower Φ anchor (fun _ ↦ True) hp anchor le_rfl v hv trivial

def lowerAnchor : (decomposition Φ anchor hp).flag.Node :=
  ⟨TwoLayer.lower anchor anchor le_rfl, active_lowerAnchor Φ anchor hp⟩

theorem lowerAnchor_le_upper : lowerAnchor Φ anchor hp ≤ upper Φ anchor hp anchor := by
  exact (TwoLayer.lower_le_upper anchor anchor anchor le_rfl).mpr le_rfl

@[simp]
theorem lowerAnchor_cumulativeWeight :
    (decomposition Φ anchor hp).cumulativeWeight (lowerAnchor Φ anchor hp) =
      Φ.cumulativeWeight anchor := by
  rw [(FaceRefinement.splitWeights Φ anchor (fun _ ↦ True)).decomposition_cumulativeWeight
    hp (lowerAnchor Φ anchor hp)]
  funext v
  exact (FaceRefinement.cumulative_lower Φ anchor (fun _ ↦ True) anchor le_rfl v).trans
    (ite_eq_left trivial)

/-- Moving all atoms down preserves the old cumulative function at both
copies of every surviving node. -/
theorem cumulativeWeight_projection (x : (decomposition Φ anchor hp).flag.Node) :
    (decomposition Φ anchor hp).cumulativeWeight x = Φ.cumulativeWeight x.1.1.1 := by
  rw [(FaceRefinement.splitWeights Φ anchor (fun _ ↦ True)).decomposition_cumulativeWeight hp x]
  funext v
  obtain ⟨a, ha⟩ := (TwoLayer.layerEquiv anchor).surjective x.1
  cases a with
  | inl a =>
      have ha' : x.1 = TwoLayer.upper anchor a := ha.symm
      rw [ha']
      exact FaceRefinement.cumulative_upper Φ anchor (fun _ ↦ True) a v
  | inr a =>
      have ha' : x.1 = TwoLayer.lower anchor a.1 a.2 := ha.symm
      rw [ha']
      exact (FaceRefinement.cumulative_lower Φ anchor (fun _ ↦ True) a.1 a.2 v).trans
        (ite_eq_left trivial)

/-- Every local generator below the upper anchor has lower-layer base. -/
theorem local_layer_zero (q : (decomposition Φ anchor hp).flag.Point)
    (hq : q ∈ (decomposition Φ anchor hp).omegaZero)
    (hbelow : q.base ≤ upper Φ anchor hp anchor) : q.base.1.1.2 = 0 := by
  obtain ⟨z, _, hz⟩ := hq
  obtain ⟨_, v, _, hv⟩ := (FlagDecompositionRaw.localLift_ne_zero_iff _ _ _ _).mp hz
  by_contra hlayer
  change TwoLayer.splitWeight anchor Φ.localWeight (fun _ ↦ True) q.base.1 v ≠ 0 at hv
  have hbase : q.base.1.1.1 ≤ anchor := hbelow.1
  simp only [TwoLayer.splitWeight, ite_eq_right hlayer, hbase, and_self, ite_eq_left] at hv
  exact hv rfl

/-- The old upper anchor has no proper point based there after all its
local generators have moved down to the lower layer. -/
theorem upperAnchor_not_isReducedElement :
    ¬ (decomposition Φ anchor hp).IsReducedElement (upper Φ anchor hp anchor) := by
  rintro ⟨q, ⟨n, points, weight, hpoints, hcomb⟩, hbase⟩
  have hle : q.base ≤ lowerAnchor Φ anchor hp := by
    apply hcomb.base_isLUB.2
    intro i hi
    have hupper : (points i).base ≤ upper Φ anchor hp anchor := by
      rw [← hbase]
      exact hcomb.base_isLUB.1 i hi
    have hzero := local_layer_zero Φ anchor hp (points i) (hpoints i) hupper
    change (points i).base.1.1.1 ≤ anchor ∧ (points i).base.1.1.2 ≤ (0 : Fin 2)
    exact ⟨hupper.1, by rw [hzero]⟩
  rw [hbase] at hle
  exact TwoLayer.not_upper_le_lower anchor anchor anchor le_rfl hle

/-- Additional slab coordinates are carried only by lower nodes. -/
noncomputable def extra (k : ℕ) (x : (decomposition Φ anchor hp).flag.Node) : ℕ :=
  if x.1.1.2 = 0 then k else 0

theorem extra_antitone (k : ℕ) : Antitone (extra Φ anchor hp k) := by
  intro x y hxy
  unfold extra
  by_cases hy : y.1.1.2 = 0
  · have hx : x.1.1.2 = 0 := by
      have hle : x.1.1.2 ≤ y.1.1.2 := hxy.2
      rw [hy] at hle
      exact le_antisymm hle (Fin.zero_le _)
    rw [ite_eq_left hy, ite_eq_left hx]
  · rw [ite_eq_right hy]
    exact Nat.zero_le _

@[simp]
theorem extra_upper (k : ℕ) (x : Φ.flag.Node) :
    extra Φ anchor hp k (upper Φ anchor hp x) = 0 := by
  simp [extra, upper, FaceRefinement.upper, TwoLayer.upper]

@[simp]
theorem extra_lowerAnchor (k : ℕ) :
    extra Φ anchor hp k (lowerAnchor Φ anchor hp) = k := by
  simp [extra, lowerAnchor, TwoLayer.lower]

end EGZ.FlagDecomposition.LowerTransfer
