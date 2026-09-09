/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import Mathlib.Analysis.InnerProductSpace.Symmetric
public import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.InnerProductSpace.Calculus

/-! Conservation of the antisymmetric frame pairing for a particle flow
whose acceleration gradient is a symmetric operator. -/

@[expose] public section


noncomputable section


open Set InnerProductSpace
open scoped Topology

namespace Euler.ComparatorBridge

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem frame_wronskian_constant
    (F G H B : ℝ → E →L[ℝ] E) (T : ℝ) (hT : 0 < T)
    (hF : ∀ t ∈ Icc 0 T, HasDerivWithinAt F (G t) (Icc 0 T) t)
    (hG : ∀ t ∈ Icc 0 T, HasDerivWithinAt G (H t) (Icc 0 T) t)
    (hH : ∀ t ∈ Icc 0 T, ∀ v, H t v = -(B t (F t v)))
    (hB : ∀ t ∈ Icc 0 T, (B t).IsSymmetric)
    (v w : E) (t : ℝ) (ht : t ∈ Icc 0 T) :
    ⟪G t v, F t w⟫_ℝ - ⟪F t v, G t w⟫_ℝ =
      ⟪G 0 v, F 0 w⟫_ℝ - ⟪F 0 v, G 0 w⟫_ℝ := by
  let q : ℝ → ℝ := fun r => ⟪G r v, F r w⟫_ℝ - ⟪F r v, G r w⟫_ℝ
  have hd (r : ℝ) (hr : r ∈ Icc 0 T) :
      HasDerivWithinAt q 0 (Icc 0 T) r := by
    have hfv := (ContinuousLinearMap.apply ℝ E v).hasFDerivAt.comp_hasDerivWithinAt r (hF r hr)
    have hfw := (ContinuousLinearMap.apply ℝ E w).hasFDerivAt.comp_hasDerivWithinAt r (hF r hr)
    have hgv := (ContinuousLinearMap.apply ℝ E v).hasFDerivAt.comp_hasDerivWithinAt r (hG r hr)
    have hgw := (ContinuousLinearMap.apply ℝ E w).hasFDerivAt.comp_hasDerivWithinAt r (hG r hr)
    have hh := (hgv.inner ℝ hfw).sub (hfv.inner ℝ hgw)
    convert! hh using 1
    change 0 = (⟪G r v, G r w⟫_ℝ + ⟪H r v, F r w⟫_ℝ) -
      (⟪F r v, H r w⟫_ℝ + ⟪G r v, G r w⟫_ℝ)
    have hb : ⟪B r (F r v), F r w⟫_ℝ = ⟪F r v, B r (F r w)⟫_ℝ := hB r hr _ _
    rw [hH r hr v, hH r hr w, inner_neg_left, inner_neg_right, hb]
    ring
  exact constant_of_derivWithin_zero
    (fun r hr => (hd r hr).differentiableWithinAt)
    (fun r hr => (hd r ⟨hr.1, hr.2.le⟩).derivWithin
      (uniqueDiffOn_Icc hT r ⟨hr.1, hr.2.le⟩)) t ht

/-- An initially symmetric Eulerian velocity gradient stays symmetric.
The two frame identities identify that gradient as `G * F⁻¹`. -/
theorem strain_symmetric_of_frame_wronskian
    (F G H B S J : ℝ → E →L[ℝ] E) (T : ℝ) (hT : 0 < T)
    (hF : ∀ t ∈ Icc 0 T, HasDerivWithinAt F (G t) (Icc 0 T) t)
    (hG : ∀ t ∈ Icc 0 T, HasDerivWithinAt G (H t) (Icc 0 T) t)
    (hH : ∀ t ∈ Icc 0 T, ∀ v, H t v = -(B t (F t v)))
    (hB : ∀ t ∈ Icc 0 T, (B t).IsSymmetric)
    (hS : ∀ t ∈ Icc 0 T, ∀ v, G t v = S t (F t v))
    (hJ : ∀ t ∈ Icc 0 T, ∀ v, F t (J t v) = v)
    (hzero : (S 0).IsSymmetric)
    (t : ℝ) (ht : t ∈ Icc 0 T) : (S t).IsSymmetric := by
  intro v w
  have hz : (0 : ℝ) ∈ Icc 0 T := ⟨le_rfl, hT.le⟩
  have hh := frame_wronskian_constant F G H B T hT hF hG hH hB (J t v) (J t w) t ht
  rw [hS t ht, hS t ht, hJ t ht, hJ t ht, hS 0 hz, hS 0 hz] at hh
  have hs : ⟪S 0 (F 0 (J t v)), F 0 (J t w)⟫_ℝ =
      ⟪F 0 (J t v), S 0 (F 0 (J t w))⟫_ℝ := hzero _ _
  rw [hs] at hh
  exact sub_eq_zero.mp (hh.trans (sub_self _))

end Euler.ComparatorBridge
