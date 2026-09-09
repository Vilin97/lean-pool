/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.SmoothL2Gevrey
public import LeanPool.NavierStokesAndEuler.Euler.GevreyProductLp

@[expose] public section

/-! The classical label Sobolev norm also bounds the actual L² tensor
jets, so a parent satisfying (21) supplies every outer L² input needed
by the volume-preserving composition estimate. -/

noncomputable section

namespace EulerLpTranslation.SmoothL2Field

open MeasureTheory Filter Finset EulerSmoothLimit EulerMeanSmoothRepresentative
  EulerMeanClassicalWordBounds EulerParameterWordGevrey EulerPacketParentLabelBounds
  EulerGevreyProductLp
open scoped ContDiff

theorem norm_jetLp_le_wordSum (A : SmoothL2Field Space) (n : ℕ) :
    ‖A.jetLp n‖ ≤ wordSum direction (fun a : Space => translation a A.toLp) n 0 := by
  have he : representative A.toLp A.translation_contDiff = A.field :=
    representative_unique A.toLp A.translation_contDiff A.field A.smooth.continuous A.toLp_ae
  have ha (w : Fin n → Fin 3) :
      (ordinaryWord direction A.toLp w : Space → Space) =ᵐ[volume] wordDerivative direction A.field
        w := by
    simpa only [he] using ordinaryWord_ae direction A.toLp A.translation_contDiff w
  have hm (w : Fin n → Fin 3) : MemLp (wordDerivative direction A.field w) 2 volume :=
    (Lp.memLp (ordinaryWord direction A.toLp w)).ae_eq (ha w)
  let H : (Fin n → Fin 3) → Space → ℝ := fun w x => ‖wordDerivative direction A.field w x‖
  have hn (w : Fin n → Fin 3) : (eLpNorm (H w) 2 volume).toReal = ‖ordinaryWord direction A.toLp w‖
    := by
    rw [show H w = fun x => ‖wordDerivative direction A.field w x‖ from rfl,eLpNorm_norm]
    rw [← eLpNorm_congr_ae (ha w),Lp.norm_def]
  have hb := (finite_domination volume (univ : Finset (Fin n → Fin 3)) (iteratedFDeriv ℝ n A.field)
    ((A.smooth.continuous_iteratedFDeriv (m := n) (by simp)).aestronglyMeasurable)
    H (fun w _ => (hm w).norm) (fun x => tensor_le_wordSum A.field n x)).2
  rw [norm_jetLp]
  simpa only [hn,wordSum,ordinaryWord,EulerMeanSolenoidal.translation,
    EulerLpTranslation.translation] using hb

theorem norm_jetLp_le_classicalBlock (A : SmoothL2Field Space) (q n : ℕ) :
    ‖A.jetLp n‖ ≤ classicalBlockSize direction q A.toLp A.translation_contDiff n := by
  apply (norm_jetLp_le_wordSum A n).trans
  refine le_trans ?_ (le_of_eq
    (classicalBlockSize_eq direction q A.toLp A.translation_contDiff n).symm)
  unfold wordSum block
  exact sum_le_sum (fun w _ => norm_le_baseSize direction q _ 0)

theorem hasJetBound_of_labelBound (A : SmoothL2Field Space) (K : ℝ)
    (h : HasLabelBound K A) : A.HasJetBound K K := by
  intro n
  exact (norm_jetLp_le_classicalBlock A 6 n).trans
    ((h n).trans_eq (by rw [pow_succ]; ring))

theorem sup_bound_of_labelBound (A : SmoothL2Field Space) (K : ℝ)
    (h : HasLabelBound K A) (n : ℕ) (x : Space) :
    ‖iteratedFDeriv ℝ n A.field x‖ ≤ (embeddingCost*K)*K^n*(n.factorial : ℝ)^2 := by
  have hb := field_tensor_gevrey A.toLp A.translation_contDiff A.field A.smooth.continuous A.toLp_ae
    6 (by norm_num) K K (source_block_bound A.toLp A.translation_contDiff K h) n x
  simpa only [EulerGevrey.majorant,Nat.add_zero,mul_assoc] using hb

end EulerLpTranslation.SmoothL2Field
