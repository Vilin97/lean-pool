/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.LpSmoothFieldAlgebra
public import LeanPool.NavierStokesAndEuler.Euler.PacketParentLabelBudgets
import Mathlib.Algebra.Order.Star.Real

/-! Ordinary spatial L² tensor bounds imply the actual classical label
Sobolev word bounds. The finite Sobolev order contributes only a fixed
polynomial amplitude and one fixed enlargement of the radius. -/

@[expose] public section


noncomputable section

namespace EulerLpTranslation.SmoothL2Field

open MeasureTheory EulerSmoothLimit EulerMeanClassicalWordBounds
  EulerParameterWordGevrey EulerGevrey
open scoped ContDiff

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

/-- Has jet bound, given by `∀ n, ‖A.jetLp n‖ ≤ C*R^n*(n.factorial : ℝ)^2`. -/
def HasJetBound (A : SmoothL2Field V) (C R : ℝ) : Prop :=
  ∀ n, ‖A.jetLp n‖ ≤ C*R^n*(n.factorial : ℝ)^2

theorem norm_jetLp (A : SmoothL2Field V) (n : ℕ) :
    ‖A.jetLp n‖ = (eLpNorm (iteratedFDeriv ℝ n A.field) 2 volume).toReal :=
  Lp.norm_toLp _ _

theorem hasJetBound_iff (A : SmoothL2Field V) (C R : ℝ) :
    A.HasJetBound C R ↔ ∀ n,
      (eLpNorm (iteratedFDeriv ℝ n A.field) 2 volume).toReal ≤
        C*R^n*(n.factorial : ℝ)^2 := by
  simp only [HasJetBound,norm_jetLp]

theorem HasJetBound.mono {A : SmoothL2Field V} {C R D S : ℝ}
    (h : A.HasJetBound C R) (hC : 0 ≤ C) (hR : 0 ≤ R)
    (hCD : C ≤ D) (hRS : R ≤ S) : A.HasJetBound D S := by
  intro n
  exact (h n).trans (mul_le_mul_of_nonneg_right
    (mul_le_mul hCD (pow_le_pow_left₀ hR hRS n) (pow_nonneg hR n) (hC.trans hCD))
    (sq_nonneg _))

theorem HasJetBound.add {A B : SmoothL2Field V} {C D R : ℝ}
    (hA : A.HasJetBound C R) (hB : B.HasJetBound D R) :
    (addField A B).HasJetBound (C+D) R := by
  intro n
  rw [jetLp_addField]
  exact (norm_add_le _ _).trans ((add_le_add (hA n) (hB n)).trans_eq (by ring))

theorem classicalBlockSize_of_jet_bound {ι : Type*} [Fintype ι]
    (directions : ι → Space) (hd : ∀ i, ‖directions i‖ ≤ 1)
    (q : ℕ) (A : SmoothL2Field Space) (C R : ℝ) (hC : 0 ≤ C) (hR : 0 ≤ R)
    (hb : A.HasJetBound C R) (n : ℕ) :
    classicalBlockSize directions q A.toLp A.translation_contDiff n ≤
      sobolevCoefficientAmplitude ι q R C *
        (sobolevCoefficientRadius ι R)^n*(n.factorial : ℝ)^2 := by
  apply (classicalBlockSize_eq directions q A.toLp A.translation_contDiff n).trans_le
  have hc := coefficientBlock_of_tensor_bound directions hd q
    (fun a : Space => translation a A.toLp) A.translation_contDiff R C hR hC
    (fun j a => (A.norm_iteratedFDeriv_translation_le j a).trans
      (by simpa only [majorant,Nat.add_zero,mul_assoc] using hb j)) n 0
  have hp : (1 : ℝ) ≤ (2 : ℝ)^q := one_le_pow₀ (by norm_num)
  have hle : block directions q (fun a : Space => translation a A.toLp) n 0 ≤
      coefficientBlock directions q (fun a : Space => translation a A.toLp) n 0 := by
    exact (one_mul _).symm.trans_le (mul_le_mul_of_nonneg_right hp
      (block_nonneg directions q (fun a : Space => translation a A.toLp) n 0))
  exact hle.trans (by simpa only [majorant,Nat.add_zero,mul_assoc] using hc)

theorem hasLabelBound_of_jet_bound (A : SmoothL2Field Space) (C R K : ℝ)
    (hC : 0 ≤ C) (hR : 0 ≤ R) (hb : A.HasJetBound C R)
    (hamp : sobolevCoefficientAmplitude (Fin 3) 6 R C ≤ K)
    (hrad : sobolevCoefficientRadius (Fin 3) R ≤ K) :
    EulerPacketParentLabelBounds.HasLabelBound K A := by
  have hr := sobolevCoefficientRadius_nonneg (ι := Fin 3) R hR
  have ha := sobolevCoefficientAmplitude_nonneg (ι := Fin 3) 6 R C hR hC
  intro n
  have h := classicalBlockSize_of_jet_bound EulerPacketParentLabelBounds.direction
    (by intro i; simp [EulerPacketParentLabelBounds.direction]) 6 A C R hC hR hb n
  apply h.trans
  have hpow := pow_le_pow_left₀ hr hrad n
  have hm := mul_le_mul hamp hpow (pow_nonneg hr n) (ha.trans hamp)
  simpa only [pow_succ,mul_comm K] using
    mul_le_mul_of_nonneg_right hm (sq_nonneg (n.factorial : ℝ))

end EulerLpTranslation.SmoothL2Field
