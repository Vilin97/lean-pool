/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.PacketFieldTower
public import LeanPool.NavierStokesAndEuler.Euler.PacketCylinderFieldProducts

/-! Exact identification of the packet's ordered-word blocks with the
genuine Sobolev blocks used in the correction energy. -/

@[expose] public section


noncomputable section

namespace EulerPacketCylinderField.Field

open Set Finset EulerSmoothLimit EulerLiftedGradientSpace EulerCylinderSobolevSpace
  EulerCylinderSobolev EulerCylinderSmoothOrbit EulerPacketProfileRecursion
  EulerParameterWordGevrey EulerLpCylinderTranslation EulerJetProductBounds
  EulerH6Pressure EulerSobolevGevreyOperators EulerSobolevWordBlocks

variable {P T : ℝ} [Fact (0 < P)] {raw : VectorField}

theorem toFieldTower_derivative (G : Field P T raw) (s : ℕ) (i : Fin 4)
    (t : Icc (0 : ℝ) T) :
    derivativeOperator P s i (G.toFieldTower.realization (s+1) t) =
      (G.derivative i).toFieldTower.realization s t := by
  apply value_injective P
  rw [(G.derivative i).toFieldTower_value]
  exact wordPath_eq_sobolev P G.path G.orbit s (fun _ : Fin 1 => i) t

theorem toFieldTower_derivative_path (G : Field P T raw) (s : ℕ) (i : Fin 4) :
    (derivativeOperator P s i).compLeftContinuous ℝ (Icc (0 : ℝ) T)
        (G.toFieldTower.realization (s+1)) = (G.derivative i).toFieldTower.realization s := by
  apply ContinuousMap.ext
  intro t
  exact G.toFieldTower_derivative s i t

theorem toFieldTower_levelNorm_eq (G : Field P T raw) (s n : ℕ) (hn : n ≤ s)
    (t : Icc (0 : ℝ) T) :
    levelNorm P (toJet P (G.toFieldTower.realization s t)) n =
      wordSum standardDirection (fun a : LiftTangent => translate P a (G.path t)) n 0 := by
  rw [levelNorm_eq_words]
  apply sum_congr rfl
  intro w _
  rw [toJet_word P _ hn]
  exact congrArg norm (sobolev_coordinate P s (G.path t)
    (path_evaluation_smooth P G.path G.orbit t) ⟨⟨n,by omega⟩,w⟩)

theorem toFieldTower_blockNorm_eq (G : Field P T raw) (s q n : ℕ) (hn : n + q ≤ s)
    (t : Icc (0 : ℝ) T) :
    blockNorm P (toJet P (G.toFieldTower.realization s t)) q n =
      block standardDirection q (fun a : LiftTangent => translate P a (G.path t)) n 0 := by
  rw [block_eq_sum_levels standardDirection q _ (path_evaluation_smooth P G.path G.orbit t)]
  apply sum_congr rfl
  intro r hr
  exact G.toFieldTower_levelNorm_eq s (n+r) (by have := mem_range.mp hr; omega) t

/-- Time evaluation is contractive for the full ordered-word block. -/
theorem toFieldTower_blockNorm_le (G : Field P T raw) (s q n : ℕ) (hn : n + q ≤ s)
    (t : Icc (0 : ℝ) T) :
    blockNorm P (toJet P (G.toFieldTower.realization s t)) q n ≤
      block standardDirection q (fun a : LiftTangent => pathTranslate P a G.path) n 0 := by
  rw [G.toFieldTower_blockNorm_eq s q n hn t]
  rw [← classicalBlockSize_eq P q (G.path t) (path_evaluation_smooth P G.path G.orbit t) n]
  exact path_classicalBlockSize_le P q G.path G.orbit t n

/-- Summing the four genuine coordinate derivatives spends exactly one
external word; there is no additional dimension factor. -/
theorem toFieldTower_derivative_block_sum_le (G : Field P T raw) (s q n : ℕ)
    (hn : n + q ≤ s) (t : Icc (0 : ℝ) T) :
    (∑ i : Fin 4, blockNorm P
      (toJet P (derivativeOperator P s i (G.toFieldTower.realization (s+1) t))) q n) ≤
      block standardDirection q (fun a : LiftTangent => pathTranslate P a G.path) (n+1) 0 := by
  calc
    _ ≤ ∑ i : Fin 4, block standardDirection q
        (fun a : LiftTangent => pathTranslate P a (G.derivative i).path) n 0 := by
      apply sum_le_sum
      intro i _
      rw [G.toFieldTower_derivative]
      exact (G.derivative i).toFieldTower_blockNorm_le s q n hn t
    _ = _ := by
      rw [block_succ standardDirection q _ G.orbit]
      apply sum_congr rfl
      intro i _
      have he : (fun a : LiftTangent => pathTranslate P a (G.derivative i).path) =
          directional standardDirection (fun a : LiftTangent => pathTranslate P a G.path) i :=
        funext (derivativePath_translation P G.path G.orbit i)
      rw [he]

end EulerPacketCylinderField.Field
