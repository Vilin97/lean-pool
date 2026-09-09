/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.PacketFieldSobolev

@[expose] public section

/-! Exact bounded-map naturality of every genuine Sobolev coordinate of
an actual packet field. -/

noncomputable section

namespace EulerPacketCylinderField.Field

open Set MeasureTheory EulerSmoothLimit EulerLiftedGradientSpace
  EulerCylinderSobolevSpace EulerCylinderSobolev EulerCylinderSmoothOrbit EulerParameterWordGevrey
  EulerLpCylinderTranslation EulerPacketProfileRecursion

variable {P T : ℝ} [Fact (0 < P)] {raw : VectorField}

theorem toFieldTower_word_eq (G : Field P T raw) (s n : ℕ) (hn : n ≤ s)
    (w : Fin n → Fin 4) (t : Icc (0 : ℝ) T) :
    (toJet P (G.toFieldTower.realization s t)).word w =
      wordDerivative standardDirection (fun a : LiftTangent => translate P a (G.path t)) w 0 := by
  rw [toJet_word P _ hn]
  exact sobolev_coordinate P s (G.path t) (path_evaluation_smooth P G.path G.orbit t)
    ⟨⟨n,by omega⟩,w⟩

theorem toFieldTower_word_map (G : Field P T raw) (L : Space →L[ℝ] Space)
    (s n : ℕ) (hn : n ≤ s) (w : Fin n → Fin 4) (t : Icc (0 : ℝ) T) :
    (toJet P ((G.map L).toFieldTower.realization s t)).word w =
      L.compLpL 2 (liftMeasure P) ((toJet P (G.toFieldTower.realization s t)).word w) := by
  rw [(G.map L).toFieldTower_word_eq s n hn w t,G.toFieldTower_word_eq s n hn w t]
  have he : (fun a : LiftTangent => translate P a ((G.map L).path t)) =
      (EulerCylinderConstantMap.map P L) ∘ (fun a : LiftTangent => translate P a (G.path t)) := by
    funext a
    exact (EulerCylinderConstantMap.map_translation P L a (G.path t)).symm
  rw [he]
  exact wordDerivative_comp_clm standardDirection (EulerCylinderConstantMap.map P L)
    (fun a : LiftTangent => translate P a (G.path t))
    (path_evaluation_smooth P G.path G.orbit t) w 0

end EulerPacketCylinderField.Field
