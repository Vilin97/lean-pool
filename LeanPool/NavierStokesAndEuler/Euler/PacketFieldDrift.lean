/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import LeanPool.NavierStokesAndEuler.Euler.PacketCylinderFieldBounds
public import LeanPool.NavierStokesAndEuler.Euler.PacketFieldTower
public import LeanPool.NavierStokesAndEuler.Euler.SobolevDriftNorm
import LeanPool.NavierStokesAndEuler.Euler.PacketFieldSobolevBudget
public import LeanPool.NavierStokesAndEuler.Euler.PacketCylinderFieldProducts
public import LeanPool.NavierStokesAndEuler.Euler.PacketCylinderFieldAdvection
public import LeanPool.NavierStokesAndEuler.Euler.FunctionalVelocity
public import LeanPool.NavierStokesAndEuler.Euler.LiftedTransportComponents
import LeanPool.NavierStokesAndEuler.Euler.Foundations.SobolevDerivativeNorm

/-! The actual small drift budget from the packet's spatial and normal
word bounds, with the same radius and no full-velocity substitution. -/

section

/-! The actual four-component transport vector retains the small normal
component separately from its three scaled spatial components. -/

@[expose] public section

noncomputable section

namespace EulerLiftedVelocitySplit

open MeasureTheory ContinuousLinearMap InnerProductSpace EulerSmoothLimit
  EulerLiftedGradientSpace EulerMetricTransport EulerSobolevTransport
  EulerFunctionalVelocity EulerVectorCylinder EulerCylinderConstantMap
  EulerCylinderScalarPrimitive EulerPacketCylinderField

/-- Spatial velocity map, given by `velocityMap (Fin.cons 0 (fun i : Fin 3 => coordinate 3 i))`. -/
def spatialVelocityMap : Space →L[ℝ] EulerSobolev.Domain 4 :=
  velocityMap (Fin.cons 0 (fun i : Fin 3 => coordinate 3 i))

/-- Normal velocity map, given by `(toSpanSingleton ℝ (EuclideanSpace.single (0 : Fin 4) (1 :
ℝ))).comp scalarProject`. -/
def normalVelocityMap : Space →L[ℝ] EulerSobolev.Domain 4 :=
  (toSpanSingleton ℝ (EuclideanSpace.single (0 : Fin 4) (1 : ℝ))).comp scalarProject

theorem spatialVelocityMap_norm : ‖spatialVelocityMap‖ ≤ 3 := by
  apply opNorm_le_bound _ (by norm_num)
  intro z
  calc
    ‖spatialVelocityMap z‖ ≤ ∑ i : Fin 4, ‖spatialVelocityMap z i‖ :=
      EulerSobolevDerivativeNorm.norm_le_sum_coordinates 4 _
    _ = ∑ i : Fin 3, ‖coordinate 3 i z‖ := by
      rw [Fin.sum_univ_succ]
      simp only [spatialVelocityMap,velocityMap_apply,Fin.cons_zero,zero_apply,
        norm_zero,Fin.cons_succ,zero_add]
    _ ≤ ∑ _i : Fin 3, ‖z‖ := by
      apply Finset.sum_le_sum
      intro i _
      exact ((coordinate 3 i).le_opNorm z).trans
        ((mul_le_mul_of_nonneg_right (coordinate_norm_le 3 i) (norm_nonneg z)).trans_eq
          (one_mul _))
    _ = 3*‖z‖ := by simp

theorem normalVelocityMap_norm : ‖normalVelocityMap‖ ≤ 1 := by
  calc
    ‖normalVelocityMap‖ ≤ ‖toSpanSingleton ℝ (EuclideanSpace.single (0 : Fin 4) (1 : ℝ))‖*
        ‖scalarProject‖ := opNorm_comp_le _ _
    _ = 1 := by simp [norm_toSpanSingleton,scalarProject_norm]

theorem velocityMap_split (κ : ℝ) (m : Space) :
    velocityMap (velocityComponents κ m) =
      κ • spatialVelocityMap + normalVelocityMap.comp (normalComponentMap m) := by
  apply ContinuousLinearMap.ext
  intro v
  ext i
  refine Fin.cases ?_ (fun j => ?_) i
  · simp [velocityMap_apply,velocityComponents,spatialVelocityMap,normalVelocityMap,
      toSpanSingleton_apply]
  · simp [velocityMap_apply,velocityComponents,spatialVelocityMap,normalVelocityMap,
      toSpanSingleton_apply]

variable (P : ℝ) [Fact (0 < P)]

theorem velocityMap_L2_bound (κ : ℝ) (m : Space) (u : LiftL2 P) :
    ‖(velocityMap (velocityComponents κ m)).compLpL 2 (liftMeasure P) u‖ ≤
      3 * |κ| * ‖u‖ + ‖(normalComponentMap m).compLpL 2 (liftMeasure P) u‖ := by
  rw [velocityMap_split,add_compLpL,smul_compLpL,add_apply,smul_apply]
  have he : (normalVelocityMap.comp (normalComponentMap m)).compLpL 2 (liftMeasure P) u =
      normalVelocityMap.compLpL 2 (liftMeasure P)
        ((normalComponentMap m).compLpL 2 (liftMeasure P) u) := by
    exact congrArg (fun L => L u) (map_comp P normalVelocityMap (normalComponentMap m))
  rw [he]
  calc
    _ ≤ |κ| * ‖spatialVelocityMap.compLpL 2 (liftMeasure P) u‖ +
        ‖normalVelocityMap.compLpL 2 (liftMeasure P)
          ((normalComponentMap m).compLpL 2 (liftMeasure P) u)‖ := by
      simpa only [norm_smul,Real.norm_eq_abs] using norm_add_le
        (κ • spatialVelocityMap.compLpL 2 (liftMeasure P) u)
        (normalVelocityMap.compLpL 2 (liftMeasure P)
          ((normalComponentMap m).compLpL 2 (liftMeasure P) u))
    _ ≤ |κ| * (3*‖u‖) + 1*‖(normalComponentMap m).compLpL 2 (liftMeasure P) u‖ := by
      apply add_le_add
      · exact mul_le_mul_of_nonneg_left
          (((spatialVelocityMap.compLpL 2 (liftMeasure P)).le_opNorm u).trans
            (mul_le_mul_of_nonneg_right
              (spatialVelocityMap.norm_compLpL_le.trans spatialVelocityMap_norm) (norm_nonneg u)))
          (abs_nonneg κ)
      · exact ((normalVelocityMap.compLpL 2 (liftMeasure P)).le_opNorm _).trans
          (mul_le_mul_of_nonneg_right
            (normalVelocityMap.norm_compLpL_le.trans normalVelocityMap_norm) (norm_nonneg _))
    _ = _ := by ring

end EulerLiftedVelocitySplit

end
end

end

section

/-! Exact bounded-map naturality of every genuine Sobolev coordinate of
an actual packet field. -/

@[expose] public section

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

end
end

end

@[expose] public section

noncomputable section

namespace EulerPacketCylinderField.Field

open Set Finset EulerSmoothLimit EulerLiftedGradientSpace EulerCylinderSobolevSpace
  EulerCylinderSobolev EulerSobolevDriftNorm EulerSobolevTransport EulerFunctionalVelocity
  EulerLiftedVelocitySplit EulerPacketProfileRecursion EulerPacketWeights
  EulerSobolevGevreyOperators EulerJetProductBounds EulerH6Pressure

variable {P T : ℝ} [Fact (0 < P)] {raw : VectorField}

theorem toFieldTower_driftLevel_le (G : Field P T raw) (κ : ℝ) (m : Space)
    (s n : ℕ) (hn : n ≤ s) (t : Icc (0 : ℝ) T) :
    driftLevelNorm P n (velocityMap (velocityComponents κ m)) (G.toFieldTower.realization s t) ≤
      3 * |κ| * levelNorm P (toJet P (G.toFieldTower.realization s t)) n +
        levelNorm P (toJet P ((G.map (normalComponentMap m)).toFieldTower.realization s t)) n := by
  rw [levelNorm_eq_words,levelNorm_eq_words,mul_sum,← sum_add_distrib]
  apply sum_le_sum
  intro w _
  rw [G.toFieldTower_word_map (normalComponentMap m) s n hn w t]
  exact velocityMap_L2_bound P κ m ((toJet P (G.toFieldTower.realization s t)).word w)

theorem toFieldTower_driftBlock_le (G : Field P T raw) (κ : ℝ) (m : Space)
    (s q n : ℕ) (hn : n + q ≤ s) (t : Icc (0 : ℝ) T) :
    driftBlockNorm P q n (velocityMap (velocityComponents κ m)) (G.toFieldTower.realization s t) ≤
      3 * |κ| * blockNorm P (toJet P (G.toFieldTower.realization s t)) q n +
        blockNorm P (toJet P ((G.map (normalComponentMap m)).toFieldTower.realization s t)) q n :=
            by
  unfold driftBlockNorm blockNorm
  rw [mul_sum,← sum_add_distrib]
  apply sum_le_sum
  intro r hr
  exact G.toFieldTower_driftLevel_le κ m s (n+r) (by have := mem_range.mp hr; omega) t

theorem toFieldTower_weightedDrift_le (G : Field P T raw) (κ : ℝ) (m : Space)
    (s q N : ℕ) (hN : N + q ≤ s) (ρ : ℝ) (hρ : 0 < ρ) (t : Icc (0 : ℝ) T) :
    weightedDriftNorm P q N ρ (velocityMap (velocityComponents κ m))
        (G.toFieldTower.realization s t) ≤
      3 * |κ| * weightedNorm P q N ρ (G.toFieldTower.realization s t) +
        weightedNorm P q N ρ ((G.map (normalComponentMap m)).toFieldTower.realization s t) := by
  unfold weightedDriftNorm weightedNorm
  rw [mul_sum,← sum_add_distrib]
  apply sum_le_sum
  intro n hn
  have h := mul_le_mul_of_nonneg_left
    (G.toFieldTower_driftBlock_le κ m s q n (by have := mem_range.mp hn; omega) t)
    (weight_pos hρ n).le
  exact h.trans_eq (by ring)

/-- Separate word estimates for the full normalized vector and its actual
normal component give exactly the small transport budget needed by the
drift-preserving correction theorem. -/
theorem WordBound.toFieldTower_weightedDrift_le_two
    {G : Field P T raw} {q : ℕ} {R A₀ A₁ : ℝ}
    (hG : G.WordBound q R A₀ 0) (κ : ℝ) (m : Space)
    (hNrm : (G.map (normalComponentMap m)).WordBound q R A₁ 0)
    (hR : 0 ≤ R) (hA₀ : 0 ≤ A₀) (hA₁ : 0 ≤ A₁)
    (s N : ℕ) (hN : N + q ≤ s) (ρ : ℝ) (hρ : 0 < ρ) (hsmall : ρ * R ≤ 1 / 2)
    (t : Icc (0 : ℝ) T) :
    weightedDriftNorm P q N ρ (velocityMap (velocityComponents κ m))
      (G.toFieldTower.realization s t) ≤ 2 * (3 * |κ| * A₀ + A₁) := by
  have hz := hG.toFieldTower_weightedNorm_le_two hR hA₀ s N hN ρ hρ hsmall t
  have hn := hNrm.toFieldTower_weightedNorm_le_two hR hA₁ s N hN ρ hρ hsmall t
  exact (G.toFieldTower_weightedDrift_le κ m s q N hN ρ hρ t).trans
    ((add_le_add (mul_le_mul_of_nonneg_left hz (by positivity)) hn).trans_eq (by ring))

end EulerPacketCylinderField.Field
