/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.MeanPacketCylinderFields
public import LeanPool.NavierStokesAndEuler.Euler.CylinderSpatialMeanPath
public import LeanPool.NavierStokesAndEuler.Euler.ParameterWordRestriction
public import LeanPool.NavierStokesAndEuler.Euler.CylinderActionWords
public import LeanPool.NavierStokesAndEuler.Euler.PacketCylinderFieldBounds

@[expose] public section

/-!
Exact parameter restriction transfers the ordinary mean estimates to the
four-letter cylinder word alphabet.  The zero angular direction is retained,
so neither the external radius nor the fixed Sobolev order changes.
-/

noncomputable section

namespace EulerMeanPacketProvider

open Set Real MeasureTheory ContinuousLinearMap EulerSmoothLimit EulerMeanSolenoidal
  EulerLiftedGradientSpace EulerLpCylinderTranslation EulerCylinderSpatialEmbedding
  EulerCylinderSpatialMean EulerMeanTimeContinuousTranslation EulerCylinderSobolev
  EulerParameterWordGevrey EulerGevrey EulerPacketCylinderField EulerPacketProfileRecursion
open scoped ContDiff

def spatialDirection (i : Fin 4) : Space := (standardDirection i).1

theorem spatialDirection_norm (i : Fin 4) : ‖spatialDirection i‖ ≤ 1 := by
  cases i using Fin.cases <;> simp [spatialDirection]

variable (P T : ℝ) [Fact (0 < P)]

private local instance : NormedAddCommGroup C(Icc (0 : ℝ) T,L2) := inferInstance
private local instance : NormedSpace ℝ C(Icc (0 : ℝ) T,L2) := inferInstance
private local instance : NormedAddCommGroup C(Icc (0 : ℝ) T,LiftL2 P) := inferInstance
private local instance : NormedSpace ℝ C(Icc (0 : ℝ) T,LiftL2 P) := inferInstance

theorem spatialEmbeddingPath_norm : ‖spatialEmbeddingPath P T‖ ≤ sqrt P := by
  apply opNorm_le_bound _ (sqrt_nonneg P)
  intro p
  apply (ContinuousMap.norm_le _ (mul_nonneg (sqrt_nonneg P) (norm_nonneg p))).mpr
  intro t
  exact ((embedding (V := Space) P).le_of_opNorm_le (embedding_norm P) (p t)).trans
    (mul_le_mul_of_nonneg_left (p.norm_coe_le_norm t) (sqrt_nonneg P))

theorem pathMean_spatialEmbeddingPath (p : C(Icc (0 : ℝ) T,L2)) :
    pathMean P (spatialEmbeddingPath P T p) = p := by
  apply ContinuousMap.ext
  intro t
  exact mean_embedding P (p t)

theorem spatialEmbeddingPath_block_le (p : C(Icc (0 : ℝ) T,L2))
    (hp : ContDiff ℝ ∞ (fun a : Space => pathTranslation T a p))
    (q n : ℕ) (a : LiftTangent) :
    block standardDirection q
      (fun b : LiftTangent => pathTranslate P b (spatialEmbeddingPath P T p)) n a ≤
      sqrt P*block spatialDirection q (fun b : Space => pathTranslation T b p) n a.1 := by
  let f := fun b : Space => pathTranslation T b p
  let fstMap : LiftTangent →L[ℝ] Space := fst ℝ Space ℝ
  have he : (fun b : LiftTangent => pathTranslate P b (spatialEmbeddingPath P T p)) =
      (spatialEmbeddingPath P T) ∘ (f ∘ fstMap) :=
    funext (fun b => spatialEmbeddingPath_translation P T p b)
  refine (congrArg (fun g : LiftTangent → C(Icc (0 : ℝ) T,LiftL2 P) =>
    block standardDirection q g n a) he).trans_le ?_
  have hh := block_comp_clm_le standardDirection q (spatialEmbeddingPath P T)
    (f ∘ fstMap) (hp.comp fstMap.contDiff) n a
  have hh := hh.trans_eq (congrArg (fun r : ℝ => ‖spatialEmbeddingPath P T‖*r)
    (block_comp_right standardDirection fstMap q f hp n a))
  exact hh.trans (mul_le_mul_of_nonneg_right (spatialEmbeddingPath_norm P T)
    (block_nonneg spatialDirection q f n a.1))

theorem ordinaryPath_block_le (p : C(Icc (0 : ℝ) T,L2))
    (hp : ContDiff ℝ ∞ (fun a : Space => pathTranslation T a p))
    (q n : ℕ) (a : Space) :
    block spatialDirection q (fun b : Space => pathTranslation T b p) n a ≤
      (P⁻¹*sqrt P)*block standardDirection q
        (fun b : LiftTangent => pathTranslate P b (spatialEmbeddingPath P T p)) n (a,0) := by
  let f := fun b : Space => pathTranslation T b p
  let fstMap : LiftTangent →L[ℝ] Space := fst ℝ Space ℝ
  let g := fun b : LiftTangent => pathTranslate P b (spatialEmbeddingPath P T p)
  have he : (fun b : LiftTangent => pathMean P (g b)) = f ∘ fstMap := by
    funext b
    change pathMean P (pathTranslate P b (spatialEmbeddingPath P T p)) = f (fstMap b)
    rw [spatialEmbeddingPath_translation, pathMean_spatialEmbeddingPath]
    rfl
  have hh := pathMean_block_bound P standardDirection q g (spatialEmbeddingPath_orbit P T p hp) n
    (a,0)
  rw [he, block_comp_right standardDirection fstMap q f hp] at hh
  exact hh

theorem ordinaryPath_majorant (p : C(Icc (0 : ℝ) T,L2))
    (hp : ContDiff ℝ ∞ (fun a : Space => pathTranslation T a p))
    (q : ℕ) (R A : ℝ) (d : ℕ)
    (hb : ∀ n, block standardDirection q
      (fun b : LiftTangent => pathTranslate P b (spatialEmbeddingPath P T p)) n 0 ≤ A*majorant R d
        n)
    (n : ℕ) (a : Space) :
    block spatialDirection q (fun b : Space => pathTranslation T b p) n a ≤
      ((P⁻¹*sqrt P)*A)*majorant R d n := by
  have hh := ordinaryPath_block_le P T p hp q n a
  rw [path_block_constant P standardDirection q (spatialEmbeddingPath P T p)
    (spatialEmbeddingPath_orbit P T p hp)] at hh
  exact hh.trans ((mul_le_mul_of_nonneg_left (hb n)
    (mul_nonneg (inv_nonneg.mpr (le_of_lt (Fact.out : 0 < P))) (sqrt_nonneg P))).trans_eq (by ring))

theorem spatialEmbeddingPath_majorant (p : C(Icc (0 : ℝ) T,L2))
    (hp : ContDiff ℝ ∞ (fun a : Space => pathTranslation T a p))
    (q : ℕ) (R A : ℝ) (d : ℕ)
    (hb : ∀ n a, block spatialDirection q (fun b : Space => pathTranslation T b p) n a ≤
      A*majorant R d n) (n : ℕ) :
    block standardDirection q
      (fun b : LiftTangent => pathTranslate P b (spatialEmbeddingPath P T p)) n 0 ≤
      (sqrt P*A)*majorant R d n := by
  exact (spatialEmbeddingPath_block_le P T p hp q n 0).trans
    ((mul_le_mul_of_nonneg_left (hb n 0) (sqrt_nonneg P)).trans_eq (by ring))

theorem embedding_mean_norm_product : sqrt P*(P⁻¹*sqrt P) = 1 := by
  have hP := (Fact.out : 0 < P)
  calc
    _ = P⁻¹*(sqrt P)^2 := by ring
    _ = 1 := by rw [sq_sqrt hP.le, inv_mul_cancel₀ hP.ne']

namespace Forcing

variable {T} {D : Data} {raw : VectorField} (G : Forcing D raw)

theorem ordinary_word_bound {q : ℕ} {R A : ℝ} {d : ℕ}
    (hb : (G.toCylinderField P).WordBound q R A d) (n : ℕ) (a : Space) :
    block spatialDirection q (fun b : Space => pathTranslation D.T b G.path) n a ≤
      ((P⁻¹*sqrt P)*A)*majorant R d n :=
  ordinaryPath_majorant P D.T G.path G.path_orbit q R A d hb n a

theorem toCylinderField_word_bound {q : ℕ} {R A : ℝ} {d : ℕ}
    (hb : ∀ n a, block spatialDirection q (fun b : Space => pathTranslation D.T b G.path) n a ≤
      A*majorant R d n) : (G.toCylinderField P).WordBound q R (sqrt P*A) d :=
  spatialEmbeddingPath_majorant P D.T G.path G.path_orbit q R A d hb

end Forcing
end EulerMeanPacketProvider
