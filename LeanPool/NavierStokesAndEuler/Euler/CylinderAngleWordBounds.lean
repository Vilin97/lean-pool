/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.CylinderAnglePrimitive
public import LeanPool.NavierStokesAndEuler.Euler.ParameterSobolevProductGevrey
public import LeanPool.NavierStokesAndEuler.Euler.LpCylinderOrbit

@[expose] public section

/-! Same-radius mixed-word and continuous-time estimates for the actual angular operator. -/

noncomputable section

namespace EulerCylinderAnglePrimitive

open Set MeasureTheory EulerLiftedGradientSpace EulerParameterWordGevrey EulerGevrey
  EulerLpCylinderTranslation
open scoped ContDiff

variable (P : ℝ) [Fact (0 < P)]

theorem primitive_hasDerivWithinAt (s : Set ℝ) (t : ℝ) (u : ℝ → LiftL2 P)
    (ut : LiftL2 P) (hu : HasDerivWithinAt u ut s t) :
    HasDerivWithinAt (fun r => primitive P (u r)) (primitive P ut) s t :=
  (primitive P).hasFDerivAt.comp_hasDerivWithinAt t hu

theorem primitive_mixed_translation (a : LiftTangent) (u : LiftL2 P) :
    primitive P (translate P a u) = translate P a (primitive P u) :=
  primitive_translation P _ u

variable {X ι : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [Fintype ι]

theorem primitive_block_bound (directions : ι → X) (q : ℕ)
    (f : X → LiftL2 P) (hf : ContDiff ℝ ∞ f) (n : ℕ) (x : X) :
    block directions q (fun y => primitive P (f y)) n x ≤ P*block directions q f n x :=
  (block_comp_clm_le directions q (primitive P) f hf n x).trans
    (mul_le_mul_of_nonneg_right (primitive_norm P) (block_nonneg directions q f n x))

theorem primitive_block_majorant (directions : ι → X) (q : ℕ)
    (f : X → LiftL2 P) (hf : ContDiff ℝ ∞ f) (R C : ℝ) (d : ℕ)
    (hb : ∀ n x, block directions q f n x ≤ C*majorant R d n) (n : ℕ) (x : X) :
    block directions q (fun y => primitive P (f y)) n x ≤ (P*C)*majorant R d n :=
  (primitive_block_bound P directions q f hf n x).trans
    ((mul_le_mul_of_nonneg_left (hb n x) (le_of_lt (Fact.out : 0 < P))).trans_eq
      (mul_assoc P C _).symm)

variable {K : Type*} [TopologicalSpace K] [CompactSpace K]

private local instance : NormedAddCommGroup C(K,LiftL2 P) := inferInstance
private local instance : NormedSpace ℝ C(K,LiftL2 P) := inferInstance
private local instance : NormedAddCommGroup (C(K,LiftL2 P) →L[ℝ] C(K,LiftL2 P)) := inferInstance
private local instance : NormedSpace ℝ (C(K,LiftL2 P) →L[ℝ] C(K,LiftL2 P)) := inferInstance

def pathPrimitive : C(K,LiftL2 P) →L[ℝ] C(K,LiftL2 P) :=
  (primitive P).compLeftContinuous ℝ K

omit [CompactSpace K] in
@[simp] theorem pathPrimitive_apply (u : C(K,LiftL2 P)) (t : K) :
    pathPrimitive P u t = primitive P (u t) := rfl

theorem pathPrimitive_norm : ‖pathPrimitive (K := K) P‖ ≤ P := by
  have hP : 0 ≤ P := le_of_lt (Fact.out : 0 < P)
  apply ContinuousLinearMap.opNorm_le_bound _ hP
  intro u
  apply (ContinuousMap.norm_le _ (mul_nonneg hP (norm_nonneg u))).mpr
  intro t
  exact ((primitive P).le_of_opNorm_le (primitive_norm P) (u t)).trans
    (mul_le_mul_of_nonneg_left (u.norm_coe_le_norm t) hP)

/-- The angular operation preserves the same fixed base order and radius in the true time supremum. -/
theorem pathPrimitive_block_bound (directions : ι → X) (q : ℕ)
    (f : X → C(K,LiftL2 P)) (hf : ContDiff ℝ ∞ f) (n : ℕ) (x : X) :
    block directions q (fun y => pathPrimitive P (f y)) n x ≤ P*block directions q f n x := by
  have h := block_comp_clm_le (E := C(K,LiftL2 P)) (F := C(K,LiftL2 P))
    directions q (pathPrimitive (K := K) P) f hf n x
  have hn : ‖pathPrimitive (K := K) P‖ ≤ P := pathPrimitive_norm P
  exact h.trans (mul_le_mul_of_nonneg_right hn (block_nonneg directions q f n x))

theorem pathPrimitive_block_majorant (directions : ι → X) (q : ℕ)
    (f : X → C(K,LiftL2 P)) (hf : ContDiff ℝ ∞ f) (R C : ℝ) (d : ℕ)
    (hb : ∀ n x, block directions q f n x ≤ C*majorant R d n) (n : ℕ) (x : X) :
    block directions q (fun y => pathPrimitive P (f y)) n x ≤ (P*C)*majorant R d n :=
  (pathPrimitive_block_bound P directions q f hf n x).trans
    ((mul_le_mul_of_nonneg_left (hb n x) (le_of_lt (Fact.out : 0 < P))).trans_eq
      (mul_assoc P C _).symm)

end EulerCylinderAnglePrimitive
