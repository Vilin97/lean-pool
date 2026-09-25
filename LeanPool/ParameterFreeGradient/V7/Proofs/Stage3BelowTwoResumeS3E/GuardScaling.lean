/-
Copyright (c) 2026 Yuning Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuning Yang
-/
module


public import LeanPool.ParameterFreeGradient.V7.Proofs.Stage3BelowTwo.Dual

/-!
Observable below-two guards transported through the trial's affine normalization.
-/

@[expose] public section

namespace V7

/-! Dependency-pure R2 proof of the physical/normalized cocoercivity guard. -/

theorem belowGuardScaling : BelowGuardScalingStatement := by
  intro p M D hp hM hD d oracle c x y
  dsimp
  have hdisp : c + D • x - (c + D • y) = D • (x - y) := by
    ext i
    simp only [Pi.add_apply, Pi.smul_apply, Pi.sub_apply, smul_eq_mul]
    ring
  have hpairRight :
      pairing (oracle.gradient (c + D • y)) (D • (x - y)) =
        D * pairing (oracle.gradient (c + D • y)) (x - y) :=
    O3.Stage2RouteD.pairing_smul_right _ _ _
  have hpairLeft :
      pairing ((1 / (M * D)) • oracle.gradient (c + D • y)) (x - y) =
        (1 / (M * D)) * pairing (oracle.gradient (c + D • y)) (x - y) :=
    O3.Stage2RouteD.pairing_smul_left _ _ _
  have hBregman :
      FunctionBregman
          (fun z => (oracle.value (c + D • z) - oracle.value c) /
            (M * D ^ (2 : ℕ)))
          (fun z => (1 / (M * D)) • oracle.gradient (c + D • z)) x y =
        BregmanRemainder oracle (c + D • x) (c + D • y) /
          (M * D ^ (2 : ℕ)) := by
    unfold FunctionBregman BregmanRemainder
    rw [hdisp, hpairRight, hpairLeft]
    field_simp [hM.ne', hD.ne']
    ring
  have hgrad :
      (1 / (M * D)) • oracle.gradient (c + D • x) -
          (1 / (M * D)) • oracle.gradient (c + D • y) =
        (1 / (M * D)) •
          (oracle.gradient (c + D • x) - oracle.gradient (c + D • y)) := by
    exact (smul_sub (1 / (M * D)) _ _).symm
  have hq : 1 ≤ conjugateExponent p :=
    (O3.one_lt_conjugateExponent hp).le
  have hscale :
      lpNorm (conjugateExponent p)
          ((1 / (M * D)) •
            (oracle.gradient (c + D • x) - oracle.gradient (c + D • y))) =
        (1 / (M * D)) *
          lpNorm (conjugateExponent p)
            (oracle.gradient (c + D • x) - oracle.gradient (c + D • y)) := by
    change O3.lpNorm (O3.conjugateExponent p)
        ((1 / (M * D)) •
          (oracle.gradient (c + D • x) - oracle.gradient (c + D • y))) = _
    rw [O3.Stage2RouteC.lpNorm_smul hq]
    rw [abs_of_pos (one_div_pos.mpr (mul_pos hM hD))]
  refine ⟨?_, hBregman, ?_⟩
  · intro z
    rfl
  · rw [hBregman, hgrad, hscale]
    unfold CocoercivityGuard
    constructor <;> intro h
    · field_simp [hM.ne', hD.ne'] at h ⊢
      nlinarith
    · field_simp [hM.ne', hD.ne'] at h ⊢
      nlinarith

end V7
