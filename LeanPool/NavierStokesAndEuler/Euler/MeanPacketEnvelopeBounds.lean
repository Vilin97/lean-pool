/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.MeanPacketZeroForcing
public import LeanPool.NavierStokesAndEuler.Euler.MeanPacketSobolevData
public import LeanPool.NavierStokesAndEuler.Euler.ParameterSobolevScaling

@[expose] public section

/-!
# Mean inverse estimates with an external forcing envelope

The scalar amplitude is normalized before the actual solve and restored by
proved homogeneity. Every radius condition depends only on the fixed source
data and the fixed normalized forcing scale, never on the recursive grade
or its forcing envelope. Zero envelope is treated by actual zero forcing.
-/

noncomputable section

namespace EulerMeanPacketProvider.SobolevData

open Set EulerSmoothLimit EulerMeanSolenoidal EulerMeanTimeTranslation
  EulerMeanTimeContinuousTranslation EulerParameterWordGevrey EulerGevrey
  EulerPacketProfileRecursion
open scoped ContDiff

variable {D : Data} {ι : Type*} [Fintype ι] {q : ℕ} {R : ℝ}

/-- The fixed-Hq mean inverse preserves one external radius for arbitrary
nonnegative scalar forcing envelopes. -/
theorem envelope_bounds (E : SobolevData D ι q R)
    (directions : ι → Space) (hd : ∀ i, ‖directions i‖ ≤ 1)
    {raw : VectorField} (G : Forcing D raw) (d : ℕ) (A : ℝ) (hA : 0 ≤ A)
    (hfb : ∀ n a, block directions q (fun b : Space => timeTranslation D.T b G.lp) n a ≤
      A*(E.Cf*majorant R d n))
    (hfCb : ∀ n a, block directions q (fun b : Space => pathTranslation D.T b G.path) n a ≤
      A*(E.Cf*majorant R d n)) :
    (∀ n a, block directions q (fun b : Space => pathTranslation D.T b G.velocityPath) n a ≤
      A*(E.velocityAmplitude*majorant R (d+2) n)) ∧
    (∀ n a, block directions q (fun b : Space => pathTranslation D.T b G.derivativePath) n a ≤
      A*(E.derivativeAmplitude*majorant R (d+3) n)) ∧
    (∀ n a, block directions q (fun b : Space => pathTranslation D.T b G.pressureForcePath) n a ≤
      A*(E.pressureAmplitude*majorant R (d+3) n)) := by
  rcases eq_or_lt_of_le hA with hzero | hpos
  · subst A
    have hv := value_zero_of_block_zero_bound directions q
      (fun b : Space => pathTranslation D.T b G.path) 0 (by simpa only [zero_mul] using hfCb 0 0)
    have he : pathTranslation D.T 0 G.path = G.path := by
      apply ContinuousMap.ext
      intro t
      exact translation_zero (G.path t)
    have hp : G.path = 0 := he.symm.trans hv
    have hzero := G.paths_zero_of_path_zero hp
    simp only [hzero.1, hzero.2.1, hzero.2.2, map_zero, block_zero_function, zero_mul,
      le_refl, implies_true, and_self]
  · let H : Forcing D (A⁻¹ • raw) := G.smul A⁻¹
    have hscale : ∀ (t : Icc (0 : ℝ) D.T) x θ,
        (A⁻¹ • raw) (t,(x,θ)) = A⁻¹ • raw (t,(x,θ)) := fun _ _ _ => rfl
    have hLp : (fun b : Space => timeTranslation D.T b H.lp) =
        fun b : Space => A⁻¹ • timeTranslation D.T b G.lp := by
      funext b
      exact (congrArg (timeTranslation D.T b) (Forcing.lp_smul G H A⁻¹ hscale)).trans
        ((timeTranslation D.T b).map_smul A⁻¹ G.lp)
    have hPath : (fun b : Space => pathTranslation D.T b H.path) =
        fun b : Space => A⁻¹ • pathTranslation D.T b G.path := by
      funext b
      exact (congrArg (pathTranslation D.T b) (Forcing.path_smul G H A⁻¹ hscale)).trans
        ((pathTranslation D.T b).map_smul A⁻¹ G.path)
    have hn : ∀ n a, block directions q (fun b : Space => timeTranslation D.T b H.lp) n a ≤
        E.Cf*majorant R d n := by
      intro n a
      refine (congrArg (fun g : Space → EulerTimeLp.TimeLp D.T L2 =>
        block directions q g n a) hLp).trans_le ?_
      exact block_normalize_bound directions q _ G.lp_orbit A hpos R E.Cf d n a (hfb n a)
    have hnC : ∀ n a, block directions q (fun b : Space => pathTranslation D.T b H.path) n a ≤
        E.Cf*majorant R d n := by
      intro n a
      refine (congrArg (fun g : Space → C(Icc (0 : ℝ) D.T,L2) =>
        block directions q g n a) hPath).trans_le ?_
      exact block_normalize_bound directions q _ G.path_orbit A hpos R E.Cf d n a (hfCb n a)
    have hbounds := E.normalized_bounds directions hd H d hn hnC
    have hback : ∀ (t : Icc (0 : ℝ) D.T) x θ,
        raw (t,(x,θ)) = A • (A⁻¹ • raw) (t,(x,θ)) := by
      intro t x θ
      simp only [Pi.smul_apply, smul_smul, mul_inv_cancel₀ hpos.ne', one_smul]
    have hVB := Forcing.velocityPath_smul H G A hback
    have hVD := Forcing.derivativePath_smul H G A hback
    have hVP := Forcing.pressureForcePath_smul H G A hback
    refine ⟨?_, ?_, ?_⟩
    · intro n a
      apply block_restore_bound directions q _ _ H.velocityPath_orbit A hpos.le
        (fun b => (congrArg (pathTranslation D.T b) hVB).trans
          ((pathTranslation D.T b).map_smul A H.velocityPath)) R E.velocityAmplitude (d+2) n a
            (hbounds.1 n a)
    · intro n a
      apply block_restore_bound directions q _ _ H.derivativePath_orbit A hpos.le
        (fun b => (congrArg (pathTranslation D.T b) hVD).trans
          ((pathTranslation D.T b).map_smul A H.derivativePath)) R E.derivativeAmplitude (d+3) n a
            (hbounds.2.1 n a)
    · intro n a
      apply block_restore_bound directions q _ _ H.pressureForcePath_orbit A hpos.le
        (fun b => (congrArg (pathTranslation D.T b) hVP).trans
          ((pathTranslation D.T b).map_smul A H.pressureForcePath)) R E.pressureAmplitude (d+3) n a
            (hbounds.2.2 n a)

end EulerMeanPacketProvider.SobolevData
