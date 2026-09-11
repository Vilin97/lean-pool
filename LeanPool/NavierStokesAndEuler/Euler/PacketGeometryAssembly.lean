/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import LeanPool.NavierStokesAndEuler.Euler.PacketPropagationTime
public import LeanPool.NavierStokesAndEuler.Euler.PacketGeometryData
import LeanPool.NavierStokesAndEuler.Euler.PacketActualFrameEstimates
import LeanPool.NavierStokesAndEuler.Euler.PacketBeforeTargetSize
import LeanPool.NavierStokesAndEuler.Euler.PacketGeometryGuards
import LeanPool.NavierStokesAndEuler.Euler.PacketHorizonSize
import LeanPool.NavierStokesAndEuler.Euler.PacketPhysicalCompression
import LeanPool.NavierStokesAndEuler.Euler.PacketTargetAmplification
import Mathlib.Algebra.Order.Star.Real
public import LeanPool.NavierStokesAndEuler.Euler.PacketScaledVelocity
import LeanPool.NavierStokesAndEuler.Euler.PacketPhysicalNormBounds
import LeanPool.NavierStokesAndEuler.Euler.Foundations.PacketFrameQuantitative
import LeanPool.NavierStokesAndEuler.Euler.PacketPhysicalFrameRenewal
public import LeanPool.NavierStokesAndEuler.Euler.Foundations.PacketRay
public import LeanPool.NavierStokesAndEuler.Euler.Foundations.PacketBridge
import LeanPool.NavierStokesAndEuler.Euler.Foundations.PacketExistence
import LeanPool.NavierStokesAndEuler.Euler.Foundations.PacketFrameStability
public import LeanPool.NavierStokesAndEuler.Euler.PacketPhysicalCoefficients
import LeanPool.NavierStokesAndEuler.Euler.Foundations.PacketGrowth
import LeanPool.NavierStokesAndEuler.Euler.PacketScaledVelocitySystem
import LeanPool.NavierStokesAndEuler.Euler.PacketWithinRay
public import LeanPool.NavierStokesAndEuler.Euler.PacketNeighborControlled
public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.Topology.Algebra.Module.ModuleTopology
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import LeanPool.NavierStokesAndEuler.Euler.ClosedIntervalDerivativeExtension
import LeanPool.NavierStokesAndEuler.Euler.Foundations.PacketPerturbation
public import LeanPool.NavierStokesAndEuler.Euler.PacketScaledRay
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.Calculus.MeanValue

/-!
One geometric stage: actual neighboring physical fields, the constructed
common scalar reference, and the source amplitude choice.  All hypotheses
are the literal physical data and explicit scale guards in the data record.
-/

section

/-! Tangency is preserved by the actual ray and projected velocity ODEs. -/

@[expose] public section

noncomputable section

namespace EulerPacketMovingFrame

open Set EulerSmoothLimit InnerProductSpace ContinuousLinearMap

theorem tangentPairing_hasDerivWithinAt (M : Space →L[ℝ] Space)
    {r w : ℝ → Space} {t : ℝ} {S : Set ℝ}
    (hr : HasDerivWithinAt r (-M.adjoint (r t)) S t)
    (hw : HasDerivWithinAt w (-M (w t) + (2 * ⟪r t, M (w t)⟫_ℝ / ‖r t‖ ^ 2) • r t) S t)
    (hr0 : r t ≠ 0) : HasDerivWithinAt (fun s => ⟪r s,w s⟫_ℝ) 0 S t := by
  apply (hr.inner ℝ hw).congr_deriv
  simp only [inner_add_right, inner_neg_right, real_inner_smul_right,
    real_inner_self_eq_norm_sq, inner_neg_left, adjoint_inner_left]
  have hn := pow_ne_zero 2 (norm_ne_zero_iff.mpr hr0)
  field_simp
  ring

theorem rescaled_tangentPairing_zero (M : ℝ → Space →L[ℝ] Space)
    {r w : ℝ → Space} {t₀ a ε T : ℝ} {S : Set ℝ}
    (hmap : MapsTo (physicalTime t₀ a ε) (Icc 0 T) S)
    (hr : ∀ t ∈ S, HasDerivWithinAt r (-(M t).adjoint (r t)) S t)
    (hw : ∀ t ∈ S, HasDerivWithinAt w (-(M t) (w t) +
      (2 * ⟪r t, (M t) (w t)⟫_ℝ / ‖r t‖ ^ 2) • r t) S t)
    (hr0 : ∀ τ ∈ Icc 0 T, r (physicalTime t₀ a ε τ) ≠ 0)
    (h0 : ⟪r t₀, w t₀⟫_ℝ = 0) :
    ∀ τ ∈ Icc 0 T, ⟪r (physicalTime t₀ a ε τ),w (physicalTime t₀ a ε τ)⟫_ℝ = 0 := by
  have hderiv : ∀ τ ∈ Icc 0 T, HasDerivWithinAt
      (fun s => ⟪r (physicalTime t₀ a ε s),w (physicalTime t₀ a ε s)⟫_ℝ) 0 (Icc 0 T) τ := by
    intro τ hτ
    have ht := hmap hτ
    simpa only [zero_mul, Function.comp_def] using
      (tangentPairing_hasDerivWithinAt (M (physicalTime t₀ a ε τ)) (hr _ ht)
        (hw _ ht) (hr0 τ hτ)).comp τ
          (physicalTime_hasDerivAt t₀ a ε τ).hasDerivWithinAt hmap
  have hh := norm_image_sub_le_of_norm_deriv_le_segment' hderiv
    (fun _ _ => (by simp : ‖(0:ℝ)‖ ≤ 0))
  intro τ hτ
  have h := hh τ hτ
  simpa only [physicalTime, mul_zero, add_zero, h0, sub_zero, zero_mul,
    norm_le_zero_iff] using h

end EulerPacketMovingFrame

end
end

end

section

/-! Continuity of the actual rescaled moving-frame matrices. -/

@[expose] public section

noncomputable section

namespace EulerPacketMovingFrame

open Set EulerSmoothLimit EulerPacketNormalizedPrimary EulerPacketRay InnerProductSpace

theorem rescaledFrame_continuousOn (B D : ℝ → Space →L[ℝ] Space)
    {m v : ℝ → Space} {S U : Set ℝ} {t₀ a ε : ℝ}
    (hmap : MapsTo (physicalTime t₀ a ε) U S)
    (hDc : ContinuousOn D S)
    (hm : ∀ t ∈ S, HasDerivWithinAt m (-(B t).adjoint (m t)) S t)
    (hv : ∀ t ∈ S, HasDerivWithinAt v (-(B t) (v t) +
      (2 * ⟪m t, (B t) (v t)⟫_ℝ / ‖m t‖ ^ 2) • m t) S t)
    (hm0 : ∀ t ∈ S, m t ≠ 0) (hv0 : ∀ t ∈ S, v t ≠ 0)
    (hmv : ∀ t ∈ S, ⟪m t, v t⟫_ℝ = 0) :
    ∀ i j, ContinuousOn (fun τ => rescaledFrame D m v t₀ a ε τ i j) U := by
  have ht : ContinuousOn (physicalTime t₀ a ε) U := by unfold physicalTime; fun_prop
  have hf : ∀ i, ContinuousOn (fun t => normalizedFrame m v t i) S := by
    intro i t hts
    exact (normalizedFrame_hasDerivWithinAt (B t) (hm t hts) (hv t hts)
      (hm0 t hts) (hv0 t hts) (hmv t hts) i).continuousWithinAt
  intro i j
  exact ((hf i).comp ht hmap).inner ((hDc.comp ht hmap).clm_apply ((hf j).comp ht hmap))

theorem frameSkew_continuousOn {B : ℝ → Fin 3 → Fin 3 → ℝ} {U : Set ℝ}
    (hB : ∀ i j, ContinuousOn (fun τ => B τ i j) U) :
    ∀ i j, ContinuousOn (fun τ => frameSkew (B τ) i j) U := by
  intro i j
  unfold frameSkew
  split_ifs <;> fun_prop

theorem scaledRayEntry_continuousOn {M S : ℝ → Fin 3 → Fin 3 → ℝ} {U : Set ℝ}
    (a ε : ℝ) (hM : ∀ i j, ContinuousOn (fun τ => M τ i j) U)
    (hS : ∀ i j, ContinuousOn (fun τ => S τ i j) U) :
    ∀ i j, ContinuousOn (fun τ => scaledRayEntry a ε (M τ) (S τ) i j) U := by
  intro i j
  unfold scaledRayEntry
  fun_prop

theorem scaledVelocityEntry_continuousOn {M : ℝ → Fin 3 → Fin 3 → ℝ} {U : Set ℝ}
    (a ε : ℝ) (hM : ∀ i j, ContinuousOn (fun τ => M τ i j) U) :
    ∀ i j, ContinuousOn (fun τ => scaledVelocityEntry a ε (M τ) i j) U := by
  intro i j
  unfold scaledVelocityEntry
  fun_prop

end EulerPacketMovingFrame

end
end

end

section

/-!
Uniform neighboring amplification and before-target size control from the
actual physical equations.  The scalar reference is shared by uniqueness,
so its choice is independent of the physical label.
-/

section

/-!
Actual neighboring physical primaries satisfy the amplification estimate
with their genuine initial discrepancy.  The source moving frame is the
center frame.  Its neighboring matrix perturbation is part of the actual
parent error; all scaled coefficient and ray bounds are derived here.
-/

@[expose] public section

noncomputable section

namespace EulerPacketMovingFrame

open Set EulerSmoothLimit EulerPacketNormalizedPrimary EulerPacketRay
    InnerProductSpace ContinuousLinearMap

theorem physical_neighbor_stage_references
    {B B₁ M E : ℝ → Space →L[ℝ] Space} {m v r w : ℝ → Space}
    {c s₀ t₀ a ε σ Θ T G d lam : ℝ} {S : Set ℝ}
    (hσ : 0 < σ) (hσsmall : σ ≤ 1 / 4) (hT0 : 0 < T) (hT : T ≤ Θ)
    (ha : 1 / 2 ≤ a) (hε : 0 < ε) (hΘ : 1 ≤ Θ) (hG : 1 ≤ G) (hd : 0 ≤ d)
    (hs₀ : s₀ ≠ 0) (hlam : 0 ≤ lam)
    (hsmall : 1000000 * neighborStabilityConstant * (16 * (ε * Θ * (4 * G) ^ 2 + d)) * Θ ^ 40 ≤ 1)
    (hmap : MapsTo (physicalTime t₀ a ε) (Icc 0 Θ) S)
    (hMc : ContinuousOn M S)
    (hBd : ∀ t ∈ S, HasDerivWithinAt B (B₁ t) S t)
    (hmd : ∀ t ∈ S, HasDerivWithinAt m (-(B t).adjoint (m t)) S t)
    (hvd : ∀ t ∈ S, HasDerivWithinAt v (-(B t) (v t) +
      (2 * ⟪m t, (B t) (v t)⟫_ℝ / ‖m t‖ ^ 2) • m t) S t)
    (hrd : ∀ t ∈ S, HasDerivWithinAt r (-(M t).adjoint (r t)) S t)
    (hwd : ∀ t ∈ S, HasDerivWithinAt w (-(M t) (w t) +
      (2 * ⟪r t, (M t) (w t)⟫_ℝ / ‖r t‖ ^ 2) • r t) S t)
    (hm0 : ∀ t ∈ S, m t ≠ 0) (hv0 : ∀ t ∈ S, v t ≠ 0)
    (hmv : ∀ t ∈ S, ⟪m t, v t⟫_ℝ = 0) (hrw0 : ⟪r t₀, w t₀⟫_ℝ = 0)
    (hB : ∀ t ∈ S, ‖B t‖ ≤ G) (hB₁ : ∀ t ∈ S, ‖B₁ t‖ ≤ G ^ 2)
    (hE : ∀ t ∈ S, ‖E t‖ ≤ d)
    (hparent : ∀ t ∈ S, M t = B t +
      primaryShear c m v t • rankOne ℝ (unit (v t)) (unit (m t)) + E t)
    (hb0 : rescaledFrame B m v t₀ a ε 0 0 1 = a)
    (hk0 : rescaledFrame B m v t₀ a ε 0 2 1 = a * σ ^ 2)
    (hh0 : rescaledShear c m v t₀ a ε 0 = a / ε ^ 2)
    (hrInitial : norm3 (scaledRay m v r s₀ t₀ a ε 0 0) (scaledRay m v r s₀ t₀ a ε 0 1)
      (scaledRay m v r s₀ t₀ a ε 0 2 - 1) ≤ 16 * (ε * Θ * (4 * G) ^ 2 + d))
    (hvelocityInitial : |scaledVelocity m v w t₀ a ε 0 1 - 1| +
      |scaledVelocity m v w t₀ a ε 0 0 + lam| ≤ 16 * (ε * Θ * (4 * G) ^ 2 + d)) :
    let e := 16*(ε*Θ*(4*G)^2+d)
    let U := fun τ => scaledVelocity m v w t₀ a ε τ 0
    let V := fun τ => scaledVelocity m v w t₀ a ε τ 1
    (∀ τ ∈ Icc 0 T,
      norm3 (scaledRay m v r s₀ t₀ a ε τ 0-σ^2*τ^2)
        (scaledRay m v r s₀ t₀ a ε τ 1+2*σ^2*τ)
        (scaledRay m v r s₀ t₀ a ε τ 2-1) ≤ 800*e*Θ^5 ∧
      1/2 ≤ scaledRay m v r s₀ t₀ a ε τ 2 ∧
      ⟪r (physicalTime t₀ a ε τ), w (physicalTime t₀ a ε τ)⟫_ℝ = 0) ∧
    ∃ F F₁ Z Z₁ : ℝ → ℝ,
      F 0 = 1 ∧ F₁ 0 = 0 ∧ Z 0 = 1 ∧ Z₁ 0 = lam ∧
      (∀ t, HasDerivAt F (F₁ t) t) ∧ (∀ t, HasDerivAt Z (Z₁ t) t) ∧
      (∀ t, HasDerivAt (fun s => (1+(σ^2*s^2)^2)*F₁ s)
        (2*(1-σ^2*(σ^2*t^2))*F t) t) ∧
      (∀ t, HasDerivAt (fun s => (1+(σ^2*s^2)^2)*Z₁ s)
        (2*(1-σ^2*(σ^2*t^2))*Z t) t) ∧
      (∀ t ∈ Icc 0 T, |V t-Z t|+|U t+Z₁ t| ≤ 400000000*e*Θ^29*(1+lam)*F t) ∧
      (∀ t ∈ Icc 1 T, 0 < V t ∧ |V t/Z t-1| ≤ neighborStabilityConstant*e*Θ^29 ∧
        |U t/V t+Z₁ t/Z t| ≤ 10*(neighborStabilityConstant*e*Θ^29)) := by
  let e := 16*(ε*Θ*(4*G)^2+d)
  let Rp := scaledRay m v r s₀ t₀ a ε
  let Vp := scaledVelocity m v w t₀ a ε
  let Mf := rescaledFrame M m v t₀ a ε
  let Bf := rescaledFrame B m v t₀ a ε
  let Rmat : ℝ → Fin 3 → Fin 3 → ℝ := fun τ => scaledRayEntry a ε (Mf τ) (frameSkew (Bf τ))
  let Amat : ℝ → Fin 3 → Fin 3 → ℝ := fun τ => scaledVelocityEntry a ε (Mf τ)
  let Cmat : ℝ → Fin 3 → Fin 3 → ℝ := fun τ =>
    scaledVelocityEntry a ε (fun i j => Mf τ i j+frameSkew (Bf τ) i j)
  have he : 0 ≤ e := by dsimp [e]; positivity
  have hΘ0 : 0 ≤ Θ := by linarith
  have hK : 1 ≤ neighborStabilityConstant := le_trans (by norm_num) neighborStabilityConstant_ge
  have hbase : 1000000*e*Θ^40 ≤ 1 := by
    have hnonneg := mul_nonneg (sub_nonneg.mpr hK) (mul_nonneg he (pow_nonneg hΘ0 40))
    change 1000000*neighborStabilityConstant*e*Θ^40 ≤ 1 at hsmall
    nlinarith only [hsmall, hnonneg]
  have heΘ : e ≤ e*Θ^40 := by
    simpa only [mul_one] using mul_le_mul_of_nonneg_left (one_le_pow₀ hΘ : 1 ≤ Θ^40) he
  have heSmall : e ≤ 1 := by nlinarith only [hbase, heΘ, he]
  have hpow : e*Θ^5 ≤ e*Θ^40 :=
    mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hΘ (by decide : 5 ≤ 40)) he
  have hsmallRay : 400*(4*e)*Θ^5 ≤ 1 := by
    nlinarith only [hbase, hpow, mul_nonneg he (pow_nonneg hΘ0 5)]
  have ha0 : 0 < a := by linarith
  have hσsq : σ^2 ≤ 1 := by nlinarith only [hσ, hσsmall]
  have herr := physical_matrix_errors ha hε hΘ hG hd heSmall hmap hBd hmd hvd hm0 hv0 hmv
    hB hB₁ hE hparent hb0 hk0 hh0
  have hsub : Icc (0:ℝ) T ⊆ Icc 0 Θ := fun _ ht => ⟨ht.1, ht.2.trans hT⟩
  have hmapT : MapsTo (physicalTime t₀ a ε) (Icc 0 T) S := fun _ ht => hmap (hsub ht)
  have hMf : ∀ i j, ContinuousOn (fun τ => Mf τ i j) (Icc 0 T) :=
    rescaledFrame_continuousOn B M hmapT hMc hmd hvd hm0 hv0 hmv
  have hBf : ∀ i j, ContinuousOn (fun τ => Bf τ i j) (Icc 0 T) :=
    rescaledFrame_continuousOn B B hmapT (fun t ht => (hBd t ht).continuousWithinAt)
      hmd hvd hm0 hv0 hmv
  have hSf := frameSkew_continuousOn hBf
  have hRmc : ∀ i j, ContinuousOn (fun τ => Rmat τ i j) (Icc 0 T) :=
    scaledRayEntry_continuousOn a ε hMf hSf
  have hAmc : ∀ i j, ContinuousOn (fun τ => Amat τ i j) (Icc 0 T) :=
    scaledVelocityEntry_continuousOn a ε hMf
  have hCmc : ∀ i j, ContinuousOn (fun τ => Cmat τ i j) (Icc 0 T) :=
    scaledVelocityEntry_continuousOn a ε (fun i j => (hMf i j).add (hSf i j))
  have hRode : ∀ i τ, τ ∈ Icc 0 T → HasDerivWithinAt (fun s => Rp s i)
      (∑ j : Fin 3, Rmat τ i j*Rp τ j) (Icc 0 T) τ := by
    intro i τ hτ
    have ht := hmapT hτ
    exact scaledRay_hasDerivWithinAt (B (physicalTime t₀ a ε τ)) (M (physicalTime t₀ a ε τ))
      (ne_of_gt ha0) (ne_of_gt hε) hs₀ hmapT (hmd _ ht) (hvd _ ht) (hrd _ ht)
      (hm0 _ ht) (hv0 _ ht) (hmv _ ht) i
  have hP : ∀ τ ∈ Icc 0 T, HasDerivWithinAt (fun s => Rp s 0)
      (Rmat τ 0 0*Rp τ 0+Rmat τ 0 1*Rp τ 1+Rmat τ 0 2*Rp τ 2) (Icc 0 T) τ := by
    intro τ hτ
    simpa only [Fin.sum_univ_three] using hRode 0 τ hτ
  have hQ : ∀ τ ∈ Icc 0 T, HasDerivWithinAt (fun s => Rp s 1)
      (Rmat τ 1 0*Rp τ 0+Rmat τ 1 1*Rp τ 1+Rmat τ 1 2*Rp τ 2) (Icc 0 T) τ := by
    intro τ hτ
    simpa only [Fin.sum_univ_three] using hRode 1 τ hτ
  have hN : ∀ τ ∈ Icc 0 T, HasDerivWithinAt (fun s => Rp s 2)
      (Rmat τ 2 0*Rp τ 0+Rmat τ 2 1*Rp τ 1+Rmat τ 2 2*Rp τ 2) (Icc 0 T) τ := by
    intro τ hτ
    simpa only [Fin.sum_univ_three] using hRode 2 τ hτ
  have hRclose : ∀ τ ∈ Icc 0 T, ∀ i j, |Rmat τ i j-idealRayEntry (σ^2) i j| ≤ 4*e :=
    fun τ hτ => (herr.2 τ (hsub hτ)).1
  have hnear := ray_closeness_within (sq_nonneg σ) hσsq hΘ hT0 hT
    (mul_nonneg (by norm_num : (0:ℝ) ≤ 4) he) hsmallRay hRmc hP hQ hN hRclose
    (hrInitial.trans (show e ≤ 4*e by linarith))
  have hrnonzero : ∀ τ ∈ Icc 0 T, r (physicalTime t₀ a ε τ) ≠ 0 := by
    intro τ hτ hzero
    have hNne : Rp τ 2 ≠ 0 := by linarith only [(hnear τ hτ).2]
    apply hNne
    simp only [Rp, scaledRay, movingRay, hzero, inner_zero_right, zero_div]
  have hpair := rescaled_tangentPairing_zero M hmapT hrd hwd hrnonzero hrw0
  have hUV : ∀ τ ∈ Icc 0 T,
      HasDerivWithinAt (fun s => Vp s 0)
        (velocityFirstRhs (Amat τ) (Cmat τ) ε (Rp τ 0) (Rp τ 1) (Rp τ 2) (Vp τ 0) (Vp τ 1)) (Icc 0
            T) τ ∧
      HasDerivWithinAt (fun s => Vp s 1)
        (velocitySecondRhs (Amat τ) (Cmat τ) ε (Rp τ 0) (Rp τ 1) (Rp τ 2) (Vp τ 0) (Vp τ 1)) (Icc 0
            T) τ := by
    intro τ hτ
    have ht := hmapT hτ
    have hNne : Rp τ 2 ≠ 0 := by linarith only [(hnear τ hτ).2]
    exact scaledVelocity_firstTwo_hasDerivWithinAt (B (physicalTime t₀ a ε τ))
      (M (physicalTime t₀ a ε τ)) (ne_of_gt ha0) (ne_of_gt hε) hs₀ hmapT
      (hmd _ ht) (hvd _ ht) (hwd _ ht) (hm0 _ ht) (hv0 _ ht) (hmv _ ht)
      (hrnonzero τ hτ) (hpair τ hτ) hNne
  refine ⟨?_, ?_⟩
  · intro τ hτ
    refine ⟨?_, (hnear τ hτ).2, hpair τ hτ⟩
    nlinarith only [(hnear τ hτ).1]
  · exact controlled_neighbor_stage_references_within hσ hσsmall hΘ hT0 hT he hε.le herr.1 hlam
      hsmall
      hRmc hAmc hCmc hP hQ hN (fun τ hτ => (hUV τ hτ).1) (fun τ hτ => (hUV τ hτ).2)
      hRclose (fun τ hτ => (herr.2 τ (hsub hτ)).2.1) (fun τ hτ => (herr.2 τ (hsub hτ)).2.2)
      hrInitial hvelocityInitial

end EulerPacketMovingFrame

end
end

end

section

/-! Uniqueness of the actual scalar comparison equation, including its state. -/

@[expose] public section

noncomputable section

namespace EulerPacketMovingFrame

open Set EulerPacketGrowth EulerPacketExistence

/-- The scalar equation and its initial state determine both state
components on the forward half-line.  This lets independently constructed
neighbor comparisons use one common reference. -/
theorem equation30_state_eq_of_initial
    {σ : ℝ} {Z Z₁ W W₁ : ℝ → ℝ}
    (hσ : 0 < σ) (hσsmall : σ ≤ 1 / 4)
    (hZ : ∀ t, 0 ≤ t → HasDerivAt Z (Z₁ t) t)
    (hW : ∀ t, 0 ≤ t → HasDerivAt W (W₁ t) t)
    (hfluxZ : ∀ t, 0 ≤ t → HasDerivAt (fun s => (1 + (σ ^ 2 * s ^ 2) ^ 2) * Z₁ s)
      (2 * (1 - σ ^ 2 * (σ ^ 2 * t ^ 2)) * Z t) t)
    (hfluxW : ∀ t, 0 ≤ t → HasDerivAt (fun s => (1 + (σ ^ 2 * s ^ 2) ^ 2) * W₁ s)
      (2 * (1 - σ ^ 2 * (σ ^ 2 * t ^ 2)) * W t) t)
    (hi : Z 0 = W 0) (hi₁ : Z₁ 0 = W₁ 0) :
    ∀ t, 0 ≤ t → Z t = W t ∧ Z₁ t = W₁ t := by
  have hσ2 : σ^2 ≤ 1 := by nlinarith only [hσ, hσsmall]
  obtain ⟨F, F₁, hF0, hF₁0, hF, hfluxF⟩ := equation30_exists_global (sq_nonneg σ) hσ2 1 0
  intro t ht
  have hdiff : ∀ s ∈ Icc 0 t,
      HasDerivAt (fun x => Z x-W x) (Z₁ s-W₁ s) s := by
    intro s hs
    exact (hZ s hs.1).sub (hW s hs.1)
  have hfluxdiff : ∀ s ∈ Icc 0 t,
      HasDerivAt (fun x => (1+(σ^2*x^2)^2)*(Z₁ x-W₁ x))
        (2*(1-σ^2*(σ^2*s^2))*(Z s-W s)) s := by
    intro s hs
    convert! (hfluxZ s hs.1).sub (hfluxW s hs.1) using 1
    · ext x
      dsimp only [Pi.sub_apply]
      ring
    · ring
  have hb := equation30_relative_propagator hσ hσsmall (le_max_left 1 t)
    (by norm_num : (0:ℝ) ≤ 0) ht (le_max_right 1 t)
    (fun s _ => hF s) (fun s _ => hfluxF s) hF0 hF₁0 hdiff hfluxdiff
  simp only [hi, hi₁, sub_self, abs_zero, add_zero, mul_zero] at hb
  have hz : |Z t-W t| = 0 := by linarith only [hb, abs_nonneg (Z t-W t), abs_nonneg (Z₁ t-W₁ t)]
  have hz₁ : |Z₁ t-W₁ t| = 0 := by linarith only [hb, abs_nonneg (Z t-W t), abs_nonneg (Z₁ t-W₁ t)]
  exact ⟨sub_eq_zero.mp (abs_eq_zero.mp hz), sub_eq_zero.mp (abs_eq_zero.mp hz₁)⟩

end EulerPacketMovingFrame

end
end

end

@[expose] public section

noncomputable section

namespace EulerPacketMovingFrame

open Set EulerSmoothLimit EulerPacketNormalizedPrimary EulerPacketRay
  InnerProductSpace ContinuousLinearMap

theorem physical_family_amplification_and_size {α : Type*} (center : α)
    {B B₁ : ℝ → Space →L[ℝ] Space} {M E : α → ℝ → Space →L[ℝ] Space}
    {m v : ℝ → Space} {r w : α → ℝ → Space}
    {c s₀ t₀ a ε σ Θ T G d lam : ℝ} {S : Set ℝ}
    (hσ : 0 < σ) (hσsmall : σ ≤ 1 / 4) (hT0 : 1 ≤ T) (hT : T ≤ Θ)
    (ha : 1 / 2 ≤ a) (hε : 0 < ε) (hΘ : 1 ≤ Θ) (hG : 1 ≤ G) (hd : 0 ≤ d)
    (hs₀ : 0 < s₀) (hlam : 0 ≤ lam)
    (hsmall : 1000000 * neighborStabilityConstant * (16 * (ε * Θ * (4 * G) ^ 2 + d)) * Θ ^ 40 ≤ 1)
    (hmap : MapsTo (physicalTime t₀ a ε) (Icc 0 Θ) S)
    (hMc : ∀ ξ, ContinuousOn (M ξ) S)
    (hBd : ∀ t ∈ S, HasDerivWithinAt B (B₁ t) S t)
    (hmd : ∀ t ∈ S, HasDerivWithinAt m (-(B t).adjoint (m t)) S t)
    (hvd : ∀ t ∈ S, HasDerivWithinAt v (-(B t) (v t) +
      (2 * ⟪m t, (B t) (v t)⟫_ℝ / ‖m t‖ ^ 2) • m t) S t)
    (hrd : ∀ ξ t, t ∈ S → HasDerivWithinAt (r ξ) (-(M ξ t).adjoint (r ξ t)) S t)
    (hwd : ∀ ξ t, t ∈ S → HasDerivWithinAt (w ξ) (-(M ξ t) (w ξ t) +
      (2 * ⟪r ξ t, (M ξ t) (w ξ t)⟫_ℝ / ‖r ξ t‖ ^ 2) • r ξ t) S t)
    (hm0 : ∀ t ∈ S, m t ≠ 0) (hv0 : ∀ t ∈ S, v t ≠ 0)
    (hmv : ∀ t ∈ S, ⟪m t, v t⟫_ℝ = 0) (hrw0 : ∀ ξ, ⟪r ξ t₀, w ξ t₀⟫_ℝ = 0)
    (hB : ∀ t ∈ S, ‖B t‖ ≤ G) (hB₁ : ∀ t ∈ S, ‖B₁ t‖ ≤ G ^ 2)
    (hE : ∀ ξ t, t ∈ S → ‖E ξ t‖ ≤ d)
    (hparent : ∀ ξ t, t ∈ S → M ξ t = B t +
      primaryShear c m v t • rankOne ℝ (unit (v t)) (unit (m t)) + E ξ t)
    (hb0 : rescaledFrame B m v t₀ a ε 0 0 1 = a)
    (hk0 : rescaledFrame B m v t₀ a ε 0 2 1 = a * σ ^ 2)
    (hh0 : rescaledShear c m v t₀ a ε 0 = a / ε ^ 2)
    (hrInitial : ∀ ξ,
      norm3 (scaledRay m v (r ξ) s₀ t₀ a ε 0 0) (scaledRay m v (r ξ) s₀ t₀ a ε 0 1)
        (scaledRay m v (r ξ) s₀ t₀ a ε 0 2 - 1) ≤ 16 * (ε * Θ * (4 * G) ^ 2 + d))
    (hvelocityInitial : ∀ ξ, |scaledVelocity m v (w ξ) t₀ a ε 0 1 - 1| +
      |scaledVelocity m v (w ξ) t₀ a ε 0 0 + lam| ≤ 16 * (ε * Θ * (4 * G) ^ 2 + d)) :
    let e := 16*(ε*Θ*(4*G)^2+d)
    ∃ F F₁ Z Z₁ : ℝ → ℝ,
      F 0 = 1 ∧ F₁ 0 = 0 ∧ Z 0 = 1 ∧ Z₁ 0 = lam ∧
      (∀ t, HasDerivAt F (F₁ t) t) ∧ (∀ t, HasDerivAt Z (Z₁ t) t) ∧
      (∀ t, HasDerivAt (fun s => (1+(σ^2*s^2)^2)*F₁ s)
        (2*(1-σ^2*(σ^2*t^2))*F t) t) ∧
      (∀ t, HasDerivAt (fun s => (1+(σ^2*s^2)^2)*Z₁ s)
        (2*(1-σ^2*(σ^2*t^2))*Z t) t) ∧
      (∀ ξ τ, τ ∈ Icc 0 T →
        norm3 (scaledRay m v (r ξ) s₀ t₀ a ε τ 0-σ^2*τ^2)
          (scaledRay m v (r ξ) s₀ t₀ a ε τ 1+2*σ^2*τ)
          (scaledRay m v (r ξ) s₀ t₀ a ε τ 2-1) ≤ 800*e*Θ^5 ∧
        1/2 ≤ scaledRay m v (r ξ) s₀ t₀ a ε τ 2 ∧
        ⟪r ξ (physicalTime t₀ a ε τ), w ξ (physicalTime t₀ a ε τ)⟫_ℝ = 0) ∧
      (∀ ξ τ, τ ∈ Icc 0 T →
        |scaledVelocity m v (w ξ) t₀ a ε τ 1-Z τ| +
          |scaledVelocity m v (w ξ) t₀ a ε τ 0+Z₁ τ| ≤ 400000000*e*Θ^29*(1+lam)*F τ) ∧
      (∀ ξ τ, τ ∈ Icc 1 T →
        0 < scaledVelocity m v (w ξ) t₀ a ε τ 1 ∧
        |scaledVelocity m v (w ξ) t₀ a ε τ 1/Z τ-1| ≤ neighborStabilityConstant*e*Θ^29 ∧
        |scaledVelocity m v (w ξ) t₀ a ε τ 0/scaledVelocity m v (w ξ) t₀ a ε τ 1+Z₁ τ/Z τ|
          ≤ 10*(neighborStabilityConstant*e*Θ^29)) ∧
      (∀ ξ τ, τ ∈ Icc 1 T →
        ‖r ξ (physicalTime t₀ a ε τ)‖*‖w ξ (physicalTime t₀ a ε τ)‖ ≤
          64*(‖r center (physicalTime t₀ a ε T)‖*‖w center (physicalTime t₀ a ε T)‖)) := by
  let e := 16*(ε*Θ*(4*G)^2+d)
  have hTpos : 0 < T := by linarith only [hT0]
  have hall (ξ : α) := physical_neighbor_stage_references hσ hσsmall hTpos hT ha hε hΘ hG hd
    (ne_of_gt hs₀) hlam hsmall hmap (hMc ξ) hBd hmd hvd (hrd ξ) (hwd ξ) hm0 hv0 hmv (hrw0 ξ)
    hB hB₁ (hE ξ) (hparent ξ) hb0 hk0 hh0 (hrInitial ξ) (hvelocityInitial ξ)
  obtain ⟨_, F, F₁, Z, Z₁, hF0, hF₁0, hZ0, hZ₁0, hF, hZ, hfluxF, hfluxZ, _, _⟩ := hall center
  have hcommon (ξ : α) :
      (∀ τ ∈ Icc 0 T,
        norm3 (scaledRay m v (r ξ) s₀ t₀ a ε τ 0-σ^2*τ^2)
          (scaledRay m v (r ξ) s₀ t₀ a ε τ 1+2*σ^2*τ)
          (scaledRay m v (r ξ) s₀ t₀ a ε τ 2-1) ≤ 800*e*Θ^5 ∧
        1/2 ≤ scaledRay m v (r ξ) s₀ t₀ a ε τ 2 ∧
        ⟪r ξ (physicalTime t₀ a ε τ), w ξ (physicalTime t₀ a ε τ)⟫_ℝ = 0) ∧
      (∀ τ ∈ Icc 0 T,
        |scaledVelocity m v (w ξ) t₀ a ε τ 1-Z τ| +
          |scaledVelocity m v (w ξ) t₀ a ε τ 0+Z₁ τ| ≤ 400000000*e*Θ^29*(1+lam)*F τ) ∧
      (∀ τ ∈ Icc 1 T,
        0 < scaledVelocity m v (w ξ) t₀ a ε τ 1 ∧
        |scaledVelocity m v (w ξ) t₀ a ε τ 1/Z τ-1| ≤ neighborStabilityConstant*e*Θ^29 ∧
        |scaledVelocity m v (w ξ) t₀ a ε τ 0/scaledVelocity m v (w ξ) t₀ a ε τ 1+Z₁ τ/Z τ|
          ≤ 10*(neighborStabilityConstant*e*Θ^29)) := by
    obtain ⟨hray, F', F₁', Z', Z₁', hF0', hF₁0', hZ0', hZ₁0', hF', hZ', hfluxF', hfluxZ', herr,
        hrel⟩ := hall ξ
    have hFeq := equation30_state_eq_of_initial hσ hσsmall (fun t _ => hF' t) (fun t _ => hF t)
      (fun t _ => hfluxF' t) (fun t _ => hfluxF t) (hF0'.trans hF0.symm) (hF₁0'.trans hF₁0.symm)
    have hZeq := equation30_state_eq_of_initial hσ hσsmall (fun t _ => hZ' t) (fun t _ => hZ t)
      (fun t _ => hfluxZ' t) (fun t _ => hfluxZ t) (hZ0'.trans hZ0.symm) (hZ₁0'.trans hZ₁0.symm)
    refine ⟨hray, ?_, ?_⟩
    · intro τ hτ
      simpa only [(hFeq τ hτ.1).1, (hZeq τ hτ.1).1, (hZeq τ hτ.1).2] using herr τ hτ
    · intro τ hτ
      have ht0 : 0 ≤ τ := by linarith only [hτ.1]
      simpa only [(hZeq τ ht0).1, (hZeq τ ht0).2] using hrel τ hτ
  refine ⟨F, F₁, Z, Z₁, hF0, hF₁0, hZ0, hZ₁0, hF, hZ, hfluxF, hfluxZ,
    (fun ξ => (hcommon ξ).1), (fun ξ => (hcommon ξ).2.1), (fun ξ => (hcommon ξ).2.2), ?_⟩
  have he : 0 ≤ e := by dsimp [e]; positivity
  have hεe : ε ≤ e := by
    have hg : 1 ≤ (4*G)^2 := by nlinarith only [hG, sq_nonneg (G-1)]
    have hc : 1 ≤ Θ*(4*G)^2 := by
      simpa only [one_mul] using mul_le_mul hΘ hg
        (by norm_num : (0:ℝ) ≤ 1) (by linarith only [hΘ] : 0 ≤ Θ)
    have hh := mul_le_mul_of_nonneg_left hc hε.le
    dsimp [e]
    nlinarith only [hh, hd, hε]
  have hK : 1 ≤ neighborStabilityConstant := (by
      norm_num : (1:ℝ) ≤ 1000000000).trans neighborStabilityConstant_ge
  have hsub : Icc (1:ℝ) T ⊆ Icc 0 T := fun _ ht => ⟨by linarith only [ht.1], ht.2⟩
  have htime {τ : ℝ} (hτ : τ ∈ Icc 1 T) : physicalTime t₀ a ε τ ∈ S :=
    hmap ⟨(hsub hτ).1, hτ.2.trans hT⟩
  have hrays (ξ : α) (τ : ℝ) (hτ : τ ∈ Icc 1 T) :
      |scaledRay m v (r ξ) s₀ t₀ a ε τ 0-σ^2*τ^2| ≤ 800*e*Θ^5 ∧
      |scaledRay m v (r ξ) s₀ t₀ a ε τ 1-(-2*σ^2*τ)| ≤ 800*e*Θ^5 ∧
      |scaledRay m v (r ξ) s₀ t₀ a ε τ 2-1| ≤ 800*e*Θ^5 := by
    have hh := ((hcommon ξ).1 τ (hsub hτ)).1
    unfold norm3 at hh
    have hqeq : scaledRay m v (r ξ) s₀ t₀ a ε τ 1-(-2*σ^2*τ) =
        scaledRay m v (r ξ) s₀ t₀ a ε τ 1+2*σ^2*τ := by ring
    rw [hqeq]
    constructor
    · linarith only [hh, abs_nonneg (scaledRay m v (r ξ) s₀ t₀ a ε τ 1+2*σ^2*τ),
        abs_nonneg (scaledRay m v (r ξ) s₀ t₀ a ε τ 2-1)]
    constructor
    · linarith only [hh, abs_nonneg (scaledRay m v (r ξ) s₀ t₀ a ε τ 0-σ^2*τ^2),
        abs_nonneg (scaledRay m v (r ξ) s₀ t₀ a ε τ 2-1)]
    · linarith only [hh, abs_nonneg (scaledRay m v (r ξ) s₀ t₀ a ε τ 0-σ^2*τ^2),
        abs_nonneg (scaledRay m v (r ξ) s₀ t₀ a ε τ 1+2*σ^2*τ)]
  exact physical_before_target_size_bound center (fun _ => m) (fun _ => v) r w
    hs₀ hε hσ hσsmall hT0 hT hΘ hK he hεe hsmall
    (fun _ _ hτ => hm0 _ (htime hτ)) (fun _ _ hτ => hv0 _ (htime hτ))
    (fun _ _ hτ => hmv _ (htime hτ)) (fun ξ τ hτ => ((hcommon ξ).1 τ (hsub hτ)).2.2)
    (fun t _ => hZ t) (fun t _ => hfluxZ t) hZ0 (by rw [hZ₁0]; exact hlam)
    (fun ξ τ hτ => (hrays ξ τ hτ).1) (fun ξ τ hτ => (hrays ξ τ hτ).2.1)
    (fun ξ τ hτ => (hrays ξ τ hτ).2.2) (fun ξ τ hτ => ((hcommon ξ).2.2 τ hτ).2.1)
    (fun ξ τ hτ => ((hcommon ξ).2.2 τ hτ).2.2)

end EulerPacketMovingFrame

end
end

end

section

/-! Relative propagator estimates on arbitrary subintervals for actual velocity states. -/

@[expose] public section

noncomputable section

namespace EulerPacketMovingFrame

open Set EulerPacketBridge EulerPacketPerturbation EulerClosedIntervalDerivativeExtension

theorem velocity_propagator_bound
    {σ Θ s t δ : ℝ} {F F₁ G G₁ U U₁ V V₁ : ℝ → ℝ}
    (hσ : 0 < σ) (hσsmall : σ ≤ 1 / 4) (hΘ : 1 ≤ Θ)
    (hs : 0 ≤ s) (hst : s ≤ t) (ht : t ≤ Θ) (hδ : 0 ≤ δ)
    (hsmall : 20 * Θ ^ 8 * δ * (t - s) ≤ 1 / 2)
    (hF : ∀ x, 0 ≤ x → HasDerivAt F (F₁ x) x)
    (hG : ∀ x, 0 ≤ x → HasDerivAt G (G₁ x) x)
    (hfluxF : ∀ x, 0 ≤ x → HasDerivAt (fun u => (1 + (σ ^ 2 * u ^ 2) ^ 2) * F₁ u)
      (2 * (1 - σ ^ 2 * (σ ^ 2 * x ^ 2)) * F x) x)
    (hfluxG : ∀ x, 0 ≤ x → HasDerivAt (fun u => (1 + (σ ^ 2 * u ^ 2) ^ 2) * G₁ u)
      (2 * (1 - σ ^ 2 * (σ ^ 2 * x ^ 2)) * G x) x)
    (hF0 : F 0 = 1) (hF₁0 : F₁ 0 = 0) (hG₁0 : G₁ 0 = 1)
    (hU : ∀ x ∈ Icc s t, HasDerivAt U (U₁ x) x)
    (hV : ∀ x ∈ Icc s t, HasDerivAt V (V₁ x) x)
    (hU₁c : ContinuousOn U₁ (Icc s t)) (hV₁c : ContinuousOn V₁ (Icc s t))
    (herror : ∀ x ∈ Icc s t,
      |U₁ x - idealVelocityFirst (σ ^ 2) x (U x) (V x)| + |V₁ x + U x| ≤ δ * (|U x| + |V x|)) :
    |U t|+|V t| ≤ 40*Θ^8*(F t/F s)*(|U s|+|V s|) := by
  let f : ℝ → ℝ := fun x => V₁ x+U x
  let g : ℝ → ℝ := fun x => -U₁ x+idealVelocityFirst (σ^2) x (U x) (V x)
  have hUc : ContinuousOn U (Icc s t) := fun x hx => (hU x hx).continuousAt.continuousWithinAt
  have hVc : ContinuousOn V (Icc s t) := fun x hx => (hV x hx).continuousAt.continuousWithinAt
  have hfc : ContinuousOn f (Icc s t) := hV₁c.add hUc
  have hgc : ContinuousOn g (Icc s t) := hU₁c.neg.add (continuousOn_idealVelocityFirst hUc hVc)
  have hY : ∀ x ∈ Icc s t, HasDerivAt V (-U x+f x) x := by
    intro x hx
    exact (velocity_scalar_flux (β := σ^2) (hU x hx) (hV x hx)).1
  have hfluxY : ∀ x ∈ Icc s t, HasDerivAt (fun u => (1+(σ^2*u^2)^2)*(-U u))
      (2*(1-σ^2*(σ^2*x^2))*V x+(1+(σ^2*x^2)^2)*g x) x := by
    intro x hx
    exact (velocity_scalar_flux (β := σ^2) (hU x hx) (hV x hx)).2
  have hforcing : ∀ x ∈ Icc s t, |f x|+|g x| ≤ δ*(|V x|+|-U x|) := by
    intro x hx
    have hg : |g x| = |U₁ x-idealVelocityFirst (σ^2) x (U x) (V x)| := by
      dsimp [g]
      rw [neg_add_eq_sub, abs_sub_comm]
    rw [hg, abs_neg]
    dsimp [f]
    linarith only [herror x hx]
  have hb := equation30_perturbed_bound hσ hσsmall hΘ hs hst ht hδ hsmall
    hF hG hfluxF hfluxG hF0 hF₁0 hG₁0 hY hfluxY hfc hgc hforcing t ⟨hst, le_rfl⟩
  simpa only [abs_neg, add_comm] using hb

theorem velocity_propagator_bound_within
    {σ Θ T e : ℝ} {F F₁ G G₁ U U₁ V V₁ : ℝ → ℝ}
    (hσ : 0 < σ) (hσsmall : σ ≤ 1 / 4) (hΘ : 1 ≤ Θ)
    (hT0 : 0 < T) (hT : T ≤ Θ) (he : 0 ≤ e) (hsmall : 40 * e * Θ ^ 21 ≤ 1)
    (hF : ∀ x, 0 ≤ x → HasDerivAt F (F₁ x) x)
    (hG : ∀ x, 0 ≤ x → HasDerivAt G (G₁ x) x)
    (hfluxF : ∀ x, 0 ≤ x → HasDerivAt (fun u => (1 + (σ ^ 2 * u ^ 2) ^ 2) * F₁ u)
      (2 * (1 - σ ^ 2 * (σ ^ 2 * x ^ 2)) * F x) x)
    (hfluxG : ∀ x, 0 ≤ x → HasDerivAt (fun u => (1 + (σ ^ 2 * u ^ 2) ^ 2) * G₁ u)
      (2 * (1 - σ ^ 2 * (σ ^ 2 * x ^ 2)) * G x) x)
    (hF0 : F 0 = 1) (hF₁0 : F₁ 0 = 0) (hG₁0 : G₁ 0 = 1)
    (hU : ∀ x ∈ Icc 0 T, HasDerivWithinAt U (U₁ x) (Icc 0 T) x)
    (hV : ∀ x ∈ Icc 0 T, HasDerivWithinAt V (V₁ x) (Icc 0 T) x)
    (hU₁c : ContinuousOn U₁ (Icc 0 T)) (hV₁c : ContinuousOn V₁ (Icc 0 T))
    (herror : ∀ x ∈ Icc 0 T,
      |U₁ x - idealVelocityFirst (σ ^ 2) x (U x) (V x)| + |V₁ x + U x| ≤ (e * Θ ^ 12) * (|U x| + |V
          x|)) :
    ∀ s t, 0 ≤ s → s ≤ t → t ≤ T →
      |U t|+|V t| ≤ 40*Θ^8*(F t/F s)*(|U s|+|V s|) := by
  obtain ⟨U', hUeq, hU'⟩ := exists_extension hT0 hU
  obtain ⟨V', hVeq, hV'⟩ := exists_extension hT0 hV
  intro s t hs hst ht
  have hsub : Icc s t ⊆ Icc 0 T := fun x hx => ⟨hs.trans hx.1, hx.2.trans ht⟩
  have hδ : 0 ≤ e*Θ^12 := by positivity
  have hspan : t-s ≤ Θ := by linarith only [ht, hT, hs]
  have hsmall' : 20*Θ^8*(e*Θ^12)*(t-s) ≤ 1/2 := by
    have hh := mul_le_mul_of_nonneg_left hspan (show 0 ≤ 20*e*Θ^20 by positivity)
    nlinarith only [hh, hsmall]
  have he' : ∀ x ∈ Icc s t,
      |U₁ x-idealVelocityFirst (σ^2) x (U' x) (V' x)|+|V₁ x+U' x| ≤
        (e*Θ^12)*(|U' x|+|V' x|) := by
    intro x hx
    simpa only [hUeq (hsub hx), hVeq (hsub hx)] using herror x (hsub hx)
  have hb := velocity_propagator_bound hσ hσsmall hΘ hs hst (ht.trans hT) hδ hsmall'
    hF hG hfluxF hfluxG hF0 hF₁0 hG₁0 (fun x hx => hU' x (hsub hx))
    (fun x hx => hV' x (hsub hx)) (hU₁c.mono hsub) (hV₁c.mono hsub) he'
  have hsT : s ∈ Icc 0 T := ⟨hs, hst.trans ht⟩
  have htT : t ∈ Icc 0 T := ⟨hs.trans hst, ht⟩
  simpa only [hUeq htT, hVeq htT, hUeq hsT, hVeq hsT] using hb

end EulerPacketMovingFrame

end
end

end

section

/-! Polynomial conversion between physical tangent vectors and the two-state system. -/

@[expose] public section

noncomputable section

namespace EulerPacketMovingFrame

open EulerSmoothLimit EulerPacketNormalizedPrimary EulerPacketRay InnerProductSpace

theorem scaled_pair_le_physical_norm (m v w : ℝ → Space) {t₀ a ε τ : ℝ}
    (hε : 0 < ε) (hε1 : ε ≤ 1)
    (hm : m (physicalTime t₀ a ε τ) ≠ 0) (hv : v (physicalTime t₀ a ε τ) ≠ 0)
    (hmv : ⟪m (physicalTime t₀ a ε τ), v (physicalTime t₀ a ε τ)⟫_ℝ = 0) :
    |scaledVelocity m v w t₀ a ε τ 0|+|scaledVelocity m v w t₀ a ε τ 1| ≤
      (2/ε)*‖w (physicalTime t₀ a ε τ)‖ := by
  have hU := frame_coordinate_abs_le_norm (unit (m (physicalTime t₀ a ε τ)))
    (unit (v (physicalTime t₀ a ε τ))) (w (physicalTime t₀ a ε τ))
    (unit_inner_self hm) (unit_inner_self hv) (unit_inner_zero hmv) 0
  have hV := frame_coordinate_abs_le_norm (unit (m (physicalTime t₀ a ε τ)))
    (unit (v (physicalTime t₀ a ε τ))) (w (physicalTime t₀ a ε τ))
    (unit_inner_self hm) (unit_inner_self hv) (unit_inner_zero hmv) 1
  change |movingVelocity m v w (physicalTime t₀ a ε τ) 0| ≤ _ at hU
  change |movingVelocity m v w (physicalTime t₀ a ε τ) 1| ≤ _ at hV
  rw [← scaledVelocity_restore m v w (ne_of_gt hε) 0] at hU
  rw [← scaledVelocity_restore m v w (ne_of_gt hε) 1] at hV
  norm_num [velocityScale, Fin.ext_iff, abs_mul, abs_of_pos hε] at hU hV
  have hεV := mul_le_mul_of_nonneg_left hV hε.le
  have hεnorm := mul_le_mul_of_nonneg_right hε1 (norm_nonneg (w (physicalTime t₀ a ε τ)))
  have hh : |scaledVelocity m v w t₀ a ε τ 0|+|scaledVelocity m v w t₀ a ε τ 1| ≤
      (2*‖w (physicalTime t₀ a ε τ)‖)/ε := by
    apply (le_div_iff₀ hε).mpr
    nlinarith only [hU, hεV, hεnorm]
  convert! hh using 1
  ring

theorem physical_velocity_le_scaled_state (m v r w : ℝ → Space)
    {s₀ t₀ a ε τ Θ ρ P₀ Q₀ : ℝ}
    (hs₀ : s₀ ≠ 0) (hε : 0 < ε) (hε1 : ε ≤ 1)
    (hm : m (physicalTime t₀ a ε τ) ≠ 0) (hv : v (physicalTime t₀ a ε τ) ≠ 0)
    (hmv : ⟪m (physicalTime t₀ a ε τ), v (physicalTime t₀ a ε τ)⟫_ℝ = 0)
    (hrw : ⟪r (physicalTime t₀ a ε τ), w (physicalTime t₀ a ε τ)⟫_ℝ = 0)
    (hΘ : 1 ≤ Θ) (hρ0 : 0 ≤ ρ) (hρ : ρ ≤ 1 / 2)
    (hP₀ : |P₀| ≤ Θ ^ 2) (hQ₀ : |Q₀| ≤ 2 * Θ ^ 2)
    (hP : |scaledRay m v r s₀ t₀ a ε τ 0 - P₀| ≤ ρ)
    (hQ : |scaledRay m v r s₀ t₀ a ε τ 1 - Q₀| ≤ ρ)
    (hN : |scaledRay m v r s₀ t₀ a ε τ 2 - 1| ≤ ρ) :
    ‖w (physicalTime t₀ a ε τ)‖ ≤
      7*Θ^2*(|scaledVelocity m v w t₀ a ε τ 0|+|scaledVelocity m v w t₀ a ε τ 1|) := by
  let R := scaledRay m v r s₀ t₀ a ε τ
  let V := scaledVelocity m v w t₀ a ε τ
  have hpair := scaled_pairing_zero m v r w hs₀ (ne_of_gt hε) hm hv hmv hrw
  obtain ⟨hn, _, _, _, hw, _, _⟩ := ray_geometric_bounds (ε := ε) (U := V 0) (V := V 1)
    hΘ hρ0 hρ hP₀ hQ₀ hP hQ hN
  have hNne : R 2 ≠ 0 := by linarith only [hn]
  have hthird := thirdVelocity_of_pairing R V hNne hpair
  rw [← hthird] at hw
  have hΘ2 : 1 ≤ Θ^2 := one_le_pow₀ hΘ
  have hV : norm3 (V 0) (V 1) (V 2) ≤ 7*Θ^2*(|V 0|+|V 1|) := by
    dsimp [norm3]
    have ht := mul_le_mul_of_nonneg_right hΘ2 (add_nonneg (abs_nonneg (V 0)) (abs_nonneg (V 1)))
    nlinarith only [hw, ht]
  exact (scaledVelocity_norm_le_norm3 m v w hε hε1 hm hv hmv).trans hV

end EulerPacketMovingFrame

end
end

end

section

/-!
The arbitrary physical tangent propagator has polynomial loss relative to
the actual primary scalar profile.  All scaled coefficients and tangency
properties are derived from the physical ODEs and parent decomposition.
-/

section

/-! The actual controlled velocity system has polynomial relative propagation. -/

section

/-! Relative growth of the primary scalar reference dominates zero slope. -/

@[expose] public section

noncomputable section

namespace EulerPacketMovingFrame

open Set EulerPacketGrowth

theorem equation30_slope_ratio_dominates
    {σ lam s t : ℝ} {F F₁ Z Z₁ : ℝ → ℝ}
    (hσ : 0 < σ) (hσsmall : σ ≤ 1 / 4) (hlam : 0 ≤ lam)
    (hF : ∀ x, 0 ≤ x → HasDerivAt F (F₁ x) x)
    (hZ : ∀ x, 0 ≤ x → HasDerivAt Z (Z₁ x) x)
    (hfluxF : ∀ x, 0 ≤ x → HasDerivAt (fun u => (1 + (σ ^ 2 * u ^ 2) ^ 2) * F₁ u)
      (2 * (1 - σ ^ 2 * (σ ^ 2 * x ^ 2)) * F x) x)
    (hfluxZ : ∀ x, 0 ≤ x → HasDerivAt (fun u => (1 + (σ ^ 2 * u ^ 2) ^ 2) * Z₁ u)
      (2 * (1 - σ ^ 2 * (σ ^ 2 * x ^ 2)) * Z x) x)
    (hF0 : F 0 = 1) (hF₁0 : F₁ 0 = 0) (hZ0 : Z 0 = 1) (hZ₁0 : Z₁ 0 = lam)
    (hs : 0 ≤ s) (hst : s ≤ t) :
    F t/F s ≤ Z t/Z s := by
  have hFp := equation30_global_positive hσ hσsmall hF hfluxF hF0 (by rw [hF₁0])
  have hZp := equation30_global_positive hσ hσsmall hZ hfluxZ hZ0 (by rw [hZ₁0]; exact hlam)
  have ht : 0 ≤ t := hs.trans hst
  let D : ℝ → ℝ := fun x => 1+(σ^2*x^2)^2
  have hquotient : ∀ x ∈ Icc 0 t,
      HasDerivAt (fun u => Z u/F u) (lam/(D x*(F x)^2)) x := by
    have hh := quotient_derivative_of_flux
      (D := D) (c := fun x => 2*(1-σ^2*(σ^2*x^2)))
      (fun x (hx : x ∈ Icc 0 t) => hF x hx.1)
      (fun x hx => hZ x hx.1) (fun x hx => hfluxF x hx.1) (fun x hx => hfluxZ x hx.1)
      (fun _ _ => by dsimp [D]; positivity)
      (fun x hx => ne_of_gt (hFp x hx.1))
    intro x hx
    simpa only [hF0, hF₁0, hZ₁0, D, zero_pow (by decide : 2 ≠ 0), mul_zero, zero_mul,
      add_zero, one_mul, sub_zero] using hh x hx
  have hmono : MonotoneOn (fun x => Z x/F x) (Icc 0 t) := by
    apply monotoneOn_of_hasDerivWithinAt_nonneg (convex_Icc (0:ℝ) t)
      (fun x hx => (hquotient x hx).continuousAt.continuousWithinAt)
      (fun x hx => (hquotient x (interior_subset hx)).hasDerivWithinAt)
    intro x _
    exact div_nonneg hlam (by dsimp [D]; positivity)
  have hr := hmono ⟨hs, hst⟩ ⟨ht, le_rfl⟩ hst
  have hp := (div_le_div_iff₀ (hFp s hs) (hFp t ht)).mp hr
  apply (div_le_div_iff₀ (hFp s hs) (hZp s hs)).mpr
  nlinarith only [hp]

end EulerPacketMovingFrame

end
end

end

@[expose] public section

noncomputable section

namespace EulerPacketMovingFrame

open Set EulerPacketRay EulerPacketBridge EulerPacketExistence

/-- No initial velocity restriction is imposed.  The reference can have
any nonnegative initial slope, and the bound retains its ratio. -/
theorem controlled_velocity_propagator_within
    {σ Θ T e ε : ℝ} {Z Z₁ U V P Q N : ℝ → ℝ}
    {R A C : ℝ → Fin 3 → Fin 3 → ℝ}
    (hσ : 0 < σ) (hσsmall : σ ≤ 1 / 4) (hΘ : 1 ≤ Θ)
    (hT0 : 0 < T) (hT : T ≤ Θ) (he : 0 ≤ e) (hε : 0 ≤ ε) (hεe : ε ≤ e)
    (hsmall : 8000000 * e * Θ ^ 21 ≤ 1)
    (hRc : ∀ i j, ContinuousOn (fun t => R t i j) (Icc 0 T))
    (hAc : ∀ i j, ContinuousOn (fun t => A t i j) (Icc 0 T))
    (hCc : ∀ i j, ContinuousOn (fun t => C t i j) (Icc 0 T))
    (hP : ∀ t ∈ Icc 0 T, HasDerivWithinAt P
      (R t 0 0 * P t + R t 0 1 * Q t + R t 0 2 * N t) (Icc 0 T) t)
    (hQ : ∀ t ∈ Icc 0 T, HasDerivWithinAt Q
      (R t 1 0 * P t + R t 1 1 * Q t + R t 1 2 * N t) (Icc 0 T) t)
    (hN : ∀ t ∈ Icc 0 T, HasDerivWithinAt N
      (R t 2 0 * P t + R t 2 1 * Q t + R t 2 2 * N t) (Icc 0 T) t)
    (hU : ∀ t ∈ Icc 0 T, HasDerivWithinAt U
      (velocityFirstRhs (A t) (C t) ε (P t) (Q t) (N t) (U t) (V t)) (Icc 0 T) t)
    (hV : ∀ t ∈ Icc 0 T, HasDerivWithinAt V
      (velocitySecondRhs (A t) (C t) ε (P t) (Q t) (N t) (U t) (V t)) (Icc 0 T) t)
    (hRclose : ∀ t ∈ Icc 0 T, ∀ i j, |R t i j - idealRayEntry (σ ^ 2) i j| ≤ 4 * e)
    (hAclose : ∀ t ∈ Icc 0 T, ∀ i j, |A t i j - idealVelocityEntry (σ ^ 2) i j| ≤ 3 * e)
    (hCclose : ∀ t ∈ Icc 0 T, ∀ j,
      |C t 0 j - idealUnprojectedEntry 0 j| ≤ 5 * e ∧
      |C t 1 j - idealUnprojectedEntry 1 j| ≤ 5 * e)
    (hrayInitial : norm3 (P 0) (Q 0) (N 0 - 1) ≤ e)
    (hZ : ∀ t, 0 ≤ t → HasDerivAt Z (Z₁ t) t)
    (hfluxZ : ∀ t, 0 ≤ t → HasDerivAt (fun s => (1 + (σ ^ 2 * s ^ 2) ^ 2) * Z₁ s)
      (2 * (1 - σ ^ 2 * (σ ^ 2 * t ^ 2)) * Z t) t)
    (hZ0 : Z 0 = 1) (hZ₁0 : 0 ≤ Z₁ 0) :
    ∀ s t, 0 ≤ s → s ≤ t → t ≤ T →
      |U t|+|V t| ≤ 40*Θ^8*(Z t/Z s)*(|U s|+|V s|) := by
  have hσ2 : σ^2 ≤ 1 := by nlinarith only [hσ, hσsmall]
  obtain ⟨F, F₁, G, G₁, hF0, hF₁0, _, hG₁0, hF, hG, hfluxF, hfluxG⟩ :=
    equation30_exists_fundamental_system (sq_nonneg σ) hσ2
  have hΘ0 : 0 ≤ Θ := by linarith only [hΘ]
  have hgeom : 10000*e*Θ^5 ≤ 1 := by
    have hh := mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hΘ (by decide : 5 ≤ 21)) he
    nlinarith only [hsmall, hh, mul_nonneg he (pow_nonneg hΘ0 21)]
  have hcontrol := ray_controlled_velocity_error_within (sq_nonneg σ) hσ2 hΘ hT0 hT
    he hε hεe hgeom hRc hP hQ hN hRclose hAclose hCclose hrayInitial
  have hPc : ContinuousOn P (Icc 0 T) := fun t ht => (hP t ht).continuousWithinAt
  have hQc : ContinuousOn Q (Icc 0 T) := fun t ht => (hQ t ht).continuousWithinAt
  have hNc : ContinuousOn N (Icc 0 T) := fun t ht => (hN t ht).continuousWithinAt
  have hUc : ContinuousOn U (Icc 0 T) := fun t ht => (hU t ht).continuousWithinAt
  have hVc : ContinuousOn V (Icc 0 T) := fun t ht => (hV t ht).continuousWithinAt
  have hNne : ∀ t ∈ Icc 0 T, N t ≠ 0 := by
    intro t ht
    linarith only [(hcontrol t ht).1.2]
  obtain ⟨hU₁c, hV₁c⟩ := continuousOn_velocity_rhs (ε := ε) hAc hCc hPc hQc hNc hUc hVc hNne
  have hs : 40*(200000*e)*Θ^21 ≤ 1 := by nlinarith only [hsmall]
  have hprop := velocity_propagator_bound_within hσ hσsmall hΘ hT0 hT
    (show 0 ≤ 200000*e by positivity) hs (fun t _ => hF t) (fun t _ => hG t)
    (fun t _ => hfluxF t) (fun t _ => hfluxG t) hF0 hF₁0 hG₁0 hU hV hU₁c hV₁c
    (fun t ht => (hcontrol t ht).2 (U t) (V t))
  intro s t hstart hst ht
  have hratio := equation30_slope_ratio_dominates hσ hσsmall hZ₁0
    (fun x _ => hF x) hZ (fun x _ => hfluxF x) hfluxZ hF0 hF₁0 hZ0 rfl hstart hst
  have hcompare := mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left hratio (show 0 ≤ 40*Θ^8 by positivity))
    (add_nonneg (abs_nonneg (U s)) (abs_nonneg (V s)))
  exact (hprop s t hstart hst ht).trans hcompare

end EulerPacketMovingFrame

end
end

end

@[expose] public section

noncomputable section

namespace EulerPacketMovingFrame

open Set EulerSmoothLimit EulerPacketNormalizedPrimary EulerPacketRay
    InnerProductSpace ContinuousLinearMap

theorem physical_tangent_propagator
    {B B₁ M E : ℝ → Space →L[ℝ] Space} {m v r w : ℝ → Space}
    {c s₀ t₀ a ε σ Θ T G d : ℝ} {S : Set ℝ}
    (hσ : 0 < σ) (hσsmall : σ ≤ 1 / 4) (hT0 : 0 < T) (hT : T ≤ Θ)
    (ha : 1 / 2 ≤ a) (hε : 0 < ε) (hΘ : 1 ≤ Θ) (hG : 1 ≤ G) (hd : 0 ≤ d)
    (hs₀ : s₀ ≠ 0)
    (hsmall : 8000000 * (16 * (ε * Θ * (4 * G) ^ 2 + d)) * Θ ^ 21 ≤ 1)
    (hmap : MapsTo (physicalTime t₀ a ε) (Icc 0 Θ) S)
    (hMc : ContinuousOn M S)
    (hBd : ∀ t ∈ S, HasDerivWithinAt B (B₁ t) S t)
    (hmd : ∀ t ∈ S, HasDerivWithinAt m (-(B t).adjoint (m t)) S t)
    (hvd : ∀ t ∈ S, HasDerivWithinAt v (-(B t) (v t) +
      (2 * ⟪m t, (B t) (v t)⟫_ℝ / ‖m t‖ ^ 2) • m t) S t)
    (hrd : ∀ t ∈ S, HasDerivWithinAt r (-(M t).adjoint (r t)) S t)
    (hwd : ∀ t ∈ S, HasDerivWithinAt w (-(M t) (w t) +
      (2 * ⟪r t, (M t) (w t)⟫_ℝ / ‖r t‖ ^ 2) • r t) S t)
    (hm0 : ∀ t ∈ S, m t ≠ 0) (hv0 : ∀ t ∈ S, v t ≠ 0)
    (hmv : ∀ t ∈ S, ⟪m t, v t⟫_ℝ = 0) (hrw0 : ⟪r t₀, w t₀⟫_ℝ = 0)
    (hB : ∀ t ∈ S, ‖B t‖ ≤ G) (hB₁ : ∀ t ∈ S, ‖B₁ t‖ ≤ G ^ 2)
    (hE : ∀ t ∈ S, ‖E t‖ ≤ d)
    (hparent : ∀ t ∈ S, M t = B t +
      primaryShear c m v t • rankOne ℝ (unit (v t)) (unit (m t)) + E t)
    (hb0 : rescaledFrame B m v t₀ a ε 0 0 1 = a)
    (hk0 : rescaledFrame B m v t₀ a ε 0 2 1 = a * σ ^ 2)
    (hh0 : rescaledShear c m v t₀ a ε 0 = a / ε ^ 2)
    (hrInitial : norm3 (scaledRay m v r s₀ t₀ a ε 0 0) (scaledRay m v r s₀ t₀ a ε 0 1)
      (scaledRay m v r s₀ t₀ a ε 0 2 - 1) ≤ 16 * (ε * Θ * (4 * G) ^ 2 + d))
    {Z Z₁ : ℝ → ℝ}
    (hZ : ∀ t, 0 ≤ t → HasDerivAt Z (Z₁ t) t)
    (hfluxZ : ∀ t, 0 ≤ t → HasDerivAt (fun s => (1 + (σ ^ 2 * s ^ 2) ^ 2) * Z₁ s)
      (2 * (1 - σ ^ 2 * (σ ^ 2 * t ^ 2)) * Z t) t)
    (hZ0 : Z 0 = 1) (hZ₁0 : 0 ≤ Z₁ 0) :
    ContinuousOn Z (Icc 0 T) ∧ (∀ t ∈ Icc 0 T, 0 < Z t) ∧
      ∀ s t, 0 ≤ s → s ≤ t → t ≤ T →
        ‖w (physicalTime t₀ a ε t)‖ ≤
          (560*Θ^10/ε)*(Z t/Z s)*‖w (physicalTime t₀ a ε s)‖ := by
  let e := 16*(ε*Θ*(4*G)^2+d)
  let Rp := scaledRay m v r s₀ t₀ a ε
  let Vp := scaledVelocity m v w t₀ a ε
  let Mf := rescaledFrame M m v t₀ a ε
  let Bf := rescaledFrame B m v t₀ a ε
  let Rmat : ℝ → Fin 3 → Fin 3 → ℝ := fun τ => scaledRayEntry a ε (Mf τ) (frameSkew (Bf τ))
  let Amat : ℝ → Fin 3 → Fin 3 → ℝ := fun τ => scaledVelocityEntry a ε (Mf τ)
  let Cmat : ℝ → Fin 3 → Fin 3 → ℝ := fun τ =>
    scaledVelocityEntry a ε (fun i j => Mf τ i j+frameSkew (Bf τ) i j)
  have he : 0 ≤ e := by dsimp [e]; positivity
  have hΘ0 : 0 ≤ Θ := by linarith
  change 8000000*e*Θ^21 ≤ 1 at hsmall
  have heΘ : e ≤ e*Θ^21 := by
    simpa only [mul_one] using mul_le_mul_of_nonneg_left (one_le_pow₀ hΘ : 1 ≤ Θ^21) he
  have heSmall : e ≤ 1 := by nlinarith only [hsmall, heΘ, he]
  have hpow : e*Θ^5 ≤ e*Θ^21 :=
    mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hΘ (by decide : 5 ≤ 21)) he
  have hsmallRay : 400*(4*e)*Θ^5 ≤ 1 := by
    nlinarith only [hsmall, hpow, mul_nonneg he (pow_nonneg hΘ0 5)]
  have ha0 : 0 < a := by linarith
  have hσsq : σ^2 ≤ 1 := by nlinarith only [hσ, hσsmall]
  have herr := physical_matrix_errors ha hε hΘ hG hd heSmall hmap hBd hmd hvd hm0 hv0 hmv
    hB hB₁ hE hparent hb0 hk0 hh0
  have hsub : Icc (0:ℝ) T ⊆ Icc 0 Θ := fun _ ht => ⟨ht.1, ht.2.trans hT⟩
  have hmapT : MapsTo (physicalTime t₀ a ε) (Icc 0 T) S := fun _ ht => hmap (hsub ht)
  have hMf : ∀ i j, ContinuousOn (fun τ => Mf τ i j) (Icc 0 T) :=
    rescaledFrame_continuousOn B M hmapT hMc hmd hvd hm0 hv0 hmv
  have hBf : ∀ i j, ContinuousOn (fun τ => Bf τ i j) (Icc 0 T) :=
    rescaledFrame_continuousOn B B hmapT (fun t ht => (hBd t ht).continuousWithinAt)
      hmd hvd hm0 hv0 hmv
  have hSf := frameSkew_continuousOn hBf
  have hRmc : ∀ i j, ContinuousOn (fun τ => Rmat τ i j) (Icc 0 T) :=
    scaledRayEntry_continuousOn a ε hMf hSf
  have hAmc : ∀ i j, ContinuousOn (fun τ => Amat τ i j) (Icc 0 T) :=
    scaledVelocityEntry_continuousOn a ε hMf
  have hCmc : ∀ i j, ContinuousOn (fun τ => Cmat τ i j) (Icc 0 T) :=
    scaledVelocityEntry_continuousOn a ε (fun i j => (hMf i j).add (hSf i j))
  have hRode : ∀ i τ, τ ∈ Icc 0 T → HasDerivWithinAt (fun s => Rp s i)
      (∑ j : Fin 3, Rmat τ i j*Rp τ j) (Icc 0 T) τ := by
    intro i τ hτ
    have ht := hmapT hτ
    exact scaledRay_hasDerivWithinAt (B (physicalTime t₀ a ε τ)) (M (physicalTime t₀ a ε τ))
      (ne_of_gt ha0) (ne_of_gt hε) hs₀ hmapT (hmd _ ht) (hvd _ ht) (hrd _ ht)
      (hm0 _ ht) (hv0 _ ht) (hmv _ ht) i
  have hP : ∀ τ ∈ Icc 0 T, HasDerivWithinAt (fun s => Rp s 0)
      (Rmat τ 0 0*Rp τ 0+Rmat τ 0 1*Rp τ 1+Rmat τ 0 2*Rp τ 2) (Icc 0 T) τ := by
    intro τ hτ
    simpa only [Fin.sum_univ_three] using hRode 0 τ hτ
  have hQ : ∀ τ ∈ Icc 0 T, HasDerivWithinAt (fun s => Rp s 1)
      (Rmat τ 1 0*Rp τ 0+Rmat τ 1 1*Rp τ 1+Rmat τ 1 2*Rp τ 2) (Icc 0 T) τ := by
    intro τ hτ
    simpa only [Fin.sum_univ_three] using hRode 1 τ hτ
  have hN : ∀ τ ∈ Icc 0 T, HasDerivWithinAt (fun s => Rp s 2)
      (Rmat τ 2 0*Rp τ 0+Rmat τ 2 1*Rp τ 1+Rmat τ 2 2*Rp τ 2) (Icc 0 T) τ := by
    intro τ hτ
    simpa only [Fin.sum_univ_three] using hRode 2 τ hτ
  have hRclose : ∀ τ ∈ Icc 0 T, ∀ i j, |Rmat τ i j-idealRayEntry (σ^2) i j| ≤ 4*e :=
    fun τ hτ => (herr.2 τ (hsub hτ)).1
  have hnear := ray_closeness_within (sq_nonneg σ) hσsq hΘ hT0 hT
    (mul_nonneg (by norm_num : (0:ℝ) ≤ 4) he) hsmallRay hRmc hP hQ hN hRclose
    (hrInitial.trans (show e ≤ 4*e by linarith))
  have hrnonzero : ∀ τ ∈ Icc 0 T, r (physicalTime t₀ a ε τ) ≠ 0 := by
    intro τ hτ hzero
    have hNne : Rp τ 2 ≠ 0 := by linarith only [(hnear τ hτ).2]
    apply hNne
    simp only [Rp, scaledRay, movingRay, hzero, inner_zero_right, zero_div]
  have hpair := rescaled_tangentPairing_zero M hmapT hrd hwd hrnonzero hrw0
  have hUV : ∀ τ ∈ Icc 0 T,
      HasDerivWithinAt (fun s => Vp s 0)
        (velocityFirstRhs (Amat τ) (Cmat τ) ε (Rp τ 0) (Rp τ 1) (Rp τ 2) (Vp τ 0) (Vp τ 1)) (Icc 0
            T) τ ∧
      HasDerivWithinAt (fun s => Vp s 1)
        (velocitySecondRhs (Amat τ) (Cmat τ) ε (Rp τ 0) (Rp τ 1) (Rp τ 2) (Vp τ 0) (Vp τ 1)) (Icc 0
            T) τ := by
    intro τ hτ
    have ht := hmapT hτ
    have hNne : Rp τ 2 ≠ 0 := by linarith only [(hnear τ hτ).2]
    exact scaledVelocity_firstTwo_hasDerivWithinAt (B (physicalTime t₀ a ε τ))
      (M (physicalTime t₀ a ε τ)) (ne_of_gt ha0) (ne_of_gt hε) hs₀ hmapT
      (hmd _ ht) (hvd _ ht) (hwd _ ht) (hm0 _ ht) (hv0 _ ht) (hmv _ ht)
      (hrnonzero τ hτ) (hpair τ hτ) hNne
  have hprop := controlled_velocity_propagator_within hσ hσsmall hΘ hT0 hT he hε.le herr.1 hsmall
    hRmc hAmc hCmc hP hQ hN (fun τ hτ => (hUV τ hτ).1) (fun τ hτ => (hUV τ hτ).2)
    hRclose (fun τ hτ => (herr.2 τ (hsub hτ)).2.1) (fun τ hτ => (herr.2 τ (hsub hτ)).2.2)
    hrInitial hZ hfluxZ hZ0 hZ₁0
  have hZpos := EulerPacketGrowth.equation30_global_positive hσ hσsmall hZ hfluxZ hZ0 hZ₁0
  refine ⟨(fun τ hτ => (hZ τ hτ.1).continuousAt.continuousWithinAt),
    (fun τ hτ => hZpos τ hτ.1), ?_⟩
  intro s t hs hst ht
  have hsT : s ∈ Icc 0 T := ⟨hs, hst.trans ht⟩
  have htT : t ∈ Icc 0 T := ⟨hs.trans hst, ht⟩
  have htimeS := hmapT hsT
  have htimeT := hmapT htT
  have hε1 : ε ≤ 1 := herr.1.trans heSmall
  have hρ0 : 0 ≤ 800*e*Θ^5 := by positivity
  have hρ : 800*e*Θ^5 ≤ 1/2 := by
    nlinarith only [hsmall, hpow, mul_nonneg he (pow_nonneg hΘ0 5)]
  have hrt : norm3 (Rp t 0-σ^2*t^2) (Rp t 1+2*σ^2*t) (Rp t 2-1) ≤ 800*e*Θ^5 := by
    nlinarith only [(hnear t htT).1]
  have hPt : |Rp t 0-σ^2*t^2| ≤ 800*e*Θ^5 := by
    dsimp [norm3] at hrt
    linarith only [hrt, abs_nonneg (Rp t 1+2*σ^2*t), abs_nonneg (Rp t 2-1)]
  have hQt : |Rp t 1-(-2*σ^2*t)| ≤ 800*e*Θ^5 := by
    rw [show Rp t 1-(-2*σ^2*t) = Rp t 1+2*σ^2*t by ring]
    dsimp [norm3] at hrt
    linarith only [hrt, abs_nonneg (Rp t 0-σ^2*t^2), abs_nonneg (Rp t 2-1)]
  have hNt : |Rp t 2-1| ≤ 800*e*Θ^5 := by
    dsimp [norm3] at hrt
    linarith only [hrt, abs_nonneg (Rp t 0-σ^2*t^2), abs_nonneg (Rp t 1+2*σ^2*t)]
  have htΘ : t ≤ Θ := ht.trans hT
  have ht2 : t^2 ≤ Θ^2 := (sq_le_sq₀ htT.1 hΘ0).mpr htΘ
  have hP₀ : |σ^2*t^2| ≤ Θ^2 := by
    rw [abs_of_nonneg (by positivity : 0 ≤ σ^2*t^2)]
    nlinarith only [mul_le_mul_of_nonneg_right hσsq (sq_nonneg t), ht2]
  have hQ₀ : |-2*σ^2*t| ≤ 2*Θ^2 := by
    rw [abs_mul, abs_mul, abs_of_nonneg (sq_nonneg σ), abs_of_nonneg htT.1]
    norm_num only [abs_neg, abs_of_nonneg (by norm_num : (0:ℝ) ≤ 2)]
    nlinarith only [mul_le_mul_of_nonneg_right hσsq htT.1, htΘ, hΘ, sq_nonneg (Θ-1)]
  have hfinish := physical_velocity_le_scaled_state m v r w hs₀ hε hε1
    (hm0 _ htimeT) (hv0 _ htimeT) (hmv _ htimeT) (hpair t htT) hΘ hρ0 hρ hP₀ hQ₀ hPt hQt hNt
  have hstart := scaled_pair_le_physical_norm m v w hε hε1 (hm0 _ htimeS) (hv0 _ htimeS) (hmv _
      htimeS)
  have hratio : 0 ≤ Z t/Z s := div_nonneg (hZpos t htT.1).le (hZpos s hs).le
  have h1 := mul_le_mul_of_nonneg_left (hprop s t hs hst ht) (show 0 ≤ 7*Θ^2 by positivity)
  have h2 := mul_le_mul_of_nonneg_left hstart (show 0 ≤ 280*Θ^10*(Z t/Z s) by positivity)
  calc
    _ ≤ 7*Θ^2*(|Vp t 0|+|Vp t 1|) := hfinish
    _ ≤ 7*Θ^2*(40*Θ^8*(Z t/Z s)*(|Vp s 0|+|Vp s 1|)) := h1
    _ = 280*Θ^10*(Z t/Z s)*(|Vp s 0|+|Vp s 1|) := by ring
    _ ≤ 280*Θ^10*(Z t/Z s)*((2/ε)*‖w (physicalTime t₀ a ε s)‖) := h2
    _ = _ := by ring

end EulerPacketMovingFrame

end
end

end

section

/-!
# Packet Stage
-/

@[expose] public section

noncomputable section

open Set

namespace EulerPacketStage

open Real EulerPacketGrowth EulerPacketRay EulerPacketBridge EulerPacketFrameStability
    EulerPacketExistence

/-- Absolute relative-stability constant obtained from the propagator
bound and the primary-solution lower comparison. -/
noncomputable def stabilityConstant : ℝ := 320000000 * exp 6

theorem stabilityConstant_ge : 320000000 ≤ stabilityConstant := by
  have hh : (1 : ℝ) ≤ exp 6 := one_le_exp_iff.mpr (by norm_num)
  unfold stabilityConstant
  nlinarith only [hh]

/-- The controlled velocity system has an exact scalar comparison
solution, constructed from the axioms rather than supplied as a hypothesis. -/
theorem controlled_stage_references
    {σ Θ T e ε lam : ℝ} {U V P Q N : ℝ → ℝ} {R A C : ℝ → Fin 3 → Fin 3 → ℝ}
    (hσ : 0 < σ) (hσsmall : σ ≤ 1 / 4) (hΘ : 1 ≤ Θ)
    (hT0 : 0 ≤ T) (hT : T ≤ Θ) (he : 0 ≤ e) (hε : 0 ≤ ε) (hεe : ε ≤ e)
    (hlam : 0 ≤ lam) (hsmall : 1000000 * stabilityConstant * e * Θ ^ 40 ≤ 1)
    (hRc : ∀ i j, ContinuousOn (fun t => R t i j) (Icc 0 T))
    (hAc : ∀ i j, ContinuousOn (fun t => A t i j) (Icc 0 T))
    (hCc : ∀ i j, ContinuousOn (fun t => C t i j) (Icc 0 T))
    (hP : ∀ t ∈ Icc 0 T, HasDerivAt P
      (R t 0 0 * P t + R t 0 1 * Q t + R t 0 2 * N t) t)
    (hQ : ∀ t ∈ Icc 0 T, HasDerivAt Q
      (R t 1 0 * P t + R t 1 1 * Q t + R t 1 2 * N t) t)
    (hN : ∀ t ∈ Icc 0 T, HasDerivAt N
      (R t 2 0 * P t + R t 2 1 * Q t + R t 2 2 * N t) t)
    (hU : ∀ t ∈ Icc 0 T, HasDerivAt U
      (velocityFirstRhs (A t) (C t) ε (P t) (Q t) (N t) (U t) (V t)) t)
    (hV : ∀ t ∈ Icc 0 T, HasDerivAt V
      (velocitySecondRhs (A t) (C t) ε (P t) (Q t) (N t) (U t) (V t)) t)
    (hRclose : ∀ t ∈ Icc 0 T, ∀ i j, |R t i j - idealRayEntry (σ ^ 2) i j| ≤ 4 * e)
    (hAclose : ∀ t ∈ Icc 0 T, ∀ i j, |A t i j - idealVelocityEntry (σ ^ 2) i j| ≤ 3 * e)
    (hCclose : ∀ t ∈ Icc 0 T, ∀ i j, |C t i j - idealUnprojectedEntry i j| ≤ 5 * e)
    (hrayInitial : norm3 (P 0) (Q 0) (N 0 - 1) ≤ e)
    (hU0 : U 0 = -lam) (hV0 : V 0 = 1) :
    ∃ F F₁ Z Z₁ : ℝ → ℝ,
      F 0 = 1 ∧ F₁ 0 = 0 ∧ Z 0 = 1 ∧ Z₁ 0 = lam ∧
      (∀ t, HasDerivAt F (F₁ t) t) ∧ (∀ t, HasDerivAt Z (Z₁ t) t) ∧
      (∀ t, HasDerivAt (fun s => (1 + (σ ^ 2 * s ^ 2) ^ 2) * F₁ s)
        (2 * (1 - σ ^ 2 * (σ ^ 2 * t ^ 2)) * F t) t) ∧
      (∀ t, HasDerivAt (fun s => (1 + (σ ^ 2 * s ^ 2) ^ 2) * Z₁ s)
        (2 * (1 - σ ^ 2 * (σ ^ 2 * t ^ 2)) * Z t) t) ∧
      (∀ t ∈ Icc 0 T, |V t - Z t| + |U t + Z₁ t| ≤
        160000000 * e * Θ ^ 29 * (1 + lam) * F t) ∧
      (∀ t ∈ Icc 1 T, 0 < V t ∧
        |V t / Z t - 1| ≤ stabilityConstant * e * Θ ^ 29 ∧
        |U t / V t + Z₁ t / Z t| ≤ 10 * (stabilityConstant * e * Θ ^ 29)) := by
  have hσ2 : σ ^ 2 ≤ 1 := by nlinarith only [hσ, hσsmall]
  obtain ⟨F, F₁, G, G₁, hF0, hF₁0, _, hG₁0, hF, hG, hfluxF, hfluxG⟩ :=
    equation30_exists_fundamental_system (sq_nonneg σ) hσ2
  obtain ⟨Z, Z₁, hZ0, hZ₁0, hZ, hfluxZ⟩ := equation30_exists_global (sq_nonneg σ) hσ2 1 lam
  have hK := stabilityConstant_ge
  have hΘ0 : 0 ≤ Θ := by linarith
  have hpow21 : Θ ^ 21 ≤ Θ ^ 40 := pow_le_pow_right₀ hΘ (by decide)
  have hpow29 : Θ ^ 29 ≤ Θ ^ 40 := pow_le_pow_right₀ hΘ (by decide)
  have hsmallODE : 8000000 * e * Θ ^ 21 ≤ 1 := by
    have hm := mul_le_mul_of_nonneg_left hpow21 he
    have hKmul := mul_nonneg (show 0 ≤ stabilityConstant - 8 by linarith)
      (mul_nonneg he (pow_nonneg hΘ0 40))
    nlinarith only [hsmall, hm, hKmul]
  have herror := controlled_velocity_relative_error hσ hσsmall hΘ hT0 hT he hε hεe hlam hsmallODE
    (fun t _ => hF t) (fun t _ => hG t) (fun t _ => hfluxF t) (fun t _ => hfluxG t)
    hF0 hF₁0 hG₁0 hRc hAc hCc hP hQ hN hU hV hRclose hAclose hCclose
    (fun t _ => hZ t) (fun t _ => hfluxZ t) hrayInitial hU0 hV0 hZ0 hZ₁0
  refine ⟨F, F₁, Z, Z₁, hF0, hF₁0, hZ0, hZ₁0, hF, hZ, hfluxF, hfluxZ, herror, ?_⟩
  intro t ht
  let δ := 160000000 * e * Θ ^ 29
  have hδ : 0 ≤ δ := by dsimp [δ]; positivity
  have hrelSmall : 4 * exp 6 * δ ≤ 1 := by
    have hm := mul_le_mul_of_nonneg_left hpow29 (by positivity : 0 ≤ stabilityConstant * e)
    have hn : 0 ≤ stabilityConstant * e * Θ ^ 40 := by positivity
    dsimp [δ]
    unfold stabilityConstant at hm hn hsmall
    nlinarith only [hm, hn, hsmall]
  have herror' : |V t - Z t| + |U t + Z₁ t| ≤ δ * (1 + lam) * F t :=
    herror t ⟨by linarith [ht.1], ht.2⟩
  have hc := equation30_relative_state_consequences hσ hσsmall hlam ht.1 hδ hrelSmall
    (fun t _ => hF t) (fun t _ => hZ t) (fun t _ => hfluxF t) (fun t _ => hfluxZ t)
    hF0 hF₁0 hZ0 hZ₁0 herror'
  refine ⟨hc.1, ?_, ?_⟩
  · dsimp [δ]
      at hc
    unfold stabilityConstant
    nlinarith only [hc.2.1]
  · dsimp [δ]
      at hc
    unfold stabilityConstant
    nlinarith only [hc.2.2]

/-- Early forward amplitudes are exponentially small relative to target
amplitude, with the initial slope cancelling from the estimate.  This is
the finite-ODE amplification mechanism underlying equation (36). -/
theorem early_forward_exponential_suppression
    {σ Θ T lam δ : ℝ} {F F₁ Z Z₁ U V : ℝ → ℝ}
    (hσ : 0 < σ) (hσsmall : σ ≤ 1 / 4) (_hΘ : 1 ≤ Θ) (hT : T ≤ Θ)
    (hTtarget : 1 / σ ≤ T) (hlam : 0 ≤ lam) (hδ : 0 ≤ δ)
    (hδsmall : 4 * exp 6 * δ ≤ 1)
    (hF : ∀ t, HasDerivAt F (F₁ t) t) (hZ : ∀ t, HasDerivAt Z (Z₁ t) t)
    (hfluxF : ∀ t, HasDerivAt (fun s => (1 + (σ ^ 2 * s ^ 2) ^ 2) * F₁ s)
      (2 * (1 - σ ^ 2 * (σ ^ 2 * t ^ 2)) * F t) t)
    (hfluxZ : ∀ t, HasDerivAt (fun s => (1 + (σ ^ 2 * s ^ 2) ^ 2) * Z₁ s)
      (2 * (1 - σ ^ 2 * (σ ^ 2 * t ^ 2)) * Z t) t)
    (hF0 : F 0 = 1) (hF₁0 : F₁ 0 = 0) (hZ0 : Z 0 = 1) (hZ₁0 : Z₁ 0 = lam)
    (herror : ∀ t ∈ Icc 0 T, |V t - Z t| + |U t + Z₁ t| ≤ δ * (1 + lam) * F t) :
    0 < V T ∧ ∀ s ∈ Icc 0 1,
      (|U s| + |V s|) / V T ≤ 84 * exp 9 * Θ * exp (-(1 / (4 * σ))) := by
  have hσne : σ ≠ 0 := ne_of_gt hσ
  have hTpos : 0 < T := lt_of_lt_of_le (by positivity : 0 < 1 / σ) hTtarget
  have hT1 : 1 ≤ T := by
    have hh := (div_le_iff₀ hσ).mp hTtarget
    nlinarith only [hh, hσ, hσsmall, hTpos]
  have hx : 1 ≤ σ * T := by
    have hh := (div_le_iff₀ hσ).mp hTtarget
    nlinarith only [hh]
  have hxpos : 0 < σ * T := by positivity
  have hF₁0pos : 0 ≤ F₁ 0 := by rw [hF₁0]
  have hZ₁0pos : 0 ≤ Z₁ 0 := by rw [hZ₁0]; exact hlam
  have hZpos := equation30_global_positive hσ hσsmall (fun t _ => hZ t)
    (fun t _ => hfluxZ t) hZ0 hZ₁0pos T hTpos.le
  have hc := equation30_relative_state_consequences hσ hσsmall hlam hT1 hδ hδsmall
    (fun t _ => hF t) (fun t _ => hZ t) (fun t _ => hfluxF t) (fun t _ => hfluxZ t)
    hF0 hF₁0 hZ0 hZ₁0 (herror T ⟨hTpos.le, le_rfl⟩)
  have hVpos := hc.1
  have hVlower : Z T / 2 ≤ V T := by
    have hh := (abs_le.mp hc.2.1).1
    have hη : 2 * exp 6 * δ ≤ 1 / 2 := by nlinarith only [hδsmall]
    have hratio : (1 : ℝ) / 2 ≤ V T / Z T := by nlinarith only [hh, hη]
    have hm := (le_div_iff₀ hZpos).mp hratio
    nlinarith only [hm]
  have hZlower := equation30_slope_uniform_lower hσ hσsmall hlam
    (fun t _ => hF t) (fun t _ => hZ t) (fun t _ => hfluxF t) (fun t _ => hfluxZ t)
    hF0 hF₁0 hZ0 hZ₁0 T hT1
  have hgrowth := equation30_endpoint_exponential (sq_pos_of_pos hσ)
    (by nlinarith only [hσ, hσsmall] : σ ^ 2 ≤ 1 / 16)
    (fun t _ => hF t) (fun t _ => hfluxF t) hF0 hF₁0pos
  rw [sqrt_sq hσ.le] at hgrowth
  have hpost := (equation30_post_inversion_lower hσ hσsmall
    (fun t _ => hF t) (fun t _ => hfluxF t) hF0 hF₁0pos (σ * T) hx).1
  rw [mul_div_cancel_left₀ T hσne] at hpost
  have hFtarget : exp (1 / (4 * σ)) ≤ (σ * T) * F T := by
    have hh := (div_le_iff₀ hxpos).mp hpost
    nlinarith only [hgrowth, hh]
  have hexp6 : 0 < exp (6 : ℝ) := exp_pos _
  have hZscaled : (1 + lam) * F T ≤ 2 * exp 6 * Z T := by
    have hm := mul_le_mul_of_nonneg_left hZlower (by positivity : 0 ≤ 2 * exp (6 : ℝ))
    have hid : (2 * exp 6) * (((1 + lam) / (2 * exp 6)) * F T) = (1 + lam) * F T := by field_simp
    rw [hid] at hm
    nlinarith only [hm]
  have htarget : (1 + lam) * exp (1 / (4 * σ)) ≤ 4 * exp 6 * (σ * T) * V T := by
    have h₁ := mul_le_mul_of_nonneg_left hFtarget (by positivity : 0 ≤ 1 + lam)
    have h₂ := mul_le_mul_of_nonneg_left hZscaled hxpos.le
    have h₃ := mul_le_mul_of_nonneg_left hVlower (by positivity : 0 ≤ 4 * exp 6 * (σ * T))
    nlinarith only [h₁, h₂, h₃]
  refine ⟨hVpos, ?_⟩
  intro s hs
  have hsT : s ∈ Icc 0 T := ⟨hs.1, hs.2.trans hT1⟩
  have hFpos := equation30_global_positive hσ hσsmall (fun t _ => hF t)
    (fun t _ => hfluxF t) hF0 hF₁0pos s hs.1
  have hFsmall := equation30_zero_slope_prefix_upper hσ hσsmall
    (fun t _ => hF t) (fun t _ => hfluxF t) hF0 hF₁0 s hs
  have hZstate := equation30_relative_propagator hσ hσsmall (by norm_num : (1 : ℝ) ≤ 1)
    (by norm_num : (0 : ℝ) ≤ 0) hs.1 hs.2
    (fun t _ => hF t) (fun t _ => hfluxF t) hF0 hF₁0 (fun t _ => hZ t) (fun t _ => hfluxZ t)
  simp only [hF0, hZ0, hZ₁0, one_pow, div_one, abs_one, abs_of_nonneg hlam, mul_one] at hZstate
  have hδ1 : δ ≤ 1 := by
    have hh : (1 : ℝ) ≤ exp 6 := one_le_exp_iff.mpr (by norm_num)
    have hm := mul_le_mul_of_nonneg_right hh hδ
    nlinarith only [hm, hδsmall]
  have hUtri := abs_add_le (U s + Z₁ s) (-Z₁ s)
  have hVtri := abs_add_le (V s - Z s) (Z s)
  rw [abs_neg] at hUtri
  have hUid : U s + Z₁ s + -Z₁ s = U s := by ring
  have hVid : V s - Z s + Z s = V s := by ring
  rw [hUid] at hUtri
  rw [hVid] at hVtri
  have hnorm : |U s| + |V s| ≤ 21 * exp 3 * (1 + lam) := by
    have herr := herror s hsT
    have hmδ := mul_le_mul_of_nonneg_right hδ1 (by positivity : 0 ≤ (1 + lam) * F s)
    have hmF := mul_le_mul_of_nonneg_right hFsmall (by positivity : 0 ≤ 21 * (1 + lam))
    nlinarith only [hUtri, hVtri, herr, hZstate, hmδ, hmF]
  have hscaled := mul_le_mul_of_nonneg_left htarget
    (by positivity : 0 ≤ 21 * exp 3 * exp (-(1 / (4 * σ))))
  have hexpCancel : exp (-(1 / (4 * σ))) * exp (1 / (4 * σ)) = 1 := by
    rw [← exp_add, neg_add_cancel, exp_zero]
  have hexp9 : exp (9 : ℝ) = exp 3 * exp 6 := by rw [← exp_add]; norm_num
  have hscaled' : 21 * exp 3 * (1 + lam) ≤ 84 * exp 9 * (σ * T) * exp (-(1 / (4 * σ))) * V T := by
    have hid : (21 * exp 3 * exp (-(1 / (4 * σ)))) * ((1 + lam) * exp (1 / (4 * σ))) =
        21 * exp 3 * (1 + lam) := by
      calc
        _ = (21 * exp 3 * (1 + lam)) * (exp (-(1 / (4 * σ))) * exp (1 / (4 * σ))) := by ring
        _ = _ := by rw [hexpCancel, mul_one]
    rw [hid] at hscaled
    rw [hexp9]
    nlinarith only [hscaled]
  have hxΘ : σ * T ≤ Θ := by
    have hm := mul_le_mul_of_nonneg_right (show σ ≤ 1 by linarith) hTpos.le
    nlinarith only [hm, hT]
  have hmΘ := mul_le_mul_of_nonneg_right hxΘ
    (by positivity : 0 ≤ 84 * exp 9 * exp (-(1 / (4 * σ))) * V T)
  apply (div_le_iff₀ hVpos).mpr
  nlinarith only [hnorm, hscaled', hmΘ]

end EulerPacketStage

end
end

end

section

/-!
The pressure numerator of the actual primary is positive.  The scale
condition `1 ≤ σ * Θ` is the source horizon condition; the smallness of the
matrix and ray errors is converted to smallness relative to `σ^2`.
-/

@[expose] public section

noncomputable section

namespace EulerPacketMovingFrame

open EulerSmoothLimit EulerPacketRay EulerPacketGrowth EulerPacketFrameStability
  EulerPacketFrameQuantitative InnerProductSpace

theorem controlled_pressure_ratio_lower
    {A : Fin 3 → Fin 3 → ℝ} {σ Θ K e τ P Q N r : ℝ} {Z Z₁ : ℝ → ℝ}
    (hσ : 0 < σ) (hσsmall : σ ≤ 1 / 4) (hΘ : 1 ≤ Θ) (hK : 1 ≤ K) (he : 0 ≤ e)
    (hσΘ : 1 ≤ σ * Θ) (hτ : 1 ≤ τ) (hτΘ : τ ≤ Θ) (hsmall : 1000000 * K * e * Θ ^ 40 ≤ 1)
    (hZ : ∀ t, 0 ≤ t → HasDerivAt Z (Z₁ t) t)
    (hfluxZ : ∀ t, 0 ≤ t → HasDerivAt (fun s => (1 + (σ ^ 2 * s ^ 2) ^ 2) * Z₁ s)
      (2 * (1 - σ ^ 2 * (σ ^ 2 * t ^ 2)) * Z t) t)
    (hZ0 : Z 0 = 1) (hZ₁0 : 0 ≤ Z₁ 0)
    (hP : |P - σ ^ 2 * τ ^ 2| ≤ 800 * e * Θ ^ 5)
    (hQ : |Q - (-2 * σ ^ 2 * τ)| ≤ 800 * e * Θ ^ 5)
    (hN : |N - 1| ≤ 800 * e * Θ ^ 5)
    (hratio : |r + Z₁ τ / Z τ| ≤ 10 * (K * e * Θ ^ 29))
    (hA : ∀ i j, |A i j - idealVelocityEntry (σ ^ 2) i j| ≤ 3 * e) :
    σ^2/2 ≤ velocityNumerator A P Q N r 1 (velocityThird P Q N r 1) := by
  let ρ := 800*e*Θ^5
  let η := K*e*Θ^29
  let j := 147*e*Θ^4+1600*e*Θ^5
  have hΘ0 : 0 ≤ Θ := by linarith only [hΘ]
  have hΘpos : 0 < Θ := by linarith only [hΘ]
  have hK0 : 0 ≤ K := by linarith only [hK]
  have hτ0 : 0 ≤ τ := by linarith only [hτ]
  have hσ2 : σ^2 ≤ 1 := by nlinarith only [hσ, hσsmall]
  have hρ0 : 0 ≤ ρ := by dsimp [ρ]; positivity
  have hη0 : 0 ≤ η := by dsimp [η]; positivity
  have hj : 0 ≤ j := by dsimp [j]; positivity
  have hρ : ρ ≤ 1/2 := by
    have hp := scaled_power_le hΘ hK he (by decide : 5 ≤ 40)
    dsimp [ρ]
    nlinarith only [hp, hsmall]
  have hη : η ≤ 1/2 := by
    have hp := mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hΘ (by decide : 29 ≤ 40))
      (mul_nonneg hK0 he)
    dsimp [η]
    nlinarith only [hp, hsmall]
  have ht2 : τ^2 ≤ Θ^2 := (sq_le_sq₀ hτ0 hΘ0).mpr hτΘ
  have hP₀ : |σ^2*τ^2| ≤ Θ^2 := by
    rw [abs_of_nonneg (mul_nonneg (sq_nonneg σ) (sq_nonneg τ))]
    nlinarith only [mul_le_mul_of_nonneg_right hσ2 (sq_nonneg τ), ht2]
  have hQ₀ : |-2*σ^2*τ| ≤ 2*Θ^2 := by
    rw [abs_mul, abs_mul, abs_of_nonneg (sq_nonneg σ), abs_of_nonneg hτ0]
    norm_num only [abs_neg, abs_of_nonneg (by norm_num : (0:ℝ) ≤ 2)]
    nlinarith only [mul_le_mul_of_nonneg_right hσ2 hτ0, hτΘ, hΘ, sq_nonneg (Θ-1)]
  obtain ⟨_, hp, hq, hn, hw, _, _⟩ := ray_geometric_bounds (ε := 0) (U := r) (V := 1)
    hΘ hρ0 hρ hP₀ hQ₀ hP hQ hN
  have hβ : |σ^2| ≤ 1 := by simpa only [abs_of_nonneg (sq_nonneg σ)] using hσ2
  have hJ : |velocityNumerator A P Q N r 1 (velocityThird P Q N r 1) -
      ((σ^2*τ^2+σ^2)*1+(-2*σ^2*τ)*r)| ≤ j*(|r|+|1|) := by
    have hh := velocity_numerator_error hΘ hρ0 (show 0 ≤ 3*e by positivity)
      hβ hA hp hq hn hP hQ hN hw
    dsimp [j, ρ] at *
    nlinarith only [hh]
  have hslope := equation30_primary_logderivative_bound hσ hσsmall hZ hfluxZ hZ0 hZ₁0 τ hτ
  have hr₀ : |-Z₁ τ/Z τ| ≤ 4 := by simpa only [neg_div, abs_neg] using hslope
  have hr' : |r/1-(-Z₁ τ/Z τ)| ≤ 10*η := by
    simpa only [div_one, neg_div, sub_neg_eq_add] using hratio
  have herr := pressure_ratio_error hΘ hη0 hη hj (by norm_num : (0:ℝ) < 1) hQ₀ hr₀ hr' hJ
  simp only [div_one] at herr
  have herrorSmall : 10*j+20*Θ^2*η ≤ σ^2/2 := by
    have hp6 := scaled_power_le hΘ hK he (by decide : 6 ≤ 40)
    have hp7 := scaled_power_le hΘ hK he (by decide : 7 ≤ 40)
    have hp33 := mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hΘ (by decide : 33 ≤ 40))
      (mul_nonneg hK0 he)
    have hs : (10*j+20*Θ^2*η)*Θ^2 ≤ 1/2 := by
      dsimp [j, η]
      nlinarith only [hp6, hp7, hp33, hsmall]
    have hστ : 1 ≤ σ^2*Θ^2 := by
      have hh := mul_le_mul hσΘ hσΘ (by norm_num : (0:ℝ) ≤ 1) (by positivity : 0 ≤ σ*Θ)
      nlinarith only [hh]
    apply (mul_le_mul_iff_right₀ (sq_pos_of_pos hΘpos)).mp
    nlinarith only [hs, hστ]
  have hZpos := equation30_global_positive hσ hσsmall hZ hfluxZ hZ0 hZ₁0 τ hτ0
  have hnum := equation30_ideal_numerator_positive hσ hσsmall hZ hfluxZ hZ0 hZ₁0 τ hτ0
  have hideal : σ^2 ≤ σ^2*τ^2+σ^2+(-2*σ^2*τ)*(-Z₁ τ/Z τ) := by
    apply (mul_le_mul_iff_right₀ hZpos).mp
    have hz : Z τ ≠ 0 := ne_of_gt hZpos
    have hid : (σ^2*τ^2+σ^2+(-2*σ^2*τ)*(-Z₁ τ/Z τ))*Z τ =
        (σ^2*τ^2+σ^2)*Z τ+2*σ^2*τ*Z₁ τ := by field_simp
    nlinarith only [hid, hnum]
  linarith only [(abs_le.mp herr).1, herrorSmall, hideal]

/-- Source (33), stated for the actual physical ray and velocity. -/
theorem physical_pressure_positive_order40 (M : Space →L[ℝ] Space) (m v r w : ℝ → Space)
    {s₀ t₀ a ε τ σ Θ K e : ℝ} {Z Z₁ : ℝ → ℝ}
    (ha : 0 < a) (hs₀ : 0 < s₀) (hε : 0 < ε)
    (hm : m (physicalTime t₀ a ε τ) ≠ 0) (hv : v (physicalTime t₀ a ε τ) ≠ 0)
    (hmv : ⟪m (physicalTime t₀ a ε τ), v (physicalTime t₀ a ε τ)⟫_ℝ = 0)
    (hrw : ⟪r (physicalTime t₀ a ε τ), w (physicalTime t₀ a ε τ)⟫_ℝ = 0)
    (hV : 0 < scaledVelocity m v w t₀ a ε τ 1)
    (hσ : 0 < σ) (hσsmall : σ ≤ 1 / 4) (hΘ : 1 ≤ Θ) (hK : 1 ≤ K) (he : 0 ≤ e)
    (hσΘ : 1 ≤ σ * Θ) (hτ : 1 ≤ τ) (hτΘ : τ ≤ Θ) (hsmall : 1000000 * K * e * Θ ^ 40 ≤ 1)
    (hZ : ∀ t, 0 ≤ t → HasDerivAt Z (Z₁ t) t)
    (hfluxZ : ∀ t, 0 ≤ t → HasDerivAt (fun s => (1 + (σ ^ 2 * s ^ 2) ^ 2) * Z₁ s)
      (2 * (1 - σ ^ 2 * (σ ^ 2 * t ^ 2)) * Z t) t)
    (hZ0 : Z 0 = 1) (hZ₁0 : 0 ≤ Z₁ 0)
    (hP : |scaledRay m v r s₀ t₀ a ε τ 0 - σ ^ 2 * τ ^ 2| ≤ 800 * e * Θ ^ 5)
    (hQ : |scaledRay m v r s₀ t₀ a ε τ 1 - (-2 * σ ^ 2 * τ)| ≤ 800 * e * Θ ^ 5)
    (hN : |scaledRay m v r s₀ t₀ a ε τ 2 - 1| ≤ 800 * e * Θ ^ 5)
    (hratio : |scaledVelocity m v w t₀ a ε τ 0 / scaledVelocity m v w t₀ a ε τ 1 + Z₁ τ / Z τ|
      ≤ 10 * (K * e * Θ ^ 29))
    (hA : ∀ i j, |scaledAction M m v a ε (physicalTime t₀ a ε τ) i j -
      idealVelocityEntry (σ ^ 2) i j| ≤ 3 * e) :
    s₀*a*scaledVelocity m v w t₀ a ε τ 1*(σ^2/2) ≤
        ⟪r (physicalTime t₀ a ε τ), M (w (physicalTime t₀ a ε τ))⟫_ℝ ∧
      0 < ⟪r (physicalTime t₀ a ε τ), M (w (physicalTime t₀ a ε τ))⟫_ℝ := by
  let R := scaledRay m v r s₀ t₀ a ε τ
  let V := scaledVelocity m v w t₀ a ε τ
  have hp := scaled_power_le hΘ hK he (by decide : 5 ≤ 40)
  have hρ : 800*e*Θ^5 ≤ 1/2 := by nlinarith only [hp, hsmall]
  have hNne : R 2 ≠ 0 := by
    have hh := (abs_le.mp hN).1
    change -(800*e*Θ^5) ≤ R 2-1 at hh
    linarith only [hh, hρ]
  have hpair := scaled_pairing_zero m v r w (ne_of_gt hs₀) (ne_of_gt hε) hm hv hmv hrw
  have hthird := thirdRatio_from_pairing R V hNne (ne_of_gt hV) hpair
  have hj := controlled_pressure_ratio_lower hσ hσsmall hΘ hK he hσΘ hτ hτΘ hsmall
    hZ hfluxZ hZ0 hZ₁0 hP hQ hN hratio hA
  rw [← hthird] at hj
  have hid := physical_pressure_ratio M m v r w (ne_of_gt ha) (ne_of_gt hs₀) (ne_of_gt hε)
    hm hv hmv (ne_of_gt hV)
  rw [hid]
  have hc : 0 < s₀*a*V 1 := mul_pos (mul_pos hs₀ ha) hV
  exact ⟨mul_le_mul_of_nonneg_left hj hc.le, mul_pos hc (lt_of_lt_of_le (by positivity) hj)⟩

end EulerPacketMovingFrame

end
end

end

section

/-!
Early physical amplitudes are exponentially small relative to the center
target amplitude.  The initial scalar slope cancels, including for
neighboring initial data controlled by the common reference.
-/

@[expose] public section

noncomputable section

namespace EulerPacketMovingFrame

open Set Real EulerSmoothLimit EulerPacketRay EulerPacketStage InnerProductSpace

theorem early_neighbor_state_bound {α : Type*} (center : α) (U V : α → ℝ → ℝ)
    {σ Θ T lam δ : ℝ} {F F₁ Z Z₁ : ℝ → ℝ}
    (hσ : 0 < σ) (hσsmall : σ ≤ 1 / 4) (hΘ : 1 ≤ Θ) (hT : T ≤ Θ)
    (hTtarget : 1 / σ ≤ T) (hlam : 0 ≤ lam) (hδ : 0 ≤ δ) (hδsmall : 4 * exp 6 * δ ≤ 1)
    (hF : ∀ t, HasDerivAt F (F₁ t) t) (hZ : ∀ t, HasDerivAt Z (Z₁ t) t)
    (hfluxF : ∀ t, HasDerivAt (fun s => (1 + (σ ^ 2 * s ^ 2) ^ 2) * F₁ s)
      (2 * (1 - σ ^ 2 * (σ ^ 2 * t ^ 2)) * F t) t)
    (hfluxZ : ∀ t, HasDerivAt (fun s => (1 + (σ ^ 2 * s ^ 2) ^ 2) * Z₁ s)
      (2 * (1 - σ ^ 2 * (σ ^ 2 * t ^ 2)) * Z t) t)
    (hF0 : F 0 = 1) (hF₁0 : F₁ 0 = 0) (hZ0 : Z 0 = 1) (hZ₁0 : Z₁ 0 = lam)
    (herror : ∀ ξ t, t ∈ Icc 0 T → |V ξ t - Z t| + |U ξ t + Z₁ t| ≤ δ * (1 + lam) * F t) :
    0 < V center T ∧ ∀ ξ s, s ∈ Icc 0 1 →
      (|U ξ s|+|V ξ s|)/V center T ≤ 84*exp 9*Θ*exp (-(1/(4*σ))) := by
  have hcenter := early_forward_exponential_suppression hσ hσsmall hΘ hT hTtarget hlam hδ hδsmall
    hF hZ hfluxF hfluxZ hF0 hF₁0 hZ0 hZ₁0 (herror center)
  have hTpos : 0 < T := lt_of_lt_of_le (by positivity : 0 < 1/σ) hTtarget
  have hTnot : ¬T ≤ 1 := by
    have hh := (div_le_iff₀ hσ).mp hTtarget
    nlinarith only [hh, hσ, hσsmall, hTpos]
  refine ⟨hcenter.1, ?_⟩
  intro ξ s hs
  let U' : ℝ → ℝ := fun t => if t ≤ 1 then U ξ t else U center t
  let V' : ℝ → ℝ := fun t => if t ≤ 1 then V ξ t else V center t
  have he : ∀ t ∈ Icc 0 T, |V' t-Z t|+|U' t+Z₁ t| ≤ δ*(1+lam)*F t := by
    intro t ht
    by_cases h : t ≤ 1
    · simpa only [U', V', ite_eq_left h] using herror ξ t ht
    · simpa only [U', V', ite_eq_right h] using herror center t ht
  have hh := early_forward_exponential_suppression hσ hσsmall hΘ hT hTtarget hlam hδ hδsmall
    hF hZ hfluxF hfluxZ hF0 hF₁0 hZ0 hZ₁0 he
  simpa only [U', V', ite_eq_left hs.2, ite_eq_right hTnot] using hh.2 s hs

/-- The early part of source (36) for actual Euclidean norm products.
The estimate is uniform over neighboring labels and over the nonnegative
initial slope of the common scalar reference. -/
theorem early_physical_size_suppression {α : Type*} (center : α)
    (m v : ℝ → Space) (r w : α → ℝ → Space)
    {s₀ t₀ a ε σ Θ T lam δ ρ : ℝ} {F F₁ Z Z₁ : ℝ → ℝ}
    (hs₀ : 0 < s₀) (hε : 0 < ε) (hε1 : ε ≤ 1)
    (hσ : 0 < σ) (hσsmall : σ ≤ 1 / 4) (hΘ : 1 ≤ Θ) (hT : T ≤ Θ)
    (hTtarget : 1 / σ ≤ T) (hlam : 0 ≤ lam) (hδ : 0 ≤ δ) (hδsmall : 4 * exp 6 * δ ≤ 1)
    (hρ0 : 0 ≤ ρ) (hρ : ρ ≤ 1 / 2)
    (hm : ∀ τ ∈ Icc 0 T, m (physicalTime t₀ a ε τ) ≠ 0)
    (hv : ∀ τ ∈ Icc 0 T, v (physicalTime t₀ a ε τ) ≠ 0)
    (hmv : ∀ τ ∈ Icc 0 T, ⟪m (physicalTime t₀ a ε τ), v (physicalTime t₀ a ε τ)⟫_ℝ = 0)
    (hrw : ∀ ξ τ, τ ∈ Icc 0 T → ⟪r ξ (physicalTime t₀ a ε τ), w ξ (physicalTime t₀ a ε τ)⟫_ℝ = 0)
    (hP : ∀ ξ τ, τ ∈ Icc 0 T → |scaledRay m v (r ξ) s₀ t₀ a ε τ 0 - σ ^ 2 * τ ^ 2| ≤ ρ)
    (hQ : ∀ ξ τ, τ ∈ Icc 0 T → |scaledRay m v (r ξ) s₀ t₀ a ε τ 1 - (-2 * σ ^ 2 * τ)| ≤ ρ)
    (hN : ∀ ξ τ, τ ∈ Icc 0 T → |scaledRay m v (r ξ) s₀ t₀ a ε τ 2 - 1| ≤ ρ)
    (hF : ∀ t, HasDerivAt F (F₁ t) t) (hZ : ∀ t, HasDerivAt Z (Z₁ t) t)
    (hfluxF : ∀ t, HasDerivAt (fun s => (1 + (σ ^ 2 * s ^ 2) ^ 2) * F₁ s)
      (2 * (1 - σ ^ 2 * (σ ^ 2 * t ^ 2)) * F t) t)
    (hfluxZ : ∀ t, HasDerivAt (fun s => (1 + (σ ^ 2 * s ^ 2) ^ 2) * Z₁ s)
      (2 * (1 - σ ^ 2 * (σ ^ 2 * t ^ 2)) * Z t) t)
    (hF0 : F 0 = 1) (hF₁0 : F₁ 0 = 0) (hZ0 : Z 0 = 1) (hZ₁0 : Z₁ 0 = lam)
    (herror : ∀ ξ τ, τ ∈ Icc 0 T →
      |scaledVelocity m v (w ξ) t₀ a ε τ 1 - Z τ| +
        |scaledVelocity m v (w ξ) t₀ a ε τ 0 + Z₁ τ| ≤ δ * (1 + lam) * F τ) :
    0 < ‖r center (physicalTime t₀ a ε T)‖*‖w center (physicalTime t₀ a ε T)‖ ∧
    ∀ ξ τ, τ ∈ Icc 0 1 →
      (‖r ξ (physicalTime t₀ a ε τ)‖*‖w ξ (physicalTime t₀ a ε τ)‖)/
          (‖r center (physicalTime t₀ a ε T)‖*‖w center (physicalTime t₀ a ε T)‖) ≤
        8232*exp 9*Θ^5*exp (-(1/(4*σ))) := by
  have hstate := early_neighbor_state_bound center
    (fun ξ τ => scaledVelocity m v (w ξ) t₀ a ε τ 0)
    (fun ξ τ => scaledVelocity m v (w ξ) t₀ a ε τ 1)
    hσ hσsmall hΘ hT hTtarget hlam hδ hδsmall hF hZ hfluxF hfluxZ hF0 hF₁0 hZ0 hZ₁0 herror
  have hTpos : 0 < T := lt_of_lt_of_le (by positivity : 0 < 1/σ) hTtarget
  have hT1 : 1 ≤ T := by
    have hh := (div_le_iff₀ hσ).mp hTtarget
    nlinarith only [hh, hσ, hσsmall, hTpos]
  have hTT : T ∈ Icc 0 T := ⟨hTpos.le, le_rfl⟩
  have hNt : 1/2 ≤ scaledRay m v (r center) s₀ t₀ a ε T 2 := by
    have hh := (abs_le.mp (hN center T hTT)).1
    linarith only [hh, hρ]
  have htarget := physical_size_ge_second m v (r center) (w center) hs₀ (ne_of_gt hε)
    (hm T hTT) (hv T hTT) (hmv T hTT) hNt hstate.1.le
  have htargetpos : 0 < ‖r center (physicalTime t₀ a ε T)‖*‖w center (physicalTime t₀ a ε T)‖ :=
    lt_of_lt_of_le (div_pos (mul_pos hs₀ hstate.1) (by norm_num)) htarget
  refine ⟨htargetpos, ?_⟩
  intro ξ τ hτ
  have hτT : τ ∈ Icc 0 T := ⟨hτ.1, hτ.2.trans hT1⟩
  have hΘ2 : 1 ≤ Θ^2 := one_le_pow₀ hΘ
  have hσ2 : σ^2 ≤ 1 := by nlinarith only [hσ, hσsmall]
  have hτ2 : τ^2 ≤ 1 := by nlinarith only [hτ.1, hτ.2]
  have hP₀ : |σ^2*τ^2| ≤ Θ^2 := by
    rw [abs_of_nonneg (by positivity : 0 ≤ σ^2*τ^2)]
    have hh := mul_le_mul hσ2 hτ2 (sq_nonneg τ) (by norm_num : (0:ℝ) ≤ 1)
    nlinarith only [hh, hΘ2]
  have hQ₀ : |-2*σ^2*τ| ≤ 2*Θ^2 := by
    rw [abs_mul, abs_mul, abs_of_nonneg (sq_nonneg σ), abs_of_nonneg hτ.1]
    norm_num only [abs_neg, abs_of_nonneg (by norm_num : (0:ℝ) ≤ 2)]
    have hh := mul_le_mul hσ2 hτ.2 hτ.1 (by norm_num : (0:ℝ) ≤ 1)
    nlinarith only [hh, hΘ2]
  have hupper := physical_size_le_scaled_state m v (r ξ) (w ξ) hs₀ hε hε1
    (hm τ hτT) (hv τ hτT) (hmv τ hτT) (hrw ξ τ hτT) hΘ hρ0 hρ hP₀ hQ₀
    (hP ξ τ hτT) (hQ ξ τ hτT) (hN ξ τ hτT)
  have hstates := (div_le_iff₀ hstate.1).mp (hstate.2 ξ τ hτ)
  have hs := mul_le_mul_of_nonneg_left hstates (show 0 ≤ 49*s₀*Θ^4 by positivity)
  have ht := mul_le_mul_of_nonneg_left htarget
    (show 0 ≤ 8232*exp 9*Θ^5*exp (-(1/(4*σ))) by positivity)
  apply (div_le_iff₀ htargetpos).mpr
  nlinarith only [hupper, hs, ht]

end EulerPacketMovingFrame

end
end

end

@[expose] public section

noncomputable section

namespace EulerPacketMovingFrame

open Set Real EulerSmoothLimit EulerPacketRay InnerProductSpace PhysicalGeometryData

/-- Physical geometry conclusion data, collecting `initial_values`, `F_derivative`,
`Z_derivative`, `F_flux`, `Z_flux`, `ray_control` and their compatibility conditions. -/
structure PhysicalGeometryConclusion {α : Type*} (D : PhysicalGeometryData α)
    (F F₁ Z Z₁ : ℝ → ℝ) : Prop where
  initial_values : F 0 = 1 ∧ F₁ 0 = 0 ∧ Z 0 = 1 ∧ Z₁ 0 = D.lam
  F_derivative : ∀ t, HasDerivAt F (F₁ t) t
  Z_derivative : ∀ t, HasDerivAt Z (Z₁ t) t
  F_flux : ∀ t, HasDerivAt (fun s => (1+(D.σ^2*s^2)^2)*F₁ s)
    (2*(1-D.σ^2*(D.σ^2*t^2))*F t) t
  Z_flux : ∀ t, HasDerivAt (fun s => (1+(D.σ^2*s^2)^2)*Z₁ s)
    (2*(1-D.σ^2*(D.σ^2*t^2))*Z t) t
  ray_control : ∀ ξ τ, τ ∈ Icc 0 D.H →
    norm3 (D.ray ξ τ 0-D.σ^2*τ^2) (D.ray ξ τ 1+2*D.σ^2*τ) (D.ray ξ τ 2-1) ≤
      800*D.error*D.Θ^5 ∧ 1/2 ≤ D.ray ξ τ 2 ∧
      ⟪D.r ξ (D.time τ),D.w ξ (D.time τ)⟫_ℝ = 0
  state_error : ∀ ξ τ, τ ∈ Icc 0 D.H →
    |D.velocity ξ τ 1-Z τ|+|D.velocity ξ τ 0+Z₁ τ| ≤ 400000000*D.error*D.Θ^29*(1+D.lam)*F τ
  relative_error : ∀ ξ τ, τ ∈ Icc 1 D.H →
    0 < D.velocity ξ τ 1 ∧ |D.velocity ξ τ 1/Z τ-1| ≤ neighborStabilityConstant*D.error*D.Θ^29 ∧
      |D.velocity ξ τ 0/D.velocity ξ τ 1+Z₁ τ/Z τ| ≤ 10*(neighborStabilityConstant*D.error*D.Θ^29)
  positive_pressure : ∀ ξ τ, τ ∈ Icc 1 D.H →
    0 < ⟪D.r ξ (D.time τ),(D.M ξ (D.time τ)) (D.w ξ (D.time τ))⟫_ℝ
  target_positive : 0 < D.targetSize
  target_growth : D.s₀*exp (1/(4*D.σ)) ≤ 4*D.Θ*D.targetSize
  horizon_size : ∀ ξ τ, τ ∈ Icc 1 D.H → D.size ξ τ ≤ 64*exp 6*D.targetSize
  early_size : ∀ ξ τ, τ ∈ Icc 0 1 →
    D.size ξ τ/D.targetSize ≤ 8232*exp 9*D.Θ^5*exp (-(1/(4*D.σ)))
  next_frame :
    |D.nextCoupling/D.a-1| ≤
        D.y^4+D.σ^2*D.y^2+8*D.σ*D.y^3+30000000*neighborStabilityConstant*D.error*D.Θ^40 ∧
    |(D.y⁻¹)^2*D.nextTilt-1| ≤ 1500*D.σ+30000000*neighborStabilityConstant*D.error*D.Θ^40
  compression_bound : D.nextCompression ≤ -(D.targetShear*D.ε)/(10*D.target)+3*(D.G+D.d)
  compression_negative : D.nextCompression < 0
  amplitude_nonneg : 0 ≤ D.amplitude
  amplitude_normalization : D.amplitude*D.targetSize = D.δ*D.hchild
  amplitude_exponential : D.amplitude ≤ (4*D.Θ*D.δ*D.hchild/D.s₀)*exp (-(1/(4*D.σ)))
  amplitude_profile : ∀ τ ∈ Icc 0 D.H, D.amplitude*Z τ ≤ 8*exp 6*D.δ*D.hchild/D.s₀
  amplitude_profile_sup : sSup ((fun τ => D.amplitude*Z τ) '' Icc 0 D.H) ≤ 8*exp 6*D.δ*D.hchild/D.s₀
  physical_profile_continuous :
    ContinuousOn (physicalProfile Z D.t₀ D.a D.ε) (Icc D.t₀ (D.time D.H))
  physical_profile_positive : ∀ t ∈ Icc D.t₀ (D.time D.H), 0 < physicalProfile Z D.t₀ D.a D.ε t
  tangent_propagator : ∀ ξ (u : ℝ → Space),
    (∀ t ∈ D.S, HasDerivWithinAt u
      (-(D.M ξ t) (u t)+(2*⟪D.r ξ t,(D.M ξ t) (u t)⟫_ℝ/‖D.r ξ t‖^2) • D.r ξ t) D.S t) →
    ⟪D.r ξ D.t₀,u D.t₀⟫_ℝ = 0 →
    ∀ s t, s ∈ Icc D.t₀ (D.time D.H) → t ∈ Icc D.t₀ (D.time D.H) → s ≤ t →
      ‖u t‖ ≤ (560*D.Θ^10/D.ε) *
        (physicalProfile Z D.t₀ D.a D.ε t/physicalProfile Z D.t₀ D.a D.ε s)*‖u s‖

theorem PhysicalGeometryData.exists_geometry {α : Type*} (D : PhysicalGeometryData α) :
    ∃ F F₁ Z Z₁ : ℝ → ℝ, PhysicalGeometryConclusion D F F₁ Z Z₁ := by
  have hK : 1 ≤ neighborStabilityConstant :=
    (by norm_num : (1:ℝ) ≤ 1000000000).trans neighborStabilityConstant_ge
  obtain ⟨F, F₁, Z, Z₁, hF0, hF₁0, hZ0, hZ₁0, hF, hZ, hfluxF, hfluxZ, hray, herr, hrel, _⟩ :=
    physical_family_amplification_and_size D.center D.sigma_pos D.sigma_small D.horizon_one
        D.horizon_le_Theta
      D.a_lower D.epsilon_pos D.Theta_lower D.G_lower D.d_nonneg D.ray_scale_pos D.slope_nonneg
          D.small
      D.time_maps D.M_continuous D.B_derivative D.old_ray_equation D.old_velocity_equation
      D.ray_equation D.velocity_equation D.old_ray_nonzero D.old_velocity_nonzero D.old_tangent
      D.initial_tangent D.B_bound D.B_derivative_bound D.E_bound D.parent_decomposition
      D.initial_coupling D.initial_tilt D.initial_shear D.initial_ray_error D.initial_velocity_error
  have hZ₁pos : 0 ≤ Z₁ 0 := by rw [hZ₁0]; exact D.slope_nonneg
  have hZpos := EulerPacketGrowth.equation30_global_positive D.sigma_pos D.sigma_small
    (fun t _ => hZ t) (fun t _ => hfluxZ t) hZ0 hZ₁pos
  have hsub : Icc (1:ℝ) D.H ⊆ Icc 0 D.H := fun _ ht => ⟨by linarith only [ht.1], ht.2⟩
  have htarget : D.target ∈ Icc 0 D.H := ⟨D.target_pos.le, D.target_le_horizon⟩
  have htarget1 : D.target ∈ Icc 1 D.H := ⟨D.target_one, D.target_le_horizon⟩
  have hcoords (ξ : α) (τ : ℝ) (hτ : τ ∈ Icc 0 D.H) :
      |D.ray ξ τ 0-D.σ^2*τ^2| ≤ 800*D.error*D.Θ^5 ∧
      |D.ray ξ τ 1-(-2*D.σ^2*τ)| ≤ 800*D.error*D.Θ^5 ∧
      |D.ray ξ τ 2-1| ≤ 800*D.error*D.Θ^5 := by
    have hh : norm3 (D.ray ξ τ 0-D.σ^2*τ^2) (D.ray ξ τ 1+2*D.σ^2*τ) (D.ray ξ τ 2-1) ≤
        800*D.error*D.Θ^5 := (hray ξ τ hτ).1
    rw [show D.ray ξ τ 1-(-2*D.σ^2*τ) = D.ray ξ τ 1+2*D.σ^2*τ by ring]
    dsimp [norm3] at hh
    constructor
    · linarith only [hh, abs_nonneg (D.ray ξ τ 1+2*D.σ^2*τ), abs_nonneg (D.ray ξ τ 2-1)]
    constructor
    · linarith only [hh, abs_nonneg (D.ray ξ τ 0-D.σ^2*τ^2), abs_nonneg (D.ray ξ τ 2-1)]
    · linarith only [hh, abs_nonneg (D.ray ξ τ 0-D.σ^2*τ^2), abs_nonneg (D.ray ξ τ 1+2*D.σ^2*τ)]
  have htcoords := hcoords D.center D.target htarget
  have htstate := hrel D.center D.target htarget1
  have htframes := D.target_time_mem
  have hsizeTarget := physical_ideal_size_comparison_order40 D.m D.v (D.r D.center) (D.w D.center)
    D.ray_scale_pos D.epsilon_pos D.sigma_pos D.sigma_small
    (D.old_ray_nonzero _ htframes) (D.old_velocity_nonzero _ htframes) (D.old_tangent _ htframes)
    (hray D.center D.target htarget).2.2 D.Theta_lower hK D.error_nonneg D.epsilon_le_error D.small
    D.target_one D.target_le_Theta (fun t _ => hZ t) (fun t _ => hfluxZ t) hZ0 hZ₁pos
    htcoords.1 htcoords.2.1 htcoords.2.2 htstate.2.1 htstate.2.2
  have hgrowth := physical_target_exponential_lower D.m D.v (D.r D.center) (D.w D.center)
    D.ray_scale_pos (ne_of_gt D.epsilon_pos) D.sigma_pos D.sigma_small D.target_from_sigma
        D.target_le_Theta
    (D.old_ray_nonzero _ htframes) (D.old_velocity_nonzero _ htframes) (D.old_tangent _ htframes)
    (hray D.center D.target htarget).2.1 (htstate.2.1.trans D.relative_error_small)
    (fun t _ => hZ t) (fun t _ => hfluxZ t) hZ0 hZ₁pos
  have hsize := physical_horizon_size_bound D.center (fun _ => D.m) (fun _ => D.v) D.r D.w
    D.ray_scale_pos D.epsilon_pos D.sigma_pos D.sigma_small D.target_one D.target_le_horizon
        D.horizon_le_Theta
    D.short_extension D.Theta_lower hK D.error_nonneg D.epsilon_le_error D.small
    (fun _ τ hτ => D.old_ray_nonzero _ (D.time_mem (hsub hτ)))
    (fun _ τ hτ => D.old_velocity_nonzero _ (D.time_mem (hsub hτ)))
    (fun _ τ hτ => D.old_tangent _ (D.time_mem (hsub hτ)))
    (fun ξ τ hτ => (hray ξ τ (hsub hτ)).2.2)
    (fun t _ => hZ t) (fun t _ => hfluxZ t) hZ0 hZ₁pos
    (fun ξ τ hτ => (hcoords ξ τ (hsub hτ)).1)
    (fun ξ τ hτ => (hcoords ξ τ (hsub hτ)).2.1)
    (fun ξ τ hτ => (hcoords ξ τ (hsub hτ)).2.2)
    (fun ξ τ hτ => (hrel ξ τ hτ).2.1) (fun ξ τ hτ => (hrel ξ τ hτ).2.2)
  have htoH : Icc (0:ℝ) D.target ⊆ Icc 0 D.H := fun _ ht => ⟨ht.1, ht.2.trans D.target_le_horizon⟩
  have hearly := early_physical_size_suppression D.center D.m D.v D.r D.w
    D.ray_scale_pos D.epsilon_pos D.epsilon_le_one D.sigma_pos D.sigma_small D.Theta_lower
        D.target_le_Theta
    D.target_from_sigma D.slope_nonneg (show 0 ≤ 400000000*D.error*D.Θ^29 by
        positivity [D.error_nonneg, D.Theta_pos])
    D.scalar_error_small (show 0 ≤ 800*D.error*D.Θ^5 by
        positivity [D.error_nonneg, D.Theta_pos]) D.ray_error_small
    (fun τ hτ => D.old_ray_nonzero _ (D.time_mem (htoH hτ)))
    (fun τ hτ => D.old_velocity_nonzero _ (D.time_mem (htoH hτ)))
    (fun τ hτ => D.old_tangent _ (D.time_mem (htoH hτ)))
    (fun ξ τ hτ => (hray ξ τ (htoH hτ)).2.2)
    (fun ξ τ hτ => (hcoords ξ τ (htoH hτ)).1)
    (fun ξ τ hτ => (hcoords ξ τ (htoH hτ)).2.1)
    (fun ξ τ hτ => (hcoords ξ τ (htoH hτ)).2.2)
    hF hZ hfluxF hfluxZ hF0 hF₁0 hZ0 hZ₁0 (fun ξ τ hτ => herr ξ τ (htoH hτ))
  have hPeq : D.σ^2*D.target^2 = (D.y⁻¹)^2 := by
    dsimp [target]
    field_simp [ne_of_gt D.sigma_pos]
  have hQeq : 2*D.σ^2*D.target = 2*D.σ*D.y⁻¹ := by
    dsimp [target]
    field_simp [ne_of_gt D.sigma_pos]
  have hframeP : |D.ray D.center D.target 0-(D.y⁻¹)^2| ≤ 800*D.error*D.Θ^5 := by
    simpa only [hPeq] using htcoords.1
  have hframeQ : |D.ray D.center D.target 1+2*D.σ*D.y⁻¹| ≤ 800*D.error*D.Θ^5 := by
    simpa only [neg_mul, sub_neg_eq_add, hQeq] using htcoords.2.1
  have hframe := physical_frame_renewal_order40 (D.M D.center D.targetTime) D.m D.v (D.r D.center)
      (D.w D.center)
    (ne_of_gt D.a_pos) D.ray_scale_pos D.epsilon_pos
    (D.old_ray_nonzero _ htframes) (D.old_velocity_nonzero _ htframes) (D.old_tangent _ htframes)
    (hray D.center D.target htarget).2.2 htstate.1 D.sigma_pos D.sigma_small D.y_pos D.y_small
    D.Theta_lower hK D.error_nonneg D.epsilon_le_error D.target_le_Theta D.small
    (fun t _ => hZ t) (fun t _ => hfluxZ t) hZ0 hZ₁pos hframeP hframeQ htcoords.2.2 htstate.2.2
    (D.action_error D.center htarget)
  have hcompressQ : |D.ray D.center D.target 1+2*D.σ^2*D.target| ≤ 800*D.error*D.Θ^5 := by
    simpa only [neg_mul, sub_neg_eq_add] using htcoords.2.1
  have hcomp := physical_target_compression (D.B D.targetTime) (D.M D.center D.targetTime)
    (D.E D.center D.targetTime) D.targetShear D.m D.v (D.r D.center)
    (ne_of_gt D.ray_scale_pos) D.epsilon_pos
    (D.old_ray_nonzero _ htframes) (D.old_velocity_nonzero _ htframes) (D.old_tangent _ htframes)
    (D.parent_decomposition D.center _ htframes) (sq_pos_of_pos D.sigma_pos)
    (by nlinarith only [D.sigma_pos, D.sigma_small] : D.σ^2 ≤ 1) D.target_pos D.target_le_Theta
    D.Theta_lower hK D.error_nonneg D.epsilon_le_error D.target_shear_pos.le D.small D.target_scale
    htcoords.1 hcompressQ htcoords.2.2
  have hampProfile := primaryAmplitude_profile_bound (D.r D.center) (D.w D.center)
    (targetTime := D.targetTime) D.delta_nonneg D.child_nonneg D.ray_scale_pos D.sigma_pos
        D.sigma_small
    D.target_one D.short_extension (fun t _ => hZ t) (fun t _ => hfluxZ t) hZ0 hZ₁pos hsizeTarget.1
  have hzcont : ContinuousOn Z (Icc 0 D.H) := fun t ht => (hZ t).continuousAt.continuousWithinAt
  refine ⟨F, F₁, Z, Z₁, {
    initial_values := ⟨hF0, hF₁0, hZ0, hZ₁0⟩
    F_derivative := hF
    Z_derivative := hZ
    F_flux := hfluxF
    Z_flux := hfluxZ
    ray_control := hray
    state_error := herr
    relative_error := hrel
    positive_pressure := ?_
    target_positive := hgrowth.1
    target_growth := hgrowth.2
    horizon_size := hsize
    early_size := hearly.2
    next_frame := hframe
    compression_bound := ?_
    compression_negative := hcomp.2 D.compression_domination
    amplitude_nonneg := primaryAmplitude_nonneg _ _ _ _ _ D.delta_nonneg D.child_nonneg
    amplitude_normalization := primaryAmplitude_target_identity _ _ _ _ _ hgrowth.1
    amplitude_exponential := primaryAmplitude_exponential_bound _ _ D.delta_nonneg D.child_nonneg
        D.ray_scale_pos D.Theta_pos hgrowth.2
    amplitude_profile := hampProfile
    amplitude_profile_sup := ?_
    physical_profile_continuous := physicalProfile_continuousOn D.a_pos D.epsilon_pos hzcont
    physical_profile_positive := physicalProfile_positive D.a_pos D.epsilon_pos (fun t ht => hZpos
        t ht.1)
    tangent_propagator := ?_ }⟩
  · intro ξ τ hτ
    have hp := hcoords ξ τ (hsub hτ)
    have hv := hrel ξ τ hτ
    exact (physical_pressure_positive_order40 (D.M ξ (D.time τ)) D.m D.v (D.r ξ) (D.w ξ)
      D.a_pos D.ray_scale_pos D.epsilon_pos
      (D.old_ray_nonzero _ (D.time_mem (hsub hτ))) (D.old_velocity_nonzero _ (D.time_mem (hsub hτ)))
      (D.old_tangent _ (D.time_mem (hsub hτ))) (hray ξ τ (hsub hτ)).2.2 hv.1
      D.sigma_pos D.sigma_small D.Theta_lower hK D.error_nonneg D.sigma_Theta hτ.1
      (hτ.2.trans D.horizon_le_Theta) D.small (fun t _ => hZ t) (fun t _ => hfluxZ t) hZ0 hZ₁pos
      hp.1 hp.2.1 hp.2.2 hv.2.2 (D.action_error ξ (hsub hτ))).2
  · have hn := add_le_add (D.B_bound _ htframes) (D.E_bound D.center _ htframes)
    exact hcomp.1.trans (by nlinarith only [hn])
  · apply csSup_le
    · exact ⟨D.amplitude*Z 0, 0, ⟨le_rfl, D.horizon_pos.le⟩, rfl⟩
    · rintro _ ⟨τ, hτ, rfl⟩
      exact hampProfile τ hτ
  · intro ξ u hu hutangent
    have hp := physical_tangent_propagator D.sigma_pos D.sigma_small D.horizon_pos
        D.horizon_le_Theta
      D.a_lower D.epsilon_pos D.Theta_lower D.G_lower D.d_nonneg (ne_of_gt D.ray_scale_pos)
      D.propagator_small D.time_maps (D.M_continuous ξ) D.B_derivative D.old_ray_equation
          D.old_velocity_equation
      (D.ray_equation ξ) hu D.old_ray_nonzero D.old_velocity_nonzero D.old_tangent hutangent
      D.B_bound D.B_derivative_bound (D.E_bound ξ) (D.parent_decomposition ξ) D.initial_coupling
          D.initial_tilt
      D.initial_shear (D.initial_ray_error ξ) (fun t _ => hZ t) (fun t _ => hfluxZ t) hZ0 hZ₁pos
    exact physical_propagation_of_scaled u Z D.a_pos D.epsilon_pos hp.2.2

end EulerPacketMovingFrame
