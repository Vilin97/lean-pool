/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.Topology.Algebra.Module.ModuleTopology
import LeanPool.NavierStokesAndEuler.Euler.ClosedIntervalDerivativeExtension
import LeanPool.NavierStokesAndEuler.Euler.Foundations.PacketCoefficientControl

/-! Normalized coefficient motion from genuine one-sided time derivatives. -/

@[expose] public section


noncomputable section


namespace EulerPacketMovingFrame

open Set EulerPacketCoefficientControl EulerClosedIntervalDerivativeExtension

/-- The existing quantitative motion estimate applies on closed intervals
without assuming an extension of the original coefficient paths. -/
theorem normalized_motion_errors_within
    {a ε Θ G d β : ℝ} {B E : ℝ → Fin 3 → Fin 3 → ℝ}
    {h h₁ b₁ k₁ : ℝ → ℝ}
    (ha : 1 / 2 ≤ a) (hε : 0 < ε) (hΘ : 1 ≤ Θ) (hG : 1 ≤ G) (hd : 0 ≤ d)
    (hsmall : 16 * (ε * Θ * G ^ 2 + d) ≤ 1)
    (hB : ∀ t ∈ Icc 0 Θ, ∀ i j, |B t i j| ≤ G)
    (hE : ∀ t ∈ Icc 0 Θ, ∀ i j, |E t i j| ≤ d)
    (hb : ∀ t ∈ Icc 0 Θ, HasDerivWithinAt (fun s => B s 0 1) (b₁ t) (Icc 0 Θ) t)
    (hk : ∀ t ∈ Icc 0 Θ, HasDerivWithinAt (fun s => B s 2 1) (k₁ t) (Icc 0 Θ) t)
    (hbBound : ∀ t ∈ Icc 0 Θ, |b₁ t| ≤ 2 * ε * G ^ 2)
    (hkBound : ∀ t ∈ Icc 0 Θ, |k₁ t| ≤ 2 * ε * G ^ 2)
    (hShear : ∀ t ∈ Icc 0 Θ, HasDerivWithinAt h (h₁ t) (Icc 0 Θ) t)
    (hShearBound : ∀ t ∈ Icc 0 Θ, |h₁ t| ≤ (4 * ε * G) * |h t|)
    (hb0 : B 0 0 1 = a) (hk0 : B 0 2 1 = a * β) (hh0 : h 0 = a / ε ^ 2) :
    let e := 16 * (ε * Θ * G ^ 2 + d)
    ε ≤ e ∧ ∀ t ∈ Icc 0 Θ,
      (∀ i j, |ε * B t i j / a| ≤ e) ∧
      (∀ i j, |E t i j / a| ≤ e) ∧
      |ε ^ 2 * h t / a - 1| ≤ e ∧
      |B t 0 1 / a - 1| ≤ e ∧ |B t 2 1 / a - β| ≤ e := by
  have hΘ0 : 0 < Θ := by linarith
  have h0 : (0:ℝ) ∈ Icc 0 Θ := ⟨le_rfl, hΘ0.le⟩
  obtain ⟨b', hbeq, hbd⟩ := exists_extension hΘ0 hb
  obtain ⟨k', hkeq, hkd⟩ := exists_extension hΘ0 hk
  obtain ⟨h', hheq, hhd⟩ := exists_extension hΘ0 hShear
  let B' : ℝ → Fin 3 → Fin 3 → ℝ := fun t i j =>
    if i = 0 ∧ j = 1 then b' t else if i = 2 ∧ j = 1 then k' t else B t i j
  have hBeq : ∀ t ∈ Icc 0 Θ, ∀ i j, B' t i j = B t i j := by
    intro t ht i j
    dsimp [B']
    split_ifs with hb hk
    · rcases hb with ⟨rfl, rfl⟩
      exact hbeq ht
    · rcases hk with ⟨rfl, rfl⟩
      exact hkeq ht
    · rfl
  have hB' : ∀ t ∈ Icc 0 Θ, ∀ i j, |B' t i j| ≤ G := by
    intro t ht i j
    rw [hBeq t ht]
    exact hB t ht i j
  have hb' : ∀ t ∈ Icc 0 Θ, HasDerivAt (fun s => B' s 0 1) (b₁ t) t := by
    intro t ht
    simpa [B'] using hbd t ht
  have hk' : ∀ t ∈ Icc 0 Θ, HasDerivAt (fun s => B' s 2 1) (k₁ t) t := by
    intro t ht
    simpa [B'] using hkd t ht
  have hh' : ∀ t ∈ Icc 0 Θ, |h₁ t| ≤ (4*ε*G)*|h' t| := by
    intro t ht
    rw [hheq ht]
    exact hShearBound t ht
  have hb0' : B' 0 0 1 = a := (hBeq 0 h0 0 1).trans hb0
  have hk0' : B' 0 2 1 = a*β := (hBeq 0 h0 2 1).trans hk0
  have hh0' : h' 0 = a/ε^2 := (hheq h0).trans hh0
  have herr := normalized_motion_errors ha hε hΘ hG hd hsmall hB' hE hb' hk'
    hbBound hkBound hhd hh' hb0' hk0' hh0'
  refine ⟨herr.1, ?_⟩
  intro t ht
  simpa only [hBeq t ht, hheq ht] using herr.2 t ht

end EulerPacketMovingFrame
