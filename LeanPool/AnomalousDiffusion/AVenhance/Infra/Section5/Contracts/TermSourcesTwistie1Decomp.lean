/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.Contracts.TermSourcesTwistie1Analytic
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.Contracts.TermSourcesTwistie1Corrector
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.Contracts.TermSourcesCutoffPointwise
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.SlowFactorBoundsSource

/-! # Finite decomposition of `twistie1`

At fixed `t`, `twistie1(t) = ∑_{k ∈ s} ∑_j f_{k,j} · (χ_{m,k,j} ∘ X_{m-1,l_k}⁻¹)` over the finite
    set
`s` of odd `k` with `ξ_{m,k}(t) ≠ 0` (at most three), `f_{k,j}` the slow factor of
`e.fg.choice.1` (`section5SlowChoice1`). -/

@[expose] public section

open MeasureTheory Homogenization
open scoped ContDiff

noncomputable section

namespace AVenhance.Infra.Section5.Contracts

open AVenhance AVenhance.Infra.Section5 AVenhance.Infra.Section4 AVenhance.Infra.Ergodic

/-- The vector field `∇ ∇·((K_m + s_{m-1}) ∇T)` at time `t`. -/
def seGd {β : ℝ} (I : Ingredients β) {Φ : ℕ → ℝ → Vec 2 → ℝ} (hΦ : IsStreamSeq I Φ) (m : ℕ)
    (κ : ℝ) (T : ℝ → Vec 2 → ℝ) (t : ℝ) : Vec 2 → Vec 2 := fun x =>
  gradDiv (fun s y => (I.Kmat κ m s + I.sMat hΦ m κ s y).mulVec (spaceGrad (T s) y)) t x

theorem seGd_apply {β : ℝ} (I : Ingredients β) {Φ : ℕ → ℝ → Vec 2 → ℝ} (hΦ : IsStreamSeq I Φ)
    (m : ℕ) (κ : ℝ) (T : ℝ → Vec 2 → ℝ) (t : ℝ) (x : Vec 2) (i : Fin 2) :
    seGd I hΦ m κ T t x i =
      slowFactorGradDiv (fun y => I.Kmat κ m t + I.sMat hΦ m κ t y) (T t) i x := by
  have h := slowFactorGradDiv_eq_gradDiv (fun s y => I.Kmat κ m s + I.sMat hΦ m κ s y) T t i
  exact (congrFun h x).symm

theorem se_memL2On_of_continuous {f : Vec 2 → ℝ} (hf : Continuous f) : MemL2On unitCube f := by
  have h := continuous_unitCell_memLp_two hf
  rw [Measure.restrict_congr_set Infra.Torus.unitCell_ae_eq_unitCube] at h
  simpa using h

/-- `ξ_{m,k}(t) ≠ 0` for `k` in a finite set. -/
theorem se_xi_support {β : ℝ} (I : Ingredients β) (m : ℕ) (t : ℝ) :
    ∃ s : Finset {k : ℤ // Odd k}, s.card ≤ 3 ∧ (∀ q ∈ s, I.xiMK m q.1 t ≠ 0) ∧
      ∀ q : {k : ℤ // Odd k}, q ∉ s → I.xiMK m q.1 t = 0 := by
  classical
  obtain ⟨s, hcard, hs⟩ := sb_odd_support_card I m t
  refine ⟨s.filter (fun q => I.xiMK m q.1 t ≠ 0), (Finset.card_filter_le _ _).trans hcard,
    fun q hq => (Finset.mem_filter.1 hq).2, fun q hq => ?_⟩
  by_contra hne
  exact hq (Finset.mem_filter.2 ⟨hs q hne, hne⟩)

/-- The finite decomposition of `twistie1(t)`. -/
theorem se_twistie1_eq_sum {β : ℝ} (I : Ingredients β) {Φ : ℕ → ℝ → Vec 2 → ℝ}
    (hΦ : IsStreamSeq I Φ) (m : ℕ) (κ : ℝ) (T : ℝ → Vec 2 → ℝ) (t : ℝ)
    (s : Finset {k : ℤ // Odd k}) (hs : ∀ q : {k : ℤ // Odd k}, q ∉ s → I.xiMK m q.1 t = 0) :
    twistie1 I hΦ m κ T t = fun x => ∑ q ∈ s, ∑ j : Fin 2,
      section5SlowChoice1 I hΦ m κ T q.1 t j x * I.chiTilde hΦ m κ q.1 t x j := by
  funext x
  unfold twistie1
  have hterm : ∀ q : {k : ℤ // Odd k},
      I.xiMK m q.1 t * vecDot (I.chiTilde hΦ m κ q.1 t x)
        ((flowGradK I hΦ m q.1 t x).mulVec
          (gradDiv (fun s y =>
            (I.Kmat κ m s + I.sMat hΦ m κ s y).mulVec (spaceGrad (T s) y)) t x)) =
      ∑ j : Fin 2, section5SlowChoice1 I hΦ m κ T q.1 t j x * I.chiTilde hΦ m κ q.1 t x j := by
    intro q
    unfold vecDot section5SlowChoice1
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    ring
  simp_rw [hterm]
  rw [tsum_eq_sum (s := s)]
  intro q hq
  rw [← hterm q, hs q hq, zero_mul]

end AVenhance.Infra.Section5.Contracts
end
