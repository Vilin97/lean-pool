/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Statements.Construction.NextStream
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Construction.NextStreamFinite
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Construction.StreamAdmissible
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Flow.JointSmoothFromFixedStart
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Flow.Laws
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Ingredients.TimeScaleArithmetic
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Ingredients.TimeScales
public import LeanPool.AnomalousDiffusion.AVenhance.Statements.FlowDefs.FlowIsFlow
public import Mathlib.Algebra.Order.Floor.Ring
public import Mathlib.Analysis.Calculus.ContDiff.Operations
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

/-! Provider proofs for the §2 construction recursion. -/

@[expose] public section

open MeasureTheory Homogenization Filter Topology
open scoped ContDiff

noncomputable section

namespace AVenhance.Proofs.IsAdmissibleStream

theorem NextStreamAdmissible.epsilon_inv_eq_nat {β : ℝ} (I : Ingredients β) {m : ℕ}
    (hm : 1 ≤ m) :
    (epsilon β I.Λ m)⁻¹ =
      (⌈(I.Λ : ℝ) ^ (q β ^ m / (q β - 1))⌉₊ : ℝ) := by
  have hm0 : m ≠ 0 := by omega
  simp [epsilon, hm0]

theorem NextStreamAdmissible.psi_lattice_periodic {β : ℝ} (I : Ingredients β) {m : ℕ}
    (hm : 1 ≤ m) (k : ℤ) (x : Vec 2) (j : Fin 2 → ℤ) :
    psi β I.Λ m k (x + latticeShift j) = psi β I.Λ m k x := by
  let E : ℕ := ⌈(I.Λ : ℝ) ^ (q β ^ m / (q β - 1))⌉₊
  have hE : (epsilon β I.Λ m)⁻¹ = (E : ℝ) := by
    simpa [E] using NextStreamAdmissible.epsilon_inv_eq_nat I hm
  have hscaled (i : Fin 2) :
      ((epsilon β I.Λ m)⁻¹ • (x + latticeShift j)) i =
        ((epsilon β I.Λ m)⁻¹ • x) i + (((E : ℤ) * j i : ℤ) : ℝ) := by
    simp only [Pi.smul_apply, Pi.add_apply, latticeShift]
    rw [hE]
    push_cast
    ring
  have hsin (i : Fin 2) :
      Real.sin (2 * Real.pi *
        (((epsilon β I.Λ m)⁻¹ • (x + latticeShift j)) i)) =
        Real.sin (2 * Real.pi * (((epsilon β I.Λ m)⁻¹ • x) i)) := by
    rw [hscaled i]
    have harg : 2 * Real.pi *
        (((epsilon β I.Λ m)⁻¹ • x) i + (((E : ℤ) * j i : ℤ) : ℝ)) =
        2 * Real.pi * (((epsilon β I.Λ m)⁻¹ • x) i) +
          ((E : ℤ) * j i : ℤ) * (2 * Real.pi) := by
      push_cast
      ring
    rw [harg, Real.sin_add_int_mul_two_pi]
  have hcore : psi0 k ((epsilon β I.Λ m)⁻¹ • (x + latticeShift j)) =
      psi0 k ((epsilon β I.Λ m)⁻¹ • x) := by
    unfold psi0
    by_cases h1 : k % 4 = 1
    · simp [h1]
      simpa only [Pi.smul_apply, smul_eq_mul, Pi.add_apply] using hsin 0
    · by_cases h3 : k % 4 = 3
      · simp [h3]
        simpa only [Pi.smul_apply, smul_eq_mul, Pi.add_apply] using hsin 1
      · simp [h1, h3]
  unfold psi
  rw [hcore]

theorem NextStreamAdmissible.psi_index_periodic {β : ℝ} (I : Ingredients β) (m : ℕ)
    {K : ℤ} (hK : K % 4 = 0) (k : ℤ) (x : Vec 2) :
    psi β I.Λ m (k + K) x = psi β I.Λ m k x := by
  have h1 : ((k + K) % 4 = 1) = (k % 4 = 1) := propext (by omega)
  have h3 : ((k + K) % 4 = 3) = (k % 4 = 3) := propext (by omega)
  simp [psi, psi0, h1, h3]

theorem NextStreamAdmissible.nextStreamTerm_contDiff {β : ℝ} (I : Ingredients β) (m : ℕ)
    (φ : ℝ → Vec 2 → ℝ) (hφ : IsAdmissibleStream φ) (k : ℤ) :
    ContDiff ℝ ∞ (fun p : ℝ × Vec 2 =>
      I.nextStreamTerm m φ hφ p.1 p.2 k) := by
  have hb : Infra.Flow.SmoothPeriodicField (streamVel φ) :=
    Infra.Construction.smoothPeriodic_streamVel hφ
  have hX : IsFlow (streamVel φ)
      (flow (streamVel φ) hφ.vel_continuous hφ.vel_lipschitz) :=
    flow_isFlow _ _ _
  let start : ℝ := (lIdx β I.Λ m k : ℝ) * tauPP β I.Λ m
  have hflow : ContDiff ℝ ∞ (fun p : ℝ × Vec 2 =>
      flowInv (streamVel φ) hφ.vel_continuous hφ.vel_lipschitz p.1 p.2 start) := by
    have hjoint := Infra.Flow.flow_inverse_joint_contDiff_infty hb hX
    have hmap : ContDiff ℝ ∞ (fun p : ℝ × Vec 2 => (p.1, p.2, start)) := by
      fun_prop
    have hcomp := hjoint.comp hmap
    simpa only [Function.comp_def, flowInv, start] using hcomp
  have hpsi : ContDiff ℝ ∞ (psi β I.Λ m k) := by
    unfold psi
    have hinner : ContDiff ℝ ∞
        (fun x : Vec 2 => psi0 k ((epsilon β I.Λ m)⁻¹ • x)) := by
      unfold psi0
      split_ifs <;> fun_prop
    change ContDiff ℝ ∞ (fun x : Vec 2 =>
      a β I.Λ m * epsilon β I.Λ m ^ 2 *
        psi0 k ((epsilon β I.Λ m)⁻¹ • x))
    exact contDiff_const.mul hinner
  have hpsiFlow : ContDiff ℝ ∞
      (fun p : ℝ × Vec 2 => psi β I.Λ m k
        (flowInv (streamVel φ) hφ.vel_continuous hφ.vel_lipschitz p.1 p.2 start)) :=
    hpsi.comp hflow
  have hhat : ContDiff ℝ ∞
      (fun p : ℝ × Vec 2 => I.hatZetaML m (lIdx β I.Λ m k) p.1) := by
    unfold Ingredients.hatZetaML shiftCutoff
    change ContDiff ℝ ∞
      (I.hatZeta m ∘ fun p : ℝ × Vec 2 => p.1 -
        (lIdx β I.Λ m k : ℝ) * tauPP β I.Λ m)
    exact (I.hatZeta_smooth m).comp (by fun_prop)
  have hzeta : ContDiff ℝ ∞ (fun p : ℝ × Vec 2 => I.zetaMK m k p.1) := by
    unfold Ingredients.zetaMK scaledCutoff
    change ContDiff ℝ ∞
      (I.zeta ∘ fun p : ℝ × Vec 2 => (p.1 - (k : ℝ) * tau β I.Λ m) /
        tau β I.Λ m)
    exact I.zeta_smooth.comp (by fun_prop)
  change ContDiff ℝ ∞ (fun p : ℝ × Vec 2 =>
    I.hatZetaML m (lIdx β I.Λ m k) p.1 * I.zetaMK m k p.1 *
      psi β I.Λ m k
        (flowInv (streamVel φ) hφ.vel_continuous hφ.vel_lipschitz p.1 p.2 start))
  simpa [mul_assoc] using hhat.mul (hzeta.mul hpsiFlow)

theorem NextStreamAdmissible.nextStreamTerm_ne_zero_distance {β : ℝ} (I : Ingredients β)
    (m : ℕ) (φ : ℝ → Vec 2 → ℝ) (hφ : IsAdmissibleStream φ)
    (t : ℝ) (x : Vec 2) (k : ℤ)
    (hne : I.nextStreamTerm m φ hφ t x k ≠ 0) :
    |t - (k : ℝ) * tau β I.Λ m| ≤ (2 / 3 : ℝ) * tau β I.Λ m := by
  have hτ : 0 < tau β I.Λ m :=
    Infra.Ingredients.tau_pos I.one_lt_beta I.beta_lt I.two_pow_seven_le
  have hz : I.zetaMK m k t ≠ 0 := by
    intro hzero
    apply hne
    simp [Ingredients.nextStreamTerm, hzero]
  have harg : I.zeta ((t - (k : ℝ) * tau β I.Λ m) / tau β I.Λ m) ≠ 0 := by
    simpa [Ingredients.zetaMK, scaledCutoff] using hz
  let u := (t - (k : ℝ) * tau β I.Λ m) / tau β I.Λ m
  have hpos : 0 < I.zeta u :=
    lt_of_le_of_ne (I.zeta_nonneg u) (Ne.symm (by simpa [u] using harg))
  have hle := I.zeta_le_ind u
  have hu : u ∈ Set.Icc (-(2 / 3 : ℝ)) (2 / 3) := by
    by_contra hnot
    have hzero : indIcc (-(2 / 3 : ℝ)) (2 / 3) u = 0 := by
      simp [indIcc, hnot]
    rw [hzero] at hle
    linarith
  have habs : |u| ≤ 2 / 3 := abs_le.mpr ⟨hu.1, hu.2⟩
  have hdiv : |t - (k : ℝ) * tau β I.Λ m| / tau β I.Λ m ≤ 2 / 3 := by
    simpa [u, abs_div, abs_of_pos hτ] using habs
  rw [div_le_iff₀ hτ] at hdiv
  exact hdiv

theorem NextStreamAdmissible.nextStreamTerm_locally_finite_sum {β : ℝ} (I : Ingredients β)
    (m : ℕ) (φ : ℝ → Vec 2 → ℝ) (hφ : IsAdmissibleStream φ)
    (p : ℝ × Vec 2) :
    ∃ S : Finset ℤ, ∀ᶠ q : ℝ × Vec 2 in 𝓝 p,
      (∑' k : ℤ, I.nextStreamTerm m φ hφ q.1 q.2 k) =
        ∑ k ∈ S, I.nextStreamTerm m φ hφ q.1 q.2 k := by
  let τ := tau β I.Λ m
  have hτ : 0 < τ := by
    dsimp [τ]
    exact Infra.Ingredients.tau_pos I.one_lt_beta I.beta_lt I.two_pow_seven_le
  let S : Finset ℤ := Finset.Icc (⌊(p.1 - 1) / τ⌋ - 1) (⌈(p.1 + 1) / τ⌉ + 1)
  refine ⟨S, ?_⟩
  have hopen : Set.Ioo (p.1 - 1) (p.1 + 1) ∈ 𝓝 p.1 :=
    isOpen_Ioo.mem_nhds ⟨by linarith, by linarith⟩
  have htime : ∀ᶠ q : ℝ × Vec 2 in 𝓝 p, q.1 ∈ Set.Icc (p.1 - 1) (p.1 + 1) := by
    filter_upwards [continuous_fst.continuousAt.preimage_mem_nhds hopen] with q hq
    exact ⟨le_of_lt hq.1, le_of_lt hq.2⟩
  filter_upwards [htime] with q hq
  apply tsum_eq_sum
  intro k hk
  have hzero : I.nextStreamTerm m φ hφ q.1 q.2 k = 0 := by
    by_contra hne
    have hdist := NextStreamAdmissible.nextStreamTerm_ne_zero_distance I m φ hφ q.1 q.2 k hne
    have habs := abs_le.mp hdist
    have hklower : p.1 - 1 - (2 / 3 : ℝ) * τ ≤ (k : ℝ) * τ := by
      nlinarith [hq.1, habs.2]
    have hkupper : (k : ℝ) * τ ≤ p.1 + 1 + (2 / 3 : ℝ) * τ := by
      nlinarith [hq.2, habs.1]
    have hloForm : ((p.1 - 1) - (2 / 3 : ℝ) * τ) / τ =
        (p.1 - 1) / τ - 2 / 3 := by
      field_simp [ne_of_gt hτ]
    have hhiForm : ((p.1 + 1) + (2 / 3 : ℝ) * τ) / τ =
        (p.1 + 1) / τ + 2 / 3 := by
      field_simp [ne_of_gt hτ]
    have hlo : ((p.1 - 1) / τ) - 2 / 3 ≤ (k : ℝ) := by
      rw [← hloForm]
      exact (div_le_iff₀ hτ).2 hklower
    have hhi : (k : ℝ) ≤ ((p.1 + 1) / τ) + 2 / 3 := by
      rw [← hhiForm]
      exact (le_div_iff₀ hτ).2 hkupper
    have hfloor : (⌊(p.1 - 1) / τ⌋ : ℝ) ≤ (p.1 - 1) / τ := Int.floor_le _
    have hceil : (p.1 + 1) / τ ≤ (⌈(p.1 + 1) / τ⌉ : ℝ) := Int.le_ceil _
    have hklo : ((⌊(p.1 - 1) / τ⌋ - 1 : ℤ) : ℝ) ≤ (k : ℝ) := by
      simp only [Int.cast_sub, Int.cast_one]
      linarith
    have hkhi : (k : ℝ) ≤ ((⌈(p.1 + 1) / τ⌉ + 1 : ℤ) : ℝ) := by
      simp only [Int.cast_add, Int.cast_one]
      linarith
    have hklo' : ⌊(p.1 - 1) / τ⌋ - 1 ≤ k := by exact_mod_cast hklo
    have hkhi' : k ≤ ⌈(p.1 + 1) / τ⌉ + 1 := by exact_mod_cast hkhi
    have hmem : k ∈ S := by
      simp only [S, Finset.mem_Icc]
      exact ⟨hklo', hkhi'⟩
    exact (hk hmem).elim
  exact hzero

theorem NextStreamAdmissible.nextStream_smooth {β : ℝ} (I : Ingredients β) (m : ℕ)
    (φ : ℝ → Vec 2 → ℝ) (hφ : IsAdmissibleStream φ) :
    ContDiff ℝ ∞ (Function.uncurry (I.nextStream m φ hφ)) := by
  rw [contDiff_iff_contDiffAt]
  intro p
  obtain ⟨S, hS⟩ := NextStreamAdmissible.nextStreamTerm_locally_finite_sum I m φ hφ p
  have hsum : ContDiff ℝ ∞
      (fun q : ℝ × Vec 2 => ∑ k ∈ S, I.nextStreamTerm m φ hφ q.1 q.2 k) := by
    apply ContDiff.sum
    intro k hk
    exact NextStreamAdmissible.nextStreamTerm_contDiff I m φ hφ k
  have hfinite : ContDiff ℝ ∞
      (fun q : ℝ × Vec 2 => φ q.1 q.2 +
        ∑ k ∈ S, I.nextStreamTerm m φ hφ q.1 q.2 k) := by
    exact hφ.1.add hsum
  have heq : (Function.uncurry (I.nextStream m φ hφ)) =ᶠ[𝓝 p]
      (fun q : ℝ × Vec 2 => φ q.1 q.2 +
        ∑ k ∈ S, I.nextStreamTerm m φ hφ q.1 q.2 k) := by
    filter_upwards [hS] with q hq
    simp only [Ingredients.nextStream, Function.uncurry]
    rw [hq]
  exact hfinite.contDiffAt.congr_of_eventuallyEq heq

theorem NextStreamAdmissible.flow_integer_time_shift {b : ℝ → Vec 2 → Vec 2}
    (hb : Infra.Flow.SmoothPeriodicField b)
    {X : ℝ → Vec 2 → ℝ → Vec 2} (hX : IsFlow b X)
    (hL : ∃ L : ℝ, ∀ t x y, ‖b t x - b t y‖ ≤ L * ‖x - y‖)
    (N : ℤ) (x : Vec 2) (s t : ℝ) :
    X (t + (N : ℝ)) x (s + (N : ℝ)) = X t x s := by
  rcases hL with ⟨L, hL⟩
  have htime (r : ℝ) (y : Vec 2) : b (r + (N : ℝ)) y = b r y := by
    have h := hb.periodic N (fun _ => 0) r y
    have hz : latticeShift (fun _ : Fin 2 => (0 : ℤ)) = (0 : Vec 2) := by
      ext i
      simp [latticeShift]
    rw [hz, add_zero] at h
    exact h
  have hshift (r : ℝ) : HasDerivAt (fun u => X (u + (N : ℝ)) x (s + (N : ℝ)))
      (b r (X (r + (N : ℝ)) x (s + (N : ℝ)))) r := by
    simpa only [Function.comp_def, htime r (X (r + (N : ℝ)) x (s + (N : ℝ)))] using
      (hX.2 x (s + (N : ℝ)) (r + (N : ℝ))).comp_add_const r (N : ℝ)
  have hstart : X (s + (N : ℝ)) x (s + (N : ℝ)) = X s x s := by
    rw [hX.1, hX.1]
  have hcurves := Infra.Flow.integralCurve_unique b hL hshift (fun r => hX.2 x s r) hstart
  exact congrFun hcurves t

theorem NextStreamAdmissible.lIdx_add_time_shift {β : ℝ} (I : Ingredients β) (m : ℕ)
    (k K L : ℤ) (hKτ : (K : ℝ) * tau β I.Λ m = (L : ℝ) * tauPP β I.Λ m) :
    lIdx β I.Λ m (k + K) = lIdx β I.Λ m k + L := by
  have hτPP : 0 < tauPP β I.Λ m :=
    Infra.Cutoff.tauPP_pos I.one_lt_beta I.beta_lt I.two_pow_seven_le
  have harg :
      (((k + K : ℤ) : ℝ) * tau β I.Λ m +
          (1 / 2) * (tauPP β I.Λ m - tau β I.Λ m)) / tauPP β I.Λ m =
        (((k : ℝ) * tau β I.Λ m +
          (1 / 2) * (tauPP β I.Λ m - tau β I.Λ m)) / tauPP β I.Λ m) + (L : ℝ) := by
    rw [Int.cast_add, add_mul]
    rw [hKτ]
    field_simp [ne_of_gt hτPP]
    ring
  unfold lIdx
  rw [harg, Int.floor_add_intCast]

theorem NextStreamAdmissible.zetaMK_add_time_shift {β : ℝ} (I : Ingredients β) (m : ℕ)
    (k K N : ℤ) (t : ℝ)
    (hKτ : (K : ℝ) * tau β I.Λ m = (N : ℝ)) :
    I.zetaMK m (k + K) (t + (N : ℝ)) = I.zetaMK m k t := by
  unfold Ingredients.zetaMK scaledCutoff
  have harg :
      (t + (N : ℝ) - ((k + K : ℤ) : ℝ) * tau β I.Λ m) / tau β I.Λ m =
        (t - (k : ℝ) * tau β I.Λ m) / tau β I.Λ m := by
    rw [Int.cast_add, add_mul, hKτ]
    ring
  rw [harg]

theorem NextStreamAdmissible.hatZetaML_add_time_shift {β : ℝ} (I : Ingredients β) (m : ℕ)
    (l L N : ℤ) (t : ℝ)
    (hLPP : (L : ℝ) * tauPP β I.Λ m = (N : ℝ)) :
    I.hatZetaML m (l + L) (t + (N : ℝ)) = I.hatZetaML m l t := by
  unfold Ingredients.hatZetaML shiftCutoff
  have harg :
      t + (N : ℝ) - ((l + L : ℤ) : ℝ) * tauPP β I.Λ m =
        t - (l : ℝ) * tauPP β I.Λ m := by
    rw [Int.cast_add, add_mul, hLPP]
    ring
  rw [harg]

/-- The §2 recursion preserves the smooth joint space-time profile and
its integer space-time periodicity. -/
theorem nextStream_isAdmissible {β : ℝ} (I : Ingredients β) (m : ℕ) (hm : 1 ≤ m)
    (φ : ℝ → Vec 2 → ℝ) (hφ : IsAdmissibleStream φ) :
    IsAdmissibleStream (I.nextStream m φ hφ) := by
  refine ⟨?_, ?_⟩
  · have h := NextStreamAdmissible.nextStream_smooth I m φ hφ
    simpa using h
  · intro N j t x
    have hb := Infra.Construction.smoothPeriodic_streamVel hφ
    rcases Infra.Flow.exists_global_spatial_lipschitz hb with ⟨Lflow, _, hLflow⟩
    have hL : ∃ L : ℝ, ∀ r y z,
        ‖streamVel φ r y - streamVel φ r z‖ ≤ L * ‖y - z‖ :=
      ⟨Lflow, hLflow⟩
    have hX : IsFlow (streamVel φ)
        (flow (streamVel φ) hφ.vel_continuous hφ.vel_lipschitz) :=
      flow_isFlow _ _ _
    have hspace (r : ℝ) : IsZ2Periodic (streamVel φ r) := by
      intro z y
      have hp := hb.periodic 0 z r y
      simpa using hp
    obtain ⟨qτ, hqτ⟩ :=
      (Infra.Ingredients.tauPP_ratio_and_tau_reciprocal
        I.one_lt_beta I.beta_lt I.two_pow_seven_le hm).2
    obtain ⟨qPP, hqPP⟩ := Infra.Ingredients.tauPP_reciprocal_multiple_four
      I.one_lt_beta I.beta_lt I.two_pow_seven_le hm
    let K : ℤ := N * (4 * (qτ : ℤ))
    let J : ℤ := N * (4 * (qPP : ℤ))
    have hτ : 0 < tau β I.Λ m :=
      Infra.Ingredients.tau_pos I.one_lt_beta I.beta_lt I.two_pow_seven_le
    have hτPP : 0 < tauPP β I.Λ m :=
      Infra.Cutoff.tauPP_pos I.one_lt_beta I.beta_lt I.two_pow_seven_le
    have hτrecip : (tau β I.Λ m)⁻¹ = ((4 * qτ : ℕ) : ℝ) := by
      simpa [one_div] using hqτ
    have hτPPrec : (tauPP β I.Λ m)⁻¹ = ((4 * qPP : ℕ) : ℝ) := by
      simpa [one_div] using hqPP
    have hτunit : tau β I.Λ m * ((4 * qτ : ℕ) : ℝ) = 1 := by
      rw [← hτrecip]
      exact mul_inv_cancel₀ (ne_of_gt hτ)
    have hτPPunit : tauPP β I.Λ m * ((4 * qPP : ℕ) : ℝ) = 1 := by
      rw [← hτPPrec]
      exact mul_inv_cancel₀ (ne_of_gt hτPP)
    have hτunit' : tau β I.Λ m * (4 * (qτ : ℝ)) = 1 := by
      simpa only [Nat.cast_mul, Nat.cast_ofNat] using hτunit
    have hτPPunit' : tauPP β I.Λ m * (4 * (qPP : ℝ)) = 1 := by
      simpa only [Nat.cast_mul, Nat.cast_ofNat] using hτPPunit
    have hKtime : (K : ℝ) * tau β I.Λ m = (N : ℝ) := by
      dsimp [K]
      push_cast
      calc
        (N : ℝ) * (4 * (qτ : ℝ)) * tau β I.Λ m =
            (N : ℝ) * (tau β I.Λ m * (4 * (qτ : ℝ))) := by ring
        _ = (N : ℝ) := by rw [hτunit', mul_one]
    have hJtime : (J : ℝ) * tauPP β I.Λ m = (N : ℝ) := by
      dsimp [J]
      push_cast
      calc
        (N : ℝ) * (4 * (qPP : ℝ)) * tauPP β I.Λ m =
            (N : ℝ) * (tauPP β I.Λ m * (4 * (qPP : ℝ))) := by ring
        _ = (N : ℝ) := by rw [hτPPunit', mul_one]
    have hKmod : K % 4 = 0 := by
      have hfour : (4 * (qτ : ℤ)) % 4 = 0 := by omega
      dsimp [K]
      rw [Int.mul_emod, hfour]
      simp
    have hidx (k : ℤ) :
        lIdx β I.Λ m (k + K) = lIdx β I.Λ m k + J := by
      apply NextStreamAdmissible.lIdx_add_time_shift I m k K J
      calc
        (K : ℝ) * tau β I.Λ m = (N : ℝ) := hKtime
        _ = (J : ℝ) * tauPP β I.Λ m := hJtime.symm
    have hflowShift (r : ℝ) (y : Vec 2) (s : ℝ) :
        flow (streamVel φ) hφ.vel_continuous hφ.vel_lipschitz
          (r + (N : ℝ)) y (s + (N : ℝ)) =
        flow (streamVel φ) hφ.vel_continuous hφ.vel_lipschitz r y s :=
      NextStreamAdmissible.flow_integer_time_shift hb hX hL N y s r
    have hterm (k : ℤ) :
        I.nextStreamTerm m φ hφ (t + (N : ℝ)) (x + latticeShift j) (k + K) =
          I.nextStreamTerm m φ hφ t x k := by
      have hInv :
          flowInv (streamVel φ) hφ.vel_continuous hφ.vel_lipschitz
              (t + (N : ℝ)) (x + latticeShift j)
              (((lIdx β I.Λ m k + J : ℤ) : ℝ) * tauPP β I.Λ m) =
            flowInv (streamVel φ) hφ.vel_continuous hφ.vel_lipschitz t x
              ((lIdx β I.Λ m k : ℝ) * tauPP β I.Λ m) + latticeShift j := by
        change flow (streamVel φ) hφ.vel_continuous hφ.vel_lipschitz
            (((lIdx β I.Λ m k + J : ℤ) : ℝ) * tauPP β I.Λ m)
            (x + latticeShift j) (t + (N : ℝ)) = _
        have hstart :
            ((lIdx β I.Λ m k + J : ℤ) : ℝ) * tauPP β I.Λ m =
              (lIdx β I.Λ m k : ℝ) * tauPP β I.Λ m + (N : ℝ) := by
          rw [Int.cast_add, add_mul, hJtime]
        rw [hstart, hflowShift]
        exact Infra.Flow.flow_lattice_equivariant (streamVel φ) hL hspace hX
          x t ((lIdx β I.Λ m k : ℝ) * tauPP β I.Λ m) j
      unfold Ingredients.nextStreamTerm
      rw [hidx k]
      rw [NextStreamAdmissible.hatZetaML_add_time_shift I m (lIdx β I.Λ m k) J N t hJtime]
      rw [NextStreamAdmissible.zetaMK_add_time_shift I m k K N t hKtime]
      rw [NextStreamAdmissible.psi_index_periodic I m hKmod k]
      rw [hInv, NextStreamAdmissible.psi_lattice_periodic I hm k _ j]
    have hsum :
        (∑' k : ℤ, I.nextStreamTerm m φ hφ (t + (N : ℝ))
          (x + latticeShift j) k) =
        ∑' k : ℤ, I.nextStreamTerm m φ hφ t x k := by
      rw [← (Equiv.addRight K).tsum_eq]
      congr 1
      funext k
      exact hterm k
    change I.nextStream m φ hφ (t + (N : ℝ)) (x + latticeShift j) =
      I.nextStream m φ hφ t x
    simp only [Ingredients.nextStream]
    rw [hφ.2 N j t x, hsum]

end AVenhance.Proofs.IsAdmissibleStream

end
