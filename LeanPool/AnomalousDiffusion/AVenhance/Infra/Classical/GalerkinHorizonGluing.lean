/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Statements.Section4.IsClassicalSol

/-! Glue compatible smooth Galerkin limits on increasing integer horizons. -/

@[expose] public section

noncomputable section

open Set
open Topology
open Homogenization

namespace AVenhance.Infra.Classical

/-- Select the first integer horizon extending past a nonnegative time; use zero before time zero.
-/
noncomputable def classicalGlueHorizonFamily
    (family : ℕ → ℝ → Vec 2 → ℝ) (t : ℝ) (x : Vec 2) : ℝ :=
  if 0 ≤ t then family (Nat.floor t + 1) t x else 0

theorem classicalGlueHorizonFamily_apply_of_nonneg
    (family : ℕ → ℝ → Vec 2 → ℝ) (t : ℝ) (x : Vec 2) (ht : 0 ≤ t) :
    classicalGlueHorizonFamily family t x = family (Nat.floor t + 1) t x := by
  unfold classicalGlueHorizonFamily
  simp [ht]

theorem classicalGlueHorizonFamily_fun_of_nonneg
    (family : ℕ → ℝ → Vec 2 → ℝ) (t : ℝ) (ht : 0 ≤ t) :
    classicalGlueHorizonFamily family t = family (Nat.floor t + 1) t := by
  funext x
  exact classicalGlueHorizonFamily_apply_of_nonneg family t x ht

/-- Compatible smooth solutions on every integer horizon glue to a global classical solution.
The hypotheses are local in time: they do not assume the global conclusion. -/
theorem classicalClassicalSol_of_consistent_horizon_family
    (b : ℝ → Vec 2 → Vec 2) (κ : ℝ) (F : ℝ → Vec 2 → ℝ)
    (θ₀ : Vec 2 → ℝ) (family : ℕ → ℝ → Vec 2 → ℝ)
    (hsmooth : ∀ (N : ℕ), 0 < N → ContDiffOn ℝ (⊤ : ℕ∞)
      (Function.uncurry (family N)) (Icc (0 : ℝ) (N : ℝ) ×ˢ univ))
    (hperiodic : ∀ (N : ℕ), 0 < N → ∀ t, 0 ≤ t →
      AVenhance.IsZ2Periodic (family N t))
    (hinitial : ∀ (N : ℕ), 0 < N → ∀ x, family N 0 x = θ₀ x)
    (hpde : ∀ (N : ℕ), 0 < N → ∀ t, t ∈ Ioo (0 : ℝ) (N : ℝ) → ∀ x,
      AVenhance.advDiffOp b κ (family N) t x = F t x)
    (hcompatible : ∀ (M N : ℕ), M ≤ N → ∀ t, t ∈ Icc (0 : ℝ) (M : ℝ) →
      family M t = family N t) :
    ∃ θ : ℝ → Vec 2 → ℝ, AVenhance.IsClassicalSol b κ F θ₀ θ := by
  let θ := classicalGlueHorizonFamily family
  have hregular : ContDiffOn ℝ (⊤ : ℕ∞) (Function.uncurry θ)
      (Ici (0 : ℝ) ×ˢ univ) := by
    intro p hp
    rcases Set.mem_prod.mp hp with ⟨ht, hx⟩
    let M : ℕ := Nat.floor p.1 + 2
    have hM : 0 < M := by omega
    have htM : p.1 < (M : ℝ) := by
      have hf := Nat.lt_floor_add_one p.1
      dsimp [M]
      push_cast
      linarith
    have hpM : p ∈ Icc (0 : ℝ) (M : ℝ) ×ˢ univ := by
      exact ⟨⟨ht, le_of_lt htM⟩, trivial⟩
    have hMregular := hsmooth M hM
    have hwithinM : ContDiffWithinAt ℝ (⊤ : ℕ∞)
        (Function.uncurry (family M)) (Icc (0 : ℝ) (M : ℝ) ×ˢ univ) p :=
      hMregular p hpM
    have hnear : ∀ᶠ q : ℝ × Vec 2 in 𝓝 p, q.1 < (M : ℝ) := by
      exact (continuous_fst.continuousAt.tendsto).eventually
        (Iio_mem_nhds htM)
    have hsets : (Ici (0 : ℝ) ×ˢ univ) =ᶠ[𝓝 p]
        (Icc (0 : ℝ) (M : ℝ) ×ˢ univ) := by
      filter_upwards [hnear] with q hq
      simp only [Set.mem_prod, Set.mem_Ici, Set.mem_Icc, Set.mem_univ]
      apply propext
      constructor
      · intro hq0
        exact ⟨⟨hq0.1, le_of_lt hq⟩, trivial⟩
      · intro hq0
        exact ⟨hq0.1.1, trivial⟩
    have hwithin : ContDiffWithinAt ℝ (⊤ : ℕ∞)
        (Function.uncurry (family M)) (Ici (0 : ℝ) ×ˢ univ) p :=
      hwithinM.congr_set hsets.symm
    have hnearWithin : ∀ᶠ q : ℝ × Vec 2 in
        𝓝[Ici (0 : ℝ) ×ˢ univ] p, q.1 < (M : ℝ) :=
      Filter.Eventually.filter_mono inf_le_left hnear
    have heq : Function.uncurry θ =ᶠ[𝓝[Ici (0 : ℝ) ×ˢ univ] p]
        Function.uncurry (family M) := by
      filter_upwards [self_mem_nhdsWithin, hnearWithin] with q hq hqM
      rcases Set.mem_prod.mp hq with ⟨hq0, hqx⟩
      change 0 ≤ q.1 at hq0
      let K : ℕ := Nat.floor q.1 + 1
      have hK : 0 < K := by omega
      have hqK : q.1 ∈ Icc (0 : ℝ) (K : ℝ) := by
        refine ⟨hq0, ?_⟩
        have hf := Nat.lt_floor_add_one q.1
        dsimp [K]
        exact le_of_lt (by simpa using hf)
      have hqM' : q.1 ∈ Icc (0 : ℝ) (M : ℝ) := ⟨hq0, le_of_lt hqM⟩
      change classicalGlueHorizonFamily family q.1 q.2 = family M q.1 q.2
      rw [classicalGlueHorizonFamily_apply_of_nonneg family q.1 q.2 hq0]
      change family K q.1 q.2 = family M q.1 q.2
      by_cases hKM : K ≤ M
      · have heq := hcompatible K M hKM q.1 hqK
        exact congrArg (fun f : Vec 2 → ℝ => f q.2) heq
      · have hMK : M ≤ K := le_of_not_ge hKM
        have heq := hcompatible M K hMK q.1 hqM'
        exact (congrArg (fun f : Vec 2 → ℝ => f q.2) heq).symm
    have hEqAt : Function.uncurry θ p = Function.uncurry (family M) p :=
      heq.self_of_nhdsWithin hp
    exact hwithin.congr_of_eventuallyEq heq hEqAt
  have hperiodicθ : ∀ t, 0 ≤ t → AVenhance.IsZ2Periodic (θ t) := by
    intro t ht
    let N : ℕ := Nat.floor t + 1
    have hN : 0 < N := by omega
    have hperiod := hperiodic N hN t ht
    change AVenhance.IsZ2Periodic (classicalGlueHorizonFamily family t)
    rw [classicalGlueHorizonFamily_fun_of_nonneg family t ht]
    simpa [N] using hperiod
  have hinitialθ : ∀ x, θ 0 x = θ₀ x := by
    intro x
    have hN : 0 < Nat.floor (0 : ℝ) + 1 := by norm_num
    simpa [θ, classicalGlueHorizonFamily] using hinitial
      (Nat.floor (0 : ℝ) + 1) hN x
  have hpdeθ : ∀ t, 0 < t → ∀ x,
      AVenhance.advDiffOp b κ θ t x = F t x := by
    intro t ht x
    let N : ℕ := Nat.floor t + 1
    have hN : 0 < N := by omega
    have htime : t ∈ Ioo (0 : ℝ) (N : ℝ) := by
      refine ⟨ht, ?_⟩
      have hf := Nat.lt_floor_add_one t
      dsimp [N]
      simpa using hf
    have hEq : θ t = family N t := by
      change classicalGlueHorizonFamily family t = family N t
      rw [classicalGlueHorizonFamily_fun_of_nonneg family t (le_of_lt ht)]
    have hnearPos : ∀ᶠ s : ℝ in 𝓝 t, 0 < s := Ioi_mem_nhds ht
    have hnearN : ∀ᶠ s : ℝ in 𝓝 t, s < (N : ℝ) := by
      exact (continuous_id.continuousAt.tendsto).eventually (Iio_mem_nhds htime.2)
    have hlocal : (fun s => θ s x) =ᶠ[𝓝 t]
        (fun s => family N s x) := by
      filter_upwards [hnearPos, hnearN] with s hs0 hsN
      let K : ℕ := Nat.floor s + 1
      have hKpos : 0 < K := by omega
      have hsK : s ∈ Icc (0 : ℝ) (K : ℝ) := by
        refine ⟨le_of_lt hs0, ?_⟩
        have hf := Nat.lt_floor_add_one s
        dsimp [K]
        exact le_of_lt (by simpa using hf)
      have hsN' : s ∈ Icc (0 : ℝ) (N : ℝ) := ⟨le_of_lt hs0, le_of_lt hsN⟩
      change classicalGlueHorizonFamily family s x = family N s x
      rw [classicalGlueHorizonFamily_apply_of_nonneg family s x (le_of_lt hs0)]
      change family K s x = family N s x
      by_cases hKN : K ≤ N
      · have heq := hcompatible K N hKN s hsK
        exact congrArg (fun f : Vec 2 → ℝ => f x) heq
      · have hNK : N ≤ K := le_of_not_ge hKN
        have heq := hcompatible N K hNK s hsN'
        exact (congrArg (fun f : Vec 2 → ℝ => f x) heq).symm
    have hslab : (Icc (0 : ℝ) (N : ℝ) ×ˢ univ) ∈ 𝓝 (t, x) := by
      have hopen : (Ioo (0 : ℝ) (N : ℝ) ×ˢ univ) ∈ 𝓝 (t, x) := by
        exact (isOpen_Ioo.prod isOpen_univ).mem_nhds ⟨⟨htime.1, htime.2⟩, trivial⟩
      apply Filter.mem_of_superset hopen
      intro p hp
      exact ⟨⟨le_of_lt hp.1.1, le_of_lt hp.1.2⟩, trivial⟩
    have hfamilyAt : ContDiffAt ℝ (⊤ : ℕ∞)
        (Function.uncurry (family N)) (t, x) :=
      (hsmooth N hN (t, x) (by exact ⟨⟨le_of_lt htime.1, le_of_lt htime.2⟩, trivial⟩)).contDiffAt
          hslab
    have hcurve : ContDiff ℝ (⊤ : ℕ∞) (fun s : ℝ => (s, x)) :=
      contDiff_id.prodMk contDiff_const
    have hcurveAt : ContDiffAt ℝ (⊤ : ℕ∞) (fun s : ℝ => (s, x)) t :=
      hcurve.contDiffAt
    have hsectionAt : ContDiffAt ℝ (⊤ : ℕ∞) (fun s => family N s x) t := by
      simpa only [Function.comp_def, Function.uncurry_apply_pair] using
        ContDiffAt.comp t hfamilyAt hcurveAt
    have hsectionDeriv := (hsectionAt.differentiableAt (by simp)).hasDerivAt
    have hglobalDeriv := hsectionDeriv.congr_of_eventuallyEq hlocal
    have htimeEq : deriv (fun s => θ s x) t =
        deriv (fun s => family N s x) t := by
      rw [hglobalDeriv.deriv, hsectionDeriv.deriv]
    have hfamilyPDE := hpde N hN t htime x
    unfold AVenhance.advDiffOp at hfamilyPDE ⊢
    rw [htimeEq, hEq]
    exact hfamilyPDE
  exact ⟨θ, hregular, hperiodicθ, hinitialθ, hpdeθ⟩

end AVenhance.Infra.Classical

end
