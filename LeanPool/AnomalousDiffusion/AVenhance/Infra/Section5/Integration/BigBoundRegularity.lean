/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.Integration.BigBound
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.Terms.R46IteratesRegularity
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.ResidualPointwiseConstructor
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.Integration.Energy.AnsatzRegularity
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section4.IteratesEnergy
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section4.Amnr.HmAdapter
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section4.Amnr.FlowAverage
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.RelativeError.IteratesLMNSmooth
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.HmBaseFluxIdentity
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.CorrectorLocalization
public import Mathlib.Analysis.Matrix.Normed

/-! Regularity fields for one big-bound estimate instance, excluding the scalar mean fields. -/

@[expose] public section

noncomputable section

open Homogenization MeasureTheory
open scoped ContDiff Topology Matrix.Norms.Elementwise

namespace AVenhance.Infra.Section5.Integration

open AVenhance AVenhance.Infra.Section5

theorem BigBoundRegularity.lmn_contDiff_top_any {β : ℝ} (I : Ingredients β)
    {m : ℕ} (hm : 1 ≤ m) (κ : ℝ) (n : ℕ) :
    ContDiff ℝ (⊤ : ℕ∞) (I.LMN κ m n) := by
  let ρ := 4 * Real.pi ^ 2 * κ / epsilon β I.Λ m ^ 2
  have hterm (l : ℤ) (t : ℝ) :
      I.hatZetaML m l t * ∫ s in Set.Iic t,
        I.hatZetaML m l s *
          (4 * Real.pi ^ 2 * κ * (s - t) / epsilon β I.Λ m ^ 2) ^ n *
          Real.exp (4 * Real.pi ^ 2 * κ / epsilon β I.Λ m ^ 2 * (s - t)) =
      I.hatZetaML m l t * ∫ s in Set.Iic t,
        I.hatZetaML m l s * (ρ * (s - t)) ^ n * Real.exp (ρ * (s - t)) := by
    congr 1
    apply setIntegral_congr_fun measurableSet_Iic
    intro s hs
    simp only [ρ]
    congr 2; ring
  unfold Ingredients.LMN
  apply Infra.Section5.RelativeError.contDiff_tsum_of_locallyFinite
    (g := fun l t => I.hatZetaML m l t * ∫ s in Set.Iic t,
      I.hatZetaML m l s *
        (4 * Real.pi ^ 2 * κ * (s - t) / epsilon β I.Λ m ^ 2) ^ n *
        Real.exp (4 * Real.pi ^ 2 * κ / epsilon β I.Λ m ^ 2 * (s - t)))
  · intro l
    have h := Infra.Section5.RelativeError.memory_term_contDiff
      (Infra.Section5.RelativeError.hatZetaML_contDiff I m l)
      (Infra.Section5.RelativeError.hatZetaML_hasCompactSupport I hm l) ρ n
    have heq : (fun t => I.hatZetaML m l t * ∫ s in Set.Iic t,
      I.hatZetaML m l s *
        (4 * Real.pi ^ 2 * κ * (s - t) / epsilon β I.Λ m ^ 2) ^ n *
        Real.exp (4 * Real.pi ^ 2 * κ / epsilon β I.Λ m ^ 2 * (s - t))) =
        fun t => I.hatZetaML m l t * ∫ s in Set.Iic t,
          I.hatZetaML m l s * (ρ * (s - t)) ^ n * Real.exp (ρ * (s - t)) :=
      funext (hterm l)
    rw [heq]
    exact h
  · intro t
    obtain ⟨S, hS⟩ := Infra.Section5.RelativeError.exists_finset_hatZeta_vanish I hm t
    refine ⟨S, ?_⟩
    have hball : ∀ᶠ y in 𝓝 t, |y - t| < 1 := by
      have hb := Metric.ball_mem_nhds t (zero_lt_one' ℝ)
      filter_upwards [hb] with y hy
      simpa [Metric.mem_ball, Real.dist_eq] using hy
    filter_upwards [hball] with y hy l hl
    simp only [hS y hy l hl, zero_mul]

theorem BigBoundRegularity.amnr_seedMultiplier_contDiff_any {β : ℝ} (I : Ingredients β)
    {Φ : ℕ → ℝ → Vec 2 → ℝ} (hΦ : IsStreamSeq I Φ)
    {m : ℕ} (hm : 1 ≤ m) {κ : ℝ} (n N : ℕ)
    (j k i p : Fin 2) :
    ContDiff ℝ N (Infra.Section4.amnrSeedMultiplier I hΦ m κ n j k i p) := by
  have hAvg := Infra.Section4.amnrFlowAverageA0Plus_contDiffOn (N := N)
    I hΦ hm isOpen_univ j k i p
    (fun l => (Infra.Section4.amnr_flowGrad_joint_contDiff_infty I hΦ m l j i).of_le
      (by simp) |>.contDiffOn)
    (fun l => (Infra.Section4.amnr_flowGrad_joint_contDiff_infty I hΦ m l k p).of_le
      (by simp) |>.contDiffOn)
  have hL : ContDiff ℝ N (fun z : Infra.Section4.AmnrSpace => I.LMN κ m n z.1) :=
    ((BigBoundRegularity.lmn_contDiff_top_any I hm κ n).of_le (by simp)).comp
      contDiff_fst
  change ContDiff ℝ N (Infra.Section4.amnrSeedMultiplierA0Plus I hΦ m κ n j k i p)
  rw [Infra.Section4.amnrSeedMultiplierA0Plus_eq]
  exact hL.neg.mul (contDiffOn_univ.mp hAvg)

/-- The AMNR recursion has every finite joint order for an actual
terminal iterate. The source-order cap is needed for estimates, not for this
qualitative regularity statement. -/
theorem BigBoundRegularity.amnr_actual_contDiffOn_any {β : ℝ} (I : Ingredients β)
    {Φ : ℕ → ℝ → Vec 2 → ℝ} (hΦ : IsStreamSeq I Φ)
    {m : ℕ} (hm : 1 ≤ m) {κm κprev : ℝ} {θ₀ : Vec 2 → ℝ}
    {θprev : ℝ → Vec 2 → ℝ} {T : ℕ → ℝ → Vec 2 → ℝ}
    (hθprev : IsClassicalSol (streamVel (Φ (m - 1))) κprev
      (fun _ _ => 0) θ₀ θprev)
    (hT : I.IsTIterates hΦ m κm κprev θ₀ θprev T)
    (n r ord : ℕ) (i j k : Fin 2) :
    ContDiffOn ℝ ord
      (fun z : Infra.Section4.AmnrSpace =>
        I.Amnr hΦ m κm n (T (Nstar β)) r z.1 z.2 i j k)
      (Set.Ioi (0 : ℝ) ×ˢ Set.univ) := by
  let U : Set Infra.Section4.AmnrSpace := Set.Ioi (0 : ℝ) ×ˢ Set.univ
  let b := fun z : Infra.Section4.AmnrSpace => streamVel (Φ (m - 1)) z.1 z.2
  have hU : IsOpen U := isOpen_Ioi.prod isOpen_univ
  have hbInf : ContDiff ℝ (⊤ : ℕ∞) b :=
    contDiff_infty.mpr (fun N => Infra.Section4.amnr_previous_velocity_contDiff I hΦ hm N)
  have hb : ContDiffOn ℝ (ord + r) b U := (hbInf.of_le (by simp)).contDiffOn
  have hB : ∀ i q, ContDiffOn ℝ (ord + r)
      (Infra.Section4.amnrVelocityGradient b i q) U := by
    intro i q
    have hq := Infra.Section4.amnrVelocityGradient_contDiffOn_infty hU
      hbInf.contDiffOn i q
    exact hq.of_le (by simp)
  obtain ⟨F, hfinal⟩ := Infra.Section4.amnr_tIterates_classical_family
    I hΦ hθprev hT (Nstar β) le_rfl
  have hTgrad : ∀ q, ContDiffOn ℝ (ord + r)
      (Infra.Section4.amnrTGradient (T (Nstar β)) q) U := by
    intro q
    exact Infra.Section4.amnr_classical_gradient_smooth hfinal q (ord + r)
  have hf : ∀ i q, ContDiffOn ℝ (ord + r)
      (Infra.Section4.amnrSeedMultiplier I hΦ m κm n j k i q) U := by
    intro i q
    exact (BigBoundRegularity.amnr_seedMultiplier_contDiff_any I hΦ hm n (ord + r) j k i
        q).contDiffOn
  exact Infra.Section4.Amnr_contDiffOn_of_factors I hΦ hm κm n
    (T (Nstar β)) hU (N := ord + r) j k hb hB hf hTgrad
    (r := r) (a := ord) le_rfl i

theorem BigBoundRegularity.vecDiv_contDiff_infty {F : Vec 2 → Vec 2}
    (hF : ContDiff ℝ (⊤ : ℕ∞) F) :
    ContDiff ℝ (⊤ : ℕ∞) (fun x => vecDiv F x) := by
  have hgrad (i : Fin 2) : ContDiff ℝ (⊤ : ℕ∞)
      (spaceGrad (fun x => F x i)) :=
    Infra.Section4.iterate_gradient_smooth ((contDiff_pi.mp hF) i)
  unfold vecDiv
  exact ContDiff.sum (fun i _ => contDiff_pi.mp (hgrad i) i)

theorem amnr_slice_contDiff_infty {β : ℝ} (I : Ingredients β)
    {Φ : ℕ → ℝ → Vec 2 → ℝ} (hΦ : IsStreamSeq I Φ)
    {m : ℕ} (hm : 1 ≤ m) {κm κprev : ℝ} {θ₀ : Vec 2 → ℝ}
    {θprev : ℝ → Vec 2 → ℝ} {T : ℕ → ℝ → Vec 2 → ℝ}
    (hθprev : IsClassicalSol (streamVel (Φ (m - 1))) κprev
      (fun _ _ => 0) θ₀ θprev)
    (hT : I.IsTIterates hΦ m κm κprev θ₀ θprev T)
    (n r : ℕ) (i j k : Fin 2) {t : ℝ} (ht : 0 < t) :
    ContDiff ℝ (⊤ : ℕ∞)
      (fun x => I.Amnr hΦ m κm n (T (Nstar β)) r t x i j k) := by
  apply contDiff_infty.mpr
  intro p
  have hreg := BigBoundRegularity.amnr_actual_contDiffOn_any I hΦ hm hθprev hT n r p i j k
  let embed : Vec 2 → Infra.Section4.AmnrSpace := fun x => (t, x)
  have hembed : ContDiff ℝ p embed := by fun_prop
  have hmaps : Set.MapsTo embed Set.univ (Set.Ioi (0 : ℝ) ×ˢ Set.univ) := by
    intro x hx
    exact ⟨ht, Set.mem_univ _⟩
  have hh := hreg.comp hembed.contDiffOn hmaps
  exact contDiffOn_univ.mp (by simpa [embed, Function.comp_def] using hh)

theorem BigBoundRegularity.hm_slice_contDiff_infty {β : ℝ} (I : Ingredients β)
    {Φ : ℕ → ℝ → Vec 2 → ℝ} (hΦ : IsStreamSeq I Φ)
    {m : ℕ} (hm : 1 ≤ m) {κm κprev : ℝ} {θ₀ : Vec 2 → ℝ}
    {θprev : ℝ → Vec 2 → ℝ} {T : ℕ → ℝ → Vec 2 → ℝ}
    (hθprev : IsClassicalSol (streamVel (Φ (m - 1))) κprev
      (fun _ _ => 0) θ₀ θprev)
    (hT : I.IsTIterates hΦ m κm κprev θ₀ θprev T)
    {t : ℝ} (ht : 0 < t) :
    ContDiff ℝ (⊤ : ℕ∞) (I.Hm hΦ m κm (T (Nstar β)) t) := by
  have hHmr (r : ℕ) (hr : r ∈ Finset.range (Jcut β)) :
      ContDiff ℝ (⊤ : ℕ∞) (I.Hmr hΦ m κm (T (Nstar β)) r t) := by
    have hflux : ContDiff ℝ (⊤ : ℕ∞) (fun x i =>
        ∑ n ∈ Finset.range (Nstar β), ∑ j : Fin 2, ∑ k : Fin 2,
          I.Amnr hΦ m κm n (T (Nstar β)) r t x i j k *
            I.qMNR κm m n (r + 1) t j k) := by
      apply contDiff_pi.mpr
      intro i
      apply ContDiff.sum
      intro n hn
      apply ContDiff.sum
      intro j hj
      apply ContDiff.sum
      intro k hk
      exact (amnr_slice_contDiff_infty I hΦ hm hθprev hT n r i j k ht).mul
        contDiff_const
    have hEq : I.Hmr hΦ m κm (T (Nstar β)) r t = fun x =>
        vecDiv (fun y i => ∑ n ∈ Finset.range (Nstar β), ∑ j : Fin 2, ∑ k : Fin 2,
          I.Amnr hΦ m κm n (T (Nstar β)) r t y i j k *
            I.qMNR κm m n (r + 1) t j k) x := rfl
    rw [hEq]
    exact BigBoundRegularity.vecDiv_contDiff_infty hflux
  unfold Ingredients.Hm
  exact ContDiff.sum (fun r hr => hHmr r hr)

theorem BigBoundRegularity.amnr_time_differentiable_at {β : ℝ} (I : Ingredients β)
    {Φ : ℕ → ℝ → Vec 2 → ℝ} (hΦ : IsStreamSeq I Φ)
    {m : ℕ} (hm : 1 ≤ m) {κm κprev : ℝ} {θ₀ : Vec 2 → ℝ}
    {θprev : ℝ → Vec 2 → ℝ} {T : ℕ → ℝ → Vec 2 → ℝ}
    (hθprev : IsClassicalSol (streamVel (Φ (m - 1))) κprev
      (fun _ _ => 0) θ₀ θprev)
    (hT : I.IsTIterates hΦ m κm κprev θ₀ θprev T)
    (n r : ℕ) (i j k : Fin 2) {t : ℝ} (ht : 0 < t) (x : Vec 2) :
    DifferentiableAt ℝ
      (fun s => I.Amnr hΦ m κm n (T (Nstar β)) r s x i j k) t := by
  let U : Set Infra.Section4.AmnrSpace := Set.Ioi (0 : ℝ) ×ˢ Set.univ
  let embed : ℝ → Infra.Section4.AmnrSpace := fun s => (s, x)
  have hembed : ContDiff ℝ 1 embed := by fun_prop
  have hmaps : Set.MapsTo embed (Set.Ioi (0 : ℝ)) U := by
    intro s hs
    exact ⟨hs, Set.mem_univ _⟩
  have hreg := BigBoundRegularity.amnr_actual_contDiffOn_any I hΦ hm hθprev hT n r 1 i j k
  have hcomp := hreg.comp hembed.contDiffOn hmaps
  have hslice : ContDiffOn ℝ 1
      (fun s => I.Amnr hΦ m κm n (T (Nstar β)) r s x i j k) (Set.Ioi (0 : ℝ)) := by
    simpa [U, embed, Function.comp_def] using hcomp
  exact (hslice.contDiffAt (isOpen_Ioi.mem_nhds ht)).differentiableAt (by norm_num)

theorem amnr_periodic_of_iterates {β : ℝ} (I : Ingredients β)
    {Φ : ℕ → ℝ → Vec 2 → ℝ} (hΦ : IsStreamSeq I Φ)
    {m : ℕ} (hm : 1 ≤ m) {κm κprev : ℝ} {θ₀ : Vec 2 → ℝ}
    {θprev : ℝ → Vec 2 → ℝ} {T : ℕ → ℝ → Vec 2 → ℝ}
    (hθprev : IsClassicalSol (streamVel (Φ (m - 1))) κprev
      (fun _ _ => 0) θ₀ θprev)
    (hT : I.IsTIterates hΦ m κm κprev θ₀ θprev T) :
    ∀ r t, 0 < t → ∀ n (z : Fin 2 → ℤ) x i j k,
      I.Amnr hΦ m κm n (T (Nstar β)) r t (x + latticeShift z) i j k =
        I.Amnr hΦ m κm n (T (Nstar β)) r t x i j k := by
  have hvelper (t : ℝ) (ht : 0 < t) :
      IsZ2Periodic (streamVel (Φ (m - 1)) t) := by
    have hfield := Infra.Construction.smoothPeriodic_streamVel (hΦ.adm_pred m)
    intro q x
    simpa using hfield.periodic 0 q t x
  have hvelSmooth (t : ℝ) (ht : 0 < t) :
      ContDiff ℝ (⊤ : ℕ∞) (streamVel (Φ (m - 1)) t) := by
    have hfield := Infra.Construction.smoothPeriodic_streamVel (hΦ.adm_pred m)
    exact hfield.smooth.comp
      (by fun_prop : ContDiff ℝ (⊤ : ℕ∞) (fun x : Vec 2 => (t, x)))
  have hTper (t : ℝ) (ht : 0 < t) : IsZ2Periodic (T (Nstar β) t) :=
    Infra.Section4.tIterate_periodic I hΦ hT hθprev le_rfl ht.le
  have hTsm (t : ℝ) (ht : 0 < t) : ContDiff ℝ (⊤ : ℕ∞) (T (Nstar β) t) :=
    Infra.Section4.tIterate_space_contDiff I hΦ hT hθprev le_rfl ht.le
  have hGradPer (t : ℝ) (ht : 0 < t) : IsZ2Periodic
      (spaceGrad (T (Nstar β) t)) :=
    Infra.Section4.iterate_gradient_periodic
      ((hTsm t ht).of_le (by simp)) (hTper t ht)
  have hFlowPer (l : ℤ) (t : ℝ) (ht : 0 < t) :
      IsZ2Periodic (I.flowGrad hΦ m l t) := by
    intro q x
    ext a b
    exact Infra.Section4.amnr_flowGrad_spatial_periodic I hΦ m l t a b q x
  intro r
  induction r with
  | zero =>
      intro t ht n q x i j k
      rw [Infra.Section4.Amnr_zero_factors I hΦ hm κm n (T (Nstar β)) t
        (x + latticeShift q) i j k,
        Infra.Section4.Amnr_zero_factors I hΦ hm κm n (T (Nstar β)) t x i j k]
      apply Finset.sum_congr rfl
      intro p hp
      have hseed : Infra.Section4.amnrSeedMultiplierA0Plus I hΦ m κm n j k i p
          (t, x + latticeShift q) =
          Infra.Section4.amnrSeedMultiplierA0Plus I hΦ m κm n j k i p (t, x) := by
        simp only [Infra.Section4.amnrSeedMultiplierA0Plus, Infra.Section4.amnrSeedMultiplierGen,
          Infra.Section4.amnrFlowAverageGen]
        congr 1
        apply tsum_congr
        intro l
        rw [hFlowPer l t ht q x]
      rw [congrFun (hGradPer t ht q x) p, hseed]
  | succ r ih =>
      intro t ht n q x i j k
      have hper (s : ℝ) (hs : 0 < s) :
          I.Amnr hΦ m κm n (T (Nstar β)) r s (x + latticeShift q) i j k =
            I.Amnr hΦ m κm n (T (Nstar β)) r s x i j k := ih s hs n q x i j k
      have hlocal :
          (fun s => I.Amnr hΦ m κm n (T (Nstar β)) r s (x + latticeShift q) i j k) =ᶠ[𝓝 t]
            fun s => I.Amnr hΦ m κm n (T (Nstar β)) r s x i j k := by
        filter_upwards [isOpen_Ioi.mem_nhds ht] with s hs
        exact hper s hs
      have hderiv :
          deriv (fun s => I.Amnr hΦ m κm n (T (Nstar β)) r s (x + latticeShift q) i j k) t =
            deriv (fun s => I.Amnr hΦ m κm n (T (Nstar β)) r s x i j k) t := by
        exact ((BigBoundRegularity.amnr_time_differentiable_at I hΦ hm hθprev hT
          n r i j k ht x).hasDerivAt.congr_of_eventuallyEq hlocal).deriv
      have hAper (i' j' k' : Fin 2) : IsZ2Periodic
          (fun y => I.Amnr hΦ m κm n (T (Nstar β)) r t y i' j' k') :=
        fun q' y => ih t ht n q' y i' j' k'
      have hAgradPer : IsZ2Periodic (spaceGrad
          (fun y => I.Amnr hΦ m κm n (T (Nstar β)) r t y i j k)) :=
        Infra.Section4.iterate_gradient_periodic
          ((contDiff_infty.mp
            (amnr_slice_contDiff_infty I hΦ hm hθprev hT n r i j k ht)) 1)
          (hAper i j k)
      have hVper : ∀ a : Fin 2, IsZ2Periodic
          (fun y => streamVel (Φ (m - 1)) t y a) := by
        intro a q' y
        exact congrFun (hvelper t ht q' y) a
      have hVgradPer (a b : Fin 2) : IsZ2Periodic
          (spaceGrad (fun y => streamVel (Φ (m - 1)) t y a)) :=
        Infra.Section4.iterate_gradient_periodic
          ((contDiff_infty.mp (contDiff_pi.mp (hvelSmooth t ht) a)) 1)
          (hVper a)
      have hdot : vecDot (streamVel (Φ (m - 1)) t (x + latticeShift q))
          (spaceGrad (fun y => I.Amnr hΦ m κm n (T (Nstar β)) r t y i j k)
            (x + latticeShift q)) =
          vecDot (streamVel (Φ (m - 1)) t x)
          (spaceGrad (fun y => I.Amnr hΦ m κm n (T (Nstar β)) r t y i j k) x) := by
        rw [hvelper t ht q x, hAgradPer q x]
      have hsum :
          (∑ ℓ : Fin 2, spaceGrad
            (fun y => streamVel (Φ (m - 1)) t y i) (x + latticeShift q) ℓ *
              I.Amnr hΦ m κm n (T (Nstar β)) r t (x + latticeShift q) ℓ j k) =
          ∑ ℓ : Fin 2, spaceGrad
            (fun y => streamVel (Φ (m - 1)) t y i) x ℓ *
              I.Amnr hΦ m κm n (T (Nstar β)) r t x ℓ j k := by
        apply Finset.sum_congr rfl
        intro ℓ hℓ
        rw [hVgradPer i ℓ q x]
        exact congrArg (fun a => spaceGrad
          (fun y => streamVel (Φ (m - 1)) t y i) x ℓ * a)
          (hAper ℓ j k q x)
      unfold Ingredients.Amnr
      rw [hderiv, hdot, hsum]

theorem BigBoundRegularity.hm_periodic_of_iterates {β : ℝ} (I : Ingredients β)
    {Φ : ℕ → ℝ → Vec 2 → ℝ} (hΦ : IsStreamSeq I Φ)
    {m : ℕ} (hm : 1 ≤ m) {κm κprev : ℝ} {θ₀ : Vec 2 → ℝ}
    {θprev : ℝ → Vec 2 → ℝ} {T : ℕ → ℝ → Vec 2 → ℝ}
    (hθprev : IsClassicalSol (streamVel (Φ (m - 1))) κprev
      (fun _ _ => 0) θ₀ θprev)
    (hT : I.IsTIterates hΦ m κm κprev θ₀ θprev T) {t : ℝ} (ht : 0 < t) :
    IsZ2Periodic (I.Hm hΦ m κm (T (Nstar β)) t) := by
  classical
  unfold Ingredients.Hm
  intro q x
  apply Finset.sum_congr rfl
  intro r hr
  let F : Vec 2 → Vec 2 := fun y i =>
    ∑ n ∈ Finset.range (Nstar β), ∑ j : Fin 2, ∑ k : Fin 2,
      I.Amnr hΦ m κm n (T (Nstar β)) r t y i j k *
        I.qMNR κm m n (r + 1) t j k
  have hFsm : ContDiff ℝ (⊤ : ℕ∞) F := by
    apply contDiff_pi.mpr
    intro i
    apply ContDiff.sum
    intro n hn
    apply ContDiff.sum
    intro j hj
    apply ContDiff.sum
    intro k hk
    exact (amnr_slice_contDiff_infty I hΦ hm hθprev hT n r i j k ht).mul
      contDiff_const
  have hFper : IsZ2Periodic F := by
    intro q' y
    funext i
    simp only [F]
    apply Finset.sum_congr rfl
    intro n hn
    apply Finset.sum_congr rfl
    intro j hj
    apply Finset.sum_congr rfl
    intro k hk
    rw [amnr_periodic_of_iterates I hΦ hm hθprev hT r t ht n q' y i j k]
  have hgradPer (i : Fin 2) : IsZ2Periodic
      (spaceGrad (fun y => F y i)) :=
    Infra.Section4.iterate_gradient_periodic
      ((contDiff_pi.mp hFsm i).of_le (by simp)) (fun q' y => congrFun (hFper q' y) i)
  change vecDiv F (x + latticeShift q) = vecDiv F x
  unfold vecDiv
  apply Finset.sum_congr rfl
  intro i hi
  exact congrFun (hgradPer i q x) i

theorem BigBoundRegularity.matrixMulVec_contDiff_infty
    {A : Vec 2 → Matrix (Fin 2) (Fin 2) ℝ} {v : Vec 2 → Vec 2}
    (hA : ContDiff ℝ (⊤ : ℕ∞) A) (hv : ContDiff ℝ (⊤ : ℕ∞) v) :
    ContDiff ℝ (⊤ : ℕ∞) (fun x => (A x).mulVec (v x)) := by
  apply contDiff_pi.mpr
  intro i
  change ContDiff ℝ (⊤ : ℕ∞) (fun x => ∑ j : Fin 2, A x i j * v x j)
  apply ContDiff.sum
  intro j hj
  exact (contDiff_pi.mp (contDiff_pi.mp hA i) j).mul (contDiff_pi.mp hv j)

theorem BigBoundRegularity.psi_contDiff_infty {β : ℝ} (I : Ingredients β) (m : ℕ) (k : ℤ) :
    ContDiff ℝ (⊤ : ℕ∞) (psi β I.Λ m k) := by
  unfold psi
  have hprofile : ContDiff ℝ (⊤ : ℕ∞)
      (fun y : Vec 2 => psi0 k ((epsilon β I.Λ m)⁻¹ • y)) := by
    unfold psi0
    split_ifs <;> fun_prop
  exact contDiff_const.mul hprofile

theorem BigBoundRegularity.psi_isZ2Periodic {β : ℝ} (I : Ingredients β) {m : ℕ}
    (k : ℤ) : IsZ2Periodic (psi β I.Λ m k) := by
  intro z x
  obtain ⟨N, hN⟩ :=
    AVenhance.Infra.Section5.Integration.epsilon_inv_exists_nat β I.Λ m
  have hscaled (i : Fin 2) :
      ((epsilon β I.Λ m)⁻¹ • (x + latticeShift z)) i =
        ((epsilon β I.Λ m)⁻¹ • x) i + (((N : ℤ) * z i : ℤ) : ℝ) := by
    simp only [Pi.smul_apply, Pi.add_apply, latticeShift]
    rw [hN]
    push_cast
    ring
  have hcore :
      psi0 k ((epsilon β I.Λ m)⁻¹ • (x + latticeShift z)) =
        psi0 k ((epsilon β I.Λ m)⁻¹ • x) := by
    by_cases h1 : k % 4 = 1
    · simp only [psi0, h1, ↓reduceIte, Fin.isValue, Pi.smul_apply, Pi.add_apply, smul_eq_mul]
      have hscaled0 : (epsilon β I.Λ m)⁻¹ * (x 0 + z 0) =
          (epsilon β I.Λ m)⁻¹ * x 0 + (((N : ℤ) * z 0 : ℤ) : ℝ) := by
        simpa [latticeShift] using hscaled 0
      change Real.sin (2 * Real.pi *
          ((epsilon β I.Λ m)⁻¹ * (x 0 + (z 0 : ℝ)))) = _
      rw [hscaled0]
      have harg : 2 * Real.pi *
          ((epsilon β I.Λ m)⁻¹ * x 0 + (((N : ℤ) * z 0 : ℤ) : ℝ)) =
          2 * Real.pi * ((epsilon β I.Λ m)⁻¹ * x 0) +
            ((N : ℤ) * z 0 : ℤ) * (2 * Real.pi) := by push_cast; ring
      rw [harg, Real.sin_add_int_mul_two_pi]
    · by_cases h3 : k % 4 = 3
      · simp only [psi0, h3, OfNat.ofNat_ne_one, ↓reduceIte, Fin.isValue, Pi.smul_apply,
          Pi.add_apply, smul_eq_mul]
        have hscaled1 : (epsilon β I.Λ m)⁻¹ * (x 1 + z 1) =
            (epsilon β I.Λ m)⁻¹ * x 1 + (((N : ℤ) * z 1 : ℤ) : ℝ) := by
          simpa [latticeShift] using hscaled 1
        change Real.sin (2 * Real.pi *
            ((epsilon β I.Λ m)⁻¹ * (x 1 + (z 1 : ℝ)))) = _
        rw [hscaled1]
        have harg : 2 * Real.pi *
            ((epsilon β I.Λ m)⁻¹ * x 1 + (((N : ℤ) * z 1 : ℤ) : ℝ)) =
            2 * Real.pi * ((epsilon β I.Λ m)⁻¹ * x 1) +
              ((N : ℤ) * z 1 : ℤ) * (2 * Real.pi) := by push_cast; ring
        rw [harg, Real.sin_add_int_mul_two_pi]
      · simp [psi0, h1, h3]
  unfold psi
  rw [hcore]

theorem BigBoundRegularity.psiTilde_contDiff_infty {β : ℝ} (I : Ingredients β)
    {Φ : ℕ → ℝ → Vec 2 → ℝ} (hΦ : IsStreamSeq I Φ)
    (m : ℕ) (t : ℝ) : ContDiff ℝ (⊤ : ℕ∞) (psiTilde I hΦ m t) := by
  classical
  let S : Finset {k : ℤ // Odd k} :=
    ((I.zetaMK_support_finite m t).preimage
      (fun _ _ _ _ h => Subtype.ext h)).toFinset
  have hrep : psiTilde I hΦ m t = fun x =>
      ∑ k ∈ S, I.hatZetaML m (lIdx β I.Λ m k.1) t * I.zetaMK m k.1 t *
        psi β I.Λ m k.1 (I.xFlowInv hΦ m (lIdx β I.Λ m k.1) t x) := by
    funext x
    unfold psiTilde
    apply tsum_eq_sum
    intro k hk
    have hz : I.zetaMK m k.1 t = 0 := by
      by_contra hn
      have hS : k ∈ S := by
        simp only [S, Set.Finite.mem_toFinset, Set.mem_preimage]
        exact hn
      exact hk hS
    simp [hz]
  rw [hrep]
  apply ContDiff.sum
  intro k hk
  have hinv : ContDiff ℝ (⊤ : ℕ∞)
      (I.xFlowInv hΦ m (lIdx β I.Λ m k.1) t) :=
    (Infra.Section4.amnr_xFlowInv_joint_contDiff_infty I hΦ m
      (lIdx β I.Λ m k.1)).comp
      (by fun_prop : ContDiff ℝ (⊤ : ℕ∞) (fun x : Vec 2 => (t, x)))
  exact (contDiff_const.mul contDiff_const).mul
    ((BigBoundRegularity.psi_contDiff_infty I m k.1).comp hinv)

theorem BigBoundRegularity.psiTilde_isZ2Periodic {β : ℝ} (I : Ingredients β)
    {Φ : ℕ → ℝ → Vec 2 → ℝ} (hΦ : IsStreamSeq I Φ)
    {m : ℕ} (_hm : 1 ≤ m) (t : ℝ) : IsZ2Periodic (psiTilde I hΦ m t) := by
  classical
  let S : Finset {k : ℤ // Odd k} :=
    ((I.zetaMK_support_finite m t).preimage
      (fun _ _ _ _ h => Subtype.ext h)).toFinset
  have hrep (x : Vec 2) : psiTilde I hΦ m t x =
      ∑ k ∈ S, I.hatZetaML m (lIdx β I.Λ m k.1) t * I.zetaMK m k.1 t *
        psi β I.Λ m k.1 (I.xFlowInv hΦ m (lIdx β I.Λ m k.1) t x) := by
    unfold psiTilde
    apply tsum_eq_sum
    intro k hk
    have hz : I.zetaMK m k.1 t = 0 := by
      by_contra hn
      have hS : k ∈ S := by
        simp only [S, Set.Finite.mem_toFinset, Set.mem_preimage]
        exact hn
      exact hk hS
    simp [hz]
  intro z x
  rw [hrep (x + latticeShift z), hrep x]
  apply Finset.sum_congr rfl
  intro k hk
  have hinv := Infra.Section4.amnr_xFlowInv_lattice_equivariant I hΦ m
    (lIdx β I.Λ m k.1) t z x
  rw [hinv, BigBoundRegularity.psi_isZ2Periodic I k.1 z]

theorem BigBoundRegularity.diffusionMatrix_contDiff_infty {β : ℝ} (I : Ingredients β)
    {Φ : ℕ → ℝ → Vec 2 → ℝ} (hΦ : IsStreamSeq I Φ)
    (m : ℕ) (κm t : ℝ) :
    ContDiff ℝ (⊤ : ℕ∞) (diffusionMatrix I hΦ m κm t) := by
  have hpsi : ContDiff ℝ (⊤ : ℕ∞) (psiTilde I hΦ m t) :=
    BigBoundRegularity.psiTilde_contDiff_infty I hΦ m t
  exact contDiff_const.add (hpsi.smul contDiff_const)

theorem BigBoundRegularity.diffusionMatrix_isZ2Periodic {β : ℝ} (I : Ingredients β)
    {Φ : ℕ → ℝ → Vec 2 → ℝ} (hΦ : IsStreamSeq I Φ)
    {m : ℕ} (hm : 1 ≤ m) (κm t : ℝ) :
    IsZ2Periodic (diffusionMatrix I hΦ m κm t) := by
  intro z x
  change κm • (1 : Matrix (Fin 2) (Fin 2) ℝ) +
      psiTilde I hΦ m t (x + latticeShift z) • sigmaMat =
    κm • (1 : Matrix (Fin 2) (Fin 2) ℝ) + psiTilde I hΦ m t x • sigmaMat
  rw [BigBoundRegularity.psiTilde_isZ2Periodic I hΦ hm t z x]

theorem BigBoundRegularity.chiTilde_isZ2Periodic {β : ℝ} (I : Ingredients β)
    {Φ : ℕ → ℝ → Vec 2 → ℝ} (hΦ : IsStreamSeq I Φ)
    (m : ℕ) (κm : ℝ) (k : ℤ) (t : ℝ) : IsZ2Periodic (I.chiTilde hΦ m κm k t) := by
  intro z x
  have hinv := Infra.Section4.amnr_xFlowInv_lattice_equivariant I hΦ m
    (lIdx β I.Λ m k) t z x
  have hu := AVenhance.Infra.Section5.Integration.uShear_isZ2Periodic
    β I.Λ m k z (I.xFlowInv hΦ m (lIdx β I.Λ m k) t x)
  simp only [Ingredients.chiTilde, Ingredients.chiMK]
  rw [hinv, hu]

theorem G_contDiff_infty {β : ℝ} (I : Ingredients β)
    {Φ : ℕ → ℝ → Vec 2 → ℝ} (hΦ : IsStreamSeq I Φ)
    (m : ℕ) (T : ℝ → Vec 2 → ℝ) (t : ℝ) (l : ℤ)
    (hT : ContDiff ℝ (⊤ : ℕ∞) (T t)) :
    ContDiff ℝ (⊤ : ℕ∞) (G I hΦ m T l t) := by
  let f : Vec 2 → ℝ := fun y => T t (I.xFlow hΦ m l t y)
  have hX : ContDiff ℝ (⊤ : ℕ∞) (I.xFlow hΦ m l t) :=
    (Infra.Section4.amnr_xFlow_joint_contDiff_infty I hΦ m l).comp
      (by fun_prop : ContDiff ℝ (⊤ : ℕ∞) (fun y : Vec 2 => (t, y)))
  have hY : ContDiff ℝ (⊤ : ℕ∞) (I.xFlowInv hΦ m l t) :=
    (Infra.Section4.amnr_xFlowInv_joint_contDiff_infty I hΦ m l).comp
      (by fun_prop : ContDiff ℝ (⊤ : ℕ∞) (fun y : Vec 2 => (t, y)))
  have hgrad : ContDiff ℝ (⊤ : ℕ∞) (spaceGrad f) :=
    Infra.Section4.iterate_gradient_smooth (hT.comp hX)
  change ContDiff ℝ (⊤ : ℕ∞) (spaceGrad f ∘ I.xFlowInv hΦ m l t)
  exact hgrad.comp hY

theorem G_isZ2Periodic {β : ℝ} (I : Ingredients β)
    {Φ : ℕ → ℝ → Vec 2 → ℝ} (hΦ : IsStreamSeq I Φ)
    (m : ℕ) (T : ℝ → Vec 2 → ℝ) (t : ℝ) (l : ℤ)
    (hTper : IsZ2Periodic (T t)) (hTsm : ContDiff ℝ 1 (T t)) :
    IsZ2Periodic (G I hΦ m T l t) := by
  let f : Vec 2 → ℝ := fun y => T t (I.xFlow hΦ m l t y)
  have hXper := Infra.Section4.amnr_xFlow_lattice_equivariant I hΦ m l t
  have hYper := Infra.Section4.amnr_xFlowInv_lattice_equivariant I hΦ m l t
  have hfper : IsZ2Periodic f := by
    intro z y
    dsimp [f]
    rw [hXper z y]
    exact hTper z (I.xFlow hΦ m l t y)
  have hX : ContDiff ℝ 1 (I.xFlow hΦ m l t) := by
    exact ((Infra.Section4.amnr_xFlow_joint_contDiff_infty I hΦ m l).of_le
      (by simp)).comp (by fun_prop : ContDiff ℝ 1 (fun y : Vec 2 => (t, y)))
  have hgradper := Infra.Section4.iterate_gradient_periodic (hTsm.comp hX) hfper
  intro z x
  change spaceGrad f (I.xFlowInv hΦ m l t (x + latticeShift z)) =
    spaceGrad f (I.xFlowInv hΦ m l t x)
  rw [hYper z x]
  exact hgradper z _

theorem BigBoundRegularity.gradG_contDiff_infty {β : ℝ} (I : Ingredients β)
    {Φ : ℕ → ℝ → Vec 2 → ℝ} (hΦ : IsStreamSeq I Φ)
    (m : ℕ) (T : ℝ → Vec 2 → ℝ) (t : ℝ) (l : ℤ)
    (hT : ContDiff ℝ (⊤ : ℕ∞) (T t)) :
    ContDiff ℝ (⊤ : ℕ∞) (gradG I hΦ m T l t) := by
  have hG := G_contDiff_infty I hΦ m T t l hT
  apply contDiff_pi.mpr
  intro i
  apply contDiff_pi.mpr
  intro j
  change ContDiff ℝ (⊤ : ℕ∞)
    (fun x => spaceGrad (fun y => G I hΦ m T l t y j) x i)
  exact contDiff_pi.mp
    (Infra.Section4.iterate_gradient_smooth (contDiff_pi.mp hG j)) i

theorem BigBoundRegularity.gradG_isZ2Periodic {β : ℝ} (I : Ingredients β)
    {Φ : ℕ → ℝ → Vec 2 → ℝ} (hΦ : IsStreamSeq I Φ)
    (m : ℕ) (T : ℝ → Vec 2 → ℝ) (t : ℝ) (l : ℤ)
    (hGper : IsZ2Periodic (G I hΦ m T l t))
    (hGsm : ContDiff ℝ (⊤ : ℕ∞) (G I hΦ m T l t)) :
    IsZ2Periodic (gradG I hΦ m T l t) := by
  intro z x
  ext i j
  exact congrFun (Infra.Section4.iterate_gradient_periodic
    ((contDiff_infty.mp (contDiff_pi.mp hGsm j)) 1)
    (fun z' y => congrFun (hGper z' y) j) z x) i

theorem BigBoundRegularity.normie2Flux_smooth_of_iterates {β : ℝ} (I : Ingredients β)
    {Φ : ℕ → ℝ → Vec 2 → ℝ} (hΦ : IsStreamSeq I Φ)
    {m : ℕ} (hm : 1 ≤ m) (κm κprev : ℝ) {θ₀ : Vec 2 → ℝ}
    {θprev : ℝ → Vec 2 → ℝ} {T : ℕ → ℝ → Vec 2 → ℝ}
    (hθprev : IsClassicalSol (streamVel (Φ (m - 1))) κprev
      (fun _ _ => 0) θ₀ θprev)
    (hT : I.IsTIterates hΦ m κm κprev θ₀ θprev T)
    {t : ℝ} (ht : 0 < t) :
    ContDiff ℝ (⊤ : ℕ∞) (normie2Flux I hΦ m κm (T (Nstar β)) t) := by
  have hD : ContDiff ℝ (⊤ : ℕ∞) (diffusionMatrix I hΦ m κm t) := by
    have hpsi : ContDiff ℝ (⊤ : ℕ∞) (psiTilde I hΦ m t) := by
      classical
      let S : Finset {k : ℤ // Odd k} :=
        ((I.zetaMK_support_finite m t).preimage
          (fun _ _ _ _ h => Subtype.ext h)).toFinset
      have hrep : psiTilde I hΦ m t = fun x =>
          ∑ k ∈ S, I.hatZetaML m (lIdx β I.Λ m k.1) t * I.zetaMK m k.1 t *
            psi β I.Λ m k.1 (I.xFlowInv hΦ m (lIdx β I.Λ m k.1) t x) := by
        funext x
        unfold psiTilde
        apply tsum_eq_sum
        intro k hk
        have hz : I.zetaMK m k.1 t = 0 := by
          by_contra hn
          have hS : k ∈ S := by
            simp only [S, Set.Finite.mem_toFinset, Set.mem_preimage]
            exact hn
          exact hk hS
        simp [hz]
      rw [hrep]
      apply ContDiff.sum
      intro k hk
      have hinv : ContDiff ℝ (⊤ : ℕ∞) (I.xFlowInv hΦ m
          (lIdx β I.Λ m k.1) t) :=
        (Infra.Section4.amnr_xFlowInv_joint_contDiff_infty I hΦ m
          (lIdx β I.Λ m k.1)).comp
            (by fun_prop : ContDiff ℝ (⊤ : ℕ∞) (fun x : Vec 2 => (t, x)))
      exact (contDiff_const.mul contDiff_const).mul
        ((BigBoundRegularity.psi_contDiff_infty I m k.1).comp hinv)
    exact contDiff_const.add (hpsi.smul contDiff_const)
  have hHm := BigBoundRegularity.hm_slice_contDiff_infty I hΦ hm hθprev hT ht
  have hgrad := Infra.Section4.iterate_gradient_smooth hHm
  unfold normie2Flux
  exact BigBoundRegularity.matrixMulVec_contDiff_infty hD hgrad

theorem BigBoundRegularity.chiTilde_contDiff_infty {β : ℝ} (I : Ingredients β)
    {Φ : ℕ → ℝ → Vec 2 → ℝ} (hΦ : IsStreamSeq I Φ)
    (m : ℕ) (κm : ℝ) (k : ℤ) (t : ℝ) :
    ContDiff ℝ (⊤ : ℕ∞) (I.chiTilde hΦ m κm k t) := by
  have hY : ContDiff ℝ (⊤ : ℕ∞)
      (I.xFlowInv hΦ m (lIdx β I.Λ m k) t) :=
    (Infra.Section4.amnr_xFlowInv_joint_contDiff_infty I hΦ m
      (lIdx β I.Λ m k)).comp
      (by fun_prop : ContDiff ℝ (⊤ : ℕ∞) (fun x : Vec 2 => (t, x)))
  apply contDiff_pi.mpr
  intro i
  have hu : ContDiff ℝ (⊤ : ℕ∞)
      (fun x => uShear β I.Λ m k (I.xFlowInv hΦ m (lIdx β I.Λ m k) t x) i) :=
    (contDiff_apply ℝ ℝ i).comp ((contDiff_uShear' β I.Λ m k).comp hY)
  simpa [Ingredients.chiTilde, Ingredients.chiMK] using
    (contDiff_const : ContDiff ℝ (⊤ : ℕ∞)
      (fun _ : Vec 2 => -(I.corrTime κm m k t))).mul hu

theorem BigBoundRegularity.chiGradG_contDiff_infty {β : ℝ} (I : Ingredients β)
    {Φ : ℕ → ℝ → Vec 2 → ℝ} (hΦ : IsStreamSeq I Φ)
    (m : ℕ) (κm : ℝ) (T : ℝ → Vec 2 → ℝ) (k : ℤ) (t : ℝ)
    (hT : ContDiff ℝ (⊤ : ℕ∞) (T t)) :
    ContDiff ℝ (⊤ : ℕ∞) (chiGradG I hΦ m κm T k t) := by
  have hχ := BigBoundRegularity.chiTilde_contDiff_infty I hΦ m κm k t
  have hG := BigBoundRegularity.gradG_contDiff_infty I hΦ m T t (lIdx β I.Λ m k) hT
  apply contDiff_pi.mpr
  intro i
  change ContDiff ℝ (⊤ : ℕ∞) (fun x => ∑ j : Fin 2,
    I.chiTilde hΦ m κm k t x j * gradG I hΦ m T
      (lIdx β I.Λ m k) t x i j)
  apply ContDiff.sum
  intro j hj
  exact (contDiff_pi.mp hχ j).mul
    (contDiff_pi.mp (contDiff_pi.mp hG i) j)

theorem BigBoundRegularity.chiGradG_isZ2Periodic {β : ℝ} (I : Ingredients β)
    {Φ : ℕ → ℝ → Vec 2 → ℝ} (hΦ : IsStreamSeq I Φ)
    (m : ℕ) (κm : ℝ) (T : ℝ → Vec 2 → ℝ) (k : ℤ) (t : ℝ)
    (hχ : IsZ2Periodic (I.chiTilde hΦ m κm k t))
    (hG : IsZ2Periodic (gradG I hΦ m T (lIdx β I.Λ m k) t)) :
    IsZ2Periodic (chiGradG I hΦ m κm T k t) := by
  intro z x
  funext i
  unfold chiGradG
  apply Finset.sum_congr rfl
  intro j hj
  rw [congrFun (hχ z x) j, congrFun (congrFun (hG z x) i) j]

theorem BigBoundRegularity.twistie3Flux_regular_of_iterates {β : ℝ} (I : Ingredients β)
    {Φ : ℕ → ℝ → Vec 2 → ℝ} (hΦ : IsStreamSeq I Φ)
    {m : ℕ} (hm : 1 ≤ m) (κm κprev : ℝ) {θ₀ : Vec 2 → ℝ}
    {θprev : ℝ → Vec 2 → ℝ}
    (hθprev : IsClassicalSol (streamVel (Φ (m - 1))) κprev
      (fun _ _ => 0) θ₀ θprev)
    {T : ℕ → ℝ → Vec 2 → ℝ}
    (hT : I.IsTIterates hΦ m κm κprev θ₀ θprev T)
    {t : ℝ} (ht : 0 < t) :
    ContDiff ℝ (⊤ : ℕ∞) (twistie3Flux I hΦ m κm (T (Nstar β)) t) ∧
      IsZ2Periodic (twistie3Flux I hΦ m κm (T (Nstar β)) t) := by
  classical
  let Tlast := T (Nstar β)
  let U := (Infra.Section3.xiMK_odd_support_finite I hm t).toFinset
  have hTsm : ContDiff ℝ (⊤ : ℕ∞) (Tlast t) :=
    Infra.Section4.tIterate_space_contDiff I hΦ hT hθprev le_rfl ht.le
  have hTper : IsZ2Periodic (Tlast t) :=
    Infra.Section4.tIterate_periodic I hΦ hT hθprev le_rfl ht.le
  have hgrad : ContDiff ℝ (⊤ : ℕ∞) (spaceGrad (Tlast t)) :=
    Infra.Section4.iterate_gradient_smooth hTsm
  have hgradper : IsZ2Periodic (spaceGrad (Tlast t)) :=
    Infra.Section4.iterate_gradient_periodic
      ((contDiff_infty.mp hTsm) 1) hTper
  have hD : ContDiff ℝ (⊤ : ℕ∞) (diffusionMatrix I hΦ m κm t) :=
    BigBoundRegularity.diffusionMatrix_contDiff_infty I hΦ m κm t
  have hDper : IsZ2Periodic (diffusionMatrix I hΦ m κm t) :=
    BigBoundRegularity.diffusionMatrix_isZ2Periodic I hΦ hm κm t
  have hG (k : {k : ℤ // Odd k}) :
      ContDiff ℝ (⊤ : ℕ∞) (G I hΦ m Tlast (lIdx β I.Λ m k.1) t) :=
    G_contDiff_infty I hΦ m Tlast t (lIdx β I.Λ m k.1) hTsm
  have hGper (k : {k : ℤ // Odd k}) :
      IsZ2Periodic (G I hΦ m Tlast (lIdx β I.Λ m k.1) t) :=
    G_isZ2Periodic I hΦ m Tlast t (lIdx β I.Λ m k.1) hTper
      ((contDiff_infty.mp hTsm) 1)
  have hrep : twistie3Flux I hΦ m κm Tlast t = fun x =>
      ∑ k ∈ U, I.xiMK m k.1 t •
        (diffusionMatrix I hΦ m κm t x).mulVec
          (spaceGrad (Tlast t) x - G I hΦ m Tlast
            (lIdx β I.Λ m k.1) t x) := by
    funext x
    exact xiMK_odd_tsum_eq_subtype_support_sum I m hm t (fun k =>
      (diffusionMatrix I hΦ m κm t x).mulVec
        (spaceGrad (Tlast t) x - G I hΦ m Tlast
          (lIdx β I.Λ m k.1) t x))
  constructor
  · rw [hrep]
    apply ContDiff.sum
    intro k hk
    have hv := (hgrad.sub (hG k))
    exact (contDiff_const : ContDiff ℝ (⊤ : ℕ∞)
      (fun _ : Vec 2 => I.xiMK m k.1 t)).smul
        (BigBoundRegularity.matrixMulVec_contDiff_infty hD hv)
  · rw [hrep]
    intro z x
    apply Finset.sum_congr rfl
    intro k hk
    rw [hDper z x, hgradper z x, hGper k z x]

theorem BigBoundRegularity.normie1Flux_regular_of_iterates {β : ℝ} (I : Ingredients β)
    {Φ : ℕ → ℝ → Vec 2 → ℝ} (hΦ : IsStreamSeq I Φ)
    {m : ℕ} (hm : 1 ≤ m) (κm κprev : ℝ) {θ₀ : Vec 2 → ℝ}
    {θprev : ℝ → Vec 2 → ℝ}
    (hθprev : IsClassicalSol (streamVel (Φ (m - 1))) κprev
      (fun _ _ => 0) θ₀ θprev)
    {T : ℕ → ℝ → Vec 2 → ℝ}
    (hT : I.IsTIterates hΦ m κm κprev θ₀ θprev T)
    {t : ℝ} (ht : 0 < t) :
    ContDiff ℝ (⊤ : ℕ∞) (normie1Flux I hΦ m κm (T (Nstar β)) t) ∧
      IsZ2Periodic (normie1Flux I hΦ m κm (T (Nstar β)) t) := by
  classical
  let Tlast := T (Nstar β)
  let U := (Infra.Section3.xiMK_odd_support_finite I hm t).toFinset
  have hTsm : ContDiff ℝ (⊤ : ℕ∞) (Tlast t) :=
    Infra.Section4.tIterate_space_contDiff I hΦ hT hθprev le_rfl ht.le
  have hTper : IsZ2Periodic (Tlast t) :=
    Infra.Section4.tIterate_periodic I hΦ hT hθprev le_rfl ht.le
  have hD : ContDiff ℝ (⊤ : ℕ∞) (diffusionMatrix I hΦ m κm t) :=
    BigBoundRegularity.diffusionMatrix_contDiff_infty I hΦ m κm t
  have hDper : IsZ2Periodic (diffusionMatrix I hΦ m κm t) :=
    BigBoundRegularity.diffusionMatrix_isZ2Periodic I hΦ hm κm t
  have hgradG (k : {k : ℤ // Odd k}) :
      ContDiff ℝ (⊤ : ℕ∞) (gradG I hΦ m Tlast
        (lIdx β I.Λ m k.1) t) :=
    BigBoundRegularity.gradG_contDiff_infty I hΦ m Tlast t (lIdx β I.Λ m k.1) hTsm
  have hgradGper (k : {k : ℤ // Odd k}) :
      IsZ2Periodic (gradG I hΦ m Tlast (lIdx β I.Λ m k.1) t) := by
    exact BigBoundRegularity.gradG_isZ2Periodic I hΦ m Tlast t (lIdx β I.Λ m k.1)
      (G_isZ2Periodic I hΦ m Tlast t (lIdx β I.Λ m k.1) hTper
        ((contDiff_infty.mp hTsm) 1))
      (G_contDiff_infty I hΦ m Tlast t (lIdx β I.Λ m k.1) hTsm)
  have hχ (k : {k : ℤ // Odd k}) :
      IsZ2Periodic (I.chiTilde hΦ m κm k.1 t) :=
    BigBoundRegularity.chiTilde_isZ2Periodic I hΦ m κm k.1 t
  have hrep : normie1Flux I hΦ m κm Tlast t = fun x =>
      ∑ k ∈ U, I.xiMK m k.1 t •
        (diffusionMatrix I hΦ m κm t x).mulVec
          (chiGradG I hΦ m κm Tlast k.1 t x) := by
    funext x
    exact xiMK_odd_tsum_eq_subtype_support_sum I m hm t (fun k =>
      (diffusionMatrix I hΦ m κm t x).mulVec
        (chiGradG I hΦ m κm Tlast k.1 t x))
  constructor
  · rw [hrep]
    apply ContDiff.sum
    intro k hk
    have hχsm := BigBoundRegularity.chiTilde_contDiff_infty I hΦ m κm k.1 t
    have hv := BigBoundRegularity.chiGradG_contDiff_infty I hΦ m κm Tlast k.1 t hTsm
    exact (contDiff_const : ContDiff ℝ (⊤ : ℕ∞)
      (fun _ : Vec 2 => I.xiMK m k.1 t)).smul
        (BigBoundRegularity.matrixMulVec_contDiff_infty hD hv)
  · rw [hrep]
    intro z x
    apply Finset.sum_congr rfl
    intro k hk
    have hχG := BigBoundRegularity.chiGradG_isZ2Periodic I hΦ m κm Tlast k.1 t
      (hχ k) (hgradGper k)
    rw [hDper z x, hχG z x]

theorem BigBoundRegularity.normie2Flux_periodic_of_iterates {β : ℝ} (I : Ingredients β)
    {Φ : ℕ → ℝ → Vec 2 → ℝ} (hΦ : IsStreamSeq I Φ)
    {m : ℕ} (hm : 1 ≤ m) (κm κprev : ℝ) {θ₀ : Vec 2 → ℝ}
    {θprev : ℝ → Vec 2 → ℝ}
    (hθprev : IsClassicalSol (streamVel (Φ (m - 1))) κprev
      (fun _ _ => 0) θ₀ θprev)
    {T : ℕ → ℝ → Vec 2 → ℝ}
    (hT : I.IsTIterates hΦ m κm κprev θ₀ θprev T)
    {t : ℝ} (ht : 0 < t) :
    IsZ2Periodic (normie2Flux I hΦ m κm (T (Nstar β)) t) := by
  let Tlast := T (Nstar β)
  have hDper := BigBoundRegularity.diffusionMatrix_isZ2Periodic I hΦ hm κm t
  have hHmper := BigBoundRegularity.hm_periodic_of_iterates I hΦ hm hθprev hT ht
  have hHm := BigBoundRegularity.hm_slice_contDiff_infty I hΦ hm hθprev hT ht
  have hgradper := Infra.Section4.iterate_gradient_periodic
    ((contDiff_infty.mp hHm) 1) hHmper
  intro z x
  unfold normie2Flux
  change (diffusionMatrix I hΦ m κm t (x + latticeShift z)).mulVec
      (spaceGrad (I.Hm hΦ m κm Tlast t) (x + latticeShift z)) = _
  rw [hDper z x, hgradper z x]

/-- A smooth periodic divergence has zero integral on the unit cell.
This is the `u = 1` case of torus integration by parts. -/
theorem meanZeroOn_vecDiv_of_contDiff_periodic {F : Vec 2 → Vec 2}
    (hF : ContDiff ℝ (⊤ : ℕ∞) F) (hper : IsZ2Periodic F) :
    MeanZeroOn unitCube (fun x => vecDiv F x) := by
  unfold MeanZeroOn
  have hconst : ContDiff ℝ (⊤ : ℕ∞) (fun _ : Vec 2 => (1 : ℝ)) := contDiff_const
  have hconstPer : IsZ2Periodic (fun _ : Vec 2 => (1 : ℝ)) := by
    intro k x
    rfl
  have hparts := AVenhance.Infra.Section4.iterate_divergence_pairing
    hconst hconstPer hF hper
  have hgrad : (fun x => spaceGrad (fun _ : Vec 2 => (1 : ℝ)) x) =
      fun _ => (0 : Vec 2) := by
    funext x
    funext i
    simp [spaceGrad, fderiv_const_apply]
  calc
    (∫ x in unitCube, vecDiv F x) =
        ∫ x in unitCube, (1 : ℝ) * vecDiv F x := by
          congr 1
          funext x
          ring
    _ = 0 := by rw [hparts]; simp [hgrad, vecDot]

/-- Product rule for the divergence of a scalar times a vector field. -/
theorem vecDiv_scalar_mul {q : Vec 2 → ℝ} {F : Vec 2 → Vec 2} {x : Vec 2}
    (hq : ContDiff ℝ (⊤ : ℕ∞) q) (hF : ContDiff ℝ (⊤ : ℕ∞) F) :
    vecDiv (fun y => q y • F y) x =
      vecDot (spaceGrad q x) (F x) + q x * vecDiv F x := by
  have hqDiff := hq.differentiable (by simp) x
  unfold vecDiv vecDot
  have hterm (i : Fin 2) :
      spaceGrad (fun y => q y • F y i) x i =
        spaceGrad q x i * F x i + q x * spaceGrad (fun y => F y i) x i := by
    change fderiv ℝ (fun y => q y * F y i) x (basisVec i) = _
    have hFi : ContDiff ℝ (⊤ : ℕ∞) (fun y => F y i) :=
      contDiff_pi.mp hF i
    have hmul := fderiv_mul hqDiff (hFi.differentiable (by simp) x)
    have hfun : (fun y => q y * F y i) = q * (fun y => F y i) := by
      funext y
      rfl
    have hmul' : fderiv ℝ (fun y => q y * F y i) x =
        q x • fderiv ℝ (fun y => F y i) x +
          F x i • fderiv ℝ q x := by
      rw [hfun, hmul]
    rw [hmul']
    simp [spaceGrad, smul_eq_mul]
    ring
  calc
    (∑ i : Fin 2, spaceGrad (fun y => q y • F y i) x i) =
        ∑ i : Fin 2, (spaceGrad q x i * F x i +
          q x * spaceGrad (fun y => F y i) x i) := by
            apply Finset.sum_congr rfl
            intro i hi
            exact hterm i
    _ = (∑ i : Fin 2, spaceGrad q x i * F x i) +
        q x * ∑ i : Fin 2, spaceGrad (fun y => F y i) x i := by
          rw [Finset.sum_add_distrib, Finset.mul_sum]

theorem BigBoundRegularity.flowGradK_contDiff_infty {β : ℝ} (I : Ingredients β)
    {Φ : ℕ → ℝ → Vec 2 → ℝ} (hΦ : IsStreamSeq I Φ)
    (m : ℕ) (k : ℤ) (t : ℝ) :
    ContDiff ℝ (⊤ : ℕ∞) (flowGradK I hΦ m k t) := by
  apply contDiff_pi.mpr
  intro i
  apply contDiff_pi.mpr
  intro j
  exact (Infra.Section4.amnr_flowGrad_joint_contDiff_infty I hΦ m
    (lIdx β I.Λ m k) i j).comp
      (by fun_prop : ContDiff ℝ (⊤ : ℕ∞)
        (fun x : Vec 2 => (t, x)))

theorem BigBoundRegularity.flowGradK_isZ2Periodic {β : ℝ} (I : Ingredients β)
    {Φ : ℕ → ℝ → Vec 2 → ℝ} (hΦ : IsStreamSeq I Φ)
    (m : ℕ) (k : ℤ) (t : ℝ) : IsZ2Periodic (flowGradK I hΦ m k t) := by
  intro z x
  ext i j
  exact Infra.Section4.amnr_flowGrad_spatial_periodic I hΦ m
    (lIdx β I.Λ m k) t i j z x

/-- Corrector flux transformed by the transposed flow Jacobian. -/
def BigBoundRegularity.chiPushforwardFlux {β : ℝ} (I : Ingredients β)
    {Φ : ℕ → ℝ → Vec 2 → ℝ} (hΦ : IsStreamSeq I Φ)
    (m : ℕ) (κ : ℝ) (k : ℤ) (t : ℝ) : Vec 2 → Vec 2 :=
  fun x => (flowGradK I hΦ m k t x).transpose.mulVec
    (I.chiTilde hΦ m κ k t x)

theorem BigBoundRegularity.chiPushforwardFlux_regular {β : ℝ} (I : Ingredients β)
    {Φ : ℕ → ℝ → Vec 2 → ℝ} (hΦ : IsStreamSeq I Φ)
    (m : ℕ) (κ : ℝ) (k : ℤ) (t : ℝ) :
    ContDiff ℝ (⊤ : ℕ∞) (BigBoundRegularity.chiPushforwardFlux I hΦ m κ k t) ∧
      IsZ2Periodic (BigBoundRegularity.chiPushforwardFlux I hΦ m κ k t) := by
  have hF := BigBoundRegularity.flowGradK_contDiff_infty I hΦ m k t
  have hχ := BigBoundRegularity.chiTilde_contDiff_infty I hΦ m κ k t
  have hFper := BigBoundRegularity.flowGradK_isZ2Periodic I hΦ m k t
  have hχper := BigBoundRegularity.chiTilde_isZ2Periodic I hΦ m κ k t
  constructor
  · apply contDiff_pi.mpr
    intro i
    change ContDiff ℝ (⊤ : ℕ∞) (fun x => ∑ j : Fin 2,
      (flowGradK I hΦ m k t x).transpose i j *
        I.chiTilde hΦ m κ k t x j)
    apply ContDiff.sum
    intro j hj
    exact (contDiff_pi.mp (contDiff_pi.mp hF j) i).mul
      (contDiff_pi.mp hχ j)
  · intro z x
    funext i
    change ∑ j : Fin 2,
        (flowGradK I hΦ m k t (x + latticeShift z)).transpose i j *
          I.chiTilde hΦ m κ k t (x + latticeShift z) j =
      ∑ j : Fin 2, (flowGradK I hΦ m k t x).transpose i j *
        I.chiTilde hΦ m κ k t x j
    apply Finset.sum_congr rfl
    intro j hj
    rw [hFper z x, hχper z x]

theorem BigBoundRegularity.sigmaGrad_div_zero {f : Vec 2 → ℝ}
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) (x : Vec 2) :
    vecDiv (fun y => sigmaMat.mulVec (spaceGrad f y)) x = 0 := by
  have hcomm := Infra.Section4.iterate_coordinate_derivatives_commute hf
    (0 : Fin 2) 1 x
  unfold vecDiv
  simp only [Fin.sum_univ_two]
  have h0 : (fun y => sigmaMat.mulVec (spaceGrad f y) 0) =
      fun y => -spaceGrad f y 1 := by
    funext y
    simp [sigmaMat, Matrix.mulVec, dotProduct, Fin.sum_univ_two]
  have h1 : (fun y => sigmaMat.mulVec (spaceGrad f y) 1) =
      fun y => spaceGrad f y 0 := by
    funext y
    simp [sigmaMat, Matrix.mulVec, dotProduct, Fin.sum_univ_two]
  rw [h0, h1]
  have hneg : spaceGrad (fun y => -(spaceGrad f y 1)) x 0 =
      -spaceGrad (fun y => spaceGrad f y 1) x 0 := by
    simp [spaceGrad]
  rw [hneg]
  rw [hcomm]
  ring

theorem BigBoundRegularity.chiMK_div_zero {β : ℝ} (I : Ingredients β)
    (m : ℕ) (κ : ℝ) (k : ℤ) (t : ℝ) (x : Vec 2) :
    vecDiv (fun y => I.chiMK κ m k t y) x = 0 := by
  have hε : epsilon β I.Λ m ≠ 0 :=
    ne_of_gt (Infra.Cutoff.epsilon_pos I.one_lt_beta I.beta_lt
      I.two_pow_seven_le)
  have hu := Infra.Section3.uShear_eq_sigma_spaceGrad (β := β)
    (Λ := I.Λ) (m := m) k
    (hε := hε)
  have hψ : ContDiff ℝ (⊤ : ℕ∞) (psi β I.Λ m k) :=
    BigBoundRegularity.psi_contDiff_infty I m k
  have hrot : vecDiv (fun y => sigmaMat.mulVec
      (spaceGrad (psi β I.Λ m k) y)) x = 0 := BigBoundRegularity.sigmaGrad_div_zero hψ x
  have hfield : (fun y => I.chiMK κ m k t y) =
      fun y => (-(I.corrTime κ m k t)) •
        (sigmaMat.mulVec (spaceGrad (psi β I.Λ m k) y)) := by
    funext y
    rw [show I.chiMK κ m k t y =
      (-(I.corrTime κ m k t)) • uShear β I.Λ m k y by rfl, hu]
  rw [hfield]
  have hF : ContDiff ℝ (⊤ : ℕ∞)
      (fun y => sigmaMat.mulVec (spaceGrad (psi β I.Λ m k) y)) := by
    have hgrad := Infra.Section4.iterate_gradient_smooth hψ
    apply contDiff_pi.mpr
    intro i
    change ContDiff ℝ (⊤ : ℕ∞)
      (fun y => ∑ j : Fin 2, sigmaMat i j * spaceGrad
        (psi β I.Λ m k) y j)
    apply ContDiff.sum
    intro j hj
    exact contDiff_const.mul (contDiff_pi.mp hgrad j)
  have hmul := vecDiv_scalar_mul
    (q := fun _ : Vec 2 => -(I.corrTime κ m k t))
    (F := fun y => sigmaMat.mulVec (spaceGrad (psi β I.Λ m k) y))
    (x := x) contDiff_const hF
  rw [hmul, hrot]
  simp [spaceGrad, fderiv_const_apply, vecDot]

theorem BigBoundRegularity.chiPushforwardFlux_div_zero {β : ℝ} (I : Ingredients β)
    {Φ : ℕ → ℝ → Vec 2 → ℝ} (hΦ : IsStreamSeq I Φ)
    (m : ℕ) (κ : ℝ) (k : ℤ) (t : ℝ) (x : Vec 2) :
    vecDiv (BigBoundRegularity.chiPushforwardFlux I hΦ m κ k t) x = 0 := by
  have hdiv := Infra.Section5.streamVel_spatialDivergence_eq_zero I hΦ m
  have hχ : ContDiff ℝ 2 (fun y => I.chiMK κ m k t y) := by
    apply contDiff_pi.mpr
    intro i
    exact (Infra.Section3.chiMK_component_contDiff_two I κ k i).comp
      (by fun_prop : ContDiff ℝ 2 (fun y : Vec 2 => (t, y)))
  have hpiola := Infra.Section5.xFlowInv_cofactorPiola_of_streamSeq
    I hΦ m (lIdx β I.Λ m k) t x
    ((hχ.differentiable (by norm_num) _).hasFDerivAt)
  have hfield : BigBoundRegularity.chiPushforwardFlux I hΦ m κ k t = fun y =>
      (rowCofactor (gradMatrix
        (I.xFlowInv hΦ m (lIdx β I.Λ m k) t) y)).mulVec
        (I.chiMK κ m k t
          (I.xFlowInv hΦ m (lIdx β I.Λ m k) t y)) := by
    funext y
    have hc := Infra.Section5.xFlowInv_rowCofactor_eq_flowGrad_transpose
      I hΦ m (lIdx β I.Λ m k) t y hdiv
    change (I.flowGrad hΦ m (lIdx β I.Λ m k) t y).transpose.mulVec
        (I.chiTilde hΦ m κ k t y) = _
    rw [hc]
    rfl
  rw [hfield]
  simpa using hpiola.trans
    (BigBoundRegularity.chiMK_div_zero I m κ k t (I.xFlowInv hΦ m (lIdx β I.Λ m k) t x))

/-- Time derivative of each component of the cell corrector. -/
def chiMKTimeDerivative {β : ℝ} (I : Ingredients β)
    (m : ℕ) (κ : ℝ) (k : ℤ) (t : ℝ) : Vec 2 → Vec 2 :=
  fun y j => deriv (fun s => I.chiMK κ m k s y j) t

theorem BigBoundRegularity.chiMKTimeDerivative_eq_shear {β : ℝ} (I : Ingredients β)
    (m : ℕ) (κ : ℝ) (k : ℤ) (t : ℝ) :
    chiMKTimeDerivative I m κ k t = fun y =>
      (-(I.zetaProd m k t -
        (4 * Real.pi ^ 2 * κ / epsilon β I.Λ m ^ 2) *
          I.corrTime κ m k t)) • uShear β I.Λ m k y := by
  funext y j
  exact (Infra.Section3.chiMK_component_hasDerivAt I κ k t y j).deriv

theorem BigBoundRegularity.chiMKTimeDerivative_regular {β : ℝ} (I : Ingredients β)
    {m : ℕ} (_hm : 1 ≤ m) (κ : ℝ) (k : ℤ) (t : ℝ) :
    ContDiff ℝ (⊤ : ℕ∞) (chiMKTimeDerivative I m κ k t) ∧
      IsZ2Periodic (chiMKTimeDerivative I m κ k t) ∧
      (∀ x, vecDiv (chiMKTimeDerivative I m κ k t) x = 0) := by
  have hrep := BigBoundRegularity.chiMKTimeDerivative_eq_shear I m κ k t
  have hu : ContDiff ℝ (⊤ : ℕ∞) (uShear β I.Λ m k) :=
    contDiff_uShear' β I.Λ m k
  have huper := AVenhance.Infra.Section5.Integration.uShear_isZ2Periodic
    β I.Λ m k
  have hε : epsilon β I.Λ m ≠ 0 :=
    ne_of_gt (Infra.Cutoff.epsilon_pos I.one_lt_beta I.beta_lt
      I.two_pow_seven_le)
  have husigma (x : Vec 2) := Infra.Section3.uShear_eq_sigma_spaceGrad
    (β := β) (Λ := I.Λ) (m := m) k x hε
  have hψ : ContDiff ℝ (⊤ : ℕ∞) (psi β I.Λ m k) :=
    BigBoundRegularity.psi_contDiff_infty I m k
  have huEq : uShear β I.Λ m k =
      fun x => sigmaMat.mulVec (spaceGrad (psi β I.Λ m k) x) := by
    funext x
    exact husigma x
  have hdivu (x : Vec 2) : vecDiv (uShear β I.Λ m k) x = 0 := by
    rw [huEq]
    exact BigBoundRegularity.sigmaGrad_div_zero hψ x
  constructor
  · rw [hrep]
    exact (contDiff_const : ContDiff ℝ (⊤ : ℕ∞)
      (fun _ : Vec 2 => -(I.zetaProd m k t -
        (4 * Real.pi ^ 2 * κ / epsilon β I.Λ m ^ 2) *
          I.corrTime κ m k t))).smul hu
  constructor
  · rw [hrep]
    intro z x
    change (-(I.zetaProd m k t -
        (4 * Real.pi ^ 2 * κ / epsilon β I.Λ m ^ 2) *
          I.corrTime κ m k t)) • uShear β I.Λ m k (x + latticeShift z) =
      (-(I.zetaProd m k t -
        (4 * Real.pi ^ 2 * κ / epsilon β I.Λ m ^ 2) *
          I.corrTime κ m k t)) • uShear β I.Λ m k x
    rw [huper z x]
  · intro x
    rw [hrep]
    have hmul := vecDiv_scalar_mul
      (q := fun _ : Vec 2 => -(I.zetaProd m k t -
        (4 * Real.pi ^ 2 * κ / epsilon β I.Λ m ^ 2) *
          I.corrTime κ m k t)) (F := uShear β I.Λ m k) (x := x)
      contDiff_const hu
    rw [hmul, hdivu x]
    simp [spaceGrad, fderiv_const_apply, vecDot]

/-- Time derivative of the corrector transformed by the transposed flow Jacobian. -/
def chiTimePushforwardFlux {β : ℝ} (I : Ingredients β)
    {Φ : ℕ → ℝ → Vec 2 → ℝ} (hΦ : IsStreamSeq I Φ)
    (m : ℕ) (κ : ℝ) (k : ℤ) (t : ℝ) : Vec 2 → Vec 2 :=
  fun x => (flowGradK I hΦ m k t x).transpose.mulVec
    (chiMKTimeDerivative I m κ k t
      (I.xFlowInv hΦ m (lIdx β I.Λ m k) t x))

theorem chiTimePushforwardFlux_regular {β : ℝ} (I : Ingredients β)
    {Φ : ℕ → ℝ → Vec 2 → ℝ} (hΦ : IsStreamSeq I Φ)
    {m : ℕ} (hm : 1 ≤ m) (κ : ℝ) (k : ℤ) (t : ℝ) :
    ContDiff ℝ (⊤ : ℕ∞) (chiTimePushforwardFlux I hΦ m κ k t) ∧
      IsZ2Periodic (chiTimePushforwardFlux I hΦ m κ k t) ∧
      (∀ x, vecDiv (chiTimePushforwardFlux I hΦ m κ k t) x = 0) := by
  have hFsm := BigBoundRegularity.flowGradK_contDiff_infty I hΦ m k t
  have hFper := BigBoundRegularity.flowGradK_isZ2Periodic I hΦ m k t
  have hdot := BigBoundRegularity.chiMKTimeDerivative_regular I hm κ k t
  have hYsm : ContDiff ℝ (⊤ : ℕ∞)
      (I.xFlowInv hΦ m (lIdx β I.Λ m k) t) :=
    (Infra.Section4.amnr_xFlowInv_joint_contDiff_infty I hΦ m
      (lIdx β I.Λ m k)).comp
      (by fun_prop : ContDiff ℝ (⊤ : ℕ∞) (fun x : Vec 2 => (t, x)))
  have hYper := Infra.Section4.amnr_xFlowInv_lattice_equivariant
    I hΦ m (lIdx β I.Λ m k) t
  have hcomp : ContDiff ℝ (⊤ : ℕ∞)
      (fun x => chiMKTimeDerivative I m κ k t
        (I.xFlowInv hΦ m (lIdx β I.Λ m k) t x)) :=
    hdot.1.comp hYsm
  have hcompPer : IsZ2Periodic
      (fun x => chiMKTimeDerivative I m κ k t
        (I.xFlowInv hΦ m (lIdx β I.Λ m k) t x)) := by
    intro z x
    change chiMKTimeDerivative I m κ k t
        (I.xFlowInv hΦ m (lIdx β I.Λ m k) t (x + latticeShift z)) =
      chiMKTimeDerivative I m κ k t
        (I.xFlowInv hΦ m (lIdx β I.Λ m k) t x)
    rw [hYper z x]
    exact hdot.2.1 z _
  have hcofactor : ∀ x,
      rowCofactor (gradMatrix (I.xFlowInv hΦ m (lIdx β I.Λ m k) t) x) =
        (I.flowGrad hΦ m (lIdx β I.Λ m k) t x).transpose := by
    intro x
    exact Infra.Section5.xFlowInv_rowCofactor_eq_flowGrad_transpose
      I hΦ m (lIdx β I.Λ m k) t x
      (Infra.Section5.streamVel_spatialDivergence_eq_zero I hΦ m)
  constructor
  · apply contDiff_pi.mpr
    intro i
    change ContDiff ℝ (⊤ : ℕ∞) (fun x => ∑ j : Fin 2,
      (flowGradK I hΦ m k t x).transpose i j *
        chiMKTimeDerivative I m κ k t
          (I.xFlowInv hΦ m (lIdx β I.Λ m k) t x) j)
    apply ContDiff.sum
    intro j hj
    exact (contDiff_pi.mp (contDiff_pi.mp hFsm j) i).mul
      (contDiff_pi.mp hcomp j)
  constructor
  · intro z x
    change (flowGradK I hΦ m k t (x + latticeShift z)).transpose.mulVec
        (chiMKTimeDerivative I m κ k t
          (I.xFlowInv hΦ m (lIdx β I.Λ m k) t (x + latticeShift z))) =
      (flowGradK I hΦ m k t x).transpose.mulVec
        (chiMKTimeDerivative I m κ k t
          (I.xFlowInv hΦ m (lIdx β I.Λ m k) t x))
    rw [hFper z x]
    exact congrArg (fun v : Vec 2 => (flowGradK I hΦ m k t x).transpose.mulVec v)
      (hcompPer z x)
  · intro x
    have hχ : ContDiff ℝ 2 (chiMKTimeDerivative I m κ k t) :=
      (hdot.1.of_le (by norm_num))
    have hpiola := Infra.Section5.xFlowInv_cofactorPiola_of_streamSeq
      I hΦ m (lIdx β I.Λ m k) t x
      ((hχ.differentiable (by norm_num) _).hasFDerivAt)
    have hfield : chiTimePushforwardFlux I hΦ m κ k t = fun y =>
        (rowCofactor (gradMatrix
          (I.xFlowInv hΦ m (lIdx β I.Λ m k) t) y)).mulVec
          (chiMKTimeDerivative I m κ k t
            (I.xFlowInv hΦ m (lIdx β I.Λ m k) t y)) := by
      funext y
      change (I.flowGrad hΦ m (lIdx β I.Λ m k) t y).transpose.mulVec _ = _
      rw [hcofactor y]
    rw [hfield]
    simpa using hpiola.trans
      (hdot.2.2 (I.xFlowInv hΦ m (lIdx β I.Λ m k) t x))

theorem BigBoundRegularity.meanZeroOn_finite_weighted_divergence
    {ι : Type*} (U : Finset ι) (c : ι → ℝ)
    (F : ι → Vec 2 → Vec 2)
    (hFsm : ∀ i ∈ U, ContDiff ℝ (⊤ : ℕ∞) (F i))
    (hFper : ∀ i ∈ U, IsZ2Periodic (F i)) :
    MeanZeroOn unitCube (fun x => vecDiv (fun y =>
      ∑ i ∈ U, c i • F i y) x) := by
  classical
  have hWsm : ContDiff ℝ (⊤ : ℕ∞) (fun y => ∑ i ∈ U, c i • F i y) := by
    apply ContDiff.sum
    intro i hi
    exact (contDiff_const : ContDiff ℝ (⊤ : ℕ∞) (fun _ : Vec 2 => c i)).smul
      (hFsm i hi)
  have hWper : IsZ2Periodic (fun y => ∑ i ∈ U, c i • F i y) := by
    intro z x
    funext j
    change (∑ i ∈ U, c i • F i (x + latticeShift z)) j =
      (∑ i ∈ U, c i • F i x) j
    simp only [Finset.sum_apply, Pi.smul_apply]
    apply Finset.sum_congr rfl
    intro i hi
    exact congrArg (fun v : Vec 2 => c i • v j) (hFper i hi z x)
  exact meanZeroOn_vecDiv_of_contDiff_periodic hWsm hWper

theorem BigBoundRegularity.meanZeroOn_weighted_grad_pairing
    {ι : Type*} (U : Finset ι) (c : ι → ℝ)
    (q : ι → Vec 2 → ℝ) (P : ι → Vec 2 → Vec 2)
    (hqsm : ∀ i ∈ U, ContDiff ℝ (⊤ : ℕ∞) (q i))
    (hqper : ∀ i ∈ U, IsZ2Periodic (q i))
    (hPsm : ∀ i ∈ U, ContDiff ℝ (⊤ : ℕ∞) (P i))
    (hPper : ∀ i ∈ U, IsZ2Periodic (P i))
    (hPdiv : ∀ i ∈ U, ∀ x, vecDiv (P i) x = 0) :
    MeanZeroOn unitCube (fun x => ∑ i ∈ U,
      c i * vecDot (spaceGrad (q i) x) (P i x)) := by
  classical
  let F : ι → Vec 2 → Vec 2 := fun i x => q i x • P i x
  have hFsm (i : ι) (hi : i ∈ U) : ContDiff ℝ (⊤ : ℕ∞) (F i) :=
    (hqsm i hi).smul (hPsm i hi)
  have hFper (i : ι) (hi : i ∈ U) : IsZ2Periodic (F i) := by
    intro z x
    change q i (x + latticeShift z) • P i (x + latticeShift z) = _
    rw [hqper i hi z x, hPper i hi z x]
  have hsum := BigBoundRegularity.meanZeroOn_finite_weighted_divergence U c F hFsm hFper
  have hdiv (i : ι) (hi : i ∈ U) (x : Vec 2) :
      vecDiv (F i) x = vecDot (spaceGrad (q i) x) (P i x) := by
    change vecDiv (fun y => q i y • P i y) x = _
    rw [vecDiv_scalar_mul (hqsm i hi) (hPsm i hi), hPdiv i hi x]
    simp
  have hderiv (i : ι) (hi : i ∈ U) (x : Vec 2) :
      HasFDerivAt (F i) (fderiv ℝ (F i) x) x :=
    ((hFsm i hi).differentiable (by simp) x).hasFDerivAt
  have hpoint (x : Vec 2) :
      vecDiv (fun y => ∑ i ∈ U, c i • F i y) x =
        ∑ i ∈ U, c i * vecDot (spaceGrad (q i) x) (P i x) := by
    rw [Infra.Section5.vecDiv_finite_weighted_sum U c F x
      (fun i hi => hderiv i hi x)]
    apply Finset.sum_congr rfl
    intro i hi
    rw [hdiv i hi x]
  unfold MeanZeroOn at hsum ⊢
  have hfun : (fun x => ∑ i ∈ U,
      c i * vecDot (spaceGrad (q i) x) (P i x)) =
      fun x => vecDiv (fun y => ∑ i ∈ U, c i • F i y) x := by
    funext x
    exact (hpoint x).symm
  rw [hfun]
  exact hsum

variable {β : ℝ} (I : Ingredients β)
variable {Φ : ℕ → ℝ → Vec 2 → ℝ}

theorem BigBoundRegularity.matrixMul_contDiff_infty
    {A B : Vec 2 → Matrix (Fin 2) (Fin 2) ℝ}
    (hA : ContDiff ℝ (⊤ : ℕ∞) A) (hB : ContDiff ℝ (⊤ : ℕ∞) B) :
    ContDiff ℝ (⊤ : ℕ∞) (fun x => A x * B x) := by
  apply contDiff_pi.mpr
  intro i
  apply contDiff_pi.mpr
  intro j
  change ContDiff ℝ (⊤ : ℕ∞) (fun x => ∑ k : Fin 2, A x i k * B x k j)
  apply ContDiff.sum
  intro k hk
  exact (contDiff_pi.mp (contDiff_pi.mp hA i) k).mul
    (contDiff_pi.mp (contDiff_pi.mp hB k) j)

theorem BigBoundRegularity.matrixMul_isZ2Periodic
    {A B : Vec 2 → Matrix (Fin 2) (Fin 2) ℝ}
    (hA : IsZ2Periodic A) (hB : IsZ2Periodic B) :
    IsZ2Periodic (fun x => A x * B x) := by
  intro z x
  ext i j
  change (∑ k : Fin 2, A (x + latticeShift z) i k * B (x + latticeShift z) k j) =
    ∑ k : Fin 2, A x i k * B x k j
  apply Finset.sum_congr rfl
  intro k hk
  rw [congrFun (congrFun (hA z x) i) k,
    congrFun (congrFun (hB z x) k) j]

/-- Each localized corrector flux is smooth and periodic on its active cutoff
mode. -/
theorem correctorFlux_regular_of_mode
    {β : ℝ} (I : Ingredients β) {Φ : ℕ → ℝ → Vec 2 → ℝ}
    (hΦ : IsStreamSeq I Φ) (m : ℕ) (hm : 1 ≤ m) (κ : ℝ)
    (k : ℤ) (t : ℝ) (hk : Odd k) (hxi : I.xiMK m k t ≠ 0) :
    ContDiff ℝ (⊤ : ℕ∞) (correctorFlux I hΦ m κ k t) ∧
      IsZ2Periodic (correctorFlux I hΦ m κ k t) := by
  have hchi := BigBoundRegularity.chiTilde_contDiff_infty I hΦ m κ k t
  have hchiPer := BigBoundRegularity.chiTilde_isZ2Periodic I hΦ m κ k t
  have hgrad : ContDiff ℝ (⊤ : ℕ∞) (gradChiTilde I hΦ m κ k t) := by
    unfold gradChiTilde
    apply contDiff_pi.mpr
    intro i
    apply contDiff_pi.mpr
    intro j
    change ContDiff ℝ (⊤ : ℕ∞)
      (fun x => spaceGrad (fun y => I.chiTilde hΦ m κ k t y j) x i)
    exact contDiff_pi.mp
      (Infra.Section4.iterate_gradient_smooth (contDiff_pi.mp hchi j)) i
  have hgradPer : IsZ2Periodic (gradChiTilde I hΦ m κ k t) := by
    intro z x
    ext i j
    exact congrFun (Infra.Section4.iterate_gradient_periodic
      ((contDiff_infty.mp (contDiff_pi.mp hchi j)) 1)
      (fun z' y => congrFun (hchiPer z' y) j) z x) i
  have hD := BigBoundRegularity.diffusionMatrix_contDiff_infty I hΦ m κ t
  have hDper := BigBoundRegularity.diffusionMatrix_isZ2Periodic I hΦ hm κ t
  have hE : ContDiff ℝ (⊤ : ℕ∞)
      (fun x => (1 : Matrix (Fin 2) (Fin 2) ℝ) +
        gradChiTilde I hΦ m κ k t x) := contDiff_const.add hgrad
  have hEper : IsZ2Periodic (fun x =>
      (1 : Matrix (Fin 2) (Fin 2) ℝ) + gradChiTilde I hΦ m κ k t x) := by
    intro z x
    change (1 : Matrix (Fin 2) (Fin 2) ℝ) + gradChiTilde I hΦ m κ k t (x + latticeShift z) =
      (1 : Matrix (Fin 2) (Fin 2) ℝ) + gradChiTilde I hΦ m κ k t x
    rw [hgradPer z x]
  have hsel := diffusionMatrix_mul_one_plus_gradChi_eq_correctorFlux
    I hΦ m hm κ k t hk hxi
  have hsm : ContDiff ℝ (⊤ : ℕ∞)
      (fun x => diffusionMatrix I hΦ m κ t x *
        ((1 : Matrix (Fin 2) (Fin 2) ℝ) + gradChiTilde I hΦ m κ k t x)) :=
    BigBoundRegularity.matrixMul_contDiff_infty hD hE
  have hper : IsZ2Periodic (fun x => diffusionMatrix I hΦ m κ t x *
      ((1 : Matrix (Fin 2) (Fin 2) ℝ) + gradChiTilde I hΦ m κ k t x)) :=
    BigBoundRegularity.matrixMul_isZ2Periodic hDper hEper
  rw [← hsel]
  exact ⟨hsm, hper⟩

end AVenhance.Infra.Section5.Integration

end
