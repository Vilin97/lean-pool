/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import Mathlib.Analysis.Real.Pi.Bounds

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.Integration.PartIAnsatzPointwise
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.Integration.PartIAnsatzL2
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.Integration.PartIHmRegularityHm
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.Integration.Energy.AnsatzRegularity
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section4.TIterateSmooth
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.RelativeError.LeadingErrorAlgebraContinuity
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.A0Facts
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.MStar
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section3.LRecurseTop
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Classical.Uniqueness
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section4.ThetaClassicalUniqueness
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section4.ThetaScale
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Parabolic.FourierGalerkin.TimeDependentFourierTest
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Numeric.Exponents

/-! # Right-limit initial defect for the Section 5 ansatz

The ansatz at time zero depends on the arbitrary negative-time extension of an iterate.  This file
proves its required initial defect as `s → 0⁺`.  The only input data are the literal diffusivity
    bounds
conclusion and the positive-time Hm bound from half-cell bound; continuity and the oscillatory
    corrector bound
are proved here.
-/

@[expose] public section

open MeasureTheory Homogenization Filter Topology
open scoped ContDiff

noncomputable section

namespace AVenhance.Infra.Section5.Integration

open AVenhance AVenhance.Infra.Section5 AVenhance.Infra.Section5.RelativeError
  AVenhance.Infra.Classical

theorem PartIInitial.initial_sqrt_l2NormSq_le_of_abs_le {f g : Vec 2 → ℝ}
    (hg : Continuous g) (hfg : ∀ x, |f x| ≤ g x) :
    Real.sqrt (l2NormSq f) ≤ Real.sqrt (l2NormSq g) := by
  refine Real.sqrt_le_sqrt ?_
  unfold l2NormSq
  refine integral_mono_of_nonneg (Filter.Eventually.of_forall fun x => sq_nonneg _)
    (integrableOn_sq_unitCube_of_continuous hg) (Filter.Eventually.of_forall fun x => ?_)
  change (f x) ^ 2 ≤ (g x) ^ 2
  rw [← sq_abs (f x)]
  exact pow_le_pow_left₀ (abs_nonneg _) (hfg x) 2

theorem PartIInitial.initial_sqrt_l2NormSq_const_mul {c : ℝ} (hc : 0 ≤ c)
    (f : Vec 2 → ℝ) :
    Real.sqrt (l2NormSq (fun x => c * f x)) = c * Real.sqrt (l2NormSq f) := by
  unfold l2NormSq
  simp_rw [mul_pow]
  rw [integral_const_mul, Real.sqrt_mul (sq_nonneg c), Real.sqrt_sq hc]

theorem PartIInitial.tNstar_classical_solution
    {β : ℝ} (I : Ingredients β) {Φ : ℕ → ℝ → Vec 2 → ℝ}
    {m : ℕ} {κm κprev : ℝ} {θ₀ : Vec 2 → ℝ}
    {hΦ : IsStreamSeq I Φ} {θprev : ℝ → Vec 2 → ℝ} {T : ℕ → ℝ → Vec 2 → ℝ}
    (hθprev : IsClassicalSol (streamVel (Φ (m - 1))) κprev (fun _ _ => 0) θ₀ θprev)
    (hT : I.IsTIterates hΦ m κm κprev θ₀ θprev T) :
    ∃ F : ℝ → Vec 2 → ℝ,
      IsClassicalSol (streamVel (Φ (m - 1))) κprev F θ₀ (T (Nstar β)) := by
  by_cases hn : Nstar β = 0
  · rw [hn, hT.1]
    exact ⟨_, hθprev⟩
  · exact ⟨_, hT.2 (Nstar β) (Nat.one_le_iff_ne_zero.mpr hn) le_rfl⟩

theorem PartIInitial.zero_data_classical_solution
    {φ : ℝ → Vec 2 → ℝ} {κ : ℝ} {F : ℝ → Vec 2 → ℝ}
    (hF : ∀ t : ℝ, 0 < t → ∀ x, F t x = 0) :
    IsClassicalSol (streamVel φ) κ F (fun _ : Vec 2 => 0) (fun _ _ => 0) := by
  refine ⟨contDiffOn_const, ?_, ?_, ?_⟩
  · intro t ht k x
    rfl
  · intro x
    rfl
  · intro t ht x
    simp [advDiffOp, spaceLap, spaceGrad, Homogenization.vecDot, hF t ht x]

theorem PartIInitial.classical_zero_data_solution_is_zero
    {φ : ℝ → Vec 2 → ℝ} (hφ : IsAdmissibleStream φ) {κ : ℝ}
    (hκ : 0 < κ) {θ : ℝ → Vec 2 → ℝ}
    (hθ : IsClassicalSol (streamVel φ) κ (fun _ _ => 0) (fun _ => 0) θ) :
    ∀ t : ℝ, 0 ≤ t → θ t = fun _ => 0 := by
  have hz := PartIInitial.zero_data_classical_solution (φ := φ) (κ := κ) (F := fun _ _ => 0)
    (by intro t ht x; rfl)
  have heq := AVenhance.Infra.Classical.streamVel_classical_unique φ hφ κ hκ (fun _ _ => 0)
    (fun _ => 0) (θ := θ) (ψ := fun _ _ => 0) hθ hz
  intro t ht
  funext x
  exact (heq t ht x).symm

theorem PartIInitial.tIterates_zero_of_zero_data
    {β : ℝ} (I : Ingredients β) {Φ : ℕ → ℝ → Vec 2 → ℝ}
    (hΦ : IsStreamSeq I Φ) {m : ℕ} (hm : 2 ≤ m) {κm κprev : ℝ}
    (hκprev : 0 < κprev) {θprev : ℝ → Vec 2 → ℝ}
    (hθprev : IsClassicalSol (streamVel (Φ (m - 1))) κprev
      (fun _ _ => 0) (fun _ => 0) θprev)
    {T : ℕ → ℝ → Vec 2 → ℝ}
    (hT : I.IsTIterates hΦ m κm κprev (fun _ => 0) θprev T) :
    ∀ i : ℕ, i ≤ Nstar β → ∀ t : ℝ, 0 ≤ t → T i t = fun _ => 0 := by
  have hφ : IsAdmissibleStream (Φ (m - 1)) :=
    AVenhance.Infra.Section4.theta_prev_stream_admissible I Φ hΦ hm
  have hprevZero := PartIInitial.classical_zero_data_solution_is_zero hφ hκprev hθprev
  intro i
  induction i with
  | zero =>
      intro hi t ht
      rw [hT.1]
      exact hprevZero t ht
  | succ i ih =>
      intro hi t ht
      let F : ℝ → Vec 2 → ℝ := I.TForcing hΦ m κm κprev (T i)
      have hFzero : ∀ s : ℝ, 0 < s → ∀ x, F s x = 0 := by
        intro s hs x
        have hTiZero := ih (by omega) s hs.le
        have hgrad : spaceGrad (T i s) = 0 := by
          rw [hTiZero]
          funext x j
          simp [spaceGrad]
        simp [F, Ingredients.TForcing, hgrad, AVenhance.vecDiv, Matrix.mulVec_zero,
          spaceGrad]
      have hTi : IsClassicalSol (streamVel (Φ (m - 1))) κprev F
          (fun _ => 0) (T (i + 1)) := by
        simpa [F, Nat.add_sub_cancel] using
          hT.2 (i + 1) (by omega) (by omega : i + 1 ≤ Nstar β)
      have hzTi := PartIInitial.zero_data_classical_solution (φ := Φ (m - 1))
        (κ := κprev) (F := F) hFzero
      have heq := AVenhance.Infra.Classical.streamVel_classical_unique
        (Φ (m - 1)) hφ κprev hκprev F
        (fun _ => 0) hTi hzTi
      funext x
      exact (heq t ht x).symm

theorem PartIInitial.initial_gamma_lt_one {β : ℝ} (hβ : 1 < β) (hβ' : β < 4 / 3) :
    gamma β < 1 := by
  rw [Infra.Numeric.gamma_eq_beta_fraction hβ]
  have h : 0 < 5 * β - 4 := by linarith
  rw [div_lt_one h]
  nlinarith

/-- Abstract-real scale conversion, kept local to avoid importing the diffusivity bounds wrapper. -/
theorem PartIInitial.initial_ansatz_scale_bound {β : ℝ} (hβ : 1 < β) (hβ' : β < 4 / 3)
    {K e em A : ℝ} (hK : 1 ≤ K) (he : 0 < e) (he1 : e ≤ 1) (hem : 0 < em)
    (hA0 : 0 ≤ A) (hA : A ≤ K * em ^ (-gamma β))
    (hemK : em ≤ K * e ^ q β) :
    A * em / (2 * Real.pi) * e ^ (-(1 + gamma β / 2)) ≤ K ^ 2 * e ^ delta β := by
  have hpi : 1 ≤ 2 * Real.pi := by linarith [Real.pi_gt_three]
  have hg1 := PartIInitial.initial_gamma_lt_one hβ hβ'
  have hg0 := Infra.Ingredients.gamma_pos hβ hβ'
  have hK0 : 0 < K := by linarith
  have hd := Infra.Ingredients.delta_pos hβ hβ'
  have h1 : A * em / (2 * Real.pi) ≤ K * em ^ (1 - gamma β) := by
    have hrw : em ^ (1 - gamma β) = em ^ (-gamma β) * em := by
      rw [show 1 - gamma β = -gamma β + 1 by ring, Real.rpow_add hem, Real.rpow_one]
    rw [hrw]
    calc
      A * em / (2 * Real.pi) ≤ A * em := by
        rw [div_le_iff₀ (by linarith)]
        nlinarith [mul_nonneg hA0 hem.le]
      _ ≤ K * em ^ (-gamma β) * em := mul_le_mul_of_nonneg_right hA hem.le
      _ = K * (em ^ (-gamma β) * em) := by ring
  have h2 : em ^ (1 - gamma β) ≤ K * e ^ (q β * (1 - gamma β)) := by
    have hexp : 0 ≤ 1 - gamma β := by linarith
    calc
      em ^ (1 - gamma β) ≤ (K * e ^ q β) ^ (1 - gamma β) :=
        Real.rpow_le_rpow hem.le hemK hexp
      _ = K ^ (1 - gamma β) * e ^ (q β * (1 - gamma β)) := by
        rw [Real.mul_rpow hK0.le (Real.rpow_nonneg he.le _), ← Real.rpow_mul he.le]
      _ ≤ K ^ (1 : ℝ) * e ^ (q β * (1 - gamma β)) := by
        exact mul_le_mul_of_nonneg_right
          (Real.rpow_le_rpow_of_exponent_le hK
            (by linarith : 1 - gamma β ≤ (1 : ℝ)))
          (Real.rpow_nonneg he.le _)
      _ = K * e ^ (q β * (1 - gamma β)) := by rw [Real.rpow_one]
  have h3 : e ^ (q β * (1 - gamma β)) * e ^ (-(1 + gamma β / 2)) ≤ e ^ delta β := by
    rw [← Real.rpow_add he]
    have hid := Infra.Numeric.four_delta_identity hβ
    have hexp : q β * (1 - gamma β) + -(1 + gamma β / 2) = 4 * delta β := by linarith
    rw [hexp]
    exact Real.rpow_le_rpow_of_exponent_ge he he1 (by linarith)
  have hep : 0 ≤ e ^ (-(1 + gamma β / 2)) := Real.rpow_nonneg he.le _
  calc
    A * em / (2 * Real.pi) * e ^ (-(1 + gamma β / 2)) ≤
        (K * (K * e ^ (q β * (1 - gamma β)))) * e ^ (-(1 + gamma β / 2)) := by
      gcongr
      exact h1.trans (mul_le_mul_of_nonneg_left h2 hK0.le)
    _ = K ^ 2 * (e ^ (q β * (1 - gamma β)) * e ^ (-(1 + gamma β / 2))) := by ring
    _ ≤ K ^ 2 * e ^ delta β := by gcongr

theorem PartIInitial.initial_chi_const_eq {a e κ : ℝ} (ha : 0 < a) (he : 0 < e)
    (hκ : 0 < κ) :
    (4 * Real.pi ^ 2 * κ / e ^ 2)⁻¹ * |2 * Real.pi * a * e| =
      (a * e ^ 2 / κ) * e / (2 * Real.pi) := by
  rw [abs_of_pos (by positivity)]
  field_simp
  norm_num

theorem PartIInitial.continuous_pair_difference_l2_at_initial
    {b b' : ℝ → Vec 2 → Vec 2} {κ κ' : ℝ}
    {Fforce Gforce : ℝ → Vec 2 → ℝ}
    {Fsol Gsol : ℝ → Vec 2 → ℝ} {f₀ : Vec 2 → ℝ}
    (hF : IsClassicalSol b κ Fforce f₀ Fsol)
    (hG : IsClassicalSol b' κ' Gforce f₀ Gsol) :
    ∀ η : ℝ, 0 < η →
      ∀ᶠ s in 𝓝[>] (0 : ℝ),
        Real.sqrt (l2NormSq (fun x => Fsol s x - Gsol s x)) < η := by
  intro η hη
  let P : ℝ × Vec 2 → ℝ × Vec 2 := fun p => (max p.1 0, p.2)
  have hPcont : Continuous P := by
    exact (continuous_fst.max continuous_const).prodMk continuous_snd
  have hPmap : ∀ p, P p ∈ Set.Ici (0 : ℝ) ×ˢ Set.univ := by
    rintro ⟨t, x⟩
    exact ⟨le_max_right t 0, Set.mem_univ _⟩
  have hPmaps : Set.MapsTo P Set.univ (Set.Ici (0 : ℝ) ×ˢ Set.univ) := by
    intro p hp
    exact hPmap p
  have hFcont : Continuous (fun p : ℝ × Vec 2 => Fsol (max p.1 0) p.2) := by
    change Continuous ((Function.uncurry Fsol) ∘ P)
    exact continuousOn_univ.mp (hF.1.continuousOn.comp hPcont.continuousOn hPmaps)
  have hGcont : Continuous (fun p : ℝ × Vec 2 => Gsol (max p.1 0) p.2) := by
    change Continuous ((Function.uncurry Gsol) ∘ P)
    exact continuousOn_univ.mp (hG.1.continuousOn.comp hPcont.continuousOn hPmaps)
  let Q : ℝ × Vec 2 → ℝ := fun p =>
    (Fsol (max p.1 0) p.2 - Gsol (max p.1 0) p.2) ^ 2
  have hQcont : Continuous Q := (hFcont.sub hGcont).pow 2
  have hIntcont : Continuous (fun t => ∫ x in unitCube, Q (t, x)) :=
    AVenhance.Infra.Parabolic.FourierGalerkin.continuous_cell_integral_of_joint hQcont
  let N : ℝ → ℝ := fun t => Real.sqrt (∫ x in unitCube, Q (t, x))
  have hNcont : Continuous N := Real.continuous_sqrt.comp hIntcont
  have hNzero : N 0 = 0 := by
    simp [N, Q, hF.2.2.1, hG.2.2.1]
  have hnear : {t : ℝ | N t < η} ∈ 𝓝 (0 : ℝ) :=
    (isOpen_lt hNcont continuous_const).mem_nhds
    (by
      change N 0 < η
      rw [hNzero]
      exact hη)
  have hwithin : {t : ℝ | N t < η} ∈ 𝓝[>] (0 : ℝ) :=
    Filter.Eventually.filter_mono nhdsWithin_le_nhds hnear
  filter_upwards [hwithin, self_mem_nhdsWithin] with s hs hspos
  have hsmax : max s 0 = s := max_eq_left hspos.le
  simpa [N, Q, hsmax, l2NormSq] using hs

theorem PartIInitial.continuous_classical_gradient_l2_at_initial
    {b : ℝ → Vec 2 → Vec 2} {κ : ℝ} {F : ℝ → Vec 2 → ℝ}
    {θ₀ : Vec 2 → ℝ} {T : ℝ → Vec 2 → ℝ}
    (hT : IsClassicalSol b κ F θ₀ T) :
    ∀ η : ℝ, 0 < η →
      ∀ᶠ s in 𝓝[>] (0 : ℝ),
        Real.sqrt (gradNormSq (spaceGrad (T s))) <
          Real.sqrt (gradNormSq (spaceGrad θ₀)) + η := by
  intro η hη
  let P : ℝ × Vec 2 → ℝ × Vec 2 := fun p => (max p.1 0, p.2)
  have hPcont : Continuous P := by
    exact (continuous_fst.max continuous_const).prodMk continuous_snd
  have hPmap : ∀ p, P p ∈ Set.Ici (0 : ℝ) ×ˢ Set.univ := by
    rintro ⟨t, x⟩
    exact ⟨le_max_right t 0, Set.mem_univ _⟩
  have hPmaps : Set.MapsTo P Set.univ (Set.Ici (0 : ℝ) ×ˢ Set.univ) := by
    intro p hp
    exact hPmap p
  have hgradCoord (i : Fin 2) : ContinuousOn
      (fun p : ℝ × Vec 2 => spaceGrad (T p.1) p.2 i)
      (Set.Ici (0 : ℝ) ×ˢ Set.univ) :=
    AVenhance.Infra.Section5.RelativeError.continuousOn_spaceGrad_joint hT.1 i
  have hgrad : Continuous (fun p : ℝ × Vec 2 => spaceGrad (T (max p.1 0)) p.2) := by
    apply continuous_pi
    intro i
    change Continuous ((fun p : ℝ × Vec 2 => spaceGrad (T p.1) p.2 i) ∘ P)
    exact continuousOn_univ.mp ((hgradCoord i).comp hPcont.continuousOn hPmaps)
  have hQcont : Continuous (fun p : ℝ × Vec 2 =>
      vecNormSq (spaceGrad (T (max p.1 0)) p.2)) := by
    unfold vecNormSq vecDot
    exact continuous_finsetSum _ (fun i _ =>
      ((continuous_apply i).comp hgrad).mul ((continuous_apply i).comp hgrad))
  have hIntcont : Continuous (fun t => ∫ x in unitCube,
      vecNormSq (spaceGrad (T (max t 0)) x)) :=
    AVenhance.Infra.Parabolic.FourierGalerkin.continuous_cell_integral_of_joint hQcont
  let N : ℝ → ℝ := fun t => Real.sqrt (∫ x in unitCube,
    vecNormSq (spaceGrad (T (max t 0)) x))
  have hNcont : Continuous N := Real.continuous_sqrt.comp hIntcont
  have hNzero : N 0 = Real.sqrt (gradNormSq (spaceGrad θ₀)) := by
    have hinit : T 0 = θ₀ := by
      funext x
      simpa using hT.2.2.1 x
    simp only [N, max_self]
    rw [hinit]
    rfl
  have hnear : {t : ℝ | N t < Real.sqrt (gradNormSq (spaceGrad θ₀)) + η} ∈
      𝓝 (0 : ℝ) :=
    (isOpen_lt hNcont continuous_const).mem_nhds (by
      change N 0 < _
      rw [hNzero]
      linarith)
  have hwithin : {t : ℝ | N t < Real.sqrt (gradNormSq (spaceGrad θ₀)) + η} ∈
      𝓝[>] (0 : ℝ) := Filter.Eventually.filter_mono nhdsWithin_le_nhds hnear
  filter_upwards [hwithin, self_mem_nhdsWithin] with s hs hspos
  have hsmax : max s 0 = s := max_eq_left hspos.le
  simpa [N, hsmax, gradNormSq] using hs

theorem PartIInitial.corrector_l2_bound_by_gradient
    {β : ℝ} (I : Ingredients β) {Φ : ℕ → ℝ → Vec 2 → ℝ}
    (hΦ : IsStreamSeq I Φ) {m : ℕ} (hm : 2 ≤ m) {κ : ℝ} (hκ : 0 < κ)
    {T : ℝ → Vec 2 → ℝ} {t : ℝ} (hTt : ContDiff ℝ ∞ (T t)) :
    Real.sqrt (l2NormSq (fun x => I.ansatz hΦ m κ T t x - T t x - I.Hm hΦ m κ T t x)) ≤
      8 * chiSup I κ m * Real.sqrt (gradNormSq (spaceGrad (T t))) := by
  let P : Vec 2 → ℝ := fun x => I.ansatz hΦ m κ T t x - T t x - I.Hm hΦ m κ T t x
  let g : Vec 2 → ℝ := fun x =>
    Real.sqrt (vecNormSq (spaceGrad (T t) x))
  have hg : Continuous g := by
    unfold g vecNormSq vecDot
    exact Real.continuous_sqrt.comp <| continuous_finsetSum _ fun i _ =>
      ((contDiff_spaceGrad_component hTt i).continuous).mul
        ((contDiff_spaceGrad_component hTt i).continuous)
  have hchi : 0 ≤ chiSup I κ m := chiSup_nonneg I hκ m
  have hpoint : ∀ x, |P x| ≤ (8 * chiSup I κ m) * g x := by
    intro x
    have hbase := ansatz_sub_T_sub_Hm_abs_le I hΦ hm hκ hTt x
    have hcoord (i : Fin 2) :
        |spaceGrad (T t) x i| ≤ g x := by
      rw [← Real.sqrt_sq_eq_abs]
      exact Real.sqrt_le_sqrt (Homogenization.sq_apply_le_vecNormSq _ i)
    have hg0 : 0 ≤ g x := Real.sqrt_nonneg _
    dsimp [P, g]
    calc
      |I.ansatz hΦ m κ T t x - T t x - I.Hm hΦ m κ T t x|
          ≤ 4 * chiSup I κ m *
            (|spaceGrad (T t) x 0| + |spaceGrad (T t) x 1|) := hbase
      _ ≤ 4 * chiSup I κ m * (g x + g x) :=
          mul_le_mul_of_nonneg_left (add_le_add (hcoord 0) (hcoord 1)) (by positivity)
      _ = (8 * chiSup I κ m) * g x := by ring
  have hnorm : l2NormSq g = gradNormSq (spaceGrad (T t)) := by
    unfold l2NormSq gradNormSq g
    congr 1
    funext x
    have hnonneg : 0 ≤ vecNormSq (spaceGrad (T t) x) := by
      exact Homogenization.vecNormSq_nonneg _
    change (Real.sqrt (vecNormSq (spaceGrad (T t) x))) ^ 2 = _
    rw [Real.sq_sqrt hnonneg]
  calc
    Real.sqrt (l2NormSq P) ≤ Real.sqrt (l2NormSq (fun x => (8 * chiSup I κ m) * g x)) :=
      PartIInitial.initial_sqrt_l2NormSq_le_of_abs_le (continuous_const.mul hg) hpoint
    _ = 8 * chiSup I κ m * Real.sqrt (l2NormSq g) :=
      PartIInitial.initial_sqrt_l2NormSq_const_mul (by positivity) g
    _ = 8 * chiSup I κ m * Real.sqrt (gradNormSq (spaceGrad (T t))) := by rw [hnorm]

/-- the coefficient scale, conditional on the literal two-part diffusivity bounds conclusion.  The
    terminal
index uses the already-proved one-sided `l_recurse_top` endpoint estimate. -/
theorem chiSup_analytic_scale_of_A5
    {β : ℝ} (I : Ingredients β)
    {m M : ℕ} (hm : 2 ≤ m) (hmM : m ≤ M)
    {κ : ℝ} (hκ : 0 < κ) (hPerm : κ ∈ permittedInterval β I.Λ M)
    (hM : 1 ≤ M) {C₀ c C : ℝ}
    (_hCzeta : I.Czeta ≤ C₀) (_hCxi : I.Cxi ≤ C₀) (_hChat : I.Chat ≤ C₀)
    (_hpermissible : κ ∈ permissibleSet β I.Λ)
    (hc : 0 < c) (_hcC : c < C)
    (hA5 :
      (∀ j : ℕ, 1 ≤ j → j < M →
        c * (a β I.Λ j * epsilon β I.Λ j ^ (2 + gamma β)) ≤
            I.kappaAt κ j (M - j) ∧
        I.kappaAt κ j (M - j) ≤
            C * (a β I.Λ j * epsilon β I.Λ j ^ (2 + gamma β))) ∧
      (∀ j : ℕ, 2 ≤ j → j < M →
        c * epsilon β I.Λ (j - 1) ^ (4 * delta β) ≤
            epsilon β I.Λ j ^ 2 / (I.kappaAt κ j (M - j) * tau β I.Λ j) ∧
        epsilon β I.Λ j ^ 2 / (I.kappaAt κ j (M - j) * tau β I.Λ j) ≤
            C * epsilon β I.Λ (j - 1) ^ (4 * delta β)))
    {R : ℝ} (_hR : 0 < R)
    (hRscale : epsilon β I.Λ (m - 1) ^ (1 + gamma β / 2) ≤ R) :
    0 < I.kappaSeq κ M m ∧
      chiSup I (I.kappaSeq κ M m) m *
          epsilon β I.Λ (m - 1) ^ (-(1 + gamma β / 2)) ≤
        (max (max 1 (min c (1 / 2))⁻¹)
          (1 + Infra.Ingredients.supergeoConstant β)) ^ 2 *
            epsilon β I.Λ (m - 1) ^ delta β := by
  let e := epsilon β I.Λ (m - 1)
  let em := epsilon β I.Λ m
  let κm := I.kappaSeq κ M m
  let cbar := min c (1 / 2)
  let S := 1 + Infra.Ingredients.supergeoConstant β
  let K := max (max 1 cbar⁻¹) S
  have he : 0 < e := by
    dsimp [e]
    exact Infra.Cutoff.epsilon_pos I.one_lt_beta I.beta_lt
      I.two_pow_seven_le
  have he1 : e ≤ 1 := by
    dsimp [e]
    exact Infra.Construction.epsilon_le_one I.one_lt_beta
      I.beta_lt I.two_pow_seven_le
  have hem : 0 < em := by
    dsimp [em]
    exact Infra.Cutoff.epsilon_pos I.one_lt_beta I.beta_lt
      I.two_pow_seven_le
  have ha : 0 < a β I.Λ m := by
    rw [a]
    exact Real.rpow_pos_of_pos hem _
  have hcbar : 0 < cbar := by
    dsimp [cbar]
    exact lt_min hc (by norm_num)
  have hcbarInv : 0 < cbar⁻¹ := inv_pos.mpr hcbar
  have hsg : 0 ≤ Infra.Ingredients.supergeoConstant β := by
    unfold Infra.Ingredients.supergeoConstant
    have hq : 0 ≤ q β := by linarith [Infra.Ingredients.one_lt_q I.one_lt_beta I.beta_lt]
    exact mul_nonneg
      (mul_nonneg (by norm_num) hq)
      (Real.exp_nonneg _)
  have hS : 1 ≤ S := by dsimp [S]; linarith
  have hK : 1 ≤ K := by dsimp [K]; exact le_max_of_le_left (le_max_left _ _)
  have hKc : cbar⁻¹ ≤ K := by
    dsimp [K]
    exact le_max_of_le_left (le_max_of_le_right le_rfl)
  have hKS : S ≤ K := by dsimp [K]; exact le_max_right _ _
  have hfactor : 0 < a β I.Λ m * em ^ (2 + gamma β) := by positivity
  have hlower : cbar * (a β I.Λ m * em ^ (2 + gamma β)) ≤ κm := by
    by_cases hlt : m < M
    · have hlow := hA5.1 m (by omega) hlt
      have hcbarc : cbar ≤ c := by dsimp [cbar]; exact min_le_left _ _
      have hmul := mul_le_mul_of_nonneg_right hcbarc hfactor.le
      simpa [κm, Ingredients.kappaSeq] using hmul.trans hlow.1
    · have heq : m = M := by omega
      subst m
      have htop := AVenhance.Infra.Section3.l_recurse_top I.one_lt_beta I.beta_lt
        I.two_pow_seven_le hκ hPerm hM
      have htop' : (1 / 2 : ℝ) *
          (a β I.Λ M * epsilon β I.Λ M ^ (2 + gamma β)) ≤ I.kappaAt κ M 0 := by
        simpa [Ingredients.kappaAt, mul_assoc] using htop.1
      have hcbarhalf : cbar ≤ (1 / 2 : ℝ) := by
        dsimp [cbar]
        exact min_le_right _ _
      have hmul := mul_le_mul_of_nonneg_right hcbarhalf hfactor.le
      simpa [κm, Ingredients.kappaSeq, em] using hmul.trans htop'
  have hκm : 0 < κm := by
    have := mul_pos hcbar hfactor
    exact this.trans_le hlower
  have hcoef : a β I.Λ m * em ^ 2 / κm ≤ cbar⁻¹ * em ^ (-gamma β) := by
    have hpow : em ^ (2 + gamma β) * em ^ (-gamma β) = em ^ 2 := by
      calc
        em ^ (2 + gamma β) * em ^ (-gamma β) =
            em ^ ((2 + gamma β) + (-gamma β)) := by rw [← Real.rpow_add hem]
      _ = em ^ 2 := by
        rw [show (2 + gamma β) + -gamma β = (2 : ℝ) by ring]
        exact Real.rpow_natCast em 2
    have hmul : cbar * (a β I.Λ m * em ^ 2) ≤ κm * em ^ (-gamma β) := by
      have hprod := mul_le_mul_of_nonneg_right hlower (Real.rpow_nonneg hem.le (-gamma β))
      calc
        cbar * (a β I.Λ m * em ^ 2) =
            cbar * (a β I.Λ m * (em ^ (2 + gamma β) * em ^ (-gamma β))) := by
              rw [hpow]
        _ = cbar * (a β I.Λ m * em ^ (2 + gamma β)) * em ^ (-gamma β) := by ring
        _ ≤ κm * em ^ (-gamma β) := hprod
    have hdiv : cbar * (a β I.Λ m * em ^ 2) / κm ≤ em ^ (-gamma β) := by
      apply (div_le_iff₀ hκm).2
      simpa [mul_comm] using hmul
    have hdiv' : cbar * (a β I.Λ m * em ^ 2 / κm) ≤ em ^ (-gamma β) := by
      calc
        cbar * (a β I.Λ m * em ^ 2 / κm) =
            cbar * (a β I.Λ m * em ^ 2) / κm := by ring
        _ ≤ em ^ (-gamma β) := hdiv
    have hdiv'' : a β I.Λ m * em ^ 2 / κm ≤ em ^ (-gamma β) / cbar :=
      (le_div_iff₀ hcbar).2 (by simpa [mul_comm] using hdiv')
    simpa [div_eq_mul_inv, mul_comm] using hdiv''
  have hA : 0 ≤ a β I.Λ m * em ^ 2 / κm := by positivity
  have hAupper : a β I.Λ m * em ^ 2 / κm ≤ K * em ^ (-gamma β) :=
    hcoef.trans (mul_le_mul_of_nonneg_right hKc (Real.rpow_nonneg hem.le _))
  have hgeo := (Infra.Ingredients.epsilon_supergeo I.one_lt_beta I.beta_lt
    I.two_pow_seven_le (m := m - 1) (by omega)).2
  have hmeq : m - 1 + 1 = m := by omega
  rw [hmeq] at hgeo
  have hgeo' : em ≤ S * e ^ q β := by
    dsimp [em, e, S]
    calc
      epsilon β I.Λ m ≤
          (1 + Infra.Ingredients.supergeoConstant β * epsilon β I.Λ (m - 1)) *
            epsilon β I.Λ (m - 1) ^ q β := hgeo
      _ ≤ (1 + Infra.Ingredients.supergeoConstant β) *
            epsilon β I.Λ (m - 1) ^ q β := by
        have hp : 0 ≤ epsilon β I.Λ (m - 1) ^ q β := Real.rpow_nonneg he.le _
        have hcoef : 1 + Infra.Ingredients.supergeoConstant β *
            epsilon β I.Λ (m - 1) ≤ 1 + Infra.Ingredients.supergeoConstant β := by
          nlinarith [mul_le_mul_of_nonneg_left he1 hsg]
        exact mul_le_mul_of_nonneg_right hcoef hp
  have hgeoK : em ≤ K * e ^ q β := by
    exact hgeo'.trans (mul_le_mul_of_nonneg_right hKS (Real.rpow_nonneg he.le _))
  have hscale := PartIInitial.initial_ansatz_scale_bound I.one_lt_beta I.beta_lt
    hK he he1 hem hA hAupper hgeoK
  have hchi : chiSup I κm m = (a β I.Λ m * em ^ 2 / κm) * em / (2 * Real.pi) := by
    unfold chiSup κm em
    rw [PartIInitial.initial_chi_const_eq ha hem hκm]
  refine ⟨hκm, ?_⟩
  rw [hchi]
  exact hscale

/-- the right-limit input to step-down part (i), under the exact diffusivity bounds conclusion and
    the scalar Hm bound.
The oscillatory corrector contributes the sharper `ε_(m-1)^(4δ)` through
`q(1−γ)−1−γ/2=4δ`; it is weakened to the common `ε_(m-1)^δ` scale in the result. -/
theorem partI_initial_right_limit_of_A5_and_Hm_of_positive_data
    {β : ℝ} (I : Ingredients β) {Φ : ℕ → ℝ → Vec 2 → ℝ}
    (hΦ : IsStreamSeq I Φ) {m M : ℕ} (hm : 2 ≤ m) (hmM : m ≤ M)
    {κ : ℝ} (hκ : 0 < κ) (hPerm : κ ∈ permittedInterval β I.Λ M)
    (hM : 1 ≤ M) {C₀ c C R CH : ℝ}
    (hCzeta : I.Czeta ≤ C₀) (hCxi : I.Cxi ≤ C₀) (hChat : I.Chat ≤ C₀)
    (hpermissible : κ ∈ permissibleSet β I.Λ)
    (hc : 0 < c) (hcC : c < C)
    (hA5 :
      (∀ j : ℕ, 1 ≤ j → j < M →
        c * (a β I.Λ j * epsilon β I.Λ j ^ (2 + gamma β)) ≤
            I.kappaAt κ j (M - j) ∧
        I.kappaAt κ j (M - j) ≤
            C * (a β I.Λ j * epsilon β I.Λ j ^ (2 + gamma β))) ∧
      (∀ j : ℕ, 2 ≤ j → j < M →
        c * epsilon β I.Λ (j - 1) ^ (4 * delta β) ≤
            epsilon β I.Λ j ^ 2 / (I.kappaAt κ j (M - j) * tau β I.Λ j) ∧
        epsilon β I.Λ j ^ 2 / (I.kappaAt κ j (M - j) * tau β I.Λ j) ≤
            C * epsilon β I.Λ (j - 1) ^ (4 * delta β)))
    {θ₀ : Vec 2 → ℝ} {θm θprev : ℝ → Vec 2 → ℝ}
    {T : ℕ → ℝ → Vec 2 → ℝ} {κm : ℝ}
    (hNpos : 0 < Real.sqrt (l2NormSq θ₀))
    (hθm : IsClassicalSol (streamVel (Φ m)) κm (fun _ _ => 0) θ₀ θm)
    (hθprev : IsClassicalSol (streamVel (Φ (m - 1)))
      (I.kappaSeq κ M (m - 1)) (fun _ _ => 0) θ₀ θprev)
    (hT : I.IsTIterates hΦ m (I.kappaSeq κ M m) (I.kappaSeq κ M (m - 1)) θ₀ θprev T)
    (hR : 0 < R) (hRscale : epsilon β I.Λ (m - 1) ^ (1 + gamma β / 2) ≤ R)
    (hmean : ∫ x in unitCube, θ₀ x = 0)
    (hanalytic : IsThetaAnalytic R θ₀)
    (hCH : 0 ≤ CH)
    (hHm : ∀ t ∈ Set.Ioc (0 : ℝ) 1,
      Real.sqrt (l2NormSq (I.Hm hΦ m (I.kappaSeq κ M m) (T (Nstar β)) t)) ≤
        CH * epsilon β I.Λ (m - 1) ^ delta β * Real.sqrt (l2NormSq θ₀)) :
    ∀ᶠ s in 𝓝[>] (0 : ℝ),
      Real.sqrt (l2NormSq (fun x => θm s x -
        I.ansatz hΦ m (I.kappaSeq κ M m) (T (Nstar β)) s x)) ≤
        (CH + 2 + 8 * (max (max 1 (min c (1 / 2))⁻¹)
          (1 + Infra.Ingredients.supergeoConstant β)) ^ 2 * (Real.sqrt 2 + 1)) *
          epsilon β I.Λ (m - 1) ^ delta β * Real.sqrt (l2NormSq θ₀) := by
  let e := epsilon β I.Λ (m - 1)
  let κm' := I.kappaSeq κ M m
  let Tm1 := T (Nstar β)
  let N := Real.sqrt (l2NormSq θ₀)
  let K := max (max 1 (min c (1 / 2))⁻¹)
      (1 + Infra.Ingredients.supergeoConstant β)
  have hNnonneg : 0 ≤ N := by dsimp [N]; exact Real.sqrt_nonneg _
  have he : 0 < e := by
    dsimp [e]
    exact Infra.Cutoff.epsilon_pos I.one_lt_beta I.beta_lt
      I.two_pow_seven_le
  have heδ : 0 < e ^ delta β := Real.rpow_pos_of_pos he (delta β)
  have hKdata := chiSup_analytic_scale_of_A5 I hm hmM hκ hPerm hM
    hCzeta hCxi hChat hpermissible hc hcC hA5 hR hRscale
  have hK : 1 ≤ K := by dsimp [K]; exact le_max_of_le_left (le_max_left _ _)
  have hscale : chiSup I κm' m * e ^ (-(1 + gamma β / 2)) ≤ K ^ 2 * e ^ delta β := by
    simpa [κm', e, K] using hKdata.2
  have hκmpos : 0 < κm' := by simpa [κm'] using hKdata.1
  obtain ⟨F, hTsol⟩ := PartIInitial.tNstar_classical_solution I hθprev hT
  have hpair := PartIInitial.continuous_pair_difference_l2_at_initial hθm hTsol
    (2 * e ^ delta β * N) (by positivity)
  have hθ0smooth : ContDiff ℝ (⊤ : ℕ∞) θ₀ := by
    have hsmooth := classicalSol_space_contDiff_of_nonneg hθprev (show 0 ≤ (0 : ℝ) by norm_num)
    have hinit : θprev 0 = θ₀ := by funext x; exact hθprev.2.2.1 x
    rw [← hinit]
    exact hsmooth
  have hθ0per : IsZ2Periodic θ₀ := by
    have hper := hθprev.2.1 0 (show 0 ≤ (0 : ℝ) by norm_num)
    have hinit : θprev 0 = θ₀ := by funext x; exact hθprev.2.2.1 x
    rw [← hinit]
    exact hper
  have hgrad0sq : gradNormSq (spaceGrad θ₀) ≤ 2 * l2NormSq θ₀ / R ^ 2 :=
    analytic_gradient_bound (hθ0smooth.of_le (by norm_num)) hanalytic
  have hRbound := analytic_radius_bound (hθ0smooth.of_le (by norm_num)) hθ0per hmean
    (by
      have hNsq : N ^ 2 = l2NormSq θ₀ := by
        dsimp [N]
        exact Real.sq_sqrt (integral_nonneg (fun x => sq_nonneg (θ₀ x)))
      rw [← hNsq]
      exact sq_pos_of_pos hNpos) hR hanalytic
  have hden : 1 < Real.sqrt 2 * Real.pi := by
    have hsqrt : 1 < Real.sqrt 2 := by
      rw [← Real.sqrt_one]
      exact Real.sqrt_lt_sqrt (by norm_num) (by norm_num)
    nlinarith [Real.pi_gt_three]
  have hRle1 : R ≤ 1 := by
    have hdenpos : 0 < Real.sqrt 2 * Real.pi := by positivity
    have hrecip : 1 / (Real.sqrt 2 * Real.pi) < 1 := (div_lt_one hdenpos).2 hden
    exact hRbound.trans hrecip.le
  have hRinv : 1 ≤ 1 / R := by
    simpa using one_div_le_one_div_of_le hR hRle1
  have hN2 : N ^ 2 = l2NormSq θ₀ := by
    dsimp [N]
    exact Real.sq_sqrt (integral_nonneg (fun x => sq_nonneg (θ₀ x)))
  have hgrad0 : Real.sqrt (gradNormSq (spaceGrad θ₀)) ≤ Real.sqrt 2 * N / R := by
    apply Real.sqrt_le_iff.mpr
    constructor
    · exact div_nonneg (mul_nonneg (Real.sqrt_nonneg _) hNnonneg) hR.le
    · calc
        gradNormSq (spaceGrad θ₀) ≤ 2 * l2NormSq θ₀ / R ^ 2 := hgrad0sq
        _ = (Real.sqrt 2 * N / R) ^ 2 := by
          rw [div_pow, mul_pow, Real.sq_sqrt (by norm_num : 0 ≤ (2 : ℝ)), hN2]
  have hgradTrace := PartIInitial.continuous_classical_gradient_l2_at_initial hTsol N hNpos
  have hgradBound : ∀ᶠ s in 𝓝[>] (0 : ℝ),
      Real.sqrt (gradNormSq (spaceGrad (Tm1 s))) ≤ (Real.sqrt 2 + 1) * N / R := by
    filter_upwards [hgradTrace] with s hs
    have hNdiv : N ≤ N / R := by
      calc N = N * 1 := by ring
        _ ≤ N * (1 / R) := mul_le_mul_of_nonneg_left hRinv hNnonneg
        _ = N / R := by ring
    have hsum : Real.sqrt (gradNormSq (spaceGrad θ₀)) + N ≤
        (Real.sqrt 2 + 1) * N / R := by
      calc
        _ ≤ Real.sqrt 2 * N / R + N / R := add_le_add hgrad0 hNdiv
        _ = (Real.sqrt 2 + 1) * N / R := by ring
    exact le_of_lt (hs.trans_le hsum)
  have hslt1 : {s : ℝ | s < 1} ∈ 𝓝[>] (0 : ℝ) := by
    have hnear : {s : ℝ | s < 1} ∈ 𝓝 (0 : ℝ) :=
      (isOpen_lt continuous_id continuous_const).mem_nhds (by norm_num)
    exact Filter.Eventually.filter_mono nhdsWithin_le_nhds hnear
  filter_upwards [hpair, hgradBound, hslt1, self_mem_nhdsWithin] with s hp hg hs hspos
  have hTt : ContDiff ℝ (⊤ : ℕ∞) (Tm1 s) := by
    change ContDiff ℝ (⊤ : ℕ∞) (T (Nstar β) s)
    by_cases hzero : Nstar β = 0
    · rw [hzero, hT.1]
      exact classicalSol_space_contDiff_of_nonneg hθprev hspos.le
    · exact classicalSol_space_contDiff_of_nonneg
        (hT.2 (Nstar β) (Nat.one_le_iff_ne_zero.mpr hzero) le_rfl) hspos.le
  have hHt : ContDiff ℝ (⊤ : ℕ∞) (I.Hm hΦ m κm' Tm1 s) :=
    Hm_slice_contDiff_pos I hΦ (by omega) hκmpos hθprev hT hspos
  have hAt : ContDiff ℝ (⊤ : ℕ∞) (I.ansatz hΦ m κm' Tm1 s) :=
    ansatz_slice_contDiff I hΦ m κm' hTt hHt
  let P : Vec 2 → ℝ := fun x => I.ansatz hΦ m κm' Tm1 s x - Tm1 s x - I.Hm hΦ m κm' Tm1 s x
  let V : Vec 2 → ℝ := fun x => θm s x - Tm1 s x
  let H : Vec 2 → ℝ := I.Hm hΦ m κm' Tm1 s
  have hPcont : Continuous P := by
    exact ((hAt.continuous.sub hTt.continuous).sub hHt.continuous)
  have hVcont : Continuous V := by
    exact (classicalSol_space_contDiff_of_nonneg hθm hspos.le).continuous.sub hTt.continuous
  have hHcont : Continuous H := hHt.continuous
  have hPnorm := PartIInitial.corrector_l2_bound_by_gradient I hΦ hm hκmpos hTt
  have hHmAt := hHm s ⟨hspos, le_of_lt hs⟩
  have hsplit : (fun x => θm s x - I.ansatz hΦ m κm' Tm1 s x) =
      fun x => (V x + -P x) + -H x := by
    funext x
    dsimp [V, P, H]
    ring
  rw [hsplit]
  have htriangle1 := sqrt_l2NormSq_add_le_of_continuous hVcont hPcont.neg
  have htriangle2 := sqrt_l2NormSq_add_le_of_continuous
    (hVcont.add hPcont.neg) hHcont.neg
  have hPbound : Real.sqrt (l2NormSq P) ≤
      8 * chiSup I κm' m * ((Real.sqrt 2 + 1) * N / R) := by
    exact hPnorm.trans (mul_le_mul_of_nonneg_left hg
      (mul_nonneg (by norm_num) (chiSup_nonneg I hκmpos m)))
  have hPscale : chiSup I κm' m / R ≤ K ^ 2 * e ^ delta β := by
    have hInvScale : 1 / R ≤ e ^ (-(1 + gamma β / 2)) := by
      calc
        1 / R ≤ 1 / (e ^ (1 + gamma β / 2)) := one_div_le_one_div_of_le
          (Real.rpow_pos_of_pos he _ ) hRscale
        _ = e ^ (-(1 + gamma β / 2)) := by
          rw [one_div, ← Real.rpow_neg he.le]
    have hchi := mul_le_mul_of_nonneg_left hInvScale (chiSup_nonneg I hκmpos m)
    have hscale0 : chiSup I κm' m * e ^ (-(1 + gamma β / 2)) ≤ K ^ 2 * e ^ delta β := by
      simpa [κm', e, K] using hKdata.2
    calc
      chiSup I κm' m / R = chiSup I κm' m * (1 / R) := by ring
      _ ≤ chiSup I κm' m * e ^ (-(1 + gamma β / 2)) := hchi
      _ ≤ K ^ 2 * e ^ delta β := hscale0
  have hPfinal : Real.sqrt (l2NormSq P) ≤
      8 * K ^ 2 * (Real.sqrt 2 + 1) * e ^ delta β * N := by
    have hconst : 0 ≤ 8 * (Real.sqrt 2 + 1) * N := by positivity
    calc
      Real.sqrt (l2NormSq P) ≤ 8 * chiSup I κm' m * ((Real.sqrt 2 + 1) * N / R) := hPbound
      _ = (8 * (Real.sqrt 2 + 1) * N) * (chiSup I κm' m / R) := by ring
      _ ≤ (8 * (Real.sqrt 2 + 1) * N) * (K ^ 2 * e ^ delta β) :=
        mul_le_mul_of_nonneg_left hPscale hconst
      _ = 8 * K ^ 2 * (Real.sqrt 2 + 1) * e ^ delta β * N := by ring
  have hpBound : Real.sqrt (l2NormSq V) ≤ 2 * e ^ delta β * N := le_of_lt hp
  have hsumBound : Real.sqrt (l2NormSq ((fun x => V x + -P x) + -H)) ≤
      Real.sqrt (l2NormSq V) + Real.sqrt (l2NormSq P) + Real.sqrt (l2NormSq H) := by
    calc
      _ ≤ Real.sqrt (l2NormSq (fun x => V x + -P x)) +
          Real.sqrt (l2NormSq H) := by simpa [l2NormSq] using htriangle2
      _ ≤ Real.sqrt (l2NormSq V) + Real.sqrt (l2NormSq P) +
          Real.sqrt (l2NormSq H) := by
        have hinner : Real.sqrt (l2NormSq (fun x => V x + -P x)) ≤
            Real.sqrt (l2NormSq V) + Real.sqrt (l2NormSq P) := by
          simpa [l2NormSq] using htriangle1
        exact add_le_add hinner (le_rfl)
  have hHnonneg : 0 ≤ CH * e ^ delta β * N := by positivity
  have hHbound : Real.sqrt (l2NormSq H) ≤ CH * e ^ delta β * N := by
    simpa [H, κm', Tm1] using hHmAt
  calc
    Real.sqrt (l2NormSq ((fun x => V x + -P x) + -H))
        ≤ Real.sqrt (l2NormSq V) + Real.sqrt (l2NormSq P) + Real.sqrt (l2NormSq H) := by
          exact hsumBound
    _ ≤ 2 * e ^ delta β * N +
        (8 * K ^ 2 * (Real.sqrt 2 + 1) * e ^ delta β * N) +
          CH * e ^ delta β * N := by
          exact add_le_add (add_le_add hpBound hPfinal) hHbound
    _ = (CH + 2 + 8 * K ^ 2 * (Real.sqrt 2 + 1)) * e ^ delta β * N := by ring

/-- Zero-data counterpart of the right-limit estimate.  Classical uniqueness makes both
temperature solutions and every T iterate vanish; the supplied Hm estimate then forces the
remaining ansatz term to vanish in L². -/
theorem partI_initial_zero_defect_of_A5_and_Hm
    {β : ℝ} (I : Ingredients β) {Φ : ℕ → ℝ → Vec 2 → ℝ}
    (hΦ : IsStreamSeq I Φ) {m M : ℕ} (hm : 2 ≤ m) (hmM : m ≤ M)
    {κ : ℝ} {c C CH : ℝ} (hc : 0 < c)
    (hA5 :
      (∀ j : ℕ, 1 ≤ j → j < M →
        c * (a β I.Λ j * epsilon β I.Λ j ^ (2 + gamma β)) ≤
            I.kappaAt κ j (M - j) ∧
        I.kappaAt κ j (M - j) ≤
            C * (a β I.Λ j * epsilon β I.Λ j ^ (2 + gamma β))) ∧
      (∀ j : ℕ, 2 ≤ j → j < M →
        c * epsilon β I.Λ (j - 1) ^ (4 * delta β) ≤
            epsilon β I.Λ j ^ 2 / (I.kappaAt κ j (M - j) * tau β I.Λ j) ∧
        epsilon β I.Λ j ^ 2 / (I.kappaAt κ j (M - j) * tau β I.Λ j) ≤
            C * epsilon β I.Λ (j - 1) ^ (4 * delta β)))
    {θ₀ : Vec 2 → ℝ} {θm θprev : ℝ → Vec 2 → ℝ}
    {T : ℕ → ℝ → Vec 2 → ℝ} {κm : ℝ}
    (hNzero : Real.sqrt (l2NormSq θ₀) = 0)
    (hκmpos : 0 < κm)
    (hθm : IsClassicalSol (streamVel (Φ m)) κm (fun _ _ => 0) θ₀ θm)
    (hθprev : IsClassicalSol (streamVel (Φ (m - 1)))
      (I.kappaSeq κ M (m - 1)) (fun _ _ => 0) θ₀ θprev)
    (hT : I.IsTIterates hΦ m (I.kappaSeq κ M m) (I.kappaSeq κ M (m - 1)) θ₀ θprev T)
    (hHm : ∀ t ∈ Set.Ioc (0 : ℝ) 1,
      Real.sqrt (l2NormSq (I.Hm hΦ m (I.kappaSeq κ M m) (T (Nstar β)) t)) ≤
        CH * epsilon β I.Λ (m - 1) ^ delta β * Real.sqrt (l2NormSq θ₀)) :
    ∀ t ∈ Set.Ioc (0 : ℝ) 1,
      Real.sqrt (l2NormSq (fun x => θm t x -
        I.ansatz hΦ m (I.kappaSeq κ M m) (T (Nstar β)) t x)) = 0 := by
  have hSnonneg : 0 ≤ l2NormSq θ₀ := by
    unfold l2NormSq
    exact integral_nonneg fun _ => sq_nonneg _
  have hSzero : l2NormSq θ₀ = 0 := by
    have hsq := congrArg (fun x : ℝ => x ^ 2) hNzero
    rw [Real.sq_sqrt hSnonneg] at hsq
    simpa using hsq
  have hθ₀smooth : ContDiff ℝ (⊤ : ℕ∞) θ₀ := by
    have hsmooth := classicalSmooth_slice_nonneg hθprev.1 (t := 0) (by norm_num)
    have hinit : θprev 0 = θ₀ := funext hθprev.2.2.1
    rw [← hinit]
    exact hsmooth
  have hθ₀periodic : IsZ2Periodic θ₀ := by
    have hper := hθprev.2.1 0 (by norm_num)
    have hinit : θprev 0 = θ₀ := funext hθprev.2.2.1
    rw [← hinit]
    exact hper
  have hθ₀zero : θ₀ = (fun _ : Vec 2 => 0) :=
    AVenhance.Infra.Section4.theta_continuous_periodic_eq_zero_of_l2NormSq_eq_zero
      hθ₀smooth hθ₀periodic hSzero
  have heprev : 0 < epsilon β I.Λ (m - 1) :=
    Infra.Cutoff.epsilon_pos I.one_lt_beta I.beta_lt I.two_pow_seven_le
  have haprev : 0 < a β I.Λ (m - 1) := by
    rw [a]
    exact Real.rpow_pos_of_pos heprev _
  have hfactor : 0 < a β I.Λ (m - 1) *
      epsilon β I.Λ (m - 1) ^ (2 + gamma β) := by positivity
  have hlow := hA5.1 (m - 1) (by omega) (by omega)
  have hκprev : 0 < I.kappaSeq κ M (m - 1) := by
    have hpos := (mul_pos hc hfactor).trans_le hlow.1
    simpa [Ingredients.kappaSeq] using hpos
  have hθprev' : IsClassicalSol (streamVel (Φ (m - 1)))
      (I.kappaSeq κ M (m - 1)) (fun _ _ => 0) (fun _ => 0) θprev := by
    simpa [hθ₀zero] using hθprev
  have hφprev : IsAdmissibleStream (Φ (m - 1)) :=
    AVenhance.Infra.Section4.theta_prev_stream_admissible I Φ hΦ hm
  have hprevZero := PartIInitial.classical_zero_data_solution_is_zero hφprev hκprev hθprev'
  have hθm' : IsClassicalSol (streamVel (Φ m)) κm
      (fun _ _ => 0) (fun _ => 0) θm := by
    simpa [hθ₀zero] using hθm
  have hφm : IsAdmissibleStream (Φ m) := by
    simpa only [Nat.add_sub_cancel] using
      AVenhance.Infra.Section4.theta_prev_stream_admissible I Φ hΦ
        (m := m + 1) (by omega)
  have hmZero := PartIInitial.classical_zero_data_solution_is_zero hφm hκmpos hθm'
  have hT' : I.IsTIterates hΦ m (I.kappaSeq κ M m) (I.kappaSeq κ M (m - 1))
      (fun _ => 0) θprev T := by
    simpa [hθ₀zero] using hT
  have hTzero := PartIInitial.tIterates_zero_of_zero_data I hΦ hm hκprev hθprev' hT'
  intro t ht
  have hHmzero : Real.sqrt (l2NormSq
      (I.Hm hΦ m (I.kappaSeq κ M m) (T (Nstar β)) t)) = 0 := by
    have hb := hHm t ht
    rw [hNzero, mul_zero] at hb
    exact le_antisymm hb (Real.sqrt_nonneg _)
  have hUzero : T (Nstar β) t = fun _ => 0 := hTzero (Nstar β) le_rfl t ht.1.le
  have hgradzero (k : ℤ) (x : Vec 2) : spaceGrad
      (fun y => (fun _ : Vec 2 => (0 : ℝ))
        (I.xFlow hΦ m (lIdx β I.Λ m k) t y))
      (I.xFlowInv hΦ m (lIdx β I.Λ m k) t x) = 0 := by
    ext i
    simp [AVenhance.spaceGrad]
  have hansatz : I.ansatz hΦ m (I.kappaSeq κ M m) (T (Nstar β)) t =
      I.Hm hΦ m (I.kappaSeq κ M m) (T (Nstar β)) t := by
    funext x
    rw [AVenhance.Ingredients.ansatz, hUzero]
    have hsum : (∑' k : ℤ, I.xiMK m k t *
        Homogenization.vecDot (I.chiTilde hΦ m (I.kappaSeq κ M m) k t x)
          (spaceGrad (fun y => (fun _ : Vec 2 => (0 : ℝ))
            (I.xFlow hΦ m (lIdx β I.Λ m k) t y))
            (I.xFlowInv hΦ m (lIdx β I.Λ m k) t x))) = 0 := by
      calc
        _ = ∑' k : ℤ, (0 : ℝ) := tsum_congr fun k => by
          rw [hgradzero k x]
          simp [Homogenization.vecDot]
        _ = 0 := tsum_zero
    rw [hsum]
    simp
  have hdiff : (fun x => θm t x -
      I.ansatz hΦ m (I.kappaSeq κ M m) (T (Nstar β)) t x) =
      fun x => -(I.Hm hΦ m (I.kappaSeq κ M m) (T (Nstar β)) t x) := by
    funext x
    rw [hmZero t ht.1.le, hansatz]
    ring
  rw [hdiff]
  have hneg : l2NormSq (fun x => -(I.Hm hΦ m (I.kappaSeq κ M m)
      (T (Nstar β)) t x)) = l2NormSq
        (I.Hm hΦ m (I.kappaSeq κ M m) (T (Nstar β)) t) := by
    unfold l2NormSq
    congr 1
    funext x
    ring
  rw [hneg, hHmzero]

end AVenhance.Infra.Section5.Integration
