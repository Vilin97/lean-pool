/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section4.ThetaHonestAnalytic
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section4.ThetaDifferentiated
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section4.ThetaCommutatorBounds
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section4.ThetaAnalyticData
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section4.ThetaZeroBounds

/-! Honest energy recursion and analytic bounds for the classical theta
solution, conditional only on the stream-regularity and diffusivity-recursion conclusion data. -/

@[expose] public section

noncomputable section

open MeasureTheory Homogenization
open scoped Topology

namespace AVenhance.Infra.Section4

theorem ThetaHonestRecursion.theta_list_fun_sum_apply {α : Type*} (L : List (α → ℝ))
    (x : α) : L.sum x = (L.map fun f => f x).sum := by
  induction L with
  | nil => simp
  | cons f L ih => simp [ih]

theorem ThetaHonestRecursion.theta_continuous_fun_list_sum {α : Type*} [TopologicalSpace α]
    (L : List (α → ℝ)) (hL : ∀ f ∈ L, Continuous f) : Continuous L.sum := by
  induction L with
  | nil => exact continuous_const
  | cons f L ih =>
      have htail : ∀ g ∈ L, Continuous g := by
        intro g hg
        exact hL g (by simp [hg])
      change Continuous (fun x => f x + L.sum x)
      exact (hL f (by simp)).add (ih htail)

/-- One differentiated-drift term in the joint space-time representation of
the transport commutator. -/
def thetaHonestResidualTermExtension
    (φ θ : ℝ → Vec 2 → ℝ)
    (split : List (Fin 2) × List (Fin 2)) (j : Fin 2)
    (p : ℝ × Vec 2) : ℝ :=
  thetaStreamWordExtension φ split.1 p j *
    thetaWordExtension θ (j :: split.2) p

/-- Joint continuous representative of the differentiated transport
commutator. -/
noncomputable def thetaHonestResidualExtension
    (φ θ : ℝ → Vec 2 → ℝ) (w : List (Fin 2))
  (p : ℝ × Vec 2) : ℝ :=
  ∑ j : Fin 2,
    ((classicalWordCommutatorSplits w).map fun split =>
      thetaHonestResidualTermExtension φ θ split j).sum p

theorem thetaHonestResidualExtension_continuous
    {φ θ : ℝ → Vec 2 → ℝ} {w : List (Fin 2)}
    (hφ : ContDiffOn ℝ (⊤ : ℕ∞) (Function.uncurry φ)
      (Set.Ici (0 : ℝ) ×ˢ Set.univ))
    (hθ : ContDiffOn ℝ (⊤ : ℕ∞) (Function.uncurry θ)
      (Set.Ici (0 : ℝ) ×ˢ Set.univ)) :
    Continuous (thetaHonestResidualExtension φ θ w) := by
  unfold thetaHonestResidualExtension
  apply continuous_finsetSum
  intro j hj
  let L := (classicalWordCommutatorSplits w).map fun split =>
    thetaHonestResidualTermExtension φ θ split j
  have hcont : ∀ f ∈ L, Continuous f := by
    intro f hf
    obtain ⟨split, hsplit, rfl⟩ := List.mem_map.mp hf
    exact ((continuous_apply j).comp (thetaStreamWordExtension_continuous hφ)).mul
      (thetaWordExtension_continuous hθ)
  simpa [L] using ThetaHonestRecursion.theta_continuous_fun_list_sum L hcont

theorem thetaHonestResidualExtension_eq_commutator
    {φ θ : ℝ → Vec 2 → ℝ} {w : List (Fin 2)}
    (hφ : ContDiffOn ℝ (⊤ : ℕ∞) (Function.uncurry φ)
      (Set.Ici (0 : ℝ) ×ˢ Set.univ))
    (hθ : ContDiffOn ℝ (⊤ : ℕ∞) (Function.uncurry θ)
      (Set.Ici (0 : ℝ) ×ˢ Set.univ))
    {t : ℝ} (ht : 0 < t) (x : Vec 2) :
    thetaHonestResidualExtension φ θ w (t, x) =
      classicalWordDerivative w
        (classicalTransport
          (AVenhance.streamVel (fun _ => φ t) 0) (θ t)) x -
        vecDot (AVenhance.streamVel (fun _ => φ t) 0 x)
          (spaceGrad (classicalWordDerivative w (θ t)) x) := by
  let f := φ t
  let u := θ t
  have hf : ContDiff ℝ (⊤ : ℕ∞) f := by
    have hm : ContDiffOn ℝ (⊤ : ℕ∞) (fun y : Vec 2 => (t, y)) Set.univ :=
      contDiffOn_const.prodMk contDiffOn_id
    have hmem : ∀ y ∈ (Set.univ : Set (Vec 2)),
        (t, y) ∈ Set.Ici (0 : ℝ) ×ˢ Set.univ := by
      intro y hy
      exact ⟨ht.le, Set.mem_univ _⟩
    have hc := hφ.comp hm hmem
    exact contDiffOn_univ.mp (by simpa [f, Function.uncurry, Function.comp_def] using hc)
  have hu : ContDiff ℝ (⊤ : ℕ∞) u := by
    have hm : ContDiffOn ℝ (⊤ : ℕ∞) (fun y : Vec 2 => (t, y)) Set.univ :=
      contDiffOn_const.prodMk contDiffOn_id
    have hmem : ∀ y ∈ (Set.univ : Set (Vec 2)),
        (t, y) ∈ Set.Ici (0 : ℝ) ×ˢ Set.univ := by
      intro y hy
      exact ⟨ht.le, Set.mem_univ _⟩
    have hc := hθ.comp hm hmem
    exact contDiffOn_univ.mp (by simpa [u, Function.uncurry, Function.comp_def] using hc)
  have hstream (split : List (Fin 2) × List (Fin 2)) (j : Fin 2) :
    thetaStreamWordExtension φ split.1 (t, x) j =
        classicalWordDerivative split.1
          (fun y => AVenhance.streamVel (fun _ => f) 0 y j) x := by
    rw [thetaStreamWordExtension_eq_slice t ht x]
    exact (congrFun (classicalWordDerivative_streamVel_component
      split.1 f hf j) x).symm
  have hword (split : List (Fin 2) × List (Fin 2)) (j : Fin 2) :
      thetaWordExtension θ (j :: split.2) (t, x) =
        classicalWordDerivative split.2
          (fun y => spaceGrad u y j) x := by
    rw [thetaWordExtension_eq_slice t ht x]
    exact (congrFun (classicalWordDerivative_commute_gradient
      split.2 u hu j) x).symm
  have hsplit (j : Fin 2) :
      ((classicalWordCommutatorSplits w).map fun split =>
        thetaHonestResidualTermExtension φ θ split j).sum (t, x) =
      classicalWordCommutatorExpansion w
        (fun y => AVenhance.streamVel (fun _ => f) 0 y j)
        (fun y => spaceGrad u y j) x := by
    rw [ThetaHonestRecursion.theta_list_fun_sum_apply]
    unfold classicalWordCommutatorExpansion Classical.classicalWordCommutatorExpansion
    rw [ThetaHonestRecursion.theta_list_fun_sum_apply]
    simp only [List.map_map, Function.comp_def]
    apply congrArg List.sum
    apply List.map_congr_left
    intro split hmem
    change thetaHonestResidualTermExtension φ θ split j (t, x) =
      classicalWordDerivative split.1 (fun y => AVenhance.streamVel (fun _ => f) 0 y j) x *
        classicalWordDerivative split.2 (fun y => spaceGrad u y j) x
    dsimp only [thetaHonestResidualTermExtension]
    rw [hstream, hword]
  rw [thetaHonestResidualExtension]
  have hsum : ∑ j : Fin 2,
      classicalWordCommutatorExpansion w
        (fun y => AVenhance.streamVel (fun _ => f) 0 y j)
        (fun y => spaceGrad u y j) x =
      ∑ j : Fin 2,
        ((classicalWordCommutatorSplits w).map fun split =>
          thetaHonestResidualTermExtension φ θ split j).sum (t, x) := by
    apply Finset.sum_congr rfl
    intro j hj
    exact (hsplit j).symm
  rw [← hsum]
  exact (classicalWordDerivative_transport_eq_commutatorExpansion
    w (AVenhance.streamVel (fun _ => f) 0) u
    (theta_streamVel_contDiff f hf) hu x).symm

/-- The coefficient supplied by the high-order stream-regularity barNorm bound for
a split with `q` derivatives on the drift. -/
noncomputable def thetaHonestDriftCoefficient {β : ℝ} {m : ℕ}
    (I : AVenhance.Ingredients β) (q : ℕ) : ℝ :=
  2 ^ 5 * AVenhance.a β I.Λ (m - 1) *
    AVenhance.epsilon β I.Λ (m - 1) ^ 2 *
    ((q + 1).factorial : ℝ) *
    (2 ^ 8 * (AVenhance.epsilon β I.Λ (m - 1))⁻¹) ^ (q + 1)

theorem ThetaHonestRecursion.theta_sqrt_gradient_word_le_energyLevel
    {θ : ℝ → Vec 2 → ℝ} {κ : ℝ} (hκ : 0 < κ)
    (w : List (Fin 2)) :
    Real.sqrt (thetaWordSpaceTimeGradientEnergy θ w) ≤
      thetaEnergyLevel θ κ w.length / Real.sqrt κ := by
  let i : Fin w.length → Fin 2 := fun j => w.get j
  have hword : thetaCoordinateWord i = w := by
    exact List.ofFn_get w
  have hlevel := thetaEnergyLevel_le_of_coordinate θ κ w.length i
  rw [hword] at hlevel
  have hsp : 0 ≤ Real.sqrt (thetaWordSpatialEnergySup θ w) := Real.sqrt_nonneg _
  have hgrad : Real.sqrt κ *
      Real.sqrt (thetaWordSpaceTimeGradientEnergy θ w) ≤
        thetaEnergyLevel θ κ w.length := by linarith
  apply (le_div_iff₀ (Real.sqrt_pos.2 hκ)).2
  nlinarith [hgrad]

theorem ThetaHonestRecursion.theta_residual_term_integral_bound_of_A3
    {β : ℝ} {m : ℕ} {κ T : ℝ} (I : AVenhance.Ingredients β)
    (Φ : ℕ → ℝ → Vec 2 → ℝ) (hΦ : AVenhance.IsStreamSeq I Φ)
    (hm : 2 ≤ m)
    (hA3 : ∀ j : ℕ, 1 ≤ j → ∀ t : ℝ, ∀ n : ℕ, 2 ≤ n →
      AVenhance.barNorm n (2 ^ 8 * (AVenhance.epsilon β I.Λ j)⁻¹)
        (Φ j t) ≤
      ENNReal.ofReal (2 ^ 5 * AVenhance.a β I.Λ j *
        AVenhance.epsilon β I.Λ j ^ 2 *
        (((n : ℝ) + 2) ^ 2 / ((n : ℝ) + 1) ^ 3)))
    {θ₀ : Vec 2 → ℝ} {θ : ℝ → Vec 2 → ℝ}
    (hsol : AVenhance.IsClassicalSol
      (AVenhance.streamVel (fun t => Φ (m - 1) t)) κ
      (fun _ _ => 0) θ₀ θ)
    (hκ : 0 < κ) (hT : T ∈ Set.Icc (0 : ℝ) 1)
    {w : List (Fin 2)} (split : List (Fin 2) × List (Fin 2))
    (j : Fin 2) (hleft : 1 ≤ split.1.length) :
    |∫ p in Set.Ioo (0 : ℝ) T ×ˢ AVenhance.unitCube,
      thetaWordExtension θ w p *
        thetaHonestResidualTermExtension (fun t => Φ (m - 1) t) θ split j p| ≤
      thetaHonestDriftCoefficient (m := m) I split.1.length *
        Real.sqrt (thetaWordSpatialEnergySup θ w) *
        thetaEnergyLevel θ κ split.2.length / Real.sqrt κ := by
  let φ : ℝ → Vec 2 → ℝ := fun t => Φ (m - 1) t
  let e := AVenhance.epsilon β I.Λ (m - 1)
  let q := split.1.length
  have he : 0 < e := AVenhance.Infra.Cutoff.epsilon_pos
    I.one_lt_beta I.beta_lt I.two_pow_seven_le
  have hφ : ContDiffOn ℝ (⊤ : ℕ∞) (Function.uncurry φ)
      (Set.Ici (0 : ℝ) ×ˢ Set.univ) := by
    have hφtop := (theta_prev_stream_admissible I Φ hΦ hm).1
    simpa [φ] using hφtop.contDiffOn.mono (by
      intro p hp
      exact Set.mem_univ p)
  have hθ : ContDiffOn ℝ (⊤ : ℕ∞) (Function.uncurry θ)
      (Set.Ici (0 : ℝ) ×ˢ Set.univ) := hsol.1
  let F : ℝ × Vec 2 → ℝ := thetaWordExtension θ w
  let G : ℝ × Vec 2 → ℝ := thetaWordExtension θ (j :: split.2)
  let A : ℝ × Vec 2 → ℝ := fun p =>
    thetaStreamWordExtension φ split.1 p j
  have hF : Continuous F := thetaWordExtension_continuous hθ
  have hG : Continuous G := thetaWordExtension_continuous hθ
  have hA : Continuous A := by
    change Continuous (fun p => thetaStreamWordExtension φ split.1 p j)
    exact (continuous_apply j).comp (thetaStreamWordExtension_continuous hφ)
  have hcoef : ∀ p ∈ Set.Ioo (0 : ℝ) T ×ˢ AVenhance.unitCube,
      |A p| ≤ thetaHonestDriftCoefficient (m := m) I q := by
    intro p hp
    change |thetaStreamWordExtension φ split.1 p j| ≤ _
    have hpoint := theta_prev_drift_word_abs_le_of_A3 I Φ hΦ hm hA3
      p.1 split.1 hleft j p.2
    rw [thetaStreamWordExtension_eq_slice p.1 hp.1.1 p.2]
    have hf : ContDiff ℝ (⊤ : ℕ∞) (Φ (m - 1) p.1) := by
      have hadm := theta_prev_stream_admissible I Φ hΦ hm
      have hmap : ContDiff ℝ (⊤ : ℕ∞)
          (fun y : Vec 2 => (p.1, y)) :=
        contDiff_const.prodMk contDiff_id
      simpa [Function.uncurry, Function.comp_def] using hadm.1.comp hmap
    have hstream := congrFun (classicalWordDerivative_streamVel_component
      split.1 (Φ (m - 1) p.1) hf j) p.2
    rw [← hstream]
    simpa [thetaHonestDriftCoefficient, q, φ, e] using hpoint
  have ha : 0 < AVenhance.a β I.Λ (m - 1) := by
    rw [AVenhance.a]
    exact Real.rpow_pos_of_pos he _
  have hM : 0 ≤ thetaHonestDriftCoefficient (m := m) I q := by
    unfold thetaHonestDriftCoefficient
    positivity
  have hCauchy := theta_intervalCube_integral_mul_bounded_le
    (T := T) (M := thetaHonestDriftCoefficient (m := m) I q)
      hT hF hG hA hM hcoef
  have hleftEnergy :
      (∫ p in Set.Ioo (0 : ℝ) T ×ˢ AVenhance.unitCube, F p ^ 2) ≤
        thetaWordSpatialEnergySup θ w := by
    exact theta_interval_word_l2_le_spatial_sup hsol hT w
  have hrightEnergy :
      (∫ p in Set.Ioo (0 : ℝ) T ×ˢ AVenhance.unitCube, G p ^ 2) ≤
        thetaWordSpaceTimeGradientEnergy θ split.2 := by
    unfold G
    exact theta_interval_word_l2_le_gradient hθ hT
      (j :: split.2) split.2 (List.Perm.refl _)
  have hrootL := Real.sqrt_le_sqrt hleftEnergy
  have hrootR := Real.sqrt_le_sqrt hrightEnergy
  have hrootR' := hrootR.trans (ThetaHonestRecursion.theta_sqrt_gradient_word_le_energyLevel
    (κ := κ) hκ split.2)
  have hbound := calc
      |∫ p in Set.Ioo (0 : ℝ) T ×ˢ AVenhance.unitCube,
          F p * (A p * G p)| ≤
        thetaHonestDriftCoefficient (m := m) I q *
          Real.sqrt (∫ p in Set.Ioo (0 : ℝ) T ×ˢ AVenhance.unitCube, F p ^ 2) *
          Real.sqrt (∫ p in Set.Ioo (0 : ℝ) T ×ˢ AVenhance.unitCube, G p ^ 2) := hCauchy
      _ ≤ thetaHonestDriftCoefficient (m := m) I q *
          Real.sqrt (thetaWordSpatialEnergySup θ w) *
          (thetaEnergyLevel θ κ split.2.length / Real.sqrt κ) := by
        have hmul := mul_le_mul hrootL hrootR'
          (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
        nlinarith [hM]
  simpa [F, G, A, thetaHonestResidualTermExtension, q, φ,
    thetaHonestDriftCoefficient] using (calc
      |∫ p in Set.Ioo (0 : ℝ) T ×ˢ AVenhance.unitCube,
          F p * (A p * G p)| ≤
        thetaHonestDriftCoefficient (m := m) I q *
          Real.sqrt (thetaWordSpatialEnergySup θ w) *
          (thetaEnergyLevel θ κ split.2.length / Real.sqrt κ) := hbound
      _ = thetaHonestDriftCoefficient (m := m) I split.1.length *
          Real.sqrt (thetaWordSpatialEnergySup θ w) *
          thetaEnergyLevel θ κ split.2.length / Real.sqrt κ := by
        simp [q]
        ring)

/-- Closed time-space unit cell for the temperature residual recursion. -/
def ThetaHonestRecursion.thetaResidualClosedCell : Set (ℝ × Vec 2) :=
  Set.Icc (0 : ℝ) 1 ×ˢ Set.pi Set.univ
    (fun _ : Fin 2 => Set.Icc (0 : ℝ) 1)

theorem ThetaHonestRecursion.thetaResidualClosedCell_compact :
    IsCompact ThetaHonestRecursion.thetaResidualClosedCell := by
  apply IsCompact.prod isCompact_Icc
  simpa [ThetaHonestRecursion.thetaResidualClosedCell] using
    isCompact_univ_pi (fun _ : Fin 2 => isCompact_Icc)

theorem ThetaHonestRecursion.theta_residual_interval_subset_closedCell {T : ℝ}
    (hT : T ∈ Set.Icc (0 : ℝ) 1) :
    Set.Ioo (0 : ℝ) T ×ˢ AVenhance.unitCube ⊆ ThetaHonestRecursion.thetaResidualClosedCell := by
  rintro ⟨t, x⟩ ⟨ht, hx⟩
  refine ⟨⟨le_of_lt ht.1, ht.2.le.trans hT.2⟩, ?_⟩
  change ∀ i ∈ Set.univ, x i ∈ Set.Icc (0 : ℝ) 1
  intro i hi
  exact ⟨le_of_lt (hx i hi).1, le_of_lt (hx i hi).2⟩

theorem ThetaHonestRecursion.theta_residual_interval_integrable {T : ℝ}
    (hT : T ∈ Set.Icc (0 : ℝ) 1) {f : ℝ × Vec 2 → ℝ}
    (hf : Continuous f) :
    IntegrableOn f (Set.Ioo (0 : ℝ) T ×ˢ AVenhance.unitCube) := by
  exact (hf.continuousOn.integrableOn_compact ThetaHonestRecursion.thetaResidualClosedCell_compact)
    |>.mono_set (ThetaHonestRecursion.theta_residual_interval_subset_closedCell hT)

theorem ThetaHonestRecursion.theta_abs_list_sum_le (L : List ℝ) :
    |L.sum| ≤ (L.map fun a => |a|).sum := by
  induction L with
  | nil => simp
  | cons a L ih =>
      simp only [List.sum_cons, List.map_cons]
      calc
        |a + L.sum| ≤ |a| + |L.sum| := abs_add_le _ _
        _ ≤ |a| + (List.map (fun a => |a|) L).sum := by nlinarith [ih]

theorem ThetaHonestRecursion.theta_list_sum_right_factor {α : Type*}
    (L : List α) (f : α → ℝ) (c : ℝ) :
    (L.map fun a => f a * c).sum = (L.map f).sum * c := by
  induction L with
  | nil => simp
  | cons a L ih =>
      simp only [List.map_cons, List.sum_cons]
      rw [ih]
      ring

/-- The complete commutator pairing on a partial time interval, bounded by
the stream-regularity Leibniz convolution and the lower energy levels. -/
theorem ThetaHonestRecursion.theta_residual_pairing_abs_le_of_A3
    {β : ℝ} {m : ℕ} {κ T : ℝ} (I : AVenhance.Ingredients β)
    (Φ : ℕ → ℝ → Vec 2 → ℝ) (hΦ : AVenhance.IsStreamSeq I Φ)
    (hm : 2 ≤ m)
    (hA3 : ∀ j : ℕ, 1 ≤ j → ∀ t : ℝ, ∀ n : ℕ, 2 ≤ n →
      AVenhance.barNorm n (2 ^ 8 * (AVenhance.epsilon β I.Λ j)⁻¹)
        (Φ j t) ≤
      ENNReal.ofReal (2 ^ 5 * AVenhance.a β I.Λ j *
        AVenhance.epsilon β I.Λ j ^ 2 *
        (((n : ℝ) + 2) ^ 2 / ((n : ℝ) + 1) ^ 3)))
    {θ₀ : Vec 2 → ℝ} {θ : ℝ → Vec 2 → ℝ}
    (hsol : AVenhance.IsClassicalSol
      (AVenhance.streamVel (fun t => Φ (m - 1) t)) κ
      (fun _ _ => 0) θ₀ θ)
    (hκ : 0 < κ) (hT : T ∈ Set.Icc (0 : ℝ) 1)
    (w : List (Fin 2)) :
    |∫ p in Set.Ioo (0 : ℝ) T ×ˢ AVenhance.unitCube,
      thetaWordExtension θ w p *
        thetaHonestResidualExtension (fun t => Φ (m - 1) t) θ w p| ≤
      2 * Real.sqrt (thetaWordSpatialEnergySup θ w) *
        ∑ q ∈ Finset.range (w.length + 1),
          (((if q = 0 then 0 else w.length.choose q : ℕ) : ℝ) *
            (thetaHonestDriftCoefficient (m := m) I q *
              thetaEnergyLevel θ κ (w.length - q) / Real.sqrt κ)) := by
  let φ : ℝ → Vec 2 → ℝ := fun t => Φ (m - 1) t
  let S : Set (ℝ × Vec 2) := Set.Ioo (0 : ℝ) T ×ˢ AVenhance.unitCube
  let F : ℝ × Vec 2 → ℝ := thetaWordExtension θ w
  let L : List (List (Fin 2) × List (Fin 2)) :=
    classicalWordCommutatorSplits w
  let P (j : Fin 2) : List (ℝ × Vec 2 → ℝ) :=
    L.map fun split => fun p =>
      F p * thetaHonestResidualTermExtension φ θ split j p
  have hθcont : ContDiffOn ℝ (⊤ : ℕ∞) (Function.uncurry θ)
      (Set.Ici (0 : ℝ) ×ˢ Set.univ) := hsol.1
  have hφcont : ContDiffOn ℝ (⊤ : ℕ∞) (Function.uncurry φ)
      (Set.Ici (0 : ℝ) ×ˢ Set.univ) := by
    have hφtop := (theta_prev_stream_admissible I Φ hΦ hm).1
    simpa [φ] using hφtop.contDiffOn.mono (by
      intro p hp
      exact Set.mem_univ p)
  have hF : Continuous F := thetaWordExtension_continuous hθcont
  have htermCont (j : Fin 2) : ∀ f ∈ P j, Continuous f := by
    intro f hf
    obtain ⟨split, hs, rfl⟩ := List.mem_map.mp hf
    exact hF.mul ((continuous_apply j).comp
      (thetaStreamWordExtension_continuous hφcont) |>.mul
        (thetaWordExtension_continuous hθcont))
  have hPcont (j : Fin 2) : Continuous (P j).sum := by
    exact ThetaHonestRecursion.theta_continuous_fun_list_sum (P j) (htermCont j)
  have hsumIntegral :
      (∫ p in S, F p * thetaHonestResidualExtension φ θ w p) =
        ∑ j : Fin 2, ((P j).map fun f => ∫ p in S, f p).sum := by
    have hpoint (p : ℝ × Vec 2) :
        F p * thetaHonestResidualExtension φ θ w p =
          ∑ j : Fin 2, ((P j).map fun f => f p).sum := by
      rw [thetaHonestResidualExtension]
      simp only [Fin.sum_univ_two]
      rw [ThetaHonestRecursion.theta_list_fun_sum_apply
        (L.map fun split => thetaHonestResidualTermExtension φ θ split 0) p,
        ThetaHonestRecursion.theta_list_fun_sum_apply
          (L.map fun split => thetaHonestResidualTermExtension φ θ split 1) p,
        ← ThetaHonestRecursion.theta_list_fun_sum_apply (P 0) p,
        ← ThetaHonestRecursion.theta_list_fun_sum_apply (P 1) p]
      simp only [P, L, List.map_map, Function.comp_def]
      have hlist (j : Fin 2) :
          F p * (L.map fun split =>
            thetaHonestResidualTermExtension φ θ split j p).sum =
          (L.map fun split =>
            F p * thetaHonestResidualTermExtension φ θ split j p).sum := by
        induction L with
        | nil => simp
        | cons split rest ih =>
            simp only [List.map_cons, List.sum_cons]
            rw [mul_add, ih]
      rw [ThetaHonestRecursion.theta_list_fun_sum_apply
          (L.map fun split => fun p =>
            F p * thetaHonestResidualTermExtension φ θ split 0 p) p,
        ThetaHonestRecursion.theta_list_fun_sum_apply
          (L.map fun split => fun p =>
            F p * thetaHonestResidualTermExtension φ θ split 1 p) p]
      simp only [List.map_map, Function.comp_def]
      rw [mul_add, hlist 0, hlist 1]
    calc
      _ = ∫ p in S, ∑ j : Fin 2, ((P j).map fun f => f p).sum := by
        apply setIntegral_congr_fun
          (MeasurableSet.prod measurableSet_Ioo thetaTime_measurableSet_unitCube)
        intro p hp
        exact hpoint p
      _ = ∫ p in S, ∑ j : Fin 2, (P j).sum p := by
        congr 1
        funext p
        apply Finset.sum_congr rfl
        intro j hj
        exact (ThetaHonestRecursion.theta_list_fun_sum_apply (P j) p).symm
      _ = ∑ j : Fin 2, ∫ p in S, (P j).sum p := by
        rw [MeasureTheory.integral_finsetSum (s := Finset.univ)
          (f := fun j p => (P j).sum p) (by
            intro j hj
            exact ThetaHonestRecursion.theta_residual_interval_integrable hT (hPcont j))]
      _ = ∑ j : Fin 2, ((P j).map fun f => ∫ p in S, f p).sum := by
        apply Finset.sum_congr rfl
        intro j hj
        simpa only [ThetaHonestRecursion.theta_list_fun_sum_apply] using
          theta_intervalCube_integral_list_sum hT (P j) (htermCont j)
  rw [hsumIntegral]
  have hlist (j : Fin 2) :
      ((P j).map fun f => |∫ p in S, f p|).sum ≤
        (L.map fun split =>
          thetaHonestDriftCoefficient (m := m) I split.1.length *
            Real.sqrt (thetaWordSpatialEnergySup θ w) *
            thetaEnergyLevel θ κ split.2.length / Real.sqrt κ).sum := by
    simp only [P, List.map_map, Function.comp_def]
    apply List.sum_le_sum
    intro split hs
    have hleft : 1 ≤ split.1.length := by
      have hne := classicalWordCommutatorSplits_left_ne_nil w hs
      cases hlen : split.1.length with
      | zero => exact (hne (List.length_eq_zero_iff.mp hlen)).elim
      | succ q => omega
    have hterm := ThetaHonestRecursion.theta_residual_term_integral_bound_of_A3 (w := w) I Φ hΦ hm
        hA3
      hsol hκ hT split j hleft
    simpa [P, L, S, F, φ, thetaHonestResidualTermExtension,
      mul_assoc] using hterm
  have hlistsum :
      ∑ j : Fin 2,
        ((P j).map fun f => |∫ p in S, f p|).sum ≤
      ∑ j : Fin 2,
        (L.map fun split =>
          thetaHonestDriftCoefficient (m := m) I split.1.length *
            Real.sqrt (thetaWordSpatialEnergySup θ w) *
            thetaEnergyLevel θ κ split.2.length / Real.sqrt κ).sum :=
    Finset.sum_le_sum (by intro j hj; exact hlist j)
  have hfactor :
      (L.map fun split =>
        thetaHonestDriftCoefficient (m := m) I split.1.length *
          Real.sqrt (thetaWordSpatialEnergySup θ w) *
          thetaEnergyLevel θ κ split.2.length / Real.sqrt κ).sum =
      Real.sqrt (thetaWordSpatialEnergySup θ w) *
        (L.map fun split =>
          thetaHonestDriftCoefficient (m := m) I split.1.length *
            thetaEnergyLevel θ κ split.2.length / Real.sqrt κ).sum := by
    calc
      _ = (L.map fun split =>
          (thetaHonestDriftCoefficient (m := m) I split.1.length *
            thetaEnergyLevel θ κ split.2.length / Real.sqrt κ) *
              Real.sqrt (thetaWordSpatialEnergySup θ w)).sum := by
        apply congrArg List.sum
        apply List.map_congr_left
        intro split hs
        ring
      _ = Real.sqrt (thetaWordSpatialEnergySup θ w) *
          (L.map fun split =>
            thetaHonestDriftCoefficient (m := m) I split.1.length *
              thetaEnergyLevel θ κ split.2.length / Real.sqrt κ).sum := by
        rw [ThetaHonestRecursion.theta_list_sum_right_factor]
        ring
  have hweight :
      (L.map fun split =>
        thetaHonestDriftCoefficient (m := m) I split.1.length *
          thetaEnergyLevel θ κ split.2.length / Real.sqrt κ).sum =
      ∑ q ∈ Finset.range (w.length + 1),
        (((if q = 0 then 0 else w.length.choose q : ℕ) : ℝ) *
          (thetaHonestDriftCoefficient (m := m) I q *
            thetaEnergyLevel θ κ (w.length - q) / Real.sqrt κ)) := by
    have hsame :
        (L.map fun split =>
          thetaHonestDriftCoefficient (m := m) I split.1.length *
            thetaEnergyLevel θ κ split.2.length / Real.sqrt κ).sum =
        (L.map fun split =>
          thetaHonestDriftCoefficient (m := m) I split.1.length *
            thetaEnergyLevel θ κ (w.length - split.1.length) / Real.sqrt κ).sum := by
      apply congrArg List.sum
      apply List.map_congr_left
      intro split hs
      have hlen := classicalWordCommutatorSplits_length w hs
      have hright : split.2.length = w.length - split.1.length := by omega
      rw [hright]
    rw [hsame]
    exact theta_commutator_split_weighted_sum w
      (fun q => thetaHonestDriftCoefficient (m := m) I q *
        thetaEnergyLevel θ κ (w.length - q) / Real.sqrt κ)
  have hsumabs :
      |∑ j : Fin 2, ((P j).map fun f => ∫ p in S, f p).sum| ≤
        ∑ j : Fin 2,
          ((P j).map fun f => |∫ p in S, f p|).sum := by
    calc
      _ ≤ ∑ j : Fin 2, |((P j).map fun f => ∫ p in S, f p).sum| :=
        Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ j : Fin 2,
          ((P j).map fun f => |∫ p in S, f p|).sum := by
        apply Finset.sum_le_sum
        intro j hj
        simpa [List.map_map, Function.comp_def] using
          ThetaHonestRecursion.theta_abs_list_sum_le ((P j).map fun f => ∫ p in S, f p)
  have hfinal :
      (∑ j : Fin 2,
        (L.map fun split =>
          thetaHonestDriftCoefficient (m := m) I split.1.length *
            Real.sqrt (thetaWordSpatialEnergySup θ w) *
            thetaEnergyLevel θ κ split.2.length / Real.sqrt κ).sum) =
        2 * Real.sqrt (thetaWordSpatialEnergySup θ w) *
          ∑ q ∈ Finset.range (w.length + 1),
            (((if q = 0 then 0 else w.length.choose q : ℕ) : ℝ) *
              (thetaHonestDriftCoefficient (m := m) I q *
                thetaEnergyLevel θ κ (w.length - q) / Real.sqrt κ)) := by
    rw [Fin.sum_univ_two, hfactor, hweight]
    ring
  exact hsumabs.trans (hlistsum.trans (le_of_eq hfinal))

theorem ThetaHonestRecursion.theta_energyLevel_nonneg
    {θ : ℝ → Vec 2 → ℝ} {κ : ℝ} (n : ℕ) :
    0 ≤ thetaEnergyLevel θ κ n := by
  let i : Fin n → Fin 2 := fun _ => 0
  have hterm : 0 ≤ Real.sqrt (thetaWordSpatialEnergySup θ
      (thetaCoordinateWord i)) + Real.sqrt κ * Real.sqrt
        (thetaWordSpaceTimeGradientEnergy θ (thetaCoordinateWord i)) := by
    exact add_nonneg (Real.sqrt_nonneg _) <|
      mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
  exact hterm.trans (thetaEnergyLevel_le_of_coordinate θ κ n i)

theorem ThetaHonestRecursion.theta_driftCoefficient_nonneg {β : ℝ} {m q : ℕ}
    (I : AVenhance.Ingredients β) :
    0 ≤ thetaHonestDriftCoefficient (m := m) I q := by
  unfold thetaHonestDriftCoefficient
  have he : 0 < AVenhance.epsilon β I.Λ (m - 1) :=
    AVenhance.Infra.Cutoff.epsilon_pos
      I.one_lt_beta I.beta_lt I.two_pow_seven_le
  rw [AVenhance.a]
  positivity

private theorem ThetaHonestRecursion.theta_word_energy_bound_of_A3_energyT1 :
  ∀ {β : ℝ} {m : ℕ} {κ : ℝ} (I : Ingredients β) (Φ : ℕ → ℝ → Vec (2 : ℕ) → ℝ), IsStreamSeq I Φ →
    (2 : ℕ) ≤ m → (∀ (j : ℕ), (1 : ℕ) ≤ j → ∀ (t : ℝ) (n : ℕ), (2 : ℕ) ≤ n → barNorm n ((2 : ℝ)
    ^ (8 : ℕ) * (epsilon β I.Λ j)⁻¹) (Φ j t) ≤ ENNReal.ofReal ((2 : ℝ) ^ (5 : ℕ) * AVenhance.a β
    I.Λ j * epsilon β I.Λ j ^ (2 : ℕ) * (((↑n : ℝ) + (2 : ℝ)) ^ (2 : ℕ) / ((↑n : ℝ) + (1 : ℝ)) ^
    (3 : ℕ)))) → ∀ {θ₀ : Vec (2 : ℕ) → ℝ} {θ : ℝ → Vec (2 : ℕ) → ℝ}, IsClassicalSol (streamVel
    fun (t : ℝ) => Φ (m - (1 : ℕ)) t) κ (fun (_ : ℝ) (_ : Vec (2 : ℕ)) => (0 : ℝ)) θ₀ θ → (0 :
    ℝ) < κ → ∀ (w : List (Fin (2 : ℕ))),
  let φ : ℝ → Vec (2 : ℕ) → ℝ := fun (t : ℝ) => Φ (m - (1 : ℕ)) t;
  let S : ℝ := thetaWordSpatialEnergySup θ w;
  let S₀ : ℝ := ∫ (x : Vec (2 : ℕ)) in unitCube, classicalWordDerivative w θ₀ x ^ (2 : ℕ);
  let B : ℝ := ∑ q ∈ Finset.range (w.length + (1 : ℕ)), (↑(if q = (0 : ℕ) then (0 : ℕ) else
    w.length.choose q) : ℝ) * (thetaHonestDriftCoefficient (m := m) I q * thetaEnergyLevel θ κ
    (w.length - q) / √κ);
  let X : ℝ := √S;
  IsAdmissibleStream φ → (∀ T ∈ Set.Icc (0 : ℝ) (1 : ℝ), ∫ (t : ℝ) in (0 : ℝ)..T, ∫ (x : Vec (2
    : ℕ)) in unitCube, classicalWordDerivative w (θ t) x * (classicalWordDerivative w
    (classicalTransport (streamVel (fun (s : ℝ) => Φ (m - (1 : ℕ)) s) t) (θ t)) x - vecDot
    (streamVel (fun (s : ℝ) => Φ (m - (1 : ℕ)) s) t x) (spaceGrad (classicalWordDerivative w (θ
    t)) x)) = ∫ (p : ℝ × Vec (2 : ℕ)) in Set.Ioo (0 : ℝ) T ×ˢ unitCube, thetaWordExtension θ w p
    * thetaHonestResidualExtension φ θ w p) → ∀ T ∈ Set.Icc (0 : ℝ) (1 : ℝ),
    thetaWordSpatialEnergy θ w T ≤ S₀ + (4 : ℝ) * X * B
    := by
  intro β m κ I Φ hΦ hm hA3 θ₀ θ hsol hκ w φ S S₀ B X hφ hresidual_to_set T hT
  have hidentity :=
    (theta_classical_differentiated_energy_integrated hφ hsol hT.1 w).1
  let P : ℝ := ∫ t in (0 : ℝ)..T,
    ∫ x in AVenhance.unitCube,
      classicalWordDerivative w (θ t) x *
        (classicalWordDerivative w
            (classicalTransport
              (AVenhance.streamVel (fun s => Φ (m - 1) s) t) (θ t)) x -
          vecDot (AVenhance.streamVel (fun s => Φ (m - 1) s) t x)
            (AVenhance.spaceGrad (classicalWordDerivative w (θ t)) x))
  have hpair := ThetaHonestRecursion.theta_residual_pairing_abs_le_of_A3
    (w := w) I Φ hΦ hm hA3 hsol hκ hT
  have hpair' : |P| ≤ 2 * X * B := by
    rw [← hresidual_to_set T hT] at hpair
    simpa [P, X, B, S] using hpair
  have hPcost : -2 * P ≤ 4 * X * B := by
    calc
      -2 * P ≤ 2 * |P| := by nlinarith [neg_le_abs P]
      _ ≤ 2 * (2 * X * B) := by
        exact mul_le_mul_of_nonneg_left hpair' (by norm_num)
      _ = 4 * X * B := by ring
  have hgradnonneg :
      0 ≤ ∫ t in (0 : ℝ)..T,
        ∫ x in AVenhance.unitCube,
          Homogenization.vecNormSq
            (AVenhance.spaceGrad (classicalWordDerivative w (θ t)) x) := by
    apply intervalIntegral.integral_nonneg hT.1
    intro t ht
    exact integral_nonneg fun _ => Homogenization.vecNormSq_nonneg _
  have hdrop : 0 ≤ 2 * κ *
      (∫ t in (0 : ℝ)..T,
        ∫ x in AVenhance.unitCube,
          Homogenization.vecNormSq
            (AVenhance.spaceGrad (classicalWordDerivative w (θ t)) x)) :=
    mul_nonneg (mul_nonneg (by norm_num) hκ.le) hgradnonneg
  have hrewrite :
      thetaWordSpatialEnergy θ w T + 2 * κ *
        (∫ t in (0 : ℝ)..T,
          ∫ x in AVenhance.unitCube,
            Homogenization.vecNormSq
              (AVenhance.spaceGrad (classicalWordDerivative w (θ t)) x)) =
        S₀ - 2 * P := by
    simpa [thetaWordSpatialEnergy, S₀, P] using hidentity
  linarith

private theorem ThetaHonestRecursion.theta_word_energy_bound_of_A3_Gtime2 :
  ∀ {θ : ℝ → Vec (2 : ℕ) → ℝ} (w : List (Fin (2 : ℕ))),
  let G : ℝ := thetaWordSpaceTimeGradientEnergy θ w;
  ContDiffOn ℝ (↑(⊤ : ℕ∞) : WithTop ℕ∞) (Function.uncurry θ) (Set.Ici (0 : ℝ) ×ˢ Set.univ) → G =
    ∫ (t : ℝ) in (0 : ℝ)..(1 : ℝ), ∫ (x : Vec (2 : ℕ)) in unitCube, vecNormSq (spaceGrad
    (classicalWordDerivative w (θ t)) x)
    := by
  intro θ w G hθcont
  have hV : Continuous (thetaWordGradientExtension θ w) :=
    thetaWordGradientExtension_continuous hθcont
  have hnorm : Continuous (fun p : ℝ × Vec 2 =>
      Homogenization.vecNormSq (thetaWordGradientExtension θ w p)) := by
    change Continuous (fun p => ∑ j : Fin 2,
      thetaWordGradientExtension θ w p j * thetaWordGradientExtension θ w p j)
    apply continuous_finsetSum
    intro j hj
    exact ((continuous_apply j).comp hV).mul ((continuous_apply j).comp hV)
  have hcube := theta_timeCube_integral_eq_interval_integral hnorm
  have hgradExt := thetaWordGradientExtension_energy_eq (u := θ) (w := w)
  have htime :
      (∫ t in (0 : ℝ)..1,
        ∫ x in AVenhance.unitCube,
          Homogenization.vecNormSq (thetaWordGradientExtension θ w (t, x))) =
      ∫ t in (0 : ℝ)..1,
        ∫ x in AVenhance.unitCube,
          Homogenization.vecNormSq
            (AVenhance.spaceGrad (classicalWordDerivative w (θ t)) x) := by
    apply intervalIntegral.integral_congr_ae
    filter_upwards with t ht
    have ht' : t ∈ Set.Ioc (0 : ℝ) 1 := by
      simpa only [Set.uIoc_of_le (by norm_num : (0 : ℝ) ≤ 1)] using ht
    apply integral_congr_ae
    filter_upwards with x
    rw [thetaWordGradientExtension_eq_slice (u := θ) (w := w) t ht'.1 x]
  calc
    G = ∫ p in AVenhance.timeCube,
        Homogenization.vecNormSq (thetaWordGradientExtension θ w p) := hgradExt
    _ = ∫ t in (0 : ℝ)..1,
        ∫ x in AVenhance.unitCube,
          Homogenization.vecNormSq (thetaWordGradientExtension θ w (t, x)) := hcube
    _ = _ := htime

private theorem ThetaHonestRecursion.word_residual_integral_identity :
  ∀ {m : ℕ} (Φ : ℕ → ℝ → Vec (2 : ℕ) → ℝ) {θ : ℝ → Vec (2 : ℕ) → ℝ} (w : List (Fin (2 : ℕ))),
  let φ : ℝ → Vec (2 : ℕ) → ℝ := fun (t : ℝ) => Φ (m - (1 : ℕ)) t;
  ContDiffOn ℝ (↑(⊤ : ℕ∞) : WithTop ℕ∞) (Function.uncurry φ) (Set.Ici (0 : ℝ) ×ˢ Set.univ) →
    ContDiffOn ℝ (↑(⊤ : ℕ∞) : WithTop ℕ∞) (Function.uncurry θ) (Set.Ici (0 : ℝ) ×ˢ Set.univ) →
    (Continuous fun (p : ℝ × Vec (2 : ℕ)) => thetaWordExtension θ w p *
    thetaHonestResidualExtension φ θ w p) → ∀ T ∈ Set.Icc (0 : ℝ) (1 : ℝ), ∫ (t : ℝ) in (0 :
    ℝ)..T, ∫ (x : Vec (2 : ℕ)) in unitCube, classicalWordDerivative w (θ t) x *
    (classicalWordDerivative w (classicalTransport (streamVel (fun (s : ℝ) => Φ (m - (1 : ℕ)) s)
    t) (θ t)) x - vecDot (streamVel (fun (s : ℝ) => Φ (m - (1 : ℕ)) s) t x) (spaceGrad
    (classicalWordDerivative w (θ t)) x)) = ∫ (p : ℝ × Vec (2 : ℕ)) in Set.Ioo (0 : ℝ) T ×ˢ
    unitCube, thetaWordExtension θ w p * thetaHonestResidualExtension φ θ w p
    := by
  intro m Φ θ w φ hφcont hθcont hpaircont T hT
  have hspaceTime := theta_intervalCube_integral_eq_interval_integral hT hpaircont
  have hconvert :
      (∫ t in (0 : ℝ)..T,
        ∫ x in AVenhance.unitCube,
          thetaWordExtension θ w (t, x) *
            thetaHonestResidualExtension φ θ w (t, x)) =
      ∫ t in (0 : ℝ)..T,
        ∫ x in AVenhance.unitCube,
          classicalWordDerivative w (θ t) x *
            (classicalWordDerivative w
                (classicalTransport
                  (AVenhance.streamVel (fun s => Φ (m - 1) s) t) (θ t)) x -
              vecDot (AVenhance.streamVel (fun s => Φ (m - 1) s) t x)
                (AVenhance.spaceGrad
                  (classicalWordDerivative w (θ t)) x)) := by
    apply intervalIntegral.integral_congr_ae
    filter_upwards with t ht
    have ht' : t ∈ Set.Ioc (0 : ℝ) T := by
      simpa only [Set.uIoc_of_le hT.1] using ht
    apply integral_congr_ae
    filter_upwards with x
    rw [thetaWordExtension_eq_slice t ht'.1 x,
      thetaHonestResidualExtension_eq_commutator hφcont hθcont ht'.1 x]
    congr 1
  calc
    _ = ∫ t in (0 : ℝ)..T,
        ∫ x in AVenhance.unitCube,
          thetaWordExtension θ w (t, x) *
            thetaHonestResidualExtension φ θ w (t, x) := hconvert.symm
    _ = _ := hspaceTime.symm

/-- One ordered derivative's energy estimate after inserting the stream-regularity
barNorm conclusion.  The commutator is paired in space-time and Cauchy--
Schwarz is applied before Young's inequality, so the conclusion records the
larger honest convolution cost. -/
theorem ThetaHonestRecursion.theta_word_energy_bound_of_A3
    {β : ℝ} {m : ℕ} {κ R N : ℝ} (I : AVenhance.Ingredients β)
    (Φ : ℕ → ℝ → Vec 2 → ℝ) (hΦ : AVenhance.IsStreamSeq I Φ)
    (hm : 2 ≤ m)
    (hA3 : ∀ j : ℕ, 1 ≤ j → ∀ t : ℝ, ∀ n : ℕ, 2 ≤ n →
      AVenhance.barNorm n (2 ^ 8 * (AVenhance.epsilon β I.Λ j)⁻¹)
        (Φ j t) ≤
      ENNReal.ofReal (2 ^ 5 * AVenhance.a β I.Λ j *
        AVenhance.epsilon β I.Λ j ^ 2 *
        (((n : ℝ) + 2) ^ 2 / ((n : ℝ) + 1) ^ 3)))
    {θ₀ : Vec 2 → ℝ} {θ : ℝ → Vec 2 → ℝ}
    (hsol : AVenhance.IsClassicalSol
      (AVenhance.streamVel (fun t => Φ (m - 1) t)) κ
      (fun _ _ => 0) θ₀ θ)
    (hκ : 0 < κ)
    (hθ₀ : AVenhance.IsThetaAnalytic R θ₀)
    (hN : N = Real.sqrt (AVenhance.l2NormSq θ₀))
    (w : List (Fin 2)) :
    Real.sqrt (thetaWordSpatialEnergySup θ w) +
      Real.sqrt κ * Real.sqrt (thetaWordSpaceTimeGradientEnergy θ w) ≤
    8 * (N * ((w.length.factorial : ℝ) / R ^ w.length) +
      ∑ q ∈ Finset.range (w.length + 1),
        (((if q = 0 then 0 else w.length.choose q : ℕ) : ℝ) *
          (thetaHonestDriftCoefficient (m := m) I q *
            thetaEnergyLevel θ κ (w.length - q) / Real.sqrt κ))) := by
  let φ : ℝ → Vec 2 → ℝ := fun t => Φ (m - 1) t
  let S : ℝ := thetaWordSpatialEnergySup θ w
  let G : ℝ := thetaWordSpaceTimeGradientEnergy θ w
  let S₀ : ℝ := ∫ x in AVenhance.unitCube,
    (classicalWordDerivative w θ₀ x) ^ 2
  let B : ℝ := ∑ q ∈ Finset.range (w.length + 1),
    (((if q = 0 then 0 else w.length.choose q : ℕ) : ℝ) *
      (thetaHonestDriftCoefficient (m := m) I q *
        thetaEnergyLevel θ κ (w.length - q) / Real.sqrt κ))
  let X : ℝ := Real.sqrt S
  let Y : ℝ := Real.sqrt κ * Real.sqrt G
  let A : ℝ := Real.sqrt S₀
  have hφ : AVenhance.IsAdmissibleStream φ :=
    theta_prev_stream_admissible I Φ hΦ hm
  have hφcont : ContDiffOn ℝ (⊤ : ℕ∞) (Function.uncurry φ)
      (Set.Ici (0 : ℝ) ×ˢ Set.univ) := by
    have htop := hφ.1
    simpa [φ] using htop.contDiffOn.mono (by
      intro p hp
      exact Set.mem_univ p)
  have hθcont : ContDiffOn ℝ (⊤ : ℕ∞) (Function.uncurry θ)
      (Set.Ici (0 : ℝ) ×ˢ Set.univ) := hsol.1
  have hwordext : Continuous (thetaWordExtension θ w) :=
    thetaWordExtension_continuous hθcont
  have hrescont : Continuous (thetaHonestResidualExtension φ θ w) :=
    thetaHonestResidualExtension_continuous hφcont hθcont
  have hpaircont : Continuous (fun p : ℝ × Vec 2 =>
      thetaWordExtension θ w p * thetaHonestResidualExtension φ θ w p) :=
    hwordext.mul hrescont
  have hresidual_to_set (T : ℝ) (hT : T ∈ Set.Icc (0 : ℝ) 1) :
      (∫ t in (0 : ℝ)..T,
        ∫ x in AVenhance.unitCube,
          classicalWordDerivative w (θ t) x *
            (classicalWordDerivative w
                (classicalTransport
                  (AVenhance.streamVel (fun s => Φ (m - 1) s) t) (θ t)) x -
              vecDot (AVenhance.streamVel (fun s => Φ (m - 1) s) t x)
                (AVenhance.spaceGrad
                  (classicalWordDerivative w (θ t)) x))) =
      ∫ p in Set.Ioo (0 : ℝ) T ×ˢ AVenhance.unitCube,
        thetaWordExtension θ w p *
          thetaHonestResidualExtension φ θ w p := by
    exact @ThetaHonestRecursion.word_residual_integral_identity m Φ θ w hφcont hθcont hpaircont T hT
  have hS₀nonneg : 0 ≤ S₀ := by
    dsimp [S₀]
    exact integral_nonneg fun _ => sq_nonneg _
  have hSnonneg : 0 ≤ S := by
    have htime : (0 : ℝ) ∈ Set.Icc (0 : ℝ) 1 := by norm_num
    have hle := theta_word_spatial_energy_le_sup_of_classical hsol w htime
    have hE0 : 0 ≤ thetaWordSpatialEnergy θ w 0 := by
      exact integral_nonneg fun _ => sq_nonneg _
    dsimp [S]
    exact hE0.trans hle
  have hGnonneg : 0 ≤ G := by
    dsimp [G, thetaWordSpaceTimeGradientEnergy]
    exact integral_nonneg fun _ => Homogenization.vecNormSq_nonneg _
  have hBnonneg : 0 ≤ B := by
    unfold B
    apply Finset.sum_nonneg
    intro q hq
    apply mul_nonneg
    · positivity
    · apply div_nonneg
      · exact mul_nonneg (ThetaHonestRecursion.theta_driftCoefficient_nonneg I)
          (ThetaHonestRecursion.theta_energyLevel_nonneg _)
      · exact Real.sqrt_nonneg _
  have hNnonneg : 0 ≤ N := by rw [hN]; exact Real.sqrt_nonneg _
  have hAinit := theta_initial_word_l2_le_of_analytic hθ₀ hsol w
  have hAinit' : A ≤ N * ((w.length.factorial : ℝ) / R ^ w.length) := by
    simpa [A, S₀, hN] using hAinit
  have henergyT (T : ℝ) (hT : T ∈ Set.Icc (0 : ℝ) 1) :
      thetaWordSpatialEnergy θ w T ≤ S₀ + 4 * X * B := by
    exact @ThetaHonestRecursion.theta_word_energy_bound_of_A3_energyT1 β m κ I Φ hΦ hm hA3 θ₀ θ
        hsol hκ w hφ hresidual_to_set T hT
  have hSup : S ≤ S₀ + 4 * X * B := by
    apply thetaWordSpatialEnergySup_le θ w
    intro t ht
    exact henergyT t ht
  have hGtime : G =
      ∫ t in (0 : ℝ)..1,
        ∫ x in AVenhance.unitCube,
          Homogenization.vecNormSq
            (AVenhance.spaceGrad (classicalWordDerivative w (θ t)) x) := by
    exact @ThetaHonestRecursion.theta_word_energy_bound_of_A3_Gtime2 θ w hθcont
  have hgradBound : κ * G ≤ S₀ / 2 + 2 * X * B := by
    have hidentity :=
      (theta_classical_differentiated_energy_integrated hφ hsol (by norm_num : 0 ≤ (1 : ℝ)) w).1
    let P : ℝ := ∫ t in (0 : ℝ)..1,
      ∫ x in AVenhance.unitCube,
        classicalWordDerivative w (θ t) x *
          (classicalWordDerivative w
              (classicalTransport
                (AVenhance.streamVel (fun s => Φ (m - 1) s) t) (θ t)) x -
            vecDot (AVenhance.streamVel (fun s => Φ (m - 1) s) t x)
              (AVenhance.spaceGrad (classicalWordDerivative w (θ t)) x))
    have hpair := ThetaHonestRecursion.theta_residual_pairing_abs_le_of_A3
      (w := w) I Φ hΦ hm hA3 hsol hκ (by norm_num : (1 : ℝ) ∈ Set.Icc (0 : ℝ) 1)
    have hpair' : |P| ≤ 2 * X * B := by
      rw [← hresidual_to_set 1 (by norm_num : (1 : ℝ) ∈ Set.Icc (0 : ℝ) 1)] at hpair
      simpa [P, X, B, S] using hpair
    have henergy1nonneg : 0 ≤ thetaWordSpatialEnergy θ w 1 := by
      exact integral_nonneg fun _ => sq_nonneg _
    have hrewrite :
        thetaWordSpatialEnergy θ w 1 + 2 * κ * G = S₀ - 2 * P := by
      have hraw := hidentity
      rw [← hGtime] at hraw
      simpa [thetaWordSpatialEnergy, S₀, P, φ] using hraw
    have hpaircost : -2 * P ≤ 4 * X * B := by
      calc
        -2 * P ≤ 2 * |P| := by nlinarith [neg_le_abs P]
        _ ≤ 2 * (2 * X * B) :=
          mul_le_mul_of_nonneg_left hpair' (by norm_num)
        _ = 4 * X * B := by ring
    nlinarith
  have hYoungS : 4 * X * B ≤ S / 2 + 8 * B ^ 2 := by
    have hsq := sq_nonneg (X - 4 * B)
    have hXsq : X ^ 2 = S := by
      dsimp [X]
      exact Real.sq_sqrt hSnonneg
    nlinarith
  have hSbound : S ≤ 2 * S₀ + 16 * B ^ 2 := by
    have hSup' : S ≤ S₀ + S / 2 + 8 * B ^ 2 := by
      calc
        S ≤ S₀ + 4 * X * B := hSup
        _ ≤ S₀ + (S / 2 + 8 * B ^ 2) := by linarith [hYoungS]
        _ = S₀ + S / 2 + 8 * B ^ 2 := by ring
    nlinarith
  have hYoungG : 2 * X * B ≤ S / 4 + 4 * B ^ 2 := by
    have hsq := sq_nonneg (X - 4 * B)
    have hXsq : X ^ 2 = S := by
      dsimp [X]
      exact Real.sq_sqrt hSnonneg
    nlinarith
  have hGbound : κ * G ≤ S₀ + 8 * B ^ 2 := by
    have hbound := calc
        κ * G ≤ S₀ / 2 + 2 * X * B := hgradBound
        _ ≤ S₀ / 2 + (S / 4 + 4 * B ^ 2) := by linarith [hYoungG]
        _ ≤ S₀ / 2 + ((2 * S₀ + 16 * B ^ 2) / 4 + 4 * B ^ 2) := by
          gcongr
        _ = S₀ + 8 * B ^ 2 := by ring
    exact hbound
  have hXbound : X ≤ 4 * A + 4 * B := by
    by_contra hnot
    have hlt : 4 * A + 4 * B < X := by linarith
    have hA_nonneg : 0 ≤ A := Real.sqrt_nonneg _
    have hXnonneg : 0 ≤ X := by dsimp [X]; positivity
    have hXpos : 0 < X := by linarith [hBnonneg, hA_nonneg]
    have hprod : 4 * A * X < X * (X - 4 * B) := by
      have hlt' : 4 * A < X - 4 * B := by linarith
      have := mul_lt_mul_of_pos_left hlt' hXpos
      nlinarith
    have hprod2 : 16 * A ^ 2 ≤ 4 * A * X := by
      have hAX : 4 * A ≤ X := by linarith
      have := mul_le_mul_of_nonneg_left hAX (by positivity : 0 ≤ 4 * A)
      nlinarith
    have hXsq : X ^ 2 = S := by
      dsimp [X]
      exact Real.sq_sqrt hSnonneg
    have hA2 : A ^ 2 = S₀ := by
      dsimp [A]
      exact Real.sq_sqrt hS₀nonneg
    nlinarith
  have hYsq : Y ^ 2 = κ * G := by
    dsimp [Y]
    rw [mul_pow, Real.sq_sqrt hκ.le, Real.sq_sqrt hGnonneg]
  have hYbound : Y ≤ A + 3 * B := by
    by_contra hnot
    have hlt : A + 3 * B < Y := by linarith
    have hnonneg : 0 ≤ A + 3 * B := by positivity
    have hsq : (A + 3 * B) ^ 2 < Y ^ 2 := by
      have hpos : 0 < Y + (A + 3 * B) := by linarith
      have := mul_pos (by linarith : 0 < Y - (A + 3 * B)) hpos
      nlinarith
    have hA2 : A ^ 2 = S₀ := by
      dsimp [A]
      exact Real.sq_sqrt hS₀nonneg
    have hYboundSq : Y ^ 2 ≤ A ^ 2 + 8 * B ^ 2 := by
      rw [hYsq, hA2]
      exact hGbound
    nlinarith [sq_nonneg B]
  have hlevelBound : X + Y ≤ 8 * (A + B) := by
    have hA_nonneg : 0 ≤ A := Real.sqrt_nonneg _
    have hsum := add_le_add hXbound hYbound
    nlinarith
  have hfinal := calc
      X + Y ≤ 8 * (A + B) := hlevelBound
      _ ≤ 8 * (N * ((w.length.factorial : ℝ) / R ^ w.length) + B) := by
        exact mul_le_mul_of_nonneg_left (add_le_add hAinit' le_rfl) (by norm_num)
  simpa [X, Y, A, B, S, G] using hfinal

theorem theta_order_zero_energy_bound
    {κ N : ℝ} {φ : ℝ → Vec 2 → ℝ}
    {θ₀ : Vec 2 → ℝ} {θ : ℝ → Vec 2 → ℝ}
    (hφ : AVenhance.IsAdmissibleStream φ)
    (hsol : AVenhance.IsClassicalSol
      (AVenhance.streamVel φ) κ (fun _ _ => 0) θ₀ θ)
    (hκ : 0 < κ) (hN : N = Real.sqrt (AVenhance.l2NormSq θ₀)) :
    thetaEnergyLevel θ κ 0 ≤ 2 * N := by
  let w : List (Fin 2) := []
  let S₀ : ℝ := AVenhance.l2NormSq θ₀
  have hS₀nonneg : 0 ≤ S₀ := by
    dsimp [S₀, AVenhance.l2NormSq]
    exact integral_nonneg fun _ => sq_nonneg _
  have henergy (T : ℝ) (hT : 0 ≤ T) :
      thetaWordSpatialEnergy θ w T + 2 * κ *
        (∫ t in (0 : ℝ)..T,
          ∫ x in AVenhance.unitCube,
            Homogenization.vecNormSq
              (AVenhance.spaceGrad (θ t) x)) = S₀ := by
    have h :=
      (theta_classical_differentiated_energy_integrated hφ hsol hT w).1
    simpa [w, S₀, thetaWordSpatialEnergy, classicalWordDerivative,
      Classical.classicalWordDerivative,
      classicalTransport,
      Classical.classicalTransport, Homogenization.vecDot, Fin.sum_univ_two,
      AVenhance.l2NormSq] using h
  have hE_nonneg (T : ℝ) : 0 ≤ thetaWordSpatialEnergy θ w T := by
    exact integral_nonneg fun _ => sq_nonneg _
  have htimeBound (T : ℝ) (hT : T ∈ Set.Icc (0 : ℝ) 1) :
      thetaWordSpatialEnergy θ w T ≤ S₀ := by
    have hD : 0 ≤ ∫ t in (0 : ℝ)..T,
        ∫ x in AVenhance.unitCube,
          Homogenization.vecNormSq
            (AVenhance.spaceGrad (θ t) x) := by
      apply intervalIntegral.integral_nonneg hT.1
      intro t ht
      exact integral_nonneg fun _ => Homogenization.vecNormSq_nonneg _
    have h := henergy T hT.1
    nlinarith [hκ]
  have hSup : thetaWordSpatialEnergySup θ w ≤ S₀ :=
    thetaWordSpatialEnergySup_le θ w htimeBound
  have hGtime : thetaWordSpaceTimeGradientEnergy θ w =
      ∫ t in (0 : ℝ)..1,
        ∫ x in AVenhance.unitCube,
          Homogenization.vecNormSq
            (AVenhance.spaceGrad (classicalWordDerivative w (θ t)) x) := by
    have hθ : ContDiffOn ℝ (⊤ : ℕ∞) (Function.uncurry θ)
        (Set.Ici (0 : ℝ) ×ˢ Set.univ) := hsol.1
    have hV : Continuous (thetaWordGradientExtension θ w) :=
      thetaWordGradientExtension_continuous hθ
    have hnorm : Continuous (fun p : ℝ × Vec 2 =>
        Homogenization.vecNormSq (thetaWordGradientExtension θ w p)) := by
      change Continuous (fun p => ∑ j : Fin 2,
        thetaWordGradientExtension θ w p j * thetaWordGradientExtension θ w p j)
      apply continuous_finsetSum
      intro j hj
      exact ((continuous_apply j).comp hV).mul ((continuous_apply j).comp hV)
    have hgradExt := thetaWordGradientExtension_energy_eq (u := θ) (w := w)
    have hcube := theta_timeCube_integral_eq_interval_integral hnorm
    have htime :
        (∫ t in (0 : ℝ)..1,
          ∫ x in AVenhance.unitCube,
            Homogenization.vecNormSq (thetaWordGradientExtension θ w (t, x))) =
        ∫ t in (0 : ℝ)..1,
          ∫ x in AVenhance.unitCube,
            Homogenization.vecNormSq
              (AVenhance.spaceGrad (classicalWordDerivative w (θ t)) x) := by
      apply intervalIntegral.integral_congr_ae
      filter_upwards with t ht
      have ht' : t ∈ Set.Ioc (0 : ℝ) 1 := by
        simpa only [Set.uIoc_of_le (by norm_num : (0 : ℝ) ≤ 1)] using ht
      apply integral_congr_ae
      filter_upwards with x
      rw [thetaWordGradientExtension_eq_slice (u := θ) (w := w) t ht'.1 x]
    calc
      thetaWordSpaceTimeGradientEnergy θ w =
          ∫ p in AVenhance.timeCube,
            Homogenization.vecNormSq (thetaWordGradientExtension θ w p) := hgradExt
      _ = ∫ t in (0 : ℝ)..1,
          ∫ x in AVenhance.unitCube,
            Homogenization.vecNormSq (thetaWordGradientExtension θ w (t, x)) := hcube
      _ = _ := htime
  have hD1 : 0 ≤ ∫ t in (0 : ℝ)..1,
      ∫ x in AVenhance.unitCube,
        Homogenization.vecNormSq (AVenhance.spaceGrad (θ t) x) := by
    apply intervalIntegral.integral_nonneg (by norm_num)
    intro t ht
    exact integral_nonneg fun _ => Homogenization.vecNormSq_nonneg _
  have hGtime' : thetaWordSpaceTimeGradientEnergy θ w =
      ∫ t in (0 : ℝ)..1,
        ∫ x in AVenhance.unitCube,
          Homogenization.vecNormSq (AVenhance.spaceGrad (θ t) x) := by
    simpa [w, classicalWordDerivative,
      Classical.classicalWordDerivative] using hGtime
  have hE1 : 0 ≤ thetaWordSpatialEnergy θ w 1 := hE_nonneg 1
  have hGbound : κ * thetaWordSpaceTimeGradientEnergy θ w ≤ S₀ / 2 := by
    have hId := henergy 1 (by norm_num)
    rw [← hGtime'] at hId
    dsimp [w] at hId
    nlinarith [hD1, hE1]
  have hNnonneg : 0 ≤ N := by rw [hN]; exact Real.sqrt_nonneg _
  have hrootS : Real.sqrt (thetaWordSpatialEnergySup θ w) ≤ N := by
    rw [hN]
    exact Real.sqrt_le_sqrt (by simpa [S₀] using hSup)
  have hrootG : Real.sqrt κ *
      Real.sqrt (thetaWordSpaceTimeGradientEnergy θ w) ≤ N := by
    rw [← Real.sqrt_mul hκ.le]
    have hkg : κ * thetaWordSpaceTimeGradientEnergy θ w ≤ S₀ := by
      nlinarith [hGbound, hS₀nonneg]
    calc
      Real.sqrt (κ * thetaWordSpaceTimeGradientEnergy θ w) ≤ Real.sqrt S₀ :=
        Real.sqrt_le_sqrt hkg
      _ = N := by simpa [S₀] using hN.symm
  have hlevelEq : thetaEnergyLevel θ κ 0 =
      Real.sqrt (thetaWordSpatialEnergySup θ w) +
        Real.sqrt κ * Real.sqrt (thetaWordSpaceTimeGradientEnergy θ w) := by
    simp [thetaEnergyLevel, thetaCoordinateWord, w]
  rw [hlevelEq]
  linarith

end AVenhance.Infra.Section4

end
