/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.LeftToShow.BracketFF
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.ErgodicParams
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Ergodic.FlowAverages
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Ergodic.FourierDecay
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section3.CorrectorBounds

/-! # `e.ergodic.space.kill` at a fixed time

Source: `enhance.tex` 8510–8640 (the App C flow lemma `l.flow.averages` with the time variable
fixed).  We write `FᵗF = 1 + ∑_{k∈S} g_k ∘ X_k⁻¹` with `g_k = ξ_k(Gᵀ+G) + ξ_k² GᵀG`
(`G = ∇Χ_{m,k}`), so that
`∫|F∇T|² - ∫∇T·⟨FᵗF⟩∇T = ∑_k ∑_{ij} [⟨f_ij · (g_k)_ij ∘ X_k⁻¹⟩ - ⟨f_ij⟩⟨(g_k)_ij⟩]`
with `f_ij = ∂_iT ∂_jT`, and each bracket is bounded by the flow lemma. -/

@[expose] public section

noncomputable section

open MeasureTheory Homogenization
open scoped ContDiff

namespace AVenhance.Infra.Section5.LeftToShow

open AVenhance AVenhance.Infra.Section3

variable {β : ℝ} (I : Ingredients β) {Φ : ℕ → ℝ → Vec 2 → ℝ}

/-! ## Entries of `∇Χ_{m,k}`: sup bound and fast periodicity -/

theorem SpaceErgodic.epsilon_pos' (m : ℕ) : 0 < epsilon β I.Λ m :=
  Infra.Cutoff.epsilon_pos I.one_lt_beta I.beta_lt I.two_pow_seven_le

theorem SpaceErgodic.a_nonneg' (m : ℕ) : 0 ≤ a β I.Λ m :=
  (Infra.Cutoff.a_pos I.one_lt_beta I.beta_lt I.two_pow_seven_le (m := m)).le

/-- The amplitude `4π² a_m c_{m,k}(t)` of an entry of `∇Χ_{m,k}` is at most `a_m ε_m²/κ`. -/
theorem SpaceErgodic.amplitude_abs_le {m : ℕ} (hm : 1 ≤ m) {κ : ℝ} (hκ : 0 < κ) (k : ℤ) (t : ℝ) :
    4 * Real.pi ^ 2 * a β I.Λ m * I.corrTime κ m k t ≤ a β I.Λ m * epsilon β I.Λ m ^ 2 / κ ∧
      0 ≤ 4 * Real.pi ^ 2 * a β I.Λ m * I.corrTime κ m k t := by
  have hε := SpaceErgodic.epsilon_pos' I m
  have ha := SpaceErgodic.a_nonneg' I m
  obtain ⟨h0, h1⟩ := corrTime_nonneg_le_inv I hm κ hκ k t
  have hpi : 0 < Real.pi := Real.pi_pos
  have hP : 0 < 4 * Real.pi ^ 2 * a β I.Λ m + 1 := by positivity
  refine ⟨?_, by positivity⟩
  have h2 : 4 * Real.pi ^ 2 * a β I.Λ m * I.corrTime κ m k t ≤
      4 * Real.pi ^ 2 * a β I.Λ m * (4 * Real.pi ^ 2 * κ / epsilon β I.Λ m ^ 2)⁻¹ :=
    mul_le_mul_of_nonneg_left h1 (by positivity)
  refine h2.trans (le_of_eq ?_)
  field_simp

/-- Every entry of `∇Χ_{m,k}` is `c sin(2π y_r/ε_m)` with `|c| ≤ a_m ε_m²/κ`. -/
theorem gradMatrix_chiMK_entry_form_bdd {m : ℕ} (hm : 1 ≤ m) {κ : ℝ} (hκ : 0 < κ) (k : ℤ)
    (t : ℝ) (i j : Fin 2) :
    ∃ (c : ℝ) (r : Fin 2), |c| ≤ a β I.Λ m * epsilon β I.Λ m ^ 2 / κ ∧
      ∀ y : Vec 2, gradMatrix (I.chiMK κ m k t) y i j =
        c * Real.sin (2 * Real.pi * y r / epsilon β I.Λ m) := by
  have hε := epsilon_ne_zero I m
  have hε' := SpaceErgodic.epsilon_pos' I m
  have ha := SpaceErgodic.a_nonneg' I m
  obtain ⟨hA, hA0⟩ := SpaceErgodic.amplitude_abs_le I hm hκ k t
  have hB : 0 ≤ a β I.Λ m * epsilon β I.Λ m ^ 2 / κ := by positivity
  have hAabs : |4 * Real.pi ^ 2 * a β I.Λ m * I.corrTime κ m k t| ≤
      a β I.Λ m * epsilon β I.Λ m ^ 2 / κ := by
    rw [abs_of_nonneg hA0]; exact hA
  have hk4 : k % 4 = 1 ∨ k % 4 = 3 ∨ (k % 4 ≠ 1 ∧ k % 4 ≠ 3) := by omega
  have hentry : ∀ y : Vec 2, gradMatrix (I.chiMK κ m k t) y i j =
      spaceGrad (fun z => I.chiMK κ m k t z j) y i := fun y => by simp [gradMatrix]
  have hzero : ∀ c : Fin 2, (∀ z : Vec 2, I.chiMK κ m k t z c = 0) → ∀ y : Vec 2,
      spaceGrad (fun z => I.chiMK κ m k t z c) y i = 0 := by
    intro c h y
    have : (fun z : Vec 2 => I.chiMK κ m k t z c) = fun _ => 0 := funext h
    rw [this]
    simp [spaceGrad]
  obtain rfl | rfl : j = 0 ∨ j = 1 := by fin_cases j <;> simp
  · rcases hk4 with h1 | h3 | ⟨h1, h3⟩
    · refine ⟨0, 0, by simpa using hB, fun y => ?_⟩
      rw [hentry, hzero 0 (fun z => by simp [Ingredients.chiMK, uShear, h1])]
      simp
    · by_cases hi : i = 1
      · refine ⟨-(4 * Real.pi ^ 2 * a β I.Λ m * I.corrTime κ m k t), 1, by
          rwa [abs_neg], fun y => ?_⟩
        rw [hentry, chiMK_spaceGrad_three_all I κ k t y i h3 hε]
        simp [hi]
      · refine ⟨0, 0, by simpa using hB, fun y => ?_⟩
        rw [hentry, chiMK_spaceGrad_three_all I κ k t y i h3 hε]
        simp [hi]
    · refine ⟨0, 0, by simpa using hB, fun y => ?_⟩
      rw [hentry, hzero 0 (fun z => by simp [Ingredients.chiMK, uShear, h1, h3])]
      simp
  · rcases hk4 with h1 | h3 | ⟨h1, h3⟩
    · by_cases hi : i = 0
      · refine ⟨4 * Real.pi ^ 2 * a β I.Λ m * I.corrTime κ m k t, 0, hAabs, fun y => ?_⟩
        rw [hentry, chiMK_spaceGrad_one_all I κ k t y i h1 hε]
        simp [hi]
      · refine ⟨0, 0, by simpa using hB, fun y => ?_⟩
        rw [hentry, chiMK_spaceGrad_one_all I κ k t y i h1 hε]
        simp [hi]
    · refine ⟨0, 0, by simpa using hB, fun y => ?_⟩
      rw [hentry, hzero 1 (fun z => by simp [Ingredients.chiMK, uShear, h3])]
      simp
    · refine ⟨0, 0, by simpa using hB, fun y => ?_⟩
      rw [hentry, hzero 1 (fun z => by simp [Ingredients.chiMK, uShear, h1, h3])]
      simp

/-- |∂_iχ_{m,k,j}| ≤ a_m ε_m² / κ (e.corrm, gradient part). -/
theorem gradMatrix_chiMK_entry_abs_le {m : ℕ} (hm : 1 ≤ m) {κ : ℝ} (hκ : 0 < κ) (k : ℤ)
    (t : ℝ) (y : Vec 2) (i j : Fin 2) :
    |gradMatrix (I.chiMK κ m k t) y i j| ≤ a β I.Λ m * epsilon β I.Λ m ^ 2 / κ := by
  obtain ⟨c, r, hc, h⟩ := gradMatrix_chiMK_entry_form_bdd I hm hκ k t i j
  rw [h, abs_mul]
  calc |c| * |Real.sin (2 * Real.pi * y r / epsilon β I.Λ m)| ≤ |c| * 1 :=
        mul_le_mul_of_nonneg_left (Real.abs_sin_le_one _) (abs_nonneg c)
    _ ≤ _ := by rw [mul_one]; exact hc

/-- The matrix-valued corrector gradient is invariant under `ε_m`-lattice shifts. -/
theorem gradMatrix_chiMK_shift {m : ℕ} (_hm : 1 ≤ m) (κ : ℝ) (k : ℤ) (t : ℝ) (y : Vec 2)
    (n : Fin 2 → ℤ) :
    gradMatrix (I.chiMK κ m k t) (y + fun i => (n i : ℝ) / (ergodicFrequency β I.Λ m : ℝ)) =
      gradMatrix (I.chiMK κ m k t) y := by
  have hε := epsilon_ne_zero I m
  have hN : (ergodicFrequency β I.Λ m : ℝ) = (epsilon β I.Λ m)⁻¹ := ergodicFrequency_cast β _ m
  funext i j
  obtain ⟨c, r, h⟩ := gradMatrix_chiMK_entry_form I m κ k t i j
  rw [h, h]
  congr 1
  have : 2 * Real.pi * (y + fun i => (n i : ℝ) / (ergodicFrequency β I.Λ m : ℝ)) r /
      epsilon β I.Λ m = 2 * Real.pi * y r / epsilon β I.Λ m + (n r : ℤ) * (2 * Real.pi) := by
    simp only [Pi.add_apply, hN]
    field_simp
  rw [this, Real.sin_add_int_mul_two_pi]

/-- The corrector gradients are ε_m-periodic: fast periodic at frequency ε_m⁻¹. -/
theorem gradMatrix_chiMK_isFastPeriodic {m : ℕ} (hm : 1 ≤ m) (κ : ℝ) (k : ℤ) (t : ℝ)
    (i j : Fin 2) :
    Infra.Ergodic.IsFastPeriodic (ergodicFrequency β I.Λ m)
      (fun y => gradMatrix (I.chiMK κ m k t) y i j) := by
  intro y n
  exact congrFun (congrFun (gradMatrix_chiMK_shift I hm κ k t y n) i) j

/-! ## The Gram kernel `g_k` -/

/-- `g_k := ξ (Gᵀ + G) + ξ² GᵀG`, the `k`-th summand of `FᵗF - 1` before composing with `X_k⁻¹`. -/
def gramKernel (ξ : ℝ) (G : Matrix (Fin 2) (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  ξ • (G.transpose + G) + ξ ^ 2 • (G.transpose * G)

theorem gramKernel_entry_abs_le {ξ B : ℝ} (hξ0 : 0 ≤ ξ) (hξ1 : ξ ≤ 1)
    {G : Matrix (Fin 2) (Fin 2) ℝ} (hG : ∀ i j, |G i j| ≤ B) (i j : Fin 2) :
    |gramKernel ξ G i j| ≤ ξ * (2 * B + 2 * B ^ 2) := by
  have hB : 0 ≤ B := (abs_nonneg _).trans (hG 0 0)
  have hentry : gramKernel ξ G i j =
      ξ * (G j i + G i j) + ξ ^ 2 * (G 0 i * G 0 j + G 1 i * G 1 j) := by
    simp [gramKernel, Matrix.mul_apply, Fin.sum_univ_two]
    ring
  have h1 : |ξ * (G j i + G i j)| ≤ ξ * (2 * B) := by
    rw [abs_mul, abs_of_nonneg hξ0]
    refine mul_le_mul_of_nonneg_left ((abs_add_le _ _).trans ?_) hξ0
    linarith [hG j i, hG i j]
  have hprod : ∀ a b : Fin 2, |G a i * G a j| ≤ B ^ 2 := fun a b => by
    rw [abs_mul, pow_two]
    exact mul_le_mul (hG a i) (hG a j) (abs_nonneg _) hB
  have h2 : |ξ ^ 2 * (G 0 i * G 0 j + G 1 i * G 1 j)| ≤ ξ * (2 * B ^ 2) := by
    rw [abs_mul, abs_of_nonneg (sq_nonneg ξ)]
    have hs : |G 0 i * G 0 j + G 1 i * G 1 j| ≤ 2 * B ^ 2 :=
      (abs_add_le _ _).trans (by linarith [hprod 0 0, hprod 1 0])
    have hξ2 : ξ ^ 2 ≤ ξ := by nlinarith
    calc ξ ^ 2 * |G 0 i * G 0 j + G 1 i * G 1 j| ≤ ξ ^ 2 * (2 * B ^ 2) :=
          mul_le_mul_of_nonneg_left hs (sq_nonneg ξ)
      _ ≤ ξ * (2 * B ^ 2) := mul_le_mul_of_nonneg_right hξ2 (by positivity)
  rw [hentry]
  calc _ ≤ |ξ * (G j i + G i j)| + |ξ ^ 2 * (G 0 i * G 0 j + G 1 i * G 1 j)| := abs_add_le _ _
    _ ≤ ξ * (2 * B) + ξ * (2 * B ^ 2) := add_le_add h1 h2
    _ = _ := by ring

theorem continuous_gramKernel_grad (κm : ℝ) {m : ℕ} (t : ℝ) {k : ℤ} (hk : Odd k) (ξ : ℝ) :
    Continuous fun y => gramKernel ξ (gradMatrix (I.chiMK κm m k t) y) := by
  have hGc : Continuous fun y => gradMatrix (I.chiMK κm m k t) y :=
    (continuous_gradMatrix_chiMK I κm m hk).comp (continuous_const.prodMk continuous_id)
  unfold gramKernel
  exact ((continuous_const : Continuous fun _ : Vec 2 => ξ).smul
      (hGc.matrix_transpose.add hGc)).add
    ((continuous_const : Continuous fun _ : Vec 2 => ξ ^ 2).smul
      (hGc.matrix_transpose.matrix_mul hGc))

/-- A pointwise bound by `c` gives the same bound for the cell average. -/
theorem cellAverage_le_of_forall_le {g : Vec 2 → ℝ} {c : ℝ} (h : ∀ x, g x ≤ c)
    (hg : Continuous g) : Infra.Ergodic.cellAverage g ≤ c := by
  rw [← spaceAvg_eq_cellAverage]
  have hvol : volume unitCube = 1 := by
    unfold unitCube
    rw [volume_pi, Measure.pi_pi]
    simp [Real.volume_Ioo]
  have hint : IntegrableOn g unitCube := integrableOn_unitCube_of_continuous hg
  have hint' : IntegrableOn (fun _ : Vec 2 => c) unitCube := integrableOn_const (by simp [hvol])
  unfold spaceAvg
  calc ∫ x in unitCube, g x ≤ ∫ x in unitCube, c := setIntegral_mono hint hint' h
    _ = c := by simp [Measure.real, hvol]

/-! ## Abstract averaging algebra -/

theorem volume_unitCube_eq_one : volume unitCube = 1 := by
  unfold unitCube
  rw [volume_pi, Measure.pi_pi]
  simp [Real.volume_Ioo]

theorem spaceAvg_const_eq (c : ℝ) : spaceAvg (fun _ : Vec 2 => c) = c := by
  unfold spaceAvg
  rw [setIntegral_const]
  simp [Measure.real, volume_unitCube_eq_one]

/-- The splitting of a product average: if `h = δ + ∑_k g_k ∘ Y_k` with `⟨g_k ∘ Y_k⟩ = ⟨g_k⟩`,
then `⟨f h⟩ - ⟨h⟩⟨f⟩ = ∑_k (⟨f · g_k ∘ Y_k⟩ - ⟨f⟩⟨g_k⟩)`. -/
theorem spaceAvg_mul_sub_decomp {ι : Type*} (S : Finset ι) {f h : Vec 2 → ℝ}
    {g : ι → Vec 2 → ℝ} {Y : ι → Vec 2 → Vec 2} {δ : ℝ} (hf : Continuous f)
    (hg : ∀ k, Continuous (g k)) (hY : ∀ k, Continuous (Y k))
    (hh : ∀ x, h x = δ + ∑ k ∈ S, g k (Y k x))
    (havg : ∀ k ∈ S, spaceAvg (fun x => g k (Y k x)) = spaceAvg (g k)) :
    spaceAvg (fun x => f x * h x) - spaceAvg h * spaceAvg f =
      ∑ k ∈ S, (spaceAvg (fun x => f x * g k (Y k x)) - spaceAvg f * spaceAvg (g k)) := by
  have hgY : ∀ k, Continuous fun x => g k (Y k x) := fun k => (hg k).comp (hY k)
  have hfgY : ∀ k, Continuous fun x => f x * g k (Y k x) := fun k => hf.mul (hgY k)
  have hsum : Continuous fun x => ∑ k ∈ S, g k (Y k x) := continuous_finsetSum S fun k _ => hgY k
  have hsum' : Continuous fun x => ∑ k ∈ S, f x * g k (Y k x) :=
    continuous_finsetSum S fun k _ => hfgY k
  have h1 : spaceAvg h = δ + ∑ k ∈ S, spaceAvg (g k) := by
    have hfun : h = fun x => δ + ∑ k ∈ S, g k (Y k x) := funext hh
    rw [hfun]
    unfold spaceAvg
    rw [integral_add (integrableOn_unitCube_of_continuous continuous_const)
      (integrableOn_unitCube_of_continuous hsum),
      integral_finsetSum S fun k _ => integrableOn_unitCube_of_continuous (hgY k)]
    have := spaceAvg_const_eq δ
    unfold spaceAvg at this
    rw [this]
    congr 1
    exact Finset.sum_congr rfl fun k hk => havg k hk
  have h2 : spaceAvg (fun x => f x * h x) =
      δ * spaceAvg f + ∑ k ∈ S, spaceAvg (fun x => f x * g k (Y k x)) := by
    have hfun : (fun x => f x * h x) = fun x => δ * f x + ∑ k ∈ S, f x * g k (Y k x) := by
      funext x
      rw [hh x, mul_add, Finset.mul_sum]
      ring
    rw [hfun]
    unfold spaceAvg
    rw [integral_add ((integrableOn_unitCube_of_continuous hf).const_mul δ)
      (integrableOn_unitCube_of_continuous hsum'), integral_const_mul,
      integral_finsetSum S fun k _ => integrableOn_unitCube_of_continuous (hfgY k)]
  rw [h1, h2, Finset.sum_sub_distrib, ← Finset.mul_sum]
  ring

theorem vecDot_mulVec_eq_sum (u : Vec 2) (A : Matrix (Fin 2) (Fin 2) ℝ) :
    vecDot u (A.mulVec u) = ∑ i, ∑ j, (u i * u j) * A i j := by
  simp only [vecDot, Matrix.mulVec, dotProduct, Fin.sum_univ_two]
  ring

/-- `∫ u·(H u)` as a sum of averages of `u_i u_j H_ij`. -/
theorem integral_quad_eq_sum {u : Vec 2 → Vec 2} {H : Vec 2 → Matrix (Fin 2) (Fin 2) ℝ}
    (hu : ∀ i, Continuous fun x => u x i) (hH : ∀ i j, Continuous fun x => H x i j) :
    ∫ x in unitCube, vecDot (u x) ((H x).mulVec (u x)) =
      ∑ i, ∑ j, spaceAvg (fun x => (u x i * u x j) * H x i j) := by
  have hint : ∀ i j, IntegrableOn (fun x => (u x i * u x j) * H x i j) unitCube := fun i j =>
    integrableOn_unitCube_of_continuous (((hu i).mul (hu j)).mul (hH i j))
  simp_rw [vecDot_mulVec_eq_sum]
  rw [integral_finsetSum _ fun i _ => integrable_finsetSum _ fun j _ => hint i j]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [integral_finsetSum _ fun j _ => hint i j]
  rfl

/-- The quadratic form of a spatially averaged matrix field. -/
theorem integral_quad_spaceAvgMat {u : Vec 2 → Vec 2} {H : Vec 2 → Matrix (Fin 2) (Fin 2) ℝ}
    (hu : ∀ i, Continuous fun x => u x i) :
    ∫ x in unitCube, vecDot (u x) ((spaceAvgMat H).mulVec (u x)) =
      ∑ i, ∑ j, spaceAvg (fun x => u x i * u x j) * spaceAvg (fun x => H x i j) := by
  have h := integral_quad_eq_sum (u := u) (H := fun _ => spaceAvgMat H) hu
    (fun i j => continuous_const)
  rw [h]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  unfold spaceAvg
  rw [integral_mul_const]
  rfl

/-! ## The gradient of the slice `T(t)` -/

theorem contDiff_spaceGrad_coord {f : Vec 2 → ℝ} (hf : ContDiff ℝ (⊤ : ℕ∞) f) (i : Fin 2) :
    ContDiff ℝ ∞ (fun x => spaceGrad f x i) := by
  change ContDiff ℝ ∞ (fun x => fderiv ℝ f x (basisVec i))
  exact (hf.fderiv_right (m := ∞) (by simp)).clm_apply contDiff_const

theorem isZPeriodic_spaceGrad_coord {f : Vec 2 → ℝ} (hf : IsZ2Periodic f) (i : Fin 2) :
    Infra.Ergodic.IsZPeriodic (fun x => spaceGrad f x i) := by
  intro x n
  have hshift : (fun y : Vec 2 => f (y + fun i => (n i : ℝ))) = f := by
    funext y
    exact hf n y
  have h := fderiv_comp_add_right (𝕜 := ℝ) (f := f) (fun i => (n i : ℝ)) (x := x)
  rw [hshift] at h
  change fderiv ℝ f (x + fun i => (n i : ℝ)) (basisVec i) = fderiv ℝ f x (basisVec i)
  rw [← h]

/-! ## One flow-lemma term -/

/-- The L¹ flow lemma applied to one `(k, i, j)`. -/
theorem space_kill_term_bound (hΦ : IsStreamSeq I Φ) {m : ℕ} (hm : 1 ≤ m) {κm : ℝ}
    (hκm : 0 < κm) {T : ℝ → Vec 2 → ℝ} {t : ℝ}
    (hTs : ContDiff ℝ (⊤ : ℕ∞) (T t)) (hTp : IsZ2Periodic (T t)) {Cf r : ℝ} (hCf : 0 ≤ Cf)
    (hr : 0 < r)
    (hAn : ∀ k : ℤ, Odd k → I.xiMK m k t ≠ 0 → ∀ i j : Fin 2,
      Infra.Ergodic.HasCoordinateAnalyticL1Bounds
        (fun y => ((spaceGrad (T t) (I.xFlow hΦ m (lIdx β I.Λ m k) t y) i *
          spaceGrad (T t) (I.xFlow hΦ m (lIdx β I.Λ m k) t y) j : ℝ) : ℂ)) Cf r)
    (hrN : 1 ≤ r * (ergodicFrequency β I.Λ m : ℝ)) (k : {k : ℤ // Odd k}) (i j : Fin 2) :
    |spaceAvg (fun x => (spaceGrad (T t) x i * spaceGrad (T t) x j) *
        gramKernel (I.xiMK m k.1 t) (gradMatrix (I.chiMK κm m k.1 t)
          (I.xFlowInv hΦ m (lIdx β I.Λ m k.1) t x)) i j) -
      spaceAvg (fun x => spaceGrad (T t) x i * spaceGrad (T t) x j) *
        spaceAvg (fun y => gramKernel (I.xiMK m k.1 t)
          (gradMatrix (I.chiMK κm m k.1 t) y) i j)| ≤
      I.xiMK m k.1 t *
        (512 * Cf * (2 * (a β I.Λ m * epsilon β I.Λ m ^ 2 / κm) +
          2 * (a β I.Λ m * epsilon β I.Λ m ^ 2 / κm) ^ 2) *
        (∑' k : Fin 2 → ℤ, Real.exp (-(1 / 1024 : ℝ) * ‖k‖)) *
        Real.exp (-(r * (ergodicFrequency β I.Λ m : ℝ)) / 1024)) := by
  by_cases hξz : I.xiMK m k.1 t = 0
  · simp [hξz, gramKernel, spaceAvg]
  set N := ergodicFrequency β I.Λ m with hNdef
  set B := a β I.Λ m * epsilon β I.Λ m ^ 2 / κm with hB
  have hN : 0 < N := by
    by_contra h0
    have : N = 0 := Nat.eq_zero_of_not_pos h0
    rw [this] at hrN
    exact absurd hrN (by norm_num)
  set ξ := I.xiMK m k.1 t with hξ
  obtain ⟨hξ0, hξ1⟩ := xiMK_mem_Icc I hm k.1 t
  set X := xFlowDiffeo I hΦ m (lIdx β I.Λ m k.1) t with hX
  let g : Vec 2 → ℝ := fun y => gramKernel ξ (gradMatrix (I.chiMK κm m k.1 t) y) i j
  have hM := continuous_gramKernel_grad I κm (m := m) t k.2 ξ
  have hgc : Continuous g := hM.matrix_elem i j
  have hfast : Infra.Ergodic.IsFastPeriodic N g := by
    intro y n
    have := gradMatrix_chiMK_shift I hm κm k.1 t y n
    simp only [g]
    rw [this]
  have hgb : ∀ y, |g y| ≤ ξ * (2 * B + 2 * B ^ 2) := fun y =>
    gramKernel_entry_abs_le hξ0 hξ1 (fun a b => gradMatrix_chiMK_entry_abs_le I hm hκm k.1 t y a b)
      i j
  have hfc : ContDiff ℝ ∞ (fun y => spaceGrad (T t) y i * spaceGrad (T t) y j) :=
    (contDiff_spaceGrad_coord hTs i).mul (contDiff_spaceGrad_coord hTs j)
  have hfper : Infra.Ergodic.IsZPeriodic (fun y => spaceGrad (T t) y i * spaceGrad (T t) y j) :=
    fun y n => by
      change spaceGrad (T t) (y + fun i => (n i : ℝ)) i * spaceGrad (T t) (y + fun i => (n i : ℝ))
          j =
        spaceGrad (T t) y i * spaceGrad (T t) y j
      have h1 : spaceGrad (T t) (y + fun i => (n i : ℝ)) i = spaceGrad (T t) y i :=
        isZPeriodic_spaceGrad_coord hTp i y n
      have h2 : spaceGrad (T t) (y + fun i => (n i : ℝ)) j = spaceGrad (T t) y j :=
        isZPeriodic_spaceGrad_coord hTp j y n
      rw [h1, h2]
  have hflow := Infra.Ergodic.cellAverage_flow_mul_sub_le_of_composedCoordinateAnalyticL1Bounds
    (d := 2) (N := N) (by norm_num) hN X hfc hfper Cf r hCf hr (hAn k.1 k.2 hξz i j)
    hgc.locallyIntegrable hfast hrN
  have hgavg : Infra.Ergodic.cellAverage (fun x => |g x|) ≤ ξ * (2 * B + 2 * B ^ 2) :=
    cellAverage_le_of_forall_le hgb hgc.abs
  rw [spaceAvg_eq_cellAverage, spaceAvg_eq_cellAverage, spaceAvg_eq_cellAverage]
  have hSum : 0 ≤ ∑' k : Fin 2 → ℤ, Real.exp (-(1 / 1024 : ℝ) * ‖k‖) :=
    tsum_nonneg fun _ => (Real.exp_pos _).le
  have hE := (Real.exp_pos (-(r * (N : ℝ)) / 1024)).le
  refine hflow.trans ?_
  calc _ ≤ 512 * Cf * (ξ * (2 * B + 2 * B ^ 2)) *
          (∑' k : Fin 2 → ℤ, Real.exp (-(1 / 1024 : ℝ) * ‖k‖)) *
          Real.exp (-(r * (N : ℝ)) / 1024) := by gcongr
    _ = _ := by ring

/-! ## `e.ergodic.space.kill` at a fixed time -/

/-- e.ergodic.space.kill at a fixed time t (8604–8630, before integrating in t). -/
theorem ergodic_space_kill_slice (hΦ : IsStreamSeq I Φ) {m : ℕ} (hm : 1 ≤ m) {κm : ℝ}
    (hκm : 0 < κm) {T : ℝ → Vec 2 → ℝ} {t : ℝ}
    (hTs : ContDiff ℝ (⊤ : ℕ∞) (T t)) (hTp : IsZ2Periodic (T t)) {Cf r : ℝ} (hCf : 0 ≤ Cf)
    (hr : 0 < r)
    (hAn : ∀ k : ℤ, Odd k → I.xiMK m k t ≠ 0 → ∀ i j : Fin 2,
      Infra.Ergodic.HasCoordinateAnalyticL1Bounds
        (fun y => ((spaceGrad (T t) (I.xFlow hΦ m (lIdx β I.Λ m k) t y) i *
          spaceGrad (T t) (I.xFlow hΦ m (lIdx β I.Λ m k) t y) j : ℝ) : ℂ)) Cf r)
    (hrN : 1 ≤ r * (ergodicFrequency β I.Λ m : ℝ)) :
    |(∫ x in unitCube, vecNormSq (leadingGrad I hΦ m κm T t x)) -
        gradQuad T (leadingGramAvg I hΦ m κm t) t| ≤
      4 * 512 * Cf *
        (2 * (a β I.Λ m * epsilon β I.Λ m ^ 2 / κm) +
          2 * (a β I.Λ m * epsilon β I.Λ m ^ 2 / κm) ^ 2) *
        (∑' k : Fin 2 → ℤ, Real.exp (-(1 / 1024 : ℝ) * ‖k‖)) *
        Real.exp (-(r * (ergodicFrequency β I.Λ m : ℝ)) / 1024) := by
  classical
  set S := (xiMK_odd_support_finite I hm t).toFinset with hS
  set W := 512 * Cf * (2 * (a β I.Λ m * epsilon β I.Λ m ^ 2 / κm) +
          2 * (a β I.Λ m * epsilon β I.Λ m ^ 2 / κm) ^ 2) *
        (∑' k : Fin 2 → ℤ, Real.exp (-(1 / 1024 : ℝ) * ‖k‖)) *
        Real.exp (-(r * (ergodicFrequency β I.Λ m : ℝ)) / 1024) with hW
  let H : Vec 2 → Matrix (Fin 2) (Fin 2) ℝ := fun x =>
    (leadingMatrix I hΦ m κm t x).transpose * leadingMatrix I hΦ m κm t x
  let g : {k : ℤ // Odd k} → Vec 2 → Fin 2 → Fin 2 → ℝ := fun k y i j =>
    gramKernel (I.xiMK m k.1 t) (gradMatrix (I.chiMK κm m k.1 t) y) i j
  let Y : {k : ℤ // Odd k} → Vec 2 → Vec 2 := fun k => I.xFlowInv hΦ m (lIdx β I.Λ m k.1) t
  let D : Fin 2 → Fin 2 → {k : ℤ // Odd k} → ℝ := fun i j k =>
    spaceAvg (fun x => (spaceGrad (T t) x i * spaceGrad (T t) x j) * g k (Y k x) i j) -
      spaceAvg (fun x => spaceGrad (T t) x i * spaceGrad (T t) x j) *
        spaceAvg (fun y => g k y i j)
  have hu : ∀ i, Continuous fun x => spaceGrad (T t) x i := fun i =>
    (contDiff_spaceGrad_coord hTs i).continuous
  have hH : ∀ x i j, H x i j = (1 : Matrix (Fin 2) (Fin 2) ℝ) i j + ∑ k ∈ S, g k (Y k x) i j := by
    intro x i j
    simp only [H, g, Y]
    rw [leadingMatrix_transpose_mul I hΦ hm κm t x]
    simp only [Matrix.add_apply, Matrix.sum_apply]
    rfl
  have hgc : ∀ k i j, Continuous fun y => g k y i j := fun k i j =>
    (continuous_gramKernel_grad I κm (m := m) t k.2 _).matrix_elem i j
  have hYc : ∀ k, Continuous (Y k) := fun k => (xFlowDiffeo I hΦ m (lIdx β I.Λ m k.1)
      t).contDiff_invFun.continuous
  have hHc : ∀ i j, Continuous fun x => H x i j := by
    intro i j
    have : (fun x => H x i j) = fun x =>
        (1 : Matrix (Fin 2) (Fin 2) ℝ) i j + ∑ k ∈ S, g k (Y k x) i j := funext fun x => hH x i j
    rw [this]
    exact continuous_const.add (continuous_finsetSum S fun k _ => (hgc k i j).comp (hYc k))
  have hL : ∫ x in unitCube, vecNormSq (leadingGrad I hΦ m κm T t x) =
      ∑ i, ∑ j, spaceAvg (fun x => (spaceGrad (T t) x i * spaceGrad (T t) x j) * H x i j) := by
    rw [← integral_quad_eq_sum hu hHc]
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    exact vecNormSq_mulVec _ _
  have hR : gradQuad T (leadingGramAvg I hΦ m κm t) t =
      ∑ i, ∑ j, spaceAvg (fun x => spaceGrad (T t) x i * spaceGrad (T t) x j) *
        spaceAvg (fun x => H x i j) := integral_quad_spaceAvgMat hu
  have hdecomp : ∀ i j,
      spaceAvg (fun x => (spaceGrad (T t) x i * spaceGrad (T t) x j) * H x i j) -
        spaceAvg (fun x => spaceGrad (T t) x i * spaceGrad (T t) x j) *
          spaceAvg (fun x => H x i j) =
      ∑ k ∈ S, D i j k := by
    intro i j
    rw [mul_comm (spaceAvg (fun x => spaceGrad (T t) x i * spaceGrad (T t) x j))]
    refine spaceAvg_mul_sub_decomp S ((hu i).mul (hu j)) (fun k => hgc k i j) hYc (hH · i j)
      fun k _ => ?_
    refine spaceAvg_comp_xFlowInv I hΦ m (lIdx β I.Λ m k.1) t (g := fun y => g k y i j) ?_
    intro y n
    change gramKernel (I.xiMK m k.1 t) (gradMatrix (I.chiMK κm m k.1 t) (y + fun i => (n i : ℝ)))
        i j = gramKernel (I.xiMK m k.1 t) (gradMatrix (I.chiMK κm m k.1 t) y) i j
    have hp : gradMatrix (I.chiMK κm m k.1 t) (y + fun i => (n i : ℝ)) =
        gradMatrix (I.chiMK κm m k.1 t) y := gradMatrix_chiMK_periodic I hm κm k.1 t y n
    rw [hp]
  have hterm : ∀ (k : {k : ℤ // Odd k}) i j, |D i j k| ≤ I.xiMK m k.1 t * W := fun k i j =>
    space_kill_term_bound I hΦ hm hκm hTs hTp hCf hr hAn hrN k i j
  have hdiff : (∫ x in unitCube, vecNormSq (leadingGrad I hΦ m κm T t x)) -
      gradQuad T (leadingGramAvg I hΦ m κm t) t = ∑ i, ∑ j, ∑ k ∈ S, D i j k := by
    rw [hL, hR, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun j _ => hdecomp i j
  have hxsum : ∑ k ∈ S, I.xiMK m k.1 t = 1 := xiMK_odd_partition_finset I hm t
  rw [hdiff]
  calc |∑ i, ∑ j, ∑ k ∈ S, D i j k| ≤ ∑ i, |∑ j, ∑ k ∈ S, D i j k| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i, ∑ j, |∑ k ∈ S, D i j k| :=
        Finset.sum_le_sum fun i _ => Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i : Fin 2, ∑ j : Fin 2, ∑ k ∈ S, I.xiMK m k.1 t * W :=
        Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ =>
          (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun k _ => hterm k i j)
    _ = 4 * W := by
        simp only [← Finset.sum_mul, hxsum, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
          nsmul_eq_mul]
        norm_num
    _ = _ := by rw [hW]; ring

end AVenhance.Infra.Section5.LeftToShow

end
