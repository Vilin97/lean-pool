/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.Integration.Energy.AnsatzRegularityFlow
public import LeanPool.AnomalousDiffusion.AVenhance.Statements.Section4.Ansatz

/-! # Regularity and periodicity of the ansatz `θTilde_m`

Source: `enhance.tex` (`e.ansatz`).  With `T = T_{m-1}` and `HTilde_m` the only premises:

* `ansatz_contDiffOn_two`: joint `C²` regularity on `[0,∞) × ℝ²`.  The `ξ`-sum is locally finite in
  time (each `ξ_{m,k}` is supported in a window of length `(5/2)τ_m` about `kτ_m`), so near each
  time it is a finite sum of `C²` terms: `ξ_{m,k}` is `C^∞`, `ΧTilde_{m,k} = -corrTime · u ∘ X⁻¹` is
  `C²` (`corrTime` is `C²`, `u` and `X⁻¹` are jointly `C^∞`) and the transported gradient is jointly
  `C^∞` (`transportedGrad_contDiffOn`).
* `ansatz_slice_contDiff`: at a fixed time the ansatz is `C^∞` in space.
* `ansatz_periodic`: at a fixed time the ansatz is `ℤ²`-periodic. -/

@[expose] public section

open Homogenization Filter Topology
open scoped ContDiff

noncomputable section

namespace AVenhance.Infra.Section5.Integration

open AVenhance AVenhance.Infra.Section5

variable {β : ℝ} (I : Ingredients β) {Φ : ℕ → ℝ → Vec 2 → ℝ}

/-! ### Smoothness of the shear field and of the twisted corrector -/

/-- The shear field `u_{m,k}` is `C^∞`. -/
theorem contDiff_uShear' (β : ℝ) (Λ m : ℕ) (k : ℤ) : ContDiff ℝ ∞ (uShear β Λ m k) := by
  unfold uShear
  split_ifs
  · refine contDiff_pi.2 fun i => ?_
    fin_cases i <;> simp only [Fin.isValue, Nat.succ_eq_add_one, Nat.reduceAdd, Fin.zero_eta,
        Matrix.cons_val_zero, Fin.isValue, Nat.succ_eq_add_one, Nat.reduceAdd, Fin.mk_one,
        Matrix.cons_val_one,
                      Matrix.cons_val_fin_one] <;> fun_prop
  · refine contDiff_pi.2 fun i => ?_
    fin_cases i <;> simp only [Fin.isValue, Nat.succ_eq_add_one, Nat.reduceAdd, Fin.zero_eta,
        Matrix.cons_val_zero, Fin.isValue, Nat.succ_eq_add_one, Nat.reduceAdd, Fin.mk_one,
        Matrix.cons_val_one,
                      Matrix.cons_val_fin_one] <;> fun_prop
  · exact contDiff_const

/-- Each coordinate of `ΧTilde_{m,k}` is jointly `C²` in time and position. -/
theorem chiTilde_component_contDiff_two (hΦ : IsStreamSeq I Φ) (m : ℕ) (κm : ℝ) (k : ℤ)
    (i : Fin 2) :
    ContDiff ℝ 2 (fun p : ℝ × Vec 2 => I.chiTilde hΦ m κm k p.1 p.2 i) := by
  have hcorr : ContDiff ℝ 2 (fun p : ℝ × Vec 2 => I.corrTime κm m k p.1) :=
    (Infra.Section3.corrTime_contDiff_two I κm k).comp contDiff_fst
  have hXI := (xFlowInv_joint_contDiff_infty I hΦ m (lIdx β I.Λ m k)).of_le
    (show (2 : WithTop ℕ∞) ≤ ∞ from by simp)
  have hu : ContDiff ℝ 2 (fun p : ℝ × Vec 2 =>
      uShear β I.Λ m k (I.xFlowInv hΦ m (lIdx β I.Λ m k) p.1 p.2) i) :=
    ((contDiff_apply ℝ ℝ i).comp ((contDiff_uShear' β I.Λ m k).of_le
      (show (2 : WithTop ℕ∞) ≤ ∞ from by simp))).comp hXI
  simpa [Ingredients.chiTilde, Ingredients.chiMK] using hcorr.neg.mul hu

/-! ### The summands of the ansatz -/

/-- The `k`-th summand of the series in the ansatz. -/
def ansatzSummand (hΦ : IsStreamSeq I Φ) (m : ℕ) (κm : ℝ) (T : ℝ → Vec 2 → ℝ) (k : ℤ)
    (t : ℝ) (x : Vec 2) : ℝ :=
  I.xiMK m k t *
    vecDot (I.chiTilde hΦ m κm k t x)
      (spaceGrad (fun y => T t (I.xFlow hΦ m (lIdx β I.Λ m k) t y))
        (I.xFlowInv hΦ m (lIdx β I.Λ m k) t x))

theorem ansatz_eq_summand (hΦ : IsStreamSeq I Φ) (m : ℕ) (κm : ℝ) (T : ℝ → Vec 2 → ℝ)
    (t : ℝ) (x : Vec 2) :
    I.ansatz hΦ m κm T t x =
      T t x + (∑' k : ℤ, ansatzSummand I hΦ m κm T k t x) + I.Hm hΦ m κm T t x := rfl

theorem ansatzSummand_eq_zero (hΦ : IsStreamSeq I Φ) (m : ℕ) (κm : ℝ) (T : ℝ → Vec 2 → ℝ)
    {k : ℤ} {t : ℝ} (h : I.xiMK m k t = 0) (x : Vec 2) :
    ansatzSummand I hΦ m κm T k t x = 0 := by
  simp [ansatzSummand, h]

/-- `ξ_{m,k}` is `C^∞`. -/
theorem contDiff_xiMK (m : ℕ) (k : ℤ) : ContDiff ℝ ∞ (I.xiMK m k) := by
  unfold Ingredients.xiMK scaledCutoff
  exact I.xi_smooth.comp ((contDiff_id.sub contDiff_const).div_const _)

/-- Each summand is jointly `C²` on `[0,∞) × ℝ²`. -/
theorem ansatzSummand_contDiffOn_two (hΦ : IsStreamSeq I Φ) (m : ℕ) (κm : ℝ) (k : ℤ)
    {T : ℝ → Vec 2 → ℝ}
    (hT : ContDiffOn ℝ ∞ (fun p : ℝ × Vec 2 => T p.1 p.2) (Set.Ici (0 : ℝ) ×ˢ Set.univ)) :
    ContDiffOn ℝ 2 (fun p : ℝ × Vec 2 => ansatzSummand I hΦ m κm T k p.1 p.2)
      (Set.Ici (0 : ℝ) ×ˢ Set.univ) := by
  have hle : (2 : WithTop ℕ∞) ≤ ∞ := by simp
  have hxi : ContDiff ℝ 2 (fun p : ℝ × Vec 2 => I.xiMK m k p.1) :=
    ((contDiff_xiMK I m k).of_le hle).comp contDiff_fst
  refine hxi.contDiffOn.mul ?_
  unfold vecDot
  refine ContDiffOn.sum fun i _ => ContDiffOn.mul ?_ ?_
  · exact (chiTilde_component_contDiff_two I hΦ m κm k i).contDiffOn
  · exact (transportedGrad_contDiffOn I hΦ m (lIdx β I.Λ m k) hT i).of_le hle

/-- Nonvanishing of `ξ_{m,k}(t)` forces `t` to lie within `(5/4) τ_m` of `k τ_m`. -/
theorem xiMK_ne_zero_abs_le' (m : ℕ) {k : ℤ} {t : ℝ} (hne : I.xiMK m k t ≠ 0) :
    |t - (k : ℝ) * tau β I.Λ m| ≤ 5 / 4 * tau β I.Λ m := by
  have hτ := I.tau_pos' m
  set u := (t - k * tau β I.Λ m) / tau β I.Λ m with hu
  have hmem : u ∈ Set.Icc (-(5 / 4) : ℝ) (5 / 4) := by
    by_contra hnot
    apply hne
    have h1 := I.xi_le_ind u
    have h2 := I.ind_le_xi u
    rw [indIcc_eq_zero_of_not_mem hnot] at h1
    have h3 := indIcc_nonneg' (-(3 / 4)) (3 / 4) u
    exact le_antisymm h1 (h3.trans h2)
  have : |u| ≤ 5 / 4 := abs_le.mpr ⟨hmem.1, hmem.2⟩
  rw [hu, abs_div, abs_of_pos hτ, div_le_iff₀ hτ] at this
  linarith

/-- The finite set of modes that can be active within unit time of `t₀`. -/
theorem exists_active_finset (m : ℕ) (t₀ : ℝ) :
    ∃ S : Finset ℤ, ∀ k ∉ S, ∀ t, |t - t₀| < 1 → I.xiMK m k t = 0 := by
  have hτ := I.tau_pos' m
  have hfin := finite_lattice_near hτ t₀ (5 / 4 * tau β I.Λ m + 1)
  refine ⟨hfin.toFinset, fun k hk t ht => ?_⟩
  by_contra hne
  apply hk
  rw [Set.Finite.mem_toFinset]
  have h1 := xiMK_ne_zero_abs_le' I m hne
  have h3 : |t₀ - (k : ℝ) * tau β I.Λ m| ≤
      |t₀ - t| + |t - (k : ℝ) * tau β I.Λ m| := by
    have := abs_add_le (t₀ - t) (t - (k : ℝ) * tau β I.Λ m)
    simpa using this
  have h2 : |t₀ - t| < 1 := by rwa [abs_sub_comm]
  change |t₀ - (k : ℝ) * tau β I.Λ m| ≤ 5 / 4 * tau β I.Λ m + 1
  linarith

/-- Joint `C²` regularity of the ansatz series on `[0,∞) × ℝ²`. -/
theorem ansatz_series_contDiffOn_two (hΦ : IsStreamSeq I Φ) (m : ℕ) (κm : ℝ)
    {T : ℝ → Vec 2 → ℝ}
    (hT : ContDiffOn ℝ ∞ (fun p : ℝ × Vec 2 => T p.1 p.2) (Set.Ici (0 : ℝ) ×ˢ Set.univ)) :
    ContDiffOn ℝ 2 (fun p : ℝ × Vec 2 => ∑' k : ℤ, ansatzSummand I hΦ m κm T k p.1 p.2)
      (Set.Ici (0 : ℝ) ×ˢ Set.univ) := by
  refine contDiffOn_of_locally_contDiffOn fun p₀ hp₀ => ?_
  obtain ⟨S, hS⟩ := exists_active_finset I m p₀.1
  have hopen : IsOpen {p : ℝ × Vec 2 | |p.1 - p₀.1| < 1} :=
    isOpen_lt (by fun_prop) continuous_const
  refine ⟨_, hopen, by simp, ?_⟩
  have hfin : ContDiffOn ℝ 2 (fun p : ℝ × Vec 2 => ∑ k ∈ S, ansatzSummand I hΦ m κm T k p.1 p.2)
      (Set.Ici (0 : ℝ) ×ˢ Set.univ ∩ {p : ℝ × Vec 2 | |p.1 - p₀.1| < 1}) :=
    ContDiffOn.sum fun k _ =>
      (ansatzSummand_contDiffOn_two I hΦ m κm k hT).mono Set.inter_subset_left
  refine hfin.congr fun p hp => ?_
  refine tsum_eq_sum fun k hk => ?_
  exact ansatzSummand_eq_zero I hΦ m κm T (hS k hk p.1 hp.2) p.2

/-- **Joint `C²` regularity of the ansatz** `θTilde_m` on `[0,∞) × ℝ²`, given `C^∞` regularity of
    the
iterate `T_{m-1}` and `C²` regularity of `HTilde_m`. -/
theorem ansatz_contDiffOn_two (hΦ : IsStreamSeq I Φ) (m : ℕ) (κm : ℝ) {T : ℝ → Vec 2 → ℝ}
    (hT : ContDiffOn ℝ (⊤ : ℕ∞) (fun p : ℝ × Vec 2 => T p.1 p.2) (Set.Ici (0 : ℝ) ×ˢ Set.univ))
    (hH : ContDiffOn ℝ 2 (fun p : ℝ × Vec 2 => I.Hm hΦ m κm T p.1 p.2)
      (Set.Ici (0 : ℝ) ×ˢ Set.univ)) :
    ContDiffOn ℝ 2 (fun p : ℝ × Vec 2 => I.ansatz hΦ m κm T p.1 p.2)
      (Set.Ici (0 : ℝ) ×ˢ Set.univ) := by
  have hT2 : ContDiffOn ℝ 2 (fun p : ℝ × Vec 2 => T p.1 p.2) (Set.Ici (0 : ℝ) ×ˢ Set.univ) :=
    hT.of_le (by simp)
  exact (hT2.add (ansatz_series_contDiffOn_two I hΦ m κm hT)).add hH

/-! ### Fixed-time smoothness -/

/-- The gradient of a `C^∞` function is `C^∞`. -/
theorem contDiff_spaceGrad_component {f : Vec 2 → ℝ} (hf : ContDiff ℝ ∞ f) (i : Fin 2) :
    ContDiff ℝ ∞ (fun x => spaceGrad f x i) :=
  (hf.fderiv_right (by simp)).clm_apply contDiff_const

/-- At a fixed time, each summand is `C^∞` in the position. -/
theorem ansatzSummand_slice_contDiff (hΦ : IsStreamSeq I Φ) (m : ℕ) (κm : ℝ) (k : ℤ)
    {T : ℝ → Vec 2 → ℝ} {t : ℝ} (hTt : ContDiff ℝ ∞ (T t)) :
    ContDiff ℝ ∞ (fun x => ansatzSummand I hΦ m κm T k t x) := by
  have hXI : ContDiff ℝ ∞ (I.xFlowInv hΦ m (lIdx β I.Λ m k) t) :=
    (xFlowInv_joint_contDiff_infty I hΦ m (lIdx β I.Λ m k)).comp (contDiff_prodMk_right t)
  have hXF : ContDiff ℝ ∞ (I.xFlow hΦ m (lIdx β I.Λ m k) t) :=
    (xFlow_joint_contDiff_infty I hΦ m (lIdx β I.Λ m k)).comp (contDiff_prodMk_right t)
  have hcomp : ContDiff ℝ ∞ (fun y => T t (I.xFlow hΦ m (lIdx β I.Λ m k) t y)) :=
    hTt.comp hXF
  unfold ansatzSummand vecDot
  refine contDiff_const.mul (ContDiff.sum fun i _ => ContDiff.mul ?_ ?_)
  · have hu : ContDiff ℝ ∞ (fun x => uShear β I.Λ m k (I.xFlowInv hΦ m (lIdx β I.Λ m k) t x) i) :=
      (contDiff_apply ℝ ℝ i).comp ((contDiff_uShear' β I.Λ m k).comp hXI)
    simpa [Ingredients.chiTilde, Ingredients.chiMK] using (contDiff_const (c := -(I.corrTime κm m
        k t))).mul hu
  · exact (contDiff_spaceGrad_component hcomp i).comp hXI

/-- **Fixed-time smoothness of the ansatz**: `θTilde_m(t)` is `C^∞` in space. -/
theorem ansatz_slice_contDiff (hΦ : IsStreamSeq I Φ) (m : ℕ) (κm : ℝ) {T : ℝ → Vec 2 → ℝ}
    {t : ℝ} (hTt : ContDiff ℝ (⊤ : ℕ∞) (T t))
    (hHt : ContDiff ℝ (⊤ : ℕ∞) (I.Hm hΦ m κm T t)) :
    ContDiff ℝ (⊤ : ℕ∞) (I.ansatz hΦ m κm T t) := by
  classical
  let S : Finset ℤ := (I.xiMK_support_finite m t).toFinset
  have hzero (k : ℤ) (hk : k ∉ S) : I.xiMK m k t = 0 := by
    by_contra hne
    exact hk ((I.xiMK_support_finite m t).mem_toFinset.mpr hne)
  have hfun : I.ansatz hΦ m κm T t = fun x =>
      T t x + (∑ k ∈ S, ansatzSummand I hΦ m κm T k t x) + I.Hm hΦ m κm T t x := by
    funext x
    rw [ansatz_eq_summand]
    congr 2
    exact tsum_eq_sum fun k hk => ansatzSummand_eq_zero I hΦ m κm T (hzero k hk) x
  rw [hfun]
  exact (hTt.add (ContDiff.sum fun k _ => ansatzSummand_slice_contDiff I hΦ m κm k hTt)).add hHt

/-! ### Periodicity -/

/-- The reciprocal cell length `ε_m⁻¹` is a natural number (`ε_0 = 1`). -/
theorem epsilon_inv_exists_nat (β : ℝ) (Λ m : ℕ) : ∃ N : ℕ, (epsilon β Λ m)⁻¹ = (N : ℝ) := by
  by_cases h : m = 0
  · exact ⟨1, by simp [epsilon, h]⟩
  · exact ⟨⌈(Λ : ℝ) ^ ((q β) ^ m / (q β - 1))⌉₊, by simp [epsilon, h]⟩

theorem AnsatzRegularity.cos_integer_frequency_periodic' (ε : ℝ) {N : ℕ} (hεinv : ε⁻¹ = (N : ℝ))
    (x : ℝ) (n : ℤ) :
    Real.cos (2 * Real.pi * (x + (n : ℝ)) / ε) = Real.cos (2 * Real.pi * x / ε) := by
  have hshift : 2 * Real.pi * (x + (n : ℝ)) / ε =
      2 * Real.pi * x / ε + ((n * (N : ℤ) : ℤ) : ℝ) * (2 * Real.pi) := by
    calc
      _ = 2 * Real.pi * x / ε + 2 * Real.pi * (n : ℝ) / ε := by ring
      _ = 2 * Real.pi * x / ε + 2 * Real.pi * ((n : ℝ) * (N : ℝ)) := by
        rw [div_eq_mul_inv, ← hεinv]
        ring
      _ = 2 * Real.pi * x / ε + ((n * (N : ℤ) : ℤ) : ℝ) * (2 * Real.pi) := by
        push_cast
        ring
  rw [hshift, Real.cos_add_int_mul_two_pi]

/-- The shear field `u_{m,k}` is `ℤ²`-periodic. -/
theorem uShear_isZ2Periodic (β : ℝ) (Λ m : ℕ) (k : ℤ) : IsZ2Periodic (uShear β Λ m k) := by
  intro n x
  obtain ⟨N, hN⟩ := epsilon_inv_exists_nat β Λ m
  ext i
  by_cases hk1 : k % 4 = 1
  · simp [uShear, hk1, latticeShift,
      AnsatzRegularity.cos_integer_frequency_periodic' (epsilon β Λ m) hN (x 0) (n 0)]
  · by_cases hk3 : k % 4 = 3
    · simp [uShear, hk3, latticeShift,
        AnsatzRegularity.cos_integer_frequency_periodic' (epsilon β Λ m) hN (x 1) (n 1)]
    · simp [uShear, hk1, hk3]

/-- The gradient of a `ℤ²`-periodic function is `ℤ²`-periodic. -/
theorem spaceGrad_isZ2Periodic {f : Vec 2 → ℝ} (hf : IsZ2Periodic f) :
    IsZ2Periodic (spaceGrad f) := by
  intro n x
  funext i
  have hfun : (fun y => f (y + latticeShift n)) = f := funext fun y => hf n y
  have h := fderiv_comp_add_right (𝕜 := ℝ) (f := f) (latticeShift n) (x := x)
  rw [hfun] at h
  simp only [spaceGrad]
  rw [← h]

/-- Each summand is `ℤ²`-periodic when `T(t)` is. -/
theorem ansatzSummand_isZ2Periodic (hΦ : IsStreamSeq I Φ) (m : ℕ) (κm : ℝ) (k : ℤ)
    {T : ℝ → Vec 2 → ℝ} {t : ℝ} (hTp : IsZ2Periodic (T t)) :
    IsZ2Periodic (fun x => ansatzSummand I hΦ m κm T k t x) := by
  intro n x
  have hinv : I.xFlowInv hΦ m (lIdx β I.Λ m k) t (x + latticeShift n) =
      I.xFlowInv hΦ m (lIdx β I.Λ m k) t x + latticeShift n :=
    LeftToShow.xFlowInv_lattice_equivariant I hΦ m (lIdx β I.Λ m k) t x n
  have hper : IsZ2Periodic (fun y => T t (I.xFlow hΦ m (lIdx β I.Λ m k) t y)) := by
    intro n' y
    have h := (LeftToShow.xFlowDiffeo I hΦ m (lIdx β I.Λ m k) t).lattice_equivariant y n'
    change I.xFlow hΦ m (lIdx β I.Λ m k) t (y + latticeShift n') =
      I.xFlow hΦ m (lIdx β I.Λ m k) t y + latticeShift n' at h
    change T t (I.xFlow hΦ m (lIdx β I.Λ m k) t (y + latticeShift n')) =
      T t (I.xFlow hΦ m (lIdx β I.Λ m k) t y)
    rw [h]
    exact hTp n' _
  have hchi : I.chiTilde hΦ m κm k t (x + latticeShift n) = I.chiTilde hΦ m κm k t x := by
    unfold Ingredients.chiTilde Ingredients.chiMK
    rw [hinv, uShear_isZ2Periodic β I.Λ m k n]
  change ansatzSummand I hΦ m κm T k t (x + latticeShift n) = ansatzSummand I hΦ m κm T k t x
  unfold ansatzSummand
  rw [hchi, hinv, spaceGrad_isZ2Periodic hper n]

/-- **Periodicity of the ansatz**: `θTilde_m(t)` is `ℤ²`-periodic when `T(t)` and `HTilde_m(t)`
    are. -/
theorem ansatz_periodic (hΦ : IsStreamSeq I Φ) (m : ℕ) (κm : ℝ) {T : ℝ → Vec 2 → ℝ} {t : ℝ}
    (hTt : ContDiff ℝ 1 (T t)) (hTp : IsZ2Periodic (T t))
    (hHp : IsZ2Periodic (I.Hm hΦ m κm T t)) :
    IsZ2Periodic (I.ansatz hΦ m κm T t) := by
  have _hTt := hTt -- `C¹` regularity is not needed: the gradient of a periodic map is periodic
  intro n x
  rw [ansatz_eq_summand, ansatz_eq_summand, hTp n x, hHp n x]
  congr 2
  exact tsum_congr fun k => ansatzSummand_isZ2Periodic I hΦ m κm k hTp n x

end AVenhance.Infra.Section5.Integration
