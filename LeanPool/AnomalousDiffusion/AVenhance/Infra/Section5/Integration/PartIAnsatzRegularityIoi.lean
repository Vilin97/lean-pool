/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.Integration.Energy.AnsatzRegularity

/-! # Part I: regularity of the ansatz `θTilde_m` on the open half space

The open-time analogue of `Energy/AnsatzRegularity`: with `T = T_{m-1}` jointly `C^∞` and `HTilde_m`
jointly `C²` only on `(0,∞) × ℝ²`, the ansatz `θTilde_m = T + ∑_k ξ_{m,k} ΧTilde_{m,k}·(…) +
    HTilde_m` is
    jointly
`C²` on `(0,∞) × ℝ²`.  (The fixed-time statements `ansatz_slice_contDiff` and `ansatz_periodic`
of `Energy/AnsatzRegularity` are pointwise in the time and are used as they stand for `t > 0`.) -/

@[expose] public section

open Homogenization
open scoped ContDiff

noncomputable section

namespace AVenhance.Infra.Section5.Integration

open AVenhance AVenhance.Infra.Section5

variable {β : ℝ} (I : Ingredients β) {Φ : ℕ → ℝ → Vec 2 → ℝ}

/-- A function that is `C^∞` on `Ioi 0 ×ˢ univ` is `C^∞` on each slice at a positive time. -/
theorem slice_contDiff_of_contDiffOn_Ioi {T : ℝ → Vec 2 → ℝ}
    (hT : ContDiffOn ℝ ∞ (fun p : ℝ × Vec 2 => T p.1 p.2) (Set.Ioi (0 : ℝ) ×ˢ Set.univ))
    {t : ℝ} (ht : 0 < t) : ContDiff ℝ ∞ (T t) := by
  have h : ContDiffOn ℝ ∞ ((fun p : ℝ × Vec 2 => T p.1 p.2) ∘ (fun y : Vec 2 => (t, y)))
      Set.univ :=
    hT.comp (contDiff_prodMk_right t).contDiffOn (fun y _ => ⟨ht, trivial⟩)
  exact contDiffOn_univ.mp h

/-- The transported gradient is jointly `C^∞` on `Ioi 0 ×ˢ univ` whenever `T` is. -/
theorem transportedGrad_contDiffOn_Ioi (hΦ : IsStreamSeq I Φ) (m : ℕ) (l : ℤ)
    {T : ℝ → Vec 2 → ℝ}
    (hT : ContDiffOn ℝ ∞ (fun p : ℝ × Vec 2 => T p.1 p.2) (Set.Ioi (0 : ℝ) ×ˢ Set.univ))
    (i : Fin 2) :
    ContDiffOn ℝ ∞ (fun p : ℝ × Vec 2 =>
      spaceGrad (fun y => T p.1 (I.xFlow hΦ m l p.1 y)) (I.xFlowInv hΦ m l p.1 p.2) i)
      (Set.Ioi (0 : ℝ) ×ˢ Set.univ) := by
  set s : Set (ℝ × Vec 2) := Set.Ioi (0 : ℝ) ×ˢ Set.univ with hs
  have hso : IsOpen s := isOpen_Ioi.prod isOpen_univ
  have hsu : UniqueDiffOn ℝ s := hso.uniqueDiffOn
  have hXF := xFlow_joint_contDiff_infty I hΦ m l
  have hXI := xFlowInv_joint_contDiff_infty I hΦ m l
  have hpair : ContDiff ℝ ∞ (fun p : ℝ × Vec 2 => (p.1, I.xFlowInv hΦ m l p.1 p.2)) :=
    contDiff_fst.prodMk hXI
  set E : ℝ × Vec 2 → ℝ := fun p => ∑ j : Fin 2,
    fderiv ℝ (fun q : ℝ × Vec 2 => I.xFlow hΦ m l q.1 q.2 j) (p.1, I.xFlowInv hΦ m l p.1 p.2)
        (0, basisVec i) *
      fderivWithin ℝ (fun p : ℝ × Vec 2 => T p.1 p.2) s p (0, basisVec j) with hE
  have hEsm : ContDiffOn ℝ ∞ E s := by
    refine ContDiffOn.sum fun j _ => ContDiffOn.mul ?_ ?_
    · have hXj : ContDiff ℝ ∞ (fun q : ℝ × Vec 2 => I.xFlow hΦ m l q.1 q.2 j) :=
        (contDiff_apply ℝ ℝ j).comp hXF
      exact ((contDiff_partial hXj (0, basisVec i)).comp hpair).contDiffOn
    · exact ((hT.fderivWithin hsu (by simp)).clm_apply contDiffOn_const)
  refine hEsm.congr ?_
  rintro ⟨t, x⟩ ⟨ht, -⟩
  have ht' : 0 < t := ht
  have hslice := slice_contDiff_of_contDiffOn_Ioi hT ht'
  have hXslice : ContDiff ℝ ∞ (I.xFlow hΦ m l t) := hXF.comp (contDiff_prodMk_right t)
  have hxx : I.xFlow hΦ m l t (I.xFlowInv hΦ m l t x) = x :=
    (LeftToShow.xFlowDiffeo I hΦ m l t).right_inv x
  have hfT : HasFDerivAt (T t) (fderiv ℝ (T t) (I.xFlow hΦ m l t (I.xFlowInv hΦ m l t x)))
      (I.xFlow hΦ m l t (I.xFlowInv hΦ m l t x)) :=
    (hslice.differentiable (by simp) _).hasFDerivAt
  have hfX : HasFDerivAt (I.xFlow hΦ m l t)
      (fderiv ℝ (I.xFlow hΦ m l t) (I.xFlowInv hΦ m l t x)) (I.xFlowInv hΦ m l t x) :=
    (hXslice.differentiable (by simp) _).hasFDerivAt
  have hchain := spaceGrad_comp_eq_gradMatrix_mul hfT hfX i
  simp only [hE]
  rw [hchain]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [hxx]
  congr 1
  · exact gradMatrix_slice_eq hXF t _ i j
  · exact spaceGrad_slice_eq (F := fun p : ℝ × Vec 2 => T p.1 p.2) (s := s) t x
      (fun y => ⟨ht', trivial⟩) (hT.differentiableOn (by simp) (t, x) ⟨ht', trivial⟩) j

/-- Each summand is jointly `C²` on `(0,∞) × ℝ²`. -/
theorem ansatzSummand_contDiffOn_two_Ioi (hΦ : IsStreamSeq I Φ) (m : ℕ) (κm : ℝ) (k : ℤ)
    {T : ℝ → Vec 2 → ℝ}
    (hT : ContDiffOn ℝ ∞ (fun p : ℝ × Vec 2 => T p.1 p.2) (Set.Ioi (0 : ℝ) ×ˢ Set.univ)) :
    ContDiffOn ℝ 2 (fun p : ℝ × Vec 2 => ansatzSummand I hΦ m κm T k p.1 p.2)
      (Set.Ioi (0 : ℝ) ×ˢ Set.univ) := by
  have hle : (2 : WithTop ℕ∞) ≤ ∞ := by simp
  have hxi : ContDiff ℝ 2 (fun p : ℝ × Vec 2 => I.xiMK m k p.1) :=
    ((contDiff_xiMK I m k).of_le hle).comp contDiff_fst
  refine hxi.contDiffOn.mul ?_
  unfold vecDot
  refine ContDiffOn.sum fun i _ => ContDiffOn.mul ?_ ?_
  · exact (chiTilde_component_contDiff_two I hΦ m κm k i).contDiffOn
  · exact (transportedGrad_contDiffOn_Ioi I hΦ m (lIdx β I.Λ m k) hT i).of_le hle

/-- Joint `C²` regularity of the ansatz series on `(0,∞) × ℝ²`. -/
theorem ansatz_series_contDiffOn_two_Ioi (hΦ : IsStreamSeq I Φ) (m : ℕ) (κm : ℝ)
    {T : ℝ → Vec 2 → ℝ}
    (hT : ContDiffOn ℝ ∞ (fun p : ℝ × Vec 2 => T p.1 p.2) (Set.Ioi (0 : ℝ) ×ˢ Set.univ)) :
    ContDiffOn ℝ 2 (fun p : ℝ × Vec 2 => ∑' k : ℤ, ansatzSummand I hΦ m κm T k p.1 p.2)
      (Set.Ioi (0 : ℝ) ×ˢ Set.univ) := by
  refine contDiffOn_of_locally_contDiffOn fun p₀ hp₀ => ?_
  obtain ⟨S, hS⟩ := exists_active_finset I m p₀.1
  have hopen : IsOpen {p : ℝ × Vec 2 | |p.1 - p₀.1| < 1} :=
    isOpen_lt (by fun_prop) continuous_const
  refine ⟨_, hopen, by simp, ?_⟩
  have hfin : ContDiffOn ℝ 2 (fun p : ℝ × Vec 2 => ∑ k ∈ S, ansatzSummand I hΦ m κm T k p.1 p.2)
      (Set.Ioi (0 : ℝ) ×ˢ Set.univ ∩ {p : ℝ × Vec 2 | |p.1 - p₀.1| < 1}) :=
    ContDiffOn.sum fun k _ =>
      (ansatzSummand_contDiffOn_two_Ioi I hΦ m κm k hT).mono Set.inter_subset_left
  refine hfin.congr fun p hp => ?_
  refine tsum_eq_sum fun k hk => ?_
  exact ansatzSummand_eq_zero I hΦ m κm T (hS k hk p.1 hp.2) p.2

/-- **Joint `C²` regularity of the ansatz** `θTilde_m` on `(0,∞) × ℝ²`, given `C^∞` regularity of
    the
iterate `T_{m-1}` and `C²` regularity of `HTilde_m` on the open half space. -/
theorem ansatz_contDiffOn_two_Ioi (hΦ : IsStreamSeq I Φ) (m : ℕ) (κm : ℝ) {T : ℝ → Vec 2 → ℝ}
    (hT : ContDiffOn ℝ (⊤ : ℕ∞) (fun p : ℝ × Vec 2 => T p.1 p.2)
      (Set.Ioi (0 : ℝ) ×ˢ Set.univ))
    (hH : ContDiffOn ℝ 2 (fun p : ℝ × Vec 2 => I.Hm hΦ m κm T p.1 p.2)
      (Set.Ioi (0 : ℝ) ×ˢ Set.univ)) :
    ContDiffOn ℝ 2 (fun p : ℝ × Vec 2 => I.ansatz hΦ m κm T p.1 p.2)
      (Set.Ioi (0 : ℝ) ×ˢ Set.univ) := by
  have hT2 : ContDiffOn ℝ 2 (fun p : ℝ × Vec 2 => T p.1 p.2) (Set.Ioi (0 : ℝ) ×ˢ Set.univ) :=
    hT.of_le (by simp)
  exact (hT2.add (ansatz_series_contDiffOn_two_Ioi I hΦ m κm hT)).add hH

end AVenhance.Infra.Section5.Integration
