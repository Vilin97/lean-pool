/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section3.ParabolicMaximum
public import Mathlib.Topology.Order.Compact

/-! A bounded whole-plane maximum principle for the scalar shear corrector. -/

@[expose] public section

noncomputable section

open Filter Homogenization
open scoped Topology

namespace AVenhance.Infra.Section3

open AVenhance

/-- Closed spatial box of radius R used in the parabolic uniqueness argument. -/
def BoundedParabolicUniqueness.parabolicSpatialBox (R : ℝ) : Set (Vec 2) :=
  Set.pi Set.univ fun _ : Fin 2 => Set.Icc (-R) R

theorem BoundedParabolicUniqueness.parabolicRadialSq_nonneg (x : Vec 2) :
    0 ≤ parabolicRadialSq x := by
  dsimp [parabolicRadialSq]
  positivity

theorem BoundedParabolicUniqueness.coord_sq_le_parabolicRadialSq (x : Vec 2) (i : Fin 2) :
    x i ^ 2 ≤ parabolicRadialSq x := by
  fin_cases i <;> simp only [Fin.zero_eta, Fin.isValue, parabolicRadialSq,
      le_add_iff_nonneg_right, Fin.mk_one, Fin.isValue, parabolicRadialSq, le_add_iff_nonneg_left]
      <;> positivity

theorem BoundedParabolicUniqueness.scalar_drift_absorb {b y c D : ℝ}
    (hb : |b| ≤ D) (hc : 0 ≤ c) :
    -b * (c * (2 * y)) ≤ c * (y ^ 2 + D ^ 2) := by
  have hmul : -b * y ≤ D * |y| := by
    calc
      -b * y ≤ |(-b) * y| := le_abs_self _
      _ = |b| * |y| := by rw [abs_mul, abs_neg]
      _ ≤ D * |y| := mul_le_mul_of_nonneg_right hb (abs_nonneg _)
  have hyoung : 2 * D * |y| ≤ y ^ 2 + D ^ 2 := by
    nlinarith only [sq_nonneg (|y| - D), sq_abs y]
  have htwice : 2 * (-b * y) ≤ 2 * D * |y| := by
    calc
      2 * (-b * y) ≤ 2 * (D * |y|) :=
        mul_le_mul_of_nonneg_left hmul (by norm_num)
      _ = 2 * D * |y| := by ring
  calc
    -b * (c * (2 * y)) = c * (2 * (-b * y)) := by ring
    _ ≤ c * (2 * D * |y|) :=
      mul_le_mul_of_nonneg_left htwice hc
    _ ≤ c * (y ^ 2 + D ^ 2) := mul_le_mul_of_nonneg_left hyoung hc

theorem BoundedParabolicUniqueness.positive_barrier_max_impossible {κ D A c y₀ y₁ ρ lap b₀ b₁ : ℝ}
    (hκ : 0 < κ) (hc : 0 < c) (hA : 4 * κ + 2 * D ^ 2 < A)
    (hAone : 1 ≤ A)
    (hρ : ρ = y₀ ^ 2 + y₁ ^ 2) (hρnonneg : 0 ≤ ρ)
    (hlap : lap ≤ 4 * c) (hb₀ : |b₀| ≤ D) (hb₁ : |b₁| ≤ D)
    (heq : A * c * (1 + ρ) =
      κ * lap - (b₀ * (c * (2 * y₀)) + b₁ * (c * (2 * y₁)))) : False := by
  have hcross₀ := BoundedParabolicUniqueness.scalar_drift_absorb (y := y₀) hb₀ hc.le
  have hcross₁ := BoundedParabolicUniqueness.scalar_drift_absorb (y := y₁) hb₁ hc.le
  have hcross :
      -b₀ * (c * (2 * y₀)) - b₁ * (c * (2 * y₁)) ≤ c * (ρ + 2 * D ^ 2) := by
    calc
      -b₀ * (c * (2 * y₀)) - b₁ * (c * (2 * y₁)) =
          (-b₀ * (c * (2 * y₀))) + (-b₁ * (c * (2 * y₁))) := by ring
      _ ≤ c * (y₀ ^ 2 + D ^ 2) + c * (y₁ ^ 2 + D ^ 2) :=
        add_le_add hcross₀ hcross₁
      _ = c * (ρ + 2 * D ^ 2) := by rw [hρ]; ring
  have hdiff : κ * lap ≤ κ * (4 * c) :=
    mul_le_mul_of_nonneg_left hlap hκ.le
  have hmain : A * c * (1 + ρ) ≤ c * (4 * κ + ρ + 2 * D ^ 2) := by
    calc
      A * c * (1 + ρ) = κ * lap +
          (-b₀ * (c * (2 * y₀)) - b₁ * (c * (2 * y₁))) := by
        rw [heq]
        ring
      _ ≤ κ * (4 * c) + c * (ρ + 2 * D ^ 2) := add_le_add hdiff hcross
      _ = c * (4 * κ + ρ + 2 * D ^ 2) := by ring
  have hmain' : c * (A * (1 + ρ)) ≤ c * (4 * κ + ρ + 2 * D ^ 2) := by
    calc
      c * (A * (1 + ρ)) = A * c * (1 + ρ) := by ring
      _ ≤ c * (4 * κ + ρ + 2 * D ^ 2) := hmain
  have hcancel : A * (1 + ρ) ≤ 4 * κ + ρ + 2 * D ^ 2 :=
    (mul_le_mul_iff_of_pos_left hc).mp hmain'
  have hprod : 0 ≤ (A - 1) * ρ :=
    mul_nonneg (by linarith) hρnonneg
  nlinarith only [hA, hAone, hprod, hcancel]

theorem BoundedParabolicUniqueness.parabolicSpatialBox_compact (R : ℝ) :
    IsCompact (BoundedParabolicUniqueness.parabolicSpatialBox R) := by
  simpa [BoundedParabolicUniqueness.parabolicSpatialBox] using
    (isCompact_univ_pi fun _ : Fin 2 => isCompact_Icc)

theorem BoundedParabolicUniqueness.parabolicSpatialBox_mem_of_coord_bounds {R : ℝ} {x : Vec 2}
    (hx : ∀ i : Fin 2, -R ≤ x i ∧ x i ≤ R) :
    BoundedParabolicUniqueness.parabolicSpatialBox R x := by
  change ∀ i ∈ (Set.univ : Set (Fin 2)), x i ∈ Set.Icc (-R) R
  intro i _
  exact Set.mem_Icc.mpr (hx i)

theorem BoundedParabolicUniqueness.spaceGrad_neg_of_contDiff {f : Vec 2 → ℝ} {x : Vec 2}
    (hf : ContDiff ℝ 2 f) (i : Fin 2) :
    spaceGrad (fun y => -f y) x i = -spaceGrad f x i := by
  have h0 : ContDiff ℝ 2 (fun _ : Vec 2 => (0 : ℝ)) := contDiff_const
  have hsub := spaceGrad_sub i
    (h0.differentiable (by norm_num) x) (hf.differentiable (by norm_num) x)
  have heq : (fun y : Vec 2 => 0 - f y) = fun y => -f y := by
    funext y
    ring
  rw [heq] at hsub
  have hgrad0 : spaceGrad (fun _ : Vec 2 => (0 : ℝ)) x i = 0 := by
    simp [spaceGrad, AVenhance.spaceGrad]
  simp only [hgrad0] at hsub
  simpa only [zero_sub] using hsub

theorem BoundedParabolicUniqueness.spaceLap_neg_of_contDiff {f : Vec 2 → ℝ} {x : Vec 2}
    (hf : ContDiff ℝ 2 f) :
    spaceLap (fun y => -f y) x = -spaceLap f x := by
  have h0 : ContDiff ℝ 2 (fun _ : Vec 2 => (0 : ℝ)) := contDiff_const
  have hsub := spaceLap_sub (x := x) h0 hf
  have heq : (fun y : Vec 2 => 0 - f y) = fun y => -f y := by
    funext y
    ring
  rw [heq] at hsub
  have hlap0 : spaceLap (fun _ : Vec 2 => (0 : ℝ)) x = 0 := by
    simp [spaceLap, AVenhance.spaceGrad]
  simp only [hlap0] at hsub
  simpa only [zero_sub] using hsub

theorem BoundedParabolicUniqueness.barrier_compact_max_interior {ε A s T R M t₀ t : ℝ}
    {x : Vec 2} {u : ℝ → Vec 2 → ℝ} {φ : ℝ × Vec 2 → ℝ}
    (hε : 0 < ε) (hA : 0 ≤ A)
    (hbound : ∀ r y, |u r y| ≤ M)
    (hzero : ∀ r, r < t₀ → ∀ y, u r y = 0)
    (hφ : ∀ p, φ p = u p.1 p.2 - parabolicBarrier ε A s p)
    (hφC : ContDiff ℝ 2 φ)
    (hs : s < t₀) (hts : s < t) (htT : t < T)
    (hbox : BoundedParabolicUniqueness.parabolicSpatialBox R x) (hφtarget : 0 < φ (t, x))
    (hside : M < ε * (1 + R ^ 2))
    (htop : M < ε * Real.exp (A * (T - s))) :
    ∃ p ∈ Set.Icc s T ×ˢ BoundedParabolicUniqueness.parabolicSpatialBox R,
      IsMaxOn φ (Set.Icc s T ×ˢ BoundedParabolicUniqueness.parabolicSpatialBox R) p ∧
        0 < φ p ∧ s < p.1 ∧ p.1 < T ∧
        ∀ i : Fin 2, -R < p.2 i ∧ p.2 i < R := by
  have htarget : (t, x) ∈ Set.Icc s T ×ˢ BoundedParabolicUniqueness.parabolicSpatialBox R :=
    ⟨⟨hts.le, htT.le⟩, hbox⟩
  have hK : IsCompact (Set.Icc s T ×ˢ BoundedParabolicUniqueness.parabolicSpatialBox R) :=
    isCompact_Icc.prod (BoundedParabolicUniqueness.parabolicSpatialBox_compact R)
  obtain ⟨p, hp, hmax⟩ := hK.exists_isMaxOn ⟨(t, x), htarget⟩
    hφC.continuous.continuousOn
  have hφmax : 0 < φ p :=
    lt_of_lt_of_le hφtarget ((isMaxOn_iff.mp hmax) (t, x) htarget)
  have hpTime : p.1 ∈ Set.Icc s T := hp.1
  have hpBox : p.2 ∈ BoundedParabolicUniqueness.parabolicSpatialBox R := hp.2
  have hcoordMem (i : Fin 2) : p.2 i ∈ Set.Icc (-R) R := by
    exact (Set.mem_pi.mp hpBox) i (Set.mem_univ i)
  have hφ_nonpos_of_large_radius (hrad : R ^ 2 ≤ parabolicRadialSq p.2) :
      φ p ≤ 0 := by
    have htimeArg : 0 ≤ A * (p.1 - s) :=
      mul_nonneg hA (sub_nonneg.mpr hpTime.1)
    have hexpLower : 1 ≤ Real.exp (A * (p.1 - s)) :=
      Real.one_le_exp htimeArg
    have hbarLower : ε * (1 + R ^ 2) ≤ parabolicBarrier ε A s p := by
      dsimp [parabolicBarrier]
      calc
        ε * (1 + R ^ 2) ≤ ε * (1 + parabolicRadialSq p.2) :=
          mul_le_mul_of_nonneg_left (by linarith) hε.le
        _ = (ε * (1 + parabolicRadialSq p.2)) * 1 := by ring
        _ ≤ (ε * (1 + parabolicRadialSq p.2)) *
            Real.exp (A * (p.1 - s)) :=
          mul_le_mul_of_nonneg_left hexpLower
            (mul_nonneg hε.le (by linarith [(BoundedParabolicUniqueness.parabolicRadialSq_nonneg
                p.2)]))
    have huUpper : u p.1 p.2 ≤ M := le_trans (le_abs_self _) (hbound p.1 p.2)
    rw [hφ]
    linarith
  have hstart_ne : p.1 ≠ s := by
    intro heq
    have hpast : p.1 < t₀ := by rw [heq]; exact hs
    have hu0 := hzero p.1 hpast p.2
    have hpEq : p = (s, p.2) := Prod.ext heq rfl
    have hbarpos : 0 < parabolicBarrier ε A s p := by
      rw [hpEq]
      have hr : 0 ≤ parabolicRadialSq p.2 := BoundedParabolicUniqueness.parabolicRadialSq_nonneg p.2
      dsimp [parabolicBarrier]
      simp only [sub_self, mul_zero, Real.exp_zero, mul_one]
      positivity
    have hφle : φ p < 0 := by rw [hφ, hu0]; linarith
    exact (not_le_of_gt hφmax) hφle.le
  have hT_ne : p.1 ≠ T := by
    intro heq
    have hpEq : p = (T, p.2) := Prod.ext heq rfl
    have hTbar : M < parabolicBarrier ε A s p := by
      rw [hpEq, parabolicBarrier]
      have hfactor : 1 ≤ 1 + parabolicRadialSq p.2 :=
        by linarith [BoundedParabolicUniqueness.parabolicRadialSq_nonneg p.2]
      have hmul : ε * Real.exp (A * (T - s)) ≤
          ε * (1 + parabolicRadialSq p.2) * Real.exp (A * (T - s)) := by
        calc
          ε * Real.exp (A * (T - s)) =
              (ε * Real.exp (A * (T - s))) * 1 := by ring
          _ ≤ (ε * Real.exp (A * (T - s))) *
                (1 + parabolicRadialSq p.2) :=
              mul_le_mul_of_nonneg_left hfactor (by positivity)
          _ = ε * (1 + parabolicRadialSq p.2) *
                Real.exp (A * (T - s)) := by ring
      exact lt_of_lt_of_le htop hmul
    have huUpper : u p.1 p.2 ≤ M := le_trans (le_abs_self _) (hbound p.1 p.2)
    have hφle : φ p < 0 := by rw [hφ]; linarith
    exact (not_le_of_gt hφmax) hφle.le
  have hpTimeOpen : s < p.1 ∧ p.1 < T := by
    constructor
    · exact lt_of_le_of_ne hpTime.1 (Ne.symm hstart_ne)
    · exact lt_of_le_of_ne hpTime.2 hT_ne
  have hcoordOpen (i : Fin 2) : -R < p.2 i ∧ p.2 i < R := by
    have hmem := hcoordMem i
    constructor
    · by_contra hnot
      have heq : p.2 i = -R := le_antisymm (not_lt.mp hnot) hmem.1
      have hsq : (p.2 i) ^ 2 = R ^ 2 := by rw [heq]; ring
      have hrad : R ^ 2 ≤ parabolicRadialSq p.2 := by
        calc
          R ^ 2 = p.2 i ^ 2 := hsq.symm
          _ ≤ parabolicRadialSq p.2 := BoundedParabolicUniqueness.coord_sq_le_parabolicRadialSq
              p.2 i
      exact (not_le_of_gt hφmax) (hφ_nonpos_of_large_radius hrad)
    · by_contra hnot
      have heq : p.2 i = R := le_antisymm hmem.2 (not_lt.mp hnot)
      have hsq : (p.2 i) ^ 2 = R ^ 2 := by rw [heq]
      have hrad : R ^ 2 ≤ parabolicRadialSq p.2 := by
        calc
          R ^ 2 = p.2 i ^ 2 := hsq.symm
          _ ≤ parabolicRadialSq p.2 := BoundedParabolicUniqueness.coord_sq_le_parabolicRadialSq
              p.2 i
      exact (not_le_of_gt hφmax) (hφ_nonpos_of_large_radius hrad)
  exact ⟨p, hp, hmax, hφmax, hpTimeOpen.1, hpTimeOpen.2, hcoordOpen⟩

private theorem BoundedParabolicUniqueness.boundedParabolic_le_zero_boxTarget1 :
  ∀ {κ D M t₀ : ℝ} {u : ℝ → Vec (2 : ℕ) → ℝ} (t : ℝ) (x : Vec (2 : ℕ)),
  let s : ℝ := t₀ - (1 : ℝ);
  let A : ℝ := (4 : ℝ) * κ + (2 : ℝ) * D ^ (2 : ℕ) + (1 : ℝ);
  let r : ℝ := parabolicRadialSq x;
  let den : ℝ := (2 : ℝ) * Real.exp (A * (t - s)) * ((1 : ℝ) + r);
  let ε : ℝ := u t x / den;
  let Moverε : ℝ := M / ε;
  let R : ℝ := Moverε + |x (0 : Fin (2 : ℕ))| + |x (1 : Fin (2 : ℕ))| + (3 : ℝ);
  (0 : ℝ) ≤ Moverε → parabolicSpatialBox R x
    := by
  intro κ D M t₀ u t x s A r den ε Moverε R hMoverε
  have hAbs0 : |x 0| < R := by
    dsimp [R]
    linarith only [hMoverε, abs_nonneg (x 1)]
  have hAbs1 : |x 1| < R := by
    dsimp [R]
    linarith only [hMoverε, abs_nonneg (x 0)]
  have h0 := abs_lt.mp hAbs0
  have h1 := abs_lt.mp hAbs1
  have hcoord : ∀ i : Fin 2, -R ≤ x i ∧ x i ≤ R := by
    intro i
    fin_cases i
    · simpa using (show -R ≤ x 0 ∧ x 0 ≤ R from
        ⟨le_of_lt h0.1, le_of_lt h0.2⟩)
    · simpa using (show -R ≤ x 1 ∧ x 1 ≤ R from
        ⟨le_of_lt h1.1, le_of_lt h1.2⟩)
  apply BoundedParabolicUniqueness.parabolicSpatialBox_mem_of_coord_bounds
  exact hcoord

/-- A bounded classical solution of a uniformly parabolic equation with
bounded drift, which vanishes on an initial half-line, is identically zero.
The proof uses an exponential quadratic barrier on an expanding finite box. -/
theorem BoundedParabolicUniqueness.boundedParabolic_le_zero {κ D M t₀ : ℝ} {u : ℝ → Vec 2 → ℝ}
    {b : ℝ → Vec 2 → Fin 2 → ℝ}
    (hκ : 0 < κ) (hM : 0 ≤ M)
    (hbound : ∀ t x, |u t x| ≤ M)
    (hb : ∀ t x i, |b t x i| ≤ D)
    (hC : ContDiff ℝ 2 (fun p : ℝ × Vec 2 => u p.1 p.2))
    (hzero : ∀ t, t < t₀ → ∀ x, u t x = 0)
    (hpde : ∀ t x,
      deriv (fun s => u s x) t =
        κ * spaceLap (u t) x -
          ∑ i : Fin 2, b t x i * spaceGrad (u t) x i) :
    ∀ t x, u t x ≤ 0 := by
  have hle_zero (t : ℝ) (x : Vec 2) : u t x ≤ 0 := by
    by_cases ht : t < t₀
    · rw [hzero t ht x]
    · have htt₀ : t₀ ≤ t := le_of_not_gt ht
      by_contra hnot
      have huPos : 0 < u t x := lt_of_not_ge hnot
      let s := t₀ - 1
      let A := 4 * κ + 2 * D ^ 2 + 1
      have hs_lt_t₀ : s < t₀ := by dsimp [s]; linarith
      have hs_lt_t : s < t := hs_lt_t₀.trans_le htt₀
      have hA : 0 < A := by dsimp [A]; positivity
      have hA_large : 4 * κ + 2 * D ^ 2 < A := by dsimp [A]; linarith
      let r := parabolicRadialSq x
      have hr_nonneg : 0 ≤ r := BoundedParabolicUniqueness.parabolicRadialSq_nonneg x
      have hfactor : 0 < 1 + r := by linarith
      have hexp : 0 < Real.exp (A * (t - s)) := Real.exp_pos _
      let den := 2 * Real.exp (A * (t - s)) * (1 + r)
      have hden : 0 < den := by dsimp [den]; positivity
      let ε := u t x / den
      have hε : 0 < ε := by dsimp [ε]; exact div_pos huPos hden
      have htargetBarrier : parabolicBarrier ε A s (t, x) = u t x / 2 := by
        dsimp [parabolicBarrier, ε, den, r]
        field_simp [ne_of_gt hexp, ne_of_gt hfactor]
        exact div_self (ne_of_gt hfactor)
      let Moverε := M / ε
      let R := Moverε + |x 0| + |x 1| + 3
      have hMoverε : 0 ≤ Moverε := by dsimp [Moverε]; exact div_nonneg hM hε.le
      have hRlo : Moverε + 3 ≤ R := by
        dsimp [R]
        linarith only [abs_nonneg (x 0), abs_nonneg (x 1)]
      have hRpos : 0 < R := by linarith only [hRlo, hMoverε]
      have hRlarge : M < ε * R := by
        have hratio : M = ε * Moverε := by
          dsimp [Moverε]
          field_simp
        rw [hratio]
        apply (mul_lt_mul_iff_of_pos_left hε).2
        dsimp [R]
        linarith only [abs_nonneg (x 0), abs_nonneg (x 1)]
      have hRge1 : 1 ≤ R := by linarith only [hRlo, hMoverε]
      have hRsq : R ≤ R ^ 2 := by
        simpa only [mul_one, pow_two] using mul_le_mul_of_nonneg_left hRge1 hRpos.le
      have hRBarrier : M < ε * (1 + R ^ 2) := by
        calc
          M < ε * R := hRlarge
          _ ≤ ε * R ^ 2 := mul_le_mul_of_nonneg_left hRsq hε.le
          _ ≤ ε * (1 + R ^ 2) :=
            mul_le_mul_of_nonneg_left (le_add_of_nonneg_left zero_le_one) hε.le
      have hq : 0 < Moverε + A * (t - s) + 2 := by
        have htime : 0 < t - s := sub_pos.mpr hs_lt_t
        dsimp [Moverε]
        positivity
      let q := Moverε + A * (t - s) + 2
      let T := s + q / A
      have hq_gt_time : A * (t - s) < q := by
        dsimp [q]
        have htime : 0 ≤ A * (t - s) :=
          mul_nonneg hA.le (sub_nonneg.mpr hs_lt_t.le)
        have hMdiv : 0 ≤ M / ε := div_nonneg hM hε.le
        linarith
      have ht_lt_T : t < T := by
        have hmul : (t - s) * A < q := by simpa only [mul_comm] using hq_gt_time
        have hquot : t - s < q / A := (lt_div_iff₀ hA).2 hmul
        dsimp [T]
        linarith
      have hTminus : T - s = q / A := by dsimp [T]; ring
      have hTexp : A * (T - s) = q := by
        rw [hTminus]
        exact mul_div_cancel₀ q (ne_of_gt hA)
      have hM_lt_eps_exp : M < ε * Real.exp q := by
        have hlin : M / ε < q + 1 := by
          dsimp [q, Moverε]
          have htime : 0 ≤ A * (t - s) :=
            mul_nonneg hA.le (sub_nonneg.mpr hs_lt_t.le)
          linarith
        have hmul : M < ε * (q + 1) := by
          simpa only [mul_comm] using (div_lt_iff₀ hε).mp hlin
        calc
          M < ε * (q + 1) := hmul
          _ ≤ ε * Real.exp q := mul_le_mul_of_nonneg_left
              (Real.add_one_le_exp q) hε.le
      let φ : ℝ × Vec 2 → ℝ := fun p =>
        u p.1 p.2 - parabolicBarrier ε A s p
      have hφdef (p : ℝ × Vec 2) :
          φ p = u p.1 p.2 - parabolicBarrier ε A s p := rfl
      have hφC : ContDiff ℝ 2 φ := by
        dsimp [φ]
        have hbar : ContDiff ℝ 2 (parabolicBarrier ε A s) := by
          unfold parabolicBarrier parabolicRadialSq
          fun_prop
        exact hC.sub hbar
      have hφTarget : 0 < φ (t, x) := by
        dsimp [φ]
        rw [htargetBarrier]
        linarith
      have hboxTarget : BoundedParabolicUniqueness.parabolicSpatialBox R x := by
        exact @BoundedParabolicUniqueness.boundedParabolic_le_zero_boxTarget1 κ D M t₀ u t x hMoverε
      have htop : M < ε * Real.exp (A * (T - s)) := by
        rw [hTexp]
        exact hM_lt_eps_exp
      obtain ⟨p, hp, hmax, hφMax, hps, hpT, hcoordOpen⟩ :=
        BoundedParabolicUniqueness.barrier_compact_max_interior hε hA.le hbound hzero hφdef hφC
          hs_lt_t₀ hs_lt_t ht_lt_T hboxTarget hφTarget hRBarrier htop
      have htimeN : Set.Icc s T ∈ 𝓝 p.1 := Icc_mem_nhds hps hpT
      have hboxN : BoundedParabolicUniqueness.parabolicSpatialBox R ∈ 𝓝 p.2 :=
        by
          simpa [BoundedParabolicUniqueness.parabolicSpatialBox] using
            (pi_Icc_mem_nhds (fun i => (hcoordOpen i).1)
              (fun i => (hcoordOpen i).2))
      have hKN : (Set.Icc s T ×ˢ BoundedParabolicUniqueness.parabolicSpatialBox R) ∈ 𝓝 p :=
        prod_mem_nhds htimeN hboxN
      have hlocal := hmax.isLocalMax hKN
      have hfacts := spaceTime_local_max_derivative_facts hφC hlocal
      let c := ε * Real.exp (A * (p.1 - s))
      have hc : 0 < c := by dsimp [c]; positivity
      have hshape : (fun y : Vec 2 => parabolicBarrier ε A s (p.1, y)) =
          fun y => c * (1 + parabolicRadialSq y) := by
        funext y
        simp [parabolicBarrier, c, mul_comm, mul_assoc]
      have huSpaceC : ContDiff ℝ 2 (u p.1) := by
        change ContDiff ℝ 2 (fun y : Vec 2 => u p.1 y)
        exact hC.comp (contDiff_const.prodMk contDiff_id)
      have hbarSpaceC : ContDiff ℝ 2 (fun y : Vec 2 =>
          parabolicBarrier ε A s (p.1, y)) := by
        change ContDiff ℝ 2 (fun y : Vec 2 =>
          ε * (1 + (y 0 ^ 2 + y 1 ^ 2)) * Real.exp (A * (p.1 - s)))
        fun_prop
      have huTimeC : ContDiff ℝ 2 (fun r : ℝ => u r p.2) := by
        exact hC.comp (contDiff_id.prodMk contDiff_const)
      have hbarTimeC : ContDiff ℝ 2 (fun r : ℝ =>
          parabolicBarrier ε A s (r, p.2)) := by
        change ContDiff ℝ 2 (fun r : ℝ =>
          ε * (1 + parabolicRadialSq p.2) * Real.exp (A * (r - s)))
        fun_prop
      have htimeEq : deriv (fun r => u r p.2) p.1 =
          deriv (fun r => parabolicBarrier ε A s (r, p.2)) p.1 := by
        have h := hfacts.1
        change deriv (fun r => u r p.2 - parabolicBarrier ε A s (r, p.2))
          p.1 = 0 at h
        rw [deriv_fun_sub (huTimeC.differentiable (by norm_num) p.1)
          (hbarTimeC.differentiable (by norm_num) p.1)] at h
        linarith
      have hgradEq (i : Fin 2) :
          spaceGrad (u p.1) p.2 i =
            spaceGrad (fun y => parabolicBarrier ε A s (p.1, y)) p.2 i := by
        have h := hfacts.2.1 i
        change spaceGrad (fun y => u p.1 y - parabolicBarrier ε A s (p.1, y))
          p.2 i = 0 at h
        rw [spaceGrad_sub i
          (huSpaceC.differentiable (by norm_num) p.2)
          (hbarSpaceC.differentiable (by norm_num) p.2)] at h
        linarith
      have hlapLe : spaceLap (u p.1) p.2 ≤
          spaceLap (fun y => parabolicBarrier ε A s (p.1, y)) p.2 := by
        have h := hfacts.2.2
        change spaceLap (fun y => u p.1 y - parabolicBarrier ε A s (p.1, y))
          p.2 ≤ 0 at h
        rw [spaceLap_sub huSpaceC hbarSpaceC] at h
        linarith
      have hgradBarrier (i : Fin 2) :
          spaceGrad (fun y => parabolicBarrier ε A s (p.1, y)) p.2 i =
            c * (2 * p.2 i) := by
        rw [hshape, spaceGrad_constantRadialSq]
      have hlapBarrier :
          spaceLap (fun y => parabolicBarrier ε A s (p.1, y)) p.2 = 4 * c := by
        rw [hshape, spaceLap_constantRadialSq]
      have htimeBarrier :
          deriv (fun r => parabolicBarrier ε A s (r, p.2)) p.1 =
            A * c * (1 + parabolicRadialSq p.2) := by
        rw [parabolicBarrier_time_deriv]
        dsimp [c]
        ring
      have hpdeAt := hpde p.1 p.2
      simp only [Fin.sum_univ_two] at hpdeAt
      rw [htimeEq, hgradEq 0, hgradEq 1,
        htimeBarrier, hgradBarrier 0, hgradBarrier 1] at hpdeAt
      have hlap : spaceLap (u p.1) p.2 ≤ 4 * c := by
        calc
          spaceLap (u p.1) p.2 ≤
              spaceLap (fun y => parabolicBarrier ε A s (p.1, y)) p.2 := hlapLe
          _ = 4 * c := hlapBarrier
      have hrho : parabolicRadialSq p.2 = p.2 0 ^ 2 + p.2 1 ^ 2 := rfl
      have hAone : 1 ≤ A := by
        dsimp [A]
        have hB : 0 ≤ 4 * κ + 2 * D ^ 2 := by positivity
        linarith [hB]
      exact BoundedParabolicUniqueness.positive_barrier_max_impossible hκ hc hA_large hAone hrho
        (BoundedParabolicUniqueness.parabolicRadialSq_nonneg p.2) hlap (hb p.1 p.2 0) (hb p.1 p.2 1)
        (by simpa [parabolicRadialSq] using hpdeAt)
  exact hle_zero

/-- A bounded classical solution with zero past of a uniformly parabolic
equation with bounded drift vanishes everywhere. -/
theorem boundedParabolic_eq_zero {κ D M t₀ : ℝ} {u : ℝ → Vec 2 → ℝ}
    {b : ℝ → Vec 2 → Fin 2 → ℝ}
    (hκ : 0 < κ) (hM : 0 ≤ M)
    (hbound : ∀ t x, |u t x| ≤ M)
    (hb : ∀ t x i, |b t x i| ≤ D)
    (hC : ContDiff ℝ 2 (fun p : ℝ × Vec 2 => u p.1 p.2))
    (hzero : ∀ t, t < t₀ → ∀ x, u t x = 0)
    (hpde : ∀ t x,
      deriv (fun s => u s x) t =
        κ * spaceLap (u t) x -
          ∑ i : Fin 2, b t x i * spaceGrad (u t) x i) :
    ∀ t x, u t x = 0 := by
  have hspaceC (t : ℝ) : ContDiff ℝ 2 (fun x : Vec 2 => u t x) := by
    exact hC.comp (contDiff_const.prodMk contDiff_id)
  have hle := BoundedParabolicUniqueness.boundedParabolic_le_zero hκ hM hbound hb hC hzero hpde
  have hnegBound : ∀ t x, |-(u t x)| ≤ M := by
    intro t x
    simpa only [abs_neg] using hbound t x
  have hnegZero : ∀ t, t < t₀ → ∀ x, -(u t x) = 0 := by
    intro t ht x
    rw [hzero t ht x]
    simp
  have hnegPDE : ∀ t x,
      deriv (fun s => -(u s x)) t =
        κ * spaceLap (fun y => -(u t y)) x -
          ∑ i : Fin 2, b t x i * spaceGrad (fun y => -(u t y)) x i := by
    intro t x
    have hlap := BoundedParabolicUniqueness.spaceLap_neg_of_contDiff (hspaceC t) (x := x)
    have hgrad (i : Fin 2) :=
      BoundedParabolicUniqueness.spaceGrad_neg_of_contDiff (hspaceC t) (x := x) i
    have hfun : (fun s : ℝ => -u s x) = -(fun s => u s x) := by
      funext s
      rfl
    rw [hfun, deriv.neg, hpde t x, hlap]
    simp only [Fin.sum_univ_two]
    rw [hgrad 0, hgrad 1]
    ring
  have hnegC : ContDiff ℝ 2 (fun p : ℝ × Vec 2 => -(u p.1 p.2)) := hC.neg
  have hge := BoundedParabolicUniqueness.boundedParabolic_le_zero hκ hM hnegBound hb hnegC
      hnegZero hnegPDE
  intro t x
  have h₁ := hle t x
  have h₂ := hge t x
  linarith

end AVenhance.Infra.Section3
