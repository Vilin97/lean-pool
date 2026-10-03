/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section4.Amnr.Calculus

/-! Induction infrastructure for the AMNR tensors. -/

@[expose] public section

noncomputable section
open Homogenization MeasureTheory
namespace AVenhance.Infra.Section4

/-- Finite-order regularity propagated by the contraction recurrence. The
premises describe its primitive factors and defining identities, not A bounds. -/
theorem amnrRec_contDiffOn {U : Set AmnrSpace} (hU : IsOpen U)
    {N : ℕ} {b : AmnrSpace → Vec 2} (hb : ContDiffOn ℝ N b U)
    {B f : Fin 2 → Fin 2 → AmnrSpace → ℝ} {g : Fin 2 → AmnrSpace → ℝ}
    (hB : ∀ i p, ContDiffOn ℝ N (B i p) U)
    (hf : ∀ i p, ContDiffOn ℝ N (f i p) U)
    (hg : ∀ p, ContDiffOn ℝ N (g p) U)
    {A : ℕ → Fin 2 → AmnrSpace → ℝ}
    (hzero : ∀ i, Set.EqOn (A 0 i) (fun z => ∑ p, f i p z * g p z) U)
    (hrec : ∀ r, r < N → ∀ i, Set.EqOn (A (r + 1) i)
      (fun z => amnrOp b none (A r i) z - ∑ p, B i p z * A r p z) U)
    {r n : ℕ} (hr : n + r ≤ N) (i : Fin 2) : ContDiffOn ℝ n (A r i) U := by
  induction r generalizing n i with
  | zero =>
    apply (ContDiffOn.sum (fun p _ =>
      ((hf i p).mul (hg p)).of_le (by exact_mod_cast (by omega : n ≤ N)))).congr
    exact hzero i
  | succ r ih =>
    have hprev := ih (n := n + 1) (by omega) i
    have hmat := (amnrWord_contDiffOn hU
      (hb.of_le (by exact_mod_cast (by omega : n + 1 ≤ N))) hprev [none]
      (n := n) (by simp)).sub (ContDiffOn.sum (s := Finset.univ) (fun p _ =>
        ((hB i p).of_le (by exact_mod_cast (by omega : n ≤ N))).mul
          (ih (n := n) (by omega) p)))
    exact hmat.congr (hrec r (by omega) i)

/-- Differentiated recurrence for ordered words, with finite-order regularity
proved from the primitive seed. -/
theorem amnrRec_word_succ {U : Set AmnrSpace} (hU : IsOpen U)
    {N : ℕ} {b : AmnrSpace → Vec 2} (hb : ContDiffOn ℝ N b U)
    {B f : Fin 2 → Fin 2 → AmnrSpace → ℝ} {g : Fin 2 → AmnrSpace → ℝ}
    (hB : ∀ i p, ContDiffOn ℝ N (B i p) U)
    (hf : ∀ i p, ContDiffOn ℝ N (f i p) U)
    (hg : ∀ p, ContDiffOn ℝ N (g p) U)
    {A : ℕ → Fin 2 → AmnrSpace → ℝ}
    (hzero : ∀ i, Set.EqOn (A 0 i) (fun z => ∑ p, f i p z * g p z) U)
    (hrec : ∀ r, r < N → ∀ i, Set.EqOn (A (r + 1) i)
      (fun z => amnrOp b none (A r i) z - ∑ p, B i p z * A r p z) U)
    (r : ℕ) (w : List (Option (Fin 2))) (hw : w.length + (r + 1) ≤ N)
    (i : Fin 2) : Set.EqOn (amnrWord b w (A (r + 1) i))
      (fun z => amnrWord b (w ++ [none]) (A r i) z -
        ∑ p, amnrWord b w (B i p * A r p) z) U := by
  let M := N - (r + 1)
  have hbM : ContDiffOn ℝ M b U := hb.of_le (by exact_mod_cast Nat.sub_le N (r + 1))
  have hAi : ContDiffOn ℝ (M + 1) (A r i) U :=
    amnrRec_contDiffOn hU hb hB hf hg hzero hrec (by dsimp [M]; omega) i
  have hD : ContDiffOn ℝ M (amnrOp b none (A r i)) U :=
    amnrWord_contDiffOn hU (hb.of_le (by exact_mod_cast (by dsimp [M]; omega : M + 1 ≤ N)))
      hAi [none] (by simp)
  have hP (p : Fin 2) : ContDiffOn ℝ M (B i p * A r p) U :=
    ((hB i p).of_le (by exact_mod_cast Nat.sub_le N (r + 1))).mul
      (amnrRec_contDiffOn hU hb hB hf hg hzero hrec (by dsimp [M]; omega) p)
  have hsum : ContDiffOn ℝ M (∑ p : Fin 2, B i p * A r p) U := by
    simpa only [Finset.sum_fn] using ContDiffOn.sum (fun p _ => hP p)
  intro z hz
  have hcon := amnrWord_congr hU (b := b) (hrec r (by omega) i) w hz
  change _ = amnrWord b w (amnrOp b none (A r i) - ∑ p : Fin 2, B i p * A r p) z at hcon
  rw [hcon, amnrWord_sub hU hbM hD hsum w (by dsimp [M]; omega) hz]
  have hS := amnrWord_sum hU hbM Finset.univ (fun p => B i p * A r p)
    (fun p _ => hP p) w (by dsimp [M]; omega) hz
  simp only [amnrWord_append, amnrWord, Finset.sum_apply, Pi.sub_apply] at *
  rw [hS]

/-- A two-coordinate contraction costs at most `2^(N+1)` Leibniz terms.
The smoothness order M can decrease along the recursion while N stays fixed. -/
theorem amnrWord_sum_mul_L2_le {U : Set AmnrSpace} (hU : IsOpen U)
    {μ : Measure AmnrSpace} (hμ : μ ≪ volume.restrict U)
    {b : AmnrSpace → Vec 2} {M N : ℕ} (hMN : M ≤ N)
    (hb : ContDiffOn ℝ M b U) {f g : Fin 2 → AmnrSpace → ℝ}
    (hf : ∀ p, ContDiffOn ℝ M (f p) U) (hg : ∀ p, ContDiffOn ℝ M (g p) U)
    {S H F G : ℝ} (hS : 0 ≤ S) (hH : 0 ≤ H) (hF : 0 ≤ F) (hG : 0 ≤ G)
    (w : List (Option (Fin 2))) (hw : amnrBudget w ≤ M)
    (hfb : ∀ p v, v.Sublist w → ∀ z ∈ U,
      |amnrWord b v (f p) z| ≤ F * amnrWeight S H v)
    (hgb : ∀ p v, v.Sublist w → eLpNorm (amnrWord b v (g p)) 2 μ ≤
      ENNReal.ofReal (G * amnrWeight S H v)) :
    eLpNorm (amnrWord b w (fun z => ∑ p, f p z * g p z)) 2 μ ≤
      ENNReal.ofReal ((2 : ℝ) ^ (N + 1) * F * G * amnrWeight S H w) := by
  have hlen := (amnrBudget_length_le w).trans hw
  have heq : amnrWord b w (fun z => ∑ p, f p z * g p z) =ᵐ[μ]
      ∑ p : Fin 2, amnrWord b w (f p * g p) := by
    apply ((ae_restrict_mem hU.measurableSet).filter_mono hμ.ae_le).mono
    intro z hz
    have hh := amnrWord_sum hU hb Finset.univ (fun p => f p * g p)
      (fun p _ => (hf p).mul (hg p)) w hlen hz
    simpa only [Finset.sum_fn, Pi.mul_apply] using hh
  rw [eLpNorm_congr_ae heq]
  have hp (p : Fin 2) := amnrWord_mul_L2_le hU hμ hb (hf p) (hg p)
    hS hH hF hG w hw (hfb p) (hgb p)
  have hpow : (2 : ℝ) ^ w.length ≤ 2 ^ N :=
    pow_le_pow_right₀ (by norm_num) (hlen.trans hMN)
  have hterm (p : Fin 2) : eLpNorm (amnrWord b w (f p * g p)) 2 μ ≤
      ENNReal.ofReal (2 ^ N * F * G * amnrWeight S H w) := by
    refine (hp p).trans (ENNReal.ofReal_le_ofReal ?_)
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hpow hF) hG)
        (amnrWeight_nonneg hS hH w)
  refine (eLpNorm_sum_le (by norm_num : (1 : ENNReal) ≤ 2)).trans
    ((Finset.sum_le_sum (fun p _ => hterm p)).trans_eq ?_)
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (by positivity)]
  congr 1
  rw [pow_succ]
  norm_num
  ring

/-- Taking a subword cannot increase its weighted regularity budget. -/
theorem amnrBudget_sublist {v w : List (Option (Fin 2))} (h : v.Sublist w) :
    amnrBudget v ≤ amnrBudget w := by
  unfold amnrBudget
  exact (h.map _).sum_le_sum (by intro a ha; exact Nat.zero_le a)

/-- The complete higher mixed-derivative contraction induction. The seed is
estimated from its primitive coefficient and gradient factors; no A bound is a
premise. The order budget is checked in the base, the material shift, and every
Leibniz factor at every level. -/
theorem amnrRec_mixed_L2_le {U : Set AmnrSpace} (hU : IsOpen U)
    {μ : Measure AmnrSpace} (hμ : μ ≪ volume.restrict U)
    {N : ℕ} {b : AmnrSpace → Vec 2} (hb : ContDiffOn ℝ N b U)
    {B f : Fin 2 → Fin 2 → AmnrSpace → ℝ} {g : Fin 2 → AmnrSpace → ℝ}
    (hB : ∀ i p, ContDiffOn ℝ N (B i p) U)
    (hf : ∀ i p, ContDiffOn ℝ N (f i p) U) (hg : ∀ p, ContDiffOn ℝ N (g p) U)
    {A : ℕ → Fin 2 → AmnrSpace → ℝ}
    (hzero : ∀ i, Set.EqOn (A 0 i) (fun z => ∑ p, f i p z * g p z) U)
    (hrec : ∀ r, r < N → ∀ i, Set.EqOn (A (r + 1) i)
      (fun z => amnrOp b none (A r i) z - ∑ p, B i p z * A r p z) U)
    {S H F G Cb : ℝ} (hS : 0 ≤ S) (hH : 0 ≤ H)
    (hF : 0 ≤ F) (hG : 0 ≤ G) (hCb : 0 ≤ Cb)
    (hfb : ∀ i p w, IsAmnrMixedWord w → amnrBudget w ≤ N → ∀ z ∈ U,
      |amnrWord b w (f i p) z| ≤ F * amnrWeight S H w)
    (hgb : ∀ p w, IsAmnrMixedWord w → amnrBudget w ≤ N →
      eLpNorm (amnrWord b w (g p)) 2 μ ≤ ENNReal.ofReal (G * amnrWeight S H w))
    (hBb : ∀ i p w, IsAmnrMixedWord w → amnrBudget w + 2 ≤ N → ∀ z ∈ U,
      |amnrWord b w (B i p) z| ≤ Cb * H * amnrWeight S H w)
    (r : ℕ) (w : List (Option (Fin 2))) (hw : IsAmnrMixedWord w)
    (hbudget : amnrBudget w + 2 * r ≤ N) (i : Fin 2) :
    eLpNorm (amnrWord b w (A r i)) 2 μ ≤
      ENNReal.ofReal ((2 : ℝ) ^ (N + 1) * F * G *
        (1 + 2 ^ (N + 1) * Cb) ^ r * H ^ r * amnrWeight S H w) := by
  let D : ℝ := 2 ^ (N + 1)
  let K : ℝ := D * F * G
  let R : ℝ := 1 + D * Cb
  have hD : 0 ≤ D := by positivity
  have hK : 0 ≤ K := mul_nonneg (mul_nonneg hD hF) hG
  have hR : 0 ≤ R := add_nonneg zero_le_one (mul_nonneg hD hCb)
  change _ ≤ ENNReal.ofReal (K * R ^ r * H ^ r * amnrWeight S H w)
  induction r generalizing w i with
  | zero =>
    have hwb : amnrBudget w ≤ N := by omega
    have heq : amnrWord b w (A 0 i) =ᵐ[μ]
        amnrWord b w (fun z => ∑ p, f i p z * g p z) := by
      apply ((ae_restrict_mem hU.measurableSet).filter_mono hμ.ae_le).mono
      intro z hz
      exact amnrWord_congr hU (b := b) (hzero i) w hz
    rw [eLpNorm_congr_ae heq]
    simp only [pow_zero, mul_one]
    apply amnrWord_sum_mul_L2_le hU hμ le_rfl hb (hf i) hg hS hH hF hG w hwb
    · intro p v hv
      exact hfb i p v (hw.sublist hv) (by
        exact (amnrBudget_sublist hv).trans hwb)
    · intro p v hv
      exact hgb p v (hw.sublist hv) ((amnrBudget_sublist hv).trans hwb)
  | succ r ih =>
    have hbnext := amnrLevelBudget hbudget
    have hlen := amnrBudget_length_le w
    have hword := amnrRec_word_succ hU hb hB hf hg hzero hrec r w (by omega) i
    have heq : amnrWord b w (A (r + 1) i) =ᵐ[μ]
        (fun z => amnrWord b (w ++ [none]) (A r i) z -
          ∑ p, amnrWord b w (B i p * A r p) z) := by
      apply ((ae_restrict_mem hU.measurableSet).filter_mono hμ.ae_le).mono
      exact fun z hz => hword hz
    rw [eLpNorm_congr_ae heq]
    have hm := ih (w ++ [none]) hw.material hbnext.1 i
    have hweight : amnrWeight S H (w ++ [none]) = amnrWeight S H w * H := by
      simp [amnrWeight]
    rw [hweight] at hm
    let M := N - r
    have hbM : ContDiffOn ℝ M b U := hb.of_le (by exact_mod_cast Nat.sub_le N r)
    have hAr (p : Fin 2) : ContDiffOn ℝ M (A r p) U :=
      amnrRec_contDiffOn hU hb hB hf hg hzero hrec (by dsimp [M]; omega) p
    have hBM (p : Fin 2) : ContDiffOn ℝ M (B i p) U :=
      (hB i p).of_le (by exact_mod_cast Nat.sub_le N r)
    have hmul := amnrWord_sum_mul_L2_le hU hμ (Nat.sub_le N r) hbM hBM hAr
      hS hH (mul_nonneg hCb hH) (mul_nonneg (mul_nonneg hK (pow_nonneg hR r))
        (pow_nonneg hH r)) w (by omega)
      (fun p v hv => hBb i p v (hw.sublist hv) (by
        have hvb := amnrBudget_sublist hv; omega))
      (fun p v hv => ih v (hw.sublist hv) (by
        have hvb := amnrBudget_sublist hv; omega) p)
    have hsumEq : amnrWord b w (fun z => ∑ p, B i p z * A r p z) =ᵐ[μ]
        (fun z => ∑ p, amnrWord b w (B i p * A r p) z) := by
      apply ((ae_restrict_mem hU.measurableSet).filter_mono hμ.ae_le).mono
      intro z hz
      simpa only [Finset.sum_fn, Pi.mul_apply] using
        amnrWord_sum hU hbM Finset.univ (fun p => B i p * A r p)
          (fun p _ => (hBM p).mul (hAr p)) w (by dsimp [M]; omega) hz
    rw [eLpNorm_congr_ae hsumEq] at hmul
    refine (eLpNorm_sub_le (by norm_num : (1 : ENNReal) ≤ 2)).trans
      ((add_le_add hm hmul).trans_eq ?_)
    have hW := amnrWeight_nonneg hS hH w
    rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
    congr 1
    dsimp [D, K, R] at *
    rw [pow_succ, pow_succ]
    ring

/-- Coordinate version of `∇^k D^ℓ`: all k spatial letters are outside the
ℓ material letters. No commutation of these operators is asserted. -/
def amnrMixedWord (α : List (Fin 2)) (ℓ : ℕ) : List (Option (Fin 2)) :=
  α.map some ++ List.replicate ℓ none

theorem amnrMixedWord_mixed (α : List (Fin 2)) (ℓ : ℕ) :
    IsAmnrMixedWord (amnrMixedWord α ℓ) := by
  unfold IsAmnrMixedWord amnrMixedWord
  apply List.pairwise_append.mpr
  refine ⟨?_, ?_, ?_⟩
  · apply List.pairwise_map.mpr
    exact List.pairwise_of_forall (by simp)
  · exact List.pairwise_replicate.mpr (by simp)
  · simp

theorem amnrMixedWord_budget (α : List (Fin 2)) (ℓ : ℕ) :
    amnrBudget (amnrMixedWord α ℓ) = α.length + 2 * ℓ := by
  unfold amnrMixedWord
  rw [amnrBudget_append]
  simp [amnrBudget, List.map_map, List.sum_replicate, Nat.mul_comm, Function.comp_def]

theorem amnrMixedWord_weight (S H : ℝ) (α : List (Fin 2)) (ℓ : ℕ) :
    amnrWeight S H (amnrMixedWord α ℓ) = S ^ α.length * H ^ ℓ := by
  simp [amnrMixedWord, amnrWeight, List.map_map, Function.comp_def]

end AVenhance.Infra.Section4
