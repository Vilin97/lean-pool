/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.NavierStokes.PeriodizedWaveBounds
public import LeanPool.NavierStokesAndEuler.NavierStokes.UniformPrimaryWeights
import Mathlib.Analysis.Calculus.ContDiff.Bounds

/-!
# Uniform native-cell bounds for actual signed coefficients

The constants in every `LocalJets` conclusion precede both band and copy.
The input functions need smoothness and jets only on their own native cells.
The matrix inverse, signed square-root quotient and projected pressure are
computed from the primitive input functions.
-/

@[expose] public section


noncomputable section

namespace NavierStokes.SignedCopyBounds

open Set Function Filter WeightedClasses PeriodizedWaveBounds
open scoped ContDiff Topology BigOperators

variable {D E F G I : Type} [NormedAddCommGroup D] [NormedSpace ℝ D]
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [NormedAddCommGroup G] [NormedSpace ℝ G]

private theorem nat_le_infty (m : ℕ) : (m : WithTop ℕ∞) ≤ ∞ :=
  WithTop.coe_le_coe.mpr le_top

/-- The quantitative chain rule needs only the actual finite jet at the
point. No common smooth extension of the native copies is required. -/
theorem comp_jet_bound_at {f : D → ℝ} {g : ℝ → ℝ} {x : D}
    (hf : ContDiffAt ℝ ∞ f x) (hg : ContDiffAt ℝ ∞ g (f x))
    (n : ℕ) {C B : ℝ}
    (hC : ∀ i ≤ n, ‖iteratedFDeriv ℝ i g (f x)‖ ≤ C)
    (hB : ∀ i, 1 ≤ i → i ≤ n → ‖iteratedFDeriv ℝ i f x‖ ≤ B ^ i) :
    ‖iteratedFDeriv ℝ n (g ∘ f) x‖ ≤ n.factorial * C * B ^ n := by
  obtain ⟨U, hU, hfU⟩ := hf.contDiffOn (nat_le_infty n) (by simp)
  obtain ⟨V, hV, hgV⟩ := hg.contDiffOn (nat_le_infty n) (by simp)
  obtain ⟨T, hTV, hT, hfxT⟩ := mem_nhds_iff.mp hV
  obtain ⟨O, hOsub, hO, hxO⟩ := mem_nhds_iff.mp
    (inter_mem hU (hf.continuousAt.eventually (hT.mem_nhds hfxT)))
  have hmap : MapsTo f O T := fun y hy => (hOsub hy).2
  have hh := norm_iteratedFDerivWithin_comp_le (hgV.mono hTV)
    (hfU.mono (fun y hy => (hOsub hy).1)) (le_refl (n : WithTop ℕ∞))
    hT.uniqueDiffOn hO.uniqueDiffOn hmap hxO
    (by intro i hi; rw [iteratedFDerivWithin_of_isOpen i hT (hmap hxO)]; exact hC i hi)
    (by intro i hi hin; rw [iteratedFDerivWithin_of_isOpen i hO hxO]; exact hB i hi hin)
  simpa only [iteratedFDerivWithin_of_isOpen n hO hxO] using hh

section LocalOperations

variable {s : StripData D} {K : ℕ → I → Set D} {w v : ℕ → D → ℝ} {α β : ℝ}

theorem local_congr {f g : ℕ → I → D → E} (hf : LocalJets s w α K f)
    (he : ∀ n i x, x ∈ s.domain → x ∈ K n i → f n i =ᶠ[𝓝 x] g n i) :
    LocalJets s w α K g := by
  refine ⟨fun n i x hx hi => (hf.smooth n i x hx hi).congr_of_eventuallyEq
    (he n i x hx hi).symm, ?_⟩
  intro m
  obtain ⟨C, hC, p, hb⟩ := hf.bounds m
  refine ⟨C, hC, p, ?_⟩
  intro n i x hx hi j hj
  rw [← jets_eq_of_germ (he n i x hx hi) j]
  exact hb n i x hx hi j hj

theorem local_of_eq {f g : ℕ → I → D → E} (hf : LocalJets s w α K f)
    (he : ∀ n i x, f n i x = g n i x) : LocalJets s w α K g :=
  local_congr hf (fun n i _ _ _ => Eventually.of_forall (he n i))

theorem local_neg {f : ℕ → I → D → E} (hf : LocalJets s w α K f) :
    LocalJets s w α K (fun n i x => -f n i x) := by
  simpa only [_root_.neg_apply, ContinuousLinearMap.id_apply] using
    hf.map (-(ContinuousLinearMap.id ℝ E))

theorem local_sub {f g : ℕ → I → D → E} (hf : LocalJets s w α K f)
    (hg : LocalJets s w α K g) (hw : ∀ n x, x ∈ s.domain → 0 ≤ w n x) :
    LocalJets s w α K (fun n i x => f n i x - g n i x) := by
  simpa only [sub_eq_add_neg] using hf.add (local_neg hg) hw

theorem local_mul {f g : ℕ → I → D → ℝ}
    (hf : LocalJets s w α K f) (hg : LocalJets s v β K g)
    (hw : ∀ n x, x ∈ s.domain → 0 ≤ w n x)
    (hv : ∀ n x, x ∈ s.domain → 0 ≤ v n x) :
    LocalJets s (fun n x => w n x * v n x) (α + β) K (fun n i x => f n i x * g n i x) := by
  simpa only [ContinuousLinearMap.lsmul_apply, smul_eq_mul] using
    hf.bilinear hg (ContinuousLinearMap.lsmul ℝ ℝ) hw hv

theorem local_coeff_mul {f g : ℕ → I → D → ℝ}
    (hf : LocalJets s (fun _ _ => 1) 0 K f) (hg : LocalJets s w α K g)
    (hw : ∀ n x, x ∈ s.domain → 0 ≤ w n x) :
    LocalJets s w α K (fun n i x => f n i x * g n i x) := by
  simpa only [one_mul, zero_add] using local_mul hf hg (fun _ _ _ => zero_le_one) hw

theorem local_band_smul {r : ℕ → ℝ} {f : ℕ → I → D → E}
    (hf : LocalJets s w α K f) (hr : BandBound s β r)
    (hw : ∀ n x, x ∈ s.domain → 0 ≤ w n x) :
    LocalJets s w (α + β) K (fun n i x => r n • f n i x) := by
  have hc : LocalJets s (fun _ _ => 1) β K (fun n _ (_ : D) => r n) := by
    apply LocalJets.of_memClass
    simpa using (unweighted_const s (1 : ℝ)).band_smul hr
  have hh := hc.bilinear hf (ContinuousLinearMap.lsmul ℝ ℝ) (fun _ _ _ => zero_le_one) hw
  simp only [one_mul, add_comm] at hh
  exact hh

/-- A band coefficient may itself depend on the copy. Its bound is still
chosen before that index, so this also permits a joint label/copy index. -/
theorem local_indexed_band_smul {r : I → ℕ → ℝ} {f : ℕ → I → D → E}
    (hf : LocalJets s w α K f) (hr : UniformPrimaryWeights.UniformBandBound s β r)
    (hw : ∀ n x, x ∈ s.domain → 0 ≤ w n x) :
    LocalJets s w (α + β) K (fun n i x => r i n • f n i x) := by
  obtain ⟨C, hC, p, hb⟩ := hr
  have hc : LocalJets s (fun _ _ => 1) β K (fun n i (_ : D) => r i n) := by
    refine ⟨fun _ _ _ _ _ => contDiffAt_const, fun _ => ⟨C, hC, p, ?_⟩⟩
    intro n i x hx hi j hj
    by_cases hj0 : j = 0
    · subst j
      rw [norm_iteratedFDeriv_zero]
      simp only [majorant, mul_one]
      exact (hb i n).trans (mul_le_mul_of_nonneg_left
        (pow_le_pow_left₀ (zero_le_one.trans (s.one_le_slow n)) (s.slow_le_growth n x) p)
        (mul_nonneg hC (Real.rpow_pos_of_pos (s.epsilon_pos n) β).le))
    · rw [iteratedFDeriv_const_of_ne hj0]
      simpa only [Pi.zero_apply, norm_zero] using majorant_nonneg s (fun _ _ => 1) β hC p n x
          zero_le_one
  have hh := hc.bilinear hf (ContinuousLinearMap.lsmul ℝ ℝ) (fun _ _ _ => zero_le_one) hw
  simp only [one_mul, add_comm] at hh
  exact hh

/-- Compactness controls only the fixed outer scalar function. The native
input jets have one bound before every band and copy index. -/
theorem local_compact_comp {f : ℕ → I → D → ℝ}
    (hf : LocalJets s (fun _ _ => 1) 0 K f)
    {g : ℝ → ℝ} {U C : Set ℝ} (hU : IsOpen U) (hg : ContDiffOn ℝ ∞ g U)
    (hC : IsCompact C) (hCU : C ⊆ U)
    (hmap : ∀ n i x, x ∈ s.domain → x ∈ K n i → f n i x ∈ C) :
    LocalJets s (fun _ _ => 1) 0 K (fun n i x => g (f n i x)) := by
  refine ⟨fun n i x hx hi => (hg.contDiffAt (hU.mem_nhds (hCU (hmap n i x hx hi)))).comp x
    (hf.smooth n i x hx hi), ?_⟩
  intro m
  obtain ⟨A, hA, p, ha⟩ := hf.bounds m
  obtain ⟨B, hB, hb⟩ := PhaseJetBounds.compact_jet_bound hU hg hC hCU m
  refine ⟨m.factorial * B * (A + 1) ^ m, by positivity, p * m, ?_⟩
  intro n i x hx hi j hj
  have hG := s.one_le_growth n x
  have hJ : 1 ≤ (A + 1) * s.growth n x ^ p :=
    one_le_mul_of_one_le_of_one_le (by linarith) (one_le_pow₀ hG)
  have hfJ (k : ℕ) (hk : k ≤ m) :
      ‖iteratedFDeriv ℝ k (f n i) x‖ ≤ (A + 1) * s.growth n x ^ p := by
    have h := ha n i x hx hi k hk
    simp only [majorant, Real.rpow_zero, mul_one] at h
    exact h.trans (mul_le_mul_of_nonneg_right (by linarith) (pow_nonneg (s.growth_nonneg n x) p))
  have hh := comp_jet_bound_at (hf.smooth n i x hx hi)
    (hg.contDiffAt (hU.mem_nhds (hCU (hmap n i x hx hi)))) j
    (fun k hk => hb k (hk.trans hj) (f n i x) (hmap n i x hx hi))
    (fun k hk hkj => (hfJ k (hkj.trans hj)).trans
      (by simpa only [pow_one] using pow_le_pow_right₀ hJ hk))
  calc
    _ ≤ j.factorial * B * ((A + 1) * s.growth n x ^ p) ^ j := hh
    _ ≤ m.factorial * B * ((A + 1) * s.growth n x ^ p) ^ m := by
      apply mul_le_mul
      · exact mul_le_mul_of_nonneg_right (by
          exact_mod_cast Nat.factorial_le hj) (zero_le_one.trans hB)
      · exact pow_le_pow_right₀ hJ hj
      · positivity
      · positivity
    _ = _ := by simp only [majorant, Real.rpow_zero, mul_one, mul_pow, ← pow_mul]; ring

theorem local_inv {f : ℕ → I → D → ℝ}
    (hf : LocalJets s (fun _ _ => 1) 0 K f) {b M : ℝ} (hb : 0 < b)
    (hl : ∀ n i x, x ∈ s.domain → x ∈ K n i → b ≤ |f n i x|)
    (hu : ∀ n i x, x ∈ s.domain → x ∈ K n i → |f n i x| ≤ M) :
    LocalJets s (fun _ _ => 1) 0 K (fun n i x => (f n i x)⁻¹) := by
  let C : Set ℝ := Metric.closedBall 0 M ∩ {x | b ≤ |x|}
  apply local_compact_comp hf isClosed_singleton.isOpen_compl
    (contDiffOn_id.inv (fun _ h => h))
    ((isCompact_closedBall 0 M).inter_right (isClosed_le continuous_const continuous_abs))
    (C := C)
  · intro x hx he
    have hh : b ≤ |x| := hx.2
    rw [Set.mem_singleton_iff.mp he, abs_zero] at hh
    linarith
  · intro n i x hx hi
    exact ⟨by
        simpa only [Metric.mem_closedBall, dist_zero_right, Real.norm_eq_abs] using hu n i x hx hi,
      hl n i x hx hi⟩

end LocalOperations

/-! ## The actual square-root quotient at a native point -/

section QuotientAt

open WeightedQuotients

theorem rpow_comp_jets_at {f : D → ℝ} {x : D} (hf : ContDiffAt ℝ ∞ f x)
    (hpos : 0 < f x) (p : ℝ) (m : ℕ) {B : ℝ} (hB : 1 ≤ B)
    (hpow : f x ^ p ≤ B) (hinv : (f x)⁻¹ ≤ B)
    (hjet : ∀ i ≤ m, ‖iteratedFDeriv ℝ i f x‖ ≤ B) {j : ℕ} (hj : j ≤ m) :
    ‖iteratedFDeriv ℝ j (fun y => f y ^ p) x‖ ≤ orderBound p m * B ^ (2 * m + 1) := by
  have hh := comp_jet_bound_at hf (Real.contDiffAt_rpow_const_of_ne hpos.ne') j
    (fun i hi => rpow_jet_bound p hB hpos hpow hinv hi)
    (fun i hi hij => (hjet i (hij.trans hj)).trans
      (by simpa only [pow_one] using pow_le_pow_right₀ hB hi))
  have he : (j.factorial : ℝ) * (coeffBound p j * B ^ (j + 1)) * B ^ j =
      (j.factorial * coeffBound p j) * B ^ (2 * j + 1) := by
    rw [show 2 * j + 1 = (j + 1) + j by omega, pow_add]
    ring
  rw [he] at hh
  exact hh.trans (mul_le_mul (orderBound_le p hj) (pow_le_pow_right₀ hB (by omega))
    (pow_nonneg (zero_le_one.trans hB) _) (orderBound_nonneg p m))

theorem normalized_jet_at {f : D → ℝ} {x : D} (hf : ContDiffAt ℝ ∞ f x)
    {w B : ℝ} (hw : 0 < w) (j : ℕ)
    (hjet : ‖iteratedFDeriv ℝ j f x‖ ≤ w * B) :
    ‖iteratedFDeriv ℝ j (normalizeAt w f) x‖ ≤ B := by
  change ‖iteratedFDeriv ℝ j (fun y => w⁻¹ * f y) x‖ ≤ B
  rw [norm_jet_const_mul hf, abs_of_pos (inv_pos.mpr hw)]
  have hh := mul_le_mul_of_nonneg_left hjet (inv_pos.mpr hw).le
  simpa only [← mul_assoc, inv_mul_cancel₀ hw.ne', one_mul] using hh

theorem mul_jets_at {f g : D → ℝ} {x : D}
    (hf : ContDiffAt ℝ ∞ f x) (hg : ContDiffAt ℝ ∞ g x)
    (n : ℕ) {A B : ℝ} (hA : 0 ≤ A) (_hB : 0 ≤ B)
    (hfj : ∀ i ≤ n, ‖iteratedFDeriv ℝ i f x‖ ≤ A)
    (hgj : ∀ i ≤ n, ‖iteratedFDeriv ℝ i g x‖ ≤ B) :
    ‖iteratedFDeriv ℝ n (fun y => f y * g y) x‖ ≤ chooseSum n * A * B := by
  obtain ⟨U, hU, hfU⟩ := hf.contDiffOn (nat_le_infty n) (by simp)
  obtain ⟨V, hV, hgV⟩ := hg.contDiffOn (nat_le_infty n) (by simp)
  obtain ⟨O, hsub, hO, hxO⟩ := mem_nhds_iff.mp (inter_mem hU hV)
  have hh := norm_iteratedFDerivWithin_mul_le (hfU.mono (hsub.trans inter_subset_left))
    (hgV.mono (hsub.trans inter_subset_right)) hO.uniqueDiffOn hxO (le_refl (n : WithTop ℕ∞))
  simp only [iteratedFDerivWithin_of_isOpen _ hO hxO] at hh
  apply hh.trans
  calc
    _ ≤ ∑ k ∈ Finset.range (n + 1), (n.choose k : ℝ) * A * B := by
      apply Finset.sum_le_sum
      intro k hk
      have hkn : k ≤ n := Nat.le_of_lt_succ (Finset.mem_range.mp hk)
      exact mul_le_mul (mul_le_mul_of_nonneg_left (hfj k hkn) (Nat.cast_nonneg _))
        (hgj (n-k) (Nat.sub_le _ _)) (norm_nonneg _) (mul_nonneg (Nat.cast_nonneg _) hA)
    _ = _ := by rw [← Finset.sum_mul, ← Finset.sum_mul]; rfl

theorem signed_jet_at {g r : D → ℝ} {x : D}
    (hg : ContDiffAt ℝ ∞ g x) (hr : ContDiffAt ℝ ∞ r x) (hpos : 0 < g x)
    {w B : ℝ} (hw : 0 < w) (hB : 1 ≤ B) (m : ℕ)
    (hlo : w / B ≤ g x)
    (hgj : ∀ i ≤ m, ‖iteratedFDeriv ℝ i g x‖ ≤ w * B)
    (hrj : ∀ i ≤ m, ‖iteratedFDeriv ℝ i r x‖ ≤ w * B) :
    ‖iteratedFDeriv ℝ m (fun y => r y / (2 * Real.sqrt (g y))) x‖ ≤
      Real.sqrt w * SignedCovariance.signedJetCost m * B ^ (2 * m + 2) := by
  have hhi : g x ≤ w * B := by
    simpa only [norm_iteratedFDeriv_zero, Real.norm_eq_abs, abs_of_pos hpos] using hgj 0
        (Nat.zero_le m)
  have hsingleton : ∀ y ∈ ({x} : Set D), 0 < g y := by
    intro y hy
    simpa only [Set.mem_singleton_iff.mp hy] using hpos
  obtain ⟨_, hi⟩ := normalized_bounds hw hB hsingleton (Set.mem_singleton x) hlo hhi
  have hG : ContDiffAt ℝ ∞ (normalizeAt w g) x := contDiffAt_const.mul hg
  have hR : ContDiffAt ℝ ∞ (normalizeAt w r) x := contDiffAt_const.mul hr
  have hGp : 0 < normalizeAt w g x := mul_pos (inv_pos.mpr hw) hpos
  have hP : ContDiffAt ℝ ∞ (fun y => normalizeAt w g y ^ (-(1/2 : ℝ))) x :=
    hG.rpow_const_of_ne hGp.ne'
  have hPj : ∀ i ≤ m, ‖iteratedFDeriv ℝ i (fun y => normalizeAt w g y ^ (-(1/2 : ℝ))) x‖ ≤
      orderBound (-(1/2 : ℝ)) m * B ^ (2 * m + 1) := fun i hi' =>
    rpow_comp_jets_at hG hGp _ m hB (neg_half_power_bound hB hGp hi) hi
      (fun k hk => normalized_jet_at hg hw k (hgj k hk)) hi'
  have hmul := mul_jets_at hR hP m (zero_le_one.trans hB)
    (mul_nonneg (orderBound_nonneg _ _) (pow_nonneg (zero_le_one.trans hB) _))
    (fun i hi' => normalized_jet_at hr hw i (hrj i hi')) hPj
  obtain ⟨O, hOsub, hO, hxO⟩ := mem_nhds_iff.mp (hg.continuousAt.eventually (Ioi_mem_nhds hpos))
  have he := signed_rescale_eventually hO (fun y hy => hOsub hy) hxO hw (r := r)
  rw [jet_congr he m, norm_jet_const_mul (hR.mul hP),
    abs_of_pos (div_pos (Real.sqrt_pos.mpr hw) (by norm_num))]
  apply (mul_le_mul_of_nonneg_left hmul (div_pos (Real.sqrt_pos.mpr hw) (by norm_num)).le).trans_eq
  unfold SignedCovariance.signedJetCost
  rw [show 2 * m + 2 = (2 * m + 1) + 1 by omega, pow_succ]
  ring

end QuotientAt

section LocalQuotient

variable {s : StripData D} {K : ℕ → I → Set D} {w : ℕ → D → ℝ}
  {g r : ℕ → I → D → ℝ}

/-- All finite input jet bounds and the positive weight margin are collected
before choosing a band, a copy, or a spatial point. -/
theorem local_input_envelope (hw : ∀ n x, x ∈ s.domain → 0 < w n x)
    (hg : LocalJets s w 0 K g) (hr : LocalJets s w 0 K r)
    {c : ℝ} (hc : 0 < c)
    (hl : ∀ n i x, x ∈ s.domain → x ∈ K n i → c * w n x ≤ g n i x) (m : ℕ) :
    ∃ C : ℝ, 1 ≤ C ∧ ∃ p : ℕ, ∀ n i x, x ∈ s.domain → x ∈ K n i →
      1 ≤ C * s.growth n x ^ p ∧ w n x / (C * s.growth n x ^ p) ≤ g n i x ∧
      (∀ j ≤ m, ‖iteratedFDeriv ℝ j (g n i) x‖ ≤ w n x * (C * s.growth n x ^ p)) ∧
      (∀ j ≤ m, ‖iteratedFDeriv ℝ j (r n i) x‖ ≤ w n x * (C * s.growth n x ^ p)) := by
  obtain ⟨Cg, hCg, pg, hgj⟩ := hg.bounds m
  obtain ⟨Cr, hCr, pr, hrj⟩ := hr.bounds m
  let C := Cg + Cr + c⁻¹ + 1
  let p := pg + pr
  have hC : 1 ≤ C := by dsimp [C]; linarith [(inv_pos.mpr hc).le]
  refine ⟨C, hC, p, ?_⟩
  intro n i x hx hi
  have hm (A : ℝ) (hA : 0 ≤ A) (hAC : A ≤ C) (k : ℕ) (hkp : k ≤ p) :
      A * s.growth n x ^ k ≤ C * s.growth n x ^ p :=
    mul_le_mul hAC (pow_le_pow_right₀ (s.one_le_growth n x) hkp)
      (pow_nonneg (s.growth_nonneg n x) k) (zero_le_one.trans hC)
  have hB : 1 ≤ C * s.growth n x ^ p :=
    one_le_mul_of_one_le_of_one_le hC (one_le_pow₀ (s.one_le_growth n x))
  have hp : 0 < g n i x := (mul_pos hc (hw n x hx)).trans_le (hl n i x hx hi)
  refine ⟨hB, ?_, ?_, ?_⟩
  · have hwg : w n x ≤ c⁻¹ * g n i x := by
      have hh := mul_le_mul_of_nonneg_left (hl n i x hx hi) (inv_pos.mpr hc).le
      simpa only [← mul_assoc, inv_mul_cancel₀ hc.ne', one_mul] using hh
    have hratio : w n x / g n i x ≤ c⁻¹ := (div_le_iff₀ hp).mpr hwg
    have hC0 : c⁻¹ ≤ C := by dsimp [C]; linarith
    have hb0 := hm (c⁻¹) (inv_pos.mpr hc).le hC0 0 (Nat.zero_le _)
    have hh : w n x / g n i x ≤ C * s.growth n x ^ p := hratio.trans
      (by simpa only [pow_zero, mul_one] using hb0)
    apply (div_le_iff₀ (zero_lt_one.trans_le hB)).mpr
    simpa only [mul_comm] using (div_le_iff₀ hp).mp hh
  · intro j hj
    have hh := hgj n i x hx hi j hj
    simp only [majorant, Real.rpow_zero, mul_one] at hh
    exact hh.trans ((mul_le_mul_of_nonneg_right
      (hm Cg hCg (by
          dsimp [C]; linarith [(inv_pos.mpr hc).le]) pg (by
              dsimp [p]; omega)) (hw n x hx).le).trans_eq (by ring))
  · intro j hj
    have hh := hrj n i x hx hi j hj
    simp only [majorant, Real.rpow_zero, mul_one] at hh
    exact hh.trans ((mul_le_mul_of_nonneg_right
      (hm Cr hCr (by
          dsimp [C]; linarith [(inv_pos.mpr hc).le]) pr (by
              dsimp [p]; omega)) (hw n x hx).le).trans_eq (by ring))

theorem local_signed_quotient_zero (hw : ∀ n x, x ∈ s.domain → 0 < w n x)
    (hg : LocalJets s w 0 K g) (hr : LocalJets s w 0 K r)
    {c : ℝ} (hc : 0 < c)
    (hl : ∀ n i x, x ∈ s.domain → x ∈ K n i → c * w n x ≤ g n i x) :
    LocalJets s (fun n x => Real.sqrt (w n x)) 0 K
      (fun n i x => r n i x / (2 * Real.sqrt (g n i x))) := by
  have hp n i x hx hi : 0 < g n i x := (mul_pos hc (hw n x hx)).trans_le (hl n i x hx hi)
  refine ⟨?_, ?_⟩
  · intro n i x hx hi
    exact (hr.smooth n i x hx hi).div
      (contDiffAt_const.mul ((hg.smooth n i x hx hi).sqrt (hp n i x hx hi).ne'))
      (mul_ne_zero (by norm_num) (Real.sqrt_pos.mpr (hp n i x hx hi)).ne')
  · intro m
    obtain ⟨C, hC, p, henv⟩ := local_input_envelope hw hg hr hc hl m
    refine ⟨SignedCovariance.prefixJetCost m * C ^ (2 * m + 2),
      mul_nonneg (SignedCovariance.prefixJetCost_pos m).le (pow_nonneg (zero_le_one.trans hC) _),
      p * (2 * m + 2), ?_⟩
    intro n i x hx hi j hj
    obtain ⟨hB, hlo, hgj, hrj⟩ := henv n i x hx hi
    have hb := signed_jet_at (hg.smooth n i x hx hi) (hr.smooth n i x hx hi) (hp n i x hx hi)
      (hw n x hx) hB j hlo (fun k hk => hgj k (hk.trans hj)) (fun k hk => hrj k (hk.trans hj))
    calc
      _ ≤ Real.sqrt (w n x) * SignedCovariance.signedJetCost j *
          (C * s.growth n x ^ p) ^ (2 * j + 2) := hb
      _ ≤ Real.sqrt (w n x) * SignedCovariance.prefixJetCost m *
          (C * s.growth n x ^ p) ^ (2 * m + 2) := by
        exact mul_le_mul (mul_le_mul_of_nonneg_left (SignedCovariance.signedJetCost_le hj)
          (Real.sqrt_nonneg _)) (pow_le_pow_right₀ hB (by omega))
          (pow_nonneg (zero_le_one.trans hB) _)
          (mul_nonneg (Real.sqrt_nonneg _) (SignedCovariance.prefixJetCost_pos m).le)
      _ = _ := by simp only [majorant, Real.rpow_zero, mul_one, mul_pow, pow_mul]; ring

theorem local_signed_quotient {β : ℝ} (hw : ∀ n x, x ∈ s.domain → 0 < w n x)
    (hg : LocalJets s w 0 K g) (hr : LocalJets s w β K r)
    {c : ℝ} (hc : 0 < c)
    (hl : ∀ n i x, x ∈ s.domain → x ∈ K n i → c * w n x ≤ g n i x) :
    LocalJets s (fun n x => Real.sqrt (w n x)) β K
      (fun n i x => r n i x / (2 * Real.sqrt (g n i x))) := by
  have hr0 : LocalJets s w 0 K (fun n i x => s.epsilon n ^ (-β) * r n i x) := by
    simpa only [smul_eq_mul, add_neg_cancel] using
      local_band_smul hr (bandBound_rpow s (-β)) (fun n x hx => (hw n x hx).le)
  have hh := local_band_smul (local_signed_quotient_zero hw hg hr0 hc hl)
    (bandBound_rpow s β) (fun _ _ _ => Real.sqrt_nonneg _)
  apply local_of_eq (by simpa only [zero_add] using hh)
  intro n i x
  simp only [smul_eq_mul, ← mul_div_assoc, ← mul_assoc, ← Real.rpow_add (s.epsilon_pos n),
    add_neg_cancel, Real.rpow_zero, one_mul]

end LocalQuotient

/-! ## Cramer's actual solve, uniformly on the native cells -/

/-- Mat2: an abbreviation for `SignedWaveUpdate.Mat2`. -/
abbrev Mat2 := SignedWaveUpdate.Mat2
/-- Vec2: an abbreviation for `SignedWaveUpdate.Vec2`. -/
abbrev Vec2 := SignedWaveUpdate.Vec2
/-- Space: an abbreviation for `ProblemStatement.Space`. -/
abbrev Space := ProblemStatement.Space

/-- Only primitive matrix/target jets and zeroth-order margins occur here.
There is no inverse-jet or signed-output estimate in this record. -/
structure NativeCovariance (s : StripData D) (K : ℕ → I → Set D)
    (H : I → ℕ → D → Mat2) (T : I → ℕ → D → Vec2) where
  matrix_jets : ∀ a b, LocalJets s (fun _ _ => 1) 0 K (fun n i x => H i n x a b)
  target_jets : ∀ a, LocalJets s (fun _ x => s.zeta x) 0 K (fun n i x => T i n x a)
  zeta_pos : ∀ x ∈ s.domain, 0 < s.zeta x
  /-- Determinant gap of `NativeCovariance`, of type `ℝ`. -/
  determinantGap : ℝ
  /-- Entry bound of `NativeCovariance`, of type `ℝ`. -/
  entryBound : ℝ
  /-- Primary lower of `NativeCovariance`, of type `ℝ`. -/
  primaryLower : ℝ
  gap_pos : 0 < determinantGap
  entry_one : 1 ≤ entryBound
  lower_pos : 0 < primaryLower
  determinant : ∀ n i x, x ∈ s.domain → x ∈ K n i →
    determinantGap ≤ |(PrimaryPulseBounds.normalizedMatrix (Real.sqrt (s.slow n)) (H i n x)).det|
  entries : ∀ n i x, x ∈ s.domain → x ∈ K n i → ∀ a b,
    |Real.sqrt (s.slow n) * H i n x a b| ≤ entryBound
  lower : ∀ n i x, x ∈ s.domain → x ∈ K n i → ∀ j,
    primaryLower * s.zeta x ≤ SmoothCovariance.weights (H i n x) (T i n x) j

namespace NativeCovariance

variable {s : StripData D} {K : ℕ → I → Set D}
  {H : I → ℕ → D → Mat2} {T : I → ℕ → D → Vec2} (h : NativeCovariance s K H T)

include h

theorem det_nonzero (n : ℕ) (i : I) {x : D} (hx : x ∈ s.domain) (hi : x ∈ K n i) :
    (H i n x).det ≠ 0 := by
  intro he
  have hh := h.determinant n i x hx hi
  rw [PrimaryPulseBounds.normalizedMatrix_det, he, mul_zero, abs_zero] at hh
  exact (not_le_of_gt h.gap_pos) hh

theorem det_eventually (n : ℕ) (i : I) {x : D} (hx : x ∈ s.domain) (hi : x ∈ K n i) :
    ∀ᶠ y in 𝓝 x, (H i n y).det ≠ 0 := by
  have hh : ContDiffAt ℝ ∞ (fun y => (H i n y).det) x := by
    simpa only [Matrix.det_fin_two] using
      (((h.matrix_jets 0 0).smooth n i x hx hi).mul ((h.matrix_jets 1 1).smooth n i x hx hi)).sub
        (((h.matrix_jets 0 1).smooth n i x hx hi).mul ((h.matrix_jets 1 0).smooth n i x hx hi))
  exact hh.continuousAt.eventually
    (isOpen_ne.mem_nhds (h.det_nonzero n i hx hi))

theorem weights_jets {R : I → ℕ → D → Vec2} {w : ℕ → D → ℝ} {β : ℝ}
    (hw : ∀ n x, x ∈ s.domain → 0 ≤ w n x)
    (hR : ∀ a, LocalJets s w β K (fun n i x => R i n x a)) (j : Fin 2) :
    LocalJets s w β K (fun n i x => SmoothCovariance.weights (H i n x) (R i n x) j) := by
  have h1 : ∀ (_ : ℕ) (x : D), x ∈ s.domain → 0 ≤ (1 : ℝ) := fun _ _ _ => zero_le_one
  have hr : LocalJets s (fun _ _ => 1) 0 K (fun n _ (_ : D) => Real.sqrt (s.slow n)) :=
    LocalJets.of_memClass (CurlClassBounds.polynomialJets_unweighted
        (PrimaryPulseBounds.sqrt_slow_polynomial s))
  have hN (a b : Fin 2) := local_coeff_mul hr (h.matrix_jets a b) h1
  have hD : LocalJets s (fun _ _ => 1) 0 K
      (fun n i x => (PrimaryPulseBounds.normalizedMatrix (Real.sqrt (s.slow n)) (H i n x)).det) :=
          by
    simpa only [Matrix.det_fin_two, PrimaryPulseBounds.normalizedMatrix] using
      local_sub (local_coeff_mul (hN 0 0) (hN 1 1) h1)
        (local_coeff_mul (hN 0 1) (hN 1 0) h1) h1
  have hupper : ∀ n i x, x ∈ s.domain → x ∈ K n i →
      |(PrimaryPulseBounds.normalizedMatrix (Real.sqrt (s.slow n)) (H i n x)).det| ≤ 2 *
          h.entryBound ^ 2 := by
    intro n i x hx hi
    simp only [Matrix.det_fin_two, PrimaryPulseBounds.normalizedMatrix]
    apply (abs_sub _ _).trans
    have hA := mul_le_mul (h.entries n i x hx hi 0 0) (h.entries n i x hx hi 1 1)
      (abs_nonneg _) (zero_le_one.trans h.entry_one)
    have hB := mul_le_mul (h.entries n i x hx hi 0 1) (h.entries n i x hx hi 1 0)
      (abs_nonneg _) (zero_le_one.trans h.entry_one)
    simp only [abs_mul] at hA hB ⊢
    nlinarith
  have hinv := local_inv hD h.gap_pos h.determinant hupper
  have hscale := local_coeff_mul (local_coeff_mul hr hr h1) hinv h1
  have hprod (a b k : Fin 2) := local_coeff_mul (h.matrix_jets a b) (hR k) hw
  have hnum : LocalJets s w β K (fun n i x => SmoothCovariance.cramerNumerator (H i n x) (R i n x)
      j) := by
    fin_cases j
    · have hh := local_sub (hprod 1 1 0) (hprod 0 1 1) hw
      simp only [SmoothCovariance.cramerNumerator, mul_comm] at hh ⊢
      exact hh
    · have hh := local_sub (hprod 0 0 1) (hprod 1 0 0) hw
      simp only [SmoothCovariance.cramerNumerator, mul_comm] at hh ⊢
      exact hh
  apply local_congr (local_coeff_mul hscale hnum hw)
  intro n i x hx hi
  filter_upwards [h.det_eventually n i hx hi] with y hy
  simpa only [pow_two] using (PrimaryPulseBounds.weights_eq_normalized
    (Real.sqrt (s.slow n)) (H i n y) (R i n y)
    (Real.sqrt_pos.mpr (zero_lt_one.trans_le (s.one_le_slow n))).ne' hy j).symm

theorem increment_jets {R : I → ℕ → D → Vec2} {β : ℝ}
    (hR : ∀ a, LocalJets s (fun _ x => s.zeta x) β K (fun n i x => R i n x a)) (j : Fin 2) :
    LocalJets s (fun _ x => Real.sqrt (s.zeta x)) β K
      (fun n i x => SignedCovariance.increment (H i n x) (T i n x) (R i n x) j) := by
  have hg := h.weights_jets (fun _ x hx => s.zeta_nonneg x hx) h.target_jets j
  have hr := h.weights_jets (fun _ x hx => s.zeta_nonneg x hx) hR j
  have hq := local_signed_quotient (fun _ x hx => h.zeta_pos x hx) hg hr h.lower_pos
    (fun n i x hx hi => h.lower n i x hx hi j)
  apply local_congr hq
  intro n i x hx hi
  filter_upwards [h.det_eventually n i hx hi] with y hy
  simp only [SignedCovariance.increment, SmoothCovariance.amplitudes,
    SmoothCovariance.inverse_formula _ _ hy]

end NativeCovariance

/-! ## The literal signed amplitude and homogeneous pressure -/

section SignedAmplitude

variable {s : StripData D} {K : ℕ → I → Set D}
  {H : I → ℕ → D → Mat2} {T R : I → ℕ → D → Vec2}
  {mask : I → ℕ → D → ℝ} {v : I → ℕ → D → Space}
  {W : ℕ → D → ℝ} {β : ℝ}

theorem signedScalar_jets (h : NativeCovariance s K H T)
    (hR : ∀ a, LocalJets s (fun _ x => s.zeta x) β K (fun n i x => R i n x a))
    (hm : LocalJets s (fun _ _ => 1) 0 K (fun n i => mask i n)) (j : Fin 2) :
    LocalJets s (fun _ x => Real.sqrt (s.zeta x)) (β + 1 / 2) K
      (fun n i => SignedWaveUpdate.signedScalar s (H i) (T i) (R i) (mask i) j n) := by
  have hh := local_coeff_mul hm (h.increment_jets hR j) (fun _ _ _ => Real.sqrt_nonneg _)
  have he := local_band_smul hh (bandBound_rpow s (1 / 2)) (fun _ _ _ => Real.sqrt_nonneg _)
  apply local_of_eq he
  intro n i x
  simp only [SignedWaveUpdate.signedScalar, smul_eq_mul, ← Real.sqrt_eq_rpow]
  ring

theorem signedVector_jets (h : NativeCovariance s K H T)
    (hR : ∀ a, LocalJets s (fun _ x => s.zeta x) β K (fun n i x => R i n x a))
    (hm : LocalJets s (fun _ _ => 1) 0 K (fun n i => mask i n))
    (hv : LocalJets s W 0 K (fun n i => v i n))
    (hW : ∀ n x, x ∈ s.domain → 0 ≤ W n x) (j : Fin 2) :
    LocalJets s (fun n x => Real.sqrt (s.zeta x) * W n x) (β + 1 / 2) K
      (fun n i => SignedWaveUpdate.signedVector s (H i) (T i) (R i) (mask i) (v i) j n) := by
  have hh := (signedScalar_jets h hR hm j).bilinear hv (ContinuousLinearMap.lsmul ℝ ℝ)
      (fun _ _ _ => Real.sqrt_nonneg _) hW
  simp only [add_zero, ContinuousLinearMap.lsmul_apply] at hh ⊢
  exact hh

end SignedAmplitude

section Pressure

open scoped InnerProductSpace

variable {s : StripData D} {K : ℕ → I → Set D} {w : ℕ → D → ℝ} {α : ℝ}

theorem local_inner {u v : ℕ → I → D → Space}
    (hu : LocalJets s (fun _ _ => 1) 0 K u) (hv : LocalJets s w α K v)
    (hw : ∀ n x, x ∈ s.domain → 0 ≤ w n x) :
    LocalJets s w α K (fun n i x => ⟪u n i x, v n i x⟫_ℝ) := by
  have hh := hu.bilinear hv (innerSL ℝ) (fun _ _ _ => zero_le_one) hw
  simp only [one_mul, zero_add] at hh
  exact hh

theorem local_normalInverse {N : ℕ → I → D → Space}
    (hN : LocalJets s (fun _ _ => 1) 0 K N) {b M : ℝ} (hb : 0 < b)
    (hl : ∀ n i x, x ∈ s.domain → x ∈ K n i → b ≤ ‖N n i x‖)
    (hu : ∀ n i x, x ∈ s.domain → x ∈ K n i → ‖N n i x‖ ≤ M) :
    LocalJets s (fun _ _ => 1) 0 K (fun n i x => (‖N n i x‖ ^ 2)⁻¹) := by
  have hsq : LocalJets s (fun _ _ => 1) 0 K (fun n i x => ‖N n i x‖ ^ 2) := by
    simpa only [real_inner_self_eq_norm_sq] using local_inner hN hN (fun _ _ _ => zero_le_one)
  apply local_inv hsq (sq_pos_of_pos hb)
  · intro n i x hx hi
    rw [abs_of_nonneg (sq_nonneg _)]
    exact (sq_le_sq₀ hb.le (norm_nonneg _)).2 (hl n i x hx hi)
  · intro n i x hx hi
    rw [abs_of_nonneg (sq_nonneg _)]
    exact (sq_le_sq₀ (norm_nonneg _) ((norm_nonneg _).trans (hu n i x hx hi))).2 (hu n i x hx hi)

theorem local_pressureCoefficient {N Ndot u : ℕ → I → D → Space}
    {A : ℕ → I → D → Space →L[ℝ] Space}
    (hN : LocalJets s (fun _ _ => 1) 0 K N)
    (hNdot : LocalJets s (fun _ _ => 1) 0 K Ndot)
    (hA : LocalJets s (fun _ _ => 1) 0 K A)
    (ha : LocalJets s w α K u) (hw : ∀ n x, x ∈ s.domain → 0 ≤ w n x)
    {b M : ℝ} (hb : 0 < b)
    (hl : ∀ n i x, x ∈ s.domain → x ∈ K n i → b ≤ ‖N n i x‖)
    (hu : ∀ n i x, x ∈ s.domain → x ∈ K n i → ‖N n i x‖ ≤ M) :
    LocalJets s w α K (fun n i x => TangentProjection.pressureCoefficient
      (N n i x) (Ndot n i x) (u n i x) (A n i x (u n i x)) 0) := by
  have hAu : LocalJets s w α K (fun n i x => A n i x (u n i x)) := by
    have hh := hA.bilinear ha (ContinuousLinearMap.apply ℝ Space).flip (fun _ _ _ => zero_le_one) hw
    simp only [one_mul, zero_add] at hh
    exact hh
  have hn := local_sub (local_inner hN hAu hw) (local_inner hNdot ha hw) hw
  have hh := local_coeff_mul (local_normalInverse hN hb hl hu) hn hw
  simpa only [TangentProjection.pressureCoefficient, inner_zero_right, add_zero,
    real_inner_self_eq_norm_sq, div_eq_mul_inv, mul_comm] using hh

theorem local_projectedPressure {N Ndot u : ℕ → I → D → Space}
    {A : ℕ → I → D → Space →L[ℝ] Space} {frequency : I → ℕ → ℝ}
    (hN : LocalJets s (fun _ _ => 1) 0 K N)
    (hNdot : LocalJets s (fun _ _ => 1) 0 K Ndot)
    (hA : LocalJets s (fun _ _ => 1) 0 K A)
    (ha : LocalJets s w α K u) (hw : ∀ n x, x ∈ s.domain → 0 ≤ w n x)
    {b M : ℝ} (hb : 0 < b)
    (hl : ∀ n i x, x ∈ s.domain → x ∈ K n i → b ≤ ‖N n i x‖)
    (hu : ∀ n i x, x ∈ s.domain → x ∈ K n i → ‖N n i x‖ ≤ M)
    (hK : UniformPrimaryWeights.UniformBandBound s (1 / 2) (fun i n => 1 / frequency i n)) :
    LocalJets s w (α + 1 / 2) K (fun n i => ParticularWaveBounds.projectedPressure
      (frequency i n) (N n i) (Ndot n i) (u n i) (fun x => A n i x (u n i x)) (fun _ => 0)) := by
  have hpc := (local_pressureCoefficient hN hNdot hA ha hw hb hl hu).map
    (Complex.I • Complex.ofRealCLM)
  have hh := local_indexed_band_smul hpc hK hw
  apply local_of_eq hh
  intro n i x
  simp only [ParticularWaveBounds.projectedPressure, _root_.smul_apply,
    Complex.ofRealCLM_apply, smul_eq_mul, Complex.real_smul, div_eq_mul_inv, mul_comm, mul_one,
        Complex.ofReal_inv]

end Pressure

section ActualCoefficients

variable {s : StripData D} {K : ℕ → I → Set D}
  {a : I → LinearWaveBounds.WaveCoefficients D}
  {d : I → LinearWaveBounds.GraphDirections D}
  {H : I → ℕ → D → Mat2} {T R : I → ℕ → D → Vec2}
  {mask : I → ℕ → D → ℝ} {v Ndot : I → ℕ → D → Space}
  {A : I → ℕ → D → Space →L[ℝ] Space} {W : ℕ → D → ℝ} {β : ℝ}

/-- Native bounds for the literal signed quotient and its constructed
homogeneous pressure. Even the background and frequency may vary with the
copy index, provided their primitive estimates are uniform. -/
theorem coefficients_jets (h : NativeCovariance s K H T)
    (hR : ∀ q, LocalJets s (fun _ x => s.zeta x) β K (fun n i x => R i n x q))
    (hm : LocalJets s (fun _ _ => 1) 0 K (fun n i => mask i n))
    (hv : LocalJets s W 0 K (fun n i => v i n))
    (hW : ∀ n x, x ∈ s.domain → 0 ≤ W n x)
    (hN : LocalJets s (fun _ _ => 1) 0 K (fun n i => (a i).normal s (d i) n))
    (hNdot : LocalJets s (fun _ _ => 1) 0 K (fun n i => Ndot i n))
    (hA : LocalJets s (fun _ _ => 1) 0 K (fun n i => A i n))
    {b M : ℝ} (hb : 0 < b)
    (hl : ∀ n i x, x ∈ s.domain → x ∈ K n i → b ≤ ‖(a i).normal s (d i) n x‖)
    (hu : ∀ n i x, x ∈ s.domain → x ∈ K n i → ‖(a i).normal s (d i) n x‖ ≤ M)
    (hK : UniformPrimaryWeights.UniformBandBound s (1 / 2) (fun i n => 1 / (a i).frequency n))
    (j : Fin 2) :
    LocalJets s (fun n x => Real.sqrt (s.zeta x) * W n x) (β + 1 / 2) K
      (fun n i => (SignedWaveUpdate.coefficients (a i) s (d i) (H i) (T i) (R i)
        (mask i) (v i) (Ndot i) (A i) j).amplitude n) ∧
    LocalJets s (fun n x => Real.sqrt (s.zeta x) * W n x) (β + 1) K
      (fun n i => (SignedWaveUpdate.coefficients (a i) s (d i) (H i) (T i) (R i)
        (mask i) (v i) (Ndot i) (A i) j).pressure n) := by
  have hv' := signedVector_jets h hR hm hv hW j
  refine ⟨hv'.map CurlClassBounds.complexify, ?_⟩
  simpa only [SignedWaveUpdate.coefficients, SignedWaveUpdate.homogeneousCoefficients,
    show β + 1 / 2 + 1 / 2 = β + 1 by ring] using
    local_projectedPressure hN hNdot hA hv'
      (fun n x hx => mul_nonneg (Real.sqrt_nonneg _) (hW n x hx)) hb hl hu hK

/-- The cutoff is applied exactly once. These are the coefficients consumed
by `PeriodizedWaveBounds.CopyData.common_bounds_from_native`. -/
theorem coefficients_localized_jets (h : NativeCovariance s K H T)
    (hR : ∀ q, LocalJets s (fun _ x => s.zeta x) β K (fun n i x => R i n x q))
    (hm : LocalJets s (fun _ _ => 1) 0 K (fun n i => mask i n))
    (hv : LocalJets s W 0 K (fun n i => v i n))
    (hW : ∀ n x, x ∈ s.domain → 0 ≤ W n x)
    (hN : LocalJets s (fun _ _ => 1) 0 K (fun n i => (a i).normal s (d i) n))
    (hNdot : LocalJets s (fun _ _ => 1) 0 K (fun n i => Ndot i n))
    (hA : LocalJets s (fun _ _ => 1) 0 K (fun n i => A i n))
    {b M : ℝ} (hb : 0 < b)
    (hl : ∀ n i x, x ∈ s.domain → x ∈ K n i → b ≤ ‖(a i).normal s (d i) n x‖)
    (hu : ∀ n i x, x ∈ s.domain → x ∈ K n i → ‖(a i).normal s (d i) n x‖ ≤ M)
    (hK : UniformPrimaryWeights.UniformBandBound s (1 / 2) (fun i n => 1 / (a i).frequency n))
    {ψ : I → ℕ → D → ℝ}
    (hψ : LocalJets s (fun _ _ => 1) 0 K (fun n i => ψ i n)) (j : Fin 2) :
    LocalJets s (fun n x => Real.sqrt (s.zeta x) * W n x) (β + 1 / 2) K
      (fun n i => ((SignedWaveUpdate.coefficients (a i) s (d i) (H i) (T i) (R i)
        (mask i) (v i) (Ndot i) (A i) j).withCutoff (ψ i)).amplitude n) ∧
    LocalJets s (fun n x => Real.sqrt (s.zeta x) * W n x) (β + 1) K
      (fun n i => ((SignedWaveUpdate.coefficients (a i) s (d i) (H i) (T i) (R i)
        (mask i) (v i) (Ndot i) (A i) j).withCutoff (ψ i)).pressure n) := by
  obtain ⟨ha, hp⟩ := coefficients_jets h hR hm hv hW hN hNdot hA hb hl hu hK j
  have hw n x hx := mul_nonneg (Real.sqrt_nonneg (s.zeta x)) (hW n x hx)
  refine ⟨hψ.smul ha hw, ?_⟩
  simpa only [LinearWaveBounds.WaveCoefficients.withCutoff, Complex.real_smul] using hψ.smul hp hw

end ActualCoefficients

/-! ## Uniformity in an external label as well as the native copy -/

section UniformLabels

variable {L : Type} {s : StripData D} {α : ℝ}
  {w : L → ℕ → D → ℝ} {K : L → ℕ → I → Set D}
  {f : L → ℕ → I → D → E}

/-- Reindexing the discrete band/label pair preserves the actual spatial
derivatives and the full inverse-edge majorant. -/
theorem local_pull (hf : UniformLocalJets s w α K f) (e : ℕ → ℕ × L) :
    LocalJets (UniformPrimaryWeights.reindexedStrip s e)
      (fun k => w (e k).2 (e k).1) α (fun k => K (e k).2 (e k).1)
      (fun k => f (e k).2 (e k).1) := by
  refine ⟨fun k => hf.smooth (e k).2 (e k).1, ?_⟩
  intro m
  obtain ⟨C, hC, p, hb⟩ := hf.bounds m
  exact ⟨C, hC, p, fun k => hb (e k).2 (e k).1⟩

/-- Surjectivity recovers all labels with the same constants. A collection
of separately bounded label outputs would not suffice here. -/
theorem uniform_local_of_pull {e : ℕ → ℕ × L} (he : Surjective e)
    (hf : LocalJets (UniformPrimaryWeights.reindexedStrip s e)
      (fun k => w (e k).2 (e k).1) α (fun k => K (e k).2 (e k).1)
      (fun k => f (e k).2 (e k).1)) : UniformLocalJets s w α K f := by
  refine ⟨?_, ?_⟩
  · intro l n i x hx hi
    obtain ⟨k, hk⟩ := he (n, l)
    have hi' : x ∈ K (e k).2 (e k).1 i := by simpa only [hk] using hi
    simpa only [hk] using hf.smooth k i x hx hi'
  · intro m
    obtain ⟨C, hC, p, hb⟩ := hf.bounds m
    refine ⟨C, hC, p, ?_⟩
    intro l n i x hx hi j hj
    obtain ⟨k, hk⟩ := he (n, l)
    have hi' : x ∈ K (e k).2 (e k).1 i := by simpa only [hk] using hi
    have hh := hb k i x hx hi' j hj
    simpa only [majorant, UniformPrimaryWeights.reindexedStrip, StripData.growth, hk] using hh

theorem uniform_smul [Countable L] [Nonempty L] {r : L → ℕ → I → D → ℝ}
    (hr : UniformLocalJets s (fun _ _ _ => 1) 0 K r)
    (hf : UniformLocalJets s w α K f)
    (hw : ∀ l n x, x ∈ s.domain → 0 ≤ w l n x) :
    UniformLocalJets s w α K (fun l n i x => r l n i x • f l n i x) := by
  apply uniform_local_of_pull (UniformPrimaryWeights.enumeration_surjective L)
  exact (local_pull hr (UniformPrimaryWeights.enumeration L)).smul
    (local_pull hf (UniformPrimaryWeights.enumeration L))
    (fun k => hw (UniformPrimaryWeights.enumeration L k).2 (UniformPrimaryWeights.enumeration L
        k).1)

end UniformLabels

/-- Primitive covariance data with one determinant gap, entry bound,
positive weight margin, and finite-jet constants for all external labels. -/
structure UniformNativeCovariance {L : Type} (s : StripData D)
    (K : L → ℕ → I → Set D) (H : L → I → ℕ → D → Mat2)
    (T : L → I → ℕ → D → Vec2) where
  matrix_jets : ∀ a b, UniformLocalJets s (fun _ _ _ => 1) 0 K (fun l n i x => H l i n x a b)
  target_jets : ∀ a, UniformLocalJets s (fun _ _ x => s.zeta x) 0 K (fun l n i x => T l i n x a)
  zeta_pos : ∀ x ∈ s.domain, 0 < s.zeta x
  /-- Determinant gap of `UniformNativeCovariance`, of type `ℝ`. -/
  determinantGap : ℝ
  /-- Entry bound of `UniformNativeCovariance`, of type `ℝ`. -/
  entryBound : ℝ
  /-- Primary lower of `UniformNativeCovariance`, of type `ℝ`. -/
  primaryLower : ℝ
  gap_pos : 0 < determinantGap
  entry_one : 1 ≤ entryBound
  lower_pos : 0 < primaryLower
  determinant : ∀ l n i x, x ∈ s.domain → x ∈ K l n i →
    determinantGap ≤ |(PrimaryPulseBounds.normalizedMatrix (Real.sqrt (s.slow n)) (H l i n x)).det|
  entries : ∀ l n i x, x ∈ s.domain → x ∈ K l n i → ∀ a b,
    |Real.sqrt (s.slow n) * H l i n x a b| ≤ entryBound
  lower : ∀ l n i x, x ∈ s.domain → x ∈ K l n i → ∀ j,
    primaryLower * s.zeta x ≤ SmoothCovariance.weights (H l i n x) (T l i n x) j

namespace UniformNativeCovariance

variable {L : Type} {s : StripData D} {K : L → ℕ → I → Set D}
  {H : L → I → ℕ → D → Mat2} {T : L → I → ℕ → D → Vec2}

/-- Pull, bundling `matrix_jets`, `target_jets`, `zeta_pos`, `determinantGap` and the required
compatibility proofs. -/
noncomputable def pull (h : UniformNativeCovariance s K H T) (e : ℕ → ℕ × L) :
    NativeCovariance (UniformPrimaryWeights.reindexedStrip s e)
      (fun k => K (e k).2 (e k).1) (fun i k => H (e k).2 i (e k).1)
      (fun i k => T (e k).2 i (e k).1) where
  matrix_jets a b := local_pull (h.matrix_jets a b) e
  target_jets a := local_pull (h.target_jets a) e
  zeta_pos := h.zeta_pos
  determinantGap := h.determinantGap
  entryBound := h.entryBound
  primaryLower := h.primaryLower
  gap_pos := h.gap_pos
  entry_one := h.entry_one
  lower_pos := h.lower_pos
  determinant k := h.determinant (e k).2 (e k).1
  entries k := h.entries (e k).2 (e k).1
  lower k := h.lower (e k).2 (e k).1

end UniformNativeCovariance

section UniformActualCoefficients

variable {L : Type} [Countable L] [Nonempty L]
  {s : StripData D} {K : L → ℕ → I → Set D}
  {a : L → I → LinearWaveBounds.WaveCoefficients D}
  {d : L → I → LinearWaveBounds.GraphDirections D}
  {H : L → I → ℕ → D → Mat2} {T R : L → I → ℕ → D → Vec2}
  {mask : L → I → ℕ → D → ℝ} {v Ndot : L → I → ℕ → D → Space}
  {A : L → I → ℕ → D → Space →L[ℝ] Space} {W : L → ℕ → D → ℝ} {β : ℝ}

/-- The amplitude and projected-pressure estimates are simultaneous in
all spatial labels, all bands and all lattice copies. Label-dependent
envelopes are retained. -/
theorem uniform_coefficients_jets (h : UniformNativeCovariance s K H T)
    (hR : ∀ q, UniformLocalJets s (fun _ _ x => s.zeta x) β K (fun l n i x => R l i n x q))
    (hm : UniformLocalJets s (fun _ _ _ => 1) 0 K (fun l n i => mask l i n))
    (hv : UniformLocalJets s W 0 K (fun l n i => v l i n))
    (hW : ∀ l n x, x ∈ s.domain → 0 ≤ W l n x)
    (hN : UniformLocalJets s (fun _ _ _ => 1) 0 K (fun l n i => (a l i).normal s (d l i) n))
    (hNdot : UniformLocalJets s (fun _ _ _ => 1) 0 K (fun l n i => Ndot l i n))
    (hA : UniformLocalJets s (fun _ _ _ => 1) 0 K (fun l n i => A l i n))
    {b M : ℝ} (hb : 0 < b)
    (hl : ∀ l n i x, x ∈ s.domain → x ∈ K l n i → b ≤ ‖(a l i).normal s (d l i) n x‖)
    (hu : ∀ l n i x, x ∈ s.domain → x ∈ K l n i → ‖(a l i).normal s (d l i) n x‖ ≤ M)
    (hK : UniformPrimaryWeights.UniformBandBound s (1 / 2)
      (fun li : L × I => fun n => 1 / (a li.1 li.2).frequency n)) (j : Fin 2) :
    UniformLocalJets s (fun l n x => Real.sqrt (s.zeta x) * W l n x) (β + 1 / 2) K
      (fun l n i => (SignedWaveUpdate.coefficients (a l i) s (d l i) (H l i) (T l i) (R l i)
        (mask l i) (v l i) (Ndot l i) (A l i) j).amplitude n) ∧
    UniformLocalJets s (fun l n x => Real.sqrt (s.zeta x) * W l n x) (β + 1) K
      (fun l n i => (SignedWaveUpdate.coefficients (a l i) s (d l i) (H l i) (T l i) (R l i)
        (mask l i) (v l i) (Ndot l i) (A l i) j).pressure n) := by
  let e := UniformPrimaryWeights.enumeration L
  have he : Surjective e := UniformPrimaryWeights.enumeration_surjective L
  have hs := signedVector_jets (h.pull e) (fun q => local_pull (hR q) e)
    (local_pull hm e) (local_pull hv e) (fun k => hW (e k).2 (e k).1) j
  have hK' : UniformPrimaryWeights.UniformBandBound
      (UniformPrimaryWeights.reindexedStrip s e) (1 / 2)
      (fun i k => 1 / (a (e k).2 i).frequency (e k).1) := by
    obtain ⟨C, hC, p, hc⟩ := hK
    exact ⟨C, hC, p, fun i k => hc ((e k).2, i) (e k).1⟩
  have hp := local_projectedPressure (local_pull hN e) (local_pull hNdot e)
    (local_pull hA e) hs
    (fun k x hx => mul_nonneg (Real.sqrt_nonneg _) (hW (e k).2 (e k).1 x hx)) hb
    (fun k => hl (e k).2 (e k).1) (fun k => hu (e k).2 (e k).1) hK'
  constructor
  · apply uniform_local_of_pull he
    exact hs.map CurlClassBounds.complexify
  · apply uniform_local_of_pull he
    simp only [show β + 1 / 2 + 1 / 2 = β + 1 by ring] at hp
    exact hp

/-- Uniform native data control the actual once-localized coefficients;
the constants can be passed directly to uniform periodization. -/
theorem uniform_coefficients_localized_jets (h : UniformNativeCovariance s K H T)
    (hR : ∀ q, UniformLocalJets s (fun _ _ x => s.zeta x) β K (fun l n i x => R l i n x q))
    (hm : UniformLocalJets s (fun _ _ _ => 1) 0 K (fun l n i => mask l i n))
    (hv : UniformLocalJets s W 0 K (fun l n i => v l i n))
    (hW : ∀ l n x, x ∈ s.domain → 0 ≤ W l n x)
    (hN : UniformLocalJets s (fun _ _ _ => 1) 0 K (fun l n i => (a l i).normal s (d l i) n))
    (hNdot : UniformLocalJets s (fun _ _ _ => 1) 0 K (fun l n i => Ndot l i n))
    (hA : UniformLocalJets s (fun _ _ _ => 1) 0 K (fun l n i => A l i n))
    {b M : ℝ} (hb : 0 < b)
    (hl : ∀ l n i x, x ∈ s.domain → x ∈ K l n i → b ≤ ‖(a l i).normal s (d l i) n x‖)
    (hu : ∀ l n i x, x ∈ s.domain → x ∈ K l n i → ‖(a l i).normal s (d l i) n x‖ ≤ M)
    (hK : UniformPrimaryWeights.UniformBandBound s (1 / 2)
      (fun li : L × I => fun n => 1 / (a li.1 li.2).frequency n))
    {ψ : L → I → ℕ → D → ℝ}
    (hψ : UniformLocalJets s (fun _ _ _ => 1) 0 K (fun l n i => ψ l i n)) (j : Fin 2) :
    UniformLocalJets s (fun l n x => Real.sqrt (s.zeta x) * W l n x) (β + 1 / 2) K
      (fun l n i => ((SignedWaveUpdate.coefficients (a l i) s (d l i) (H l i) (T l i) (R l i)
        (mask l i) (v l i) (Ndot l i) (A l i) j).withCutoff (ψ l i)).amplitude n) ∧
    UniformLocalJets s (fun l n x => Real.sqrt (s.zeta x) * W l n x) (β + 1) K
      (fun l n i => ((SignedWaveUpdate.coefficients (a l i) s (d l i) (H l i) (T l i) (R l i)
        (mask l i) (v l i) (Ndot l i) (A l i) j).withCutoff (ψ l i)).pressure n) := by
  obtain ⟨ha, hp⟩ := uniform_coefficients_jets h hR hm hv hW hN hNdot hA hb hl hu hK j
  have hw l n x hx := mul_nonneg (Real.sqrt_nonneg (s.zeta x)) (hW l n x hx)
  refine ⟨uniform_smul hψ ha hw, ?_⟩
  simpa only [LinearWaveBounds.WaveCoefficients.withCutoff, Complex.real_smul] using
    uniform_smul hψ hp hw

end UniformActualCoefficients

end NavierStokes.SignedCopyBounds
