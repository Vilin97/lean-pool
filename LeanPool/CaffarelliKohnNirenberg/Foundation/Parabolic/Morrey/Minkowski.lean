/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Foundation.Parabolic.Integration.Average
public import LeanPool.CaffarelliKohnNirenberg.Foundation.Parabolic.Morrey.Inclusions
public import Mathlib.MeasureTheory.Integral.Prod
public import Mathlib.MeasureTheory.Integral.MeanInequalities

/-!
# Minkowski

Part of the Caffarelli–Kohn–Nirenberg partial regularity proof.
-/

@[expose] public section

open MeasureTheory MeasureTheory.Measure Set Metric
open scoped ENNReal NNReal Topology


noncomputable section

namespace CKN.Foundation.Parabolic.Morrey

/-- The Morrey cell for an extended nonnegative-valued function. -/
def morreyENormCell (p q : ℝ) (f : ParabolicPoint → ℝ≥0∞)
    (z : ParabolicPoint) (r : ℝ) : ℝ≥0∞ :=
  (ENNReal.ofReal r) ^ (-(5 * (1 - p / q) / p)) *
    (∫⁻ w in parabolicCylinder z.1 z.2 r, f w ^ p) ^ (1 / p)

/-- The extended nonnegative-valued Morrey seminorm. -/
def morreyENorm (p q : ℝ) (f : ParabolicPoint → ℝ≥0∞) : ℝ≥0∞ :=
  ⨆ z : ParabolicPoint, ⨆ r : {r : ℝ // 0 < r}, morreyENormCell p q f z r.1

theorem morreyENorm_ofReal_abs (p q : ℝ) (f : ParabolicPoint → ℝ) :
    morreyENorm p q (fun z => ENNReal.ofReal |f z|) = morreyNorm p q f := by
  rfl

theorem morreyNorm_holder {p p₁ p₂ q q₁ q₂ : ℝ}
    (hp₁ : 1 ≤ p₁) (hp₂ : 1 ≤ p₂)
    (hrelp : 1 / p = 1 / p₁ + 1 / p₂)
    (hrelq : 1 / q = 1 / q₁ + 1 / q₂)
    {f g : ParabolicPoint → ℝ} (hf : AEMeasurable f volume)
    (hg : AEMeasurable g volume) :
    morreyNorm p q (fun z => f z * g z) ≤
      morreyNorm p₁ q₁ f * morreyNorm p₂ q₂ g :=
  morreyNorm_mul_le hp₁ hp₂ hrelp hrelq hf hg

theorem morreyNorm_lower_integrability {p' p q : ℝ} (hp' : 1 ≤ p')
    (hpp : p' ≤ p) (hpq : p ≤ q) {f : ParabolicPoint → ℝ}
    (hf : AEMeasurable f volume) :
    morreyNorm p' q f ≤
      (volume (parabolicCylinder 0 0 1)) ^ (1 / p' - 1 / p) *
        morreyNorm p q f :=
  morreyNorm_lower_p hp' hpp hpq hf

theorem morreyNorm_lower_morrey_exponent {p q q' : ℝ} (hp : 1 ≤ p)
    (hpq : p ≤ q) (hpq' : p ≤ q') (hq'q : q' ≤ q)
    {f : ParabolicPoint → ℝ} {z₀ : ParabolicPoint} {R : ℝ} (hR : 0 < R)
    (hsupp : ∀ w ∉ parabolicCylinder z₀.1 z₀.2 R, f w = 0) :
    morreyNorm p q' f ≤
      (ENNReal.ofReal R) ^ (5 * (1 / q' - 1 / q)) * morreyNorm p q f :=
  morreyNorm_bounded_support hp hpq hpq' hq'q hR hsupp

private theorem lintegral_minkowski
    {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    {μ : Measure α} {ν : Measure β} [SFinite μ] [SFinite ν]
    (hν : ν Set.univ ≠ ∞) {p : ℝ} (hp : 1 ≤ p)
    {F : α × β → ℝ≥0∞} (hF : AEMeasurable F (μ.prod ν)) :
    (∫⁻ y, (∫⁻ x, F (x, y) ∂μ) ^ p ∂ν) ^ (1 / p) ≤
      ∫⁻ x, (∫⁻ y, F (x, y) ^ p ∂ν) ^ (1 / p) ∂μ := by
  let h : β → ℝ≥0∞ := fun y => ∫⁻ x, F (x, y) ∂μ
  have hh : AEMeasurable h ν := by
    exact hF.lintegral_prod_left'
  by_cases hpeq : p = 1
  · subst p
    simp only [div_self (by norm_num : (1 : ℝ) ≠ 0), ENNReal.rpow_one]
    have hswap := MeasureTheory.lintegral_lintegral_swap
      (f := fun x y => F (x, y)) (by
        change AEMeasurable F (μ.prod ν)
        exact hF)
    exact hswap.symm.le
  have hpgt : 1 < p := lt_of_le_of_ne hp (Ne.symm hpeq)
  let q : ℝ := p / (p - 1)
  have hpq : p.HolderConjugate q := by
    apply Real.holderConjugate_iff.mpr
    constructor
    · exact hpgt
    · dsimp [q]
      field_simp [ne_of_gt hpgt]
      ring
  let m : ℕ → β → ℝ≥0∞ := fun n y => min (h y) n
  have hm : ∀ n, AEMeasurable (m n) ν := by
    intro n
    exact hh.min measurable_const.aemeasurable
  have hmp : ∀ n, AEMeasurable (fun y => m n y ^ p) ν := by
    intro n
    exact (hm n).pow_const p
  have hmp_mono : Monotone (fun n => fun y => m n y ^ p) := by
    intro n₁ n₂ hn y
    exact ENNReal.rpow_le_rpow (min_le_min_left _ (by exact_mod_cast hn))
      (le_trans zero_le_one hp)
  have hsup_m : ∀ y, (⨆ n, m n y) = h y := by
    intro y
    apply le_antisymm
    · exact iSup_le fun n => min_le_left _ _
    · by_cases hy : h y = ∞
      · rw [hy]
        rw [← ENNReal.iSup_natCast]
        apply iSup_mono
        intro n
        simp [m, hy]
      · obtain ⟨n, hn⟩ := exists_nat_gt (h y).toReal
        have hn' : h y < (n : ℝ≥0∞) :=
          (ENNReal.toReal_lt_toReal hy (ENNReal.natCast_ne_top n)).mp hn
        exact le_iSup_of_le n (by simp [m, min_eq_left hn'.le])
  have hsup_mp : (⨆ n, fun y => m n y ^ p) = fun y => h y ^ p := by
    funext y
    rw [iSup_apply]
    apply le_antisymm
    · exact iSup_le fun n => ENNReal.rpow_le_rpow (min_le_left _ _)
        (le_trans zero_le_one hp)
    · by_cases hy : h y = ∞
      · rw [hy, ENNReal.top_rpow_of_pos (zero_lt_one.trans_le hp)]
        rw [← ENNReal.iSup_natCast]
        apply iSup_mono
        intro n
        by_cases hn : n = 0
        · simp [hn]
        · have hbase : (1 : ℝ≥0∞) ≤ (n : ℝ≥0∞) := by
            exact_mod_cast (Nat.one_le_iff_ne_zero.mpr hn)
          simpa [m, hy] using (ENNReal.rpow_le_rpow_of_exponent_le hbase hp)
      · obtain ⟨n, hn⟩ := exists_nat_gt (h y).toReal
        have hn' : h y < (n : ℝ≥0∞) :=
          (ENNReal.toReal_lt_toReal hy (ENNReal.natCast_ne_top n)).mp hn
        exact le_iSup_of_le n (by simp [m, min_eq_left hn'.le])
  have hbound : ∀ n, (∫⁻ y, m n y ^ p ∂ν) ≠ ∞ := by
    intro n
    apply ne_of_lt
    calc
      (∫⁻ y, m n y ^ p ∂ν) ≤ ∫⁻ _y, (n : ℝ≥0∞) ^ p ∂ν := by
        apply lintegral_mono
        intro y
        exact ENNReal.rpow_le_rpow (min_le_right _ _) (le_trans zero_le_one hp)
      _ = (n : ℝ≥0∞) ^ p * ν Set.univ := lintegral_const _
      _ < ∞ := ENNReal.mul_lt_top
        (ENNReal.rpow_lt_top_of_nonneg (le_trans zero_le_one hp) (ENNReal.natCast_ne_top n))
        (lt_top_iff_ne_top.mpr hν)
  have hfiber_x : ∀ᵐ x ∂μ, AEMeasurable (fun y => F (x, y)) ν := by
    obtain ⟨G, hG, hFG⟩ := hF
    have hFG' := Measure.ae_ae_eq_curry_of_prod hFG
    filter_upwards [hFG'] with x hx
    have hgx : AEMeasurable (fun y => G (x, y)) ν := by
      simpa [Function.comp_def] using (hG.comp measurable_prodMk_left).aemeasurable
    exact hgx.congr hx.symm
  have hfiber_y : ∀ᵐ y ∂ν, AEMeasurable (fun x => F (x, y)) μ := by
    obtain ⟨G, hG, hFG⟩ := hF
    have hFGswap : (fun z => F z.swap) =ᵐ[ν.prod μ] (fun z => G z.swap) :=
      hFG.comp_tendsto Measure.measurePreserving_swap.quasiMeasurePreserving.tendsto_ae
    have hFG' := Measure.ae_ae_eq_curry_of_prod hFGswap
    filter_upwards [hFG'] with y hy
    have hgy : AEMeasurable (fun x => G (x, y)) μ := by
      simpa [Function.comp_def] using (hG.comp measurable_prodMk_right).aemeasurable
    exact hgy.congr hy.symm
  let L : α → ℝ≥0∞ := fun x => (∫⁻ y, F (x, y) ^ p ∂ν) ^ (1 / p)
  have hL : AEMeasurable L μ := by
    exact (hF.pow_const p).lintegral_prod_right'.pow_const (1 / p)
  have hlocal : ∀ n, (∫⁻ y, m n y ^ p ∂ν) ^ (1 / p) ≤
      (∫⁻ x, L x ∂μ) := by
    intro n
    let C : ℝ≥0∞ := (∫⁻ y, m n y ^ p ∂ν) ^ (1 / q)
    have hpoint : ∀ y, m n y ^ p ≤ h y * m n y ^ (p - 1) := by
      intro y
      by_cases hm0 : m n y = 0
      · simp [hm0, ENNReal.zero_rpow_of_pos (zero_lt_one.trans_le hp)]
      have hm_top : m n y ≠ ∞ :=
        ne_top_of_le_ne_top (ENNReal.natCast_ne_top n) (min_le_right _ _)
      calc
        m n y ^ p = m n y ^ ((p - 1) + 1) := by congr 1; ring
        _ = m n y ^ (p - 1) * m n y ^ (1 : ℝ) := ENNReal.rpow_add _ _ hm0 hm_top
        _ = m n y ^ (p - 1) * m n y := by rw [ENNReal.rpow_one]
        _ ≤ m n y ^ (p - 1) * h y := mul_le_mul_right (min_le_left _ _) _
        _ = h y * m n y ^ (p - 1) := by ac_rfl
    have hprod : AEMeasurable
        (fun z : α × β => F z * m n z.2 ^ (p - 1)) (μ.prod ν) := by
      exact hF.mul ((hm n).pow_const (p - 1)).comp_snd
    have hswap := MeasureTheory.lintegral_lintegral_swap
      (f := fun x y => F (x, y) * m n y ^ (p - 1)) (by
        change AEMeasurable (fun z : α × β => F z * m n z.2 ^ (p - 1)) (μ.prod ν)
        exact hprod)
    have hlow : (∫⁻ y, m n y ^ p ∂ν) ≤
        ∫⁻ y, ∫⁻ x, F (x, y) * m n y ^ (p - 1) ∂μ ∂ν := by
      calc
        (∫⁻ y, m n y ^ p ∂ν) ≤ ∫⁻ y, h y * m n y ^ (p - 1) ∂ν :=
          lintegral_mono (fun y => hpoint y)
        _ = ∫⁻ y, ∫⁻ x, F (x, y) * m n y ^ (p - 1) ∂μ ∂ν := by
          apply lintegral_congr_ae
          filter_upwards [hfiber_y] with y hy
          simp only [h]
          exact (lintegral_mul_const'' _ hy).symm
    have hholder : ∀ᵐ x ∂μ,
        (∫⁻ y, F (x, y) * m n y ^ (p - 1) ∂ν) ≤ L x * C := by
      filter_upwards [hfiber_x] with x hx
      exact (ENNReal.lintegral_mul_rpow_le_lintegral_rpow_mul_lintegral_rpow
        hpq hx (hm n)).trans_eq (by rfl)
    have houter : (∫⁻ x, (∫⁻ y, F (x, y) * m n y ^ (p - 1) ∂ν) ∂μ) ≤
        ∫⁻ x, L x * C ∂μ := lintegral_mono_ae hholder
    have hfactor : (∫⁻ x, L x * C ∂μ) = (∫⁻ x, L x ∂μ) * C :=
      lintegral_mul_const'' C hL
    have hmain : (∫⁻ y, m n y ^ p ∂ν) ≤ (∫⁻ x, L x ∂μ) * C := by
      exact hlow.trans (hswap.symm.le.trans (houter.trans_eq hfactor))
    by_cases hA0 : (∫⁻ y, m n y ^ p ∂ν) = 0
    · calc
        (∫⁻ y, m n y ^ p ∂ν) ^ (1 / p) = 0 := by
          rw [hA0, ENNReal.zero_rpow_of_pos (one_div_pos.mpr (zero_lt_one.trans_le hp))]
        _ ≤ ∫⁻ x, L x ∂μ := zero_le
    have hC0 : 0 < C := by
      dsimp [C]
      exact ENNReal.rpow_pos (bot_lt_iff_ne_bot.mpr hA0) (hbound n)
    have hAeq : (∫⁻ y, m n y ^ p ∂ν) =
        (∫⁻ y, m n y ^ p ∂ν) ^ (1 / p) * C := by
      dsimp [C]
      rw [← ENNReal.rpow_add (1 / p) (1 / q)
        (ne_of_gt (bot_lt_iff_ne_bot.mpr hA0)) (hbound n)]
      have hexp : 1 / p + 1 / q = 1 := by
        dsimp [q]
        field_simp [ne_of_gt hpgt]
        ring
      rw [hexp, ENNReal.rpow_one]
    have hCtop : C ≠ ∞ := by
      dsimp [C]
      exact ENNReal.rpow_ne_top_of_nonneg (by positivity) (hbound n)
    rw [hAeq] at hmain
    by_contra hnot
    have hlt : (∫⁻ x, L x ∂μ) <
        (∫⁻ y, m n y ^ p ∂ν) ^ (1 / p) := lt_of_not_ge hnot
    exact (not_lt_of_ge hmain) (by
      simpa [C] using ENNReal.mul_lt_mul_left hC0.ne' hCtop hlt)
  have hAeq : (∫⁻ y, h y ^ p ∂ν) =
      ⨆ n, ∫⁻ y, m n y ^ p ∂ν := by
    rw [← hsup_mp]
    have hfun : (⨆ n, fun y => m n y ^ p) = fun y => ⨆ n, m n y ^ p := by
      funext y
      exact iSup_apply
    rw [hfun]
    exact lintegral_iSup' hmp
      (Filter.Eventually.of_forall (fun y n₁ n₂ hn => hmp_mono hn y))
  have hsup_le : (⨆ n, ∫⁻ y, m n y ^ p ∂ν) ≤ (∫⁻ x, L x ∂μ) ^ p := by
    refine iSup_le fun n => ?_
    calc
      (∫⁻ y, m n y ^ p ∂ν) =
          ((∫⁻ y, m n y ^ p ∂ν) ^ (1 / p)) ^ p := by
            simpa only [one_div] using (ENNReal.rpow_inv_rpow (y := p)
            (ne_of_gt (zero_lt_one.trans_le hp)) _).symm
      _ ≤ (∫⁻ x, L x ∂μ) ^ p :=
        ENNReal.rpow_le_rpow (hlocal n) (le_trans zero_le_one hp)
  calc
    (∫⁻ y, h y ^ p ∂ν) ^ (1 / p) ≤
        ((∫⁻ x, L x ∂μ) ^ p) ^ (1 / p) :=
      ENNReal.rpow_le_rpow (by rw [hAeq]; exact hsup_le) (by positivity)
    _ = ∫⁻ x, L x ∂μ := by
      rw [← ENNReal.rpow_mul]
      simp [ne_of_gt (zero_lt_one.trans_le hp)]

theorem morreyENorm_lintegral_le
    {α : Type*} [MeasurableSpace α] (μ : Measure α) [SFinite μ]
    {p q : ℝ} (hp : 1 ≤ p) (_ : p ≤ q)
    {F : α × ParabolicPoint → ℝ≥0∞}
    (hF : AEMeasurable F (μ.prod volume)) :
    morreyENorm p q (fun z => ∫⁻ w, F (w, z) ∂μ) ≤
      ∫⁻ w, morreyENorm p q (fun z => F (w, z)) ∂μ := by
  unfold morreyENorm
  refine iSup_le fun z => iSup_le fun r => ?_
  let Q : Set ParabolicPoint := parabolicCylinder z.1 z.2 r.1
  let ν : Measure ParabolicPoint := volume.restrict Q
  have hQ : MeasurableSet Q := by
    dsimp [Q, parabolicCylinder]
    exact (vec3Ball_measurable _ _).prod measurableSet_Ioc
  have hν : ν Set.univ ≠ ∞ := by
    rw [Measure.restrict_apply_univ]
    exact (Integration.volume_parabolicCylinder_lt_top).ne
  have hνQ : volume Q ≠ ∞ := by
    dsimp [Q]
    exact (Integration.volume_parabolicCylinder_lt_top).ne
  let _ : SFinite (volume : Measure ParabolicPoint) := by
    rw [Integration.volume_parabolicPoint_eq_prod]
    exact Measure.prod.instSFinite
  let _ : IsFiniteMeasure ν := by
    dsimp [ν]
    exact isFiniteMeasure_restrict.mpr hνQ
  have hFν : AEMeasurable F (μ.prod ν) := by
    rw [show μ.prod ν = (μ.prod volume).restrict (Set.univ ×ˢ Q) by
      dsimp [ν]
      rw [← Measure.prod_restrict (μ := μ) (ν := volume) Set.univ Q]
      simp]
    exact hF.restrict
  have hM := lintegral_minkowski hν hp hFν
  let A : ℝ≥0∞ := (ENNReal.ofReal r.1) ^ (-(5 * (1 - p / q) / p))
  let L : α → ℝ≥0∞ := fun w =>
    (∫⁻ y in Q, F (w, y) ^ p) ^ (1 / p)
  have hL : AEMeasurable L μ := by
    exact (hFν.pow_const p).lintegral_prod_right'.pow_const (1 / p)
  calc
    morreyENormCell p q (fun z => ∫⁻ w, F (w, z) ∂μ) z r.1 =
        A * (∫⁻ y in Q, (∫⁻ w, F (w, y) ∂μ) ^ p) ^ (1 / p) := by
          rfl
    _ ≤ A * (∫⁻ w, L w ∂μ) := by
      apply mul_le_mul_right
      simpa [ν, L] using hM
    _ = ∫⁻ w, A * L w ∂μ := by
      rw [lintegral_const_mul'' A hL]
    _ ≤ ∫⁻ w, morreyENorm p q (fun z => F (w, z)) ∂μ := by
      apply lintegral_mono
      intro w
      dsimp [A, L]
      have hcell : morreyENormCell p q (fun z => F (w, z)) z r.1 ≤
          (⨆ z' : ParabolicPoint, ⨆ s : {s : ℝ // 0 < s},
            morreyENormCell p q (fun z => F (w, z)) z' s.1) := by
        exact le_iSup_of_le z (le_iSup_of_le r le_rfl)
      simpa [morreyENorm, morreyENormCell] using hcell

private theorem morreyENormCell_translate (p q : ℝ) (f : ParabolicPoint → ℝ≥0∞)
    (a : Vec3) (τ : ℝ) (z : ParabolicPoint) (r : ℝ) :
    morreyENormCell p q (fun w => f (parabolicTranslate a τ w)) z r =
      morreyENormCell p q f (parabolicTranslate a τ z) r := by
  let e : ParabolicPoint ≃ᵐ ParabolicPoint :=
    (MeasurableEquiv.addLeft a).prodCongr (MeasurableEquiv.addLeft τ)
  let _ : SFinite (volume : Measure ParabolicPoint) := by
    rw [Integration.volume_parabolicPoint_eq_prod]
    exact Measure.prod.instSFinite
  have he : (e : ParabolicPoint → ParabolicPoint) =
      parabolicTranslate a τ := by
    funext w
    rfl
  have hmp : MeasurePreserving e volume volume := by
    have hmp' : MeasurePreserving (parabolicTranslate a τ) volume volume := by
      rw [Integration.volume_parabolicPoint_eq_prod]
      change MeasurePreserving (fun w : Vec3 × ℝ => (a + w.1, τ + w.2))
        (volume.prod volume) (volume.prod volume)
      exact (measurePreserving_add_left (volume : Measure Vec3) a).prod
        (measurePreserving_add_left (volume : Measure ℝ) τ)
    rw [he]
    exact hmp'
  have himage : e '' parabolicCylinder z.1 z.2 r =
      parabolicCylinder (a + z.1) (τ + z.2) r := by
    simpa [he] using parabolicCylinder_translate a z.1 τ z.2 r
  have hint := hmp.setLIntegral_comp_emb e.measurableEmbedding
    (fun w => f w ^ p) (parabolicCylinder z.1 z.2 r)
  rw [himage] at hint
  rw [he] at hint
  unfold morreyENormCell
  rw [show (∫⁻ w in parabolicCylinder z.1 z.2 r,
      (fun w => f (parabolicTranslate a τ w)) w ^ p) =
      ∫⁻ w in parabolicCylinder (a + z.1) (τ + z.2) r, f w ^ p by
        simpa [parabolicTranslate] using hint]
  simp [parabolicTranslate]

theorem morreyENorm_translate (p q : ℝ) (f : ParabolicPoint → ℝ≥0∞)
    (a : Vec3) (τ : ℝ) :
    morreyENorm p q (fun w => f (parabolicTranslate a τ w)) = morreyENorm p q f := by
  apply le_antisymm
  · unfold morreyENorm
    refine iSup_le fun z => iSup_le fun r => ?_
    rw [morreyENormCell_translate p q f a τ z r.1]
    exact le_iSup_of_le (parabolicTranslate a τ z)
      (le_iSup (fun s : {s : ℝ // 0 < s} =>
        morreyENormCell p q f (parabolicTranslate a τ z) s.1) r)
  · unfold morreyENorm
    refine iSup_le fun z => iSup_le fun r => ?_
    obtain ⟨z', hz'⟩ : ∃ z', parabolicTranslate a τ z' = z := by
      refine ⟨parabolicTranslate (-a) (-τ) z, ?_⟩
      apply Prod.ext <;> simp [parabolicTranslate, add_comm]
    rw [← hz', ← morreyENormCell_translate p q f a τ z' r.1]
    exact le_iSup_of_le z'
      (le_iSup (fun s : {s : ℝ // 0 < s} =>
        morreyENormCell p q (fun w => f (parabolicTranslate a τ w)) z' s.1) r)

private theorem morreyENorm_const_mul (p q : ℝ) (c : ℝ≥0∞)
    (f : ParabolicPoint → ℝ≥0∞) (hp : 0 < p) (hc : c ≠ ∞) :
    morreyENorm p q (fun z => c * f z) = c * morreyENorm p q f := by
  have hp0 : 0 ≤ p := hp.le
  have hcp : c ^ p ≠ ∞ := ENNReal.rpow_ne_top_of_nonneg hp0 hc
  have hroot : (c ^ p) ^ (1 / p) = c := by
    rw [← ENNReal.rpow_mul]
    have hmul : p * (1 / p) = 1 := by
      field_simp
    rw [hmul, ENNReal.rpow_one]
  have hcell (z : ParabolicPoint) (r : ℝ) :
      morreyENormCell p q (fun w => c * f w) z r =
        c * morreyENormCell p q f z r := by
    unfold morreyENormCell
    have hpow : (fun w => (c * f w) ^ p) = (fun w => c ^ p * f w ^ p) := by
      funext w
      exact ENNReal.mul_rpow_of_nonneg _ _ hp0
    rw [hpow, lintegral_const_mul' (c ^ p) _ hcp]
    rw [ENNReal.mul_rpow_of_nonneg _ _ (by positivity : 0 ≤ (1 / p : ℝ))]
    rw [hroot]
    ac_rfl
  apply le_antisymm
  · unfold morreyENorm
    refine iSup_le fun z => iSup_le fun r => ?_
    rw [hcell]
    exact mul_le_mul_right (le_iSup_of_le z (le_iSup (fun s : {s : ℝ // 0 < s} =>
      morreyENormCell p q f z s.1) r)) c
  · unfold morreyENorm
    rw [ENNReal.mul_iSup]
    apply iSup_le
    intro z
    rw [ENNReal.mul_iSup]
    apply iSup_le
    intro r
    calc
      c * morreyENormCell p q f z r = morreyENormCell p q (fun w => c * f w) z r :=
        (hcell z r).symm
      _ ≤ (⨆ z' : ParabolicPoint, ⨆ r' : {r' : ℝ // 0 < r'},
        morreyENormCell p q (fun w => c * f w) z' r'.1) :=
        le_iSup_of_le z (le_iSup_of_le r le_rfl)

def parabolicConvolution (K f : ParabolicPoint → ℝ≥0∞) (z : ParabolicPoint) : ℝ≥0∞ :=
  ∫⁻ w, K w * f (parabolicTranslate (-w.1) (-w.2) z) ∂volume

theorem morreyENorm_parabolicConvolution_le
    {p q : ℝ} (hp : 1 ≤ p) (hpq : p ≤ q)
    {K f : ParabolicPoint → ℝ≥0∞}
    (hF : AEMeasurable
      (fun wz : ParabolicPoint × ParabolicPoint =>
        K wz.1 * f (parabolicTranslate (-wz.1.1) (-wz.1.2) wz.2))
      (volume.prod volume))
    (hKtop : ∀ w, K w ≠ ∞)
    (hfinit : morreyENorm p q f ≠ ∞) :
    morreyENorm p q (parabolicConvolution K f) ≤
      (∫⁻ w, K w ∂volume) * morreyENorm p q f := by
  let _ : SFinite (volume : Measure ParabolicPoint) := by
    rw [Integration.volume_parabolicPoint_eq_prod]
    exact Measure.prod.instSFinite
  have hp' : 0 < p := lt_of_lt_of_le zero_lt_one hp
  have hM := morreyENorm_lintegral_le (volume : Measure ParabolicPoint) hp hpq hF
  calc
    morreyENorm p q (parabolicConvolution K f) ≤
        ∫⁻ w, morreyENorm p q
          (fun z => K w * f (parabolicTranslate (-w.1) (-w.2) z)) ∂volume := by
      change morreyENorm p q
        (fun z => ∫⁻ w, K w * f (parabolicTranslate (-w.1) (-w.2) z) ∂volume) ≤ _
      exact hM
    _ = ∫⁻ w, K w * morreyENorm p q f ∂volume := by
      apply lintegral_congr
      intro w
      rw [morreyENorm_const_mul p q (K w)
        (fun z => f (parabolicTranslate (-w.1) (-w.2) z)) hp' (hKtop w)]
      rw [morreyENorm_translate p q f (-w.1) (-w.2)]
    _ = (∫⁻ w, K w ∂volume) * morreyENorm p q f := by
      exact lintegral_mul_const' _ _ hfinit

def spatialConvolution (K : Vec3 → ℝ≥0∞) (f : ParabolicPoint → ℝ≥0∞)
    (z : ParabolicPoint) : ℝ≥0∞ :=
  ∫⁻ y, K y * f (parabolicTranslate (-y) 0 z) ∂volume

theorem morreyENorm_spatialConvolution_le
    {p q : ℝ} (hp : 1 ≤ p) (hpq : p ≤ q)
    {K : Vec3 → ℝ≥0∞} {f : ParabolicPoint → ℝ≥0∞}
    (hF : AEMeasurable
      (fun yz : Vec3 × ParabolicPoint =>
        K yz.1 * f (parabolicTranslate (-yz.1) 0 yz.2))
      (volume.prod volume))
    (hKtop : ∀ y, K y ≠ ∞)
    (hfinit : morreyENorm p q f ≠ ∞) :
    morreyENorm p q (spatialConvolution K f) ≤
      (∫⁻ y, K y ∂volume) * morreyENorm p q f := by
  have hp' : 0 < p := lt_of_lt_of_le zero_lt_one hp
  have hM := morreyENorm_lintegral_le (volume : Measure Vec3) hp hpq hF
  calc
    morreyENorm p q (spatialConvolution K f) ≤
        ∫⁻ y, morreyENorm p q
          (fun z => K y * f (parabolicTranslate (-y) 0 z)) ∂volume := by
      change morreyENorm p q
        (fun z => ∫⁻ y, K y * f (parabolicTranslate (-y) 0 z) ∂volume) ≤ _
      exact hM
    _ = ∫⁻ y, K y * morreyENorm p q f ∂volume := by
      apply lintegral_congr
      intro y
      rw [morreyENorm_const_mul p q (K y)
        (fun z => f (parabolicTranslate (-y) 0 z)) hp' (hKtop y)]
      rw [morreyENorm_translate p q f (-y) 0]
    _ = (∫⁻ y, K y ∂volume) * morreyENorm p q f := by
      exact lintegral_mul_const' _ _ hfinit

end CKN.Foundation.Parabolic.Morrey
