/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Pressure.PkBoundsP7SolutionMeas
public import LeanPool.CaffarelliKohnNirenberg.Pressure.PkBoundsUnconditionalConstants

/-!
# Pk Bounds P7 Solution Bound

Part of the Caffarelli–Kohn–Nirenberg partial regularity proof.
-/

@[expose] public section

open MeasureTheory MeasureTheory.Measure Set Filter
open scoped BigOperators ENNReal NNReal Topology
open CKN.Foundation.Parabolic
open CKN.Foundation.Parabolic.Integration
open CKN.Foundation.Euclidean

noncomputable section

namespace CKN

private lemma hedbergNearConstant_ne_top : hedbergNearConstant ≠ ∞ := by
  unfold hedbergNearConstant
  change (∑' n : ℕ,
    (ENNReal.ofReal ((2 : ℝ) ^ (Int.negSucc n : ℝ))) ^ (-2 : ℝ) *
      ENNReal.ofReal ((4 * ((2 : ℝ) ^ (Int.negSucc n : ℝ))) ^ 3)) ≠ ∞
  have hterm : ∀ n : ℕ,
      (ENNReal.ofReal ((2 : ℝ) ^ (Int.negSucc n : ℝ))) ^ (-2 : ℝ) *
          ENNReal.ofReal ((4 * ((2 : ℝ) ^ (Int.negSucc n : ℝ))) ^ 3) =
        ENNReal.ofReal (32 * ((1 / 2 : ℝ) ^ n)) := by
    intro n
    let b : ℝ := (1 / 2 : ℝ) ^ (n + 1)
    have hb : 0 < b := by dsimp [b]; positivity
    have hbase : (2 : ℝ) ^ (Int.negSucc n : ℝ) = b := by
      dsimp [b]
      rw [Int.cast_negSucc]
      rw [Real.rpow_neg (by norm_num)]
      rw [← Real.rpow_natCast]
      rw [show (1 / 2 : ℝ) = 2 ^ (-1 : ℝ) by
        rw [Real.rpow_neg (by positivity)]
        norm_num]
      rw [← Real.rpow_mul (by positivity)]
      calc
        (2 ^ (↑(n + 1) : ℝ))⁻¹ = 2 ^ (-(↑(n + 1) : ℝ)) :=
          (Real.rpow_neg (by positivity) _).symm
        _ = 2 ^ (-1 * (↑(n + 1) : ℝ)) := by congr 1; ring
    rw [hbase]
    rw [show (4 * b) ^ 3 = (4 : ℝ) ^ 3 * b ^ 3 by ring]
    rw [ENNReal.ofReal_mul (by positivity)]
    norm_num
    rw [ENNReal.ofReal_rpow_of_pos hb]
    calc
      ENNReal.ofReal (b ^ (-2 : ℝ)) *
          (64 * ENNReal.ofReal (b ^ (3 : ℕ))) =
          ENNReal.ofReal (b ^ (-2 : ℝ)) *
            (ENNReal.ofReal (64 : ℝ) * ENNReal.ofReal (b ^ (3 : ℕ))) := by
        norm_num
      _ = (ENNReal.ofReal (b ^ (-2 : ℝ)) * ENNReal.ofReal (64 : ℝ)) *
          ENNReal.ofReal (b ^ (3 : ℕ)) := by ring
      _ = ENNReal.ofReal (b ^ (-2 : ℝ) * 64) *
          ENNReal.ofReal (b ^ (3 : ℕ)) := by
        rw [ENNReal.ofReal_mul (by positivity)]
      _ = ENNReal.ofReal (b ^ (-2 : ℝ) * 64 * b ^ (3 : ℕ)) := by
        conv_rhs =>
          rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_mul (by positivity)]
        rw [ENNReal.ofReal_mul (by positivity)]
      _ = 32 * ENNReal.ofReal (1 / 2 : ℝ) ^ n := by
        have hreal : b ^ (-2 : ℝ) * 64 * b ^ (3 : ℕ) =
            32 * ((1 / 2 : ℝ) ^ n) := by
          dsimp [b]
          have hbase' : (1 / 2 : ℝ) ^ (n + 1) =
              (1 / 2 : ℝ) ^ (↑(n + 1) : ℝ) :=
            (Real.rpow_natCast (1 / 2 : ℝ) (n + 1)).symm
          rw [hbase']
          rw [← Real.rpow_mul (by positivity)]
          rw [← Real.rpow_natCast ((1 / 2 : ℝ) ^ (↑(n + 1) : ℝ)) 3]
          rw [← Real.rpow_mul (by positivity)]
          calc
            (1 / 2 : ℝ) ^ (↑(n + 1) * (-2 : ℝ)) * 64 *
                (1 / 2 : ℝ) ^ (↑(n + 1) * (3 : ℝ)) =
                64 * ((1 / 2 : ℝ) ^ (↑(n + 1) * (-2 : ℝ)) *
                  (1 / 2 : ℝ) ^ (↑(n + 1) * (3 : ℝ))) := by ring
            _ = 64 * (1 / 2 : ℝ) ^
                (↑(n + 1) * (-2 : ℝ) + ↑(n + 1) * (3 : ℝ)) := by
              rw [Real.rpow_add (by positivity)]
            _ = 32 * (1 / 2 : ℝ) ^ n := by
              rw [show ↑(n + 1) * (-2 : ℝ) + ↑(n + 1) * (3 : ℝ) =
                ↑n + 1 by push_cast; ring]
              rw [show (1 / 2 : ℝ) ^ ((n : ℝ) + 1) =
                (1 / 2 : ℝ) ^ (n : ℝ) * (1 / 2 : ℝ) by
                rw [Real.rpow_add (by positivity)]
                norm_num]
              rw [Real.rpow_natCast]
              ring
        rw [hreal, ENNReal.ofReal_mul (by positivity)]
        norm_num
  rw [show (∑' n : ℕ,
      (ENNReal.ofReal ((2 : ℝ) ^ (Int.negSucc n : ℝ))) ^ (-2 : ℝ) *
        ENNReal.ofReal ((4 * ((2 : ℝ) ^ (Int.negSucc n : ℝ))) ^ 3)) =
      ∑' n : ℕ, ENNReal.ofReal (32 * ((1 / 2 : ℝ) ^ n)) by
    congr 1
    funext n
    exact hterm n]
  exact (Summable.tsum_ofReal_ne_top (by
    have hs : Summable (fun n : ℕ => 32 * ((1 / 2 : ℝ) ^ n)) := by
      exact summable_geometric_two.mul_left 32
    exact hs))

private lemma far_term_eq (n : ℕ) :
    ((ENNReal.ofReal ((2 : ℝ) ^ (n : ℝ))) ^ (-(10 / 3 : ℝ)) *
      ENNReal.ofReal ((4 * ((2 : ℝ) ^ (n : ℝ))) ^ 3)) ^ (3 / 5 : ℝ) =
      ENNReal.ofReal ((64 : ℝ) ^ (3 / 5 : ℝ)) *
        ENNReal.ofReal ((2 : ℝ) ^ (-(1 / 5 : ℝ))) ^ n := by
  let a : ℝ := (2 : ℝ) ^ (n : ℝ)
  have ha : 0 < a := by dsimp [a]; positivity
  rw [show (2 : ℝ) ^ (n : ℝ) = a by rfl]
  rw [show (4 * a) ^ 3 = (4 : ℝ) ^ 3 * a ^ 3 by ring]
  rw [ENNReal.ofReal_mul (by positivity)]
  norm_num
  rw [ENNReal.ofReal_rpow_of_pos ha]
  have hinside : ENNReal.ofReal (a ^ (-(10 / 3 : ℝ))) *
      (64 * ENNReal.ofReal (a ^ (3 : ℕ))) =
      ENNReal.ofReal (64 * a ^ (-(10 / 3 : ℝ)) * a ^ (3 : ℕ)) := by
    conv_rhs =>
      rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_mul (by positivity)]
    rw [show (64 : ℝ≥0∞) = ENNReal.ofReal (64 : ℝ) by norm_num]
    ring_nf
  rw [hinside]
  rw [ENNReal.ofReal_rpow_of_pos (by positivity)]
  have hreal : (64 * a ^ (-(10 / 3 : ℝ)) * a ^ (3 : ℕ)) ^
      (3 / 5 : ℝ) =
      (64 : ℝ) ^ (3 / 5 : ℝ) * (2 : ℝ) ^ (-(1 / 5 : ℝ) * n) := by
    have ha3 : a ^ (3 : ℕ) = a ^ (3 : ℝ) := by norm_num
    rw [ha3]
    rw [show 64 * a ^ (-(10 / 3 : ℝ)) * a ^ (3 : ℝ) =
      64 * (a ^ (-(10 / 3 : ℝ)) * a ^ (3 : ℝ)) by ring]
    rw [Real.mul_rpow (by positivity) (by positivity)]
    rw [← Real.rpow_add ha]
    have hsum : -(10 / 3 : ℝ) + 3 = -(1 / 3 : ℝ) := by ring
    rw [hsum]
    rw [← Real.rpow_mul (by positivity)]
    rw [← Real.rpow_mul (by positivity)]
    rw [show (-(1 / 3 : ℝ)) * (3 / 5 : ℝ) = -(1 / 5 : ℝ) by ring]
    rw [show (n : ℝ) * (-(1 / 5 : ℝ)) = -(1 / 5 : ℝ) * n by ring]
  rw [hreal, ENNReal.ofReal_mul (by positivity)]
  congr 1
  have hpow : (2 : ℝ) ^ (-(1 / 5 : ℝ) * n) =
      ((2 : ℝ) ^ (-(1 / 5 : ℝ))) ^ n := by
    rw [← Real.rpow_natCast]
    rw [Real.rpow_mul (by positivity)]
  rw [hpow, ENNReal.ofReal_pow (by positivity)]

private lemma hedbergFarConstant_ne_top : hedbergFarConstant ≠ ∞ := by
  unfold hedbergFarConstant
  change (∑' n : ℕ,
    ((ENNReal.ofReal ((2 : ℝ) ^ (n : ℝ))) ^ (-(10 / 3 : ℝ)) *
      ENNReal.ofReal ((4 * ((2 : ℝ) ^ (n : ℝ))) ^ 3)) ^ (3 / 5 : ℝ)) ≠ ∞
  have hterm : ∀ n : ℕ,
      ((ENNReal.ofReal ((2 : ℝ) ^ (n : ℝ))) ^ (-(10 / 3 : ℝ)) *
        ENNReal.ofReal ((4 * ((2 : ℝ) ^ (n : ℝ))) ^ 3)) ^ (3 / 5 : ℝ) =
      ENNReal.ofReal ((64 : ℝ) ^ (3 / 5 : ℝ) *
        ((2 : ℝ) ^ (-(1 / 5 : ℝ))) ^ n) := by
    intro n
    have h0 := far_term_eq n
    rw [h0]
    rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_pow (by positivity)]
  rw [show (∑' n : ℕ,
      ((ENNReal.ofReal ((2 : ℝ) ^ (n : ℝ))) ^ (-(10 / 3 : ℝ)) *
        ENNReal.ofReal ((4 * ((2 : ℝ) ^ (n : ℝ))) ^ 3)) ^ (3 / 5 : ℝ)) =
      ∑' n : ℕ, ENNReal.ofReal ((64 : ℝ) ^ (3 / 5 : ℝ) *
        ((2 : ℝ) ^ (-(1 / 5 : ℝ))) ^ n) by
    congr 1
    funext n
    exact hterm n]
  apply Summable.tsum_ofReal_ne_top
  have hr : ‖(2 : ℝ) ^ (-(1 / 5 : ℝ))‖ < 1 := by
    rw [Real.norm_of_nonneg (by positivity)]
    exact Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by norm_num)
  exact (summable_geometric_of_norm_lt_one hr).mul_left ((64 : ℝ) ^ (3 / 5 : ℝ))

private lemma hlsRieszConstant_ne_top : hlsRieszConstant ≠ ∞ := by
  unfold hlsRieszConstant
  exact ENNReal.mul_ne_top
    (ENNReal.add_ne_top.mpr ⟨hedbergNearConstant_ne_top, hedbergFarConstant_ne_top⟩)
    (by
      apply ENNReal.rpow_ne_top_of_nonneg (by positivity)
      apply ENNReal.div_ne_top
      · apply ENNReal.mul_ne_top
        · apply ENNReal.mul_ne_top
          · finiteness
          · exact ENNReal.ofReal_ne_top
        · exact ENNReal.ofReal_ne_top
      · exact (ENNReal.ofReal_pos.mpr (by norm_num)).ne')

/-- Force coefficient in the P7 estimate after the Hardy–Littlewood–Sobolev bound. -/
noncomputable def pressureP7SolutionConstant (q : ℝ) : ℝ≥0∞ :=
  (3 * (ENNReal.ofReal ((4 * Real.pi)⁻¹) * hlsRieszConstant)) *
    ENNReal.ofReal (4 * Real.pi / 3) ^ (1 - 1 / q : ℝ)

theorem pressureP7SolutionConstant_ne_top {q : ℝ} (hq : 5 / 2 < q) :
    pressureP7SolutionConstant q ≠ ∞ := by
  unfold pressureP7SolutionConstant
  have hqpos : 0 < q := by linarith only [hq]
  have hexp : 0 ≤ 1 - 1 / q := by
    apply sub_nonneg.mpr
    apply (div_le_iff₀ hqpos).2
    nlinarith only [hq]
  apply ENNReal.mul_ne_top
  · apply ENNReal.mul_ne_top
    · norm_num
    · apply ENNReal.mul_ne_top
      · exact ENNReal.ofReal_ne_top
      · exact hlsRieszConstant_ne_top
  · apply ENNReal.rpow_ne_top_of_nonneg hexp
    exact ENNReal.ofReal_ne_top

private lemma pressureP7_bound_hQr_1 :
    ∀ {z : ParabolicPoint} {ρ r : ℝ},
      (0 : ℝ) < ρ →
        (0 : ℝ) < r → r ≤ ρ / (2 : ℝ) → parabolicCylinder z.1 z.2 r ⊆ parabolicCylinder z.1 z.2 ρ
    := by
  intro z ρ r hρ hr hhalf w hw
  change w.1 ∈ vec3Ball z.1 r ∧
    w.2 ∈ Ioc (z.2 - r ^ 2) z.2 at hw
  change w.1 ∈ vec3Ball z.1 ρ ∧
    w.2 ∈ Ioc (z.2 - ρ ^ 2) z.2
  rcases hw with ⟨hwx, hwt⟩
  refine ⟨?_, ?_⟩
  · rw [mem_vec3Ball] at hwx ⊢
    have hrho : r ≤ ρ := hhalf.trans (by linarith only [hρ])
    exact lt_of_lt_of_le hwx hrho
  · have hρ0 : 0 ≤ ρ := by linarith only [hhalf, hr]
    have hsq : r ^ 2 ≤ ρ ^ 2 := by
      exact (sq_le_sq₀ hr.le hρ0).2 (by linarith only [hhalf, hρ0])
    exact ⟨by linarith only [hwt.1, hsq], hwt.2⟩

private lemma pressureP7_bound_hPprod_2 :
    ∀ {Ω : Set Vec3} {I : Set ℝ} {q : ℝ} {u : ParabolicPoint → Vec3}
      {Du : ParabolicPoint → Fin (3 : ℕ) → Vec3} {p : ParabolicPoint → ℝ}
      {f : ParabolicPoint → Vec3},
      IsSuitableWeakSolutionIntegrable Ω I q u Du p f →
        ∀ {z : ParabolicPoint} {ρ r : ℝ} (hρ : (0 : ℝ) < ρ),
          closure (parabolicCylinder z.1 z.2 ρ) ⊆ spaceTimeSet Ω I →
            let Br : Set Vec3 := vec3Ball z.1 r;
            let Tr : Set ℝ := Ioc (z.2 - r ^ (2 : ℕ)) z.2;
            parabolicCylinder z.1 z.2 r ⊆ parabolicCylinder z.1 z.2 ρ →
              AEStronglyMeasurable (β := ℝ) (m₀ := Prod.instMeasurableSpace)
                (fun (w : Vec3 × ℝ) => pressureP7 (mollifiedBallCutoff z.1 hρ) f w.2 w.1)
                (Measure.prod (Measure.restrict volume Br) (Measure.restrict volume Tr))
    := by
  intro Ω I q u Du p f hsol z ρ r hρ hsub Br Tr hQr
  have hP := pressureP7_aestronglyMeasurable_on_cylinder hsol hρ hsub
  have hP' := hP.mono_measure (Measure.restrict_mono_set volume hQr)
  have hset : parabolicCylinder z.1 z.2 r = Br ×ˢ Tr := by
    ext w
    rfl
  rw [hset] at hP'
  have hmeasure : volume.restrict (Br ×ˢ Tr) =
      (volume.restrict Br).prod (volume.restrict Tr) := by
    rw [Measure.prod_restrict Br Tr,
      MeasureTheory.Measure.volume_eq_prod Vec3 ℝ]
  rw [← hmeasure]
  exact hP'

private lemma pressureP7_bound_hprod_3 :
    ∀ {q : ℝ} {f : ParabolicPoint → Vec3} {z : ParabolicPoint} {ρ r : ℝ} (hρ : (0 : ℝ) < ρ),
      let Bρ : Set Vec3 := vec3Ball z.1 ρ;
      let Br : Set Vec3 := vec3Ball z.1 r;
      let Tρ : Set ℝ := Ioc (z.2 - ρ ^ (2 : ℕ)) z.2;
      let Tr : Set ℝ := Ioc (z.2 - r ^ (2 : ℕ)) z.2;
      let C : ℝ≥0∞ := (3 : ℝ≥0∞) * (ENNReal.ofReal ((4 : ℝ) * Real.pi)⁻¹ * hlsRieszConstant);
      let V : ℝ≥0∞ :=
        HPow.hPow (α := ℝ≥0∞) ((volume : Set Vec3 → ℝ≥0∞) Bρ : ℝ≥0∞) ((2 / 5 : ℝ) - (1 : ℝ) / q);
      let W : ℝ≥0∞ := HPow.hPow (α := ℝ≥0∞) ((volume : Set Vec3 → ℝ≥0∞) Br : ℝ≥0∞) (3 / 5 : ℝ);
      (∀ᵐ (s : ℝ) ∂Measure.restrict volume Tρ,
          @eLpNorm' _ ℝ _ MeasureSpace.toMeasurableSpace
              (fun (x : Vec3) => pressureP7 (mollifiedBallCutoff z.1 hρ) f s x) (15 : ℝ) volume ≤
            C *
                @eLpNorm' _ Vec3 _ MeasureSpace.toMeasurableSpace (fun (x : Vec3) => f (x, s)) q
                  (Measure.restrict volume Bρ) *
              V) →
        Tr ⊆ Tρ →
          AEStronglyMeasurable (β := ℝ) (m₀ := Prod.instMeasurableSpace)
              (fun (w : Vec3 × ℝ) => pressureP7 (mollifiedBallCutoff z.1 hρ) f w.2 w.1)
              (Measure.prod (Measure.restrict volume Br) (Measure.restrict volume Tr)) →
            @eLpNorm' _ ℝ _ Prod.instMeasurableSpace
                (fun (w : Vec3 × ℝ) => pressureP7 (mollifiedBallCutoff z.1 hρ) f w.2 w.1)
                (3 / 2 : ℝ)
                (Measure.prod (Measure.restrict volume Br) (Measure.restrict volume Tr)) ≤
              (∫⁻ (s : ℝ) in Tr,
                  (C *
                          @eLpNorm' _ Vec3 _ MeasureSpace.toMeasurableSpace
                            (fun (x : Vec3) => f (x, s)) q (Measure.restrict volume Bρ) *
                        V *
                      W) ^
                    (3 / 2 : ℝ)) ^
                (2 / 3 : ℝ)
    := by
  intro q f z ρ r hρ Bρ Br Tρ Tr C V W hD hTr hPprod
  have hDTr := ae_restrict_of_ae_restrict_of_subset hTr hD
  have hmeasure : volume.restrict (Br ×ˢ Tr) =
      (volume.restrict Br).prod (volume.restrict Tr) := by
    rw [Measure.prod_restrict Br Tr,
      MeasureTheory.Measure.volume_eq_prod Vec3 ℝ]
  have hPprod' := hPprod
  rw [← hmeasure] at hPprod'
  have hbound := eLpNorm'_prod_three_halves (P := fun w : Vec3 × ℝ =>
    pressureP7 (mollifiedBallCutoff z.1 hρ) f w.2 w.1)
    (B := Br) (T := Tr) hPprod' hDTr
  rw [hmeasure] at hbound
  simpa [W] using hbound

private lemma pressureP7_bound_hInt_4 :
    ∀ {q : ℝ} {f : ParabolicPoint → Vec3} {z : ParabolicPoint} {ρ r : ℝ},
      let Bρ : Set Vec3 := vec3Ball z.1 ρ;
      let Br : Set Vec3 := vec3Ball z.1 r;
      let Tρ : Set ℝ := Ioc (z.2 - ρ ^ (2 : ℕ)) z.2;
      let Tr : Set ℝ := Ioc (z.2 - r ^ (2 : ℕ)) z.2;
      let H : ℝ → ℝ≥0∞ := fun (s : ℝ) => ∫⁻ (x : Vec3) in Bρ, ‖f (x, s)‖ₑ ^ q;
      let G : ℝ → ℝ := fun (s : ℝ) => (H s).toReal ^ ((1 : ℝ) / q);
      let C : ℝ≥0∞ := (3 : ℝ≥0∞) * (ENNReal.ofReal ((4 : ℝ) * Real.pi)⁻¹ * hlsRieszConstant);
      let V : ℝ≥0∞ :=
        HPow.hPow (α := ℝ≥0∞) ((volume : Set Vec3 → ℝ≥0∞) Bρ : ℝ≥0∞) ((2 / 5 : ℝ) - (1 : ℝ) / q);
      let W : ℝ≥0∞ := HPow.hPow (α := ℝ≥0∞) ((volume : Set Vec3 → ℝ≥0∞) Br : ℝ≥0∞) (3 / 5 : ℝ);
      AEStronglyMeasurable (m₀ := MeasureSpace.toMeasurableSpace) G (Measure.restrict volume Tρ) →
        (∫⁻ (s : ℝ) in Ioc (z.2 - r ^ (2 : ℕ)) z.2, ENNReal.ofReal (G s) ^ (3 / 2 : ℝ)) ^
              (2 / 3 : ℝ) ≤
            ENNReal.ofReal r ^ ((2 : ℝ) * ((2 / 3 : ℝ) - (1 : ℝ) / q)) *
              @eLpNorm' _ _ _ MeasureSpace.toMeasurableSpace G q
                (Measure.restrict volume (Ioc (z.2 - ρ ^ (2 : ℕ)) z.2)) →
          Tr ⊆ Tρ →
            let D : ℝ → ℝ≥0∞ := fun (s : ℝ) =>
              C *
                  @eLpNorm' _ Vec3 _ MeasureSpace.toMeasurableSpace (fun (x : Vec3) => f (x, s)) q
                    (Measure.restrict volume Bρ) *
                V;
            (∀ᵐ (s : ℝ) ∂Measure.restrict volume Tr, D s * W ≤ C * V * W * ENNReal.ofReal (G s)) →
              (∫⁻ (s : ℝ) in Tr, (D s * W) ^ (3 / 2 : ℝ)) ^ (2 / 3 : ℝ) ≤
                C * V * W *
                  (ENNReal.ofReal r ^ ((2 : ℝ) * ((2 / 3 : ℝ) - (1 : ℝ) / q)) *
                    @eLpNorm' _ _ _ MeasureSpace.toMeasurableSpace G q (Measure.restrict volume Tρ))
    := by
  intro q f z ρ r Bρ Br Tρ Tr H G C V W hGmeas htime_holder hTr D hDpoint
  have hmonpow : ∀ᵐ s ∂volume.restrict Tr,
      (D s * W) ^ (3 / 2 : ℝ) ≤
        ((C * V * W) * ENNReal.ofReal (G s)) ^ (3 / 2 : ℝ) := by
    filter_upwards [hDpoint] with s hs
    exact ENNReal.rpow_le_rpow hs (by norm_num)
  have hmonint := lintegral_mono_ae
    (μ := volume.restrict Tr) hmonpow
  calc
    _ ≤ (∫⁻ s in Tr,
        ((C * V * W) * ENNReal.ofReal (G s)) ^ (3 / 2 : ℝ)) ^
          (2 / 3 : ℝ) :=
      ENNReal.rpow_le_rpow hmonint (by norm_num)
    _ = (C * V * W) *
        (∫⁻ s in Tr, ENNReal.ofReal (G s) ^ (3 / 2 : ℝ)) ^
          (2 / 3 : ℝ) := by
      have hfactor : (∫⁻ s in Tr,
          (C * V * W * ENNReal.ofReal (G s)) ^ (3 / 2 : ℝ)) =
          (C * V * W) ^ (3 / 2 : ℝ) *
            (∫⁻ s in Tr, ENNReal.ofReal (G s) ^ (3 / 2 : ℝ)) := by
        simp_rw [ENNReal.mul_rpow_of_nonneg (C * V * W) _
          (by norm_num : (0 : ℝ) ≤ 3 / 2)]
        have hGTr := hGmeas.mono_measure
          (Measure.restrict_mono_set volume hTr)
        have hGpow : AEMeasurable
            (fun s => ENNReal.ofReal (G s) ^ (3 / 2 : ℝ))
            (volume.restrict Tr) :=
          (hGTr.aemeasurable.ennreal_ofReal).pow_const (3 / 2 : ℝ)
        rw [MeasureTheory.lintegral_const_mul'' _ hGpow]
      rw [hfactor]
      rw [ENNReal.mul_rpow_of_nonneg _ _
        (by norm_num : (0 : ℝ) ≤ 2 / 3)]
      rw [← ENNReal.rpow_mul]
      norm_num
    _ ≤ _ := by
      gcongr

private lemma pressureP7_bound_hraw_5 :
    ∀ {q : ℝ} {f : ParabolicPoint → Vec3} {z : ParabolicPoint} {ρ r : ℝ} (hρ : (0 : ℝ) < ρ),
      (0 : ℝ) < r →
        let Bρ : Set Vec3 := vec3Ball z.1 ρ;
        let Br : Set Vec3 := vec3Ball z.1 r;
        let Tρ : Set ℝ := Ioc (z.2 - ρ ^ (2 : ℕ)) z.2;
        let Tr : Set ℝ := Ioc (z.2 - r ^ (2 : ℕ)) z.2;
        let H : ℝ → ℝ≥0∞ := fun (s : ℝ) => ∫⁻ (x : Vec3) in Bρ, ‖f (x, s)‖ₑ ^ q;
        let G : ℝ → ℝ := fun (s : ℝ) => (H s).toReal ^ ((1 : ℝ) / q);
        let C : ℝ≥0∞ := (3 : ℝ≥0∞) * (ENNReal.ofReal ((4 : ℝ) * Real.pi)⁻¹ * hlsRieszConstant);
        let V : ℝ≥0∞ :=
          HPow.hPow (α := ℝ≥0∞) ((volume : Set Vec3 → ℝ≥0∞) Bρ : ℝ≥0∞) ((2 / 5 : ℝ) - (1 : ℝ) / q);
        let W : ℝ≥0∞ := HPow.hPow (α := ℝ≥0∞) ((volume : Set Vec3 → ℝ≥0∞) Br : ℝ≥0∞) (3 / 5 : ℝ);
        @eLpNorm' _ _ _ MeasureSpace.toMeasurableSpace G q (Measure.restrict volume Tρ) ≤
            ENNReal.ofReal (ρ ^ ((5 : ℝ) / q - (3 : ℝ)) * lambda q f z ρ) →
          let D : ℝ → ℝ≥0∞ := fun (s : ℝ) =>
            C *
                @eLpNorm' _ Vec3 _ MeasureSpace.toMeasurableSpace (fun (x : Vec3) => f (x, s)) q
                  (Measure.restrict volume Bρ) *
              V;
          (∫⁻ (s : ℝ) in Tr, (D s * W) ^ (3 / 2 : ℝ)) ^ (2 / 3 : ℝ) ≤
              C * V * W *
                (ENNReal.ofReal r ^ ((2 : ℝ) * ((2 / 3 : ℝ) - (1 : ℝ) / q)) *
                  @eLpNorm' _ _ _ MeasureSpace.toMeasurableSpace G q (Measure.restrict volume Tρ)) →
            @eLpNorm' _ ℝ _ Prod.instMeasurableSpace
                  (fun (w : Vec3 × ℝ) => pressureP7 (mollifiedBallCutoff z.1 hρ) f w.2 w.1)
                  (3 / 2 : ℝ) (Measure.restrict volume (Br ×ˢ Tr)) ≤
                (∫⁻ (s : ℝ) in Tr,
                    (C *
                            @eLpNorm' _ Vec3 _ MeasureSpace.toMeasurableSpace
                              (fun (x : Vec3) => f (x, s)) q (Measure.restrict volume Bρ) *
                          V *
                        W) ^
                      (3 / 2 : ℝ)) ^
                  (2 / 3 : ℝ) →
              ENNReal.ofReal (r ^ (-4 / 3 : ℝ)) *
                  @eLpNorm' _ ℝ _ MeasureSpace.toMeasurableSpace
                    (fun (w : ParabolicPoint) => pressureP7 (mollifiedBallCutoff z.1 hρ) f w.2 w.1)
                    (3 / 2 : ℝ) (Measure.restrict volume (parabolicCylinder z.1 z.2 r)) ≤
                ENNReal.ofReal (r ^ (-4 / 3 : ℝ)) *
                  (C * V * W *
                    (ENNReal.ofReal r ^ ((2 : ℝ) * ((2 / 3 : ℝ) - (1 : ℝ) / q)) *
                      ENNReal.ofReal (ρ ^ ((5 : ℝ) / q - (3 : ℝ)) * lambda q f z ρ)))
    := by
  intro q f z ρ r hρ hr Bρ Br Tρ Tr H G C V W hGbound D hInt hprodQ
  calc
    _ ≤ ENNReal.ofReal (r ^ (-4 / 3 : ℝ)) *
        (∫⁻ s in Tr,
          (D s * W) ^ (3 / 2 : ℝ)) ^ (2 / 3 : ℝ) := by
      exact mul_le_mul_of_nonneg_left hprodQ (by positivity)
    _ ≤ ENNReal.ofReal (r ^ (-4 / 3 : ℝ)) *
        ((C * V * W) *
          ((ENNReal.ofReal r) ^ (2 * (2 / 3 - 1 / q : ℝ)) *
            eLpNorm' G q (volume.restrict Tρ))) := by
      gcongr
    _ ≤ _ := by
      gcongr

private lemma pressureP7_bound_hscale_eq_6 :
    ∀ {q : ℝ} {_ : ParabolicPoint → ℝ} {f : ParabolicPoint → Vec3} {z : ParabolicPoint} {ρ r : ℝ}
      (hρ : (0 : ℝ) < ρ),
      (0 : ℝ) < r →
        let Bρ : Set Vec3 := vec3Ball z.1 ρ;
        let Br : Set Vec3 := vec3Ball z.1 r;
        let C : ℝ≥0∞ := (3 : ℝ≥0∞) * (ENNReal.ofReal ((4 : ℝ) * Real.pi)⁻¹ * hlsRieszConstant);
        let V : ℝ≥0∞ :=
          HPow.hPow (α := ℝ≥0∞) ((volume : Set Vec3 → ℝ≥0∞) Bρ : ℝ≥0∞) ((2 / 5 : ℝ) - (1 : ℝ) / q);
        let W : ℝ≥0∞ := HPow.hPow (α := ℝ≥0∞) ((volume : Set Vec3 → ℝ≥0∞) Br : ℝ≥0∞) (3 / 5 : ℝ);
        (5 / 2 : ℝ) < q →
          (0 : ℝ) < q →
            (∀ᵐ (s : ℝ) ∂Measure.restrict volume (Ioc (z.2 - ρ ^ (2 : ℕ)) z.2),
                AEStronglyMeasurable (β := Vec3) (m₀ := MeasureSpace.toMeasurableSpace)
                    (fun (x : Vec3) => f (x, s)) (Measure.restrict volume (vec3Ball z.1 ρ)) ∧
                  ∫⁻ (x : Vec3) in vec3Ball z.1 ρ, ‖f (x, s)‖ₑ ^ q < ∞ ∧
                    ∀ (j : Fin (3 : ℕ)),
                      AEStronglyMeasurable (β := ℝ) (m₀ := MeasureSpace.toMeasurableSpace)
                          (fun (y : Vec3) => mollifiedBallCutoff z.1 hρ y * f (y, s) j) volume ∧
                        AEStronglyMeasurable (β := ℝ) (m₀ := MeasureSpace.toMeasurableSpace)
                            (fun (x : Vec3) =>
                              pressureNewtonianDerivativePotential j
                                (fun (y : Vec3) => mollifiedBallCutoff z.1 hρ y * f (y, s) j) x)
                            volume ∧
                          ∫⁻ (y : Vec3),
                              ENNReal.ofReal |mollifiedBallCutoff z.1 hρ y * f (y, s) j| ^
                                (5 / 2 : ℝ) <
                            ∞) →
              ENNReal.ofReal (r ^ (-4 / 3 : ℝ)) *
                  (C * V * W *
                    (ENNReal.ofReal r ^ ((2 : ℝ) * ((2 / 3 : ℝ) - (1 : ℝ) / q)) *
                      ENNReal.ofReal (ρ ^ ((5 : ℝ) / q - (3 : ℝ)) * lambda q f z ρ))) =
                pressureP7SolutionConstant q *
                  ENNReal.ofReal ((r / ρ) ^ ((9 / 5 : ℝ) - (2 : ℝ) / q) * lambda q f z ρ)
    := by
  intro q p f z ρ r hρ hr Bρ Br C V W hq hqpos hsource
  have hV := pressure_volume_ball (x₀ := z.1) hρ
  have hW := pressure_volume_ball (x₀ := z.1) hr
  have hqV : 0 ≤ 2 / 5 - 1 / q := by
    have hq' : 1 / q ≤ (2 / 5 : ℝ) := by
      apply (div_le_iff₀ hqpos).2
      nlinarith only [hq]
    linarith only [hq']
  dsimp [V, W, C, pressureP7SolutionConstant]
  rw [hV, hW]
  rw [ENNReal.ofReal_mul (by positivity : 0 ≤ 4 * Real.pi / 3)]
  rw [ENNReal.ofReal_mul (by positivity : 0 ≤ 4 * Real.pi / 3)]
  rw [ENNReal.mul_rpow_of_nonneg _ _ hqV]
  rw [ENNReal.mul_rpow_of_nonneg _ _ (by norm_num :
    (0 : ℝ) ≤ 3 / 5)]
  rw [show (ρ ^ (3 : ℕ) : ℝ) = ρ ^ (3 : ℝ) by norm_num]
  rw [show (r ^ (3 : ℕ) : ℝ) = r ^ (3 : ℝ) by norm_num]
  rw [← ENNReal.ofReal_rpow_of_pos (p := (3 : ℝ)) hρ]
  rw [← ENNReal.ofReal_rpow_of_pos (p := (3 : ℝ)) hr]
  rw [← ENNReal.rpow_mul, ← ENNReal.rpow_mul]
  have hsource : ENNReal.ofReal (ρ ^ (5 / q - 3) * lambda q f z ρ) =
      ENNReal.ofReal ρ ^ (5 / q - 3) *
        ENNReal.ofReal (lambda q f z ρ) := by
    rw [ENNReal.ofReal_mul (Real.rpow_nonneg hρ.le _)]
    rw [← ENNReal.ofReal_rpow_of_pos hρ]
  rw [hsource]
  rw [← ENNReal.ofReal_rpow_of_pos (p := (-4 / 3 : ℝ)) hr]
  have htarget : ENNReal.ofReal ((r / ρ) ^ (9 / 5 - 2 / q : ℝ) *
      lambda q f z ρ) =
      ENNReal.ofReal (r / ρ) ^ (9 / 5 - 2 / q : ℝ) *
        ENNReal.ofReal (lambda q f z ρ) := by
    rw [ENNReal.ofReal_mul (Real.rpow_nonneg (by positivity) _)]
    rw [← ENNReal.ofReal_rpow_of_pos (div_pos hr hρ)]
  rw [htarget]
  have hc0 : ENNReal.ofReal (4 * Real.pi / 3) ≠ 0 :=
    ne_of_gt (ENNReal.ofReal_pos.mpr (by positivity))
  have hctop : ENNReal.ofReal (4 * Real.pi / 3) ≠ ⊤ :=
    ENNReal.ofReal_ne_top
  have hr0 : ENNReal.ofReal r ≠ 0 :=
    ne_of_gt (ENNReal.ofReal_pos.mpr hr)
  have hrtop : ENNReal.ofReal r ≠ ⊤ := ENNReal.ofReal_ne_top
  have hρ0 : ENNReal.ofReal ρ ≠ 0 :=
    ne_of_gt (ENNReal.ofReal_pos.mpr hρ)
  have hρtop : ENNReal.ofReal ρ ≠ ⊤ := ENNReal.ofReal_ne_top
  have hc : ENNReal.ofReal (4 * Real.pi / 3) ^ (2 / 5 - 1 / q : ℝ) *
      ENNReal.ofReal (4 * Real.pi / 3) ^ (3 / 5 : ℝ) =
      ENNReal.ofReal (4 * Real.pi / 3) ^ (1 - 1 / q : ℝ) := by
    rw [← ENNReal.rpow_add]
    all_goals first | exact hc0 | exact hctop | (congr 1; ring)
  have hrpow : ENNReal.ofReal r ^ (-4 / 3 : ℝ) *
      ENNReal.ofReal r ^ (3 * (3 / 5 : ℝ)) *
      ENNReal.ofReal r ^ (2 * (2 / 3 - 1 / q : ℝ)) =
      ENNReal.ofReal r ^ (9 / 5 - 2 / q : ℝ) := by
    rw [← ENNReal.rpow_add, ← ENNReal.rpow_add]
    all_goals first | exact hr0 | exact hrtop | (congr 1; ring)
  have hrhopow : ENNReal.ofReal ρ ^ (3 * (2 / 5 - 1 / q : ℝ)) *
      ENNReal.ofReal ρ ^ (5 / q - 3 : ℝ) =
      ENNReal.ofReal ρ ^ (-(9 / 5 - 2 / q : ℝ)) := by
    rw [← ENNReal.rpow_add]
    all_goals first | exact hρ0 | exact hρtop | (congr 1; ring)
  calc
    _ = 3 * (ENNReal.ofReal (4 * Real.pi)⁻¹ * hlsRieszConstant) *
        (ENNReal.ofReal (4 * Real.pi / 3) ^ (2 / 5 - 1 / q : ℝ) *
          ENNReal.ofReal (4 * Real.pi / 3) ^ (3 / 5 : ℝ)) *
        (ENNReal.ofReal r ^ (-4 / 3 : ℝ) *
          ENNReal.ofReal r ^ (3 * (3 / 5 : ℝ)) *
          ENNReal.ofReal r ^ (2 * (2 / 3 - 1 / q : ℝ))) *
        (ENNReal.ofReal ρ ^ (3 * (2 / 5 - 1 / q : ℝ)) *
          ENNReal.ofReal ρ ^ (5 / q - 3 : ℝ)) *
        ENNReal.ofReal (lambda q f z ρ) := by ring
    _ = 3 * (ENNReal.ofReal (4 * Real.pi)⁻¹ * hlsRieszConstant) *
        ENNReal.ofReal (4 * Real.pi / 3) ^ (1 - 1 / q : ℝ) *
        (ENNReal.ofReal r ^ (9 / 5 - 2 / q : ℝ) *
          ENNReal.ofReal ρ ^ (-(9 / 5 - 2 / q : ℝ))) *
        ENNReal.ofReal (lambda q f z ρ) := by
      rw [hc, hrpow, hrhopow]
      ring
    _ = _ := by
      have hratio : ENNReal.ofReal (r / ρ) ^ (9 / 5 - 2 / q : ℝ) =
          ENNReal.ofReal r ^ (9 / 5 - 2 / q : ℝ) *
            ENNReal.ofReal ρ ^ (-(9 / 5 - 2 / q : ℝ)) := by
        rw [ENNReal.ofReal_rpow_of_pos (div_pos hr hρ)]
        rw [pressure_rpow_div hr hρ]
        rw [ENNReal.ofReal_mul (Real.rpow_nonneg hr.le _)]
        rw [← ENNReal.ofReal_rpow_of_pos
          (p := (9 / 5 - 2 / q : ℝ)) hr]
        rw [← ENNReal.ofReal_rpow_of_pos
          (p := (-(9 / 5 - 2 / q : ℝ))) hρ]
      rw [hratio]
      ring

theorem pressureP7_bound
    {Ω : Set Vec3} {I : Set ℝ} {q : ℝ}
    {u : ParabolicPoint → Vec3} {Du : ParabolicPoint → Fin 3 → Vec3}
    {p : ParabolicPoint → ℝ} {f : ParabolicPoint → Vec3}
    (hsol : IsSuitableWeakSolutionIntegrable Ω I q u Du p f)
    {z : ParabolicPoint} {ρ r : ℝ} (hρ : 0 < ρ) (hr : 0 < r)
    (hhalf : r ≤ ρ / 2)
    (hsub : closure (parabolicCylinder z.1 z.2 ρ) ⊆ spaceTimeSet Ω I) :
    ENNReal.ofReal (r ^ (-4 / 3 : ℝ)) *
        eLpNorm' (fun w : ParabolicPoint =>
          pressureP7 (mollifiedBallCutoff z.1 hρ) f w.2 w.1) (3 / 2 : ℝ)
          (volume.restrict (parabolicCylinder z.1 z.2 r)) ≤
      pressureP7SolutionConstant q *
        ENNReal.ofReal ((r / ρ) * lambda q f z ρ) := by
  let Bρ : Set Vec3 := vec3Ball z.1 ρ
  let Br : Set Vec3 := vec3Ball z.1 r
  let Tρ : Set ℝ := Ioc (z.2 - ρ ^ 2) z.2
  let Tr : Set ℝ := Ioc (z.2 - r ^ 2) z.2
  let H : ℝ → ℝ≥0∞ := fun s =>
    ∫⁻ x in Bρ, ‖f (x, s)‖ₑ ^ q
  let G : ℝ → ℝ := fun s => (H s).toReal ^ (1 / q : ℝ)
  let C : ℝ≥0∞ := 3 * (ENNReal.ofReal ((4 * Real.pi)⁻¹) * hlsRieszConstant)
  let V : ℝ≥0∞ := volume Bρ ^ (2 / 5 - 1 / q : ℝ)
  let W : ℝ≥0∞ := volume Br ^ (3 / 5 : ℝ)
  obtain ⟨Ω', J, hbox, hball, htime⟩ :=
    pressure_box_geometry hsol hρ hsub
  have hBΩ : Bρ ⊆ Ω := by
    intro x hx
    exact hbox.2.2.1 (subset_closure (hball hx))
  have hηc : HasCompactSupport (mollifiedBallCutoff z.1 hρ) :=
    mollifiedBallCutoff_hasCompactSupport z.1 hρ
  have hηΩ : tsupport (mollifiedBallCutoff z.1 hρ) ⊆ Ω :=
    (pressure_cutoff_support_subset_ball z.1 hρ).trans hBΩ
  have hηbound : ∀ x, |mollifiedBallCutoff z.1 hρ x| ≤ 1 := by
    intro x
    apply abs_le.mpr
    constructor
    · linarith only [mollifiedBallCutoff_nonneg z.1 hρ x]
    · exact mollifiedBallCutoff_le_one z.1 hρ x
  have hηmeas : AEStronglyMeasurable (mollifiedBallCutoff z.1 hρ) volume :=
    (mollifiedBallCutoff_smooth z.1 hρ).continuous.aestronglyMeasurable
  have hηsupport : tsupport (mollifiedBallCutoff z.1 hρ) ⊆ Bρ := by
    exact pressure_cutoff_support_subset_ball z.1 hρ
  have hq : 5 / 2 < q := hsol.2.2.2.1
  have hqpos : 0 < q := lt_trans (by norm_num) hq
  obtain ⟨hHmeas, hHglobal⟩ := sws_force_time_data hsol hρ hsub
  have hHmeas' : AEMeasurable H (volume.restrict Tρ) := by
    simpa [H, Bρ, Tρ] using hHmeas
  have hHglobal' : (∫⁻ s in Tρ, H s) ≤
      ENNReal.ofReal ((ρ ^ (5 / q - 3) * lambda q f z ρ) ^ q) := by
    have hz : (z.1, z.2) = z := by cases z; rfl
    simpa [H, Bρ, Tρ, hz] using hHglobal
  have hHtop : (∫⁻ s in Tρ, H s) < ⊤ :=
    lt_of_le_of_lt hHglobal' ENNReal.ofReal_lt_top
  have hHs : ∀ᵐ s ∂volume.restrict Tρ, H s < ⊤ :=
    ae_lt_top' hHmeas' (ne_of_lt hHtop)
  have hGmeas : AEStronglyMeasurable G (volume.restrict Tρ) := by
    have hreal := hHmeas'.ennreal_toReal
    have hc : Continuous (fun x : ℝ => x ^ (1 / q : ℝ)) :=
      Real.continuous_rpow_const (by positivity)
    simpa [Function.comp_def, G] using
      (hc.measurable.comp_aemeasurable hreal).aestronglyMeasurable
  have hGnonneg : 0 ≤ᵐ[volume.restrict Tρ] G :=
    Eventually.of_forall (fun s => Real.rpow_nonneg ENNReal.toReal_nonneg _)
  have hforce : 0 ≤ ρ ^ (5 / q - 3) * lambda q f z ρ := by
    exact mul_nonneg (Real.rpow_nonneg hρ.le _) (by unfold lambda; positivity)
  have hGbound : eLpNorm' G q (volume.restrict Tρ) ≤
      ENNReal.ofReal (ρ ^ (5 / q - 3) * lambda q f z ρ) := by
    exact force_time_norm_bound hqpos hforce hHs hHglobal'
  have htime_holder := time_holder_q (t₀ := z.2) (r := r) (ρ := ρ) (q := q)
    hr hhalf (by linarith only [hq]) (g := G) hGmeas hGnonneg
  have hsource := sws_p7_slice_data hsol hρ hsub hηc hηΩ hηbound hηsupport hηmeas
  have hD : ∀ᵐ s ∂volume.restrict Tρ,
      eLpNorm' (fun x : Vec3 =>
        pressureP7 (mollifiedBallCutoff z.1 hρ) f s x) (15 : ℝ) volume ≤
        C * eLpNorm' (fun x : Vec3 => f (x, s)) q
            (volume.restrict Bρ) * V := by
    filter_upwards [hsource, hHs] with s hs htop
    have hsP := pressureP7_eLpNorm15_le_slice_holder hq hηbound hηsupport
      hs.1 hs.2.1 (fun j => (hs.2.2 j).1)
      (fun j => (hs.2.2 j).2.1) (fun j => (hs.2.2 j).2.2)
    simpa [C, V, Bρ] using hsP
  have hnorm : ∀ᵐ s ∂volume.restrict Tρ,
      eLpNorm' (fun x : Vec3 => f (x, s)) q (volume.restrict Bρ) ≤
        ENNReal.ofReal (G s) := by
    filter_upwards [hHs] with s hs
    rw [eLpNorm'_eq_lintegral_enorm]
    have hpow : (∫⁻ x in Bρ, ‖f (x, s)‖ₑ ^ q) ^ (1 / q : ℝ) =
        ENNReal.ofReal (G s) := by
      rw [show (∫⁻ x in Bρ, ‖f (x, s)‖ₑ ^ q) = H s by rfl]
      rw [ennreal_rpow_eq_ofReal_toReal_rpow hs.ne hqpos]
    exact hpow.le
  have hQr := @pressureP7_bound_hQr_1 z ρ r hρ hr hhalf
  have hTr : Tr ⊆ Tρ := by
    intro s hs
    have hρ0 : 0 ≤ ρ := by linarith only [hhalf, hr]
    have hsq : r ^ 2 ≤ ρ ^ 2 := by
      exact (sq_le_sq₀ hr.le hρ0).2 (by linarith only [hhalf, hρ0])
    exact ⟨by linarith only [hs.1, hsq], hs.2⟩
  have hPprod := @pressureP7_bound_hPprod_2 Ω I q u Du p f hsol z ρ r hρ hsub hQr
  let D : ℝ → ℝ≥0∞ := fun s =>
    C * eLpNorm' (fun x : Vec3 => f (x, s)) q (volume.restrict Bρ) * V
  have hprod := @pressureP7_bound_hprod_3 q f z ρ r hρ hD hTr hPprod
  have hnormTr := ae_restrict_of_ae_restrict_of_subset hTr hnorm
  have hDpoint : ∀ᵐ s ∂volume.restrict Tr,
      D s * W ≤ (C * V * W) * ENNReal.ofReal (G s) := by
    filter_upwards [hnormTr] with s hs
    dsimp [D]
    calc
      (C * eLpNorm' (fun x : Vec3 => f (x, s)) q
          (volume.restrict Bρ) * V) * W ≤
          (C * ENNReal.ofReal (G s) * V) * W := by
            gcongr
      _ = (C * V * W) * ENNReal.ofReal (G s) := by ring
  have hInt := @pressureP7_bound_hInt_4 q f z ρ r hGmeas htime_holder hTr hDpoint
  have hmeasureR : (volume : Measure (Vec3 × ℝ)).restrict (Br ×ˢ Tr) =
      (volume.restrict Br).prod (volume.restrict Tr) := by
    rw [Measure.prod_restrict Br Tr,
      MeasureTheory.Measure.volume_eq_prod Vec3 ℝ]
  have hprodQ := hprod
  rw [← hmeasureR] at hprodQ
  have hraw := @pressureP7_bound_hraw_5 q f z ρ r hρ hr hGbound hInt hprodQ
  have hscale_eq := @pressureP7_bound_hscale_eq_6 q p f z ρ r hρ hr hq hqpos hsource
  have hκ : 0 < r / ρ := div_pos hr hρ
  have hκle : r / ρ ≤ 1 := by
    apply (div_le_iff₀ hρ).2
    linarith only [hhalf, hρ]
  have hγ : 1 ≤ 9 / 5 - 2 / q := by
    have hq' : 2 / q ≤ (4 / 5 : ℝ) := by
      apply (div_le_iff₀ hqpos).2
      nlinarith only [hq]
    linarith only [hq']
  have hpowκ : (r / ρ) ^ (9 / 5 - 2 / q : ℝ) ≤ r / ρ := by
    simpa only [Real.rpow_one] using
      (Real.rpow_le_rpow_of_exponent_ge (x := r / ρ)
        (y := 9 / 5 - 2 / q) (z := 1) hκ hκle hγ)
  have hlam : 0 ≤ lambda q f z ρ := by
    unfold lambda
    positivity
  have hscaled :
      pressureP7SolutionConstant q *
          ENNReal.ofReal ((r / ρ) ^ (9 / 5 - 2 / q : ℝ) *
            lambda q f z ρ) ≤
        pressureP7SolutionConstant q *
          ENNReal.ofReal ((r / ρ) * lambda q f z ρ) := by
    gcongr
  exact hraw.trans (hscale_eq.le.trans hscaled)

end CKN
