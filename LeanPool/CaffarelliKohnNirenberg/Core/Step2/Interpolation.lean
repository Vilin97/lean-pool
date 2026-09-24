/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Setting.VectorInequalities
public import LeanPool.CaffarelliKohnNirenberg.Setting.Finiteness
public import LeanPool.CaffarelliKohnNirenberg.Setting.InterpolationCylinder
public import LeanPool.CaffarelliKohnNirenberg.Setting.SliceNormBounds
public import LeanPool.CaffarelliKohnNirenberg.Pressure.SliceIntegrability
public import LeanPool.CaffarelliKohnNirenberg.Foundation.Parabolic.Integration.Average
public import LeanPool.CaffarelliKohnNirenberg.Foundation.Parabolic.Integration.ProdSwap

/-!
# Interpolation

Part of the Caffarelli–Kohn–Nirenberg partial regularity proof.
-/

@[expose] public section

open MeasureTheory Set
open scoped ENNReal NNReal Topology
open CKN.Foundation.Parabolic
open CKN.Foundation.Parabolic.Integration
noncomputable section
namespace CKN
/-- Positive coefficient for the scale-normalized velocity interpolation estimate. -/
noncomputable def gagliardoConstant : ℝ := 1 + (81 * ENNReal.ofReal (Real.sqrt 3) *
  (Classical.choose interpolationBall_three_finite)).toReal
private theorem gamma_le_of_same_ball_interpolation
    {Ω : Set Vec3} {I : Set ℝ} {q : ℝ}
    {u : ParabolicPoint → Vec3} {Du : ParabolicPoint → Fin 3 → Vec3}
    {p : ParabolicPoint → ℝ} {f : ParabolicPoint → Vec3}
    (_ : IsSuitableWeakSolutionIntegrable Ω I q u Du p f)
    {z : ParabolicPoint} {r C : ℝ} (hr : 0 < r)
    (_ : closure (parabolicCylinder z.1 z.2 r) ⊆ spaceTimeSet Ω I)
    (hC : 0 ≤ C) (hα : 0 ≤ alpha u z r) (hβ : 0 ≤ beta u Du z r)
    (hinterpolation :
      (∫⁻ w in parabolicCylinder z.1 z.2 r,
        ENNReal.ofReal (vec3EuclideanNorm (u w)) ^ (3 : ℝ)) ≤
        ENNReal.ofReal (r ^ (2 : ℝ) *
          (C * alpha u z r ^ (1 / 2 : ℝ) * beta u Du z r ^ (1 / 2 : ℝ) +
            C * alpha u z r) ^ (3 : ℝ))) :
    gamma u z r ≤
      C * alpha u z r ^ (1 / 2 : ℝ) * beta u Du z r ^ (1 / 2 : ℝ) +
        C * alpha u z r := by
  have hfinite :
      (∫⁻ w in parabolicCylinder z.1 z.2 r,
        ENNReal.ofReal (vec3EuclideanNorm (u w)) ^ (3 : ℝ)) ≠ ⊤ :=
    ne_of_lt (lt_of_le_of_lt hinterpolation ENNReal.ofReal_lt_top)
  let A : ℝ := alpha u z r
  let B : ℝ := beta u Du z r
  let M : ℝ := C * A ^ (1 / 2 : ℝ) * B ^ (1 / 2 : ℝ) + C * A
  have hM : 0 ≤ M := by
    dsimp [M]
    positivity
  have hM_expanded : 0 ≤
      C * alpha u z r ^ (1 / 2 : ℝ) * beta u Du z r ^ (1 / 2 : ℝ) +
        C * alpha u z r := by
    simpa [M, A, B] using hM
  have hto :
      (∫⁻ w in parabolicCylinder z.1 z.2 r,
        ENNReal.ofReal (vec3EuclideanNorm (u w)) ^ (3 : ℝ)).toReal ≤
        r ^ (2 : ℝ) * M ^ (3 : ℝ) := by
    have hto' :=
      (ENNReal.toReal_le_toReal hfinite ENNReal.ofReal_ne_top).mpr hinterpolation
    calc
      _ ≤ (ENNReal.ofReal (r ^ (2 : ℝ) *
          (C * alpha u z r ^ (1 / 2 : ℝ) * beta u Du z r ^ (1 / 2 : ℝ) +
            C * alpha u z r) ^ (3 : ℝ))).toReal := hto'
      _ = r ^ (2 : ℝ) * M ^ (3 : ℝ) := by
        have hnonneg : 0 ≤ r ^ (2 : ℝ) *
            (C * alpha u z r ^ (1 / 2 : ℝ) * beta u Du z r ^
                (1 / 2 : ℝ) + C * alpha u z r) ^ (3 : ℝ) := by
          exact mul_nonneg (Real.rpow_nonneg hr.le _)
            (Real.rpow_nonneg hM_expanded _)
        rw [ENNReal.toReal_ofReal hnonneg]
  have hscaled :
      r ^ (-2 : ℝ) *
          (∫⁻ w in parabolicCylinder z.1 z.2 r,
            ENNReal.ofReal (vec3EuclideanNorm (u w)) ^ (3 : ℝ)).toReal ≤
        M ^ (3 : ℝ) := by
    calc
      _ ≤ r ^ (-2 : ℝ) * (r ^ (2 : ℝ) * M ^ (3 : ℝ)) :=
        mul_le_mul_of_nonneg_left hto (Real.rpow_nonneg hr.le _)
      _ = M ^ (3 : ℝ) := by
        rw [← mul_assoc, ← Real.rpow_add hr]
        norm_num
  change (r ^ (-2 : ℝ) *
      (∫⁻ w in parabolicCylinder z.1 z.2 r,
        ENNReal.ofReal (vec3EuclideanNorm (u w)) ^ (3 : ℝ)).toReal) ^
      (1 / 3 : ℝ) ≤ _
  have hscaled_nonneg : 0 ≤ r ^ (-2 : ℝ) *
      (∫⁻ w in parabolicCylinder z.1 z.2 r,
        ENNReal.ofReal (vec3EuclideanNorm (u w)) ^ (3 : ℝ)).toReal := by
    exact mul_nonneg (Real.rpow_nonneg hr.le _)
      ENNReal.toReal_nonneg
  calc
    _ ≤ (M ^ (3 : ℝ)) ^ (1 / 3 : ℝ) :=
      Real.rpow_le_rpow hscaled_nonneg hscaled (by norm_num)
    _ = M := by
      rw [← Real.rpow_mul hM]
      norm_num
    _ = C * alpha u z r ^ (1 / 2 : ℝ) * beta u Du z r ^ (1 / 2 : ℝ) +
        C * alpha u z r := by rfl
private lemma component_norm_le_vec3_step2 (v : Vec3) (i : Fin 3) :
    ‖v i‖ ≤ vec3EuclideanNorm v := by
  change |v i| ≤ vec3EuclideanNorm v
  unfold vec3EuclideanNorm
  exact Real.abs_le_sqrt (Finset.single_le_sum
    (fun j _ => sq_nonneg (v j)) (Finset.mem_univ i))
private lemma component_norm_sq_le_spatialGradientSq_step2
    {u : ParabolicPoint → Vec3} {Du : ParabolicPoint → Fin 3 → Vec3}
    (w : ParabolicPoint) (i : Fin 3) :
    ‖Du w i‖ₑ ^ (2 : ℝ) ≤ ENNReal.ofReal (spatialGradientSq u Du w) := by
  have hsq_nonneg : 0 ≤ spatialGradientSq u Du w := by
    unfold spatialGradientSq
    positivity
  have hsqrt_nonneg : 0 ≤ Real.sqrt (spatialGradientSq u Du w) :=
    Real.sqrt_nonneg _
  have hnorm : ‖Du w i‖ ^ 2 ≤ spatialGradientSq u Du w := by
    rw [Pi.norm_def]
    change (↑(Finset.univ.sup (fun j : Fin 3 => ‖Du w i j‖₊) : ℝ≥0) : ℝ) ^ 2 ≤ _
    have hsup : (Finset.univ.sup (fun j : Fin 3 => ‖Du w i j‖₊) : ℝ≥0) ≤
        ⟨Real.sqrt (spatialGradientSq u Du w), hsqrt_nonneg⟩ := by
      apply Finset.sup_le
      intro j hj
      change ‖Du w i j‖₊ ≤ ⟨Real.sqrt (spatialGradientSq u Du w), hsqrt_nonneg⟩
      exact_mod_cast (show ‖Du w i j‖ ≤ Real.sqrt (spatialGradientSq u Du w) by
      apply (Real.le_sqrt (norm_nonneg _) hsq_nonneg).2
      unfold spatialGradientSq
      have hterm : (Du w i j) ^ 2 ≤
          ∑ k : Fin 3, ∑ l : Fin 3, (Du w k l) ^ 2 := by
        calc
          _ ≤ ∑ l : Fin 3, (Du w i l) ^ 2 :=
            Finset.single_le_sum (fun l _ => sq_nonneg (Du w i l))
              (Finset.mem_univ j)
          _ ≤ _ := Finset.single_le_sum
            (fun k _ => Finset.sum_nonneg (fun l _ => sq_nonneg (Du w k l)))
            (Finset.mem_univ i)
      simpa [Real.norm_eq_abs, sq_abs] using hterm)
    have hsq : (Real.sqrt (spatialGradientSq u Du w)) ^ 2 =
        spatialGradientSq u Du w := by
      rw [Real.sq_sqrt]
      exact hsq_nonneg
    have hsupR : (↑(Finset.univ.sup (fun j : Fin 3 => ‖Du w i j‖₊) : ℝ≥0) : ℝ) ≤
        Real.sqrt (spatialGradientSq u Du w) := by exact_mod_cast hsup
    have hsup_nonneg :
        0 ≤ (↑(Finset.univ.sup (fun j : Fin 3 => ‖Du w i j‖₊) : ℝ≥0) : ℝ) := by
      positivity
    calc
      _ ≤ (Real.sqrt (spatialGradientSq u Du w)) ^ 2 :=
        pow_le_pow_left₀ hsup_nonneg hsupR 2
      _ = _ := hsq
  calc
    ‖Du w i‖ₑ ^ (2 : ℝ) = ENNReal.ofReal (‖Du w i‖ ^ 2) := by
      rw [show ‖Du w i‖ₑ = ENNReal.ofReal ‖Du w i‖ from (ofReal_norm _).symm,
        show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num,
        ENNReal.rpow_natCast, ← ENNReal.ofReal_pow (norm_nonneg (Du w i))]
    _ ≤ _ := ENNReal.ofReal_le_ofReal hnorm
private lemma gamma_le_gagliardo_hball_1 :
    ∀ {z : ParabolicPoint} {r : ℝ},
      (0 : ℝ) < r →
        let B : Set Vec3 := euclideanBall z.1 r;
        ∀ (Ω' : Set Vec3) (J : Set ℝ), parabolicCylinder z.1 z.2 r ⊆ spaceTimeSet Ω' J → B ⊆ Ω'
    := by
  intro z r hr B Ω' J hcyl y hy
  have hy' : vec3EuclideanNorm (y - z.1) < r := by
    change y ∈ euclideanBall z.1 r at hy
    simpa [vec3EuclideanNorm, vecEuclideanNorm, vecNormSq, vecDot, pow_two]
      using (mem_euclideanBall_iff_vecEuclideanNorm_lt hr).1 hy
  have hz : (y, z.2) ∈ parabolicCylinder z.1 z.2 r := by
    rw [parabolicCylinder]
    exact ⟨hy',
      ⟨by nlinarith only [sq_pos_of_pos hr], le_rfl⟩⟩
  exact (hcyl hz).1

private lemma gamma_le_gagliardo_hG₂_2 :
    ∀ {u : ParabolicPoint → Vec3} {Du : ParabolicPoint → Fin (3 : ℕ) → Vec3} {z : ParabolicPoint}
      {r : ℝ},
      let B : Set Vec3 := euclideanBall z.1 r;
      let T : Set ℝ := Ioc (z.2 - r ^ (2 : ℕ)) z.2;
      let G : ℝ → ℝ≥0∞ := fun (s : ℝ) =>
        (∫⁻ (y : Vec3) in B, ENNReal.ofReal (spatialGradientSq u Du (y, s))) ^ (1 / 2 : ℝ);
      let D : ℝ≥0∞ :=
        ∫⁻ (w : ParabolicPoint) in parabolicCylinder z.1 z.2 r,
          ENNReal.ofReal (spatialGradientSq u Du w);
      AEMeasurable (β := ℝ≥0∞) (_m := Prod.instMeasurableSpace)
          (fun (w : Vec3 × ℝ) => ENNReal.ofReal (spatialGradientSq u Du w))
          (Measure.prod (Measure.restrict volume B) (Measure.restrict volume T)) →
        B ×ˢ T = parabolicCylinder z.1 z.2 r →
          (∀ (s : ℝ),
              G s ^ (2 : ℝ) = ∫⁻ (y : Vec3) in B, ENNReal.ofReal (spatialGradientSq u Du (y, s))) →
            ∫⁻ (s : ℝ) in T, G s ^ (2 : ℝ) ≤ D
    := by
  intro u Du z r B T G D hDprodBT hrect hGsq
  calc
    _ = ∫⁻ s in T, ∫⁻ y in B,
        ENNReal.ofReal (spatialGradientSq u Du (y, s)) := by
      apply lintegral_congr
      intro s
      rw [hGsq]
    _ = ∫⁻ w in parabolicCylinder z.1 z.2 r,
        ENNReal.ofReal (spatialGradientSq u Du w) := by
      rw [← hrect]
      exact (prod_lintegral_swap_cyl hDprodBT).symm
    _ ≤ D := le_rfl

private lemma gamma_le_gagliardo_hgood_3 :
    ∀ {Ω : Set Vec3} {I : Set ℝ} {q : ℝ} {u : ParabolicPoint → Vec3}
      {Du : ParabolicPoint → Fin (3 : ℕ) → Vec3} {p : ParabolicPoint → ℝ}
      {f : ParabolicPoint → Vec3},
      IsSuitableWeakSolutionIntegrable Ω I q u Du p f →
        ∀ {z : ParabolicPoint} {r : ℝ},
          let T : Set ℝ := Ioc (z.2 - r ^ (2 : ℕ)) z.2;
          ∀ (Ω' : Set Vec3) (J : Set ℝ),
            localBox Ω I Ω' J →
              T ⊆ J →
                (AEStronglyMeasurable (m₀ := MeasureSpace.toMeasurableSpace) u
                      (Measure.restrict volume (spaceTimeSet Ω' J)) ∧
                    AEStronglyMeasurable (m₀ := MeasureSpace.toMeasurableSpace) Du
                        (Measure.restrict volume (spaceTimeSet Ω' J)) ∧
                      AEStronglyMeasurable (m₀ := MeasureSpace.toMeasurableSpace) p
                          (Measure.restrict volume (spaceTimeSet Ω' J)) ∧
                        AEStronglyMeasurable (m₀ := MeasureSpace.toMeasurableSpace) f
                            (Measure.restrict volume (spaceTimeSet Ω' J)) ∧
                          LT.lt (α := ℝ≥0∞)
                              (@essSup _ _ _ MeasureSpace.toMeasurableSpace
                                (fun (s : ℝ) => ∫⁻ (x : Vec3) in Ω', ‖u (x, s)‖ₑ ^ (2 : ℝ))
                                (Measure.restrict volume J))
                              ∞ ∧
                            ∫⁻ (z : ParabolicPoint) in spaceTimeSet Ω' J,
                                  ‖u z‖ₑ ^ (2 : ℝ) + ‖Du z‖ₑ ^ (2 : ℝ) <
                                ∞ ∧
                              MemLp (m0 := MeasureSpace.toMeasurableSpace) p
                                  (ENNReal.ofReal (3 / 2 : ℝ))
                                  (Measure.restrict volume (spaceTimeSet Ω' J)) ∧
                                MemLp (m0 := MeasureSpace.toMeasurableSpace) f (ENNReal.ofReal q)
                                    (Measure.restrict volume (spaceTimeSet Ω' J)) ∧
                                  ∀ (i : Fin (3 : ℕ)),
                                    ∀ᵐ (s : ℝ) ∂Measure.restrict volume J,
                                      HasWeakGradientOn Ω' (fun (x : Vec (3 : ℕ)) => u (x, s) i)
                                        fun (x : Vec (3 : ℕ)) => Du (x, s) i) →
                  ∀ᵐ (s : ℝ) ∂Measure.restrict volume T,
                    (MemLp (ε := Vec3) (m0 := MeasureSpace.toMeasurableSpace)
                          (fun (y : Vec3) => u (y, s)) (2 : ℝ≥0∞) (Measure.restrict volume Ω') ∧
                        MemLp (ε := Fin (3 : ℕ) → Vec3) (m0 := MeasureSpace.toMeasurableSpace)
                          (fun (y : Vec3) => Du (y, s)) (2 : ℝ≥0∞) (Measure.restrict volume Ω')) ∧
                      ∀ (i : Fin (3 : ℕ)),
                        HasWeakGradientOn Ω' (fun (y : Vec (3 : ℕ)) => u (y, s) i)
                          fun (y : Vec (3 : ℕ)) => Du (y, s) i
    := by
  intro Ω I q u Du p f hsol z r T Ω' J hbox htime hdata
  rcases hdata with ⟨_, _, _, _, _, _, _, _, hgradJ⟩
  have hslices := slice_memLp_ae_of_sws hsol hbox
  have hgradAll : ∀ᵐ s ∂volume.restrict J, ∀ i : Fin 3,
      HasWeakGradientOn Ω' (fun y => u (y, s) i)
        (fun y => Du (y, s) i) := by
    rw [ae_all_iff]
    intro i
    exact hgradJ i
  filter_upwards [ae_restrict_of_ae_restrict_of_subset htime hslices,
    ae_restrict_of_ae_restrict_of_subset htime hgradAll] with s hs hg
  exact ⟨hs, hg⟩

private lemma gamma_le_gagliardo_hpoint_4 :
    ∀ {u : ParabolicPoint → Vec3} {Du : ParabolicPoint → Fin (3 : ℕ) → Vec3}
      {_ : ParabolicPoint → ℝ} {z : ParabolicPoint} {r : ℝ},
      (0 : ℝ) < r →
        let B : Set Vec3 := euclideanBall z.1 r;
        let T : Set ℝ := Ioc (z.2 - r ^ (2 : ℕ)) z.2;
        let E : ℝ → ℝ≥0∞ := fun (s : ℝ) =>
          ∫⁻ (y : Vec3) in B, ENNReal.ofReal (vec3EuclideanNorm (u (y, s))) ^ (2 : ℝ);
        let A : ℝ → ℝ≥0∞ := fun (s : ℝ) => E s ^ (1 / 2 : ℝ);
        let G : ℝ → ℝ≥0∞ := fun (s : ℝ) =>
          (∫⁻ (y : Vec3) in B, ENNReal.ofReal (spatialGradientSq u Du (y, s))) ^ (1 / 2 : ℝ);
        let R : ℝ≥0∞ := ENNReal.ofReal r ^ (-(3 / 2 : ℝ));
        let C₆ : ℝ≥0∞ :=
          Classical.choose (p := fun (x : ℝ≥0∞) =>
            x ≠ ∞ ∧
              ∀ {x₀ : Vec (3 : ℕ)} {r : ℝ},
                (0 : ℝ) < r →
                  ∀ (v : H1Function (euclideanBall x₀ r)),
                    lpNormOn (3 : ℝ≥0∞) (euclideanBall x₀ r) (v.toFun (U := euclideanBall x₀ r)) ^
                        (3 : ℕ) ≤
                      x *
                            weakGradientLpNormOn (2 : ℝ≥0∞) (euclideanBall x₀ r)
                                (v.grad (U := euclideanBall x₀ r)) ^
                              (3 / 2 : ℝ) *
                          lpNormOn (2 : ℝ≥0∞) (euclideanBall x₀ r)
                              (v.toFun (U := euclideanBall x₀ r)) ^
                            (3 / 2 : ℝ) +
                        x * ENNReal.ofReal r ^ (-(3 / 2 : ℝ)) *
                          lpNormOn (2 : ℝ≥0∞) (euclideanBall x₀ r)
                              (v.toFun (U := euclideanBall x₀ r)) ^
                            (3 : ℕ))
            interpolationBall_three_finite;
        let K : ℝ≥0∞ := (81 : ℝ≥0∞) * ENNReal.ofReal √(3 : ℝ) * C₆;
        ∀ (Ω' : Set Vec3),
          B ⊆ Ω' →
            B = vec3Ball z.1 r →
              (∀ᵐ (s : ℝ) ∂Measure.restrict volume T,
                  (MemLp (ε := Vec3) (m0 := MeasureSpace.toMeasurableSpace)
                        (fun (y : Vec3) => u (y, s)) (2 : ℝ≥0∞) (Measure.restrict volume Ω') ∧
                      MemLp (ε := Fin (3 : ℕ) → Vec3) (m0 := MeasureSpace.toMeasurableSpace)
                        (fun (y : Vec3) => Du (y, s)) (2 : ℝ≥0∞) (Measure.restrict volume Ω')) ∧
                    ∀ (i : Fin (3 : ℕ)),
                      HasWeakGradientOn Ω' (fun (y : Vec (3 : ℕ)) => u (y, s) i)
                        fun (y : Vec (3 : ℕ)) => Du (y, s) i) →
                ∀ᵐ (s : ℝ) ∂Measure.restrict volume T,
                  ∫⁻ (y : Vec3) in B, ENNReal.ofReal (vec3EuclideanNorm (u (y, s))) ^ (3 : ℝ) ≤
                    K * A s ^ (3 / 2 : ℝ) * G s ^ (3 / 2 : ℝ) + K * R * A s ^ (3 : ℝ)
    := by
  intro u Du p z r hr B T E A G R C₆ K Ω' hball hballEq hgood
  filter_upwards [hgood] with s hs
  have hopen : IsOpen (euclideanBall z.1 r) := by
    change IsOpen {y : Vec3 | euclideanSqDist y z.1 < r ^ 2}
    exact (isOpen_lt (contDiff_euclideanSqDist_left z.1).continuous
      continuous_const)
  let H : ∀ i : Fin 3, H1Function (euclideanBall z.1 r) := fun i =>
    { toFun := fun y => u (y, s) i
      grad := fun y => Du (y, s) i
      memL2 := (MemLp.eval hs.1.1 i).mono_measure
        (Measure.restrict_mono_set volume hball)
      gradMemL2 := fun j => (MemLp.eval (MemLp.eval hs.1.2 i) j).mono_measure
        (Measure.restrict_mono_set volume hball)
      hasWeakGradient := (hs.2 i).restrict hopen hball }
  have hcomp : ∀ i : Fin 3, (H i).toFun = fun y => u (y, s) i := by
    intro i
    rfl
  have hsp := vector_interpolation_ball_l3_fixed (x₀ := z.1) (r := r)
    (C₆ := C₆) hr
    (fun {x₀} {r} hr v => (Classical.choose_spec interpolationBall_three_finite).2 hr v)
    H hcomp
  have hAi : ∀ i : Fin 3,
      lpNormOn 2 B (H i).toFun ≤ A s := by
    intro i
    have hstrong : AEStronglyMeasurable (fun y => u (y, s) i)
        (volume.restrict B) := by
      rw [← hcomp i]
      exact (H i).memL2.aestronglyMeasurable
    change eLpNorm (fun y => u (y, s) i) 2 (volume.restrict B) ≤ A s
    rw [eLpNorm_eq_lintegral_rpow_enorm_toReal
      (p := (2 : ℝ≥0∞)) (by norm_num) ENNReal.coe_ne_top hstrong]
    norm_num
    apply ENNReal.rpow_le_rpow
    · apply lintegral_mono
      intro y
      have hpoint : ‖u (y, s) i‖ₑ ^ (2 : ℕ) ≤
          ENNReal.ofReal (vec3EuclideanNorm (u (y, s))) ^ (2 : ℝ) := by
        have hy := component_norm_le_vec3_step2 (u (y, s)) i
        calc
          ‖u (y, s) i‖ₑ ^ (2 : ℕ) = ENNReal.ofReal (‖u (y, s) i‖ ^ 2) := by
            rw [show ‖u (y, s) i‖ₑ = ENNReal.ofReal ‖u (y, s) i‖ from
                (ofReal_norm _).symm, ← ENNReal.ofReal_pow (norm_nonneg _)]
          _ ≤ ENNReal.ofReal (vec3EuclideanNorm (u (y, s)) ^ 2) :=
            ENNReal.ofReal_le_ofReal (pow_le_pow_left₀ (norm_nonneg _) hy 2)
          _ = ENNReal.ofReal (vec3EuclideanNorm (u (y, s))) ^ (2 : ℝ) := by
            rw [ENNReal.ofReal_rpow_of_nonneg
              (vec3EuclideanNorm_nonneg _) (by norm_num)]
            norm_num [Real.rpow_natCast]
      dsimp only
      exact hpoint
    · norm_num
  have hGi : ∀ i : Fin 3,
      weakGradientLpNormOn 2 B (H i).grad ≤ G s := by
    intro i
    have hstrong : AEStronglyMeasurable (fun y => Du (y, s) i)
        (volume.restrict B) := by
      exact (MemLp.eval hs.1.2 i).aestronglyMeasurable.mono_measure
        (Measure.restrict_mono_set volume hball)
    change eLpNorm (fun y => Du (y, s) i) 2 (volume.restrict B) ≤ G s
    rw [eLpNorm_eq_lintegral_rpow_enorm_toReal
      (p := (2 : ℝ≥0∞)) (by norm_num) ENNReal.coe_ne_top hstrong]
    norm_num
    apply ENNReal.rpow_le_rpow
    · apply lintegral_mono
      intro y
      have hpoint : ‖Du (y, s) i‖ₑ ^ (2 : ℕ) ≤
          ENNReal.ofReal (spatialGradientSq u Du (y, s)) := by
        rw [← ENNReal.rpow_natCast]
        exact component_norm_sq_le_spatialGradientSq_step2
          (u := u) (Du := Du) (y, s) i
      dsimp only
      exact hpoint
    · norm_num
  let L : ℝ≥0∞ := ∑ i : Fin 3, lpNormOn 2 B (H i).toFun
  let Q : ℝ≥0∞ := ∑ i : Fin 3, weakGradientLpNormOn 2 B (H i).grad
  have hL : L ≤ 3 * A s := by
    dsimp [L]
    calc
      _ ≤ ∑ _i : Fin 3, A s := Finset.sum_le_sum (fun i _ => hAi i)
      _ = 3 * A s := by simp [Finset.sum_const, Finset.card_univ,
        Fintype.card_fin, nsmul_eq_mul]
  have hQ : Q ≤ 3 * G s := by
    dsimp [Q]
    calc
      _ ≤ ∑ _i : Fin 3, G s := Finset.sum_le_sum (fun i _ => hGi i)
      _ = 3 * G s := by simp [Finset.sum_const, Finset.card_univ,
        Fintype.card_fin, nsmul_eq_mul]
  have hsp' : (∫⁻ y in B,
      ENNReal.ofReal (vec3EuclideanNorm (u (y, s))) ^ (3 : ℝ)) ≤
      3 * ENNReal.ofReal (Real.sqrt 3) * C₆ *
          (3 * G s) ^ (3 / 2 : ℝ) * (3 * A s) ^ (3 / 2 : ℝ) +
        3 * ENNReal.ofReal (Real.sqrt 3) * C₆ * R *
          (3 * A s) ^ (3 : ℝ) := by
    rw [hballEq]
    calc
      _ ≤ 3 * ENNReal.ofReal (Real.sqrt 3) * C₆ * Q ^ (3 / 2 : ℝ) *
            L ^ (3 / 2 : ℝ) +
          3 * ENNReal.ofReal (Real.sqrt 3) * C₆ * R * L ^ (3 : ℝ) := hsp
      _ ≤ _ := by gcongr
  have hsp'' : (∫⁻ y in B,
      ENNReal.ofReal (vec3EuclideanNorm (u (y, s))) ^ (3 : ℝ)) ≤
      3 * ENNReal.ofReal (Real.sqrt 3) * C₆ *
          (3 * G s) ^ (3 / 2 : ℝ) * (3 * A s) ^ (3 / 2 : ℝ) +
        3 * ENNReal.ofReal (Real.sqrt 3) * C₆ * R *
          (3 * A s) ^ (3 : ℝ) := hsp'
  have hGmul : (3 * G s) ^ (3 / 2 : ℝ) =
      (3 : ℝ≥0∞) ^ (3 / 2 : ℝ) * G s ^ (3 / 2 : ℝ) := by
    rw [ENNReal.mul_rpow_of_nonneg _ _ (by norm_num)]
  have hAmul : (3 * A s) ^ (3 / 2 : ℝ) =
      (3 : ℝ≥0∞) ^ (3 / 2 : ℝ) * A s ^ (3 / 2 : ℝ) := by
    rw [ENNReal.mul_rpow_of_nonneg _ _ (by norm_num)]
  have hA3mul : (3 * A s) ^ (3 : ℝ) =
      (3 : ℝ≥0∞) ^ (3 : ℝ) * A s ^ (3 : ℝ) := by
    rw [ENNReal.mul_rpow_of_nonneg _ _ (by norm_num)]
  have hthree : (3 : ℝ≥0∞) ^ (3 / 2 : ℝ) *
      (3 : ℝ≥0∞) ^ (3 / 2 : ℝ) = (3 : ℝ≥0∞) ^ (3 : ℝ) := by
    rw [← ENNReal.rpow_add (3 / 2 : ℝ) (3 / 2 : ℝ) (by norm_num)
      (by norm_num)]
    norm_num
  have hfirst :
      3 * ENNReal.ofReal (Real.sqrt 3) * C₆ *
          ((3 : ℝ≥0∞) ^ (3 / 2 : ℝ) * G s ^ (3 / 2 : ℝ)) *
          ((3 : ℝ≥0∞) ^ (3 / 2 : ℝ) * A s ^ (3 / 2 : ℝ)) =
        81 * ENNReal.ofReal (Real.sqrt 3) * C₆ *
          A s ^ (3 / 2 : ℝ) * G s ^ (3 / 2 : ℝ) := by
    calc
      _ = 3 * ENNReal.ofReal (Real.sqrt 3) * C₆ *
          ((3 : ℝ≥0∞) ^ (3 / 2 : ℝ) * (3 : ℝ≥0∞) ^ (3 / 2 : ℝ)) *
          (G s ^ (3 / 2 : ℝ) * A s ^ (3 / 2 : ℝ)) := by ring
      _ = _ := by rw [hthree]; norm_num; ring
  have hsecond :
      3 * ENNReal.ofReal (Real.sqrt 3) * C₆ * R *
          ((3 : ℝ≥0∞) ^ (3 : ℝ) * A s ^ (3 : ℝ)) =
        81 * ENNReal.ofReal (Real.sqrt 3) * C₆ * R * A s ^ (3 : ℝ) := by
    norm_num
    ring
  calc
    _ ≤ 3 * ENNReal.ofReal (Real.sqrt 3) * C₆ *
        (3 * G s) ^ (3 / 2 : ℝ) * (3 * A s) ^ (3 / 2 : ℝ) +
        3 * ENNReal.ofReal (Real.sqrt 3) * C₆ * R *
          (3 * A s) ^ (3 : ℝ) := hsp''
    _ = K * A s ^ (3 / 2 : ℝ) * G s ^ (3 / 2 : ℝ) +
        K * R * A s ^ (3 : ℝ) := by
      rw [hGmul, hAmul, hA3mul, hfirst, hsecond]

private lemma gamma_le_gagliardo_hterm1_5 :
    ∀ {u : ParabolicPoint → Vec3} {Du : ParabolicPoint → Fin (3 : ℕ) → Vec3} {z : ParabolicPoint}
      {r : ℝ},
      (0 : ℝ) < r →
        let B : Set Vec3 := euclideanBall z.1 r;
        let T : Set ℝ := Ioc (z.2 - r ^ (2 : ℕ)) z.2;
        let E : ℝ → ℝ≥0∞ := fun (s : ℝ) =>
          ∫⁻ (y : Vec3) in B, ENNReal.ofReal (vec3EuclideanNorm (u (y, s))) ^ (2 : ℝ);
        let A₀ : ℝ≥0∞ :=
          @essSup _ _ _ MeasureSpace.toMeasurableSpace E (Measure.restrict volume T) ^ (1 / 2 : ℝ);
        let D : ℝ≥0∞ :=
          ∫⁻ (w : ParabolicPoint) in parabolicCylinder z.1 z.2 r,
            ENNReal.ofReal (spatialGradientSq u Du w);
        let V : ℝ≥0∞ := ENNReal.ofReal (r ^ (2 : ℝ));
        D = ENNReal.ofReal (r * beta u Du z r ^ (2 : ℕ)) →
          A₀ = ENNReal.ofReal (r * alpha u z r ^ (2 : ℕ)) ^ (1 / 2 : ℝ) →
            (0 : ℝ) ≤ alpha u z r →
              (0 : ℝ) ≤ beta u Du z r →
                (0 : ℝ) ≤ r ^ (2 : ℕ) →
                  (0 : ℝ) ≤ alpha u z r ^ (2 : ℕ) →
                    (0 : ℝ) ≤ beta u Du z r ^ (2 : ℕ) →
                      A₀ ^ (3 / 2 : ℝ) * D ^ (3 / 4 : ℝ) * V ^ (1 / 4 : ℝ) ≤
                        ENNReal.ofReal
                          (r ^ (2 : ℝ) * (alpha u z r ^ (3 / 2 : ℝ) * beta u Du z r ^ (3 / 2 : ℝ)))
    := by
  intro u Du z r hr B T E A₀ D V hDeq hA₀eq hα hβ hr2_nat hα2 hβ2
  rw [hA₀eq, hDeq]
  dsimp [V]
  rw [← ENNReal.rpow_mul]
  norm_num
  rw [ENNReal.ofReal_rpow_of_nonneg
    (mul_nonneg hr.le hα2) (by norm_num),
    ENNReal.ofReal_rpow_of_nonneg
      (mul_nonneg hr.le hβ2) (by norm_num),
    ENNReal.ofReal_rpow_of_nonneg hr2_nat (by norm_num)]
  rw [← ENNReal.ofReal_mul (by positivity),
    ← ENNReal.ofReal_mul (by positivity)]
  rw [Real.mul_rpow hr.le (by positivity),
    Real.mul_rpow hr.le (by positivity)]
  have ha : (alpha u z r ^ 2) ^ (3 / 4 : ℝ) =
      alpha u z r ^ (3 / 2 : ℝ) := by
    calc
      (alpha u z r ^ 2) ^ (3 / 4 : ℝ) =
          (alpha u z r ^ (2 : ℝ)) ^ (3 / 4 : ℝ) := by
        exact congrArg (fun x : ℝ => x ^ (3 / 4 : ℝ))
          (Real.rpow_natCast (alpha u z r) 2).symm
      _ = alpha u z r ^ ((2 : ℝ) * (3 / 4 : ℝ)) :=
        (Real.rpow_mul hα 2 (3 / 4 : ℝ)).symm
      _ = alpha u z r ^ (3 / 2 : ℝ) := by norm_num
  have hb : (beta u Du z r ^ 2) ^ (3 / 4 : ℝ) =
      beta u Du z r ^ (3 / 2 : ℝ) := by
    calc
      (beta u Du z r ^ 2) ^ (3 / 4 : ℝ) =
          (beta u Du z r ^ (2 : ℝ)) ^ (3 / 4 : ℝ) := by
        exact congrArg (fun x : ℝ => x ^ (3 / 4 : ℝ))
          (Real.rpow_natCast (beta u Du z r) 2).symm
      _ = beta u Du z r ^ ((2 : ℝ) * (3 / 4 : ℝ)) :=
        (Real.rpow_mul hβ 2 (3 / 4 : ℝ)).symm
      _ = beta u Du z r ^ (3 / 2 : ℝ) := by norm_num
  have hrpow : (r ^ 2) ^ (1 / 4 : ℝ) = r ^ (1 / 2 : ℝ) := by
    calc
      (r ^ 2) ^ (1 / 4 : ℝ) = (r ^ (2 : ℝ)) ^ (1 / 4 : ℝ) := by
        exact congrArg (fun x : ℝ => x ^ (1 / 4 : ℝ))
          (Real.rpow_natCast r 2).symm
      _ = r ^ ((2 : ℝ) * (1 / 4 : ℝ)) :=
        (Real.rpow_mul hr.le 2 (1 / 4 : ℝ)).symm
      _ = r ^ (1 / 2 : ℝ) := by norm_num
  rw [ha, hb, hrpow]
  have hr3 : r ^ (3 / 4 : ℝ) * r ^ (3 / 4 : ℝ) *
      r ^ (1 / 2 : ℝ) = r ^ (2 : ℝ) := by
    rw [← Real.rpow_add hr, ← Real.rpow_add hr]
    norm_num
  have hreal : r ^ (3 / 4 : ℝ) * alpha u z r ^ (3 / 2 : ℝ) *
        (r ^ (3 / 4 : ℝ) * beta u Du z r ^ (3 / 2 : ℝ)) *
        r ^ (1 / 2 : ℝ) =
      r ^ (2 : ℝ) * (alpha u z r ^ (3 / 2 : ℝ) *
        beta u Du z r ^ (3 / 2 : ℝ)) := by
    calc
      _ = (r ^ (3 / 4 : ℝ) * r ^ (3 / 4 : ℝ) *
          r ^ (1 / 2 : ℝ)) *
          (alpha u z r ^ (3 / 2 : ℝ) * beta u Du z r ^ (3 / 2 : ℝ)) := by
            ring
      _ = _ := by rw [hr3]
  rw [hreal]
  apply le_of_eq
  congr 1
  exact congrArg (fun x : ℝ => x *
      (alpha u z r ^ (3 / 2 : ℝ) * beta u Du z r ^ (3 / 2 : ℝ)))
    (Real.rpow_natCast r 2)

private lemma gamma_le_gagliardo_hterm2_6 :
    ∀ {u : ParabolicPoint → Vec3} {z : ParabolicPoint} {r : ℝ},
      (0 : ℝ) < r →
        let B : Set Vec3 := euclideanBall z.1 r;
        let T : Set ℝ := Ioc (z.2 - r ^ (2 : ℕ)) z.2;
        let E : ℝ → ℝ≥0∞ := fun (s : ℝ) =>
          ∫⁻ (y : Vec3) in B, ENNReal.ofReal (vec3EuclideanNorm (u (y, s))) ^ (2 : ℝ);
        let A₀ : ℝ≥0∞ :=
          @essSup _ _ _ MeasureSpace.toMeasurableSpace E (Measure.restrict volume T) ^ (1 / 2 : ℝ);
        let V : ℝ≥0∞ := ENNReal.ofReal (r ^ (2 : ℝ));
        let R : ℝ≥0∞ := ENNReal.ofReal r ^ (-(3 / 2 : ℝ));
        A₀ = ENNReal.ofReal (r * alpha u z r ^ (2 : ℕ)) ^ (1 / 2 : ℝ) →
          (0 : ℝ) ≤ alpha u z r →
            (0 : ℝ) ≤ r ^ (2 : ℕ) →
              (0 : ℝ) ≤ alpha u z r ^ (2 : ℕ) →
                R * V * A₀ ^ (3 : ℝ) ≤ ENNReal.ofReal (r ^ (2 : ℝ) * alpha u z r ^ (3 : ℝ))
    := by
  intro u z r hr B T E A₀ V R hA₀eq hα hr2_nat hα2
  rw [hA₀eq]
  dsimp [R, V]
  rw [← ENNReal.rpow_mul]
  norm_num
  have hr0 : ENNReal.ofReal r ≠ 0 := (ENNReal.ofReal_pos.mpr hr).ne'
  have hrtop : ENNReal.ofReal r ≠ ⊤ := ENNReal.ofReal_ne_top
  have hcancel : (ENNReal.ofReal r) ^ (-(3 / 2 : ℝ)) *
      (ENNReal.ofReal r) ^ (3 / 2 : ℝ) = 1 := by
    rw [← ENNReal.rpow_add (-(3 / 2 : ℝ)) (3 / 2 : ℝ) hr0 hrtop]
    norm_num
  have hsplit :
      ENNReal.ofReal (r * alpha u z r ^ 2) ^ (3 / 2 : ℝ) =
        (ENNReal.ofReal r) ^ (3 / 2 : ℝ) *
          ENNReal.ofReal (alpha u z r ^ 2) ^ (3 / 2 : ℝ) := by
    calc
      _ = ENNReal.ofReal ((r * alpha u z r ^ 2) ^ (3 / 2 : ℝ)) :=
        ENNReal.ofReal_rpow_of_nonneg
          (mul_nonneg hr.le (sq_nonneg _)) (by norm_num)
      _ = ENNReal.ofReal (r ^ (3 / 2 : ℝ) *
          (alpha u z r ^ 2) ^ (3 / 2 : ℝ)) := by
        rw [Real.mul_rpow hr.le (sq_nonneg _)]
      _ = (ENNReal.ofReal r) ^ (3 / 2 : ℝ) *
          ENNReal.ofReal (alpha u z r ^ 2) ^ (3 / 2 : ℝ) := by
        rw [ENNReal.ofReal_mul (by positivity),
          ← ENNReal.ofReal_rpow_of_nonneg hr.le (by norm_num),
          ← ENNReal.ofReal_rpow_of_nonneg hα2 (by norm_num)]
  have ha3 : ENNReal.ofReal (alpha u z r ^ 2) ^ (3 / 2 : ℝ) =
      ENNReal.ofReal (alpha u z r ^ (3 : ℕ)) := by
    rw [ENNReal.ofReal_rpow_of_nonneg (sq_nonneg _) (by norm_num)]
    congr 1
    calc
      (alpha u z r ^ 2) ^ (3 / 2 : ℝ) =
          (alpha u z r ^ (2 : ℝ)) ^ (3 / 2 : ℝ) := by
            exact congrArg (fun x : ℝ => x ^ (3 / 2 : ℝ))
              (Real.rpow_natCast (alpha u z r) 2).symm
      _ = alpha u z r ^ ((2 : ℝ) * (3 / 2 : ℝ)) :=
        (Real.rpow_mul hα 2 (3 / 2 : ℝ)).symm
      _ = alpha u z r ^ (3 : ℝ) := by
        congr 1
        norm_num
      _ = alpha u z r ^ (3 : ℕ) := Real.rpow_natCast (alpha u z r) 3
  rw [hsplit]
  calc
    _ = ((ENNReal.ofReal r) ^ (-(3 / 2 : ℝ)) *
        (ENNReal.ofReal r) ^ (3 / 2 : ℝ)) *
        ENNReal.ofReal (r ^ 2) *
        ENNReal.ofReal (alpha u z r ^ 2) ^ (3 / 2 : ℝ) := by ring
    _ = ENNReal.ofReal (r ^ 2) *
        ENNReal.ofReal (alpha u z r ^ 2) ^ (3 / 2 : ℝ) := by
      rw [hcancel, one_mul]
    _ = ENNReal.ofReal (r ^ 2) *
        ENNReal.ofReal (alpha u z r ^ (3 : ℕ)) := by rw [ha3]
    _ = ENNReal.ofReal (r ^ 2 * alpha u z r ^ (3 : ℕ)) := by
      rw [← ENNReal.ofReal_mul hr2_nat]
  exact le_refl _

private lemma gamma_le_gagliardo_hH1_7 :
    ∀ {u : ParabolicPoint → Vec3} {Du : ParabolicPoint → Fin (3 : ℕ) → Vec3} {z : ParabolicPoint}
      {r : ℝ},
      let B : Set Vec3 := euclideanBall z.1 r;
      let T : Set ℝ := Ioc (z.2 - r ^ (2 : ℕ)) z.2;
      let E : ℝ → ℝ≥0∞ := fun (s : ℝ) =>
        ∫⁻ (y : Vec3) in B, ENNReal.ofReal (vec3EuclideanNorm (u (y, s))) ^ (2 : ℝ);
      let A₀ : ℝ≥0∞ :=
        @essSup _ _ _ MeasureSpace.toMeasurableSpace E (Measure.restrict volume T) ^ (1 / 2 : ℝ);
      let D : ℝ≥0∞ :=
        ∫⁻ (w : ParabolicPoint) in parabolicCylinder z.1 z.2 r,
          ENNReal.ofReal (spatialGradientSq u Du w);
      let V : ℝ≥0∞ := ENNReal.ofReal (r ^ (2 : ℝ));
      let R : ℝ≥0∞ := ENNReal.ofReal r ^ (-(3 / 2 : ℝ));
      let C₆ : ℝ≥0∞ :=
        Classical.choose (p := fun (x : ℝ≥0∞) =>
          x ≠ ∞ ∧
            ∀ {x₀ : Vec (3 : ℕ)} {r : ℝ},
              (0 : ℝ) < r →
                ∀ (v : H1Function (euclideanBall x₀ r)),
                  lpNormOn (3 : ℝ≥0∞) (euclideanBall x₀ r) (v.toFun (U := euclideanBall x₀ r)) ^
                      (3 : ℕ) ≤
                    x *
                          weakGradientLpNormOn (2 : ℝ≥0∞) (euclideanBall x₀ r)
                              (v.grad (U := euclideanBall x₀ r)) ^
                            (3 / 2 : ℝ) *
                        lpNormOn (2 : ℝ≥0∞) (euclideanBall x₀ r)
                            (v.toFun (U := euclideanBall x₀ r)) ^
                          (3 / 2 : ℝ) +
                      x * ENNReal.ofReal r ^ (-(3 / 2 : ℝ)) *
                        lpNormOn (2 : ℝ≥0∞) (euclideanBall x₀ r)
                            (v.toFun (U := euclideanBall x₀ r)) ^
                          (3 : ℕ))
          interpolationBall_three_finite;
      let K : ℝ≥0∞ := (81 : ℝ≥0∞) * ENNReal.ofReal √(3 : ℝ) * C₆;
      let C : ℝ := K.toReal;
      (0 : ℝ) ≤ C →
        let C₉ : ℝ := (1 : ℝ) + C;
        (0 : ℝ) ≤ C₉ →
          (1 : ℝ) ≤ C₉ →
            ENNReal.ofReal C = K →
              ∫⁻ (w : ParabolicPoint) in parabolicCylinder z.1 z.2 r,
                    ENNReal.ofReal (vec3EuclideanNorm (u w)) ^ (3 : ℝ) ≤
                  K * A₀ ^ (3 / 2 : ℝ) * D ^ (3 / 4 : ℝ) * V ^ (1 / 4 : ℝ) +
                    K * R * V * A₀ ^ (3 : ℝ) →
                (0 : ℝ) ≤ alpha u z r →
                  (0 : ℝ) ≤ beta u Du z r →
                    (0 : ℝ) ≤ r ^ (2 : ℝ) →
                      (0 : ℝ≥0∞) ≤ K →
                        (0 : ℝ) ≤
                            C *
                              (r ^ (2 : ℝ) *
                                (alpha u z r ^ (3 / 2 : ℝ) * beta u Du z r ^ (3 / 2 : ℝ))) →
                          (0 : ℝ) ≤ C * (r ^ (2 : ℝ) * alpha u z r ^ (3 : ℕ)) →
                            A₀ ^ (3 / 2 : ℝ) * D ^ (3 / 4 : ℝ) * V ^ (1 / 4 : ℝ) ≤
                                ENNReal.ofReal
                                  (r ^ (2 : ℝ) *
                                    (alpha u z r ^ (3 / 2 : ℝ) * beta u Du z r ^ (3 / 2 : ℝ))) →
                              R * V * A₀ ^ (3 : ℝ) ≤
                                  ENNReal.ofReal (r ^ (2 : ℝ) * alpha u z r ^ (3 : ℕ)) →
                                ∫⁻ (w : ParabolicPoint) in parabolicCylinder z.1 z.2 r,
                                    ENNReal.ofReal (vec3EuclideanNorm (u w)) ^ (3 : ℝ) ≤
                                  ENNReal.ofReal
                                    (r ^ (2 : ℝ) *
                                      (C₉ * alpha u z r ^ (1 / 2 : ℝ) *
                                            beta u Du z r ^ (1 / 2 : ℝ) +
                                          C₉ * alpha u z r) ^
                                        (3 : ℝ))
    := by
  intro u Du z r B T E A₀ D V R C₆ K C hC0 C₉ hC₉0 hC₉1 hCof htimebound hα hβ hr2 hK0 hCterm1
    hCterm2 hterm1 hterm2_nat
  have hT :
      K * A₀ ^ (3 / 2 : ℝ) * D ^ (3 / 4 : ℝ) * V ^ (1 / 4 : ℝ) +
          K * R * V * A₀ ^ (3 : ℝ) ≤
        ENNReal.ofReal (C * (r ^ (2 : ℝ) *
            (alpha u z r ^ (3 / 2 : ℝ) * beta u Du z r ^ (3 / 2 : ℝ))) +
          C * (r ^ (2 : ℝ) * alpha u z r ^ (3 : ℕ))) := by
    calc
      _ ≤ K * ENNReal.ofReal (r ^ (2 : ℝ) *
            (alpha u z r ^ (3 / 2 : ℝ) * beta u Du z r ^ (3 / 2 : ℝ))) +
          K * ENNReal.ofReal (r ^ (2 : ℝ) * alpha u z r ^ (3 : ℕ)) := by
        exact add_le_add
          (by
            simpa only [mul_assoc] using
              (mul_le_mul_of_nonneg_left hterm1 hK0))
          (by
            simpa only [mul_assoc] using
              (mul_le_mul_of_nonneg_left hterm2_nat hK0))
      _ = _ := by
        rw [← hCof, ← ENNReal.ofReal_mul hC0,
          ← ENNReal.ofReal_mul hC0,
          ← ENNReal.ofReal_add hCterm1 hCterm2]
  let X : ℝ := alpha u z r ^ (1 / 2 : ℝ) * beta u Du z r ^ (1 / 2 : ℝ)
  let Y : ℝ := alpha u z r
  have hX0 : 0 ≤ X := by
    dsimp [X]
    exact mul_nonneg (Real.rpow_nonneg hα _) (Real.rpow_nonneg hβ _)
  have hY0 : 0 ≤ Y := by dsimp [Y]; exact hα
  have hXcube : X ^ (3 : ℕ) =
      alpha u z r ^ (3 / 2 : ℝ) * beta u Du z r ^ (3 / 2 : ℝ) := by
    dsimp [X]
    rw [mul_pow]
    have haHalf3 : (alpha u z r ^ (1 / 2 : ℝ)) ^ (3 : ℕ) =
        alpha u z r ^ (3 / 2 : ℝ) := by
      calc
        _ = (alpha u z r ^ (1 / 2 : ℝ)) ^ (3 : ℝ) := by
          exact (Real.rpow_natCast (alpha u z r ^ (1 / 2 : ℝ)) 3).symm
        _ = alpha u z r ^ ((1 / 2 : ℝ) * 3) :=
          (Real.rpow_mul hα (1 / 2 : ℝ) 3).symm
        _ = _ := by norm_num
    have hbHalf3 : (beta u Du z r ^ (1 / 2 : ℝ)) ^ (3 : ℕ) =
        beta u Du z r ^ (3 / 2 : ℝ) := by
      calc
        _ = (beta u Du z r ^ (1 / 2 : ℝ)) ^ (3 : ℝ) := by
          exact (Real.rpow_natCast (beta u Du z r ^ (1 / 2 : ℝ)) 3).symm
        _ = beta u Du z r ^ ((1 / 2 : ℝ) * 3) :=
          (Real.rpow_mul hβ (1 / 2 : ℝ) 3).symm
        _ = _ := by norm_num
    rw [haHalf3, hbHalf3]
  have hsumcube : X ^ (3 : ℕ) + Y ^ (3 : ℕ) ≤ (X + Y) ^ (3 : ℕ) := by
    have hthreeX : 0 ≤ 3 * X := mul_nonneg (by norm_num) hX0
    have hthreeXY : 0 ≤ 3 * X * Y := mul_nonneg hthreeX hY0
    have hnon : 0 ≤ 3 * X * Y * (X + Y) :=
      mul_nonneg hthreeXY (add_nonneg hX0 hY0)
    nlinarith only [hnon]
  have hC_le : C ≤ C₉ := by dsimp [C₉]; linarith only [hC0]
  have hC₉sq : 1 ≤ C₉ ^ (2 : ℕ) := by
    nlinarith only [sq_nonneg (C₉ - 1), hC₉1]
  have hC₉cube : C₉ ≤ C₉ ^ (3 : ℕ) := by
    calc
      C₉ = C₉ * 1 := by ring
      _ ≤ C₉ * C₉ ^ (2 : ℕ) :=
        mul_le_mul_of_nonneg_left hC₉sq hC₉0
      _ = C₉ ^ (3 : ℕ) := by ring
  have hrealbound :
      C * (r ^ (2 : ℝ) *
          (alpha u z r ^ (3 / 2 : ℝ) * beta u Du z r ^ (3 / 2 : ℝ))) +
        C * (r ^ (2 : ℝ) * alpha u z r ^ (3 : ℕ)) ≤
      r ^ (2 : ℝ) * (C₉ * X + C₉ * Y) ^ (3 : ℕ) := by
    calc
      _ = C * (r ^ (2 : ℝ) * (X ^ (3 : ℕ) + Y ^ (3 : ℕ))) := by
        rw [hXcube]
        dsimp [Y]
        ring
      _ ≤ C₉ * (r ^ (2 : ℝ) * (X ^ (3 : ℕ) + Y ^ (3 : ℕ))) := by
        apply mul_le_mul_of_nonneg_right hC_le
        exact mul_nonneg hr2
          (add_nonneg (pow_nonneg hX0 _) (pow_nonneg hY0 _))
      _ ≤ C₉ * (r ^ (2 : ℝ) * (X + Y) ^ (3 : ℕ)) := by
        exact mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left hsumcube hr2) hC₉0
      _ ≤ C₉ ^ (3 : ℕ) * (r ^ (2 : ℝ) * (X + Y) ^ (3 : ℕ)) := by
        exact mul_le_mul_of_nonneg_right hC₉cube
          (mul_nonneg hr2 (pow_nonneg (add_nonneg hX0 hY0) _))
      _ = r ^ (2 : ℝ) * (C₉ * X + C₉ * Y) ^ (3 : ℕ) := by
        ring
  have hrealbound' :
      C * (r ^ (2 : ℝ) *
          (alpha u z r ^ (3 / 2 : ℝ) * beta u Du z r ^ (3 / 2 : ℝ))) +
        C * (r ^ (2 : ℝ) * alpha u z r ^ (3 : ℕ)) ≤
      r ^ (2 : ℝ) *
        (C₉ * alpha u z r ^ (1 / 2 : ℝ) * beta u Du z r ^ (1 / 2 : ℝ) +
          C₉ * alpha u z r) ^ (3 : ℕ) := by
    simpa [X, Y, mul_assoc] using hrealbound
  have hrealbound'' :
      C * (r ^ (2 : ℝ) *
          (alpha u z r ^ (3 / 2 : ℝ) * beta u Du z r ^ (3 / 2 : ℝ))) +
        C * (r ^ (2 : ℝ) * alpha u z r ^ (3 : ℕ)) ≤
      r ^ (2 : ℝ) *
        (C₉ * alpha u z r ^ (1 / 2 : ℝ) * beta u Du z r ^ (1 / 2 : ℝ) +
          C₉ * alpha u z r) ^ (3 : ℝ) := by
    calc
      _ ≤ r ^ (2 : ℝ) *
            (C₉ * alpha u z r ^ (1 / 2 : ℝ) * beta u Du z r ^ (1 / 2 : ℝ) +
              C₉ * alpha u z r) ^ (3 : ℕ) := hrealbound'
      _ = _ := by
        apply congrArg (fun x : ℝ => r ^ (2 : ℝ) * x)
        exact (Real.rpow_natCast _ 3).symm
  calc
    _ ≤ K * A₀ ^ (3 / 2 : ℝ) * D ^ (3 / 4 : ℝ) * V ^ (1 / 4 : ℝ) +
        K * R * V * A₀ ^ (3 : ℝ) := htimebound
    _ ≤ ENNReal.ofReal (C * (r ^ (2 : ℝ) *
          (alpha u z r ^ (3 / 2 : ℝ) * beta u Du z r ^ (3 / 2 : ℝ))) +
        C * (r ^ (2 : ℝ) * alpha u z r ^ (3 : ℕ))) := hT
    _ ≤ _ := ENNReal.ofReal_le_ofReal hrealbound''

private lemma gamma_le_gagliardo_htime_1 :
    ∀ {z : ParabolicPoint} {r : ℝ},
      (0 : ℝ) < r →
        let T : Set ℝ := Ioc (z.2 - r ^ (2 : ℕ)) z.2;
        ∀ (Ω' : Set Vec3) (J : Set ℝ), parabolicCylinder z.1 z.2 r ⊆ spaceTimeSet Ω' J → T ⊆ J
    := by
  intro z r hr T Ω' J hcyl s hs
  have hx : z.1 ∈ vec3Ball z.1 r := by
    rw [mem_vec3Ball]
    simpa [vec3EuclideanNorm_zero] using hr
  have hz : (z.1, s) ∈ parabolicCylinder z.1 z.2 r := by
    rw [parabolicCylinder]
    exact ⟨hx, hs⟩
  exact (hcyl hz).2

private lemma gamma_le_gagliardo_hDprod_2 :
    ∀ {q : ℝ} {u : ParabolicPoint → Vec3} {Du : ParabolicPoint → Fin (3 : ℕ) → Vec3}
      {p : ParabolicPoint → ℝ} {f : ParabolicPoint → Vec3} (Ω' : Set Vec3) (J : Set ℝ),
      (AEStronglyMeasurable (m₀ := MeasureSpace.toMeasurableSpace) u
            (Measure.restrict volume (spaceTimeSet Ω' J)) ∧
          AEStronglyMeasurable (m₀ := MeasureSpace.toMeasurableSpace) Du
              (Measure.restrict volume (spaceTimeSet Ω' J)) ∧
            AEStronglyMeasurable (m₀ := MeasureSpace.toMeasurableSpace) p
                (Measure.restrict volume (spaceTimeSet Ω' J)) ∧
              AEStronglyMeasurable (m₀ := MeasureSpace.toMeasurableSpace) f
                  (Measure.restrict volume (spaceTimeSet Ω' J)) ∧
                LT.lt (α := ℝ≥0∞)
                    (@essSup _ _ _ MeasureSpace.toMeasurableSpace
                      (fun (s : ℝ) => ∫⁻ (x : Vec3) in Ω', ‖u (x, s)‖ₑ ^ (2 : ℝ))
                      (Measure.restrict volume J))
                    ∞ ∧
                  ∫⁻ (z : ParabolicPoint) in spaceTimeSet Ω' J,
                        ‖u z‖ₑ ^ (2 : ℝ) + ‖Du z‖ₑ ^ (2 : ℝ) <
                      ∞ ∧
                    MemLp (m0 := MeasureSpace.toMeasurableSpace) p (ENNReal.ofReal (3 / 2 : ℝ))
                        (Measure.restrict volume (spaceTimeSet Ω' J)) ∧
                      MemLp (m0 := MeasureSpace.toMeasurableSpace) f (ENNReal.ofReal q)
                          (Measure.restrict volume (spaceTimeSet Ω' J)) ∧
                        ∀ (i : Fin (3 : ℕ)),
                          ∀ᵐ (s : ℝ) ∂Measure.restrict volume J,
                            HasWeakGradientOn Ω' (fun (x : Vec (3 : ℕ)) => u (x, s) i)
                              fun (x : Vec (3 : ℕ)) => Du (x, s) i) →
        AEMeasurable (β := ℝ≥0∞) (_m := Prod.instMeasurableSpace)
          (fun (w : Vec3 × ℝ) => ENNReal.ofReal (spatialGradientSq u Du w))
          (Measure.prod (Measure.restrict volume Ω') (Measure.restrict volume J))
    := by
  intro q u Du p f Ω' J hdata
  rw [Measure.prod_restrict Ω' J]
  have hD := hdata.2.1
  have hcont : Continuous (fun v : Fin 3 → Vec3 =>
      ∑ i, ∑ j, (v i j) ^ (2 : ℕ)) := by fun_prop
  have hm := (ENNReal.continuous_ofReal.comp hcont).comp_aestronglyMeasurable hD
  exact hm.aemeasurable

private lemma gamma_le_gagliardo_hEeq_3 :
    ∀ {u : ParabolicPoint → Vec3} {z : ParabolicPoint} {r : ℝ},
      let B : Set Vec3 := euclideanBall z.1 r;
      let E : ℝ → ℝ≥0∞ := fun (s : ℝ) =>
        ∫⁻ (y : Vec3) in B, ENNReal.ofReal (vec3EuclideanNorm (u (y, s))) ^ (2 : ℝ);
      B = vec3Ball z.1 r →
        E = fun (s : ℝ) =>
          timeSliceBallEnergy z.1 r s fun (w : ParabolicPoint) => vec3EuclideanNorm (u w)
    := by
  intro u z r B E hballEq
  funext s
  dsimp [E, timeSliceBallEnergy]
  rw [hballEq]
  apply lintegral_congr
  intro y
  rw [Real.enorm_eq_ofReal (vec3EuclideanNorm_nonneg _)]

private lemma gamma_le_gagliardo_hV_4 :
    ∀ {z : ParabolicPoint} {r : ℝ},
      let T : Set ℝ := Ioc (z.2 - r ^ (2 : ℕ)) z.2;
      let V : ℝ≥0∞ := ENNReal.ofReal (r ^ (2 : ℝ));
      (volume : Set ℝ → ℝ≥0∞) T ≤ V
    := by
  intro z r T V
  dsimp [T, V]
  rw [Real.volume_Ioc]
  have hEq : z.2 - (z.2 - r ^ 2) = r ^ 2 := by ring
  rw [hEq]
  simp

theorem gamma_le_gagliardo_of_sws
    {Ω : Set Vec3} {I : Set ℝ} {q : ℝ}
    {u : ParabolicPoint → Vec3} {Du : ParabolicPoint → Fin 3 → Vec3}
    {p : ParabolicPoint → ℝ} {f : ParabolicPoint → Vec3}
    (hsol : IsSuitableWeakSolutionIntegrable Ω I q u Du p f)
    {z : ParabolicPoint} {r : ℝ} (hr : 0 < r)
    (hsub : closure (parabolicCylinder z.1 z.2 r) ⊆ spaceTimeSet Ω I) :
    gamma u z r ≤
      gagliardoConstant * alpha u z r ^ (1 / 2 : ℝ) * beta u Du z r ^ (1 / 2 : ℝ) +
        gagliardoConstant * alpha u z r := by
  let B : Set Vec3 := euclideanBall z.1 r
  let T : Set ℝ := Ioc (z.2 - r ^ 2) z.2
  let E : ℝ → ℝ≥0∞ := fun s =>
    ∫⁻ y in B, ENNReal.ofReal (vec3EuclideanNorm (u (y, s))) ^ (2 : ℝ)
  let A : ℝ → ℝ≥0∞ := fun s => E s ^ (1 / 2 : ℝ)
  let G : ℝ → ℝ≥0∞ := fun s =>
    (∫⁻ y in B, ENNReal.ofReal (spatialGradientSq u Du (y, s))) ^
      (1 / 2 : ℝ)
  let A₀ : ℝ≥0∞ := (essSup E (volume.restrict T)) ^ (1 / 2 : ℝ)
  let D : ℝ≥0∞ := ∫⁻ w in parabolicCylinder z.1 z.2 r,
    ENNReal.ofReal (spatialGradientSq u Du w)
  let V : ℝ≥0∞ := ENNReal.ofReal (r ^ (2 : ℝ))
  let R : ℝ≥0∞ := (ENNReal.ofReal r) ^ (-(3 / 2 : ℝ))
  let C₆ : ℝ≥0∞ := Classical.choose interpolationBall_three_finite
  have hC₆ : C₆ ≠ ∞ := (Classical.choose_spec interpolationBall_three_finite).1
  let K : ℝ≥0∞ := 81 * ENNReal.ofReal (Real.sqrt 3) * C₆
  have hKtop : K ≠ ∞ := by
    dsimp [K]
    exact ENNReal.mul_ne_top
      (ENNReal.mul_ne_top (by norm_num) ENNReal.ofReal_ne_top) hC₆
  let C : ℝ := K.toReal
  have hC0 : 0 ≤ C := by
    dsimp [C]
    exact ENNReal.toReal_nonneg
  let C₉ : ℝ := 1 + C
  have hC₉0 : 0 ≤ C₉ := by
    dsimp [C₉]
    linarith only [hC0]
  have hC₉1 : 1 ≤ C₉ := by
    dsimp [C₉]
    linarith only [hC0]
  have hCof : ENNReal.ofReal C = K := by
    exact ENNReal.ofReal_toReal hKtop
  obtain ⟨Ω', J, hbox, hcyl⟩ := exists_localBox_of_closure_subset
    hsol.1 hsol.2.1 hr hsub
  have hball := @gamma_le_gagliardo_hball_1 z r hr Ω' J hcyl
  have htime := @gamma_le_gagliardo_htime_1 z r hr Ω' J hcyl
  have hveccont : Continuous (vec3EuclideanNorm : Vec3 → ℝ) := by
    unfold vec3EuclideanNorm
    fun_prop
  have hdata := hsol.2.2.2.2.2.1 Ω' J hbox
  have hUprod : AEMeasurable (fun w =>
      ENNReal.ofReal (vec3EuclideanNorm (u w)) ^ (2 : ℝ))
      ((volume.restrict Ω').prod (volume.restrict J)) := by
    rw [Measure.prod_restrict Ω' J]
    have hnorm := hveccont.measurable.comp_aemeasurable hdata.1.aemeasurable
    exact (hnorm.ennreal_ofReal).pow_const (2 : ℝ)
  have hUprod3 : AEMeasurable (fun w =>
      ENNReal.ofReal (vec3EuclideanNorm (u w)) ^ (3 : ℝ))
      ((volume.restrict Ω').prod (volume.restrict J)) := by
    rw [Measure.prod_restrict Ω' J]
    have hnorm := hveccont.measurable.comp_aemeasurable hdata.1.aemeasurable
    exact (hnorm.ennreal_ofReal).pow_const (3 : ℝ)
  have hDprod := @gamma_le_gagliardo_hDprod_2 q u Du p f Ω' J hdata
  have hUprodB : AEMeasurable (fun w =>
      ENNReal.ofReal (vec3EuclideanNorm (u w)) ^ (2 : ℝ))
      ((volume.restrict B).prod (volume.restrict J)) := by
    exact hUprod.mono_measure (Measure.prod_mono
      (Measure.restrict_mono_set volume hball) le_rfl)
  have hDprodB : AEMeasurable (fun w : Vec3 × ℝ =>
      ENNReal.ofReal (spatialGradientSq u Du w))
      ((volume.restrict B).prod (volume.restrict J)) := by
    exact hDprod.mono_measure (Measure.prod_mono
      (Measure.restrict_mono_set volume hball) le_rfl)
  have hEmeas : AEMeasurable E (volume.restrict T) := by
    dsimp [E]
    exact hUprodB.lintegral_prod_left'
      |>.mono_measure (Measure.restrict_mono_set volume htime)
  have hAmeas : AEMeasurable A (volume.restrict T) := by
    dsimp [A]
    exact hEmeas.pow_const (1 / 2 : ℝ)
  have hGmeas : AEMeasurable G (volume.restrict T) := by
    dsimp [G]
    exact (hDprodB.lintegral_prod_left'
      |>.mono_measure (Measure.restrict_mono_set volume htime)).pow_const
        (1 / 2 : ℝ)
  have hballEq : B = vec3Ball z.1 r := by
    ext y
    change y ∈ euclideanBall z.1 r ↔ y ∈ vec3Ball z.1 r
    simpa [vec3EuclideanNorm, vecEuclideanNorm, vecNormSq, vecDot, pow_two]
      using (mem_euclideanBall_iff_vecEuclideanNorm_lt hr)
  have hEeq : E = (fun s => timeSliceBallEnergy z.1 r s
      (fun w => vec3EuclideanNorm (u w))) := by
    exact @gamma_le_gagliardo_hEeq_3 u z r hballEq
  have hEtop : essSup E (volume.restrict T) < ∞ := by
    have h := sws_timeSliceEnergyEssSup_lt_top hsol hr hsub
    rw [hEeq]
    simpa [T, timeSliceEnergyEssSup] using h
  have hA₀top : A₀ ≠ ∞ := by
    dsimp [A₀]
    exact ENNReal.rpow_ne_top_of_nonneg (by norm_num) (ne_of_lt hEtop)
  have hA₀bound : ∀ᵐ s ∂volume.restrict T, A s ≤ A₀ := by
    have hess := ENNReal.ae_le_essSup (μ := volume.restrict T) (fun s => E s)
    filter_upwards [hess] with s hs
    change E s ^ (1 / 2 : ℝ) ≤ A₀
    exact ENNReal.rpow_le_rpow hs (by norm_num)
  have hDprodBT : AEMeasurable (fun w : Vec3 × ℝ =>
      ENNReal.ofReal (spatialGradientSq u Du w))
      ((volume.restrict B).prod (volume.restrict T)) :=
    hDprodB.mono_measure (Measure.prod_mono le_rfl
      (Measure.restrict_mono_set volume htime))
  have hrect : B ×ˢ T = parabolicCylinder z.1 z.2 r := by
    rw [parabolicCylinder]
    simpa [T] using congrArg (fun S : Set Vec3 => S ×ˢ Ioc (z.2 - r ^ 2) z.2)
      hballEq
  have hGsq : ∀ s, G s ^ (2 : ℝ) =
      ∫⁻ y in B, ENNReal.ofReal (spatialGradientSq u Du (y, s)) := by
    intro s
    dsimp [G]
    rw [← ENNReal.rpow_mul]
    norm_num
  have hG₂ := @gamma_le_gagliardo_hG₂_2 u Du z r hDprodBT hrect hGsq
  have hV := @gamma_le_gagliardo_hV_4 z r
  have hgood := @gamma_le_gagliardo_hgood_3 Ω I q u Du p f hsol z r Ω' J hbox htime hdata
  have hpoint := @gamma_le_gagliardo_hpoint_4 u Du p z r hr Ω' hball hballEq hgood
  have hUprod3B : AEMeasurable (fun w : Vec3 × ℝ =>
      ENNReal.ofReal (vec3EuclideanNorm (u w)) ^ (3 : ℝ))
      ((volume.restrict B).prod (volume.restrict J)) :=
    hUprod3.mono_measure (Measure.prod_mono
      (Measure.restrict_mono_set volume hball) le_rfl)
  have hUprod3BT : AEMeasurable (fun w : Vec3 × ℝ =>
      ENNReal.ofReal (vec3EuclideanNorm (u w)) ^ (3 : ℝ))
      ((volume.restrict B).prod (volume.restrict T)) :=
    hUprod3B.mono_measure (Measure.prod_mono le_rfl
      (Measure.restrict_mono_set volume htime))
  have hUtime :
      (∫⁻ w in parabolicCylinder z.1 z.2 r,
        ENNReal.ofReal (vec3EuclideanNorm (u w)) ^ (3 : ℝ)) =
      ∫⁻ s in T, ∫⁻ y in B,
        ENNReal.ofReal (vec3EuclideanNorm (u (y, s))) ^ (3 : ℝ) := by
    rw [← hrect]
    exact prod_lintegral_swap_cyl hUprod3BT
  have htime' := time_interpolation_ball_l3 (A := A) (G := G)
    (K := K) (R := R) (A₀ := A₀) (G₂ := D) (V := V)
    hAmeas hGmeas hKtop hA₀top hA₀bound hG₂ hV
  have htimebound :
      (∫⁻ w in parabolicCylinder z.1 z.2 r,
        ENNReal.ofReal (vec3EuclideanNorm (u w)) ^ (3 : ℝ)) ≤
      K * A₀ ^ (3 / 2 : ℝ) * D ^ (3 / 4 : ℝ) * V ^ (1 / 4 : ℝ) +
        K * R * V * A₀ ^ (3 : ℝ) := by
    rw [hUtime]
    exact le_trans (lintegral_mono_ae hpoint) htime'
  have hEss := sws_timeSliceEnergyEssSup_eq_ofReal_alpha_sq hsol z hr hsub
  have hEssE : essSup E (volume.restrict T) =
      ENNReal.ofReal (r * alpha u z r ^ 2) := by
    rw [hEeq]
    simpa [T, timeSliceEnergyEssSup] using hEss
  have hDeq : D = ENNReal.ofReal (r * beta u Du z r ^ 2) := by
    dsimp [D]
    exact sws_lintegral_spatialGradientSq_eq_ofReal_beta_sq hsol z hr hsub
  have hA₀eq : A₀ = (ENNReal.ofReal (r * alpha u z r ^ 2)) ^
      (1 / 2 : ℝ) := by
    dsimp [A₀]
    rw [hEssE]
  have hα : 0 ≤ alpha u z r := by
    unfold alpha
    positivity
  have hβ : 0 ≤ beta u Du z r := by
    unfold beta
    positivity
  have hr2 : 0 ≤ r ^ (2 : ℝ) := Real.rpow_nonneg hr.le _
  have hr2_nat : 0 ≤ r ^ (2 : ℕ) := sq_nonneg _
  have hα2 : 0 ≤ alpha u z r ^ 2 := sq_nonneg _
  have hβ2 : 0 ≤ beta u Du z r ^ 2 := sq_nonneg _
  have hα32 : 0 ≤ alpha u z r ^ (3 / 2 : ℝ) := Real.rpow_nonneg hα _
  have hβ32 : 0 ≤ beta u Du z r ^ (3 / 2 : ℝ) := Real.rpow_nonneg hβ _
  have hα3 : 0 ≤ alpha u z r ^ (3 : ℕ) := pow_nonneg hα _
  have hαβ32 : 0 ≤ alpha u z r ^ (3 / 2 : ℝ) *
      beta u Du z r ^ (3 / 2 : ℝ) := mul_nonneg hα32 hβ32
  have hterm1_real_nonneg : 0 ≤ r ^ (2 : ℝ) *
      (alpha u z r ^ (3 / 2 : ℝ) * beta u Du z r ^ (3 / 2 : ℝ)) :=
    mul_nonneg hr2 hαβ32
  have hterm2_real_nonneg : 0 ≤ r ^ (2 : ℝ) * alpha u z r ^ (3 : ℕ) :=
    mul_nonneg hr2 hα3
  have hK0 : 0 ≤ K := by
    dsimp [K]
    positivity
  have hCterm1 : 0 ≤ C * (r ^ (2 : ℝ) *
      (alpha u z r ^ (3 / 2 : ℝ) * beta u Du z r ^ (3 / 2 : ℝ))) :=
    mul_nonneg hC0 hterm1_real_nonneg
  have hCterm2 : 0 ≤ C * (r ^ (2 : ℝ) * alpha u z r ^ (3 : ℕ)) :=
    mul_nonneg hC0 hterm2_real_nonneg
  have hterm1 := @gamma_le_gagliardo_hterm1_5 u Du z r hr hDeq hA₀eq hα hβ hr2_nat hα2 hβ2
  have hterm2 := @gamma_le_gagliardo_hterm2_6 u z r hr hA₀eq hα hr2_nat hα2
  have hterm2_nat : R * V * A₀ ^ (3 : ℝ) ≤
      ENNReal.ofReal (r ^ (2 : ℝ) * alpha u z r ^ (3 : ℕ)) := by
    apply le_trans hterm2
    exact (congrArg ENNReal.ofReal (congrArg (fun x : ℝ => r ^ (2 : ℝ) * x) (Real.rpow_natCast
      (alpha u z r) 3))).le
  have hH1 := @gamma_le_gagliardo_hH1_7 u Du z r hC0 hC₉0 hC₉1 hCof htimebound hα hβ hr2 hK0
    hCterm1 hCterm2 hterm1 hterm2_nat
  have hgamma := gamma_le_of_same_ball_interpolation hsol hr hsub hC₉0 hα hβ hH1
  simpa [C₉, gagliardoConstant, C, K, C₆] using hgamma
end CKN
