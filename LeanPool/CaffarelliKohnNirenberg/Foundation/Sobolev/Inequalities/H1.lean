/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Foundation.Sobolev.Inequalities.Smooth
public import LeanPool.CaffarelliKohnNirenberg.Foundation.Sobolev.H1.Basic
public import LeanPool.CaffarelliKohnNirenberg.Foundation.Sobolev.Mollify.LpApproximation
public import LeanPool.CaffarelliKohnNirenberg.Foundation.Sobolev.Mollify.Transport
public import LeanPool.CaffarelliKohnNirenberg.Foundation.Sobolev.WeakDerivative.Product
public import Mathlib.MeasureTheory.Function.ConvergenceInMeasure
public import Mathlib.MeasureTheory.Function.LpSpace.Complete
public import Mathlib.MeasureTheory.Function.LpSeminorm.SMul
public import Mathlib.MeasureTheory.SpecificCodomains.Pi
public import LeanPool.CaffarelliKohnNirenberg.Foundation.Sobolev.Cutoff.NormLeVecEuclidean

/-!
# Local Sobolev and interpolation inequalities for `H¹` representatives
The proof first multiplies the representative by the canonical compactly supported cutoff
inside the outer ball.  The product rule gives a global weak gradient for this zero extension;
global mollification then supplies smooth functions, and Fatou's lemma passes the estimate to the
representative.  This preserves the absolute constant from the smooth estimate.
-/

@[expose] public section

open MeasureTheory Set Filter
open scoped ENNReal Convolution
namespace CKN
noncomputable section
/-- The extended `Lᵖ` seminorm of a chosen weak gradient on a set. -/
def weakGradientLpNormOn (p : ℝ≥0∞) (s : Set (Vec 3)) (Du : Vec 3 → Vec 3) : ℝ≥0∞ :=
  eLpNorm Du p (volume.restrict s)
private theorem fderiv_norm_le_three_classicalGradient_h1
    {f : Vec 3 → ℝ} (x : Vec 3) :
    ‖fderiv ℝ f x‖ ≤ 3 * ‖classicalGradient f x‖ := by
  exact _root_.CKN.fderiv_norm_le_three_classicalGradient x

private theorem memLp_mul_cutoff_le
    {d : ℕ} {U : Set (Vec d)} (hU : MeasurableSet U)
    {p : ENNReal} {f : Vec d → ℝ} (hf : MemLp f p (volume.restrict U))
    {η : Vec d → ℝ} (hηMeas : Measurable η) (hηU : tsupport η ⊆ U)
    {c : ℝ} (hη : ∀ x, ‖η x‖ ≤ c) :
    MemLp (fun x => η x * f x) p volume := by
  have hmeas : AEStronglyMeasurable (fun x => η x * f x) (volume.restrict U) := by
    exact (hηMeas.aestronglyMeasurable.mul hf.aestronglyMeasurable)
  have hmul : MemLp (fun x => η x * f x) p (volume.restrict U) := by
    apply MemLp.of_le_mul hf hmeas
    on_goal 1 => filter_upwards [] with x
    on_goal 1 => rw [norm_mul]
    exact mul_le_mul_of_nonneg_right (hη x) (norm_nonneg (f x))
  have hglob : MemLp (U.indicator (fun x => η x * f x)) p volume :=
    (memLp_indicator_iff_restrict hU).2 hmul
  have heq : U.indicator (fun x => η x * f x) = (fun x => η x * f x) := by
    funext x
    by_cases hx : x ∈ U
    · simp only [Set.indicator_of_mem hx]
    · have hη0 : η x = 0 := image_eq_zero_of_notMem_tsupport (fun hxt => hx (hηU hxt))
      simp [hη0]
  rw [heq] at hglob
  exact hglob
private theorem fderiv_component_tsupport_subset
    {d : ℕ} {η : Vec d → ℝ} (i : Fin d) :
    tsupport (fun x => (fderiv ℝ η x) (basisVec i)) ⊆ tsupport η := by
  apply closure_minimal
  · intro x hx
    by_contra hxt
    have hηzero : η =ᶠ[nhds x] 0 :=
      (isClosed_tsupport (f := η)).isOpen_compl.eventually_mem hxt |>.mono
        (fun y hy => image_eq_zero_of_notMem_tsupport hy)
    have hderivzero := Filter.EventuallyEq.fderiv_eq (𝕜 := ℝ) hηzero
    have hzero : (fderiv ℝ η x) (basisVec i) = 0 := by
      rw [hderivzero]
      simp
    exact hx hzero
  · exact isClosed_tsupport (f := η)
theorem eLpNorm_pi_le_sum
    {f : Vec 3 → Vec 3} {μ : Measure (Vec 3)}
    (hf : AEStronglyMeasurable f μ) :
    eLpNorm f 2 μ ≤ ∑ i : Fin 3, eLpNorm (fun x => f x i) 2 μ := by
  have hpoint : ∀ x, ‖f x‖ ≤ ∑ i : Fin 3, ‖f x i‖ := by
    intro x
    rw [Pi.norm_def]
    have hsup : Finset.univ.sup (fun i => ‖f x i‖₊) ≤
        ∑ i : Fin 3, ‖f x i‖₊ := by
      apply Finset.sup_le
      intro i hi
      have hnonneg : ∀ j : Fin 3, j ∈ Finset.univ → 0 ≤ ‖f x j‖₊ := by
        intro j hj
        exact bot_le
      simpa only [Finset.sum_filter, Finset.mem_univ, ite_true] using
        (Finset.single_le_sum hnonneg (Finset.mem_univ i))
    exact_mod_cast hsup
  calc
    eLpNorm f 2 μ ≤ eLpNorm (fun x => ∑ i : Fin 3, ‖f x i‖) 2 μ := by
      apply eLpNorm_mono_ae hf
      filter_upwards [] with x
      rw [Real.norm_eq_abs, abs_of_nonneg (Finset.sum_nonneg
        (fun i _ => norm_nonneg (f x i)))]
      exact hpoint x
    _ = eLpNorm (∑ i : Fin 3, (fun x => ‖f x i‖)) 2 μ := by rfl
    _ ≤ ∑ i : Fin 3, eLpNorm (fun x => ‖f x i‖) 2 μ := by
      simpa using (eLpNorm_sum_le (p := (2 : ENNReal)) (s := Finset.univ)
        (f := fun i : Fin 3 => (fun x => ‖f x i‖)) (by norm_num))
    _ = ∑ i : Fin 3, eLpNorm (fun x => f x i) 2 μ := by
      congr 1
      funext i
      have hfi : AEStronglyMeasurable (fun x => f x i) μ := by
        simpa only [ContinuousLinearMap.proj_apply] using
          (ContinuousLinearMap.proj (R := ℝ) i).continuous.comp_aestronglyMeasurable hf
      rw [eLpNorm_norm _ hfi]
private theorem tendsto_sum_zero_of_fin_three
    {f : Fin 3 → ℕ → ℝ≥0∞}
    (hf : ∀ i, Tendsto (f i) atTop (nhds 0)) :
    Tendsto (fun n => ∑ i : Fin 3, f i n) atTop (nhds 0) := by
  simpa using tendsto_finsetSum Finset.univ (fun i hi => hf i)
private theorem eLpNorm_interpolate_three_h1
    {μ : Measure (Vec 3)} {u : Vec 3 → ℝ}
    (hu : AEStronglyMeasurable u μ) :
    eLpNorm u 3 μ ≤
      eLpNorm u 2 μ ^ (1 / 2 : ℝ) * eLpNorm u 6 μ ^ (1 / 2 : ℝ) := by
  let w : Vec 3 → ℝ := fun x => ‖u x‖ ^ (1 / 2 : ℝ)
  have hwm : AEStronglyMeasurable w μ := by
    simpa [w, Function.comp_def] using
      ((Real.continuous_rpow_const (q := (1 / 2 : ℝ)) (by norm_num)).aemeasurable.comp_aemeasurable
        hu.aemeasurable.norm).aestronglyMeasurable
  have : ENNReal.HolderTriple (4 : ℝ≥0∞) (12 : ℝ≥0∞) (3 : ℝ≥0∞) :=
    ⟨by
      have h : (4 : NNReal)⁻¹ + (12 : NNReal)⁻¹ = (3 : NNReal)⁻¹ := by norm_num
      change (((4 : NNReal) : ENNReal)⁻¹ + ((12 : NNReal) : ENNReal)⁻¹ =
        ((3 : NNReal) : ENNReal)⁻¹)
      rw [← ENNReal.coe_inv (show (4 : NNReal) ≠ 0 by norm_num),
        ← ENNReal.coe_inv (show (12 : NNReal) ≠ 0 by norm_num),
        ← ENNReal.coe_inv (show (3 : NNReal) ≠ 0 by norm_num)]
      exact_mod_cast h⟩
  have hholder : eLpNorm (fun x => w x * w x) 3 μ ≤
      eLpNorm w 4 μ * eLpNorm w 12 μ := by
    simpa [ENNReal.smul_def, one_mul] using
      (eLpNorm_le_eLpNorm_mul_eLpNorm_of_norm
        (μ := μ) (p := 4) (q := 12) (r := 3)
        (fun a b : ℝ => a * b) 1 continuous_mul hwm hwm
        (Filter.Eventually.of_forall (fun x => by
          simp [Real.norm_eq_abs, one_mul])))
  have hprod : (fun x => w x * w x) = fun x => ‖u x‖ := by
    funext x
    change ‖u x‖ ^ (1 / 2 : ℝ) * ‖u x‖ ^ (1 / 2 : ℝ) = ‖u x‖
    by_cases hzero : ‖u x‖ = 0
    · simp [hzero]
    · rw [← Real.rpow_add (lt_of_le_of_ne (norm_nonneg _) (Ne.symm hzero))]
      norm_num
  have hpow2 : eLpNorm w 4 μ = eLpNorm u 2 μ ^ (1 / 2 : ℝ) := by
    have hhalf : ENNReal.ofReal (1 / 2 : ℝ) = (2 : ℝ≥0∞)⁻¹ := by
      rw [show (1 / 2 : ℝ) = (2 : ℝ)⁻¹ by norm_num,
        ENNReal.ofReal_inv_of_pos (by norm_num), ENNReal.ofReal_ofNat]
    have h42 : (4 : ℝ≥0∞) * (2 : ℝ≥0∞)⁻¹ = 2 := by
      rw [show (4 : ℝ≥0∞) = 2 * 2 by norm_num, mul_assoc,
        ENNReal.mul_inv_cancel (by norm_num) (by norm_num), mul_one]
    have hraw := eLpNorm_norm_rpow u hu (by norm_num : (0 : ℝ) < 1 / 2)
      (p := (4 : ℝ≥0∞))
    rw [hhalf, h42] at hraw
    simpa [w] using hraw
  have hpow6 : eLpNorm w 12 μ = eLpNorm u 6 μ ^ (1 / 2 : ℝ) := by
    have hhalf : ENNReal.ofReal (1 / 2 : ℝ) = (2 : ℝ≥0∞)⁻¹ := by
      rw [show (1 / 2 : ℝ) = (2 : ℝ)⁻¹ by norm_num,
        ENNReal.ofReal_inv_of_pos (by norm_num), ENNReal.ofReal_ofNat]
    have h122 : (12 : ℝ≥0∞) * (2 : ℝ≥0∞)⁻¹ = 6 := by
      rw [show (12 : ℝ≥0∞) = 6 * 2 by norm_num, mul_assoc,
        ENNReal.mul_inv_cancel (by norm_num) (by norm_num), mul_one]
    have hraw := eLpNorm_norm_rpow u hu (by norm_num : (0 : ℝ) < 1 / 2)
      (p := (12 : ℝ≥0∞))
    rw [hhalf, h122] at hraw
    simpa [w] using hraw
  rw [hprod, hpow2, hpow6] at hholder
  rw [eLpNorm_norm u hu] at hholder
  exact hholder
private lemma h1_global_sobolev_bound_hGbound_1 :
    ∀ {x₀ : Vec (3 : ℕ)} {r : ℝ},
      (0 : ℝ) < r →
        ∀ (u : H1Function (euclideanBall x₀ ((2 : ℝ) * r))),
          let U : Set (Vec (3 : ℕ)) := euclideanBall x₀ ((2 : ℝ) * r);
          let η : Vec (3 : ℕ) → ℝ := canonicalBallCutoff x₀ r ((2 : ℝ) * r);
          let G : Vec (3 : ℕ) → Vec (3 : ℕ) := fun (x : Vec (3 : ℕ)) =>
            η x • u.grad (U := euclideanBall x₀ ((2 : ℝ) * r)) x +
              u.toFun (U := euclideanBall x₀ ((2 : ℝ) * r)) x • classicalGradient η x;
          MeasurableSet U →
            Measurable η →
              tsupport η ⊆ U →
                (∀ (x : Vec (3 : ℕ)), ‖η x‖ ≤ (1 : ℝ)) →
                  (∀ (x : Vec (3 : ℕ)), ‖classicalGradient η x‖ ≤ (32 : ℝ) / r) →
                    (∀ (i : Fin (3 : ℕ)),
                        Measurable (β := ℝ) fun (x : Vec (3 : ℕ)) => classicalGradient η x i) →
                      (∀ (i : Fin (3 : ℕ)),
                          (tsupport (α := ℝ) fun (x : Vec (3 : ℕ)) => classicalGradient η x i) ⊆
                            U) →
                        (∀ (i : Fin (3 : ℕ)) (x : Vec (3 : ℕ)),
                            ‖classicalGradient η x i‖ ≤ (32 : ℝ) / r) →
                          @eLpNorm _ _ _ _ MeasureSpace.toMeasurableSpace G (2 : ℝ≥0∞) volume ≤
                            weakGradientLpNormOn (2 : ℝ≥0∞) U
                                (u.grad (U := euclideanBall x₀ ((2 : ℝ) * r))) +
                              (↑((32 : ℝ) / r).toNNReal : ℝ≥0∞) *
                                lpNormOn (2 : ℝ≥0∞) U
                                  (u.toFun (U := euclideanBall x₀ ((2 : ℝ) * r)))
    := by
  intro x₀ r hr u U η G hUmeas hηMeas hηU hηBound hgradη hgradηMeas hgradηSupport hgradηBound
  let A : Vec 3 → Vec 3 := fun x => η x • u.grad x
  let B : Vec 3 → Vec 3 := fun x => u.toFun x • classicalGradient η x
  have hA_i (i : Fin 3) : MemLp (fun x => A x i) 2 volume := by
    simpa [A, Pi.smul_apply, smul_eq_mul] using
      (memLp_mul_cutoff_le hUmeas (u.grad_memL2 i) hηMeas hηU hηBound)
  have hB_i (i : Fin 3) : MemLp (fun x => B x i) 2 volume := by
    simpa [B, Pi.smul_apply, smul_eq_mul, mul_comm] using
      (memLp_mul_cutoff_le hUmeas u.memL2 (hgradηMeas i) (hgradηSupport i)
        (hgradηBound i))
  have hA : MemLp A 2 volume := (memLp_pi_iff).2 hA_i
  have hB : MemLp B 2 volume := (memLp_pi_iff).2 hB_i
  have hA_bound : eLpNorm A 2 volume ≤ eLpNorm (U.indicator u.grad) 2 volume := by
    apply eLpNorm_mono_ae hA.aestronglyMeasurable
    filter_upwards [] with x
    by_cases hx : x ∈ U
    · simp only [Set.indicator_of_mem hx]
      rw [norm_smul]
      simpa only [one_mul] using
        (mul_le_mul_of_nonneg_right (hηBound x) (norm_nonneg (u.grad x)))
    · have hη0 : η x = 0 := image_eq_zero_of_notMem_tsupport (fun hxt => hx (hηU hxt))
      simp [A, hη0]
  have hB_bound : eLpNorm B 2 volume ≤
      (Real.toNNReal (32 / r) : ℝ≥0∞) • eLpNorm (U.indicator u.toFun) 2 volume := by
    refine eLpNorm_le_nnreal_smul_eLpNorm_of_ae_le_mul' hB.aestronglyMeasurable ?_ 2
    filter_upwards [] with x
    by_cases hx : x ∈ U
    · simp only [Set.indicator_of_mem hx]
      simp only [enorm_eq_nnnorm]
      rw [← ENNReal.coe_mul]
      have hpoint : ‖B x‖₊ ≤
        Real.toNNReal (32 / r) * ‖u.toFun x‖₊ := by
        rw [nnnorm_smul]
        have hgradη' : ‖classicalGradient η x‖₊ ≤ Real.toNNReal (32 / r) := by
          rw [← NNReal.coe_le_coe]
          have hscale : (Real.toNNReal (32 / r) : ℝ) = 32 / r := by
            exact Real.coe_toNNReal (32 / r) (by positivity)
          simpa [hscale] using hgradη x
        calc
          ‖u.toFun x‖₊ * ‖classicalGradient η x‖₊ ≤
              ‖u.toFun x‖₊ * Real.toNNReal (32 / r) :=
            mul_le_mul_of_nonneg_left hgradη' bot_le
          _ = Real.toNNReal (32 / r) * ‖u.toFun x‖₊ := by ac_rfl
      exact_mod_cast hpoint
    · have hη0 : η x = 0 := image_eq_zero_of_notMem_tsupport (fun hxt => hx (hηU hxt))
      have hgradη0 : classicalGradient η x = 0 := by
        funext i
        rw [classicalGradient_apply, fderiv_of_notMem_tsupport ℝ
          (fun hxt => hx (hηU hxt))]
        simp
      simp [B, hgradη0, hx]
  have houterIndicatorG : eLpNorm (U.indicator u.grad) 2 volume =
      weakGradientLpNormOn 2 U u.grad := by
    rw [eLpNorm_indicator_eq_eLpNorm_restrict hUmeas]
    rfl
  have houterIndicatorU : eLpNorm (U.indicator u.toFun) 2 volume = lpNormOn 2 U u.toFun := by
    rw [eLpNorm_indicator_eq_eLpNorm_restrict hUmeas]
    rfl
  rw [show G = A + B by rfl]
  calc
    eLpNorm (A + B) 2 volume ≤ eLpNorm A 2 volume + eLpNorm B 2 volume :=
      eLpNorm_add_le (by norm_num)
    _ ≤ eLpNorm (U.indicator u.grad) 2 volume +
        (Real.toNNReal (32 / r) : ℝ≥0∞) • eLpNorm (U.indicator u.toFun) 2 volume :=
      add_le_add hA_bound hB_bound
    _ = weakGradientLpNormOn 2 U u.grad +
        (Real.toNNReal (32 / r) : ℝ≥0∞) * lpNormOn 2 U u.toFun := by
      rw [houterIndicatorG, houterIndicatorU]
      simp [smul_eq_mul]

private lemma h1_global_sobolev_bound_hDmemVec_2 :
    ∀ {x₀ : Vec (3 : ℕ)} {r : ℝ} (u : H1Function (euclideanBall x₀ ((2 : ℝ) * r))),
      let η : Vec (3 : ℕ) → ℝ := canonicalBallCutoff x₀ r ((2 : ℝ) * r);
      let v : Vec (3 : ℕ) → ℝ := fun (x : Vec (3 : ℕ)) =>
        η x * u.toFun (U := euclideanBall x₀ ((2 : ℝ) * r)) x;
      let G : Vec (3 : ℕ) → Vec (3 : ℕ) := fun (x : Vec (3 : ℕ)) =>
        η x • u.grad (U := euclideanBall x₀ ((2 : ℝ) * r)) x +
          u.toFun (U := euclideanBall x₀ ((2 : ℝ) * r)) x • classicalGradient η x;
      MemLp (m0 := MeasureSpace.toMeasurableSpace) G (2 : ℝ≥0∞) volume →
        let ε : ℕ → ℝ := fun (n : ℕ) => (1 : ℝ) / ((↑n : ℝ) + (1 : ℝ));
        ∀ (hεpos : ∀ (n : ℕ), (0 : ℝ) < ε n),
          (∀ (i : Fin (3 : ℕ)),
              Tendsto
                (fun (n : ℕ) =>
                  @eLpNorm _ ℝ _ _ MeasureSpace.toMeasurableSpace
                    (fun (x : Vec (3 : ℕ)) =>
                      mollify (fun (x : Vec (3 : ℕ)) => G x i) (ε n) (hεpos n) x - G x i)
                    (2 : ℝ≥0∞) volume)
                atTop (nhds (0 : ℝ≥0∞))) →
            let D : ℕ → Vec (3 : ℕ) → Vec (3 : ℕ) := fun (n : ℕ) (x : Vec (3 : ℕ)) =>
              classicalGradient (mollify v (ε n) (hεpos n)) x;
            (∀ (n : ℕ) (i : Fin (3 : ℕ)),
                Eq (α := Vec (3 : ℕ) → ℝ) (fun (x : Vec (3 : ℕ)) => D n x i)
                  (mollify (fun (y : Vec (3 : ℕ)) => G y i) (ε n) (hεpos n))) →
              (∀ (n : ℕ), MemLp (m0 := MeasureSpace.toMeasurableSpace) (D n) (2 : ℝ≥0∞) volume) →
                Tendsto
                  (fun (n : ℕ) =>
                    @eLpNorm _ _ _ _ MeasureSpace.toMeasurableSpace (D n - G) (2 : ℝ≥0∞) volume)
                  atTop (nhds (0 : ℝ≥0∞))
    := by
  intro x₀ r u η v G hG ε hεpos hGApprox D hD_i hDmemVec
  have hle : ∀ n, eLpNorm (D n - G) 2 volume ≤
      ∑ i : Fin 3, eLpNorm (fun x => mollify (fun y => G y i)
        (ε n) (hεpos n) x - G x i) 2 volume := by
    intro n
    have hmeas : AEStronglyMeasurable (D n - G) volume :=
      (hDmemVec n).sub hG |>.aestronglyMeasurable
    calc
      eLpNorm (D n - G) 2 volume ≤
          ∑ i : Fin 3, eLpNorm (fun x => (D n - G) x i) 2 volume :=
        eLpNorm_pi_le_sum hmeas
      _ = _ := by
        congr 1
        funext i
        apply eLpNorm_congr_ae
        filter_upwards [] with x
        simp only [Pi.sub_apply]
        rw [show D n x i = mollify (fun y => G y i) (ε n) (hεpos n) x by
          exact congrFun (hD_i n i) x]
  have hsum : Tendsto (fun n => ∑ i : Fin 3, eLpNorm (fun x => mollify
      (fun y => G y i) (ε n) (hεpos n) x - G x i) 2 volume) atTop (nhds 0) := by
    apply tendsto_sum_zero_of_fin_three
    intro i
    exact hGApprox i
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hsum
    (Eventually.of_forall fun _ => zero_le) (Eventually.of_forall hle)

private lemma h1_global_sobolev_bound_hvBound_3 :
    ∀ {x₀ : Vec (3 : ℕ)} {r : ℝ} (u : H1Function (euclideanBall x₀ ((2 : ℝ) * r))),
      let U : Set (Vec (3 : ℕ)) := euclideanBall x₀ ((2 : ℝ) * r);
      let η : Vec (3 : ℕ) → ℝ := canonicalBallCutoff x₀ r ((2 : ℝ) * r);
      let v : Vec (3 : ℕ) → ℝ := fun (x : Vec (3 : ℕ)) =>
        η x * u.toFun (U := euclideanBall x₀ ((2 : ℝ) * r)) x;
      MeasurableSet U →
        tsupport η ⊆ U →
          (∀ (x : Vec (3 : ℕ)), ‖η x‖ ≤ (1 : ℝ)) →
            MemLp (m0 := MeasureSpace.toMeasurableSpace) v (2 : ℝ≥0∞) volume →
              @eLpNorm _ _ _ _ MeasureSpace.toMeasurableSpace v (2 : ℝ≥0∞) volume ≤
                lpNormOn (2 : ℝ≥0∞) U (u.toFun (U := euclideanBall x₀ ((2 : ℝ) * r)))
    := by
  intro x₀ r u U η v hUmeas hηU hηBound hv
  calc
    eLpNorm v 2 volume ≤ eLpNorm (U.indicator u.toFun) 2 volume := by
      apply eLpNorm_mono_ae hv.aestronglyMeasurable
      filter_upwards [] with x
      by_cases hx : x ∈ U
      · simp only [Set.indicator_of_mem hx]
        rw [norm_mul]
        simpa only [one_mul] using
          (mul_le_mul_of_nonneg_right (hηBound x) (norm_nonneg (u.toFun x)))
      · have hη0 : η x = 0 := image_eq_zero_of_notMem_tsupport
          (fun hxt => hx (hηU hxt))
        simp [v, hη0]
    _ = lpNormOn 2 U u.toFun := by
      rw [eLpNorm_indicator_eq_eLpNorm_restrict hUmeas]
      rfl

private lemma h1_global_sobolev_bound_hboundEventually_4 :
    ∀ {x₀ : Vec (3 : ℕ)} {r : ℝ} (u : H1Function (euclideanBall x₀ ((2 : ℝ) * r))),
      let U : Set (Vec (3 : ℕ)) := euclideanBall x₀ ((2 : ℝ) * r);
      let inner : Set (Vec (3 : ℕ)) := euclideanBall x₀ r;
      let η : Vec (3 : ℕ) → ℝ := canonicalBallCutoff x₀ r ((2 : ℝ) * r);
      let v : Vec (3 : ℕ) → ℝ := fun (x : Vec (3 : ℕ)) =>
        η x * u.toFun (U := euclideanBall x₀ ((2 : ℝ) * r)) x;
      let G : Vec (3 : ℕ) → Vec (3 : ℕ) := fun (x : Vec (3 : ℕ)) =>
        η x • u.grad (U := euclideanBall x₀ ((2 : ℝ) * r)) x +
          u.toFun (U := euclideanBall x₀ ((2 : ℝ) * r)) x • classicalGradient η x;
      HasCompactSupport v →
        MemLp (m0 := MeasureSpace.toMeasurableSpace) v (2 : ℝ≥0∞) volume →
          let ε : ℕ → ℝ := fun (n : ℕ) => (1 : ℝ) / ((↑n : ℝ) + (1 : ℝ));
          ∀ (hεpos : ∀ (n : ℕ), (0 : ℝ) < ε n),
            let D : ℕ → Vec (3 : ℕ) → Vec (3 : ℕ) := fun (n : ℕ) (x : Vec (3 : ℕ)) =>
              classicalGradient (mollify v (ε n) (hεpos n)) x;
            Tendsto
                (fun (n : ℕ) =>
                  @eLpNorm _ _ _ _ MeasureSpace.toMeasurableSpace (D n - G) (2 : ℝ≥0∞) volume)
                atTop (nhds (0 : ℝ≥0∞)) →
              ∀ (ns : ℕ → ℕ),
                StrictMono ns →
                  let A : ℝ≥0∞ :=
                    weakGradientLpNormOn (2 : ℝ≥0∞) U
                        (u.grad (U := euclideanBall x₀ ((2 : ℝ) * r))) +
                      (↑((32 : ℝ) / r).toNNReal : ℝ≥0∞) *
                        lpNormOn (2 : ℝ≥0∞) U (u.toFun (U := euclideanBall x₀ ((2 : ℝ) * r)));
                  (∀ (n : ℕ),
                      @eLpNorm _ _ _ _ MeasureSpace.toMeasurableSpace (D n) (2 : ℝ≥0∞) volume ≤
                        A +
                          @eLpNorm _ _ _ _ MeasureSpace.toMeasurableSpace (D n - G) (2 : ℝ≥0∞)
                            volume) →
                    ∀ (δ : ℝ≥0∞),
                      δ ≠ ∞ →
                        (0 : ℝ≥0∞) < δ →
                          ∀ᶠ (k : ℕ) in atTop,
                            @eLpNorm _ _ _ _ MeasureSpace.toMeasurableSpace
                                (mollify v (ε (ns k)) (hεpos (ns k))) (6 : ℝ≥0∞)
                                (Measure.restrict volume inner) ≤
                              localSobolevConstant * (A + δ)
    := by
  intro x₀ r u U inner η v G hvSupport hv ε hεpos D hDerr ns hns_mono A hDnBound δ hδtop hδpos
  have hgradSmall : ∀ᶠ k in atTop, eLpNorm (D (ns k) - G) 2 volume ≤ δ :=
    (ENNReal.tendsto_nhds_zero.1 (hDerr.comp (hns_mono.tendsto_atTop)) δ hδpos)
  filter_upwards [hgradSmall] with k hgrad
  let m : Vec 3 → ℝ := mollify v (ε (ns k)) (hεpos (ns k))
  have hm : ContDiff ℝ 1 m := by
    exact mollify_contDiff (hεpos (ns k))
      (hv.locallyIntegrable (by norm_num)) (n := 1)
  have hmSupport : HasCompactSupport m := by
    change HasCompactSupport
      (mollifier (ε (ns k)) (hεpos (ns k)) ⋆[
        ContinuousLinearMap.lsmul ℝ ℝ, volume] v)
    exact (mollifier_hasCompactSupport (hεpos (ns k))).convolution
      (ContinuousLinearMap.lsmul ℝ ℝ) hvSupport
  have hglobal : eLpNorm m 6 volume ≤
      (SNormLESNormFDerivOfEqConst (E := Vec 3) ℝ (volume : Measure (Vec 3))
        (2 : ℝ) : ℝ≥0∞) * eLpNorm (fderiv ℝ m) 2 volume := by
    simpa using
      (MeasureTheory.eLpNorm_le_eLpNorm_fderiv_of_eq
        (volume : Measure (Vec 3)) hm hmSupport
        (by norm_num : (1 : NNReal) ≤ 2)
        (by norm_num : 0 < Module.finrank ℝ (Vec 3))
        (by norm_num : ((6 : NNReal) : ℝ)⁻¹ =
          ((2 : NNReal) : ℝ)⁻¹ - ((Module.finrank ℝ (Vec 3) : ℝ)⁻¹)))
  have hderivBound : eLpNorm (fderiv ℝ m) 2 volume ≤
      (3 : NNReal) • eLpNorm (D (ns k)) 2 volume := by
    refine eLpNorm_le_nnreal_smul_eLpNorm_of_ae_le_mul'
      (hm.continuous_fderiv (by norm_num)).aestronglyMeasurable ?_ 2
    exact Filter.Eventually.of_forall (fun x => by
      simp only [enorm_eq_nnnorm]
      rw [← ENNReal.coe_mul]
      have hpoint : ‖fderiv ℝ m x‖₊ ≤
          (3 : NNReal) * ‖D (ns k) x‖₊ := by
        exact_mod_cast fderiv_norm_le_three_classicalGradient_h1 x
      exact_mod_cast hpoint)
  change eLpNorm m 6 (volume.restrict inner) ≤ _
  change eLpNorm (mollify v (ε (ns k)) (hεpos (ns k))) 6
      (volume.restrict inner) ≤ _
  calc
    eLpNorm m 6 (volume.restrict inner) ≤ eLpNorm m 6 volume :=
      eLpNorm_mono_measure _ Measure.restrict_le_self
    _ ≤ (SNormLESNormFDerivOfEqConst (E := Vec 3) ℝ
        (volume : Measure (Vec 3)) (2 : ℝ) : ℝ≥0∞) *
        eLpNorm (fderiv ℝ m) 2 volume := hglobal
    _ ≤ (SNormLESNormFDerivOfEqConst (E := Vec 3) ℝ
        (volume : Measure (Vec 3)) (2 : ℝ) : ℝ≥0∞) *
        ((3 : NNReal) • eLpNorm (D (ns k)) 2 volume) := by
      gcongr
    _ = localSobolevConstant * eLpNorm (D (ns k)) 2 volume := by
      rw [localSobolevConstant]
      simp [ENNReal.smul_def, smul_eq_mul]
      ring
    _ ≤ localSobolevConstant * (A + δ) := by
      gcongr
      exact (hDnBound (ns k)).trans (add_le_add_right hgrad A)

private lemma h1_global_sobolev_bound_hfinal_5 :
    ∀ {x₀ : Vec (3 : ℕ)} {r : ℝ} (u : H1Function (euclideanBall x₀ ((2 : ℝ) * r))),
      let U : Set (Vec (3 : ℕ)) := euclideanBall x₀ ((2 : ℝ) * r);
      let inner : Set (Vec (3 : ℕ)) := euclideanBall x₀ r;
      let η : Vec (3 : ℕ) → ℝ := canonicalBallCutoff x₀ r ((2 : ℝ) * r);
      let v : Vec (3 : ℕ) → ℝ := fun (x : Vec (3 : ℕ)) =>
        η x * u.toFun (U := euclideanBall x₀ ((2 : ℝ) * r)) x;
      let ε : ℕ → ℝ := fun (n : ℕ) => (1 : ℝ) / ((↑n : ℝ) + (1 : ℝ));
      ∀ (hεpos : ∀ (n : ℕ), (0 : ℝ) < ε n) (ns : ℕ → ℕ),
        lpNormOn (6 : ℝ≥0∞) inner (u.toFun (U := euclideanBall x₀ ((2 : ℝ) * r))) ≤
            liminf
              (fun (k : ℕ) =>
                @eLpNorm _ _ _ _ MeasureSpace.toMeasurableSpace
                  (mollify v (ε (ns k)) (hεpos (ns k))) (6 : ℝ≥0∞) (Measure.restrict volume inner))
              atTop →
          let A : ℝ≥0∞ :=
            weakGradientLpNormOn (2 : ℝ≥0∞) U (u.grad (U := euclideanBall x₀ ((2 : ℝ) * r))) +
              (↑((32 : ℝ) / r).toNNReal : ℝ≥0∞) *
                lpNormOn (2 : ℝ≥0∞) U (u.toFun (U := euclideanBall x₀ ((2 : ℝ) * r)));
          (∀ (δ : ℝ≥0∞),
              δ ≠ ∞ →
                (0 : ℝ≥0∞) < δ →
                  ∀ᶠ (k : ℕ) in atTop,
                    @eLpNorm _ _ _ _ MeasureSpace.toMeasurableSpace
                        (mollify v (ε (ns k)) (hεpos (ns k))) (6 : ℝ≥0∞)
                        (Measure.restrict volume inner) ≤
                      localSobolevConstant * (A + δ)) →
            lpNormOn (6 : ℝ≥0∞) inner (u.toFun (U := euclideanBall x₀ ((2 : ℝ) * r))) ≤
              localSobolevConstant * A
    := by
  intro x₀ r u U inner η v ε hεpos ns hliminf A hboundEventually
  apply ENNReal.le_of_forall_pos_le_add
  intro δ hδ _
  have hCtop : localSobolevConstant ≠ ∞ := by
    unfold localSobolevConstant
    finiteness
  have hqtop : localSobolevConstant + 1 ≠ ∞ :=
    ENNReal.add_ne_top.mpr ⟨hCtop, ENNReal.one_ne_top⟩
  have hδ' : δ / (localSobolevConstant + 1) ≠ ∞ := by
    exact ENNReal.div_ne_top (by finiteness) (by positivity)
  have hδpos : 0 < δ / (localSobolevConstant + 1) := by
    exact ENNReal.div_pos (by exact_mod_cast hδ.ne') (by finiteness)
  have hlim := hboundEventually (δ / (localSobolevConstant + 1)) hδ' hδpos
  have hle : atTop.liminf (fun k => eLpNorm (mollify v (ε (ns k))
      (hεpos (ns k))) 6 (volume.restrict inner)) ≤
      localSobolevConstant * (A + δ / (localSobolevConstant + 1)) := by
    exact liminf_le_of_frequently_le' hlim.frequently
  refine hliminf.trans (hle.trans ?_)
  calc
    localSobolevConstant * (A + δ / (localSobolevConstant + 1)) =
        localSobolevConstant * A +
          localSobolevConstant * (δ / (localSobolevConstant + 1)) := by
      rw [mul_add]
    _ ≤ localSobolevConstant * A + δ := by
      apply add_le_add_right
      calc
        localSobolevConstant * (δ / (localSobolevConstant + 1)) ≤
            (localSobolevConstant + 1) * (δ / (localSobolevConstant + 1)) := by
          exact mul_le_mul_of_nonneg_right
            (le_add_of_nonneg_right (by norm_num)) (by positivity)
        _ = δ := by
          exact ENNReal.mul_div_cancel (by positivity) (by finiteness)

private theorem h1_global_sobolev_bound
    {x₀ : Vec 3} {r : ℝ} (hr : 0 < r)
    (u : H1Function (euclideanBall x₀ (2 * r))) :
    lpNormOn 6 (euclideanBall x₀ r) u.toFun ≤
      localSobolevConstant *
        (weakGradientLpNormOn 2 (euclideanBall x₀ (2 * r)) u.grad +
          (Real.toNNReal (32 / r) : ℝ≥0∞) *
            lpNormOn 2 (euclideanBall x₀ (2 * r)) u.toFun) := by
  let U : Set (Vec 3) := euclideanBall x₀ (2 * r)
  let inner : Set (Vec 3) := euclideanBall x₀ r
  let η : Vec 3 → ℝ := canonicalBallCutoff x₀ r (2 * r)
  let v : Vec 3 → ℝ := fun x => η x * u.toFun x
  let G : Vec 3 → Vec 3 := fun x => η x • u.grad x +
    u.toFun x • classicalGradient η x
  have hUopen : IsOpen U := by
    change IsOpen {x | euclideanSqDist x x₀ < (2 * r) ^ 2}
    exact isOpen_lt (contDiff_euclideanSqDist_left x₀).continuous continuous_const
  have hUmeas : MeasurableSet U := hUopen.measurableSet
  have hinnerMeas : MeasurableSet inner := by
    change MeasurableSet {x | euclideanSqDist x x₀ < r ^ 2}
    exact (isOpen_lt (contDiff_euclideanSqDist_left x₀).continuous continuous_const).measurableSet
  have hη : ContDiff ℝ (⊤ : ℕ∞) η := by
    exact canonicalBallCutoff_smooth x₀ (le_of_lt hr) (by linarith only [hr])
  have hηMeas : Measurable η := hη.continuous.measurable
  have hηSupport : HasCompactSupport η := by
    exact canonicalBallCutoff_hasCompactSupport (le_of_lt hr) (by linarith only [hr])
  have hηU : tsupport η ⊆ U := by
    exact canonicalBallCutoff_tsupport_subset_outer (le_of_lt hr) (by linarith only [hr])
  have hηBound : ∀ x, ‖η x‖ ≤ (1 : ℝ) := by
    intro x
    rw [Real.norm_eq_abs, abs_of_nonneg (canonicalBallCutoff_nonneg x₀ r (2 * r) x)]
    exact canonicalBallCutoff_le_one x₀ r (2 * r) x
  have hgradη : ∀ x, ‖classicalGradient η x‖ ≤ 32 / r := by
    intro x
    calc
      ‖classicalGradient η x‖ ≤
          vecEuclideanNorm (classicalGradient η x) := pi_norm_le_vecEuclideanNorm _
      _ ≤ 32 / ((2 * r) - r) := canonicalBallCutoff_gradient_bound
        (le_of_lt hr) (by linarith only [hr]) x
      _ = 32 / r := by ring_nf
  have hgradηMeas (i : Fin 3) :
      Measurable (fun x => (classicalGradient η x) i) := by
    simpa only [classicalGradient_apply] using
      (hη.continuous_fderiv (by norm_num)).clm_apply continuous_const |>.measurable
  have hgradηSupport (i : Fin 3) :
      tsupport (fun x => (classicalGradient η x) i) ⊆ U := by
    exact (fderiv_component_tsupport_subset i).trans hηU
  have hgradηBound (i : Fin 3) :
      ∀ x, ‖(classicalGradient η x) i‖ ≤ 32 / r := by
    intro x
    exact (norm_le_pi_norm (classicalGradient η x) i).trans (hgradη x)
  have huLoc : LocallyIntegrableOn u.toFun U volume := by
    exact locallyIntegrableOn_of_locallyIntegrable_restrict
      (u.memL2.locallyIntegrable (by norm_num))
  have hgradLoc (i : Fin 3) :
      LocallyIntegrableOn (fun x => u.grad x i) U volume := by
    exact locallyIntegrableOn_of_locallyIntegrable_restrict
      ((u.grad_memL2 i).locallyIntegrable (by norm_num))
  have hweak : HasWeakGradientOn Set.univ v G := by
    exact HasWeakGradientOn.mul_smooth_zeroExtend hUopen huLoc hgradLoc u.hasWeakGradient
      hη hηSupport hηU
  have hvSupport : HasCompactSupport v := by
    exact hηSupport.mul_right (f' := u.toFun)
  have hv : MemLp v 2 volume := by
    exact memLp_mul_cutoff_le hUmeas u.memL2 hηMeas hηU hηBound
  have hG_i (i : Fin 3) : MemLp (fun x => G x i) 2 volume := by
    have hηg : MemLp (fun x => η x * u.grad x i) 2 volume :=
      memLp_mul_cutoff_le hUmeas (u.grad_memL2 i) hηMeas hηU hηBound
    have hηd : MemLp (fun x => (classicalGradient η x) i * u.toFun x) 2 volume :=
      memLp_mul_cutoff_le hUmeas u.memL2 (hgradηMeas i) (hgradηSupport i) (hgradηBound i)
    convert hηg.add hηd using 1
    · ext x
      simp [G, Pi.smul_apply, smul_eq_mul, classicalGradient_apply,
        mul_comm, Pi.add_apply]
  have hG : MemLp G 2 volume := (memLp_pi_iff).2 hG_i
  have hgOuter : MemLp u.grad 2 (volume.restrict U) := by
    apply (memLp_pi_iff).2
    intro i
    exact memLpOn_mono subset_rfl (u.grad_memL2 i)
  have huOuter : MemLp u.toFun 2 (volume.restrict U) := u.memL2
  have hGbound := @h1_global_sobolev_bound_hGbound_1 x₀ r hr u hUmeas hηMeas hηU hηBound hgradη
    hgradηMeas hgradηSupport hgradηBound
  let ε : ℕ → ℝ := fun n => 1 / ((n : ℝ) + 1)
  have hεpos : ∀ n, 0 < ε n := by
    intro n
    dsimp [ε]
    positivity
  have hε : Tendsto ε atTop (nhds 0) := by
    simpa [ε] using (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
  have hvApprox := tendsto_eLpNorm_sub_zero_mollify (p := (2 : ENNReal))
    (by norm_num) ENNReal.coe_ne_top hv hε hεpos
  have hGApprox (i : Fin 3) := tendsto_eLpNorm_sub_zero_mollify (p := (2 : ENNReal))
    (by norm_num) ENNReal.coe_ne_top (hG_i i) hε hεpos
  have hderiv (n : ℕ) (i : Fin 3) (x : Vec 3) :
      (fderiv ℝ (mollify v (ε n) (hεpos n)) x) (basisVec i) =
        mollify (fun y => G y i) (ε n) (hεpos n) x := by
    exact fderiv_mollify_eq_mollify_of_hasWeakPartialDerivOn isOpen_univ
      (hv.locallyIntegrable (by norm_num)) ((hG_i i).locallyIntegrable (by norm_num))
      (hweak i) (hεpos n) (by simp)
  let D : ℕ → Vec 3 → Vec 3 := fun n x => classicalGradient
    (mollify v (ε n) (hεpos n)) x
  have hD_i (n : ℕ) (i : Fin 3) :
      (fun x => D n x i) = mollify (fun y => G y i) (ε n) (hεpos n) := by
    funext x
    exact hderiv n i x
  have hDmem (n : ℕ) (i : Fin 3) : MemLp (fun x => D n x i) 2 volume := by
    rw [hD_i]
    have hconv := young_convolution_nonneg_integral_one_of_aemeasurable
      (p := (2 : ENNReal)) (by norm_num) ENNReal.coe_ne_top
      (mollifier_nonneg (hεpos n))
      ((mollifier_contDiff (hεpos n) (n := 0)).continuous.integrable_of_hasCompactSupport
        (mollifier_hasCompactSupport (hεpos n)))
      (mollifier_integral_one (hεpos n))
      (mollifier_contDiff (hεpos n) (n := 0)).continuous.measurable
      (hG_i i).aestronglyMeasurable.aemeasurable
    rw [memLp_iff]
    simpa only [mollify] using hconv.trans_lt (hG_i i)
  have hDmemVec (n : ℕ) : MemLp (D n) 2 volume := (memLp_pi_iff).2 (hDmem n)
  have hDerr := @h1_global_sobolev_bound_hDmemVec_2 x₀ r u hG hεpos hGApprox hD_i hDmemVec
  obtain ⟨ns, hns_mono, hns_ae⟩ :=
    (tendstoInMeasure_of_tendsto_eLpNorm (μ := (volume : Measure (Vec 3)))
      (p := (2 : ENNReal)) (by norm_num) hvApprox).exists_seq_tendsto_ae
  have hinner_v : eLpNorm v 6 (volume.restrict inner) =
      lpNormOn 6 inner u.toFun := by
    apply eLpNorm_congr_ae
    filter_upwards [ae_restrict_mem hinnerMeas] with x hx
    simp only [v, η]
    rw [canonicalBallCutoff_eq_one_on_inner (x₀ := x₀) (r := r) (R := 2 * r)
      (le_of_lt hr) (by linarith only [hr]) hx]
    simp
  have hliminf : lpNormOn 6 inner u.toFun ≤
      atTop.liminf (fun k => eLpNorm (mollify v (ε (ns k)) (hεpos (ns k)))
        6 (volume.restrict inner)) := by
    rw [← hinner_v]
    apply MeasureTheory.Lp.eLpNorm_lim_le_liminf_eLpNorm
    · intro k
      exact (mollify_contDiff (hεpos (ns k))
        (hv.locallyIntegrable (by norm_num)) (n := 0)).continuous.aestronglyMeasurable.restrict
    · exact hv.aestronglyMeasurable.restrict
    · rw [ae_restrict_iff' hinnerMeas]
      filter_upwards [hns_ae] with x hx hxin
      exact hx
  let A : ℝ≥0∞ := weakGradientLpNormOn 2 U u.grad +
    (Real.toNNReal (32 / r) : ℝ≥0∞) * lpNormOn 2 U u.toFun
  have hvBound := @h1_global_sobolev_bound_hvBound_3 x₀ r u hUmeas hηU hηBound hv
  have hDnBound (n : ℕ) :
      eLpNorm (D n) 2 volume ≤ A + eLpNorm (D n - G) 2 volume := by
    calc
      eLpNorm (D n) 2 volume = eLpNorm ((D n - G) + G) 2 volume := by
        congr 1
        funext x
        simp only [Pi.sub_apply, Pi.add_apply]
        abel
      _ ≤ eLpNorm (D n - G) 2 volume + eLpNorm G 2 volume := by
        exact eLpNorm_add_le (p := (2 : ENNReal)) (by norm_num)
      _ ≤ eLpNorm (D n - G) 2 volume + A := by
        have hGbound' : eLpNorm G 2 volume ≤ A := by
          simpa [A] using hGbound
        exact add_le_add_right hGbound' _
      _ = A + eLpNorm (D n - G) 2 volume := by ac_rfl
  have hboundEventually := @h1_global_sobolev_bound_hboundEventually_4 x₀ r u hvSupport hv hεpos
    hDerr ns hns_mono hDnBound
  have hfinal := @h1_global_sobolev_bound_hfinal_5 x₀ r u hεpos ns hliminf hboundEventually
  simpa [A, inner, U, weakGradientLpNormOn] using hfinal
/-- Local `L⁶` Sobolev control for an `H¹` representative on concentric balls. -/
theorem h1SobolevBall
    {x₀ : Vec 3} {r : ℝ} (hr : 0 < r)
    (u : H1Function (euclideanBall x₀ (2 * r))) :
    lpNormOn 6 (euclideanBall x₀ r) u.toFun ≤
      localSobolevConstant *
        (weakGradientLpNormOn 2 (euclideanBall x₀ (2 * r)) u.grad +
          (Real.toNNReal (32 / r) : ℝ≥0∞) *
            lpNormOn 2 (euclideanBall x₀ (2 * r)) u.toFun) := by
  exact h1_global_sobolev_bound hr u
/-- Local `L³` interpolation control for an `H¹` representative on concentric balls. -/
theorem h1InterpolationBall
    {x₀ : Vec 3} {r : ℝ} (hr : 0 < r)
    (u : H1Function (euclideanBall x₀ (2 * r))) :
    lpNormOn 3 (euclideanBall x₀ r) u.toFun ≤
      lpNormOn 2 (euclideanBall x₀ (2 * r)) u.toFun ^ (1 / 2 : ℝ) *
        (localSobolevConstant *
          (weakGradientLpNormOn 2 (euclideanBall x₀ (2 * r)) u.grad +
            (Real.toNNReal (32 / r) : ℝ≥0∞) *
              lpNormOn 2 (euclideanBall x₀ (2 * r)) u.toFun)) ^ (1 / 2 : ℝ) := by
  let inner := euclideanBall x₀ r
  let outer := euclideanBall x₀ (2 * r)
  have hinnerOuter : inner ⊆ outer := by
    intro x hx
    change euclideanSqDist x x₀ < (2 * r) ^ 2
    have hx' : euclideanSqDist x x₀ < r ^ 2 := hx
    have hsq : r ^ 2 < (2 * r) ^ 2 := by nlinarith only [hr]
    exact hx'.trans hsq
  have hinnerMeas : MeasurableSet inner := by
    change MeasurableSet {x | euclideanSqDist x x₀ < r ^ 2}
    exact (isOpen_lt (contDiff_euclideanSqDist_left x₀).continuous
      continuous_const).measurableSet
  have hinterp := eLpNorm_interpolate_three_h1
    (μ := volume.restrict inner) (u := u.toFun)
    (memLpOn_mono hinnerOuter u.memL2).aestronglyMeasurable
  have hmono : lpNormOn 2 inner u.toFun ≤ lpNormOn 2 outer u.toFun :=
    eLpNorm_mono_measure u.toFun (Measure.restrict_mono_set volume hinnerOuter)
  have hS1 := h1SobolevBall (x₀ := x₀) (r := r) hr u
  change eLpNorm u.toFun 6 (volume.restrict inner) ≤ _ at hS1
  change eLpNorm u.toFun 3 (volume.restrict inner) ≤ _
  calc
    eLpNorm u.toFun 3 (volume.restrict inner) ≤
        eLpNorm u.toFun 2 (volume.restrict inner) ^ (1 / 2 : ℝ) *
          eLpNorm u.toFun 6 (volume.restrict inner) ^ (1 / 2 : ℝ) := hinterp
    _ ≤ eLpNorm u.toFun 2 (volume.restrict outer) ^ (1 / 2 : ℝ) *
        (localSobolevConstant *
          (weakGradientLpNormOn 2 outer u.grad +
            (Real.toNNReal (32 / r) : ℝ≥0∞) * lpNormOn 2 outer u.toFun)) ^
          (1 / 2 : ℝ) := by
      gcongr
/-- Cubed local `L³` interpolation control for an `H¹` representative. -/
theorem h1InterpolationBallCubed
    {x₀ : Vec 3} {r : ℝ} (hr : 0 < r)
    (u : H1Function (euclideanBall x₀ (2 * r))) :
    lpNormOn 3 (euclideanBall x₀ r) u.toFun ^ (3 : ℕ) ≤
      localSobolevConstant ^ (3 / 2 : ℝ) *
        lpNormOn 2 (euclideanBall x₀ (2 * r)) u.toFun ^ (3 / 2 : ℝ) *
          (weakGradientLpNormOn 2 (euclideanBall x₀ (2 * r)) u.grad +
            (Real.toNNReal (32 / r) : ℝ≥0∞) *
              lpNormOn 2 (euclideanBall x₀ (2 * r)) u.toFun) ^ (3 / 2 : ℝ) := by
  have h := h1InterpolationBall (x₀ := x₀) (r := r) hr u
  let A := lpNormOn 2 (euclideanBall x₀ (2 * r)) u.toFun
  let D := weakGradientLpNormOn 2 (euclideanBall x₀ (2 * r)) u.grad +
    (Real.toNNReal (32 / r) : ℝ≥0∞) * A
  let C := localSobolevConstant
  have hbase : lpNormOn 3 (euclideanBall x₀ r) u.toFun ≤
      A ^ (1 / 2 : ℝ) * (C * D) ^ (1 / 2 : ℝ) := by
    simpa [A, C, D, mul_assoc, mul_left_comm, mul_comm] using h
  have hpow := ENNReal.rpow_le_rpow hbase (by norm_num : 0 ≤ (3 : ℝ))
  have hpow' : lpNormOn 3 (euclideanBall x₀ r) u.toFun ^ (3 : ℕ) ≤
      (A ^ (1 / 2 : ℝ) * (C * D) ^ (1 / 2 : ℝ)) ^ (3 : ℝ) := by
    simpa [ENNReal.rpow_natCast] using hpow
  calc
    lpNormOn 3 (euclideanBall x₀ r) u.toFun ^ (3 : ℕ) ≤
        (A ^ (1 / 2 : ℝ) * (C * D) ^ (1 / 2 : ℝ)) ^ (3 : ℝ) := hpow'
    _ = C ^ (3 / 2 : ℝ) * A ^ (3 / 2 : ℝ) * D ^ (3 / 2 : ℝ) := by
      rw [ENNReal.mul_rpow_of_nonneg _ _ (by norm_num : 0 ≤ (3 : ℝ)),
        ← ENNReal.rpow_mul, ENNReal.mul_rpow_of_nonneg _ _ (by norm_num : 0 ≤ (1 / 2 : ℝ)),
        ENNReal.mul_rpow_of_nonneg _ _ (by norm_num : 0 ≤ (3 : ℝ)),
        ← ENNReal.rpow_mul, ← ENNReal.rpow_mul]
      norm_num [mul_assoc, mul_left_comm, mul_comm]
    _ = _ := by rfl
/-- Time-integrated cubed `L³` interpolation control for `H¹` representatives. -/
theorem h1InterpolationCylinderL3
    {x₀ : Vec 3} {r t : ℝ} (hr : 0 < r) {u : ℝ → H1Function (euclideanBall x₀ (2 * r))} :
    ∫⁻ s in Set.Ioc (t - r ^ 2) t,
        lpNormOn 3 (euclideanBall x₀ r) (u s).toFun ^ (3 : ℕ) ≤
      ∫⁻ s in Set.Ioc (t - r ^ 2) t,
        localSobolevConstant ^ (3 / 2 : ℝ) *
          lpNormOn 2 (euclideanBall x₀ (2 * r)) (u s).toFun ^ (3 / 2 : ℝ) *
            (weakGradientLpNormOn 2 (euclideanBall x₀ (2 * r)) (u s).grad +
              (Real.toNNReal (32 / r) : ℝ≥0∞) *
                lpNormOn 2 (euclideanBall x₀ (2 * r)) (u s).toFun) ^ (3 / 2 : ℝ) := by
  refine lintegral_mono ?_
  intro s
  exact h1InterpolationBallCubed hr (u s)
end
end CKN
