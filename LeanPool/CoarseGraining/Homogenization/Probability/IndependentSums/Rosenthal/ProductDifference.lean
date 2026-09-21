/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

import LeanPool.CoarseGraining.Homogenization.Probability.IndependentSums.Rosenthal.Symmetrization
import Mathlib.Analysis.MeanInequalitiesPow

/-! # Product Difference -/

namespace Homogenization
namespace IndependentSums

open MeasureTheory ProbabilityTheory
open Set
open scoped Topology

noncomputable section

variable {Ω ι : Type*} [MeasurableSpace Ω]
variable {μ : Measure Ω}

/-- For a finite independent family, pairing the first and second coordinate
copies on the product probability space preserves independence across the
index set. -/
theorem iIndepFun_prodMk_comp_fst_comp_snd_prod
    [Fintype ι] [IsProbabilityMeasure μ]
    {X : ι → Ω → ℝ}
    (h_indep : iIndepFun X μ)
    (h_meas : ∀ i, Measurable (X i)) :
    iIndepFun (fun i => fun ω : Ω × Ω => (X i ω.1, X i ω.2)) (μ.prod μ) := by
  classical
  let XT : Ω → ι → ℝ := fun ω i => X i ω
  let P : Ω × Ω → ι → ℝ × ℝ := fun ω i => (X i ω.1, X i ω.2)
  let Q : Ω × Ω → (ι → ℝ) × (ι → ℝ) := fun ω => (fun i => X i ω.1, fun i => X i ω.2)
  have hXT_meas : Measurable XT := by
    exact measurable_pi_lambda _ h_meas
  have hXT_map : μ.map XT = Measure.pi (fun i => μ.map (X i)) := by
    simpa [XT] using
      (ProbabilityTheory.iIndepFun_iff_map_fun_eq_pi_map
        (μ := μ) (f := X) (hf := fun i => (h_meas i).aemeasurable)).1 h_indep
  have hQfst_meas : Measurable (fun ω : Ω × Ω => fun i => X i ω.1) := by
    exact measurable_pi_lambda _ fun i => (h_meas i).comp measurable_fst
  have hQsnd_meas : Measurable (fun ω : Ω × Ω => fun i => X i ω.2) := by
    exact measurable_pi_lambda _ fun i => (h_meas i).comp measurable_snd
  have hQ_map :
      (μ.prod μ).map Q =
        (Measure.pi (fun i => μ.map (X i))).prod
          (Measure.pi (fun i => μ.map (X i))) := by
    have hQ_indep :
        (fun ω : Ω × Ω => fun i => X i ω.1) ⟂ᵢ[μ.prod μ]
          (fun ω => fun i => X i ω.2) := by
      exact indepFun_comp_fst_comp_snd_prod
        (μ := μ) (X := XT) (Y := XT) hXT_meas.aemeasurable hXT_meas.aemeasurable
    have hQ_map' :=
      (ProbabilityTheory.indepFun_iff_map_prod_eq_prod_map_map
        (μ := μ.prod μ)
        (f := fun ω : Ω × Ω => fun i => X i ω.1)
        (g := fun ω : Ω × Ω => fun i => X i ω.2)
        hQfst_meas.aemeasurable hQsnd_meas.aemeasurable).1 hQ_indep
    have hfst_map :
        (μ.prod μ).map (fun ω : Ω × Ω => fun i => X i ω.1) = μ.map XT := by
      have hXTfst : AEMeasurable XT ((μ.prod μ).map Prod.fst) := by
        rw [measurePreserving_fst.map_eq]
        exact hXT_meas.aemeasurable
      calc
        (μ.prod μ).map (fun ω : Ω × Ω => XT ω.1)
            = Measure.map XT ((μ.prod μ).map Prod.fst) := by
                symm
                exact AEMeasurable.map_map_of_aemeasurable hXTfst measurable_fst.aemeasurable
        _ = μ.map XT := by rw [measurePreserving_fst.map_eq]
    have hsnd_map :
        (μ.prod μ).map (fun ω : Ω × Ω => fun i => X i ω.2) = μ.map XT := by
      have hXTsnd : AEMeasurable XT ((μ.prod μ).map Prod.snd) := by
        rw [measurePreserving_snd.map_eq]
        exact hXT_meas.aemeasurable
      calc
        (μ.prod μ).map (fun ω : Ω × Ω => XT ω.2)
            = Measure.map XT ((μ.prod μ).map Prod.snd) := by
                symm
                exact AEMeasurable.map_map_of_aemeasurable hXTsnd measurable_snd.aemeasurable
        _ = μ.map XT := by rw [measurePreserving_snd.map_eq]
    calc
      (μ.prod μ).map Q
          = ((μ.prod μ).map (fun ω : Ω × Ω => fun i => X i ω.1)).prod
              ((μ.prod μ).map (fun ω : Ω × Ω => fun i => X i ω.2)) := hQ_map'
      _ = (μ.map XT).prod (μ.map XT) := by rw [hfst_map, hsnd_map]
      _ = (Measure.pi (fun i => μ.map (X i))).prod
            (Measure.pi (fun i => μ.map (X i))) := by rw [hXT_map]
  have hP_meas : Measurable P := by
    exact measurable_pi_lambda _ fun i =>
      ((h_meas i).comp measurable_fst).prodMk ((h_meas i).comp measurable_snd)
  have hP_map :
      (μ.prod μ).map P = Measure.pi (fun i => (μ.map (X i)).prod (μ.map (X i))) := by
    let e : (ι → ℝ × ℝ) ≃ᵐ (ι → ℝ) × (ι → ℝ) :=
      MeasurableEquiv.arrowProdEquivProdArrow ℝ ℝ ι
    apply (MeasurableEquiv.map_measurableEquiv_injective e)
    calc
      Measure.map e ((μ.prod μ).map P)
          = (μ.prod μ).map Q := by
              rw [Measure.map_map e.measurable hP_meas]
              rfl
      _ = (Measure.pi (fun i => μ.map (X i))).prod
            (Measure.pi (fun i => μ.map (X i))) := hQ_map
      _ = Measure.map e (Measure.pi (fun i => (μ.map (X i)).prod (μ.map (X i)))) := by
            symm
            exact
              (measurePreserving_arrowProdEquivProdArrow ℝ ℝ ι
                (fun i => μ.map (X i)) (fun i => μ.map (X i))).map_eq
  have hpair_map :
      ∀ i, Measure.map (fun ω : Ω × Ω => (X i ω.1, X i ω.2)) (μ.prod μ) =
        (Measure.map (X i) μ).prod (Measure.map (X i) μ) := by
    intro i
    have hXi_indep :
        (fun ω : Ω × Ω => X i ω.1) ⟂ᵢ[μ.prod μ] (fun ω => X i ω.2) := by
      exact indepFun_comp_fst_comp_snd_prod
        (μ := μ) (X := X i) (Y := X i) (h_meas i).aemeasurable (h_meas i).aemeasurable
    have hpair_map' :=
      (ProbabilityTheory.indepFun_iff_map_prod_eq_prod_map_map
        (μ := μ.prod μ)
        (f := fun ω : Ω × Ω => X i ω.1)
        (g := fun ω : Ω × Ω => X i ω.2)
        ((h_meas i).aemeasurable.comp_fst)
        ((h_meas i).aemeasurable.comp_snd)).1 hXi_indep
    have hfst_i : Measure.map (fun ω : Ω × Ω => X i ω.1) (μ.prod μ) = Measure.map (X i) μ := by
      have hXi_fst : AEMeasurable (X i) ((μ.prod μ).map Prod.fst) := by
        rw [measurePreserving_fst.map_eq]
        exact (h_meas i).aemeasurable
      calc
        Measure.map (fun ω : Ω × Ω => X i ω.1) (μ.prod μ)
            = Measure.map (X i) ((μ.prod μ).map Prod.fst) := by
                symm
                exact AEMeasurable.map_map_of_aemeasurable hXi_fst measurable_fst.aemeasurable
        _ = Measure.map (X i) μ := by rw [measurePreserving_fst.map_eq]
    have hsnd_i : Measure.map (fun ω : Ω × Ω => X i ω.2) (μ.prod μ) = Measure.map (X i) μ := by
      have hXi_snd : AEMeasurable (X i) ((μ.prod μ).map Prod.snd) := by
        rw [measurePreserving_snd.map_eq]
        exact (h_meas i).aemeasurable
      calc
        Measure.map (fun ω : Ω × Ω => X i ω.2) (μ.prod μ)
            = Measure.map (X i) ((μ.prod μ).map Prod.snd) := by
                symm
                exact AEMeasurable.map_map_of_aemeasurable hXi_snd measurable_snd.aemeasurable
        _ = Measure.map (X i) μ := by rw [measurePreserving_snd.map_eq]
    rw [hfst_i, hsnd_i] at hpair_map'
    exact hpair_map'
  have hP_aemeas :
      ∀ i, AEMeasurable (fun ω : Ω × Ω => (X i ω.1, X i ω.2)) (μ.prod μ) := by
    intro i
    exact ((h_meas i).aemeasurable.comp_fst).prodMk ((h_meas i).aemeasurable.comp_snd)
  exact
    (ProbabilityTheory.iIndepFun_iff_map_fun_eq_pi_map
      (μ := μ.prod μ)
      (f := fun i => fun ω : Ω × Ω => (X i ω.1, X i ω.2))
      (hf := hP_aemeas)).2 <|
      hP_map.trans <| by
        congr
        funext i
        exact (hpair_map i).symm

/-- The symmetrized difference family on the product probability space is
independent across the index set. -/
theorem iIndepFun_sub_comp_fst_comp_snd_prod
    [Fintype ι] [IsProbabilityMeasure μ]
    {X : ι → Ω → ℝ}
    (h_indep : iIndepFun X μ)
    (h_meas : ∀ i, Measurable (X i)) :
    iIndepFun (fun i => fun ω : Ω × Ω => X i ω.1 - X i ω.2) (μ.prod μ) := by
  let g : ι → ℝ × ℝ → ℝ := fun _ z => z.1 - z.2
  have hg : ∀ i, Measurable (g i) := by
    intro i
    exact measurable_fst.sub measurable_snd
  simpa [g] using!
    (iIndepFun_prodMk_comp_fst_comp_snd_prod (μ := μ) (X := X) h_indep h_meas).comp g hg

/-- A first-minus-second coordinate difference is symmetric on the product
probability space. -/
theorem identDistrib_sub_comp_fst_comp_snd_prod_neg
    [IsProbabilityMeasure μ] {X : Ω → ℝ}
    (h_meas : Measurable X) :
    IdentDistrib
      (fun ω : Ω × Ω => X ω.1 - X ω.2)
      (fun ω : Ω × Ω => -(X ω.1 - X ω.2))
      (μ.prod μ) (μ.prod μ) := by
  let Y : Ω × Ω → ℝ := fun ω => X ω.1 - X ω.2
  have hY_meas : Measurable Y := by
    exact (h_meas.comp measurable_fst).sub (h_meas.comp measurable_snd)
  have hswap : IdentDistrib Y (fun ω : Ω × Ω => Y (Prod.swap ω)) (μ.prod μ) (μ.prod μ) := by
    refine
      { aemeasurable_fst := hY_meas.aemeasurable
        aemeasurable_snd := hY_meas.aemeasurable.comp_measurable measurable_swap
        map_eq := ?_ }
    have hYswap : AEMeasurable Y ((μ.prod μ).map Prod.swap) := by
      rw [Measure.prod_swap]
      exact hY_meas.aemeasurable
    calc
      Measure.map Y (μ.prod μ)
          = Measure.map Y ((μ.prod μ).map Prod.swap) := by rw [Measure.prod_swap]
      _ = Measure.map (fun ω : Ω × Ω => Y (Prod.swap ω)) (μ.prod μ) := by
            exact AEMeasurable.map_map_of_aemeasurable hYswap measurable_swap.aemeasurable
  have hswap_eq :
      (fun ω : Ω × Ω => Y (Prod.swap ω)) = fun ω : Ω × Ω => -Y ω := by
    funext ω
    simp [Y]
  refine
    { aemeasurable_fst := hY_meas.aemeasurable
      aemeasurable_snd := hY_meas.neg.aemeasurable
      map_eq := ?_ }
  calc
    Measure.map Y (μ.prod μ)
        = Measure.map (fun ω : Ω × Ω => Y (Prod.swap ω)) (μ.prod μ) := hswap.map_eq
    _ = Measure.map (fun ω : Ω × Ω => -Y ω) (μ.prod μ) := by rw [hswap_eq]
    _ = Measure.map (fun ω : Ω × Ω => -(X ω.1 - X ω.2)) (μ.prod μ) := by rfl

section

omit [MeasurableSpace Ω]

/-- Pointwise `L^p` control of the finite maximum of the symmetrized family by
the maxima of the two coordinate copies. -/
theorem sup'_abs_sub_pow_le
    {X : ι → Ω → ℝ} {s : Finset ι} (hs : s.Nonempty) {p : ℕ}
    (ω : Ω × Ω) :
    (s.sup' hs (fun i => |X i ω.1 - X i ω.2|)) ^ p ≤
      (2 ^ (p - 1) : ℝ) *
        ((s.sup' hs (fun i => |X i ω.1|)) ^ p + (s.sup' hs (fun i => |X i ω.2|)) ^ p) := by
  let A : ℝ := s.sup' hs (fun i => |X i ω.1|)
  let B : ℝ := s.sup' hs (fun i => |X i ω.2|)
  have hA_nonneg : 0 ≤ A := by
    have hnonneg : 0 ≤ |X hs.choose ω.1| := abs_nonneg _
    have hle : |X hs.choose ω.1| ≤ A := by
      exact Finset.le_sup' (f := fun i => |X i ω.1|) hs.choose_spec
    exact le_trans hnonneg hle
  have hB_nonneg : 0 ≤ B := by
    have hnonneg : 0 ≤ |X hs.choose ω.2| := abs_nonneg _
    have hle : |X hs.choose ω.2| ≤ B := by
      exact Finset.le_sup' (f := fun i => |X i ω.2|) hs.choose_spec
    exact le_trans hnonneg hle
  have hsup_nonneg : 0 ≤ s.sup' hs (fun i => |X i ω.1 - X i ω.2|) := by
    have hnonneg : 0 ≤ |X hs.choose ω.1 - X hs.choose ω.2| := abs_nonneg _
    have hle :
        |X hs.choose ω.1 - X hs.choose ω.2| ≤
          s.sup' hs (fun i => |X i ω.1 - X i ω.2|) := by
      exact Finset.le_sup' (f := fun i => |X i ω.1 - X i ω.2|) hs.choose_spec
    exact le_trans hnonneg hle
  have hsup :
      s.sup' hs (fun i => |X i ω.1 - X i ω.2|) ≤ A + B := by
    refine Finset.sup'_le hs _ ?_
    intro i hi
    have hAi : |X i ω.1| ≤ A := by
      exact Finset.le_sup' (f := fun i => |X i ω.1|) hi
    have hBi : |X i ω.2| ≤ B := by
      exact Finset.le_sup' (f := fun i => |X i ω.2|) hi
    calc
      |X i ω.1 - X i ω.2| ≤ |X i ω.1| + |X i ω.2| := by
        simpa [sub_eq_add_neg] using abs_add_le (X i ω.1) (-X i ω.2)
      _ ≤ A + B := add_le_add hAi hBi
  have hpow :
      (s.sup' hs (fun i => |X i ω.1 - X i ω.2|)) ^ p ≤ (A + B) ^ p := by
    exact pow_le_pow_left₀ hsup_nonneg hsup p
  have hadd :
      (A + B) ^ p ≤ (2 ^ (p - 1) : ℝ) * (A ^ p + B ^ p) := by
    exact add_pow_le hA_nonneg hB_nonneg p
  exact le_trans hpow (by simpa [A, B] using hadd)

/-- Real-exponent pointwise `L^p` control of the finite maximum of the
symmetrized family by the maxima of the two coordinate copies. -/
theorem sup'_abs_sub_rpow_le
    {X : ι → Ω → ℝ} {s : Finset ι} (hs : s.Nonempty) {p : ℝ}
    (hp : 1 ≤ p) (ω : Ω × Ω) :
    (s.sup' hs (fun i => |X i ω.1 - X i ω.2|)) ^ p ≤
      (2 : ℝ) ^ (p - 1) *
        ((s.sup' hs (fun i => |X i ω.1|)) ^ p + (s.sup' hs (fun i => |X i ω.2|)) ^ p) := by
  let A : ℝ := s.sup' hs (fun i => |X i ω.1|)
  let B : ℝ := s.sup' hs (fun i => |X i ω.2|)
  have hA_nonneg : 0 ≤ A := by
    have hnonneg : 0 ≤ |X hs.choose ω.1| := abs_nonneg _
    have hle : |X hs.choose ω.1| ≤ A := by
      exact Finset.le_sup' (f := fun i => |X i ω.1|) hs.choose_spec
    exact le_trans hnonneg hle
  have hB_nonneg : 0 ≤ B := by
    have hnonneg : 0 ≤ |X hs.choose ω.2| := abs_nonneg _
    have hle : |X hs.choose ω.2| ≤ B := by
      exact Finset.le_sup' (f := fun i => |X i ω.2|) hs.choose_spec
    exact le_trans hnonneg hle
  have hsup_nonneg : 0 ≤ s.sup' hs (fun i => |X i ω.1 - X i ω.2|) := by
    have hnonneg : 0 ≤ |X hs.choose ω.1 - X hs.choose ω.2| := abs_nonneg _
    have hle :
        |X hs.choose ω.1 - X hs.choose ω.2| ≤
          s.sup' hs (fun i => |X i ω.1 - X i ω.2|) := by
      exact Finset.le_sup' (f := fun i => |X i ω.1 - X i ω.2|) hs.choose_spec
    exact le_trans hnonneg hle
  have hsup :
      s.sup' hs (fun i => |X i ω.1 - X i ω.2|) ≤ A + B := by
    refine Finset.sup'_le hs _ ?_
    intro i hi
    have hAi : |X i ω.1| ≤ A := by
      exact Finset.le_sup' (f := fun i => |X i ω.1|) hi
    have hBi : |X i ω.2| ≤ B := by
      exact Finset.le_sup' (f := fun i => |X i ω.2|) hi
    calc
      |X i ω.1 - X i ω.2| ≤ |X i ω.1| + |X i ω.2| := by
        simpa [sub_eq_add_neg] using abs_add_le (X i ω.1) (-X i ω.2)
      _ ≤ A + B := add_le_add hAi hBi
  have hpow :
      (s.sup' hs (fun i => |X i ω.1 - X i ω.2|)) ^ p ≤ (A + B) ^ p := by
    exact Real.rpow_le_rpow hsup_nonneg hsup (by linarith)
  have hadd :
      (A + B) ^ p ≤ (2 : ℝ) ^ (p - 1) * (A ^ p + B ^ p) := by
    exact_mod_cast NNReal.rpow_add_le_mul_rpow_add_rpow ⟨A, hA_nonneg⟩ ⟨B, hB_nonneg⟩ hp
  exact le_trans hpow (by simpa [A, B] using hadd)

end

/-- Product-space `L^p` control of the finite maximum of the symmetrized family
by the original maximum. -/
theorem integral_sup'_abs_sub_pow_le_two_pow_mul_integral_sup'_abs_pow
    [IsProbabilityMeasure μ]
    {X : ι → Ω → ℝ} {s : Finset ι} (hs : s.Nonempty) {p : ℕ}
    (hp : 1 ≤ p)
    (h_meas : ∀ i, Measurable (X i))
    (hmax_int : Integrable (fun ω => (s.sup' hs (fun i => |X i ω|)) ^ p) μ) :
    ∫ ω : Ω × Ω, (s.sup' hs (fun i => |X i ω.1 - X i ω.2|)) ^ p ∂(μ.prod μ) ≤
      (2 : ℝ) ^ p * ∫ ω, (s.sup' hs (fun i => |X i ω|)) ^ p ∂μ := by
  let M : Ω → ℝ := fun ω => s.sup' hs (fun i => |X i ω|)
  let G : Ω × Ω → ℝ := fun ω => (2 ^ (p - 1) : ℝ) * (M ω.1 ^ p + M ω.2 ^ p)
  have hfst : Integrable (fun ω : Ω × Ω => M ω.1 ^ p) (μ.prod μ) := by
    simpa [M] using hmax_int.comp_fst μ
  have hsnd : Integrable (fun ω : Ω × Ω => M ω.2 ^ p) (μ.prod μ) := by
    simpa [M] using hmax_int.comp_snd μ
  have hG_int : Integrable G (μ.prod μ) := by
    simpa [G] using (hfst.add hsnd).const_mul ((2 ^ (p - 1) : ℕ) : ℝ)
  have hleft_meas :
      Measurable (fun ω : Ω × Ω => s.sup' hs (fun i => |X i ω.1 - X i ω.2|)) := by
    have hsup_meas :
        Measurable (s.sup' hs (fun i (ω : Ω × Ω) => |X i ω.1 - X i ω.2|)) := by
      refine Finset.measurable_sup' (hs := hs) (f := fun i (ω : Ω × Ω) => |X i ω.1 - X i ω.2|) ?_
      intro i hi
      exact
        continuous_abs.measurable.comp
          (((h_meas i).comp measurable_fst).sub ((h_meas i).comp measurable_snd))
    convert hsup_meas using 1
    ext ω
    simp
  have hleft_aesm :
      AEStronglyMeasurable
        (fun ω : Ω × Ω => (s.sup' hs (fun i => |X i ω.1 - X i ω.2|)) ^ p) (μ.prod μ) := by
    exact (hleft_meas.aemeasurable.pow_const p).aestronglyMeasurable
  have hleft_int :
      Integrable
        (fun ω : Ω × Ω => (s.sup' hs (fun i => |X i ω.1 - X i ω.2|)) ^ p) (μ.prod μ) := by
    refine hG_int.mono' hleft_aesm ?_
    filter_upwards with ω
    have hω := sup'_abs_sub_pow_le (X := X) (s := s) hs (p := p) ω
    have hbase_nonneg : 0 ≤ s.sup' hs (fun i => |X i ω.1 - X i ω.2|) := by
      have hnonneg : 0 ≤ |X hs.choose ω.1 - X hs.choose ω.2| := abs_nonneg _
      exact le_trans hnonneg (Finset.le_sup' (f := fun i => |X i ω.1 - X i ω.2|) hs.choose_spec)
    simpa [G, M, abs_of_nonneg hbase_nonneg] using hω
  have hpoint :
      ∀ᵐ ω : Ω × Ω ∂(μ.prod μ),
        (s.sup' hs (fun i => |X i ω.1 - X i ω.2|)) ^ p ≤ G ω :=
    Filter.Eventually.of_forall fun ω => by
      simpa [G, M] using sup'_abs_sub_pow_le (X := X) (s := s) hs (p := p) ω
  have hM_meas : Measurable M := by
    dsimp [M]
    convert
      (Finset.measurable_sup' (hs := hs) (f := fun i ω => |X i ω|) fun i _ =>
        continuous_abs.measurable.comp (h_meas i)) using 1
    ext ω
    simp
  have hid :
      IdentDistrib
        (fun ω : Ω × Ω => M ω.1 ^ p)
        (fun ω : Ω × Ω => M ω.2 ^ p)
        (μ.prod μ) (μ.prod μ) := by
    simpa [M, Function.comp_def] using
      (identDistrib_comp_fst_comp_snd_prod (μ := μ) (X := M) hM_meas.aemeasurable).comp
        (measurable_id.pow_const p)
  have hfst_eq :
      ∫ ω : Ω × Ω, M ω.1 ^ p ∂(μ.prod μ) = ∫ ω, M ω ^ p ∂μ := by
    simpa [M] using
      (integral_fun_fst (μ := μ) (ν := μ) (f := fun ω : Ω => M ω ^ p))
  have hsnd_eq :
      ∫ ω : Ω × Ω, M ω.2 ^ p ∂(μ.prod μ) = ∫ ω : Ω × Ω, M ω.1 ^ p ∂(μ.prod μ) := by
    simpa using hid.integral_eq.symm
  have hpow_two : (2 : ℝ) ^ (p - 1) * 2 = (2 : ℝ) ^ p := by
    rcases Nat.exists_eq_add_of_le hp with ⟨n, rfl⟩
    simpa [Nat.add_comm, mul_comm] using (pow_succ' (2 : ℝ) n).symm
  calc
    ∫ ω : Ω × Ω, (s.sup' hs (fun i => |X i ω.1 - X i ω.2|)) ^ p ∂(μ.prod μ)
        ≤ ∫ ω : Ω × Ω, G ω ∂(μ.prod μ) := by
            exact integral_mono_ae hleft_int hG_int hpoint
    _ = (2 ^ (p - 1) : ℝ) *
          (∫ ω : Ω × Ω, M ω.1 ^ p ∂(μ.prod μ) +
            ∫ ω : Ω × Ω, M ω.2 ^ p ∂(μ.prod μ)) := by
          rw [show (∫ ω : Ω × Ω, G ω ∂(μ.prod μ)) =
            ∫ ω : Ω × Ω, (2 ^ (p - 1) : ℝ) * (M ω.1 ^ p + M ω.2 ^ p) ∂(μ.prod μ) by rfl]
          rw [integral_const_mul]
          congr 1
          exact integral_add hfst hsnd
    _ = (2 ^ (p - 1) : ℝ) * (2 * ∫ ω, M ω ^ p ∂μ) := by
          rw [hsnd_eq, two_mul, hfst_eq]
    _ = (2 : ℝ) ^ p * ∫ ω, M ω ^ p ∂μ := by
          calc
            (2 ^ (p - 1) : ℝ) * (2 * ∫ ω, M ω ^ p ∂μ)
                = (((2 : ℝ) ^ (p - 1)) * 2) * ∫ ω, M ω ^ p ∂μ := by ring_nf
            _ = (2 : ℝ) ^ p * ∫ ω, M ω ^ p ∂μ := by rw [hpow_two]
    _ = (2 : ℝ) ^ p * ∫ ω, (s.sup' hs (fun i => |X i ω|)) ^ p ∂μ := by
          rfl

/-- Square-integrability of the symmetrized copy follows from square
integrability of the original variable. -/
theorem integrable_pow_two_sub_comp_fst_comp_snd
    [IsProbabilityMeasure μ] {X : Ω → ℝ}
    (h_meas : Measurable X)
    (h_sq_int : Integrable (fun ω => X ω ^ (2 : ℕ)) μ) :
    Integrable (fun ω : Ω × Ω => (X ω.1 - X ω.2) ^ (2 : ℕ)) (μ.prod μ) := by
  let Y : Ω × Ω → ℝ := fun ω => X ω.1 - X ω.2
  let G : Ω × Ω → ℝ := fun ω => 2 * (X ω.1 ^ (2 : ℕ) + X ω.2 ^ (2 : ℕ))
  have hfst : Integrable (fun ω : Ω × Ω => X ω.1 ^ (2 : ℕ)) (μ.prod μ) := h_sq_int.comp_fst μ
  have hsnd : Integrable (fun ω : Ω × Ω => X ω.2 ^ (2 : ℕ)) (μ.prod μ) := h_sq_int.comp_snd μ
  have hG_int : Integrable G (μ.prod μ) := by
    simpa [G] using (hfst.add hsnd).const_mul (2 : ℝ)
  have hY_meas : Measurable Y := by
    exact (h_meas.comp measurable_fst).sub (h_meas.comp measurable_snd)
  have hY_aesm :
      AEStronglyMeasurable (fun ω : Ω × Ω => Y ω ^ (2 : ℕ)) (μ.prod μ) := by
    exact (hY_meas.aemeasurable.pow_const 2).aestronglyMeasurable
  refine hG_int.mono' hY_aesm ?_
  filter_upwards with ω
  have hpoint : (X ω.1 - X ω.2) ^ (2 : ℕ) ≤ 2 * (X ω.1 ^ (2 : ℕ) + X ω.2 ^ (2 : ℕ)) := by
    nlinarith [sq_nonneg (X ω.1 + X ω.2)]
  simpa [Y, G] using hpoint

/-- The second moment of the symmetrized copy is controlled by the original
second moment. -/
theorem moment_sub_comp_fst_comp_snd_le_four_mul
    [IsProbabilityMeasure μ] {X : Ω → ℝ}
    (h_meas : Measurable X)
    (h_sq_int : Integrable (fun ω => X ω ^ (2 : ℕ)) μ) :
    ProbabilityTheory.moment (fun ω : Ω × Ω => X ω.1 - X ω.2) 2 (μ.prod μ) ≤
      4 * ProbabilityTheory.moment X 2 μ := by
  let Y : Ω × Ω → ℝ := fun ω => X ω.1 - X ω.2
  let G : Ω × Ω → ℝ := fun ω => 2 * (X ω.1 ^ (2 : ℕ) + X ω.2 ^ (2 : ℕ))
  have hY_int : Integrable (fun ω : Ω × Ω => Y ω ^ (2 : ℕ)) (μ.prod μ) :=
    integrable_pow_two_sub_comp_fst_comp_snd (μ := μ) h_meas h_sq_int
  have hfst : Integrable (fun ω : Ω × Ω => X ω.1 ^ (2 : ℕ)) (μ.prod μ) := h_sq_int.comp_fst μ
  have hsnd : Integrable (fun ω : Ω × Ω => X ω.2 ^ (2 : ℕ)) (μ.prod μ) := h_sq_int.comp_snd μ
  have hG_int : Integrable G (μ.prod μ) := by
    simpa [G] using (hfst.add hsnd).const_mul (2 : ℝ)
  have hpoint :
      ∀ᵐ ω : Ω × Ω ∂(μ.prod μ), Y ω ^ (2 : ℕ) ≤ G ω :=
    Filter.Eventually.of_forall fun ω => by
      have hω : (X ω.1 - X ω.2) ^ (2 : ℕ) ≤ 2 * (X ω.1 ^ (2 : ℕ) + X ω.2 ^ (2 : ℕ)) := by
        nlinarith [sq_nonneg (X ω.1 + X ω.2)]
      simpa [Y, G] using hω
  have hfst_eq :
      ∫ ω : Ω × Ω, X ω.1 ^ (2 : ℕ) ∂(μ.prod μ) = ProbabilityTheory.moment X 2 μ := by
    simpa [ProbabilityTheory.moment] using
      (integral_fun_fst (μ := μ) (ν := μ) (f := fun ω : Ω => X ω ^ (2 : ℕ)))
  have hsnd_eq :
      ∫ ω : Ω × Ω, X ω.2 ^ (2 : ℕ) ∂(μ.prod μ) = ProbabilityTheory.moment X 2 μ := by
    simpa [ProbabilityTheory.moment] using
      (integral_fun_snd (μ := μ) (ν := μ) (f := fun ω : Ω => X ω ^ (2 : ℕ)))
  calc
    ProbabilityTheory.moment (fun ω : Ω × Ω => X ω.1 - X ω.2) 2 (μ.prod μ)
        = ∫ ω : Ω × Ω, Y ω ^ (2 : ℕ) ∂(μ.prod μ) := by rfl
    _ ≤ ∫ ω : Ω × Ω, G ω ∂(μ.prod μ) := by
          exact integral_mono_ae hY_int hG_int hpoint
    _ = 2 * (∫ ω : Ω × Ω, X ω.1 ^ (2 : ℕ) ∂(μ.prod μ) +
            ∫ ω : Ω × Ω, X ω.2 ^ (2 : ℕ) ∂(μ.prod μ)) := by
          rw [show (∫ ω : Ω × Ω, G ω ∂(μ.prod μ)) =
            ∫ ω : Ω × Ω, 2 * (X ω.1 ^ (2 : ℕ) + X ω.2 ^ (2 : ℕ)) ∂(μ.prod μ) by rfl]
          rw [integral_const_mul]
          congr 1
          exact integral_add hfst hsnd
    _ = 4 * ProbabilityTheory.moment X 2 μ := by
          rw [hfst_eq, hsnd_eq]
          ring

/-- Integrability of the symmetrized finite maximum follows from integrability
of the original finite maximum. -/
theorem integrable_sup'_abs_sub_pow_of_integrable_sup'_abs_pow
    [IsProbabilityMeasure μ]
    {X : ι → Ω → ℝ} {s : Finset ι} (hs : s.Nonempty) {p : ℕ}
    (h_meas : ∀ i, Measurable (X i))
    (hmax_int : Integrable (fun ω => (s.sup' hs (fun i => |X i ω|)) ^ p) μ) :
    Integrable (fun ω : Ω × Ω => (s.sup' hs (fun i => |X i ω.1 - X i ω.2|)) ^ p) (μ.prod μ) := by
  let M : Ω → ℝ := fun ω => s.sup' hs (fun i => |X i ω|)
  let G : Ω × Ω → ℝ := fun ω => (2 ^ (p - 1) : ℝ) * (M ω.1 ^ p + M ω.2 ^ p)
  have hfst : Integrable (fun ω : Ω × Ω => M ω.1 ^ p) (μ.prod μ) := by
    simpa [M] using hmax_int.comp_fst μ
  have hsnd : Integrable (fun ω : Ω × Ω => M ω.2 ^ p) (μ.prod μ) := by
    simpa [M] using hmax_int.comp_snd μ
  have hG_int : Integrable G (μ.prod μ) := by
    simpa [G] using (hfst.add hsnd).const_mul ((2 ^ (p - 1) : ℕ) : ℝ)
  have hleft_meas :
      Measurable (fun ω : Ω × Ω => s.sup' hs (fun i => |X i ω.1 - X i ω.2|)) := by
    have hsup_meas :
        Measurable (s.sup' hs (fun i (ω : Ω × Ω) => |X i ω.1 - X i ω.2|)) := by
      refine Finset.measurable_sup' (hs := hs) (f := fun i (ω : Ω × Ω) => |X i ω.1 - X i ω.2|) ?_
      intro i hi
      exact
        continuous_abs.measurable.comp
          (((h_meas i).comp measurable_fst).sub ((h_meas i).comp measurable_snd))
    convert hsup_meas using 1
    ext ω
    simp
  have hleft_aesm :
      AEStronglyMeasurable
        (fun ω : Ω × Ω => (s.sup' hs (fun i => |X i ω.1 - X i ω.2|)) ^ p) (μ.prod μ) := by
    exact (hleft_meas.aemeasurable.pow_const p).aestronglyMeasurable
  refine hG_int.mono' hleft_aesm ?_
  filter_upwards with ω
  have hω := sup'_abs_sub_pow_le (X := X) (s := s) hs (p := p) ω
  have hbase_nonneg : 0 ≤ s.sup' hs (fun i => |X i ω.1 - X i ω.2|) := by
    have hnonneg : 0 ≤ |X hs.choose ω.1 - X hs.choose ω.2| := abs_nonneg _
    exact le_trans hnonneg (Finset.le_sup' (f := fun i => |X i ω.1 - X i ω.2|) hs.choose_spec)
  simpa [G, M, abs_of_nonneg hbase_nonneg] using hω

/-- Real-exponent integrability of the symmetrized finite maximum follows
from integrability of the original finite maximum. -/
theorem integrable_sup'_abs_sub_rpow_of_integrable_sup'_abs_rpow
    [IsProbabilityMeasure μ]
    {X : ι → Ω → ℝ} {s : Finset ι} (hs : s.Nonempty) {p : ℝ}
    (hp : 1 ≤ p)
    (h_meas : ∀ i, Measurable (X i))
    (hmax_int : Integrable (fun ω => (s.sup' hs (fun i => |X i ω|)) ^ p) μ) :
    Integrable (fun ω : Ω × Ω =>
      (s.sup' hs (fun i => |X i ω.1 - X i ω.2|)) ^ p) (μ.prod μ) := by
  let M : Ω → ℝ := fun ω => s.sup' hs (fun i => |X i ω|)
  let G : Ω × Ω → ℝ := fun ω =>
    (2 : ℝ) ^ (p - 1) * (M ω.1 ^ p + M ω.2 ^ p)
  have hfst : Integrable (fun ω : Ω × Ω => M ω.1 ^ p) (μ.prod μ) := by
    simpa [M] using hmax_int.comp_fst μ
  have hsnd : Integrable (fun ω : Ω × Ω => M ω.2 ^ p) (μ.prod μ) := by
    simpa [M] using hmax_int.comp_snd μ
  have hG_int : Integrable G (μ.prod μ) := by
    simpa [G] using (hfst.add hsnd).const_mul ((2 : ℝ) ^ (p - 1))
  have hleft_meas :
      Measurable (fun ω : Ω × Ω => s.sup' hs (fun i => |X i ω.1 - X i ω.2|)) := by
    have hsup_meas :
        Measurable (s.sup' hs (fun i (ω : Ω × Ω) => |X i ω.1 - X i ω.2|)) := by
      refine Finset.measurable_sup' (hs := hs)
        (f := fun i (ω : Ω × Ω) => |X i ω.1 - X i ω.2|) ?_
      intro i hi
      exact continuous_abs.measurable.comp
        (((h_meas i).comp measurable_fst).sub ((h_meas i).comp measurable_snd))
    convert hsup_meas using 1
    ext ω
    simp
  have hleft_aesm :
      AEStronglyMeasurable
        (fun ω : Ω × Ω => (s.sup' hs (fun i => |X i ω.1 - X i ω.2|)) ^ p) (μ.prod μ) := by
    exact (hleft_meas.pow_const p).aestronglyMeasurable
  refine hG_int.mono' hleft_aesm ?_
  filter_upwards with ω
  have hω := sup'_abs_sub_rpow_le (X := X) (s := s) hs hp ω
  have hbase_nonneg : 0 ≤ s.sup' hs (fun i => |X i ω.1 - X i ω.2|) := by
    have hnonneg : 0 ≤ |X hs.choose ω.1 - X hs.choose ω.2| := abs_nonneg _
    exact le_trans hnonneg
      (Finset.le_sup' (f := fun i => |X i ω.1 - X i ω.2|) hs.choose_spec)
  simpa [G, M, abs_of_nonneg (Real.rpow_nonneg hbase_nonneg p)] using hω

/-- Product-space real-exponent `L^p` control of the finite maximum of the
symmetrized family by the original maximum. -/
theorem integral_sup'_abs_sub_rpow_le_two_rpow_mul_integral_sup'_abs_rpow
    [IsProbabilityMeasure μ]
    {X : ι → Ω → ℝ} {s : Finset ι} (hs : s.Nonempty) {p : ℝ}
    (hp : 1 ≤ p)
    (h_meas : ∀ i, Measurable (X i))
    (hmax_int : Integrable (fun ω => (s.sup' hs (fun i => |X i ω|)) ^ p) μ) :
    ∫ ω : Ω × Ω, (s.sup' hs (fun i => |X i ω.1 - X i ω.2|)) ^ p ∂(μ.prod μ) ≤
      (2 : ℝ) ^ p * ∫ ω, (s.sup' hs (fun i => |X i ω|)) ^ p ∂μ := by
  let M : Ω → ℝ := fun ω => s.sup' hs (fun i => |X i ω|)
  let G : Ω × Ω → ℝ := fun ω =>
    (2 : ℝ) ^ (p - 1) * (M ω.1 ^ p + M ω.2 ^ p)
  have hfst : Integrable (fun ω : Ω × Ω => M ω.1 ^ p) (μ.prod μ) := by
    simpa [M] using hmax_int.comp_fst μ
  have hsnd : Integrable (fun ω : Ω × Ω => M ω.2 ^ p) (μ.prod μ) := by
    simpa [M] using hmax_int.comp_snd μ
  have hG_int : Integrable G (μ.prod μ) := by
    simpa [G] using (hfst.add hsnd).const_mul ((2 : ℝ) ^ (p - 1))
  have hleft_int :
      Integrable
        (fun ω : Ω × Ω => (s.sup' hs (fun i => |X i ω.1 - X i ω.2|)) ^ p) (μ.prod μ) := by
    exact integrable_sup'_abs_sub_rpow_of_integrable_sup'_abs_rpow
      (μ := μ) (X := X) hs hp h_meas hmax_int
  have hpoint :
      ∀ᵐ ω : Ω × Ω ∂(μ.prod μ),
        (s.sup' hs (fun i => |X i ω.1 - X i ω.2|)) ^ p ≤ G ω :=
    Filter.Eventually.of_forall fun ω => by
      simpa [G, M] using sup'_abs_sub_rpow_le (X := X) (s := s) hs hp ω
  have hM_meas : Measurable M := by
    dsimp [M]
    convert
      (Finset.measurable_sup' (hs := hs) (f := fun i ω => |X i ω|) fun i _ =>
        continuous_abs.measurable.comp (h_meas i)) using 1
    ext ω
    simp
  have hid :
      IdentDistrib
        (fun ω : Ω × Ω => M ω.1 ^ p)
        (fun ω : Ω × Ω => M ω.2 ^ p)
        (μ.prod μ) (μ.prod μ) := by
    simpa [M, Function.comp_def] using
      (identDistrib_comp_fst_comp_snd_prod (μ := μ) (X := M) hM_meas.aemeasurable).comp
        (measurable_id.pow_const p)
  have hfst_eq :
      ∫ ω : Ω × Ω, M ω.1 ^ p ∂(μ.prod μ) = ∫ ω, M ω ^ p ∂μ := by
    simpa [M] using
      (integral_fun_fst (μ := μ) (ν := μ) (f := fun ω : Ω => M ω ^ p))
  have hsnd_eq :
      ∫ ω : Ω × Ω, M ω.2 ^ p ∂(μ.prod μ) =
        ∫ ω : Ω × Ω, M ω.1 ^ p ∂(μ.prod μ) := by
    simpa using hid.integral_eq.symm
  have hpow_two : (2 : ℝ) ^ (p - 1) * 2 = (2 : ℝ) ^ p := by
    calc
      (2 : ℝ) ^ (p - 1) * 2 =
          (2 : ℝ) ^ (p - 1) * (2 : ℝ) ^ (1 : ℝ) := by rw [Real.rpow_one]
      _ = (2 : ℝ) ^ ((p - 1) + 1) := (Real.rpow_add (by norm_num) _ _).symm
      _ = (2 : ℝ) ^ p := by
        congr 1
        ring
  calc
    ∫ ω : Ω × Ω, (s.sup' hs (fun i => |X i ω.1 - X i ω.2|)) ^ p ∂(μ.prod μ)
        ≤ ∫ ω : Ω × Ω, G ω ∂(μ.prod μ) := by
            exact integral_mono_ae hleft_int hG_int hpoint
    _ = (2 : ℝ) ^ (p - 1) *
          (∫ ω : Ω × Ω, M ω.1 ^ p ∂(μ.prod μ) +
            ∫ ω : Ω × Ω, M ω.2 ^ p ∂(μ.prod μ)) := by
          rw [show (∫ ω : Ω × Ω, G ω ∂(μ.prod μ)) =
            ∫ ω : Ω × Ω, (2 : ℝ) ^ (p - 1) * (M ω.1 ^ p + M ω.2 ^ p) ∂(μ.prod μ) by rfl]
          rw [integral_const_mul]
          congr 1
          exact integral_add hfst hsnd
    _ = (2 : ℝ) ^ (p - 1) * (2 * ∫ ω, M ω ^ p ∂μ) := by
          rw [hsnd_eq, two_mul, hfst_eq]
    _ = (2 : ℝ) ^ p * ∫ ω, M ω ^ p ∂μ := by
          calc
            (2 : ℝ) ^ (p - 1) * (2 * ∫ ω, M ω ^ p ∂μ) =
                (((2 : ℝ) ^ (p - 1)) * 2) * ∫ ω, M ω ^ p ∂μ := by ring_nf
            _ = (2 : ℝ) ^ p * ∫ ω, M ω ^ p ∂μ := by rw [hpow_two]
    _ = (2 : ℝ) ^ p * ∫ ω, (s.sup' hs (fun i => |X i ω|)) ^ p ∂μ := by
          rfl

/-- Computing `sup'` over the subtype attached to a nonempty finset agrees with
computing `sup'` over the original finset. -/
theorem sup'_univ_subtype_eq_sup'
    {α : Type*} [SemilatticeSup α] {s : Finset ι}
    (hs : s.Nonempty) (hs_univ : (Finset.univ : Finset ↥s).Nonempty) (f : ι → α) :
    (Finset.univ : Finset ↥s).sup' hs_univ (fun i : ↥s => f i) = s.sup' hs f := by
  simpa [Finset.univ_eq_attach, Finset.attach_map_val] using!
    (Finset.sup'_comp_eq_map
      (s := s.attach)
      (f := Function.Embedding.subtype fun x => x ∈ s)
      (g := f)
      (hs := by simpa [Finset.univ_eq_attach] using hs_univ))

section

omit [MeasurableSpace Ω]

/-- The finite symmetrized sum can be rewritten as a sum over the subtype
indexed by the ambient finite set. -/
theorem sum_univ_subtype_eq_symmetrizedFinsetSum
    {X : ι → Ω → ℝ} {s : Finset ι} (ω : Ω × Ω) :
    (∑ i ∈ (Finset.univ : Finset ↥s), (X i ω.1 - X i ω.2)) = symmetrizedFinsetSum X s ω := by
  rw [Finset.univ_eq_attach, symmetrizedFinsetSum]
  simpa using (Finset.sum_attach s (fun i => X i ω.1 - X i ω.2))

end

end
end IndependentSums
end Homogenization
