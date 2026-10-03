/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Ergodic.AveragedCompositionCalculus
public import Mathlib.MeasureTheory.Function.LpSeminorm.TriangleInequality
public import Mathlib.MeasureTheory.Function.LpSeminorm.SMul

/-! Averaged norms of the finite coordinate chain-rule terms. -/

@[expose] public section

noncomputable section
open scoped ContDiff ENNReal
open MeasureTheory Homogenization AVenhance.FaaDiBruno AVenhance.Infra.Torus
namespace AVenhance.Infra.Ergodic

/-- Smooth functions have every finite Lp norm on the bounded unit cell. -/
theorem continuous_unitCell_memLp {d : ℕ} {F : Type*}
    [NormedAddCommGroup F] {u : Vec d → F} (hu : Continuous u) (p : ℝ≥0∞) :
    MemLp u p (volume.restrict (unitCell d)) := by
  let Q : Set (Vec d) := Set.pi Set.univ fun _ => Set.Icc (0 : ℝ) 1
  have hQ : IsCompact Q := isCompact_univ_pi fun _ => isCompact_Icc
  have hsub : unitCell d ⊆ Q := by
    intro x hx
    simp only [unitCell, unitCellAt, Set.mem_ofPred_eq, zero_add] at hx
    simp only [Q, Set.mem_pi, Set.mem_univ, forall_true_left]
    exact fun i => ⟨(hx i).1.le, (hx i).2⟩
  have hfinite : IsFiniteMeasure (volume.restrict (unitCell d) : Measure (Vec d)) := by
    rw [isFiniteMeasure_iff, Measure.restrict_apply_univ]
    exact (measure_mono hsub).trans_lt hQ.measure_lt_top
  let := hfinite
  obtain ⟨C, _, hC⟩ := (hQ.image hu).isBounded.subset_ball_lt 0 0
  apply MemLp.of_bound (hu.aestronglyMeasurable.restrict) C
  filter_upwards [ae_restrict_mem (measurableSet_unitCell d)] with x hx
  have hh := hC (Set.mem_image_of_mem u (hsub hx))
  exact (show ‖u x‖ < C by simpa only [Metric.mem_ball, dist_zero_right] using hh).le

/-- Periodic volume-preserving composition preserves finite averaged Lp norms. -/
theorem eLpNorm_comp_flow_eq {d : ℕ} {u : Vec d → ℂ}
    (hu : Continuous u) (hper : IsZdPeriodic u)
    (X : PeriodicVolumePreservingDiffeomorphism d) {p : ℝ≥0∞}
    (hp0 : p ≠ 0) (hpt : p ≠ ⊤) :
    eLpNorm (u ∘ X.toFun) p (volume.restrict (unitCell d)) =
      eLpNorm u p (volume.restrict (unitCell d)) := by
  have hm := continuous_unitCell_memLp hu p
  have hmc := continuous_unitCell_memLp (hu.comp X.contDiff_toFun.continuous) p
  rw [hmc.eLpNorm_eq_integral_rpow_norm hp0 hpt,
    hm.eLpNorm_eq_integral_rpow_norm hp0 hpt]
  have hav := cellAverage_comp_flow_eq (fun x => ‖u x‖ ^ p.toReal)
    (fun x k => by
      change ‖u (x + intVector k)‖ ^ p.toReal = ‖u x‖ ^ p.toReal
      rw [hper k x]) X
  rw [cellAverage_eq_unitCellIntegral, cellAverage_eq_unitCellIntegral] at hav
  have hcell : unitCellSet d = unitCell d := by
    ext x
    simp [unitCellSet, unitCell, unitCellAt]
  simpa only [hcell, Function.comp_apply, one_div] using
    congrArg (fun a : ℝ => ENNReal.ofReal (a ^ (1 / p.toReal))) hav

/-- Uniform flow factors are placed outside the averaged norm. -/
theorem compositionJetTerm_eLpNorm_le {d n : ℕ} {f : Vec d → ℂ}
    {X : Vec d → Vec d} (hf : ContDiff ℝ ∞ f) (hXs : ContDiff ℝ ∞ X) (w : Fin n → Fin d) (c :
        OrderedFinpartition n)
    (j : Fin c.length → Fin d) {CX R : ℝ} (hCX : 0 ≤ CX) (hR : 0 ≤ R)
    (hX : ∀ (a : ℕ) (v : Fin a → Fin d), 0 < a → ∀ x i,
      |(spatialJet a X v x) i| ≤ CX * (a.factorial : ℝ) * R ^ a)
    (p : ℝ≥0∞) (μ : Measure (Vec d)) :
    eLpNorm (compositionJetTerm f X w c j) p μ ≤
      ENNReal.ofReal (∏ b, CX * (c.partSize b).factorial * R ^ c.partSize b) *
        eLpNorm (fun x => spatialJet c.length f j (X x)) p μ := by
  classical
  let B : ℝ := ∏ b, CX * (c.partSize b).factorial * R ^ c.partSize b
  have hB : 0 ≤ B := Finset.prod_nonneg fun b hb => by positivity
  have hp (x : Vec d) :
      ‖compositionJetTerm f X w c j x‖ ≤ ‖B • spatialJet c.length f j (X x)‖ := by
    simp only [compositionJetTerm, norm_smul, Real.norm_eq_abs, abs_of_nonneg hB,
      Finset.abs_prod]
    apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
    exact Finset.prod_le_prod₀ (fun _ _ => abs_nonneg _) fun b hb =>
      hX _ _ (c.partSize_pos b) x (j b)
  have hcoeff : Continuous (fun x => ∏ b,
      (spatialJet (c.partSize b) X (fun a => w (c.emb b a)) x) (j b)) :=
    continuous_finsetProd _ fun b hb =>
      (continuous_apply (j b)).comp (spatialJet_continuous hXs _)
  have hterm : Continuous (compositionJetTerm f X w c j) :=
    hcoeff.smul ((spatialJet_continuous hf j).comp hXs.continuous)
  calc
    _ ≤ eLpNorm (fun x => B • spatialJet c.length f j (X x)) p μ :=
      eLpNorm_mono_ae hterm.aestronglyMeasurable (Filter.Eventually.of_forall hp)
    _ = _ := by
      change eLpNorm (B • (fun x => spatialJet c.length f j (X x))) p μ = _
      rw [eLpNorm_const_smul]
      simp only [Real.enorm_eq_ofReal_abs, abs_of_nonneg hB, B]

end AVenhance.Infra.Ergodic
