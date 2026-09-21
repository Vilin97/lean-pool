/-
Copyright (c) 2026 Arthur Freitas Ramos and coauthors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arthur Freitas Ramos, David Barros Hulak, Ruy J. G. B. de Queiroz
-/

/-
Original copyright notice:
Copyright (c) 2026 Arthur Freitas Ramos, David Barros Hulak, Ruy J. G. B. de Queiroz. All rights
reserved.
-/

module

public import LeanPool.PoincareGeometry.AlmostSchur.TestGraphCutoff
public import LeanPool.PoincareGeometry.AlmostSchur.TestGraphUniformQuotient
public import LeanPool.PoincareGeometry.AlmostSchur.L2FiniteFamily

/-! # Constructing the actual cutoff quotient test fields

Two applications of the cutoff graph operator produce the η² test and its
product-rule derivative graph. All fields are constructed as actual L² classes.
-/

@[expose] public noncomputable section
open Set MeasureTheory Filter
open scoped Topology BigOperators

namespace AlmostSchur

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem exists_cutoff_quotient_fields (b : OrthonormalBasis ι ℝ E)
    {T : Set E} (p : Lp ℝ 2 (volume : Measure E) × (ι → Lp ℝ 2 (volume : Measure E)))
    (hp : p ∈ closure (c1SupportedTestGraph (fun i => b i) T))
    (η : E → ℝ) (hη : ContDiff ℝ 1 η) (hcη : HasCompactSupport η)
    (hη1 : ∀ x, |η x| ≤ 1) (H : ℝ) (hH : 0 ≤ H)
    (hdη : ∀ x, ‖(WithLp.toLp 2 (fun i => fderiv ℝ η x (b i)) : EuclideanSpace ℝ ι)‖ ≤ H)
    (v : E) (h : ℝ) (hh : h ≠ 0) :
    ∃ q : Lp ℝ 2 (volume : Measure E) × (ι → Lp ℝ 2 (volume : Measure E)),
    ∃ r s De : Lp (EuclideanSpace ℝ ι) 2 (volume : Measure E),
      q ∈ closure (c1SupportedTestGraph (fun i => b i) (tsupport η)) ∧
      (∀ᵐ x ∂(volume : Measure E), ∀ i, r x i = η x * directionalDifferenceQuotient (p.2 i) v h x) ∧
      (∀ᵐ x ∂(volume : Measure E), ∀ i, s x i = directionalDifferenceQuotient p.1 v h x * fderiv ℝ η x (b i)) ∧
      (∀ᵐ x ∂(volume : Measure E), ∀ i, De x i = η x * p.2 i x) ∧
      (∀ᵐ x ∂(volume : Measure E), ∀ i, q.2 i x = η x * (r x i + 2 * s x i)) ∧
      ‖s‖ ≤ H * (‖v‖ * Real.sqrt (∑ i, ‖p.2 i‖ ^ 2)) ∧
      ‖De‖ ≤ Real.sqrt (∑ i, ‖p.2 i‖ ^ 2) := by
  obtain ⟨M, N, hM, hN, hgraph⟩ := exists_cutoff_testGraph_operator (fun i => b i) η hη hcη
  let w := directionalDifferenceQuotient p.1 v h
  let V := fun i => directionalDifferenceQuotient (p.2 i) v h
  let r := l2FiniteFamily (fun i => M (V i))
  let s := l2FiniteFamily (fun i => N i w)
  let De := l2FiniteFamily (fun i => M (p.2 i))
  have hδ : (w, V) ∈ closure (c1SupportedTestGraph (fun i => b i) univ) :=
    differenceQuotient_mem_closure_c1SupportedTestGraph (fun i => b i)
      (subset_univ T) v h (subset_univ _) hp
  have hfirst := hgraph univ (w, V) hδ
  have hsecond := hgraph (tsupport η) (M w, fun i => N i w + M (V i)) hfirst
  let q := (M (M w), fun i => N i (M w) + M (N i w + M (V i)))
  have hr : ∀ᵐ x ∂(volume : Measure E), ∀ i, r x i = η x * V i x := by
    filter_upwards [l2FiniteFamily_ae_eq (fun i => M (V i)),
      ae_all_iff.mpr (fun i => hM (V i))] with x hx hm
    intro i
    exact (congrArg (fun a : EuclideanSpace ℝ ι => a i) hx).trans (hm i)
  have hs : ∀ᵐ x ∂(volume : Measure E), ∀ i, s x i = w x * fderiv ℝ η x (b i) := by
    filter_upwards [l2FiniteFamily_ae_eq (fun i => N i w),
      ae_all_iff.mpr (fun i => hN i w)] with x hx hn
    intro i
    exact (congrArg (fun a : EuclideanSpace ℝ ι => a i) hx).trans ((hn i).trans (mul_comm _ _))
  have hDe : ∀ᵐ x ∂(volume : Measure E), ∀ i, De x i = η x * p.2 i x := by
    filter_upwards [l2FiniteFamily_ae_eq (fun i => M (p.2 i)),
      ae_all_iff.mpr (fun i => hM (p.2 i))] with x hx hm
    intro i
    exact (congrArg (fun a : EuclideanSpace ℝ ι => a i) hx).trans (hm i)
  refine ⟨q, r, s, De, hsecond, hr, hs, hDe, ?_, ?_, ?_⟩
  · filter_upwards [hr, hs, hM w, ae_all_iff.mpr (fun i => hN i (M w)),
      ae_all_iff.mpr (fun i => hM (N i w + M (V i))),
      ae_all_iff.mpr (fun i => Lp.coeFn_add (N i w) (M (V i))),
      ae_all_iff.mpr (fun i => Lp.coeFn_add (N i (M w)) (M (N i w + M (V i)))),
      ae_all_iff.mpr (fun i => hN i w), ae_all_iff.mpr (fun i => hM (V i))]
      with x hr hs hMw hn hm ha hqa hnw hmv
    intro i
    change (N i (M w) + M (N i w + M (V i))) x = _
    rw [hqa i, Pi.add_apply, hn i, hm i, ha i, Pi.add_apply, hnw i, hmv i, hMw, hr i, hs i]
    ring
  · have hb : ‖s‖ ≤ H * ‖w‖ := by
      apply Lp.norm_le_mul_norm_of_ae_le_mul
      filter_upwards [hs] with x hx
      have he : s x = w x • (WithLp.toLp 2 (fun i => fderiv ℝ η x (b i)) : EuclideanSpace ℝ ι) := by
        ext i
        exact hx i
      rw [he, norm_smul]
      exact (mul_le_mul_of_nonneg_left (hdη x) (norm_nonneg _)).trans_eq (mul_comm _ _)
    exact hb.trans (mul_le_mul_of_nonneg_left
      (norm_differenceQuotient_closure_c1SupportedTestGraph_le b hp v h hh) hH)
  · rw [← norm_l2FiniteFamily]
    apply Lp.norm_le_norm_of_ae_le
    filter_upwards [hDe, l2FiniteFamily_ae_eq p.2] with x hd hx
    have he : De x = η x • l2FiniteFamily p.2 x := by
      rw [hx]
      ext i
      exact hd i
    rw [he, norm_smul, Real.norm_eq_abs]
    exact (mul_le_mul_of_nonneg_right (hη1 x) (norm_nonneg _)).trans_eq (one_mul _)

end AlmostSchur
