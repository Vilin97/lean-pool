/-
Copyright (c) 2026 Arthur Freitas Ramos, David Barros Hulak, Ruy J. G. B. de Queiroz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arthur Freitas Ramos, David Barros Hulak, Ruy J. G. B. de Queiroz
-/

import LeanPool.PoincareGeometry.BonnetMyers.MetricParallel
import LeanPool.PoincareGeometry.BonnetMyers.MetricParallelAlgebra

/-! # Metric Variable -/

noncomputable section
open Bundle Manifold Set
open scoped Manifold ContDiff ENNReal Topology BigOperators

namespace BonnetMyersEntry
universe u v w
variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type v} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [I.Boundaryless]
  {M : Type w} [TopologicalSpace M] [ChartedSpace H M]
  [T2Space M] [SigmaCompactSpace M] [IsManifold I ∞ M]
local notation "TM" => (TangentSpace I : M → Type _)
namespace LocalGeodesicData
variable [RiemannianBundle (TangentSpace I : M → Type _)]

/-! A variable-coefficient version of the metric derivative identity.  The
coefficient functions are differentiated explicitly; this is the form used
by the intrinsic transport argument. -/
lemma coordinateFrameCombination_inner_hasDerivAt_variable
    (cov : CovariantDerivative I E TM) (x₀ : M)
    (b : Module.Basis (Fin (Module.finrank ℝ E)) ℝ E)
    {γ : ℝ → M} {t : ℝ}
    (u : E) {w v : ℝ → E} {dw dv : E}
    {γ' : TangentSpace 𝓘(ℝ, ℝ) t →L[ℝ] TangentSpace I (γ t)}
    (hγ : HasMFDerivAt (𝓘(ℝ, ℝ)) I γ t γ')
    (hγ' : γ' 1 = coordinateFrameCombination (I := I) (M := M)
      (x₀ := x₀) b u (γ t))
    (hy : γ t ∈ (chartAt H x₀).source)
    (hmetric : cov.IsMetricCompatibleTangent)
    [IsContMDiffRiemannianBundle I 1 E TM]
    [CovariantDerivative.ContMDiffCovariantDerivative cov 1]
    (hframe : ∀ j : Fin (Module.finrank ℝ E),
      ∀ᶠ z in 𝓝 (γ t),
        smoothFrame (I := I) (M := M) (E := E) x₀ b j z =
          (trivializationAt E TM x₀).localFrame b j z)
    (hw : HasDerivAt w dw t) (hv : HasDerivAt v dv t) :
    HasDerivAt
      (fun s ↦ inner ℝ
        (coordinateFrameCombination (I := I) (M := M) (x₀ := x₀) b (w s) (γ s))
        (coordinateFrameCombination (I := I) (M := M) (x₀ := x₀) b (v s) (γ s)))
      (inner ℝ
        (coordinateFrameCombination (I := I) (M := M) (x₀ := x₀) b
          (dw + coordinateParallelOperator (I := I) (M := M) (E := E)
            cov x₀ b (extChartAt I x₀ (γ t)) u (w t)) (γ t))
        (coordinateFrameCombination (I := I) (M := M) (x₀ := x₀) b (v t) (γ t)) +
       inner ℝ
        (coordinateFrameCombination (I := I) (M := M) (x₀ := x₀) b (w t) (γ t))
        (coordinateFrameCombination (I := I) (M := M) (x₀ := x₀) b
          (dv + coordinateParallelOperator (I := I) (M := M) (E := E)
            cov x₀ b (extChartAt I x₀ (γ t)) u (v t)) (γ t))) t := by
  let y := γ t
  let P : E → E := coordinateParallelOperator (I := I) (M := M) (E := E)
    cov x₀ b (extChartAt I x₀ y) u
  have hbasis : ∀ (i : Fin (Module.finrank ℝ E)) (z : M),
      coordinateFrameCombination (I := I) (M := M) (x₀ := x₀) b (b i) z =
        (trivializationAt E TM x₀).localFrame b i z := by
    intro i z
    simp [coordinateFrameCombination, Module.Basis.repr_self,
      Finsupp.single_apply, eq_comm]
  have hwi : ∀ i : Fin (Module.finrank ℝ E),
      HasDerivAt (fun s ↦ (b.repr (w s)) i) ((b.repr dw) i) t := by
    intro i
    have hc : HasDerivAt (fun _ : ℝ ↦ (b.coord i).toContinuousLinearMap)
        0 t := hasDerivAt_const t (b.coord i).toContinuousLinearMap
    simpa using hc.clm_apply hw
  have hvi : ∀ j : Fin (Module.finrank ℝ E),
      HasDerivAt (fun s ↦ (b.repr (v s)) j) ((b.repr dv) j) t := by
    intro j
    have hc : HasDerivAt (fun _ : ℝ ↦ (b.coord j).toContinuousLinearMap)
        0 t := hasDerivAt_const t (b.coord j).toContinuousLinearMap
    simpa using hc.clm_apply hv
  have hG : ∀ i j : Fin (Module.finrank ℝ E),
      HasDerivAt
        (fun s ↦ inner ℝ
          (coordinateFrameCombination (I := I) (M := M) (x₀ := x₀) b (b i) (γ s))
          (coordinateFrameCombination (I := I) (M := M) (x₀ := x₀) b (b j) (γ s)))
        (inner ℝ
          (coordinateFrameCombination (I := I) (M := M) (x₀ := x₀) b (P (b i)) y)
          (coordinateFrameCombination (I := I) (M := M) (x₀ := x₀) b (b j) y) +
         inner ℝ
          (coordinateFrameCombination (I := I) (M := M) (x₀ := x₀) b (b i) y)
          (coordinateFrameCombination (I := I) (M := M) (x₀ := x₀) b (P (b j)) y)) t := by
    intro i j
    simpa [P, y] using
      (coordinateFrameCombination_inner_hasDerivAt
        (I := I) (M := M) (E := E) cov x₀ b u (b i) (b j)
        hγ hγ' hy hmetric hframe)
  have hterm : ∀ i j : Fin (Module.finrank ℝ E),
      HasDerivAt
        (fun s ↦ (b.repr (w s) i) * (b.repr (v s) j) *
          inner ℝ
            (coordinateFrameCombination (I := I) (M := M) (x₀ := x₀) b (b i) (γ s))
            (coordinateFrameCombination (I := I) (M := M) (x₀ := x₀) b (b j) (γ s)))
        (((b.repr dw i) * (b.repr (v t) j) +
            (b.repr (w t) i) * (b.repr dv j)) *
          inner ℝ
            (coordinateFrameCombination (I := I) (M := M) (x₀ := x₀) b (b i) y)
            (coordinateFrameCombination (I := I) (M := M) (x₀ := x₀) b (b j) y) +
          (b.repr (w t) i) * (b.repr (v t) j) *
            (inner ℝ
              (coordinateFrameCombination (I := I) (M := M) (x₀ := x₀) b (P (b i)) y)
              (coordinateFrameCombination (I := I) (M := M) (x₀ := x₀) b (b j) y) +
             inner ℝ
              (coordinateFrameCombination (I := I) (M := M) (x₀ := x₀) b (b i) y)
              (coordinateFrameCombination (I := I) (M := M) (x₀ := x₀) b (P (b j)) y))) t := by
    intro i j
    have hprod : HasDerivAt
        (fun s ↦ (b.repr (w s) i) * (b.repr (v s) j))
        ((b.repr dw i) * (b.repr (v t) j) +
          (b.repr (w t) i) * (b.repr dv j)) t := by
      convert (hwi i).mul (hvi j) using 1 <;> rfl
    have hall := hprod.mul (hG i j)
    convert hall using 1 <;> rfl
  have hsum0 : HasDerivAt
      (∑ i, ∑ j, fun s ↦
        (b.repr (w s) i) * (b.repr (v s) j) *
          inner ℝ
            (coordinateFrameCombination (I := I) (M := M) (x₀ := x₀) b (b i) (γ s))
            (coordinateFrameCombination (I := I) (M := M) (x₀ := x₀) b (b j) (γ s)))
      (∑ i, ∑ j,
        (((b.repr dw i) * (b.repr (v t) j) +
            (b.repr (w t) i) * (b.repr dv j)) *
          inner ℝ
            (coordinateFrameCombination (I := I) (M := M) (x₀ := x₀) b (b i) y)
            (coordinateFrameCombination (I := I) (M := M) (x₀ := x₀) b (b j) y) +
          (b.repr (w t) i) * (b.repr (v t) j) *
            (inner ℝ
              (coordinateFrameCombination (I := I) (M := M) (x₀ := x₀) b (P (b i)) y)
              (coordinateFrameCombination (I := I) (M := M) (x₀ := x₀) b (b j) y) +
             inner ℝ
              (coordinateFrameCombination (I := I) (M := M) (x₀ := x₀) b (b i) y)
              (coordinateFrameCombination (I := I) (M := M) (x₀ := x₀) b (P (b j)) y)))) t := by
    apply HasDerivAt.sum
    intro i hi
    apply HasDerivAt.sum
    intro j hj
    exact hterm i j
  have hsum : HasDerivAt
      (fun s ↦ ∑ i, ∑ j,
        (b.repr (w s) i) * (b.repr (v s) j) *
          inner ℝ
            (coordinateFrameCombination (I := I) (M := M) (x₀ := x₀) b (b i) (γ s))
            (coordinateFrameCombination (I := I) (M := M) (x₀ := x₀) b (b j) (γ s)))
      (∑ i, ∑ j,
        (((b.repr dw i) * (b.repr (v t) j) +
            (b.repr (w t) i) * (b.repr dv j)) *
          inner ℝ
            (coordinateFrameCombination (I := I) (M := M) (x₀ := x₀) b (b i) y)
            (coordinateFrameCombination (I := I) (M := M) (x₀ := x₀) b (b j) y) +
          (b.repr (w t) i) * (b.repr (v t) j) *
            (inner ℝ
              (coordinateFrameCombination (I := I) (M := M) (x₀ := x₀) b (P (b i)) y)
              (coordinateFrameCombination (I := I) (M := M) (x₀ := x₀) b (b j) y) +
             inner ℝ
              (coordinateFrameCombination (I := I) (M := M) (x₀ := x₀) b (b i) y)
              (coordinateFrameCombination (I := I) (M := M) (x₀ := x₀) b (P (b j)) y)))) t := by
    convert hsum0 using 1
    · funext s
      simp
  have hderiv := hsum.congr_of_eventuallyEq (by
    filter_upwards [] with s
    calc
      inner ℝ
          (coordinateFrameCombination (I := I) (M := M) (x₀ := x₀) b (w s) (γ s))
          (coordinateFrameCombination (I := I) (M := M) (x₀ := x₀) b (v s) (γ s)) =
          ∑ i, ∑ j, (b.repr (w s) i) * (b.repr (v s) j) *
            inner ℝ
              ((trivializationAt E TM x₀).localFrame b i (γ s))
              ((trivializationAt E TM x₀).localFrame b j (γ s)) :=
        coordinateFrameCombination_inner_expand
          (I := I) (M := M) x₀ b (w s) (v s) (γ s)
      _ = ∑ i, ∑ j, (b.repr (w s) i) * (b.repr (v s) j) *
            inner ℝ
              (coordinateFrameCombination (I := I) (M := M) (x₀ := x₀) b (b i) (γ s))
              (coordinateFrameCombination (I := I) (M := M) (x₀ := x₀) b (b j) (γ s)) := by
        apply Finset.sum_congr rfl
        intro i hi
        apply Finset.sum_congr rfl
        intro j hj
        rw [hbasis, hbasis])
  refine hderiv.congr_deriv ?_
  have hPcoeff : ∀ (q : E) (i : Fin (Module.finrank ℝ E)),
      (b.repr (P q)) i = ∑ l, ∑ k, (b.repr q l) * (b.repr u k) *
        connectionCoefficient (I := I) (M := M) (E := E)
          cov x₀ b i l k y := by
    intro q i
    have hsource : y ∈ (extChartAt I x₀).source := by
      rw [extChartAt_source]
      exact hy
    have hleft : (extChartAt I x₀).symm ((extChartAt I x₀) y) = y :=
      (extChartAt I x₀).left_inv hsource
    rw [show P q = coordinateParallelOperator (I := I) (M := M) (E := E)
        cov x₀ b (extChartAt I x₀ y) u q by rfl]
    rw [coordinateParallelOperator_apply, hleft]
    simp [Module.Basis.repr_self, Finsupp.single_apply, eq_comm]
  have hPcoeff' : ∀ (q : E) (i : Fin (Module.finrank ℝ E)),
      (b.repr (coordinateParallelOperator (I := I) (M := M) (E := E)
        cov x₀ b (extChartAt I x₀ (γ t)) u q)) i =
        ∑ l, ∑ k, (b.repr q l) * (b.repr u k) *
          connectionCoefficient (I := I) (M := M) (E := E)
            cov x₀ b i l k y := by
    intro q i
    simpa [P, y] using hPcoeff q i
  rw [coordinateFrameCombination_inner_expand,
    coordinateFrameCombination_inner_expand]
  simp_rw [hbasis]
  simp only [map_add, Finsupp.add_apply]
  simp_rw [hPcoeff']
  have hPleft : ∀ i j : Fin (Module.finrank ℝ E),
      inner ℝ
          (coordinateFrameCombination (I := I) (M := M) (x₀ := x₀) b (P (b i)) y)
          ((trivializationAt E TM x₀).localFrame b j y) =
        ∑ l, (b.repr (P (b i)) l) *
          inner ℝ ((trivializationAt E TM x₀).localFrame b l y)
            ((trivializationAt E TM x₀).localFrame b j y) := by
    intro i j
    have h := coordinateFrameCombination_inner_expand
      (I := I) (M := M) (E := E) x₀ b (P (b i)) (b j) y
    simpa [hbasis, Module.Basis.repr_self, Finsupp.single_apply, eq_comm] using h
  have hPright : ∀ i j : Fin (Module.finrank ℝ E),
      inner ℝ
          ((trivializationAt E TM x₀).localFrame b i y)
          (coordinateFrameCombination (I := I) (M := M) (x₀ := x₀) b (P (b j)) y) =
        ∑ l, (b.repr (P (b j)) l) *
          inner ℝ ((trivializationAt E TM x₀).localFrame b i y)
            ((trivializationAt E TM x₀).localFrame b l y) := by
    intro i j
    have h := coordinateFrameCombination_inner_expand
      (I := I) (M := M) (E := E) x₀ b (b i) (P (b j)) y
    simpa [hbasis, Module.Basis.repr_self, Finsupp.single_apply, eq_comm] using h
  simp_rw [hPleft, hPright]
  simp_rw [hPcoeff]
  have hPleft' : ∀ i j : Fin (Module.finrank ℝ E),
      ∑ l, (∑ r, ∑ k, (b.repr (b i)) r * (b.repr u) k *
          connectionCoefficient (I := I) (M := M) (E := E)
            cov x₀ b l r k y) *
          inner ℝ ((trivializationAt E TM x₀).localFrame b l y)
            ((trivializationAt E TM x₀).localFrame b j y) =
        ∑ l, ∑ k, (b.repr u) k *
          connectionCoefficient (I := I) (M := M) (E := E)
            cov x₀ b l i k y *
          inner ℝ ((trivializationAt E TM x₀).localFrame b l y)
            ((trivializationAt E TM x₀).localFrame b j y) := by
    intro i j
    apply Finset.sum_congr rfl
    intro l hl
    simp only [Module.Basis.repr_self, Finsupp.single_apply]
    rw [Finset.sum_eq_single i]
    · rw [Finset.sum_mul]
      simp only [if_pos, one_mul]
    · intro c hc hci
      simp [Ne.symm hci]
    · intro hi
      exact (hi (Finset.mem_univ i)).elim
  have hPright' : ∀ i j : Fin (Module.finrank ℝ E),
      ∑ l, (∑ r, ∑ k, (b.repr (b j)) r * (b.repr u) k *
          connectionCoefficient (I := I) (M := M) (E := E)
            cov x₀ b l r k y) *
          inner ℝ ((trivializationAt E TM x₀).localFrame b i y)
            ((trivializationAt E TM x₀).localFrame b l y) =
        ∑ l, ∑ k, (b.repr u) k *
          connectionCoefficient (I := I) (M := M) (E := E)
            cov x₀ b l j k y *
          inner ℝ ((trivializationAt E TM x₀).localFrame b i y)
            ((trivializationAt E TM x₀).localFrame b l y) := by
    intro i j
    apply Finset.sum_congr rfl
    intro l hl
    simp only [Module.Basis.repr_self, Finsupp.single_apply]
    rw [Finset.sum_eq_single j]
    · rw [Finset.sum_mul]
      simp only [if_pos, one_mul]
    · intro c hc hcj
      simp [Ne.symm hcj]
    · intro hj
      exact (hj (Finset.mem_univ j)).elim
  simp_rw [hPleft', hPright']
  simp only [y]
  have hframe :=
    (metric_parallel_frame_terms
      (w := fun i : Fin (Module.finrank ℝ E) ↦ (b.repr (w t)) i)
      (v := fun j : Fin (Module.finrank ℝ E) ↦ (b.repr (v t)) j)
      (u := fun k : Fin (Module.finrank ℝ E) ↦ (b.repr u) k)
      (Γ := fun i l k ↦
        connectionCoefficient (I := I) (M := M) (E := E)
          cov x₀ b i l k (γ t))
      (G := fun i j ↦
        inner ℝ
          ((trivializationAt E TM x₀).localFrame b i (γ t))
          ((trivializationAt E TM x₀).localFrame b j (γ t))))
  calc
    (∑ x, ∑ x_1,
        (((b.repr dw) x * (b.repr (v t)) x_1 +
              (b.repr (w t)) x * (b.repr dv) x_1) *
            inner ℝ ((trivializationAt E TM x₀).localFrame b x (γ t))
              ((trivializationAt E TM x₀).localFrame b x_1 (γ t)) +
          (b.repr (w t)) x * (b.repr (v t)) x_1 *
            ((∑ l, ∑ k, (b.repr u) k *
                connectionCoefficient (I := I) (M := M) (E := E)
                  cov x₀ b l x k (γ t) *
                inner ℝ ((trivializationAt E TM x₀).localFrame b l (γ t))
                  ((trivializationAt E TM x₀).localFrame b x_1 (γ t))) +
             (∑ l, ∑ k, (b.repr u) k *
                connectionCoefficient (I := I) (M := M) (E := E)
                  cov x₀ b l x_1 k (γ t) *
                inner ℝ ((trivializationAt E TM x₀).localFrame b x (γ t))
                  ((trivializationAt E TM x₀).localFrame b l (γ t)))))) =
        (∑ x, ∑ x_1,
          ((b.repr dw) x * (b.repr (v t)) x_1 +
              (b.repr (w t)) x * (b.repr dv) x_1) *
            inner ℝ ((trivializationAt E TM x₀).localFrame b x (γ t))
              ((trivializationAt E TM x₀).localFrame b x_1 (γ t))) +
        (∑ x, ∑ x_1,
          (b.repr (w t)) x * (b.repr (v t)) x_1 *
            ((∑ l, ∑ k, (b.repr u) k *
                connectionCoefficient (I := I) (M := M) (E := E)
                  cov x₀ b l x k (γ t) *
                inner ℝ ((trivializationAt E TM x₀).localFrame b l (γ t))
                  ((trivializationAt E TM x₀).localFrame b x_1 (γ t))) +
             (∑ l, ∑ k, (b.repr u) k *
                connectionCoefficient (I := I) (M := M) (E := E)
                  cov x₀ b l x_1 k (γ t) *
                inner ℝ ((trivializationAt E TM x₀).localFrame b x (γ t))
                  ((trivializationAt E TM x₀).localFrame b l (γ t))))) := by
      simp_rw [Finset.sum_add_distrib]
    _ = (∑ x, ∑ x_1,
          ((b.repr dw) x * (b.repr (v t)) x_1 +
              (b.repr (w t)) x * (b.repr dv) x_1) *
            inner ℝ ((trivializationAt E TM x₀).localFrame b x (γ t))
              ((trivializationAt E TM x₀).localFrame b x_1 (γ t))) +
        ∑ x, ∑ x_1,
          (((∑ l, ∑ k, (b.repr (w t) l) * (b.repr u) k *
              connectionCoefficient (I := I) (M := M) (E := E)
                cov x₀ b x l k (γ t)) * (b.repr (v t) x_1) +
            (b.repr (w t)) x * (∑ l, ∑ k, (b.repr (v t) l) *
              (b.repr u) k * connectionCoefficient (I := I) (M := M) (E := E)
                cov x₀ b x_1 l k (γ t))) *
            inner ℝ ((trivializationAt E TM x₀).localFrame b x (γ t))
              ((trivializationAt E TM x₀).localFrame b x_1 (γ t))) := by
      rw [hframe]
    _ =
        ∑ x, ∑ x_1,
          ((b.repr dw) x + ∑ l, ∑ k, (b.repr (w t)) l * (b.repr u) k *
              connectionCoefficient (I := I) (M := M) (E := E)
                cov x₀ b x l k (γ t)) * (b.repr (v t)) x_1 *
            inner ℝ ((trivializationAt E TM x₀).localFrame b x (γ t))
              ((trivializationAt E TM x₀).localFrame b x_1 (γ t)) +
        ∑ x, ∑ x_1,
          (b.repr (w t)) x * ((b.repr dv) x_1 + ∑ l, ∑ k,
              (b.repr (v t)) l * (b.repr u) k *
                connectionCoefficient (I := I) (M := M) (E := E)
                  cov x₀ b x_1 l k (γ t)) *
            inner ℝ ((trivializationAt E TM x₀).localFrame b x (γ t))
              ((trivializationAt E TM x₀).localFrame b x_1 (γ t)) := by
      ring_nf
      simp_rw [Finset.sum_add_distrib]
      ring

end LocalGeodesicData
end BonnetMyersEntry
