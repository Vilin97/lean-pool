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

public import LeanPool.PoincareGeometry.AlmostSchur.L2BilinearIntegral

/-! # Finite scalar L² families as Euclidean-valued L² fields -/

@[expose] public noncomputable section
open MeasureTheory Set Filter
open scoped BigOperators

namespace AlmostSchur

variable {α : Type*} [MeasurableSpace α] {μ : Measure α}
  {ι : Type*} [Fintype ι]

/-- Assemble actual scalar representatives into a Euclidean-valued L² field. -/
def l2FiniteFamily (u : ι → Lp ℝ 2 μ) : Lp (EuclideanSpace ℝ ι) 2 μ :=
  (MemLp.of_eval_piLp (fun i => Lp.memLp (u i)) :
    MemLp (fun x => WithLp.toLp 2 (fun i => u i x)) 2 μ).toLp _

theorem l2FiniteFamily_ae_eq (u : ι → Lp ℝ 2 μ) :
    l2FiniteFamily u =ᵐ[μ] (fun x => WithLp.toLp 2 (fun i => u i x)) :=
  (MemLp.of_eval_piLp (fun i => Lp.memLp (u i)) :
    MemLp (fun x => WithLp.toLp 2 (fun i => u i x)) 2 μ).coeFn_toLp

/-- The assembled field has the square-sum norm used by the test graph. -/
theorem norm_l2FiniteFamily (u : ι → Lp ℝ 2 μ) :
    ‖l2FiniteFamily u‖ = Real.sqrt (∑ i, ‖u i‖ ^ 2) := by
  have he : ‖l2FiniteFamily u‖ ^ 2 = ∑ i, ‖u i‖ ^ 2 := by
    simp_rw [← real_inner_self_eq_norm_sq, L2.inner_def]
    rw [← integral_finsetSum _ (fun i _ => L2.integrable_inner (u i) (u i))]
    apply integral_congr_ae
    filter_upwards [l2FiniteFamily_ae_eq u] with x hx
    simp only [real_inner_self_eq_norm_sq, hx, EuclideanSpace.real_norm_sq_eq,
      Real.norm_eq_abs, sq_abs]
  rw [← he, Real.sqrt_sq_eq_abs, abs_norm]

/-- The graph derivative pairing is the Euclidean-valued L² pairing. -/
theorem inner_l2FiniteFamily (u v : ι → Lp ℝ 2 μ) :
    inner ℝ (l2FiniteFamily u) (l2FiniteFamily v) = ∑ i, inner ℝ (u i) (v i) := by
  simp_rw [L2.inner_def]
  rw [← integral_finsetSum _ (fun i _ => L2.integrable_inner (u i) (v i))]
  apply integral_congr_ae
  filter_upwards [l2FiniteFamily_ae_eq u, l2FiniteFamily_ae_eq v] with x hx hy
  rw [hx, hy]
  rfl

/-- Assembly respects addition as an equality of actual L² classes. -/
theorem l2FiniteFamily_add (u v : ι → Lp ℝ 2 μ) :
    l2FiniteFamily (fun i => u i + v i) = l2FiniteFamily u + l2FiniteFamily v := by
  apply Lp.ext
  filter_upwards [l2FiniteFamily_ae_eq (fun i => u i + v i), l2FiniteFamily_ae_eq u,
    l2FiniteFamily_ae_eq v, Lp.coeFn_add (l2FiniteFamily u) (l2FiniteFamily v),
    ae_all_iff.mpr (fun i => Lp.coeFn_add (u i) (v i))] with x hx hu hv hadd hsum
  rw [hx, hadd, Pi.add_apply, hu, hv]
  ext i
  exact hsum i

end AlmostSchur
