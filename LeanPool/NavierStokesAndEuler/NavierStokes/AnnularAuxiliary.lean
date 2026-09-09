/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.NavierStokes.ParametricRadialExtension
public import LeanPool.NavierStokesAndEuler.NavierStokes.TransportPrimitive

@[expose] public section

/-!+# Smooth auxiliary fields for an annulus

The maps constructed here agree with the physical fields on an open positive
annulus and are globally smooth. Absolute histories from the axis are not
preserved by clamping. The final section proves the correct transfer statement:
supported edit differences, including their nonlinear density integrals, are
unchanged when transplanted back to the original field.
-/

noncomputable section

open Set Filter MeasureTheory
open scoped ContDiff Topology

namespace NavierStokes.AnnularAuxiliary

noncomputable def positiveMap (a X : ℝ) : ℝ :=
  a + TransportPrimitive.cutoff (a / 2) a X * (X - a)

theorem positiveMap_contDiff (a : ℝ) : ContDiff ℝ ∞ (positiveMap a) :=
  contDiff_const.add ((TransportPrimitive.cutoff_contDiff _ _).mul
    (contDiff_id.sub contDiff_const))

theorem positiveMap_eq {a X : ℝ} (ha : 0 < a) (hX : a ≤ X) : positiveMap a X = X := by
  rw [positiveMap, TransportPrimitive.cutoff_one (by linarith) hX]
  ring

theorem positiveMap_pos {a : ℝ} (ha : 0 < a) (X : ℝ) : 0 < positiveMap a X := by
  by_cases hX : X ≤ a / 2
  · rw [positiveMap, TransportPrimitive.cutoff_zero (by linarith) hX, zero_mul, add_zero]
    exact ha
  · by_cases hXa : a ≤ X
    · rw [positiveMap_eq ha hXa]
      exact ha.trans_le hXa
    · have hc := (TransportPrimitive.cutoff_mem_Icc (a / 2) a X).2
      have hm := mul_le_mul_of_nonneg_right hc (sub_nonneg.mpr (le_of_not_ge hXa))
      dsimp [positiveMap]
      nlinarith

noncomputable def auxiliary {S : Set ℝ}
    (w : ParametricRadialExtension.ParameterWindow S) (a : ℝ)
    (F : ℝ × ℝ → ℝ) (p : ℝ × ℝ) : ℝ :=
  F (positiveMap a p.1, w.parameterMap p.2)

theorem auxiliary_contDiff {S : Set ℝ}
    (w : ParametricRadialExtension.ParameterWindow S) {a : ℝ} (ha : 0 < a)
    {F : ℝ × ℝ → ℝ} (hF : ContDiffOn ℝ ∞ F (Ioi 0 ×ˢ S)) :
    ContDiff ℝ ∞ (auxiliary w a F) :=
  hF.comp_contDiff (((positiveMap_contDiff a).comp contDiff_fst).prodMk
    (w.parameterMap_contDiff.comp contDiff_snd))
    (fun p => ⟨positiveMap_pos ha p.1, w.parameterMap_mem p.2⟩)

theorem auxiliary_eq {S : Set ℝ}
    (w : ParametricRadialExtension.ParameterWindow S) {a : ℝ} (ha : 0 < a)
    (F : ℝ × ℝ → ℝ) {p : ℝ × ℝ} (hX : a ≤ p.1) (heta : |p.2| ≤ w.inner) :
    auxiliary w a F p = F p := by
  rw [auxiliary, positiveMap_eq ha hX, w.parameterMap_eq heta]

theorem auxiliary_germ {S : Set ℝ}
    (w : ParametricRadialExtension.ParameterWindow S) {a : ℝ} (ha : 0 < a)
    (F : ℝ × ℝ → ℝ) {p : ℝ × ℝ} (hX : a < p.1) (heta : |p.2| < w.inner) :
    auxiliary w a F =ᶠ[𝓝 p] F := by
  filter_upwards [(isOpen_Ioi.prod isOpen_Ioo).mem_nhds ⟨hX, abs_lt.mp heta⟩] with q hq
  exact auxiliary_eq w ha F hq.1.le (abs_lt.mpr hq.2).le

theorem auxiliary_jets {S : Set ℝ}
    (w : ParametricRadialExtension.ParameterWindow S) {a : ℝ} (ha : 0 < a)
    (F : ℝ × ℝ → ℝ) (m : ℕ) {p : ℝ × ℝ}
    (hX : a < p.1) (heta : |p.2| < w.inner) :
    iteratedFDeriv ℝ m (auxiliary w a F) p = iteratedFDeriv ℝ m F p := by
  have he := auxiliary_germ w ha F hX heta
  have hu : auxiliary w a F =ᶠ[𝓝[univ] p] F := by simpa using he
  simpa only [iteratedFDerivWithin_univ] using hu.iteratedFDerivWithin_eq he.eq_of_nhds m

section Transplant

variable {α E V : Type*} [AddCommGroup E] [AddCommGroup V]

/-- Transplant only the edit. The original field carries the unchanged
history between the axis and the edit window. -/
noncomputable def transplant (base aux replacement : α → E) (x : α) : E :=
  base x + (replacement x - aux x)

theorem transplant_outside {base aux replacement : α → E} {x : α}
    (hx : replacement x = aux x) : transplant base aux replacement x = base x := by
  simp only [transplant, hx, sub_self, add_zero]

theorem transplant_inside {base aux replacement : α → E} {x : α}
    (hx : base x = aux x) : transplant base aux replacement x = replacement x := by
  rw [transplant, hx]
  abel

/-- Arbitrary nonlinear density changes transfer pointwise. This includes
quadratic energy, transport, and pressure densities. -/
theorem transplant_density_difference (H : α → E → V)
    {base aux replacement : α → E} {K : Set α}
    (hbase : EqOn base aux K) (hedit : ∀ x ∉ K, replacement x = aux x) (x : α) :
    H x (transplant base aux replacement x) - H x (base x) =
      H x (replacement x) - H x (aux x) := by
  by_cases hx : x ∈ K
  · rw [transplant_inside (hbase hx), hbase hx]
  · rw [transplant_outside (hedit x hx), hedit x hx, sub_self, sub_self]

end Transplant

theorem transplant_contDiffOn {D : Set (ℝ × ℝ)} {base aux replacement : ℝ × ℝ → ℝ}
    (hb : ContDiffOn ℝ ∞ base D) (ha : ContDiff ℝ ∞ aux) (hr : ContDiff ℝ ∞ replacement) :
    ContDiffOn ℝ ∞ (transplant base aux replacement) D :=
  hb.add (hr.sub ha).contDiffOn

theorem transplanted_density_integral
    {E V : Type*} [AddCommGroup E] [NormedAddCommGroup V] [NormedSpace ℝ V]
    (H : (ℝ × ℝ) → E → V) {base aux replacement : ℝ × ℝ → E} {K : Set (ℝ × ℝ)}
    (hbase : EqOn base aux K) (hedit : ∀ x ∉ K, replacement x = aux x) (X eta : ℝ) :
    (∫ r in (0 : ℝ)..X, H (r, eta) (transplant base aux replacement (r, eta)) - H (r, eta) (base
      (r, eta))) =
      ∫ r in (0 : ℝ)..X, H (r, eta) (replacement (r, eta)) - H (r, eta) (aux (r, eta)) := by
  apply intervalIntegral.integral_congr
  intro r _
  exact transplant_density_difference H hbase hedit (r, eta)

end NavierStokes.AnnularAuxiliary
