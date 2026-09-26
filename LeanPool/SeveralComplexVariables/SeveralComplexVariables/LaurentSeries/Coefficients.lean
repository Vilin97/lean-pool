/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Mathlib.Topology.LocallyConstant.Basic
public import LeanPool.SeveralComplexVariables.SeveralComplexVariables.LaurentSeries.Neighborhoods
public import LeanPool.SeveralComplexVariables.SeveralComplexVariables.LaurentSeries.ProductCoefficients
public import LeanPool.SeveralComplexVariables.SeveralComplexVariables.Reinhardt.Hull
public import LeanPool.SeveralComplexVariables.SeveralComplexVariables.ZeroSets.Connected

/-!
# Global Laurent coefficients on Reinhardt domains

The space of admissible positive radii is connected. Local independence on circular product
neighborhoods therefore gives global independence of the coefficient torus.

## Main results

`IsReinhardt.isConnected_positive_radii` is connectedness of the positive radius vectors in a
connected open Reinhardt domain. `multivariableLaurentCoeff_eq_of_radii` is independence of the
torus. `multivariableLaurentCoeff_neg_eq_zero` vanishes coefficients with a negative exponent in
a coordinate that meets a hyperplane.
-/

public noncomputable section

open Complex Set Metric Filter
open scoped Topology NNReal

namespace SeveralComplexVariables

/-- Positive radius vectors of a connected open Reinhardt domain form a connected set. -/
theorem IsReinhardt.isConnected_positive_radii {n : ℕ} {U : Set (Fin n → ℂ)}
    (hR : IsReinhardt U) (ho : IsOpen U) (hc : IsPreconnected U)
    {r : Fin n → ℝ} (hr : ∀ i, 0 < r i) (hrU : (fun i => (r i : ℂ)) ∈ U) :
    IsConnected {s : Fin n → ℝ | (∀ i, 0 < s i) ∧ (fun i => (s i : ℂ)) ∈ U} := by
  have hp : AnalyticOnNhd ℂ (fun z : Fin n → ℂ => ∏ i, z i) U := by
    intro z _
    apply Finset.analyticAt_fun_prod
    intro i _
    exact (ContinuousLinearMap.proj (R := ℂ) i).analyticAt z
  have hconn := isConnected_nonzero_of_analyticOnNhd ho hc hp
    ⟨fun i => (r i : ℂ), hrU, Finset.prod_ne_zero_iff.mpr (fun i _ => by exact_mod_cast (hr i).ne')⟩
  have he : (fun z : Fin n → ℂ => fun i => ‖z i‖) '' (U \ (fun z => ∏ i, z i) ⁻¹' {0}) =
      {s : Fin n → ℝ | (∀ i, 0 < s i) ∧ (fun i => (s i : ℂ)) ∈ U} := by
    ext s
    constructor
    · rintro ⟨z, ⟨hz, hn⟩, rfl⟩
      have hn' : ∏ i, z i ≠ 0 := hn
      exact ⟨fun i => norm_pos_iff.mpr ((Finset.prod_ne_zero_iff.mp hn') i (Finset.mem_univ _)),
        hR hz (fun i => by simp)⟩
    · rintro ⟨hs, hsU⟩
      refine ⟨fun i => (s i : ℂ), ⟨hsU, ?_⟩, ?_⟩
      · exact Finset.prod_ne_zero_iff.mpr (fun i _ => by exact_mod_cast (hs i).ne')
      · funext i; simp [abs_of_pos (hs i)]
  rw [← he]
  exact hconn.image _ (by fun_prop)

variable {n : ℕ} {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F] [CompleteSpace F]

/-- Laurent coefficients on a connected Reinhardt domain are independent of the torus. The proof
uses local Cauchy–Goursat and connectedness, not Laurent expansion. -/
theorem multivariableLaurentCoeff_eq_of_radii {U : Set (Fin n → ℂ)}
    (ho : IsOpen U) (hc : IsPreconnected U) (hR : IsReinhardt U)
    {f : (Fin n → ℂ) → F} (hf : AnalyticOnNhd ℂ f U)
    {r s : Fin n → ℝ} (hr : ∀ i, 0 < r i) (hs : ∀ i, 0 < s i)
    (hrU : (fun i => (r i : ℂ)) ∈ U) (hsU : (fun i => (s i : ℂ)) ∈ U) :
    multivariableLaurentCoeff f s = multivariableLaurentCoeff f r := by
  let D : Set (Fin n → ℝ) := {t | (∀ i, 0 < t i) ∧ (fun i => (t i : ℂ)) ∈ U}
  have hD : IsConnected D := hR.isConnected_positive_radii ho hc hr hrU
  let : PreconnectedSpace D := isPreconnected_iff_preconnectedSpace.mp hD.isPreconnected
  let g : D → ((Fin n → ℤ) → F) := fun t => multivariableLaurentCoeff f t.val
  have hg : IsLocallyConstant g := by
    apply (IsLocallyConstant.iff_eventually_eq g).mpr
    intro t
    obtain ⟨V, hVo, hVc, hVr, htV, hVU⟩ :=
      hR.exists_circular_product_neighborhood ho t.property.2
    have hv : IsOpen (Set.pi univ V) := isOpen_set_pi finite_univ (fun i _ => hVo i)
    have ht : ∀ᶠ u : D in 𝓝 t, (fun i => (u.val i : ℂ)) ∈ Set.pi univ V :=
      (hv.preimage (continuous_pi fun i => Complex.continuous_ofReal.comp
        ((continuous_apply i).comp continuous_subtype_val))).mem_nhds htV
    filter_upwards [ht] with u hu
    exact multivariableLaurentCoeff_eq_on_product hVo hVc hVr (hf.mono hVU)
      t.property.1 u.property.1 (fun i => htV i (mem_univ _)) (fun i => hu i (mem_univ _))
  exact hg.apply_eq_of_preconnectedSpace ⟨s, hs, hsU⟩ ⟨r, hr, hrU⟩

/-- Meeting a coordinate hyperplane forces every negative coefficient in that coordinate to vanish.
This follows from the circle Cauchy theorem on a local product neighborhood. -/
theorem multivariableLaurentCoeff_neg_eq_zero {U : Set (Fin n → ℂ)}
    (ho : IsOpen U) (hc : IsPreconnected U) (hR : IsReinhardt U)
    {f : (Fin n → ℂ) → F} (hf : AnalyticOnNhd ℂ f U)
    {r : Fin n → ℝ} (hr : ∀ i, 0 < r i) (hrU : (fun i => (r i : ℂ)) ∈ U)
    (m : Fin n → ℤ) (i : Fin n) (hzero : ∃ z ∈ U, z i = 0) (hm : m i < 0) :
    multivariableLaurentCoeff f r m = 0 := by
  obtain ⟨z, hz, hzi⟩ := hzero
  obtain ⟨V, hVo, hVc, hVr, hzV, hVU⟩ := hR.exists_circular_product_neighborhood ho hz
  have hprod : IsReinhardt (Set.pi univ V) := by
    intro x hx y hy j _
    exact hVr j _ (hx j (mem_univ _)) _ (hy j)
  obtain ⟨s, hsV, hs⟩ := hprod.exists_strict_modulus_majorant
    (isOpen_set_pi finite_univ (fun i _ => hVo i)) hzV
  have hspos (j : Fin n) : 0 < (s j : ℝ) := by
    exact_mod_cast (show (0 : ℝ≥0) ≤ ‖z j‖₊ from zero_le).trans_lt (hs j)
  have he := multivariableLaurentCoeff_eq_of_radii ho hc hR hf hr hspos hrU (hVU hsV)
  rw [← he]
  exact multivariableLaurentCoeff_neg_on_product hVo hVc hVr (hf.mono hVU) hspos
    (fun j => hsV j (mem_univ _)) m i (by simpa only [hzi] using hzV i (mem_univ _)) hm

end SeveralComplexVariables

/- Adapted for Lean Pool: module imports and compatibility with its pinned toolchain. -/
