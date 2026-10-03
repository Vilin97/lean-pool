/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.Integration.HMinusMeasurable

/-! # Centering on the unit cube

`centerCell h = h - ⨍_{(0,1)²} h` is the mean-zero part of an `L²` function on the unit cube.  This
generic API is used by the grouped mean-zero assembly of `BigBoundInputs` (the grouped mean-zero
    decomposition (12)–(18)):
three terms (`twistie4`, `twistie5`, `normie3`) need not be individually mean zero, only their sum
is; their *centered* versions are mean zero, are bounded in `HDot⁻¹` through the `L²` estimate,
    and the
centered family has the same pointwise sum as the original one.

* `centerCell_meanZero`, `l2NormSq_centerCell_le`: mean zero and `L²` non-expansiveness;
* `sum_centerCell_eq_of_meanZero`, `centerCell_add_add`: centering a family whose sum has mean zero
  does not change the sum;
* `continuousOn_centerCell`: centering preserves joint continuity on `(0,1) × ℝ²`. -/

@[expose] public section

open MeasureTheory Homogenization Filter Topology

noncomputable section

namespace AVenhance.Infra.Section5.Integration

open AVenhance AVenhance.Infra.Section5

/-- The unit cube has volume one. -/
theorem volume_unitCube : volume unitCube = 1 := by
  unfold unitCube
  rw [volume_pi, Measure.pi_pi]
  simp [Real.volume_Ioo]

instance : IsFiniteMeasure (volume.restrict unitCube) :=
  ⟨by simp [volume_unitCube]⟩

/-- `h` minus its mean over the unit cube. -/
def centerCell (h : Vec 2 → ℝ) (x : Vec 2) : ℝ := h x - ∫ y in unitCube, h y

/-- An `L²` function on the unit cube is integrable there. -/
theorem integrableOn_unitCube_of_memL2On {h : Vec 2 → ℝ} (hh : MemL2On unitCube h) :
    IntegrableOn h unitCube :=
  hh.integrable (by norm_num)

/-- The mean of a function over the unit cube is the integral (volume one). -/
theorem integral_centerCell {h : Vec 2 → ℝ} (hh : MemL2On unitCube h) :
    ∫ x in unitCube, centerCell h x = 0 := by
  unfold centerCell
  rw [integral_sub (integrableOn_unitCube_of_memL2On hh) (integrable_const _), setIntegral_const]
  simp [Measure.real, volume_unitCube]

/-- The centered function has mean zero on the unit cube. -/
theorem centerCell_meanZero {h : Vec 2 → ℝ} (hh : MemL2On unitCube h) :
    MeanZeroOn unitCube (centerCell h) :=
  integral_centerCell hh

/-- The centered function is `L²` on the unit cube. -/
theorem memL2On_centerCell {h : Vec 2 → ℝ} (hh : MemL2On unitCube h) :
    MemL2On unitCube (centerCell h) :=
  hh.sub (memLp_const _)

/-- Centering is `L²`-nonexpansive: `‖h - ⨍ h‖² = ‖h‖² - (⨍ h)² ≤ ‖h‖²`. -/
theorem l2NormSq_centerCell_le {h : Vec 2 → ℝ} (hh : MemL2On unitCube h) :
    l2NormSq (centerCell h) ≤ l2NormSq h := by
  set c : ℝ := ∫ y in unitCube, h y with hc
  have h1 : IntegrableOn h unitCube := integrableOn_unitCube_of_memL2On hh
  have h2 : IntegrableOn (fun x => h x ^ 2) unitCube := hh.integrable_sq
  have hexp : l2NormSq (centerCell h) = l2NormSq h - c ^ 2 := by
    have hpt : ∀ x, centerCell h x ^ 2 = h x ^ 2 - (2 * c) * h x + c ^ 2 := fun x => by
      unfold centerCell
      rw [← hc]
      ring
    unfold l2NormSq
    simp_rw [hpt]
    have e1 : ∫ x in unitCube, (h x ^ 2 - (2 * c) * h x + c ^ 2) =
        (∫ x in unitCube, (h x ^ 2 - (2 * c) * h x)) + ∫ _x in unitCube, c ^ 2 :=
      integral_add (h2.sub (h1.const_mul _)) (integrable_const _)
    have e2 : ∫ x in unitCube, (h x ^ 2 - (2 * c) * h x) =
        (∫ x in unitCube, h x ^ 2) - ∫ x in unitCube, (2 * c) * h x :=
      integral_sub h2 (h1.const_mul _)
    rw [e1, e2, integral_const_mul, setIntegral_const, ← hc]
    simp [Measure.real, volume_unitCube]
    ring
  rw [hexp]
  nlinarith [sq_nonneg c]

/-- Centering a finite family whose sum has mean zero does not change the sum. -/
theorem sum_centerCell_eq_of_meanZero {ι : Type*} (s : Finset ι) (h : ι → Vec 2 → ℝ)
    (hint : ∀ i ∈ s, IntegrableOn (h i) unitCube)
    (hsum : MeanZeroOn unitCube (fun x => ∑ i ∈ s, h i x)) (x : Vec 2) :
    ∑ i ∈ s, centerCell (h i) x = ∑ i ∈ s, h i x := by
  have hmean : ∑ i ∈ s, ∫ y in unitCube, h i y = 0 := by
    rw [← integral_finsetSum s hint]
    exact hsum
  unfold centerCell
  rw [Finset.sum_sub_distrib, hmean, sub_zero]

/-- Three-term version of `sum_centerCell_eq_of_meanZero`. -/
theorem centerCell_add_add {a b c : Vec 2 → ℝ} (ha : MemL2On unitCube a)
    (hb : MemL2On unitCube b) (hc : MemL2On unitCube c)
    (hsum : MeanZeroOn unitCube (fun x => a x + b x + c x)) (x : Vec 2) :
    centerCell a x + centerCell b x + centerCell c x = a x + b x + c x := by
  have ia := integrableOn_unitCube_of_memL2On ha
  have ib := integrableOn_unitCube_of_memL2On hb
  have ic := integrableOn_unitCube_of_memL2On hc
  have hmean : (∫ y in unitCube, a y) + (∫ y in unitCube, b y) + (∫ y in unitCube, c y) = 0 := by
    have h2 := integral_add (μ := volume.restrict unitCube) (f := fun y => a y + b y) (g := c)
      (ia.add ib) ic
    have h3 := integral_add (μ := volume.restrict unitCube) (f := a) (g := b) ia ib
    have hs : ∫ y in unitCube, (a y + b y + c y) = 0 := hsum
    linarith
  unfold centerCell
  linarith

/-- Centering preserves joint continuity on `(0,1) × ℝ²`. -/
theorem continuousOn_centerCell {F : ℝ → Vec 2 → ℝ}
    (hF : ContinuousOn (fun p : ℝ × Vec 2 => F p.1 p.2) (Set.Ioo (0 : ℝ) 1 ×ˢ Set.univ)) :
    ContinuousOn (fun p : ℝ × Vec 2 => centerCell (F p.1) p.2)
      (Set.Ioo (0 : ℝ) 1 ×ˢ Set.univ) := by
  have h1 : ContinuousOn (fun t => ∫ x in unitCube, F t x * (fun _ : Vec 2 => (1 : ℝ)) x)
      (Set.Ioo (0 : ℝ) 1) := continuousOn_pairing_of_continuousOn hF continuous_const
  simp only [mul_one] at h1
  have h2 : ContinuousOn (fun p : ℝ × Vec 2 => ∫ y in unitCube, F p.1 y)
      (Set.Ioo (0 : ℝ) 1 ×ˢ Set.univ) :=
    h1.comp continuousOn_fst fun p hp => hp.1
  exact hF.sub h2

end AVenhance.Infra.Section5.Integration
end
