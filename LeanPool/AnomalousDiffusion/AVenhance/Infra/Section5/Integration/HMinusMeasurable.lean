/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.HMinusTools
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.Integration.Statements
public import Mathlib.MeasureTheory.Measure.SeparableMeasure
public import Mathlib.MeasureTheory.Function.L2Space

/-! # Measurability of `t ↦ ‖F t‖_{HDot⁻¹}` via a countable family of tests

The `hMinusOneNorm` is a supremum over an uncountable family of smooth periodic tests.  On
`L²(unitCube)` it is already computed by a *countable* family of admissible tests: the classes of
the admissible tests in `Lp ℝ 2 (volume.restrict unitCube)` form a separable subset of a
second-countable space, and `φ ↦ ∫ g φ` is the (continuous) `L²` inner product with `g`.

Consequently, if the slices `F t` are `L²` and every continuous pairing `t ↦ ∫ F t φ` is
measurable, so is `t ↦ ‖F t‖_{HDot⁻¹}` (`aemeasurable_hMinusOneNorm`); and this applies to jointly
continuous `F` on `(0,1) × ℝ²` (`aemeasurable_hMinusOneNorm_of_continuousOn`). -/

@[expose] public section

open MeasureTheory Homogenization Filter Topology

noncomputable section

namespace AVenhance.Infra.Section5.Integration

open AVenhance AVenhance.Infra.Section5

/-! ### Continuous functions are `L²` on the cube -/

/-- Continuous functions are `L²` on the unit cube. -/
theorem memL2On_unitCube_of_continuous {f : Vec 2 → ℝ} (hf : Continuous f) :
    MemL2On unitCube f := by
  have h := Infra.Ergodic.continuous_unitCell_memLp_two hf
  rw [Measure.restrict_congr_set Infra.Torus.unitCell_ae_eq_unitCube] at h
  simpa using h

/-! ### A countable family of tests -/

/-- The admissible-test subtype of the definition of `hMinusOneNorm`. -/
abbrev HMinusTest : Type :=
  {φ : Vec 2 → ℝ // ContDiff ℝ (⊤ : ℕ∞) φ ∧ IsZ2Periodic φ ∧ gradNormSq (spaceGrad φ) ≤ 1}

/-- The `L²(unitCube)` class of an admissible test. -/
def HMinusTest.toLp (φ : HMinusTest) : Lp ℝ 2 (volume.restrict unitCube) :=
  (memL2On_unitCube_of_continuous φ.property.1.continuous).toLp φ.1

/-- The pairing `∫ g φ` of an `L²` function with a continuous function is an `L²` inner product. -/
theorem integral_mul_eq_inner {g φ : Vec 2 → ℝ} (hg : MemL2On unitCube g)
    (hφ : MemL2On unitCube φ) :
    ∫ x in unitCube, g x * φ x = inner ℝ (hg.toLp g) (hφ.toLp φ) := by
  rw [L2.inner_def]
  refine integral_congr_ae ?_
  filter_upwards [hg.coeFn_toLp, hφ.coeFn_toLp] with x hx1 hx2
  rw [hx1, hx2]
  simp [mul_comm]

/-- Continuity of `u ↦ ofReal |⟪g, u⟫|` on `L²`. -/
theorem continuous_ofReal_abs_inner (w : Lp ℝ 2 (volume.restrict unitCube)) :
    Continuous fun u : Lp ℝ 2 (volume.restrict unitCube) =>
      ENNReal.ofReal |inner ℝ w u| :=
  ENNReal.continuous_ofReal.comp (continuous_abs.comp (continuous_const.inner continuous_id))

/-- `L²` of the cube is second countable. -/
theorem secondCountable_L2_unitCube :
    SecondCountableTopology (Lp ℝ 2 (volume.restrict unitCube)) := by
  have h1 : Fact (1 ≤ (2 : ENNReal)) := ⟨by norm_num⟩
  have h2 : Fact ((2 : ENNReal) ≠ ⊤) := ⟨by norm_num⟩
  infer_instance

/-- The zero function is an admissible test. -/
def zeroHMinusTest : HMinusTest :=
  ⟨fun _ => 0, contDiff_const, fun _ _ => rfl, by simp [gradNormSq, spaceGrad, vecNormSq, vecDot]⟩

/-- A fixed countable family of admissible HDot⁻¹ tests computing the norm of every L² function. -/
theorem exists_countable_hMinusOneNorm_tests :
    ∃ φ : ℕ → Vec 2 → ℝ,
      (∀ n, ContDiff ℝ (⊤ : ℕ∞) (φ n) ∧ IsZ2Periodic (φ n) ∧ gradNormSq (spaceGrad (φ n)) ≤ 1) ∧
      ∀ g : Vec 2 → ℝ, MemL2On unitCube g →
        hMinusOneNorm g = ⨆ n, ENNReal.ofReal |∫ x in unitCube, g x * φ n x| := by
  have := secondCountable_L2_unitCube
  set S : Set (Lp ℝ 2 (volume.restrict unitCube)) := Set.range HMinusTest.toLp with hS
  obtain ⟨t, htS, htc, hSt⟩ :=
    (TopologicalSpace.IsSeparable.of_separableSpace S).exists_countable_dense_subset
  have ht0 : t.Nonempty := by
    by_contra hne
    rw [Set.not_nonempty_iff_eq_empty] at hne
    have h0 : zeroHMinusTest.toLp ∈ S := ⟨_, rfl⟩
    have := hSt h0
    simp [hne] at this
  obtain ⟨u, hu⟩ := htc.exists_eq_range ht0
  have hex : ∀ n, ∃ a : HMinusTest, a.toLp = u n := fun n => by
    have hun : u n ∈ t := hu ▸ Set.mem_range_self n
    exact htS hun
  choose a ha using hex
  refine ⟨fun n => (a n).1, fun n => (a n).2, fun g hg => ?_⟩
  apply le_antisymm
  · refine iSup_le fun φ => ?_
    have hclosed : IsClosed {v : Lp ℝ 2 (volume.restrict unitCube) |
        ENNReal.ofReal |inner ℝ (hg.toLp g) v| ≤
          ⨆ n, ENNReal.ofReal |∫ x in unitCube, g x * (a n).1 x|} :=
      isClosed_le (continuous_ofReal_abs_inner (hg.toLp g))
        (continuous_const (y := ⨆ n, ENNReal.ofReal |∫ x in unitCube, g x * (a n).1 x|))
    have htsub : t ⊆ {v : Lp ℝ 2 (volume.restrict unitCube) |
        ENNReal.ofReal |inner ℝ (hg.toLp g) v| ≤
          ⨆ n, ENNReal.ofReal |∫ x in unitCube, g x * (a n).1 x|} := by
      intro v hv
      rw [hu] at hv
      obtain ⟨n, rfl⟩ := hv
      change ENNReal.ofReal |inner ℝ (hg.toLp g) (u n)| ≤ _
      refine le_trans (le_of_eq ?_) (le_iSup
        (fun n => ENNReal.ofReal |∫ x in unitCube, g x * (a n).1 x|) n)
      rw [integral_mul_eq_inner hg (memL2On_unitCube_of_continuous (a n).2.1.continuous), ← ha n]
      rfl
    have hmem := hclosed.closure_subset_iff.mpr htsub (hSt ⟨φ, rfl⟩)
    refine le_trans (le_of_eq ?_) hmem
    rw [integral_mul_eq_inner hg (memL2On_unitCube_of_continuous φ.2.1.continuous)]
    rfl
  · exact iSup_le fun n => le_iSup (fun φ : HMinusTest =>
      ENNReal.ofReal |∫ x in unitCube, g x * φ.1 x|) (a n)

/-! ### Measurability in time -/

/-- The `HDot⁻¹` norm of `L²` slices is a.e. measurable once all continuous pairings are. -/
theorem aemeasurable_hMinusOneNorm {F : ℝ → Vec 2 → ℝ}
    (hL2 : ∀ t ∈ Set.Ioo (0 : ℝ) 1, MemL2On unitCube (F t))
    (hpair : ∀ φ : Vec 2 → ℝ, Continuous φ →
      AEMeasurable (fun t => ∫ x in unitCube, F t x * φ x)
        (MeasureTheory.volume.restrict (Set.Ioo (0 : ℝ) 1))) :
    AEMeasurable (fun t => hMinusOneNorm (F t))
      (MeasureTheory.volume.restrict (Set.Ioo (0 : ℝ) 1)) := by
  obtain ⟨φ, hφ, heq⟩ := exists_countable_hMinusOneNorm_tests
  have hsup : AEMeasurable (fun t => ⨆ n, ENNReal.ofReal |∫ x in unitCube, F t x * φ n x|)
      (MeasureTheory.volume.restrict (Set.Ioo (0 : ℝ) 1)) :=
    AEMeasurable.iSup fun n =>
      ENNReal.measurable_ofReal.comp_aemeasurable
        (continuous_abs.measurable.comp_aemeasurable (hpair (φ n) (hφ n).1.continuous))
  refine hsup.congr ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ht
  exact (heq _ (hL2 t ht)).symm

/-- Slices of a function jointly continuous on `(0,1) × ℝ²` are continuous. -/
theorem continuous_slice_of_continuousOn {F : ℝ → Vec 2 → ℝ}
    (hF : ContinuousOn (fun p : ℝ × Vec 2 => F p.1 p.2) (Set.Ioo (0 : ℝ) 1 ×ˢ Set.univ))
    {t : ℝ} (ht : t ∈ Set.Ioo (0 : ℝ) 1) : Continuous (F t) :=
  hF.comp_continuous (continuous_const.prodMk continuous_id) fun x => ⟨ht, Set.mem_univ x⟩

/-- Slices of a jointly continuous function are `L²` on the cube. -/
theorem memL2On_of_continuousOn_slice {F : ℝ → Vec 2 → ℝ}
    (hF : ContinuousOn (fun p : ℝ × Vec 2 => F p.1 p.2) (Set.Ioo (0 : ℝ) 1 ×ˢ Set.univ))
    {t : ℝ} (ht : t ∈ Set.Ioo (0 : ℝ) 1) : MemL2On unitCube (F t) :=
  memL2On_unitCube_of_continuous (continuous_slice_of_continuousOn hF ht)

/-- The pairing of a jointly continuous function with a continuous test is continuous in time. -/
theorem continuousOn_pairing_of_continuousOn {F : ℝ → Vec 2 → ℝ}
    (hF : ContinuousOn (fun p : ℝ × Vec 2 => F p.1 p.2) (Set.Ioo (0 : ℝ) 1 ×ˢ Set.univ))
    {φ : Vec 2 → ℝ} (hφ : Continuous φ) :
    ContinuousOn (fun t => ∫ x in unitCube, F t x * φ x) (Set.Ioo (0 : ℝ) 1) := by
  set K : Set (Vec 2) := Set.pi Set.univ fun _ => Set.Icc (0 : ℝ) 1 with hK
  have hKc : IsCompact K := isCompact_univ_pi fun _ => isCompact_Icc
  have hae : unitCube =ᵐ[(volume : Measure (Vec 2))] K := by
    simpa [unitCube, hK, volume_pi] using
      (Measure.univ_pi_Ioo_ae_eq_Icc (f := fun _ : Fin 2 => (0 : ℝ))
        (g := fun _ : Fin 2 => (1 : ℝ)))
  have hcont : Continuous (Function.uncurry fun (u : Set.Ioo (0 : ℝ) 1) (x : Vec 2) =>
      F u x * φ x) := by
    have h1 : Continuous fun p : Set.Ioo (0 : ℝ) 1 × Vec 2 => F p.1.1 p.2 :=
      hF.comp_continuous ((continuous_subtype_val.comp continuous_fst).prodMk continuous_snd)
        fun p => ⟨p.1.2, Set.mem_univ _⟩
    exact h1.mul (hφ.comp continuous_snd)
  have : LocallyCompactSpace (Set.Ioo (0 : ℝ) 1) := isOpen_Ioo.locallyCompactSpace
  have hc := continuous_parametric_integral_of_continuous (μ := volume) hcont hKc
  rw [continuousOn_iff_continuous_domRestrict]
  convert hc using 2 with u
  exact setIntegral_congr_set hae

/-- The `HDot⁻¹` norm is a.e. measurable in time for functions jointly continuous on
`(0,1) × ℝ²`. -/
theorem aemeasurable_hMinusOneNorm_of_continuousOn {F : ℝ → Vec 2 → ℝ}
    (hF : ContinuousOn (fun p : ℝ × Vec 2 => F p.1 p.2) (Set.Ioo (0 : ℝ) 1 ×ˢ Set.univ)) :
    AEMeasurable (fun t => hMinusOneNorm (F t))
      (MeasureTheory.volume.restrict (Set.Ioo (0 : ℝ) 1)) :=
  aemeasurable_hMinusOneNorm (fun _ ht => memL2On_of_continuousOn_slice hF ht)
    fun _ hφ => (continuousOn_pairing_of_continuousOn hF hφ).aemeasurable measurableSet_Ioo

end AVenhance.Infra.Section5.Integration
end
