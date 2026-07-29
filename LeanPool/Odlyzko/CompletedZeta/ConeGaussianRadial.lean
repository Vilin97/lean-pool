/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import LeanPool.Odlyzko.CompletedZeta.ConeGaussianInterchange
public import LeanPool.Odlyzko.CompletedZeta.UnitDecomposition

/-! TODO: Add doc-string. -/

@[expose] public section

noncomputable section

open Complex MeasureTheory NumberField NumberField.InfinitePlace Set

namespace NumberField.Odlyzko

open mixedEmbedding mixedEmbedding.fundamentalCone

variable (K : Type*) [Field K] [NumberField K]

open Classical in
/-- A complex place positive orthant used in the Odlyzko-bound argument. -/
abbrev complexPlacePositiveOrthant :
    Set (InfinitePlace K → ℝ) :=
  Set.univ.pi fun _ ↦ Set.Ioi 0

open Classical in
theorem expMapBasis_image_univ :
    expMapBasis '' (Set.univ : Set (realSpace K)) =
      complexPlacePositiveOrthant K := by
  ext q
  constructor
  · rintro ⟨x, -, rfl⟩
    exact Set.mem_univ_pi.mpr fun w ↦ expMapBasis_pos x w
  · intro hq
    have hpos : ∀ w, 0 < q w :=
      Set.mem_univ_pi.mp hq
    have htarget :
        q ∈ expMapBasis.target :=
      Set.mem_univ_pi.mpr hpos
    exact ⟨expMapBasis.symm q, Set.mem_univ _,
      expMapBasis.right_inv htarget⟩

open Classical in
theorem pi_restrict_Ioi_eq_volume_restrict_positiveOrthant :
    Measure.pi
        (fun _ : InfinitePlace K ↦
          (volume : Measure ℝ).restrict (Set.Ioi 0)) =
      (volume : Measure (InfinitePlace K → ℝ)).restrict
        (complexPlacePositiveOrthant K) := by
  rw [← Measure.restrict_pi_pi, ← MeasureTheory.volume_pi]

open Classical in
/-- A complex place radial jacobian used in the Odlyzko-bound argument. -/
noncomputable def complexPlaceRadialJacobian
    (q : InfinitePlace K → ℝ) : ℝ :=
  mixedEmbedding.norm (mixedSpaceOfRealSpace q) *
    (∏ w : {w : InfinitePlace K // IsComplex w}, q w.1)⁻¹ *
    2⁻¹ ^ nrComplexPlaces K * Module.finrank ℚ K *
    NumberField.Units.regulator K

open Classical in
theorem complexPlaceRadialJacobian_expMapBasis
    (y : realSpace K) :
    complexPlaceRadialJacobian K (expMapBasis y) =
      Real.exp
          (y NumberField.Units.dirichletUnitTheorem.w₀ *
            Module.finrank ℚ K) *
        (∏ w : {w : InfinitePlace K // IsComplex w},
          expMapBasis y w.1)⁻¹ *
        2⁻¹ ^ nrComplexPlaces K * Module.finrank ℚ K *
        NumberField.Units.regulator K := by
  rw [complexPlaceRadialJacobian, norm_expMapBasis,
    ← Real.exp_nat_mul]
  grind

open Classical in
theorem integral_positiveOrthant_eq_expMapBasis
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : (InfinitePlace K → ℝ) → E) :
    (∫ q : InfinitePlace K → ℝ, f q
      ∂Measure.pi (fun _ ↦ volume.restrict (Set.Ioi 0))) =
      ∫ y : realSpace K,
        complexPlaceRadialJacobian K (expMapBasis y) •
          f (expMapBasis y) := by
  rw [pi_restrict_Ioi_eq_volume_restrict_positiveOrthant K]
  change (∫ q in complexPlacePositiveOrthant K, f q) = _
  rw [← expMapBasis_image_univ K]
  simpa only [setIntegral_univ,
    complexPlaceRadialJacobian_expMapBasis] using
    setIntegral_expMapBasis_image (K := K) MeasurableSet.univ
      f

open Classical in
theorem integral_complexPlaceMellinGaussian_eq_expMapBasis
    (x : K) (s : ℂ) :
    (∫ q : InfinitePlace K → ℝ,
      complexPlaceMellinGaussian K x s q
      ∂Measure.pi (fun _ ↦ volume.restrict (Set.Ioi 0))) =
      ∫ y : realSpace K,
        complexPlaceRadialJacobian K (expMapBasis y) •
          complexPlaceMellinGaussian K x s (expMapBasis y) :=
  integral_positiveOrthant_eq_expMapBasis K
    (complexPlaceMellinGaussian K x s)

open Classical in
theorem complexPlaceRadialJacobian_expMapBasis_pos
    (y : realSpace K) :
    0 < complexPlaceRadialJacobian K (expMapBasis y) := by
  rw [complexPlaceRadialJacobian_expMapBasis]
  have hprod :
      0 < ∏ w : {w : InfinitePlace K // IsComplex w},
        expMapBasis y w.1 :=
    Finset.prod_pos fun _ _ ↦ expMapBasis_pos _ _
  have hfin : 0 < (Module.finrank ℚ K : ℝ) := by
    exact_mod_cast Module.finrank_pos
  have hinv :
      0 < (∏ w : {w : InfinitePlace K // IsComplex w},
        expMapBasis y w.1)⁻¹ :=
    inv_pos.mpr hprod
  have htwo : 0 < (2⁻¹ : ℝ) ^ nrComplexPlaces K :=
    pow_pos (by positivity) _
  exact mul_pos
    (mul_pos (mul_pos (mul_pos (Real.exp_pos _) hinv) htwo) hfin)
    (NumberField.Units.regulator_pos K)

open Classical in
/-- A radial mellin gaussian used in the Odlyzko-bound argument. -/
noncomputable def radialMellinGaussian
    (x : K) (s : ℂ) (y : realSpace K) : ℂ :=
  complexPlaceRadialJacobian K (expMapBasis y) •
    complexPlaceMellinGaussian K x s (expMapBasis y)

open Classical in
theorem integrable_complexPlaceRadialJacobian_smul_mellinGaussian
    {x : K} (hx : x ≠ 0) {s : ℂ} (hs : 0 < s.re) :
    Integrable (radialMellinGaussian K x s) := by
  have hk := integrable_complexPlaceMellinGaussian K hx hs
  rw [pi_restrict_Ioi_eq_volume_restrict_positiveOrthant K] at hk
  have himage :
      IntegrableOn (complexPlaceMellinGaussian K x s)
        (expMapBasis '' (Set.univ : Set (realSpace K))) := by
    rw [expMapBasis_image_univ K]
    exact hk
  have hlog :=
    (integrableOn_expMapBasis_image_iff (K := K) MeasurableSet.univ
      (complexPlaceMellinGaussian K x s)).mp himage
  rw [integrableOn_univ] at hlog
  apply hlog.congr
  filter_upwards with y
  rw [radialMellinGaussian,
    complexPlaceRadialJacobian_expMapBasis]

open Classical in
theorem integral_norm_radialMellinGaussian
    (x : K) (s : ℂ) :
    (∫ y : realSpace K, ‖radialMellinGaussian K x s y‖) =
      ∫ q : InfinitePlace K → ℝ,
        ‖complexPlaceMellinGaussian K x s q‖
        ∂Measure.pi (fun _ ↦ volume.restrict (Set.Ioi 0)) := by
  rw [integral_positiveOrthant_eq_expMapBasis K
    (fun q ↦ ‖complexPlaceMellinGaussian K x s q‖)]
  apply integral_congr_ae
  filter_upwards with y
  rw [radialMellinGaussian, _root_.norm_smul,
    Real.norm_of_nonneg
      (complexPlaceRadialJacobian_expMapBasis_pos K y).le,
    smul_eq_mul]

variable [IsTotallyComplex K]

open Classical in
theorem prod_complexPlace_apply_unit_eq_one (u : (𝓞 K)ˣ) :
    ∏ w : {w : InfinitePlace K // IsComplex w},
      w.1 (((u : 𝓞 K) : K)) = 1 := by
  rw [← prod_infinitePlace_apply_unit_eq_one K u]
  symm
  simpa only [Finset.prod_const_one, Finset.prod_mul_distrib,
    Finset.prod_attach] using
    Finset.prod_subtype (Finset.univ : Finset (InfinitePlace K))
      (fun w ↦ by simp only [Finset.mem_univ, IsTotallyComplex.isComplex,
        iff_self]) (fun w ↦ w (((u : 𝓞 K) : K)))

open Classical in
theorem complexPlaceRadialJacobian_expMapBasis_add_unitCoordinateShift
    (y : realSpace K)
    (z : {w : InfinitePlace K //
      w ≠ NumberField.Units.dirichletUnitTheorem.w₀} → ℤ) :
    complexPlaceRadialJacobian K
        (expMapBasis (y + unitCoordinateShift z)) =
      complexPlaceRadialJacobian K (expMapBasis y) := by
  rw [complexPlaceRadialJacobian_expMapBasis,
    complexPlaceRadialJacobian_expMapBasis,
    expMapBasis_add_unitCoordinateShift]
  have hradial :
      (y + unitCoordinateShift z)
          NumberField.Units.dirichletUnitTheorem.w₀ =
        y NumberField.Units.dirichletUnitTheorem.w₀ := by
    simp [unitCoordinateShift]
  rw [hradial]
  simp only [Pi.mul_apply, Finset.prod_mul_distrib]
  rw [prod_complexPlace_apply_unit_eq_one K, one_mul]

open Classical in
theorem radialMellinGaussian_add_unitCoordinateShift
    (x : K) (s : ℂ) (y : realSpace K)
    (z : {w : InfinitePlace K //
      w ≠ NumberField.Units.dirichletUnitTheorem.w₀} → ℤ) :
    radialMellinGaussian K x s (y + unitCoordinateShift z) =
      radialMellinGaussian K
        ((((fundamentalUnitForShift z : (𝓞 K)ˣ) : 𝓞 K) : K) * x)
        s y := by
  rw [radialMellinGaussian, radialMellinGaussian,
    complexPlaceRadialJacobian_expMapBasis_add_unitCoordinateShift,
    expMapBasis_add_unitCoordinateShift,
    complexPlaceMellinGaussian_fundamentalUnitForShift]

open Classical in
theorem integral_radialMellinGaussian_eq_tsum_unitSlab
    {x : K} (hx : x ≠ 0) {s : ℂ} (hs : 0 < s.re) :
    (∫ y : realSpace K, radialMellinGaussian K x s y) =
      ∑' z : {w : InfinitePlace K //
          w ≠ NumberField.Units.dirichletUnitTheorem.w₀} → ℤ,
        ∫ y in unitFundamentalParamSet K,
          radialMellinGaussian K
            ((((fundamentalUnitForShift z : (𝓞 K)ˣ) : 𝓞 K) : K) * x)
            s y := by
  let g : realSpace K → ℂ := fun q ↦
    complexPlaceRadialJacobian K q •
      complexPlaceMellinGaussian K x s q
  have hunfold := integral_comp_expMapBasis_eq_tsum_unitSlab g
    (integrable_complexPlaceRadialJacobian_smul_mellinGaussian K hx hs)
  calc
    (∫ y : realSpace K, radialMellinGaussian K x s y) =
        ∑' z : {w : InfinitePlace K //
            w ≠ NumberField.Units.dirichletUnitTheorem.w₀} → ℤ,
          ∫ y in unitFundamentalParamSet K,
            g ((fun w ↦
              w (((fundamentalUnitForShift z : (𝓞 K)ˣ) : 𝓞 K) : K)) *
              expMapBasis y) := by
      simpa only [g, radialMellinGaussian] using hunfold
    _ = _ := by
      congr 1
      funext z
      apply setIntegral_congr_fun measurableSet_unitFundamentalParamSet
      intro y _
      dsimp only [g]
      rw [← expMapBasis_add_unitCoordinateShift]
      change radialMellinGaussian K x s
        (y + unitCoordinateShift z) = _
      exact radialMellinGaussian_add_unitCoordinateShift K x s y z

end NumberField.Odlyzko
