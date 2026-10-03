/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Ergodic.HMinusOne

/-! # Finite spectral support for the H⁻¹ ergodic split

These helpers sit above the shared torus Fourier API.  They do not define a
new Fourier transform or integration convention. -/

@[expose] public section

namespace AVenhance.Infra.Ergodic

open MeasureTheory
open Homogenization
open AVenhance.Infra.Torus

noncomputable section

/-- Use normalized Haar measure on the unit circle for periodic integrals. -/
local instance avInfraErgodicHMinusOneSpectralMeasureSpace1 : MeasureSpace UnitAddCircle :=
    ⟨AddCircle.haarAddCircle⟩
local instance avInfraErgodicHMinusOneSpectralMeasureIsAddHaarMeasure2 : Measure.IsAddHaarMeasure
    (volume : Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)
local instance avInfraErgodicHMinusOneSpectralIsProbabilityMeasure3 : IsProbabilityMeasure (volume
    : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

attribute [local instance] Measure.Subtype.measureSpace

/-- Move an `L²` function on a Euclidean unit cell to the normalized torus
using the existing product-cell measure-preserving equivalence. -/
theorem memLp_torusFunction_two_of_cellL2 {d : ℕ} {h : Vec d → ℂ}
    (hh : MemLp h (ENNReal.ofReal (2 : ℝ))
      ((volume : Measure (Vec d)).restrict (unitCell d))) :
    MemLp (torusFunction h) (ENNReal.ofReal (2 : ℝ))
      (volume : Measure (UnitAddTorus (Fin d))) := by
  let hs : MeasurableSet (unitCell d) := measurableSet_unitCell d
  have hmap : (volume : Measure (unitCell d)).map (Subtype.val : unitCell d → Vec d) =
      (volume : Measure (Vec d)).restrict (unitCell d) :=
    MeasurableSet.map_coe_volume hs
  rw [← hmap] at hh
  have hsub : MemLp (fun x : unitCell d => h x)
      (ENNReal.ofReal (2 : ℝ)) (volume : Measure (unitCell d)) := by
    exact (MeasurableEmbedding.subtype_coe hs).memLp_map_measure_iff.mp hh
  have hmp := UnitAddTorus.measurePreserving_equivPiIoc
    (a := fun _ : Fin d => (0 : ℝ))
  have htorus := hsub.comp_measurePreserving hmp
  convert htorus using 1
  rfl

theorem HMinusOneSpectral.periodicToTorusL2_fourierCoeff_eq_smooth {d : ℕ}
    {f : Vec d → ℂ} (hf : Continuous f) (k : Fin d → ℤ) :
    UnitAddTorus.mFourierCoeff
        (↑(Torus.periodicToTorusL2 f hf) : UnitAddTorus (Fin d) → ℂ) k =
      smoothFourierCoeff f k := by
  let hmem := Torus.memLp_periodicToTorus hf
  calc
    _ = ∫ y : UnitAddTorus (Fin d),
        UnitAddTorus.mFourier (-k) y * Torus.periodicToTorus f y := by
      apply integral_congr_ae
      filter_upwards [hmem.coeFn_toLp] with y hy
      exact congrArg (fun z : ℂ => UnitAddTorus.mFourier (-k) y * z) hy
    _ = ∫ x in Torus.unitCell d, Torus.torusCharacter k x * f x := by
      rw [← Torus.integral_periodicToTorus_eq_unitCell
        (fun x : Vec d => Torus.torusCharacter k x * f x)]
      apply integral_congr_ae
      filter_upwards with y
      change UnitAddTorus.mFourier (-k) y * f (Torus.unitTorusRepresentative d y) =
        UnitAddTorus.mFourier (-k)
          (Torus.toUnitTorus d (Torus.unitTorusRepresentative d y)) *
            f (Torus.unitTorusRepresentative d y)
      rw [Torus.toUnitTorus_unitTorusRepresentative]

theorem HMinusOneSpectral.smoothFourierCoeff_le_gradientCoeff_of_largeFrequency
    {d : ℕ} (hd : 0 < d) {φ : Vec d → ℂ}
    (hφ : ContDiff ℝ 1 φ) (hφper : IsZdPeriodic φ)
    (M : ℝ) (hMpos : 0 < M) (q : Fin d → ℤ) (hM : M ≤ ‖q‖) :
    ‖smoothFourierCoeff φ q‖ ≤
      (∑ i : Fin d, ‖smoothFourierCoeff (Torus.coordDeriv i φ) q‖ ^ 2) ^
        (1 / 2 : ℝ) / (2 * Real.pi * M) := by
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : d ≠ 0)
  have hnonempty : (Finset.univ : Finset (Fin (n + 1))).Nonempty := by
    exact ⟨⟨0, by omega⟩, Finset.mem_univ _⟩
  obtain ⟨i, hi, hmax⟩ := Finset.exists_max_image
    (Finset.univ : Finset (Fin (n + 1))) (fun j => ‖q j‖) hnonempty
  have hmax' : ∀ j : Fin (n + 1), ‖q j‖ ≤ ‖q i‖ := by
    intro j
    exact hmax j (Finset.mem_univ j)
  have hnormle : ‖q‖ ≤ ‖q i‖ :=
    (pi_norm_le_iff_of_nonneg (norm_nonneg (q i))).2 hmax'
  have hqi : M ≤ ‖q i‖ := hM.trans hnormle
  have hcoeff := Torus.smoothFourierCoeff_coordDeriv i hφ hφper q
  have hmultnorm :
      ‖Torus.smoothFourierCoeff (Torus.coordDeriv i φ) q‖ =
        (2 * Real.pi * ‖q i‖) * ‖Torus.smoothFourierCoeff φ q‖ := by
    rw [hcoeff, norm_mul]
    congr 1
    simp [Complex.norm_I, Complex.norm_intCast,
      Int.norm_eq_abs, abs_of_nonneg Real.pi_pos.le]
  have hgradnonneg : 0 ≤
      ∑ j : Fin (n + 1), ‖Torus.smoothFourierCoeff (Torus.coordDeriv j φ) q‖ ^ 2 :=
    Finset.sum_nonneg fun j _ => sq_nonneg _
  have hone : ‖Torus.smoothFourierCoeff (Torus.coordDeriv i φ) q‖ ^ 2 ≤
      ∑ j : Fin (n + 1),
        ‖Torus.smoothFourierCoeff (Torus.coordDeriv j φ) q‖ ^ 2 := by
    exact Finset.single_le_sum
      (s := Finset.univ)
      (f := fun j : Fin (n + 1) =>
        ‖Torus.smoothFourierCoeff (Torus.coordDeriv j φ) q‖ ^ 2)
      (fun j _ => sq_nonneg _)
      (Finset.mem_univ i)
  have hfactor : 2 * Real.pi * M ≤ 2 * Real.pi * ‖q i‖ := by
    exact mul_le_mul_of_nonneg_left hqi
      (by positivity : 0 ≤ 2 * Real.pi)
  have hfactor' :
      (2 * Real.pi * M) * ‖Torus.smoothFourierCoeff φ q‖ ≤
        (2 * Real.pi * ‖q i‖) * ‖Torus.smoothFourierCoeff φ q‖ :=
    mul_le_mul_of_nonneg_right hfactor (norm_nonneg _)
  have hcoeffSq :
      ((2 * Real.pi * M) * ‖Torus.smoothFourierCoeff φ q‖) ^ 2 ≤
        ∑ j : Fin (n + 1),
          ‖Torus.smoothFourierCoeff (Torus.coordDeriv j φ) q‖ ^ 2 := by
    have hcoeffLe :
        (2 * Real.pi * M) * ‖Torus.smoothFourierCoeff φ q‖ ≤
          ‖Torus.smoothFourierCoeff (Torus.coordDeriv i φ) q‖ := by
      calc
        _ ≤ (2 * Real.pi * ‖q i‖) * ‖Torus.smoothFourierCoeff φ q‖ := hfactor'
        _ = _ := hmultnorm.symm
    have hprodnonneg : 0 ≤
        (2 * Real.pi * M) * ‖Torus.smoothFourierCoeff φ q‖ :=
      mul_nonneg (mul_nonneg (by positivity : 0 ≤ 2 * Real.pi) hMpos.le)
        (norm_nonneg (Torus.smoothFourierCoeff φ q))
    have hcoeffSquare := (sq_le_sq₀ hprodnonneg
      (norm_nonneg (Torus.smoothFourierCoeff (Torus.coordDeriv i φ) q))).2 hcoeffLe
    exact hcoeffSquare.trans hone
  have hprodnonneg : 0 ≤
      (2 * Real.pi * M) * ‖Torus.smoothFourierCoeff φ q‖ :=
    mul_nonneg (mul_nonneg (by positivity : 0 ≤ 2 * Real.pi) hMpos.le)
      (norm_nonneg (Torus.smoothFourierCoeff φ q))
  have hroot := (Real.le_sqrt hprodnonneg hgradnonneg).2 hcoeffSq
  have hden : 0 < 2 * Real.pi * M := by positivity
  exact (le_div_iff₀ hden).2 (by simpa [mul_comm, Real.sqrt_eq_rpow] using hroot)

/-- A Fourier gap in an `L²` function gives the sharp reciprocal-frequency
bound when paired with a smooth periodic test. The proof uses the torus
Hilbert basis, Parseval for the test gradient, and the existing derivative
multiplier identity. -/
theorem torusPairing_le_of_fourierGap
    {d : ℕ} (hd : 0 < d) (h : UnitAddTorus (Fin d) → ℂ)
    (hh : MemLp h 2 (volume : Measure (UnitAddTorus (Fin d))))
    {φ : Vec d → ℂ} (hφ : ContDiff ℝ 1 φ) (hφper : IsZdPeriodic φ)
    (M : ℝ) (hM : 0 < M)
    (hgap : ∀ q : Fin d → ℤ, ‖q‖ < M →
      UnitAddTorus.mFourierCoeff h q = 0) :
    ‖∫ x : UnitAddTorus (Fin d),
        star (h x) * Torus.periodicToTorus φ x‖ ≤
      (2 * Real.pi * M)⁻¹ *
        (∫ x : UnitAddTorus (Fin d), ‖h x‖ ^ 2) ^ (1 / 2 : ℝ) *
        (∑ i : Fin d, ∫ x in Torus.unitCell d,
          ‖Torus.coordDeriv i φ x‖ ^ 2) ^ (1 / 2 : ℝ) := by
  classical
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : d ≠ 0)
  let hT : Torus.TorusL2 (n + 1) := hh.toLp h
  let hTfun : UnitAddTorus (Fin (n + 1)) → ℂ := (↑↑hT)
  let φL2 := Torus.periodicToTorusL2 φ hφ.continuous
  let φL2fun : UnitAddTorus (Fin (n + 1)) → ℂ := (↑φL2)
  let a : (Fin (n + 1) → ℤ) → ℝ := fun q =>
    ‖UnitAddTorus.mFourierCoeff h q‖
  let gradSq : (Fin (n + 1) → ℤ) → ℝ := fun q =>
    ∑ i : Fin (n + 1),
      ‖Torus.smoothFourierCoeff (Torus.coordDeriv i φ) q‖ ^ 2
  let b : (Fin (n + 1) → ℤ) → ℝ := fun q => Real.sqrt (gradSq q)
  have hparsevalT := UnitAddTorus.hasSum_sq_mFourierCoeff hT
  have hcoeffLp (q : Fin (n + 1) → ℤ) :
      UnitAddTorus.mFourierCoeff (↑↑hT) q = UnitAddTorus.mFourierCoeff h q := by
    unfold UnitAddTorus.mFourierCoeff
    apply integral_congr_ae
    filter_upwards [hh.coeFn_toLp] with x hx
    exact congrArg (fun z : ℂ => UnitAddTorus.mFourier (-q) x • z) hx
  have hnormInt :
      (∫ x : UnitAddTorus (Fin (n + 1)), ‖hTfun x‖ ^ 2) =
        ∫ x : UnitAddTorus (Fin (n + 1)), ‖h x‖ ^ 2 := by
    apply integral_congr_ae
    filter_upwards [hh.coeFn_toLp] with x hx
    exact congrArg (fun z : ℂ => ‖z‖ ^ 2) hx
  have hparsevalRaw : HasSum (fun q : Fin (n + 1) → ℤ =>
      ‖UnitAddTorus.mFourierCoeff h q‖ ^ 2)
      (∫ x : UnitAddTorus (Fin (n + 1)), ‖h x‖ ^ 2) := by
    have hsum := hparsevalT.congr_fun (fun q => by rw [hcoeffLp q])
    have hnormInt' :
        (∫ x : UnitAddTorus (Fin (n + 1)), ‖hTfun x‖ ^ 2) =
          ∫ x : UnitAddTorus (Fin (n + 1)), ‖h x‖ ^ 2 := by
      exact hnormInt
    rw [← hnormInt']
    exact hsum
  have hparsevalGrad := Torus.hasSum_sq_smoothGradientFourierCoeff
    hφ
  let A : ℝ := Real.sqrt (∫ x : UnitAddTorus (Fin (n + 1)), ‖h x‖ ^ 2)
  let B : ℝ := Real.sqrt (∑ i : Fin (n + 1),
    ∫ x in Torus.unitCell (n + 1), ‖Torus.coordDeriv i φ x‖ ^ 2)
  have hAint : 0 ≤ ∫ x : UnitAddTorus (Fin (n + 1)), ‖h x‖ ^ 2 :=
    integral_nonneg fun _ => sq_nonneg _
  have hBint : 0 ≤ ∑ i : Fin (n + 1),
      ∫ x in Torus.unitCell (n + 1), ‖Torus.coordDeriv i φ x‖ ^ 2 :=
    Finset.sum_nonneg fun i _ => integral_nonneg fun _ => sq_nonneg _
  have hasumA : HasSum (fun q => a q ^ (2 : ℝ)) (A ^ (2 : ℝ)) := by
    have hterms : ∀ q, a q ^ (2 : ℝ) =
        ‖UnitAddTorus.mFourierCoeff h q‖ ^ 2 := by
      intro q
      calc
        a q ^ (2 : ℝ) = a q ^ 2 := Real.rpow_two _
        _ = ‖UnitAddTorus.mFourierCoeff h q‖ ^ 2 := by rfl
    have hsum := hparsevalRaw.congr_fun hterms
    have hlim : A ^ (2 : ℝ) =
        ∫ x : UnitAddTorus (Fin (n + 1)), ‖h x‖ ^ 2 := by
      calc
        A ^ (2 : ℝ) = A ^ 2 := Real.rpow_two _
        _ = _ := by dsimp [A]; exact Real.sq_sqrt hAint
    rw [← hlim] at hsum
    exact hsum
  have hasumB : HasSum (fun q => b q ^ (2 : ℝ)) (B ^ (2 : ℝ)) := by
    have hterms : ∀ q, b q ^ (2 : ℝ) = gradSq q := by
      intro q
      dsimp [b]
      rw [Real.rpow_two, Real.sq_sqrt]
      exact Finset.sum_nonneg fun i _ => sq_nonneg _
    have hsum := hparsevalGrad.congr_fun hterms
    have hlim : B ^ (2 : ℝ) =
        ∑ i : Fin (n + 1), ∫ x in Torus.unitCell (n + 1),
          ‖Torus.coordDeriv i φ x‖ ^ 2 := by
      calc
        B ^ (2 : ℝ) = B ^ 2 := Real.rpow_two _
        _ = _ := by dsimp [B]; exact Real.sq_sqrt hBint
    rw [← hlim] at hsum
    exact hsum
  have ha : ∀ q, 0 ≤ a q := fun _ => norm_nonneg _
  have hb : ∀ q, 0 ≤ b q := fun _ => Real.sqrt_nonneg _
  have hAnonneg : 0 ≤ A := Real.sqrt_nonneg _
  have hBnonneg : 0 ≤ B := Real.sqrt_nonneg _
  obtain ⟨C, hCnonneg, hCbound, hCsum⟩ :=
    Real.inner_le_Lp_mul_Lq_hasSum_of_nonneg
      (Real.HolderConjugate.two_two) hAnonneg hBnonneg ha hb hasumA hasumB
  have hpair := UnitAddTorus.hasSum_prod_mFourierCoeff hT φL2
  have hpair' : HasSum
      (fun q : Fin (n + 1) → ℤ =>
        star (UnitAddTorus.mFourierCoeff h q) *
          Torus.smoothFourierCoeff φ q)
      (∫ x : UnitAddTorus (Fin (n + 1)),
        star (h x) * Torus.periodicToTorus φ x) := by
    convert hpair using 1
    · ext q
      rw [hcoeffLp q, HMinusOneSpectral.periodicToTorusL2_fourierCoeff_eq_smooth hφ.continuous q]
      rfl
    · apply integral_congr_ae
      filter_upwards [hh.coeFn_toLp,
        (Torus.memLp_periodicToTorus hφ.continuous).coeFn_toLp] with x hx hxφ
      change φL2fun x = Torus.periodicToTorus φ x at hxφ
      change star (h x) * Torus.periodicToTorus φ x =
        star (hTfun x) * φL2fun x
      rw [← hx, ← hxφ]
  have hpairSummable := hpair'.summable.norm
  have hmajorSum : HasSum (fun q : Fin (n + 1) → ℤ =>
      (2 * Real.pi * M)⁻¹ * (a q * b q))
      ((2 * Real.pi * M)⁻¹ * C) := hCsum.mul_left _
  have hmajorSummable := hmajorSum.summable
  have hterm : ∀ q : Fin (n + 1) → ℤ,
      ‖star (UnitAddTorus.mFourierCoeff h q) *
        Torus.smoothFourierCoeff φ q‖ ≤
        (2 * Real.pi * M)⁻¹ * (a q * b q) := by
    intro q
    by_cases hlow : ‖q‖ < M
    · simp [hgap q hlow, a]
    · have hhigh : M ≤ ‖q‖ := le_of_not_gt hlow
      have hφcoeff := HMinusOneSpectral.smoothFourierCoeff_le_gradientCoeff_of_largeFrequency
        (by omega : 0 < n + 1) hφ hφper M hM q hhigh
      dsimp [a, b, gradSq]
      rw [norm_mul, Complex.norm_conj]
      calc
        ‖UnitAddTorus.mFourierCoeff h q‖ *
            ‖Torus.smoothFourierCoeff φ q‖ ≤
          ‖UnitAddTorus.mFourierCoeff h q‖ *
            ((∑ i : Fin (n + 1),
              ‖Torus.smoothFourierCoeff (Torus.coordDeriv i φ) q‖ ^ 2) ^
                (1 / 2 : ℝ) / (2 * Real.pi * M)) :=
          mul_le_mul_of_nonneg_left hφcoeff (norm_nonneg _)
        _ = (2 * Real.pi * M)⁻¹ *
            (‖UnitAddTorus.mFourierCoeff h q‖ *
              Real.sqrt (∑ i : Fin (n + 1),
                ‖Torus.smoothFourierCoeff (Torus.coordDeriv i φ) q‖ ^ 2)) := by
          rw [Real.sqrt_eq_rpow]
          ring
  calc
    _ = ‖∑' q : Fin (n + 1) → ℤ,
        star (UnitAddTorus.mFourierCoeff h q) *
          Torus.smoothFourierCoeff φ q‖ := by
          rw [← hpair'.tsum_eq]
    _ ≤ ∑' q : Fin (n + 1) → ℤ,
        ‖star (UnitAddTorus.mFourierCoeff h q) *
          Torus.smoothFourierCoeff φ q‖ := norm_tsum_le_tsum_norm hpairSummable
    _ ≤ ∑' q : Fin (n + 1) → ℤ,
        (2 * Real.pi * M)⁻¹ * (a q * b q) :=
          Summable.tsum_mono hpairSummable hmajorSummable hterm
    _ = (2 * Real.pi * M)⁻¹ * C := hmajorSum.tsum_eq
    _ ≤ (2 * Real.pi * M)⁻¹ *
        (A * B) := by
      exact mul_le_mul_of_nonneg_left hCbound (by positivity)
    _ = (2 * Real.pi * M)⁻¹ *
        ((∫ x : UnitAddTorus (Fin (n + 1)), ‖h x‖ ^ 2) ^ (1 / 2 : ℝ) *
          (∑ i : Fin (n + 1), ∫ x in Torus.unitCell (n + 1),
            ‖Torus.coordDeriv i φ x‖ ^ 2) ^ (1 / 2 : ℝ)) := by
      simp only [A, B, Real.sqrt_eq_rpow]
    _ = (2 * Real.pi * M)⁻¹ *
        (∫ x : UnitAddTorus (Fin (n + 1)), ‖h x‖ ^ 2) ^ (1 / 2 : ℝ) *
        (∑ i : Fin (n + 1), ∫ x in Torus.unitCell (n + 1),
          ‖Torus.coordDeriv i φ x‖ ^ 2) ^ (1 / 2 : ℝ) := by ring

theorem HMinusOneSpectral.integrable_mul_continuousMap {d : ℕ} {g : UnitTorus d → ℂ}
    (hg : Integrable g) (F : C(UnitTorus d, ℂ)) :
    Integrable (fun x => g x * F x) := by
  have hg' : IntegrableOn g Set.univ volume := by simpa [IntegrableOn] using hg
  simpa [IntegrableOn, mul_comm] using
    hg'.continuousOn_mul F.continuous.continuousOn isCompact_univ

theorem HMinusOneSpectral.mFourierCoeff_zero_eq_integral_local {d : ℕ}
    (G : UnitTorus d → ℂ) :
    UnitAddTorus.mFourierCoeff G (0 : Fin d → ℤ) = ∫ x, G x := by
  simp [UnitAddTorus.mFourierCoeff, UnitAddTorus.mFourier_zero]

theorem HMinusOneSpectral.mFourierCoeff_mul_character_shift {d : ℕ}
    (G : UnitTorus d → ℂ) (q k : Fin d → ℤ) :
    (∫ x, UnitAddTorus.mFourier (-q) x *
      (UnitAddTorus.mFourier k x * G x)) =
      UnitAddTorus.mFourierCoeff G (q - k) := by
  unfold UnitAddTorus.mFourierCoeff
  apply integral_congr_ae
  filter_upwards with x
  have hfreq : -q + k = -(q - k) := by ext i; simp; omega
  calc
    _ = (UnitAddTorus.mFourier (-q) x * UnitAddTorus.mFourier k x) * G x := by ring
    _ = UnitAddTorus.mFourier (-q + k) x * G x := by
      rw [← UnitAddTorus.mFourier_add]
    _ = UnitAddTorus.mFourier (-(q - k)) x • G x := by
      rw [hfreq]
      simp [smul_eq_mul]

/-- A finite Fourier polynomial times a mean-zero `N⁻¹ℤᵈ`-periodic function
has no Fourier coefficient below the gap between the fast lattice and the
polynomial support. The finite expansion premise is the interface consumed by
the symmetric cutoff `realFourierProjection`. -/
theorem mFourierCoeff_mul_eq_zero_of_finiteSupport_fast
    {d N : ℕ} (hN : 0 < N) (S : Finset (Fin d → ℤ))
    (a : (Fin d → ℤ) → ℂ) (P : C(UnitTorus d, ℂ)) (G : UnitTorus d → ℂ)
    (hP : ∀ x, P x = ∑ k ∈ S,
      a k * UnitAddTorus.mFourier k x)
    (M : ℝ) (hS : ∀ k ∈ S, ‖k‖ ≤ M)
    (hG : Integrable G) (hGmean : ∫ x, G x = 0)
    (hGfast : ∀ i x, G (x + fastTorusShift N i) = G x)
    (q : Fin d → ℤ) (hq : ‖q‖ < (N : ℝ) - M) :
    UnitAddTorus.mFourierCoeff (fun x => P x * G x) q = 0 := by
  classical
  let T : (Fin d → ℤ) → UnitTorus d → ℂ := fun k x =>
    UnitAddTorus.mFourier (-q) x * (a k * UnitAddTorus.mFourier k x * G x)
  have htermInt (k : Fin d → ℤ) : Integrable (T k) := by
    have hmul := HMinusOneSpectral.integrable_mul_continuousMap hG
      (UnitAddTorus.mFourier (-q) * (a k • UnitAddTorus.mFourier k))
    have hmul' : Integrable (fun x => G x *
        (UnitAddTorus.mFourier (-q) x * (a k * UnitAddTorus.mFourier k x))) := by
      simpa only [ContinuousMap.mul_apply, ContinuousMap.smul_apply,
        smul_eq_mul, mul_assoc] using hmul
    have hEq : (fun x => G x *
        (UnitAddTorus.mFourier (-q) x * (a k * UnitAddTorus.mFourier k x))) = T k := by
      funext x
      dsimp [T]
      ring
    rw [hEq] at hmul'
    exact hmul'
  have hsumInt : ∀ k ∈ S, Integrable (T k) := fun k hk => htermInt k
  have hcoeff : UnitAddTorus.mFourierCoeff (fun x => P x * G x) q =
      ∑ k ∈ S, a k * UnitAddTorus.mFourierCoeff G (q - k) := by
    change (∫ x, UnitAddTorus.mFourier (-q) x * (P x * G x)) = _
    calc
      _ = ∫ x, ∑ k ∈ S, T k x := by
        apply integral_congr_ae
        filter_upwards with x
        rw [hP x]
        simp only [Finset.sum_mul, Finset.mul_sum]
        rfl
      _ = ∑ k ∈ S, ∫ x, T k x := by
        rw [integral_finsetSum]
        exact hsumInt
      _ = ∑ k ∈ S, a k * UnitAddTorus.mFourierCoeff G (q - k) := by
        apply Finset.sum_congr rfl
        intro k hk
        calc
          (∫ x, T k x) = a k *
              (∫ x, UnitAddTorus.mFourier (-q) x *
                (UnitAddTorus.mFourier k x * G x)) := by
            rw [show (fun x => T k x) = fun x =>
                a k * (UnitAddTorus.mFourier (-q) x *
                  (UnitAddTorus.mFourier k x * G x)) by
                  funext x
                  dsimp [T]
                  ring]
            rw [integral_const_mul]
          _ = a k * UnitAddTorus.mFourierCoeff G (q - k) := by
            rw [HMinusOneSpectral.mFourierCoeff_mul_character_shift]
  have hcoefZero (k : Fin d → ℤ) (hk : k ∈ S) :
      UnitAddTorus.mFourierCoeff G (q - k) = 0 := by
    by_cases hqk : q - k = 0
    · rw [hqk, HMinusOneSpectral.mFourierCoeff_zero_eq_integral_local, hGmean]
    · have hsmall : ‖q - k‖ < (N : ℝ) := by
        have htri := norm_sub_le q k
        have hkm := hS k hk
        nlinarith
      have hnotfast : ¬ IsFastFrequency N (q - k) := by
        intro hfast
        have hlarge := fastFrequency_norm_ge_nat hN hqk hfast
        linarith
      exact mFourierCoeff_eq_zero_of_not_fastFrequencyLattice hN (q - k)
        (hGfast) hnotfast
  rw [hcoeff]
  apply Finset.sum_eq_zero
  intro k hk
  rw [hcoefZero k hk, mul_zero]

end

end AVenhance.Infra.Ergodic
