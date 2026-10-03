/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Ergodic.HMinusOneSpectral
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Ergodic.LatticeDecay

/-! # The frequency split in the homogeneous H⁻¹ ergodic estimate -/

@[expose] public section

namespace AVenhance.Infra.Ergodic

open scoped ContDiff
open MeasureTheory
open Homogenization
open AVenhance.Infra.Torus

noncomputable section

variable {d : ℕ} {hd : 0 < d}

/-- Use normalized Haar measure on the unit circle for periodic integrals. -/
local instance avInfraErgodicHMinusOneErgodicCoreMeasureSpace1 : MeasureSpace UnitAddCircle :=
    ⟨AddCircle.haarAddCircle⟩
local instance avInfraErgodicHMinusOneErgodicCoreMeasureIsAddHaarMeasure2 :
    Measure.IsAddHaarMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)
local instance avInfraErgodicHMinusOneErgodicCoreIsProbabilityMeasure3 : IsProbabilityMeasure
    (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

theorem mFourierCoeff_character (q k : Fin d → ℤ) :
    UnitAddTorus.mFourierCoeff (UnitAddTorus.mFourier k) q =
      if q = k then 1 else 0 := by
  have horth := (orthonormal_iff_ite.mp
    (UnitAddTorus.orthonormal_mFourier (d := Fin d))) q k
  have hcoeff : UnitAddTorus.mFourierCoeff (UnitAddTorus.mFourier k) q =
      inner ℂ (UnitAddTorus.mFourierLp 2 q) (UnitAddTorus.mFourierLp 2 k) := by
    simp only [UnitAddTorus.mFourierCoeff, smul_eq_mul,
      UnitAddTorus.mFourier_neg]
    rw [MeasureTheory.L2.inner_def]
    apply integral_congr_ae
    filter_upwards [UnitAddTorus.coeFn_mFourierLp 2 q,
      UnitAddTorus.coeFn_mFourierLp 2 k] with x hq hk
    simp only [hq, hk, RCLike.inner_apply]
    ring
  rw [hcoeff]
  exact horth

theorem finite_frequencyBall (M : ℕ) :
    {k : Fin d → ℤ | ‖k‖ ≤ (M : ℝ)}.Finite := by
  refine (Set.Finite.pi' (fun _ : Fin d => Set.finite_Icc
    (-(M : ℤ)) (M : ℤ))).subset ?_
  intro k hk i
  have hcoord : ‖(k i : ℝ)‖ ≤ (M : ℝ) :=
    (norm_le_pi_norm k i).trans hk
  have habs : |k i| ≤ (M : ℤ) := by
    exact_mod_cast (show (|((k i : ℝ))|) ≤ (M : ℝ) by simpa [Int.norm_eq_abs,
      Int.cast_abs] using hcoord)
  exact (abs_le.mp habs)

/-- Finite set of integer frequencies within the specified frequency bound. -/
def frequencyBall (M : ℕ) : Finset (Fin d → ℤ) :=
  (finite_frequencyBall M).toFinset

theorem mem_frequencyBall {M : ℕ} {k : Fin d → ℤ} :
    k ∈ frequencyBall M ↔ ‖k‖ ≤ (M : ℝ) := by
  simp [frequencyBall]

theorem frequencyBall_neg (M : ℕ) {k : Fin d → ℤ}
    (hk : k ∈ frequencyBall M) : -k ∈ frequencyBall M := by
  rw [mem_frequencyBall] at hk ⊢
  simpa using hk

/-- Finite Fourier sum on the torus with the supplied coefficients. -/
noncomputable def fourierCutoff (M : ℕ)
    (a : (Fin d → ℤ) → ℂ) : C(UnitAddTorus (Fin d), ℂ) :=
  ⟨fun x => ∑ k ∈ frequencyBall M,
    a k * UnitAddTorus.mFourier k x,
    continuous_finsetSum _ fun k hk => by fun_prop⟩

theorem continuous_unitTorus_integrable
    {u : UnitAddTorus (Fin d) → ℂ} (hu : Continuous u) :
    Integrable u (volume : Measure (UnitAddTorus (Fin d))) := by
  have h : IntegrableOn u Set.univ (volume : Measure (UnitAddTorus (Fin d))) :=
    hu.continuousOn.integrableOn_compact (isCompact_univ :
      IsCompact (Set.univ : Set (UnitAddTorus (Fin d))))
  simpa [IntegrableOn] using h

/-- Closed spatial unit cell used for compactness and periodic integration. -/
def closedUnitCube : Set (Vec d) :=
  Set.pi Set.univ fun _ : Fin d => Set.Icc (0 : ℝ) 1

theorem unitCell_subset_closedUnitCube :
    Torus.unitCell d ⊆ closedUnitCube := by
  intro x hx
  simp only [closedUnitCube, Set.mem_pi, Set.mem_univ, forall_true_left]
  intro i
  exact ⟨le_of_lt (hx i).1, by simpa using (hx i).2⟩

theorem continuous_complex_unitCell_integrable
    {f : Vec d → ℂ} (hf : Continuous f) :
    IntegrableOn f (Torus.unitCell d) (volume : Measure (Vec d)) := by
  have hcube : IsCompact (closedUnitCube (d := d)) := by
    change IsCompact (Set.pi Set.univ fun _ : Fin d => Set.Icc (0 : ℝ) 1)
    exact isCompact_univ_pi fun _ => isCompact_Icc
  exact hf.continuousOn.integrableOn_compact hcube |>.mono_set
    unitCell_subset_closedUnitCube

theorem mFourierCoeff_sum {ι : Type*} (S : Finset ι)
    (F : ι → UnitAddTorus (Fin d) → ℂ) (q : Fin d → ℤ)
    (hF : ∀ k ∈ S, Integrable (fun x =>
      UnitAddTorus.mFourier (-q) x * F k x)
      (volume : Measure (UnitAddTorus (Fin d)))) :
    UnitAddTorus.mFourierCoeff (fun x => ∑ k ∈ S, F k x) q =
      ∑ k ∈ S, UnitAddTorus.mFourierCoeff (F k) q := by
  classical
  unfold UnitAddTorus.mFourierCoeff
  simp only [smul_eq_mul]
  calc
    (∫ x, UnitAddTorus.mFourier (-q) x * (∑ k ∈ S, F k x)) =
        ∫ x, ∑ k ∈ S, UnitAddTorus.mFourier (-q) x * F k x := by
      apply integral_congr_ae
      filter_upwards with x
      rw [Finset.mul_sum]
    _ = ∑ k ∈ S, ∫ x,
        UnitAddTorus.mFourier (-q) x * F k x := by
      rw [integral_finsetSum]
      exact hF

theorem mFourierCoeff_const_smul_character (c : ℂ)
    (q k : Fin d → ℤ) :
    UnitAddTorus.mFourierCoeff
      (fun x => c * UnitAddTorus.mFourier k x) q =
      if q = k then c else 0 := by
  unfold UnitAddTorus.mFourierCoeff
  simp only [smul_eq_mul]
  rw [show (fun x => UnitAddTorus.mFourier (-q) x *
      (c * UnitAddTorus.mFourier k x)) =
      fun x => c * (UnitAddTorus.mFourier (-q) x *
        UnitAddTorus.mFourier k x) by
          funext x
          ring,
    integral_const_mul]
  change c * UnitAddTorus.mFourierCoeff
      (UnitAddTorus.mFourier k) q = _
  rw [mFourierCoeff_character]
  split_ifs <;> simp_all

theorem mFourierCoeff_fourierCutoff
    (M : ℕ) (a : (Fin d → ℤ) → ℂ) (q : Fin d → ℤ) :
    UnitAddTorus.mFourierCoeff (fourierCutoff M a) q =
      if q ∈ frequencyBall M then a q else 0 := by
  classical
  change UnitAddTorus.mFourierCoeff
    (fun x => ∑ k ∈ frequencyBall M,
      a k * UnitAddTorus.mFourier k x) q = _
  have hF (k : Fin d → ℤ) (hk : k ∈ frequencyBall M) :
      Integrable (fun x => UnitAddTorus.mFourier (-q) x *
        (a k * UnitAddTorus.mFourier k x))
        (volume : Measure (UnitAddTorus (Fin d))) := by
    apply continuous_unitTorus_integrable
    exact (UnitAddTorus.mFourier (-q)).continuous.mul
      (continuous_const.mul (UnitAddTorus.mFourier k).continuous)
  rw [mFourierCoeff_sum (S := frequencyBall M)
    (F := fun k x => a k * UnitAddTorus.mFourier k x) (q := q) hF]
  simp only [mFourierCoeff_const_smul_character]
  simp

theorem fourierCutoff_star_eq (M : ℕ)
    (a : (Fin d → ℤ) → ℂ)
    (ha : ∀ k, a (-k) = star (a k)) (x : UnitAddTorus (Fin d)) :
    star (fourierCutoff M a x) = fourierCutoff M a x := by
  classical
  change star (∑ k ∈ frequencyBall M,
      a k * UnitAddTorus.mFourier k x) =
    ∑ k ∈ frequencyBall M, a k * UnitAddTorus.mFourier k x
  rw [star_sum]
  refine Finset.sum_bij (fun k _ => -k) ?_ ?_ ?_ ?_
  · intro k hk
    exact frequencyBall_neg M hk
  · intro k hk l hl hkl
    exact neg_injective hkl
  · intro k hk
    exact ⟨-k, frequencyBall_neg M hk, by simp⟩
  · intro k hk
    change star (a k * UnitAddTorus.mFourier k x) =
      a (-k) * UnitAddTorus.mFourier (-k) x
    rw [star_mul]
    rw [← ha k, UnitAddTorus.mFourier_neg]
    exact mul_comm _ _

/-- Real part of the finite torus Fourier sum. -/
noncomputable def realFourierCutoff (M : ℕ)
    (a : (Fin d → ℤ) → ℂ) : C(UnitAddTorus (Fin d), ℝ) :=
  ⟨fun x => (fourierCutoff M a x).re, by fun_prop⟩

theorem realFourierCutoff_complexification (M : ℕ)
    (a : (Fin d → ℤ) → ℂ)
    (ha : ∀ k, a (-k) = star (a k)) :
    (fun x => (realFourierCutoff M a x : ℂ)) = fourierCutoff M a := by
  funext x
  apply Complex.ext
  · rfl
  · have hstar := fourierCutoff_star_eq M a ha x
    have him : (fourierCutoff M a x).im = 0 := by
      have hi := congrArg Complex.im hstar
      simp only [Complex.star_def, Complex.conj_im] at hi
      linarith
    simp [realFourierCutoff, him]

theorem smoothFourierCoeff_real_neg {f : Vec d → ℝ}
    (k : Fin d → ℤ) :
    smoothFourierCoeff (fun x => (f x : ℂ)) (-k) =
      star (smoothFourierCoeff (fun x => (f x : ℂ)) k) := by
  unfold Torus.smoothFourierCoeff
  have hchar (x : Vec d) : Torus.torusCharacter (-k) x =
      star (Torus.torusCharacter k x) := by
    simp [Torus.torusCharacter, UnitAddTorus.mFourier_neg]
  calc
    (∫ x in Torus.unitCell d,
        Torus.torusCharacter (-k) x * (f x : ℂ)) =
      ∫ x in Torus.unitCell d,
        star (Torus.torusCharacter k x * (f x : ℂ)) := by
          apply setIntegral_congr_fun (Torus.measurableSet_unitCell d)
          intro x hx
          simp [hchar x]
    _ = star (∫ x in Torus.unitCell d,
        Torus.torusCharacter k x * (f x : ℂ)) := by
          rw [Complex.star_def]
          rw [integral_conj]

/-- Finite Fourier sum evaluated on Euclidean space using periodic characters. -/
def complexEuclideanCutoff (M : ℕ)
    (a : (Fin d → ℤ) → ℂ) (x : Vec d) : ℂ :=
  ∑ k ∈ frequencyBall M, a k * Torus.torusCharacter (-k) x

/-- Real part of the Euclidean finite Fourier sum. -/
def euclideanFourierCutoff (M : ℕ)
    (a : (Fin d → ℤ) → ℂ) (x : Vec d) : ℝ :=
  (complexEuclideanCutoff M a x).re

theorem complexEuclideanCutoff_smooth (M : ℕ)
    (a : (Fin d → ℤ) → ℂ) :
    ContDiff ℝ ⊤ (complexEuclideanCutoff M a) := by
  unfold complexEuclideanCutoff
  exact ContDiff.sum (fun k hk =>
    (contDiff_const : ContDiff ℝ ⊤ (fun _ : Vec d => a k)).mul
      (Torus.torusCharacter_contDiff (-k)))

theorem complexEuclideanCutoff_periodic (M : ℕ)
    (a : (Fin d → ℤ) → ℂ) :
    IsZPeriodic (complexEuclideanCutoff M a) := by
  intro x z
  unfold complexEuclideanCutoff
  apply Finset.sum_congr rfl
  intro k hk
  have hchar := Torus.torusCharacter_periodic (-k) z x
  change a k * Torus.torusCharacter (-k) (x + Torus.intVector z) = _
  exact congrArg (fun w : ℂ => a k * w) hchar

theorem euclideanFourierCutoff_contDiff (M : ℕ)
    (a : (Fin d → ℤ) → ℂ) :
  ContDiff ℝ ⊤ (euclideanFourierCutoff M a) := by
  unfold euclideanFourierCutoff
  exact (Complex.reCLM.contDiff.of_le le_top).comp
    (complexEuclideanCutoff_smooth M a)

theorem euclideanFourierCutoff_periodic (M : ℕ)
    (a : (Fin d → ℤ) → ℂ) :
    IsZPeriodic (euclideanFourierCutoff M a) := by
  intro x z
  unfold euclideanFourierCutoff
  exact congrArg Complex.re (complexEuclideanCutoff_periodic M a x z)

theorem periodicToTorus_euclideanFourierCutoff
    (M : ℕ) (a : (Fin d → ℤ) → ℂ) (y : UnitAddTorus (Fin d)) :
    Torus.periodicToTorus
        (fun x => (euclideanFourierCutoff M a x : ℂ)) y =
      (realFourierCutoff M a y : ℂ) := by
  have htor : complexEuclideanCutoff M a
      (Torus.unitTorusRepresentative d y) = fourierCutoff M a y := by
    simp [complexEuclideanCutoff, fourierCutoff,
      Torus.torusCharacter, Torus.toUnitTorus_unitTorusRepresentative]
  change ((complexEuclideanCutoff M a
      (Torus.unitTorusRepresentative d y)).re : ℂ) =
    ((fourierCutoff M a y).re : ℂ)
  rw [htor]

theorem mFourierCoeff_periodicToTorus_eq_smooth
    {f : Vec d → ℂ} (hper : Torus.IsZdPeriodic f)
    (hf : Continuous f) (k : Fin d → ℤ) :
    UnitAddTorus.mFourierCoeff
      (⟨Torus.periodicToTorus f,
        periodicToTorus_continuous_of_periodic hf hper⟩ :
          C(UnitAddTorus (Fin d), ℂ)) k = Torus.smoothFourierCoeff f k := by
  have hchar (x : UnitAddTorus (Fin d)) :
      Torus.torusCharacter k (Torus.unitTorusRepresentative d x) =
        UnitAddTorus.mFourier (-k) x := by
    simp [Torus.torusCharacter, Torus.toUnitTorus_unitTorusRepresentative]
  change (∫ x : UnitAddTorus (Fin d),
      UnitAddTorus.mFourier (-k) x • Torus.periodicToTorus f x) = _
  simp only [smul_eq_mul]
  change (∫ x : UnitAddTorus (Fin d),
      UnitAddTorus.mFourier (-k) x * Torus.periodicToTorus f x) =
    ∫ x in Torus.unitCell d, Torus.torusCharacter k x * f x
  rw [← Torus.integral_periodicToTorus_eq_unitCell
    (fun x => Torus.torusCharacter k x * f x)]
  apply integral_congr_ae
  filter_upwards with x
  change UnitAddTorus.mFourier (-k) x *
      f (Torus.unitTorusRepresentative d x) =
    Torus.torusCharacter k (Torus.unitTorusRepresentative d x) *
      f (Torus.unitTorusRepresentative d x)
  rw [← hchar x]

theorem smoothFourierCoeff_sub {f g : Vec d → ℂ}
    (hf : Continuous f) (hg : Continuous g) (k : Fin d → ℤ) :
    Torus.smoothFourierCoeff (fun x => f x - g x) k =
      Torus.smoothFourierCoeff f k - Torus.smoothFourierCoeff g k := by
  unfold Torus.smoothFourierCoeff
  rw [show (fun x => Torus.torusCharacter k x * (f x - g x)) =
      (fun x => Torus.torusCharacter k x * f x -
        Torus.torusCharacter k x * g x) by
          funext x
          ring]
  exact integral_sub
    (continuous_complex_unitCell_integrable
      ((Torus.torusCharacter_contDiff k).continuous.mul hf))
    (continuous_complex_unitCell_integrable
      ((Torus.torusCharacter_contDiff k).continuous.mul hg))

theorem hasCoordinateAnalyticL2Bounds_of_fourierDomination
    {u v : Vec d → ℂ} (hu : ContDiff ℝ ∞ u) (huper : Torus.IsZdPeriodic u)
    (hv : ContDiff ℝ ∞ v) (hvper : Torus.IsZdPeriodic v)
    (Cf r : ℝ)
    (hdom : ∀ i n k,
      ‖Torus.smoothFourierCoeff (coordDerivIter i n u) k‖ ≤
        ‖Torus.smoothFourierCoeff (coordDerivIter i n v) k‖)
    (hderiv : HasCoordinateAnalyticL2Bounds v Cf r) :
    HasCoordinateAnalyticL2Bounds u Cf r := by
  intro i n
  have huD : ContDiff ℝ ∞ (coordDerivIter i n u) :=
    coordDerivIter_contDiff_top i n hu
  have hvD : ContDiff ℝ ∞ (coordDerivIter i n v) :=
    coordDerivIter_contDiff_top i n hv
  have huPer := coordDerivIter_periodic i n huper
  have hvPer := coordDerivIter_periodic i n hvper
  have hsumU := Torus.hasSum_sq_smoothFourierCoeff huD.continuous
  have hsumV := Torus.hasSum_sq_smoothFourierCoeff hvD.continuous
  have hterm (k : Fin d → ℤ) :
      ‖Torus.smoothFourierCoeff (coordDerivIter i n u) k‖ ^ 2 ≤
        ‖Torus.smoothFourierCoeff (coordDerivIter i n v) k‖ ^ 2 := by
    exact (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).2 (hdom i n k)
  have htsum := Summable.tsum_le_tsum hterm hsumU.summable hsumV.summable
  rw [hsumU.tsum_eq, hsumV.tsum_eq] at htsum
  have hroot := Real.sqrt_le_sqrt htsum
  have hderiv' : Real.sqrt
      (∫ x in Torus.unitCell d, ‖coordDerivIter i n v x‖ ^ 2) ≤
      Cf * (n.factorial : ℝ) / r ^ n := by
    simpa only [Real.sqrt_eq_rpow] using hderiv i n
  simpa only [Real.sqrt_eq_rpow] using hroot.trans hderiv'

theorem exists_coordinate_ge_of_piNorm_gt
    (hd : 0 < d) {M : ℕ} {k : Fin d → ℤ} (hk : (M : ℝ) < ‖k‖) :
    ∃ i : Fin d, (M + 1 : ℝ) ≤ ‖(k i : ℝ)‖ := by
  obtain ⟨i, hi, hmax⟩ := Finset.exists_max_image
    (Finset.univ : Finset (Fin d)) (fun j => ‖k j‖)
    ⟨⟨0, by omega⟩, Finset.mem_univ _⟩
  have hmax' : ∀ j : Fin d, ‖k j‖ ≤ ‖k i‖ := by
    intro j
    exact hmax j (Finset.mem_univ j)
  have hnorm_le : ‖k‖ ≤ ‖k i‖ :=
    (pi_norm_le_iff_of_nonneg (norm_nonneg (k i))).2 hmax'
  have hnorm_ge : ‖k i‖ ≤ ‖k‖ := norm_le_pi_norm k i
  have hnorm : ‖k‖ = ‖k i‖ := le_antisymm hnorm_le hnorm_ge
  have hstrictNorm : (M : ℝ) < ‖k i‖ := hk.trans_eq hnorm
  have hstrict : (M : ℝ) < |(k i : ℝ)| := by
    simpa [Int.norm_eq_abs, Int.cast_abs] using hstrictNorm
  have hinter : (M : ℤ) < |k i| := by
    exact_mod_cast hstrict
  have hinter' : (M : ℤ) + 1 ≤ |k i| := by omega
  have hinterCast : ((M : ℤ) + 1 : ℝ) ≤ ((|k i| : ℤ) : ℝ) := by
    exact_mod_cast hinter'
  have hreal : (M + 1 : ℝ) ≤ ‖(k i : ℝ)‖ := by
    simpa [Int.cast_abs, Int.norm_eq_abs] using hinterCast
  exact ⟨i, hreal⟩

/-- Parseval turns the repeated derivative bounds into an exponential L²
tail for the Fourier modes outside a finite cube. -/
theorem fourierTailL2_le_of_coordinateAnalyticL2Bounds
    (hd : 0 < d) {v : Vec d → ℂ} (hv : ContDiff ℝ ∞ v) (hvper : Torus.IsZdPeriodic v)
    (Cf r : ℝ) (hCf : 0 ≤ Cf) (hr : 0 < r)
    (hderiv : HasCoordinateAnalyticL2Bounds v Cf r)
    (M : ℕ) (hscale : 1 ≤ r * (M + 1 : ℝ))
    {q : Vec d → ℂ} (hqcont : ContDiff ℝ ∞ q)
    (hqcoeff : ∀ k : Fin d → ℤ,
      Torus.smoothFourierCoeff q k =
        if ‖k‖ ≤ (M : ℝ) then 0 else Torus.smoothFourierCoeff v k) :
    (∫ x in Torus.unitCell d, ‖q x‖ ^ 2) ^ (1 / 2 : ℝ) ≤
      1024 * ((d : ℝ) + 1) * Cf * Real.exp (-r * (M + 1 : ℝ) / 512) := by
  classical
  obtain ⟨n, hn, hopt⟩ :=
    factorial_fourier_decay_optimization_exists hscale
  let b : ℝ := 2 * Real.pi * (M + 1 : ℝ)
  let bp : ℝ := b ^ n
  have hb : 0 < b := by positivity
  have hbp : 0 < bp := by positivity
  have hderivParseval (i : Fin d) :
      HasSum (fun k : Fin d → ℤ =>
        ‖Torus.smoothFourierCoeff (coordDerivIter i n v) k‖ ^ 2)
        (∫ x in Torus.unitCell d,
          ‖coordDerivIter i n v x‖ ^ 2) :=
    Torus.hasSum_sq_smoothFourierCoeff
      (coordDerivIter_contDiff_top i n hv).continuous
  let derivSq : Fin d → (Fin d → ℤ) → ℝ := fun i k =>
    ‖Torus.smoothFourierCoeff (coordDerivIter i n v) k‖ ^ 2
  have hderivSum : HasSum (fun k : Fin d → ℤ => ∑ i : Fin d, derivSq i k)
      (∑ i : Fin d, ∫ x in Torus.unitCell d,
        ‖coordDerivIter i n v x‖ ^ 2) := by
    apply hasSum_sum (s := Finset.univ)
    intro i hi
    simpa [derivSq] using hderivParseval i
  have hmajor : HasSum
      (fun k : Fin d → ℤ => (bp ^ 2)⁻¹ * ∑ i : Fin d, derivSq i k)
      ((bp ^ 2)⁻¹ * ∑ i : Fin d, ∫ x in Torus.unitCell d,
        ‖coordDerivIter i n v x‖ ^ 2) := hderivSum.mul_left _
  have hcoeffMajor (k : Fin d → ℤ) :
      ‖Torus.smoothFourierCoeff q k‖ ^ 2 ≤
        (bp ^ 2)⁻¹ * ∑ i : Fin d, derivSq i k := by
    by_cases hk : ‖k‖ ≤ (M : ℝ)
    · simp only [hqcoeff, hk, ↓reduceIte, norm_zero, ne_eq, OfNat.ofNat_ne_zero,
        not_false_eq_true, zero_pow]
      positivity
    · have hlarge : (M : ℝ) < ‖k‖ := lt_of_not_ge hk
      obtain ⟨i, hi⟩ := exists_coordinate_ge_of_piNorm_gt hd hlarge
      have hmult := smoothFourierCoeff_coordDerivIter
        hd i n hv hvper k
      have hmultNorm :
          ‖Torus.smoothFourierCoeff (coordDerivIter i n v) k‖ =
            (2 * Real.pi * ‖(k i : ℝ)‖) ^ n *
              ‖Torus.smoothFourierCoeff v k‖ := by
        rw [hmult, norm_mul, norm_pow]
        have hbase :
            ‖2 * Real.pi * Complex.I * (k i : ℂ)‖ =
              2 * Real.pi * ‖(k i : ℝ)‖ := by
          simp [Complex.norm_I, Complex.norm_intCast,
            abs_of_nonneg Real.pi_pos.le]
        rw [hbase]
      have hbasele : b ≤ 2 * Real.pi * ‖(k i : ℝ)‖ := by
        dsimp [b]
        exact mul_le_mul_of_nonneg_left hi (by positivity)
      have hpowle : bp ≤ (2 * Real.pi * ‖(k i : ℝ)‖) ^ n :=
        pow_le_pow_left₀ hb.le hbasele n
      have hscaled : bp * ‖Torus.smoothFourierCoeff v k‖ ≤
          ‖Torus.smoothFourierCoeff (coordDerivIter i n v) k‖ := by
        rw [hmultNorm]
        exact mul_le_mul_of_nonneg_right hpowle (norm_nonneg _)
      have hscaledSq := (sq_le_sq₀
        (mul_nonneg (pow_nonneg hb.le _) (norm_nonneg _))
        (norm_nonneg _)).2 hscaled
      have hratio : ‖Torus.smoothFourierCoeff v k‖ ^ 2 ≤
          ‖Torus.smoothFourierCoeff (coordDerivIter i n v) k‖ ^ 2 / bp ^ 2 := by
        apply (le_div_iff₀ (sq_pos_of_pos hbp)).2
        calc
          ‖Torus.smoothFourierCoeff v k‖ ^ 2 * bp ^ 2 =
              (bp * ‖Torus.smoothFourierCoeff v k‖) ^ 2 := by ring
          _ ≤ _ := hscaledSq
      have hsingle : derivSq i k ≤ ∑ j : Fin d, derivSq j k := by
        change ‖Torus.smoothFourierCoeff (coordDerivIter i n v) k‖ ^ 2 ≤
          ∑ j : Fin d,
            ‖Torus.smoothFourierCoeff (coordDerivIter j n v) k‖ ^ 2
        exact Finset.single_le_sum (s := Finset.univ)
          (f := fun j : Fin d =>
            ‖Torus.smoothFourierCoeff (coordDerivIter j n v) k‖ ^ 2)
          (fun j hj => sq_nonneg _) (Finset.mem_univ i)
      have hratio' : ‖Torus.smoothFourierCoeff v k‖ ^ 2 ≤
          (∑ j : Fin d, derivSq j k) / bp ^ 2 := by
        calc
          _ ≤ derivSq i k / bp ^ 2 := by simpa [derivSq] using hratio
          _ ≤ _ := div_le_div_of_nonneg_right hsingle
            (by positivity : 0 ≤ bp ^ 2)
      have hqvalue : ‖Torus.smoothFourierCoeff q k‖ =
          ‖Torus.smoothFourierCoeff v k‖ := by
        rw [hqcoeff k]
        simp [hk]
      calc
        ‖Torus.smoothFourierCoeff q k‖ ^ 2 =
            ‖Torus.smoothFourierCoeff v k‖ ^ 2 := by rw [hqvalue]
        _ ≤ (∑ j : Fin d, derivSq j k) / bp ^ 2 := hratio'
        _ = (bp ^ 2)⁻¹ * ∑ j : Fin d, derivSq j k := by
          rw [div_eq_mul_inv]
          ring
  have hqParseval := Torus.hasSum_sq_smoothFourierCoeff hqcont.continuous
  have hsumBound := Summable.tsum_le_tsum hcoeffMajor
    hqParseval.summable hmajor.summable
  rw [hqParseval.tsum_eq, hmajor.tsum_eq] at hsumBound
  have hderivSqBound (i : Fin d) :
      (∫ x in Torus.unitCell d,
        ‖coordDerivIter i n v x‖ ^ 2) ≤
        (Cf * (n.factorial : ℝ) / r ^ n) ^ 2 := by
    have hsrc : Real.sqrt
        (∫ x in Torus.unitCell d,
          ‖coordDerivIter i n v x‖ ^ 2) ≤
          Cf * (n.factorial : ℝ) / r ^ n := by
      simpa only [Real.sqrt_eq_rpow] using hderiv i n
    have hsrcNonneg : 0 ≤ Cf * (n.factorial : ℝ) / r ^ n := by positivity
    have hsquare := (sq_le_sq₀ (Real.sqrt_nonneg _) hsrcNonneg).2 hsrc
    have hI : 0 ≤ ∫ x in Torus.unitCell d,
        ‖coordDerivIter i n v x‖ ^ 2 := integral_nonneg fun _ => sq_nonneg _
    rw [Real.sq_sqrt hI] at hsquare
    exact hsquare
  have hsumDerivBound :
      (∑ i : Fin d, ∫ x in Torus.unitCell d,
        ‖coordDerivIter i n v x‖ ^ 2) ≤
      (d : ℝ) * (Cf * (n.factorial : ℝ) / r ^ n) ^ 2 := by
    calc
      _ ≤ ∑ _i : Fin d, (Cf * (n.factorial : ℝ) / r ^ n) ^ 2 :=
        Finset.sum_le_sum fun i hi => hderivSqBound i
      _ = _ := by simp
  let ratio : ℝ := (n.factorial : ℝ) / (r ^ n * bp)
  have henergy : (∫ x in Torus.unitCell d, ‖q x‖ ^ 2) ≤
      (d : ℝ) * (Cf * ratio) ^ 2 := by
    calc
      _ ≤ (bp ^ 2)⁻¹ * (∑ i : Fin d, ∫ x in Torus.unitCell d,
          ‖coordDerivIter i n v x‖ ^ 2) := hsumBound
      _ ≤ (bp ^ 2)⁻¹ * ((d : ℝ) * (Cf * (n.factorial : ℝ) / r ^ n) ^ 2) :=
        mul_le_mul_of_nonneg_left hsumDerivBound (by positivity)
      _ = (d : ℝ) * ((Cf * (n.factorial : ℝ) / r ^ n) / bp) ^ 2 := by
        field_simp [hbp.ne']
      _ = (d : ℝ) * (Cf * ratio) ^ 2 := by
        have hratioEq : (Cf * (n.factorial : ℝ) / r ^ n) / bp =
            Cf * ratio := by
          dsimp [ratio]
          field_simp [hr.ne']
        rw [hratioEq]
  have hdenEq : r ^ n * bp =
      (2 * Real.pi * (r * (M + 1 : ℝ))) ^ n := by
    rw [show 2 * Real.pi * (r * (M + 1 : ℝ)) =
        r * (2 * Real.pi * (M + 1 : ℝ)) by ring, mul_pow]
  have hratioBound : ratio ≤ 512 * Real.exp (-r * (M + 1 : ℝ) / 512) := by
    have hratioEq : ratio = (n.factorial : ℝ) /
        (2 * Real.pi * (r * (M + 1 : ℝ))) ^ n := by
      dsimp [ratio]
      rw [hdenEq]
    rw [hratioEq]
    simpa only [show -(r * (M + 1 : ℝ)) / 512 =
      -r * (M + 1 : ℝ) / 512 by ring] using hopt
  have hratioNonneg : 0 ≤ ratio := by positivity
  have htailNonneg : 0 ≤ 1024 * ((d : ℝ) + 1) * Cf *
      Real.exp (-r * (M + 1 : ℝ) / 512) := by positivity
  have henergy' : (∫ x in Torus.unitCell d, ‖q x‖ ^ 2) ≤
      (1024 * ((d : ℝ) + 1) * Cf * Real.exp (-r * (M + 1 : ℝ) / 512)) ^ 2 := by
    have hprod : Cf * ratio ≤ Cf *
        (512 * Real.exp (-r * (M + 1 : ℝ) / 512)) :=
      mul_le_mul_of_nonneg_left hratioBound hCf
    have hsq := (sq_le_sq₀ (mul_nonneg hCf hratioNonneg)
      (mul_nonneg hCf (mul_nonneg (by norm_num) (Real.exp_nonneg _)))).2 hprod
    have hdim : 0 ≤ (d : ℝ) := by positivity
    have hz : 0 ≤ Cf * Real.exp (-r * (M + 1 : ℝ) / 512) := by positivity
    have hfac : (d : ℝ) * 512 ^ 2 ≤ (1024 * ((d : ℝ) + 1)) ^ 2 := by
      nlinarith [sq_nonneg (d : ℝ)]
    calc
      _ ≤ (d : ℝ) * (Cf * ratio) ^ 2 := henergy
      _ ≤ (d : ℝ) * (Cf * (512 *
          Real.exp (-r * (M + 1 : ℝ) / 512))) ^ 2 :=
        mul_le_mul_of_nonneg_left hsq hdim
      _ = ((d : ℝ) * 512 ^ 2) *
          (Cf * Real.exp (-r * (M + 1 : ℝ) / 512)) ^ 2 := by ring
      _ ≤ (1024 * ((d : ℝ) + 1)) ^ 2 *
          (Cf * Real.exp (-r * (M + 1 : ℝ) / 512)) ^ 2 :=
        mul_le_mul_of_nonneg_right hfac (sq_nonneg _)
      _ = _ := by ring_nf
  have hroot := Real.sqrt_le_sqrt henergy'
  rw [Real.sqrt_sq_eq_abs, abs_of_nonneg htailNonneg] at hroot
  simpa only [Real.sqrt_eq_rpow] using hroot

theorem smoothFourierCoeff_euclideanCutoff
    (M : ℕ) (a : (Fin d → ℤ) → ℂ)
    (ha : ∀ k, a (-k) = star (a k)) (q : Fin d → ℤ) :
    Torus.smoothFourierCoeff
        (fun x => (euclideanFourierCutoff M a x : ℂ)) q =
      if q ∈ frequencyBall M then a q else 0 := by
  let pC : Vec d → ℂ := fun x => (euclideanFourierCutoff M a x : ℂ)
  have hcont : Continuous pC := by
    exact (Complex.ofRealCLM.contDiff.comp
      (euclideanFourierCutoff_contDiff M a)).continuous
  have hper : Torus.IsZdPeriodic pC := by
    intro k x
    exact congrArg Complex.ofReal (euclideanFourierCutoff_periodic M a x k)
  let PF : C(UnitAddTorus (Fin d), ℂ) :=
    ⟨Torus.periodicToTorus pC,
      periodicToTorus_continuous_of_periodic hcont hper⟩
  have hPF : PF = fourierCutoff M a := by
    ext y
    change Torus.periodicToTorus pC y = _
    change Torus.periodicToTorus
        (fun x => (euclideanFourierCutoff M a x : ℂ)) y = _
    rw [periodicToTorus_euclideanFourierCutoff M a y]
    exact congrFun (realFourierCutoff_complexification M a ha) y
  calc
    Torus.smoothFourierCoeff pC q = UnitAddTorus.mFourierCoeff PF q :=
      (mFourierCoeff_periodicToTorus_eq_smooth hper hcont q).symm
    _ = UnitAddTorus.mFourierCoeff (fourierCutoff M a) q := by rw [hPF]
    _ = if q ∈ frequencyBall M then a q else 0 :=
      mFourierCoeff_fourierCutoff M a q

/-- Low-frequency projection using the smooth Fourier coefficients of a real function. -/
def lowProjection (f : Vec d → ℝ) (M : ℕ) : Vec d → ℝ :=
  euclideanFourierCutoff M
    (fun k => Torus.smoothFourierCoeff (fun x => (f x : ℂ)) k)

/-- Remainder after subtracting the low-frequency projection. -/
def highRemainder (f : Vec d → ℝ) (M : ℕ) : Vec d → ℝ :=
  fun x => f x - lowProjection f M x

theorem lowProjection_contDiff {f : Vec d → ℝ} (M : ℕ) :
    ContDiff ℝ ⊤ (lowProjection f M) :=
  euclideanFourierCutoff_contDiff M _

theorem lowProjection_periodic {f : Vec d → ℝ} (M : ℕ) :
    IsZPeriodic (lowProjection f M) :=
  euclideanFourierCutoff_periodic M _

theorem highRemainder_contDiff {f : Vec d → ℝ}
    (hf : ContDiff ℝ ∞ f) (M : ℕ) :
    ContDiff ℝ ∞ (highRemainder f M) := by
  exact hf.sub ((lowProjection_contDiff M).of_le le_top)

theorem highRemainder_periodic {f : Vec d → ℝ}
    (hper : IsZPeriodic f) (M : ℕ) :
    IsZPeriodic (highRemainder f M) := by
  intro x k
  simp [highRemainder, hper x k, lowProjection_periodic M x k]

theorem lowHighCoordinateAnalyticL2Bounds
    (hd : 0 < d) {f : Vec d → ℝ} (hf : ContDiff ℝ ∞ f)
    (hper : IsZPeriodic f) (Cf r : ℝ) (hderiv :
      HasCoordinateAnalyticL2Bounds (fun x => (f x : ℂ)) Cf r)
    (M : ℕ) :
    HasCoordinateAnalyticL2Bounds
        (fun x => (lowProjection f M x : ℂ)) Cf r ∧
    HasCoordinateAnalyticL2Bounds
        (fun x => (highRemainder f M x : ℂ)) Cf r := by
  let a : (Fin d → ℤ) → ℂ :=
    fun k => Torus.smoothFourierCoeff (fun x => (f x : ℂ)) k
  have hfC : ContDiff ℝ ∞ (fun x => (f x : ℂ)) :=
    Complex.ofRealCLM.contDiff.comp hf
  have hfperC : Torus.IsZdPeriodic (fun x => (f x : ℂ)) := by
    intro k x
    exact congrArg Complex.ofReal (hper x k)
  have hlowC : ContDiff ℝ ∞ (fun x => (lowProjection f M x : ℂ)) := by
    exact Complex.ofRealCLM.contDiff.comp ((lowProjection_contDiff M).of_le le_top)
  have hlowPer : Torus.IsZdPeriodic (fun x => (lowProjection f M x : ℂ)) := by
    intro k x
    exact congrArg Complex.ofReal (lowProjection_periodic M x k)
  have hhighC : ContDiff ℝ ∞ (fun x => (highRemainder f M x : ℂ)) := by
    exact Complex.ofRealCLM.contDiff.comp (highRemainder_contDiff hf M)
  have hhighPer : Torus.IsZdPeriodic (fun x => (highRemainder f M x : ℂ)) := by
    intro k x
    exact congrArg Complex.ofReal (highRemainder_periodic hper M x k)
  have hlowCoeff (k : Fin d → ℤ) :
      Torus.smoothFourierCoeff
        (fun x => (lowProjection f M x : ℂ)) k =
        if k ∈ frequencyBall M then a k else 0 := by
    exact smoothFourierCoeff_euclideanCutoff M a
      (smoothFourierCoeff_real_neg (f := f)) k
  have hhighCoeff (k : Fin d → ℤ) :
      Torus.smoothFourierCoeff
        (fun x => (highRemainder f M x : ℂ)) k =
        if ‖k‖ ≤ (M : ℝ) then 0 else a k := by
    have hcast : (fun x => (highRemainder f M x : ℂ)) =
        (fun x => (f x : ℂ) - (lowProjection f M x : ℂ)) := by
      funext x
      simp [highRemainder]
    have hsub := smoothFourierCoeff_sub
      (f := fun x => (f x : ℂ))
      (g := fun x => (lowProjection f M x : ℂ))
      hfC.continuous hlowC.continuous k
    rw [hcast, hsub, hlowCoeff]
    by_cases hk : k ∈ frequencyBall M
    · have hball : ‖k‖ ≤ (M : ℝ) := mem_frequencyBall.mp hk
      simp [a, hk, hball]
    · have hball : ¬ ‖k‖ ≤ (M : ℝ) := by
        simpa [mem_frequencyBall] using hk
      simp [a, hk, hball]
  have hlowdom (i : Fin d) (n : ℕ) (k : Fin d → ℤ) :
      ‖Torus.smoothFourierCoeff
          (coordDerivIter i n (fun x => (lowProjection f M x : ℂ))) k‖ ≤
        ‖Torus.smoothFourierCoeff (coordDerivIter i n
          (fun x => (f x : ℂ))) k‖ := by
    rw [smoothFourierCoeff_coordDerivIter hd
        i n hlowC hlowPer k,
      smoothFourierCoeff_coordDerivIter hd
        i n hfC hfperC k, hlowCoeff]
    by_cases hk : k ∈ frequencyBall M
    · simp [a, hk]
    · have hball : ¬ ‖k‖ ≤ (M : ℝ) := by
        simpa [mem_frequencyBall] using hk
      simp only [hk, ↓reduceIte, mul_zero, norm_zero, Complex.norm_mul, norm_pow,
          Complex.norm_ofNat,
        Complex.norm_real, Real.norm_eq_abs, Real.abs_pi, Complex.norm_I, mul_one,
            Complex.norm_intCast, ge_iff_le]
      positivity
  have hhighdom (i : Fin d) (n : ℕ) (k : Fin d → ℤ) :
      ‖Torus.smoothFourierCoeff
          (coordDerivIter i n (fun x => (highRemainder f M x : ℂ))) k‖ ≤
        ‖Torus.smoothFourierCoeff (coordDerivIter i n
          (fun x => (f x : ℂ))) k‖ := by
    rw [smoothFourierCoeff_coordDerivIter hd
        i n hhighC hhighPer k,
      smoothFourierCoeff_coordDerivIter hd
        i n hfC hfperC k, hhighCoeff]
    by_cases hk : ‖k‖ ≤ (M : ℝ)
    · simp only [hk, ↓reduceIte, mul_zero, norm_zero, Complex.norm_mul, norm_pow,
        Complex.norm_ofNat,
        Complex.norm_real, Real.norm_eq_abs, Real.abs_pi, Complex.norm_I, mul_one,
            Complex.norm_intCast]
      positivity
    · simp [a, hk]
  constructor
  · exact hasCoordinateAnalyticL2Bounds_of_fourierDomination
      hlowC hlowPer hfC hfperC Cf r hlowdom hderiv
  · exact hasCoordinateAnalyticL2Bounds_of_fourierDomination
      hhighC hhighPer hfC hfperC Cf r hhighdom hderiv

theorem lowProjectionL2_le {f : Vec d → ℝ}
    (hf : ContDiff ℝ ∞ f) (M : ℕ) :
    (∫ x in Torus.unitCell d, (lowProjection f M x) ^ 2) ^
      (1 / 2 : ℝ) ≤
    (∫ x in Torus.unitCell d, f x ^ 2) ^ (1 / 2 : ℝ) := by
  let fC : Vec d → ℂ := fun x => (f x : ℂ)
  let pC : Vec d → ℂ := fun x => (lowProjection f M x : ℂ)
  let a : (Fin d → ℤ) → ℂ := fun k => Torus.smoothFourierCoeff fC k
  have hfC : ContDiff ℝ ∞ fC := Complex.ofRealCLM.contDiff.comp hf
  have hpC : ContDiff ℝ ∞ pC :=
    Complex.ofRealCLM.contDiff.comp ((lowProjection_contDiff M).of_le le_top)
  have hcoeff (k : Fin d → ℤ) : Torus.smoothFourierCoeff pC k =
      if k ∈ frequencyBall M then a k else 0 := by
    exact smoothFourierCoeff_euclideanCutoff M a
      (smoothFourierCoeff_real_neg (f := f)) k
  have hterm (k : Fin d → ℤ) :
      ‖Torus.smoothFourierCoeff pC k‖ ^ 2 ≤
        ‖Torus.smoothFourierCoeff fC k‖ ^ 2 := by
    rw [hcoeff]
    by_cases hk : k ∈ frequencyBall M
    · simp [a, fC, hk]
    · simp [a, fC, hk]
  have hsumP := Torus.hasSum_sq_smoothFourierCoeff hpC.continuous
  have hsumF := Torus.hasSum_sq_smoothFourierCoeff hfC.continuous
  have htsum := Summable.tsum_le_tsum hterm hsumP.summable hsumF.summable
  rw [hsumP.tsum_eq, hsumF.tsum_eq] at htsum
  have hpSq : ∫ x in Torus.unitCell d, ‖pC x‖ ^ 2 =
      ∫ x in Torus.unitCell d, (lowProjection f M x) ^ 2 := by
    apply setIntegral_congr_fun (Torus.measurableSet_unitCell d)
    intro x hx
    simp [pC, Complex.norm_real, sq_abs]
  have hfSq : ∫ x in Torus.unitCell d, ‖fC x‖ ^ 2 =
      ∫ x in Torus.unitCell d, f x ^ 2 := by
    apply setIntegral_congr_fun (Torus.measurableSet_unitCell d)
    intro x hx
    simp [fC, Complex.norm_real, sq_abs]
  rw [hpSq, hfSq] at htsum
  simpa only [Real.sqrt_eq_rpow] using Real.sqrt_le_sqrt htsum

theorem unitCellSet_eq_torusUnitCell (d : ℕ) :
    unitCellSet d = Torus.unitCell d := by
  ext x
  simp [unitCellSet, Torus.unitCell, Torus.unitCellAt]

theorem coordDeriv_realCast_ergodic {f : Vec d → ℝ}
    (hf : ContDiff ℝ 1 f) (i : Fin d) (x : Vec d) :
    Torus.coordDeriv i (fun y => (f y : ℂ)) x =
      (fderiv ℝ f x (Homogenization.basisVec i) : ℂ) := by
  have hreal := (hf.contDiffAt (x := x)).differentiableAt (by norm_num)
  change fderiv ℝ (Complex.ofRealCLM ∘ f) x
    (Homogenization.basisVec i) = _
  rw [fderiv_comp x Complex.ofRealCLM.differentiableAt hreal]
  simp [Homogenization.basisVec]

theorem cellMemLp_two_of_localSquare
    {h : Vec d → ℝ} (hhmeas : AEStronglyMeasurable h (volume : Measure (Vec d)))
    (hhsq : LocallyIntegrable (fun x => |h x| ^ 2) (volume : Measure (Vec d))) :
    MemLp h 2 ((volume : Measure (Vec d)).restrict (Torus.unitCell d)) ∧
    MemLp (fun x => (h x : ℂ)) 2
      ((volume : Measure (Vec d)).restrict (Torus.unitCell d)) := by
  have hcellSq : IntegrableOn (fun x => h x ^ 2) (Torus.unitCell d)
      (volume : Measure (Vec d)) := by
    have hcube := hhsq.integrableOn_isCompact (by
      change IsCompact (Set.pi Set.univ fun _ : Fin d => Set.Icc (0 : ℝ) 1)
      exact isCompact_univ_pi fun _ => isCompact_Icc)
    have hmono := hcube.mono_set unitCell_subset_closedUnitCube
    simpa [sq_abs] using hmono
  let μc := (volume : Measure (Vec d)).restrict (Torus.unitCell d)
  have hmeasCell : AEStronglyMeasurable h μc := hhmeas.restrict
  have hcomplexMeas : AEStronglyMeasurable (fun x => (h x : ℂ)) μc :=
    Complex.continuous_ofReal.comp_aestronglyMeasurable hmeasCell
  have hrealSq : Integrable (fun x => h x ^ 2) μc := by
    simpa [μc, IntegrableOn] using hcellSq
  have hrealMem : MemLp h 2 μc :=
    (memLp_two_iff_integrable_sq hmeasCell).2 hrealSq
  have hcomplexSq : Integrable (fun x => ‖(h x : ℂ)‖ ^ 2) μc := by
    simpa [μc, IntegrableOn, sq_abs] using hcellSq
  have hcellMem : MemLp (fun x => (h x : ℂ)) 2 μc :=
    (memLp_two_iff_integrable_sq_norm hcomplexMeas).2 hcomplexSq
  exact ⟨hrealMem, hcellMem⟩

/-- An `L²` function with a Fourier gap has the reciprocal-frequency
homogeneous dual bound in the cell normalization of the H⁻¹ test space. -/
theorem homogeneousHMinusOneNorm_le_of_torusFourierGap
    (hd : 0 < d) {h : Vec d → ℝ}
    (hh : MemLp (fun x => (h x : ℂ)) (ENNReal.ofReal (2 : ℝ))
      ((volume : Measure (Vec d)).restrict (Torus.unitCell d)))
    (M : ℝ) (hM : 0 < M)
    (hgap : ∀ k : Fin d → ℤ, ‖k‖ < M →
      UnitAddTorus.mFourierCoeff
        (torusFunction (fun x => (h x : ℂ))) k = 0) :
    homogeneousHMinusOneNorm h ≤ ENNReal.ofReal
      ((2 * Real.pi * M)⁻¹ *
        (∫ x in Torus.unitCell d, h x ^ 2) ^ (1 / 2 : ℝ)) := by
  classical
  let HT : UnitAddTorus (Fin d) → ℂ :=
    torusFunction (fun x => (h x : ℂ))
  have hHTmem : MemLp HT 2 (volume : Measure (UnitAddTorus (Fin d))) := by
    simpa [HT] using memLp_torusFunction_two_of_cellL2 hh
  have hHTnorm :
      ∫ x : UnitAddTorus (Fin d), ‖HT x‖ ^ 2 =
        ∫ x in Torus.unitCell d, h x ^ 2 := by
    rw [show (fun x : UnitAddTorus (Fin d) => ‖HT x‖ ^ 2) =
      Torus.periodicToTorus (fun x => h x ^ 2) by
        funext x
        have hrep : Torus.unitTorusRepresentative d x = unitCellRepresentative x := by
          funext i
          rfl
        simp only [HT, torusFunction, Torus.periodicToTorus]
        rw [hrep.symm]
        simp [Complex.norm_real, sq_abs]]
    exact Torus.integral_periodicToTorus_eq_unitCell (fun x => h x ^ 2)
  apply iSup_le
  intro φ
  let ψ := φ.val
  have hψsmooth : ContDiff ℝ 1 ψ := φ.property.1.of_le (by simp)
  have hψC : ContDiff ℝ ∞ (fun x => (ψ x : ℂ)) :=
    Complex.ofRealCLM.contDiff.comp φ.property.1
  have hψper : Torus.IsZdPeriodic (fun x => (ψ x : ℂ)) := by
    intro k x
    exact congrArg Complex.ofReal (φ.property.2.1 x k)
  have hgradEq :
      ∑ i : Fin d, ∫ x in Torus.unitCell d,
        ‖Torus.coordDeriv i (fun x => (ψ x : ℂ)) x‖ ^ 2 =
        gradientL2SquaredAverage ψ := by
    unfold gradientL2SquaredAverage
    rw [cellAverage_eq_unitCellIntegral, unitCellSet_eq_torusUnitCell]
    calc
      (∑ i : Fin d, ∫ x in Torus.unitCell d,
        ‖Torus.coordDeriv i (fun x => (ψ x : ℂ)) x‖ ^ 2) =
          ∫ x in Torus.unitCell d, ∑ i : Fin d,
            ‖Torus.coordDeriv i (fun x => (ψ x : ℂ)) x‖ ^ 2 := by
        symm
        rw [integral_finsetSum]
        intro i hi
        exact continuous_unitCell_integrable
          ((Torus.continuous_coordDeriv i (hψC.of_le (by norm_num))).norm.pow 2)
      _ = ∫ x in Torus.unitCell d,
          ∑ i : Fin d, (fderiv ℝ ψ x (Homogenization.basisVec i)) ^ 2 := by
            apply setIntegral_congr_fun (Torus.measurableSet_unitCell d)
            intro x hx
            apply Finset.sum_congr rfl
            intro i hi
            rw [coordDeriv_realCast_ergodic hψsmooth i x]
            simp
      _ = ∫ x in Torus.unitCell d,
          ∑ i : Fin d,
            (fderiv ℝ ψ x (Pi.single i (1 : ℝ))) ^ 2 := by
              apply setIntegral_congr_fun (Torus.measurableSet_unitCell d)
              intro x hx
              simp [Homogenization.basisVec]
  have hgrad :
      (∑ i : Fin d, ∫ x in Torus.unitCell d,
        ‖Torus.coordDeriv i (fun x => (ψ x : ℂ)) x‖ ^ 2) ^
          (1 / 2 : ℝ) ≤ 1 := by
    have hgradSq :
        (∑ i : Fin d, ∫ x in Torus.unitCell d,
          ‖Torus.coordDeriv i (fun x => (ψ x : ℂ)) x‖ ^ 2) ≤ 1 := by
      rw [hgradEq]
      exact φ.property.2.2.2
    have hsqrt := Real.sqrt_le_one.mpr hgradSq
    simpa only [Real.sqrt_eq_rpow] using hsqrt
  have htestPeriodic : Torus.IsZdPeriodic (fun x => (ψ x : ℂ)) := hψper
  have hpair := torusPairing_le_of_fourierGap
    hd HT hHTmem
    (hψC.of_le (by norm_num)) htestPeriodic M hM hgap
  have hpairEq :
      (∫ x : UnitAddTorus (Fin d),
        star (HT x) * Torus.periodicToTorus (fun x => (ψ x : ℂ)) x) =
      (cellAverage (fun x => h x * ψ x) : ℂ) := by
    calc
      _ = ∫ x : UnitAddTorus (Fin d),
          ((torusFunction (fun y => h y * ψ y) x : ℝ) : ℂ) := by
            apply integral_congr_ae
            filter_upwards with x
            have hrep : Torus.unitTorusRepresentative d x =
                unitCellRepresentative x := by
              funext i
              rfl
            simp [HT, Torus.periodicToTorus, torusFunction,
              unitCellRepresentative, hrep]
      _ = (cellAverage (fun x => h x * ψ x) : ℂ) := by
            rw [integral_complex_ofReal, cellAverage_eq_torus_integral]
  have hL2nonneg : 0 ≤
      (∫ x in Torus.unitCell d, h x ^ 2) ^ (1 / 2 : ℝ) :=
    Real.rpow_nonneg (integral_nonneg fun _ => sq_nonneg _) _
  have hpairReal : |cellAverage (fun x => h x * ψ x)| ≤
      (2 * Real.pi * M)⁻¹ *
        (∫ x in Torus.unitCell d, h x ^ 2) ^ (1 / 2 : ℝ) := by
    calc
      _ = ‖(cellAverage (fun x => h x * ψ x) : ℂ)‖ := by simp
      _ = ‖∫ x : UnitAddTorus (Fin d),
          star (HT x) * Torus.periodicToTorus (fun x => (ψ x : ℂ)) x‖ := by
            rw [← hpairEq]
      _ ≤ (2 * Real.pi * M)⁻¹ *
          (∫ x : UnitAddTorus (Fin d), ‖HT x‖ ^ 2) ^ (1 / 2 : ℝ) *
          (∑ i : Fin d, ∫ x in Torus.unitCell d,
            ‖Torus.coordDeriv i (fun x => (ψ x : ℂ)) x‖ ^ 2) ^
              (1 / 2 : ℝ) := hpair
      _ ≤ (2 * Real.pi * M)⁻¹ *
          (∫ x in Torus.unitCell d, h x ^ 2) ^ (1 / 2 : ℝ) := by
            rw [hHTnorm]
            have hc : 0 ≤ (2 * Real.pi * M)⁻¹ := by positivity
            have hfac : 0 ≤ (2 * Real.pi * M)⁻¹ *
                (∫ x in Torus.unitCell d, h x ^ 2) ^ (1 / 2 : ℝ) :=
              mul_nonneg hc hL2nonneg
            calc
              _ ≤ (2 * Real.pi * M)⁻¹ *
                  (∫ x in Torus.unitCell d, h x ^ 2) ^ (1 / 2 : ℝ) * 1 :=
                mul_le_mul_of_nonneg_left hgrad hfac
              _ = _ := by ring
  exact ENNReal.ofReal_le_ofReal hpairReal

theorem cellAverage_eq_torusUnitCellIntegral {v : Vec d → ℝ} :
    cellAverage v = ∫ x in Torus.unitCell d, v x := by
  rw [cellAverage_eq_unitCellIntegral, unitCellSet_eq_torusUnitCell]

theorem cellAverage_add_of_locallyIntegrable {u v : Vec d → ℝ}
    (hu : LocallyIntegrable u (volume : Measure (Vec d)))
    (hv : LocallyIntegrable v (volume : Measure (Vec d))) :
    cellAverage (fun x => u x + v x) = cellAverage u + cellAverage v := by
  have hcube : IsCompact (closedUnitCube (d := d)) := by
    change IsCompact (Set.pi Set.univ fun _ : Fin d => Set.Icc (0 : ℝ) 1)
    exact isCompact_univ_pi fun _ => isCompact_Icc
  have hsumI : IntegrableOn (fun x => u x + v x) (Torus.unitCell d)
      (volume : Measure (Vec d)) :=
    (hu.add hv).integrableOn_isCompact hcube |>.mono_set unitCell_subset_closedUnitCube
  have huI : IntegrableOn u (Torus.unitCell d) (volume : Measure (Vec d)) :=
    hu.integrableOn_isCompact hcube |>.mono_set unitCell_subset_closedUnitCube
  have hvI : IntegrableOn v (Torus.unitCell d) (volume : Measure (Vec d)) :=
    hv.integrableOn_isCompact hcube |>.mono_set unitCell_subset_closedUnitCube
  rw [cellAverage_eq_torusUnitCellIntegral, cellAverage_eq_torusUnitCellIntegral,
    cellAverage_eq_torusUnitCellIntegral]
  exact integral_add huI hvI

theorem homogeneousHMinusOneNorm_add_le_of_locallyIntegrable
    {u v : Vec d → ℝ}
    (hu : LocallyIntegrable u (volume : Measure (Vec d)))
    (hv : LocallyIntegrable v (volume : Measure (Vec d))) :
    homogeneousHMinusOneNorm (fun x => u x + v x) ≤
      homogeneousHMinusOneNorm u + homogeneousHMinusOneNorm v := by
  apply iSup_le
  intro φ
  let a := cellAverage (fun x => u x * φ.val x)
  let b := cellAverage (fun x => v x * φ.val x)
  have hsum : cellAverage (fun x => (u x + v x) * φ.val x) = a + b := by
    have hfun : (fun x => (u x + v x) * φ.val x) =
        (fun x => u x * φ.val x + v x * φ.val x) := by
      funext x
      ring
    rw [hfun]
    exact cellAverage_add_of_locallyIntegrable
      (hu.mul_continuous φ.property.1.continuous)
      (hv.mul_continuous φ.property.1.continuous)
  calc
    _ = ENNReal.ofReal |a + b| := by rw [hsum]
    _ ≤ ENNReal.ofReal (|a| + |b|) :=
      ENNReal.ofReal_le_ofReal (abs_add_le a b)
    _ = ENNReal.ofReal |a| + ENNReal.ofReal |b| := by
      rw [ENNReal.ofReal_add (abs_nonneg a) (abs_nonneg b)]
    _ ≤ homogeneousHMinusOneNorm u + homogeneousHMinusOneNorm v :=
      add_le_add (dualPairing_le_homogeneousHMinusOneNorm u φ)
        (dualPairing_le_homogeneousHMinusOneNorm v φ)

/-- The square covariance estimate gives an L² bound for a slow-fast product. -/
theorem productL2_le_of_coordinateAnalyticL2Bounds
    (hd : 0 < d) {u g : Vec d → ℝ} (hu : ContDiff ℝ ∞ u) (huper : IsZPeriodic u)
    (Cf r : ℝ) (hCf : 0 ≤ Cf) (hr : 0 < r)
    (hderiv : HasCoordinateAnalyticL2Bounds (fun x => (u x : ℂ)) Cf r)
    (hg2 : LocallyIntegrable (fun x => |g x| ^ 2) (volume : Measure (Vec d)))
    {N : ℕ} (hN : 0 < N) (hfast : IsFastPeriodic N g)
    (hNr : 2 ≤ r * (N : ℝ)) :
    (∫ x in Torus.unitCell d, (u x * g x) ^ 2) ^ (1 / 2 : ℝ) ≤
      ((∫ x in Torus.unitCell d, u x ^ 2) ^ (1 / 2 : ℝ) +
        32 * (∑' k : Fin d → ℤ,
          Real.exp (-(1 / 1024 : ℝ) * ‖k‖)) ^ (1 / 2 : ℝ) *
          Cf * Real.exp (-r * (N : ℝ) / 4096)) *
        (∫ x in Torus.unitCell d, g x ^ 2) ^ (1 / 2 : ℝ) := by
  let A : ℝ := ∫ x in Torus.unitCell d, u x ^ 2
  let B : ℝ := ∫ x in Torus.unitCell d, g x ^ 2
  let C : ℝ := ∫ x in Torus.unitCell d, (u x * g x) ^ 2
  let K : ℝ := ∑' k : Fin d → ℤ,
    Real.exp (-(1 / 1024 : ℝ) * ‖k‖)
  have hA : 0 ≤ A := by dsimp [A]; exact integral_nonneg fun _ => sq_nonneg _
  have hB : 0 ≤ B := by dsimp [B]; exact integral_nonneg fun _ => sq_nonneg _
  have hK : 0 ≤ K := by
    dsimp [K]
    exact tsum_nonneg fun _ => Real.exp_nonneg _
  have hAu : cellAverage (fun x => u x ^ 2) = A := by
    dsimp [A]
    exact cellAverage_eq_torusUnitCellIntegral
  have hBabs : cellAverage (fun x => |g x| ^ 2) = B := by
    dsimp [B]
    rw [cellAverage_eq_torusUnitCellIntegral]
    apply setIntegral_congr_fun (Torus.measurableSet_unitCell d)
    intro x hx
    simp [sq_abs]
  have hBg : cellAverage (fun x => g x ^ 2) = B := by
    dsimp [B]
    exact cellAverage_eq_torusUnitCellIntegral
  have hC : cellAverage (fun x => u x ^ 2 * g x ^ 2) = C := by
    rw [cellAverage_eq_torusUnitCellIntegral]
    dsimp [C]
    apply setIntegral_congr_fun (Torus.measurableSet_unitCell d)
    intro x hx
    ring
  have hcov := cellAverage_square_mul_sub_le_of_coordinateAnalyticL2Bounds
    hd hN hu huper Cf r hCf hr hderiv hg2 hfast hNr
  have hcov' : |C - A * B| ≤
      512 * Cf ^ 2 * B * K * Real.exp (-r * (N : ℝ) / 2048) := by
    have hexp : -((r / 2) * (N : ℝ)) / 1024 =
        -r * (N : ℝ) / 2048 := by ring
    simpa [hAu, hBg, hBabs, hC, K, hexp] using hcov
  have hCup : C ≤ A * B +
      512 * Cf ^ 2 * B * K * Real.exp (-r * (N : ℝ) / 2048) := by
    have habs := abs_le.mp hcov'
    linarith
  have herr : 0 ≤
      512 * Cf ^ 2 * B * K * Real.exp (-r * (N : ℝ) / 2048) := by positivity
  let E : ℝ := 512 * Cf ^ 2 * B * K * Real.exp (-r * (N : ℝ) / 2048)
  let Y : ℝ := Real.sqrt (A * B) +
    32 * Real.sqrt K * Cf * Real.sqrt B *
      Real.exp (-r * (N : ℝ) / 4096)
  have hY : 0 ≤ Y := by positivity
  have hEsqrt : Real.sqrt E ≤
      32 * Real.sqrt K * Cf * Real.sqrt B *
        Real.exp (-r * (N : ℝ) / 4096) := by
    apply Real.sqrt_le_iff.mpr
    constructor
    · positivity
    · have hexp : Real.exp (-r * (N : ℝ) / 2048) =
          Real.exp (-r * (N : ℝ) / 4096) ^ 2 := by
        rw [pow_two, ← Real.exp_add]
        congr 1
        ring
      have hZsq :
          (32 * Real.sqrt K * Cf * Real.sqrt B *
            Real.exp (-r * (N : ℝ) / 4096)) ^ 2 =
          1024 * Cf ^ 2 * B * K *
            Real.exp (-r * (N : ℝ) / 4096) ^ 2 := by
        calc
          _ = 32 ^ 2 * (Real.sqrt K) ^ 2 * Cf ^ 2 *
              (Real.sqrt B) ^ 2 * Real.exp (-r * (N : ℝ) / 4096) ^ 2 := by ring
          _ = _ := by
            rw [Real.sq_sqrt hK, Real.sq_sqrt hB]
            ring
      have hEupper : E ≤
          (32 * Real.sqrt K * Cf * Real.sqrt B *
            Real.exp (-r * (N : ℝ) / 4096)) ^ 2 := by
        dsimp [E]
        calc
          _ = 512 * Cf ^ 2 * B * K *
              Real.exp (-r * (N : ℝ) / 4096) ^ 2 := by rw [hexp]
          _ ≤ 1024 * Cf ^ 2 * B * K *
              Real.exp (-r * (N : ℝ) / 4096) ^ 2 := by
                have hnonneg : 0 ≤ Cf ^ 2 * B * K *
                    Real.exp (-r * (N : ℝ) / 4096) ^ 2 := by positivity
                nlinarith [hnonneg]
          _ = _ := hZsq.symm
      exact hEupper
  have hABsqrt : Real.sqrt (A * B) = Real.sqrt A * Real.sqrt B :=
    Real.sqrt_mul hA B
  have hCroot : Real.sqrt C ≤ Y := by
    apply Real.sqrt_le_iff.mpr
    constructor
    · exact hY
    · have hsA : Real.sqrt (A * B) ^ 2 = A * B :=
        Real.sq_sqrt (mul_nonneg hA hB)
      have hsE : Real.sqrt E ^ 2 = E := Real.sq_sqrt herr
      have hCupE : C ≤ A * B + E := by simpa [E] using hCup
      have hcross : 0 ≤ 2 * Real.sqrt (A * B) * Real.sqrt E := by positivity
      have hsumle : Real.sqrt (A * B) + Real.sqrt E ≤
          Real.sqrt (A * B) +
            32 * Real.sqrt K * Cf * Real.sqrt B *
              Real.exp (-r * (N : ℝ) / 4096) := by
        calc
          _ = Real.sqrt E + Real.sqrt (A * B) := by ring
          _ ≤ (32 * Real.sqrt K * Cf * Real.sqrt B *
                Real.exp (-r * (N : ℝ) / 4096)) + Real.sqrt (A * B) :=
            add_le_add_left hEsqrt _
          _ = _ := by ring
      have hsumNonneg : 0 ≤ Real.sqrt (A * B) + Real.sqrt E := by positivity
      have hsumBoundNonneg : 0 ≤ Real.sqrt (A * B) +
          32 * Real.sqrt K * Cf * Real.sqrt B *
            Real.exp (-r * (N : ℝ) / 4096) := by positivity
      have hsumSq := (sq_le_sq₀ hsumNonneg hsumBoundNonneg).2 hsumle
      calc
        C ≤ A * B + E := hCupE
        _ ≤ (Real.sqrt (A * B) + Real.sqrt E) ^ 2 := by
          nlinarith [hsA, hsE, hcross]
        _ ≤ Y ^ 2 := by simpa [Y] using hsumSq
  have hYfactor : Y =
      (Real.sqrt A + 32 * Real.sqrt K * Cf *
        Real.exp (-r * (N : ℝ) / 4096)) * Real.sqrt B := by
    dsimp [Y]
    rw [hABsqrt]
    ring
  have hroot : (C) ^ (1 / 2 : ℝ) ≤ Y := by
    simpa only [Real.sqrt_eq_rpow] using hCroot
  simpa [A, B, C, K, hYfactor, Real.sqrt_eq_rpow] using hroot

end

end AVenhance.Infra.Ergodic
