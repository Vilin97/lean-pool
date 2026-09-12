/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import LeanPool.NavierStokesAndEuler.NavierStokes.HarmonicCalculus
public import LeanPool.NavierStokesAndEuler.NavierStokes.WeightedClasses
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.Calculus.Deriv.Inv
public import LeanPool.NavierStokesAndEuler.NavierStokes.JetBounds
public import LeanPool.NavierStokesAndEuler.NavierStokes.PrimaryODE
import Mathlib.Analysis.Calculus.ContDiff.Bounds
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Topology.Algebra.Module.PerfectSpace
public import LeanPool.NavierStokesAndEuler.NavierStokes.ResidualStability
import LeanPool.NavierStokesAndEuler.NavierStokes.ResidualRegularity
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
public import Mathlib.Data.Complex.Basic
public import Mathlib.Data.Fin.VecNotation
import Mathlib.Algebra.GroupWithZero.Action.Pi
import Mathlib.Data.Fintype.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith.Frontend

/-!
# Weighted classes of actual cylindrical curl corrections

All differential operators act on the actual coefficient functions. The
oscillatory carrier is removed only after applying the product rule. The
radial graph derivative and every cylindrical connection are retained.
-/

section

/-!
# Real oscillatory curl realization

The potential and curl below use actual Euclidean spatial derivatives. The
oscillatory carrier is kept separate from the stripped remainder coefficient.
-/

section

/-!
# Algebra of the curl realization in Lemma 8.8

The dot product below is bilinear, including over `ℂ`: for a real phase normal
its self-product is the real squared length. These results check the principal
symbol and the algebraic divergence cancellation. They do not establish
regularity, bounds for the differentiated amplitude, or descent from the lift.
-/

@[expose] public section

namespace NavierStokes.CurlGeometry

/-- Vec3: an abbreviation for `Fin 3 → R`. -/
abbrev Vec3 (R : Type*) := Fin 3 → R

/-- Dot, given by `u 0 * v 0 + u 1 * v 1 + u 2 * v 2`. -/
def dot {R : Type*} [CommRing R] (u v : Vec3 R) : R :=
  u 0 * v 0 + u 1 * v 1 + u 2 * v 2

/-- Cross, given by `![u 1 * v 2 - u 2 * v 1, u 2 * v 0 - u 0 * v 2, u 0 * v 1 - u 1 * v 0]`. -/
def cross {R : Type*} [CommRing R] (u v : Vec3 R) : Vec3 R :=
  ![u 1 * v 2 - u 2 * v 1,
    u 2 * v 0 - u 0 * v 2,
    u 0 * v 1 - u 1 * v 0]

theorem cross_perpendicular_left {R : Type*} [CommRing R] (u v : Vec3 R) :
    dot u (cross u v) = 0 := by
  simp only [dot, cross, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val]
  ring

theorem cross_perpendicular_right {R : Type*} [CommRing R] (u v : Vec3 R) :
    dot v (cross u v) = 0 := by
  simp only [dot, cross, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val]
  ring

/-- The vector triple-product identity, before imposing tangency. -/
theorem triple_product {R : Type*} [CommRing R] (n a : Vec3 R) :
    cross n (cross n a) = dot n a • n - dot n n • a := by
  funext j
  fin_cases j <;> simp [cross, dot] <;> ring

/-- Tangency is exactly the hypothesis eliminating the longitudinal term. -/
theorem tangent_double_cross {R : Type*} [CommRing R] (n a : Vec3 R)
    (ha : dot n a = 0) :
    cross n (cross n a) = -(dot n n • a) := by
  rw [triple_product, ha, zero_smul, zero_sub]

theorem cross_smul {R : Type*} [CommRing R] (s t : R) (u v : Vec3 R) :
    cross (s • u) (t • v) = (s * t) • cross u v := by
  funext j
  fin_cases j <;> simp [cross] <;> ring

/-- A nonzero real normal has nonzero squared length, as required in (30). -/
theorem real_dot_self_ne_zero {n : Vec3 ℝ} (hn : n ≠ 0) : dot n n ≠ 0 := by
  intro h
  have hsum : ∑ i : Fin 3, n i * n i = 0 := by
    simpa only [Fin.sum_univ_three, dot, add_assoc] using h
  have hz := (Finset.sum_eq_zero_iff_of_nonneg
    (fun i _ => mul_self_nonneg (n i))).mp hsum
  apply hn
  funext i
  exact mul_self_eq_zero.mp (hz i (Finset.mem_univ i))

/-- The normalized double cross product displayed in Lemma 8.8. -/
theorem normalized_double_cross {R : Type*} [Field R] (n a : Vec3 R)
    (hn : dot n n ≠ 0) (ha : dot n a = 0) :
    (-1 / dot n n) • cross n (cross n a) = a := by
  rw [tangent_double_cross n a ha]
  funext j
  simp only [Pi.smul_apply, Pi.neg_apply, smul_eq_mul]
  field_simp

/-- Curl symbol, given by `cross (Complex.I • ξ) A`. -/
noncomputable def curlSymbol (ξ A : Vec3 ℂ) : Vec3 ℂ :=
  cross (Complex.I • ξ) A

/-- The coefficient of the potential (30), with the oscillatory exponential
factored out. `k` is its nonzero frequency and `n` its phase normal. -/
noncomputable def potentialCoefficient (k : ℂ) (n a : Vec3 ℂ) : Vec3 ℂ :=
  (Complex.I / (k * dot n n)) • cross n a

/-- The two factors of `i` and the vector triple product give the amplitude
with the positive sign claimed in (30). -/
theorem principal_symbol_realizes (k : ℂ) (n a : Vec3 ℂ)
    (hk : k ≠ 0) (hn : dot n n ≠ 0) (ha : dot n a = 0) :
    curlSymbol (k • n) (potentialCoefficient k n a) = a := by
  unfold curlSymbol potentialCoefficient
  rw [smul_smul, cross_smul]
  have hs : (Complex.I * k) * (Complex.I / (k * dot n n)) =
      -1 / dot n n := by
    calc
      _ = (Complex.I * Complex.I) * (k / (k * dot n n)) := by ring
      _ = _ := by rw [Complex.I_mul_I]; field_simp
  rw [hs]
  exact normalized_double_cross n a hn ha

/-- Complexify, defined pointwise by `(n j : ℂ)`. -/
def complexify (n : Vec3 ℝ) : Vec3 ℂ := fun j => (n j : ℂ)

theorem complexify_dot_self (n : Vec3 ℝ) :
    dot (complexify n) (complexify n) = ((dot n n : ℝ) : ℂ) := by
  simp [complexify, dot]

/-- Specialization to the manuscript's real, nonzero phase normal and real,
nonzero frequency. The only amplitude condition is complex tangency. -/
theorem real_normal_principal_symbol (k : ℝ) (n : Vec3 ℝ) (a : Vec3 ℂ)
    (hk : k ≠ 0) (hn : n ≠ 0) (ha : dot (complexify n) a = 0) :
    curlSymbol ((k : ℂ) • complexify n)
      (potentialCoefficient k (complexify n) a) = a := by
  apply principal_symbol_realizes (k : ℂ) (complexify n) a
    (Complex.ofReal_ne_zero.mpr hk) ?_ ha
  rw [complexify_dot_self]
  exact Complex.ofReal_ne_zero.mpr (real_dot_self_ne_zero hn)

theorem curl_symbol_transverse (ξ A : Vec3 ℂ) : dot ξ (curlSymbol ξ A) = 0 := by
  unfold curlSymbol
  have h := cross_smul Complex.I (1 : ℂ) ξ A
  simp only [one_smul, mul_one] at h
  rw [h]
  simp only [dot, Pi.smul_apply, smul_eq_mul]
  have hp := cross_perpendicular_left ξ A
  dsimp [dot] at hp
  calc
    _ = Complex.I * (ξ 0 * cross ξ A 0 + ξ 1 * cross ξ A 1 + ξ 2 * cross ξ A 2) := by
      ring
    _ = 0 := by rw [hp, mul_zero]

/-! ## Cylindrical differential cancellation

This is a conditional identity for three additive differential operators on a
commutative ring of coefficient functions. In the application `q = 1/R`.
The assumptions state pairwise commutation and precisely the radial/axial
product rules for multiplication by `q` used by the calculation. They must
still be established for the manuscript's graph derivatives.
-/

/-- Cylindrical curl, given by `![q * Dθ (A 2) - Dz (A 1), Dz (A 0) - Dr (A 2), Dr (A 1) + q * A
1 - q * Dθ (A 0)]`. -/
def cylindricalCurl {F : Type*} [CommRing F]
    (Dr Dθ Dz : F →+ F) (q : F) (A : Vec3 F) : Vec3 F :=
  ![q * Dθ (A 2) - Dz (A 1),
    Dz (A 0) - Dr (A 2),
    Dr (A 1) + q * A 1 - q * Dθ (A 0)]

/-- Cylindrical div, given by `Dr (v 0) + q * v 0 + q * Dθ (v 1) + Dz (v 2)`. -/
def cylindricalDiv {F : Type*} [CommRing F]
    (Dr Dθ Dz : F →+ F) (q : F) (v : Vec3 F) : F :=
  Dr (v 0) + q * v 0 + q * Dθ (v 1) + Dz (v 2)

/-- Divergence of the full cylindrical curl, including both `1/R` terms.
No conclusion about analytic regularity is hidden in the algebraic statement. -/
theorem cylindrical_div_curl {F : Type*} [CommRing F]
    (Dr Dθ Dz : F →+ F) (q : F)
    (hrr : ∀ f, Dr (q * f) = q * Dr f - q ^ 2 * f)
    (hzq : ∀ f, Dz (q * f) = q * Dz f)
    (hrθ : ∀ f, Dr (Dθ f) = Dθ (Dr f))
    (hrz : ∀ f, Dr (Dz f) = Dz (Dr f))
    (hθz : ∀ f, Dθ (Dz f) = Dz (Dθ f))
    (A : Vec3 F) : cylindricalDiv Dr Dθ Dz q (cylindricalCurl Dr Dθ Dz q A) = 0 := by
  simp only [cylindricalDiv, cylindricalCurl, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val, map_sub, map_add]
  rw [hrr, hzq, hzq, hrθ, hrz, hθz]
  ring

end NavierStokes.CurlGeometry

end

end

@[expose] public section

noncomputable section

namespace NavierStokes.OscillatoryCurl

open ProblemStatement Set Filter
open scoped Topology BigOperators ContDiff InnerProductSpace

/-- Cross product on the same Euclidean space as the PDE target, as a bounded
bilinear map. -/
def crossLinear : Space →L[ℝ] Space →L[ℝ] Space :=
  let projection : Fin 3 → Space →L[ℝ] ℝ := EuclideanSpace.proj
  (projection 1).smulRight ((projection 2).smulRight (coordinateVector 0)) -
  (projection 2).smulRight ((projection 1).smulRight (coordinateVector 0)) +
  (projection 2).smulRight ((projection 0).smulRight (coordinateVector 1)) -
  (projection 0).smulRight ((projection 2).smulRight (coordinateVector 1)) +
  (projection 0).smulRight ((projection 1).smulRight (coordinateVector 2)) -
  (projection 1).smulRight ((projection 0).smulRight (coordinateVector 2))

/-- Cross, given by `crossLinear u v`. -/
def cross (u v : Space) : Space := crossLinear u v

theorem cross_apply (u v : Space) :
    cross u v =
      u 1 • (v 2 • coordinateVector 0) - u 2 • (v 1 • coordinateVector 0) +
      u 2 • (v 0 • coordinateVector 1) - u 0 • (v 2 • coordinateVector 1) +
      u 0 • (v 1 • coordinateVector 2) - u 1 • (v 0 • coordinateVector 2) := rfl

@[simp] theorem cross_zero (u v : Space) : (cross u v) 0 = u 1 * v 2 - u 2 * v 1 := by
  rw [cross_apply]
  simp [coordinateVector]

@[simp] theorem cross_one (u v : Space) : (cross u v) 1 = u 2 * v 0 - u 0 * v 2 := by
  rw [cross_apply]
  simp [coordinateVector]

@[simp] theorem cross_two (u v : Space) : (cross u v) 2 = u 0 * v 1 - u 1 * v 0 := by
  rw [cross_apply]
  simp [coordinateVector]

@[simp] theorem cross_smul_left (c : ℝ) (u v : Space) :
    cross (c • u) v = c • cross u v := by simp [cross]

@[simp] theorem cross_smul_right (c : ℝ) (u v : Space) :
    cross u (c • v) = c • cross u v := by simp [cross]

@[simp] theorem cross_zero_right (u : Space) : cross u 0 = 0 := by simp [cross]

theorem inner_coordinates (u v : Space) :
    ⟪u, v⟫_ℝ = u 0 * v 0 + u 1 * v 1 + u 2 * v 2 := by
  simp [PiLp.inner_apply, Fin.sum_univ_three, mul_comm]

/-- The Euclidean cross product agrees coordinatewise with the previously
checked symbol algebra. -/
theorem cross_coordinates (u v : Space) :
    (fun i : Fin 3 => (cross u v) i) = CurlGeometry.cross (fun i => u i) (fun i => v i) := by
  ext i
  fin_cases i <;> simp [CurlGeometry.cross]

theorem cross_triple (n a : Space) :
    cross n (cross n a) = ⟪n, a⟫_ℝ • n - ‖n‖ ^ 2 • a := by
  rw [EuclideanSpace.real_norm_sq_eq]
  ext i
  fin_cases i <;> simp [inner_coordinates, Fin.sum_univ_three] <;> ring

/-- The inverse-square-normal coefficient used by the real potential. -/
def normalCoefficient (n a : Space) : Space := (‖n‖ ^ 2)⁻¹ • cross n a

theorem cross_normalCoefficient {n a : Space} (hn : n ≠ 0) (ha : ⟪n, a⟫_ℝ = 0) :
    cross n (normalCoefficient n a) = -a := by
  rw [normalCoefficient, cross_smul_right, cross_triple, ha, zero_smul, zero_sub,
    smul_neg, smul_smul, inv_mul_cancel₀ (pow_ne_zero 2 (norm_ne_zero_iff.mpr hn)), one_smul]

/-- The actual Euclidean gradient map applied to a scalar derivative. -/
def gradientLinear : (Space →L[ℝ] ℝ) →L[ℝ] Space :=
  ∑ i : Fin 3, (ContinuousLinearMap.apply ℝ ℝ (coordinateVector i)).smulRight (coordinateVector i)

@[simp] theorem gradientLinear_apply (L : Space →L[ℝ] ℝ) (i : Fin 3) :
    (gradientLinear L) i = L (coordinateVector i) := by
  fin_cases i <;> simp [gradientLinear, Fin.sum_univ_three, coordinateVector]

theorem curlLinear_smulRight (L : Space →L[ℝ] ℝ) (a : Space) :
    SpatialCurl.curlLinear (L.smulRight a) = cross (gradientLinear L) a := by
  ext i
  fin_cases i <;> simp

/-- The genuine spatial curl product rule. -/
theorem curl_smul {f : Space → ℝ} {B : Space → Space} {x : Space}
    (hf : DifferentiableAt ℝ f x) (hB : DifferentiableAt ℝ B x) :
    SpatialCurl.curl (fun y => f y • B y) x =
      cross (gradientLinear (fderiv ℝ f x)) (B x) + f x • SpatialCurl.curl B x := by
  unfold SpatialCurl.curl
  rw [fderiv_fun_smul hf hB, map_add, map_smul, curlLinear_smulRight]
  exact add_comm _ _

/-- Carrier, given by `-Real.sin (k * s) / k`. -/
def carrier (k s : ℝ) : ℝ := -Real.sin (k * s) / k

theorem carrier_hasDerivAt {k : ℝ} (hk : k ≠ 0) (s : ℝ) :
    HasDerivAt (carrier k) (-Real.cos (k * s)) s := by
  have h := ((Real.hasDerivAt_sin (k * s)).comp s
    ((hasDerivAt_id s).const_mul k)).neg.div_const k
  convert! h using 1
  field_simp

theorem carrier_contDiff (k : ℝ) : ContDiff ℝ ∞ (carrier k) :=
  ((Real.contDiff_sin.comp (contDiff_const.mul contDiff_id)).neg).div_const k

/-- Physical spatial phase normal, with time held fixed. -/
def phaseNormal (Φ : PressureField) : VelocityField :=
  fun z => gradientLinear (fderiv ℝ (fun y : Space => Φ (z.1, y)) z.2)

theorem phaseNormal_eq_pressureGradient (Φ : PressureField) (z : SpaceTime) :
    phaseNormal Φ z = pressureGradient Φ z.1 z.2 := by
  simp [phaseNormal, gradientLinear, pressureGradient]

/-- Coefficient, defined pointwise by `normalCoefficient (phaseNormal Φ z) (a z)`. -/
def coefficient (Φ : PressureField) (a : VelocityField) : VelocityField :=
  fun z => normalCoefficient (phaseNormal Φ z) (a z)

/-- `-sin(k Φ) (n × a)/(k |n|²)`, expressed by scalar multiplication. -/
def potential (k : ℝ) (Φ : PressureField) (a : VelocityField) : VelocityField :=
  fun z => carrier k (Φ z) • coefficient Φ a z

/-- Wave, given by `SpatialCurl.spatialCurl (potential k Φ a)`. -/
def wave (k : ℝ) (Φ : PressureField) (a : VelocityField) : VelocityField :=
  SpatialCurl.spatialCurl (potential k Φ a)

theorem phaseNormal_contDiffOn {U : Set SpaceTime} {Φ : PressureField}
    (hU : IsOpen U) (hΦ : ContDiffOn ℝ ∞ Φ U) : ContDiffOn ℝ ∞ (phaseNormal Φ) U :=
  (ResidualRegularity.contDiffOn_space_fderiv hU hΦ (m := ∞) (by simp)).continuousLinearMap_comp
    gradientLinear

theorem coefficient_contDiffOn {U : Set SpaceTime} {Φ : PressureField} {a : VelocityField}
    (hU : IsOpen U) (hΦ : ContDiffOn ℝ ∞ Φ U) (ha : ContDiffOn ℝ ∞ a U)
    (hn : ∀ z ∈ U, phaseNormal Φ z ≠ 0) : ContDiffOn ℝ ∞ (coefficient Φ a) U := by
  have hN := phaseNormal_contDiffOn hU hΦ
  have hnorm : ContDiffOn ℝ ∞ (fun z => ‖phaseNormal Φ z‖ ^ 2) U :=
    (contDiff_norm_sq ℝ).comp_contDiffOn hN
  exact (hnorm.inv (fun z hz => pow_ne_zero 2 (norm_ne_zero_iff.mpr (hn z hz)))).smul
    ((hN.continuousLinearMap_comp crossLinear).clm_apply ha)

theorem potential_contDiffOn {U : Set SpaceTime} {Φ : PressureField} {a : VelocityField}
    (k : ℝ) (hU : IsOpen U) (hΦ : ContDiffOn ℝ ∞ Φ U) (ha : ContDiffOn ℝ ∞ a U)
    (hn : ∀ z ∈ U, phaseNormal Φ z ≠ 0) : ContDiffOn ℝ ∞ (potential k Φ a) U :=
  ((carrier_contDiff k).comp_contDiffOn hΦ).smul (coefficient_contDiffOn hU hΦ ha hn)

/-- Exact real realization: the derivative of the carrier yields the tangent
cosine wave; every coefficient derivative remains in the displayed curl. -/
theorem wave_eq {U : Set SpaceTime} {Φ : PressureField} {a : VelocityField}
    {k : ℝ} (hk : k ≠ 0) (hU : IsOpen U) (hΦ : ContDiffOn ℝ ∞ Φ U)
    (ha : ContDiffOn ℝ ∞ a U) (hn : ∀ z ∈ U, phaseNormal Φ z ≠ 0)
    (htangent : ∀ z ∈ U, ⟪phaseNormal Φ z, a z⟫_ℝ = 0) {z : SpaceTime} (hz : z ∈ U) :
    wave k Φ a z = Real.cos (k * Φ z) • a z -
      (Real.sin (k * Φ z) / k) • SpatialCurl.spatialCurl (coefficient Φ a) z := by
  have hΦslice := ResidualStability.spatialSlice_differentiable hU hΦ hz
  have hB := coefficient_contDiffOn hU hΦ ha hn
  have hBslice := ResidualStability.spatialSlice_differentiable hU hB hz
  have hcarrier : HasFDerivAt (fun y : Space => carrier k (Φ (z.1, y)))
      ((-Real.cos (k * Φ z)) • fderiv ℝ (fun y : Space => Φ (z.1, y)) z.2) z.2 := by
    exact (carrier_hasDerivAt hk (Φ z)).comp_hasFDerivAt z.2 hΦslice.hasFDerivAt
  change SpatialCurl.curl (fun y => carrier k (Φ (z.1, y)) • coefficient Φ a (z.1, y)) z.2 = _
  rw [curl_smul hcarrier.differentiableAt hBslice, hcarrier.fderiv, map_smul,
    cross_smul_left]
  change (-Real.cos (k * Φ z)) • cross (phaseNormal Φ z) (normalCoefficient (phaseNormal Φ z) (a
      z)) +
    carrier k (Φ z) • SpatialCurl.spatialCurl (coefficient Φ a) z = _
  rw [cross_normalCoefficient (hn z hz) (htangent z hz)]
  simp only [neg_smul, smul_neg, neg_neg, carrier, neg_div, sub_eq_add_neg]

theorem wave_contDiffOn {U : Set SpaceTime} {Φ : PressureField} {a : VelocityField}
    (k : ℝ) (hU : IsOpen U) (hΦ : ContDiffOn ℝ ∞ Φ U) (ha : ContDiffOn ℝ ∞ a U)
    (hn : ∀ z ∈ U, phaseNormal Φ z ≠ 0) : ContDiffOn ℝ ∞ (wave k Φ a) U := by
  intro z hz
  exact (SpatialCurl.contDiffAt_spatialCurl
    ((potential_contDiffOn k hU hΦ ha hn).contDiffAt (hU.mem_nhds hz)) (by simp)).contDiffWithinAt

/-- Divergence vanishes for the full realized wave, including its remainder. -/
theorem wave_divergence_free {U : Set SpaceTime} {Φ : PressureField} {a : VelocityField}
    (k : ℝ) (hU : IsOpen U) (hΦ : ContDiffOn ℝ ∞ Φ U) (ha : ContDiffOn ℝ ∞ a U)
    (hn : ∀ z ∈ U, phaseNormal Φ z ≠ 0) {z : SpaceTime} (hz : z ∈ U) :
    spatialDivergence (wave k Φ a) z.1 z.2 = 0 := by
  have hpot : ContDiffAt ℝ ∞ (potential k Φ a) z :=
    (potential_contDiffOn k hU hΦ ha hn).contDiffAt (hU.mem_nhds hz)
  have hslice : ContDiffAt ℝ ∞ (fun y : Space => potential k Φ a (z.1, y)) z.2 :=
    hpot.comp (f := fun y : Space => (z.1, y)) z.2 (contDiffAt_const.prodMk contDiffAt_id)
  exact SpatialCurl.spatialDivergence_spatialCurl (potential k Φ a) z.1 z.2
    (hslice.of_le (WithTop.coe_le_coe.mpr (show (2 : ℕ∞) ≤ ⊤ from le_top)))

theorem coefficient_support_subset (Φ : PressureField) (a : VelocityField) :
    Function.support (coefficient Φ a) ⊆ Function.support a := by
  intro z hz haz
  exact hz (by simp [coefficient, normalCoefficient, haz])

theorem potential_tsupport_subset (k : ℝ) (Φ : PressureField) (a : VelocityField) :
    tsupport (potential k Φ a) ⊆ tsupport a := by
  apply closure_mono
  intro z hz haz
  exact hz (by simp [potential, coefficient, normalCoefficient, haz])

/-- Spatial differentiation cannot create support outside the closed joint
spacetime support, since vanishing on a joint neighborhood implies vanishing
on the spatial slice. -/
theorem spatialCurl_tsupport_subset (A : VelocityField) :
    tsupport (SpatialCurl.spatialCurl A) ⊆ tsupport A := by
  apply closure_minimal _ isClosed_closure
  intro z hz
  by_contra hnot
  have heq : A =ᶠ[𝓝 z] (fun _ => 0) := notMem_tsupport_iff_eventuallyEq.mp hnot
  apply hz
  change SpatialCurl.curlLinear (fderiv ℝ (fun y : Space => A (z.1, y)) z.2) = 0
  rw [ResidualRegularity.space_fderiv_congr heq]
  simp

theorem wave_tsupport_subset (k : ℝ) (Φ : PressureField) (a : VelocityField) :
    tsupport (wave k Φ a) ⊆ tsupport a :=
  (spatialCurl_tsupport_subset _).trans (potential_tsupport_subset k Φ a)

theorem wave_hasCompactSupport (k : ℝ) (Φ : PressureField) {a : VelocityField}
    (ha : HasCompactSupport a) : HasCompactSupport (wave k Φ a) :=
  ha.of_isClosed_subset isClosed_closure (wave_tsupport_subset k Φ a)

theorem phaseNormal_periodic {times : Set ℝ} {Φ : PressureField}
    (hΦ : UnitSpatialPeriodsOn times Φ) : UnitSpatialPeriodsOn times (phaseNormal Φ) := by
  intro t ht x i
  exact congrArg gradientLinear (ResidualRegularity.space_fderiv_periods hΦ t ht x i)

theorem coefficient_periodic {times : Set ℝ} {Φ : PressureField} {a : VelocityField}
    (hn : UnitSpatialPeriodsOn times (phaseNormal Φ)) (ha : UnitSpatialPeriodsOn times a) :
    UnitSpatialPeriodsOn times (coefficient Φ a) := by
  intro t ht x i
  unfold coefficient
  rw [hn t ht x i, ha t ht x i]

/-- It suffices for the sine carrier and the normal/amplitude data to be
periodic; a real-valued phase itself may have nonzero winding. -/
theorem potential_periodic {times : Set ℝ} {Φ : PressureField} {a : VelocityField} (k : ℝ)
    (hcarrier : UnitSpatialPeriodsOn times (fun z => Real.sin (k * Φ z)))
    (hn : UnitSpatialPeriodsOn times (phaseNormal Φ)) (ha : UnitSpatialPeriodsOn times a) :
    UnitSpatialPeriodsOn times (potential k Φ a) := by
  intro t ht x i
  unfold potential carrier
  have hsin := hcarrier t ht x i
  dsimp only at hsin
  rw [hsin, coefficient_periodic hn ha t ht x i]

theorem wave_periodic {times : Set ℝ} {Φ : PressureField} {a : VelocityField} (k : ℝ)
    (hcarrier : UnitSpatialPeriodsOn times (fun z => Real.sin (k * Φ z)))
    (hn : UnitSpatialPeriodsOn times (phaseNormal Φ)) (ha : UnitSpatialPeriodsOn times a) :
    UnitSpatialPeriodsOn times (wave k Φ a) :=
  SpatialCurl.spatialCurl_periodic (potential_periodic k hcarrier hn ha)

theorem wave_periodic_of_phase {times : Set ℝ} {Φ : PressureField} {a : VelocityField} (k : ℝ)
    (hΦ : UnitSpatialPeriodsOn times Φ) (ha : UnitSpatialPeriodsOn times a) :
    UnitSpatialPeriodsOn times (wave k Φ a) := by
  apply wave_periodic k _ (phaseNormal_periodic hΦ) ha
  intro t ht x i
  change Real.sin (k * Φ (t, x + coordinateVector i)) = Real.sin (k * Φ (t, x))
  rw [hΦ t ht x i]

/-- The coefficient remaining after removing the sine oscillation. -/
def strippedRemainder (k : ℝ) (B : VelocityField) : VelocityField :=
  fun z => (1 / k) • SpatialCurl.spatialCurl B z

theorem wave_eq_stripped {U : Set SpaceTime} {Φ : PressureField} {a : VelocityField}
    {k : ℝ} (hk : k ≠ 0) (hU : IsOpen U) (hΦ : ContDiffOn ℝ ∞ Φ U)
    (ha : ContDiffOn ℝ ∞ a U) (hn : ∀ z ∈ U, phaseNormal Φ z ≠ 0)
    (htangent : ∀ z ∈ U, ⟪phaseNormal Φ z, a z⟫_ℝ = 0) {z : SpaceTime} (hz : z ∈ U) :
    wave k Φ a z = Real.cos (k * Φ z) • a z -
      Real.sin (k * Φ z) • strippedRemainder k (coefficient Φ a) z := by
  rw [wave_eq hk hU hΦ ha hn htangent hz]
  simp only [strippedRemainder, smul_smul, div_eq_mul_inv, one_mul]

/-- One additional coefficient derivative and one inverse frequency, with
no derivative of the oscillatory carrier hidden in the bound. -/
theorem strippedRemainder_jet_bound {U : Set SpaceTime} {B : VelocityField}
    (k : ℝ) (hU : IsOpen U) (hB : ContDiffOn ℝ ∞ B U) {z : SpaceTime} (hz : z ∈ U) (m : ℕ) :
    ‖iteratedFDeriv ℝ m (strippedRemainder k B) z‖ ≤
      (‖SpatialCurl.curlLinear.comp (ResidualStability.spaceRestriction Space)‖ / |k|) *
        ‖iteratedFDeriv ℝ (m + 1) B z‖ := by
  have hcurl : ContDiffAt ℝ ∞ (SpatialCurl.spatialCurl B) z :=
    SpatialCurl.contDiffAt_spatialCurl (hB.contDiffAt (hU.mem_nhds hz)) (by simp)
  unfold strippedRemainder
  rw [iteratedFDeriv_const_smul_apply' (hcurl.of_le
    (ENat.natCast_le_of_coe_top_le_withTop le_rfl m)), norm_smul, Real.norm_eq_abs, abs_div,
        abs_one]
  calc
    _ ≤ (1 / |k|) * (‖SpatialCurl.curlLinear.comp (ResidualStability.spaceRestriction Space)‖ *
        ‖iteratedFDeriv ℝ (m + 1) B z‖) :=
      mul_le_mul_of_nonneg_left (ResidualStability.norm_iteratedFDeriv_spatialCurl_le hU hB hz m)
        (by positivity)
    _ = _ := by ring

theorem strippedRemainder_finiteJetBound {U : Set SpaceTime} {B : VelocityField}
    (k : ℝ) (hU : IsOpen U) (hB : ContDiffOn ℝ ∞ B U) {m : ℕ} {C : ℝ}
    (hjet : JetBounds.FiniteJetBound (m + 1) B U C) :
    JetBounds.FiniteJetBound m (strippedRemainder k B) U
      ((‖SpatialCurl.curlLinear.comp (ResidualStability.spaceRestriction Space)‖ / |k|) * C) := by
  intro n hn z hz
  exact (strippedRemainder_jet_bound k hU hB hz n).trans
    (mul_le_mul_of_nonneg_left (hjet (n + 1) (Nat.add_le_add_right hn 1) z hz) (by positivity))

end NavierStokes.OscillatoryCurl

end
end

end

section

/-!
# Uniform slow jets of the actual phase geometry

The index type below carries the band, representative, and rounded frequency.
It is not a differentiation variable.  All derivatives are actual Fréchet
derivatives in the slow variables (and, when present, the slot variable).
-/

@[expose] public section

noncomputable section

namespace NavierStokes.PhaseJetBounds

open Set
open scoped Topology ContDiff InnerProductSpace

/-- A family of open chart domains, with a slow scale at least one. -/
structure Domain (ι E : Type*) [NormedAddCommGroup E] where
  /-- Scale of `Domain`, of type `ι → ℝ`. -/
  scale : ι → ℝ
  /-- Carrier of `Domain`, of type `ι → Set E`. -/
  carrier : ι → Set E
  isOpen : ∀ i, IsOpen (carrier i)
  one_le_scale : ∀ i, 1 ≤ scale i

/-- Every fixed finite collection of actual derivatives has one polynomial
bound, uniform over all bands and charts in the index type. -/
structure PolynomialJets {ι E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (D : Domain ι E) (f : ι → E → F) : Prop where
  smooth : ∀ i, ContDiffOn ℝ ∞ (f i) (D.carrier i)
  bound : ∀ N : ℕ, ∃ C : ℝ, 1 ≤ C ∧ ∃ m : ℕ,
    ∀ i, JetBounds.FiniteJetBound N (f i) (D.carrier i) (C * D.scale i ^ m)

private theorem nat_le_infty (n : ℕ) : (n : WithTop ℕ∞) ≤ ∞ :=
  ENat.natCast_le_of_coe_top_le_withTop le_rfl n

private theorem one_le_mul' {a b : ℝ} (ha : 1 ≤ a) (hb : 1 ≤ b) : 1 ≤ a * b := by
  nlinarith

section Calculus

variable {ι E F G H : Type*}
variable [NormedAddCommGroup E] [NormedSpace ℝ E]
variable [NormedAddCommGroup F] [NormedSpace ℝ F]
variable [NormedAddCommGroup G] [NormedSpace ℝ G]
variable [NormedAddCommGroup H] [NormedSpace ℝ H]
variable {D : Domain ι E}

theorem PolynomialJets.congr {f g : ι → E → F} (hf : PolynomialJets D f)
    (hfg : ∀ i, EqOn (f i) (g i) (D.carrier i)) : PolynomialJets D g := by
  refine ⟨fun i => (hf.smooth i).congr (fun x hx => (hfg i hx).symm), ?_⟩
  intro N
  obtain ⟨C, hC, m, hm⟩ := hf.bound N
  refine ⟨C, hC, m, ?_⟩
  intro i n hn x hx
  have he := iteratedFDerivWithin_congr (𝕜 := ℝ) (hfg i) hx n
  rw [iteratedFDerivWithin_of_isOpen n (D.isOpen i) hx,
    iteratedFDerivWithin_of_isOpen n (D.isOpen i) hx] at he
  rw [← he]
  exact hm i n hn x hx

theorem PolynomialJets.const (c : ι → F) {C : ℝ} {m : ℕ} (hC : 1 ≤ C)
    (hc : ∀ i, ‖c i‖ ≤ C * D.scale i ^ m) :
    PolynomialJets D (fun i _ => c i) := by
  refine ⟨fun _ => contDiffOn_const, fun _ => ⟨C, hC, m, ?_⟩⟩
  intro i n hn x hx
  cases n with
  | zero => simpa only [norm_iteratedFDeriv_zero] using hc i
  | succ n =>
      rw [iteratedFDeriv_succ_const]
      simp only [Pi.zero_apply, norm_zero]
      exact mul_nonneg (le_trans zero_le_one hC)
        (pow_nonneg (le_trans zero_le_one (D.one_le_scale i)) _)

theorem PolynomialJets.const_uniform (c : ι → F) {C : ℝ} (hC : 1 ≤ C)
    (hc : ∀ i, ‖c i‖ ≤ C) : PolynomialJets D (fun i _ => c i) :=
  PolynomialJets.const c hC (m := 0) (by simpa using hc)

theorem PolynomialJets.const_fixed (c : F) : PolynomialJets D (fun _ _ => c) :=
  PolynomialJets.const_uniform _ (le_max_left 1 ‖c‖) (fun _ => le_max_right _ _)

theorem PolynomialJets.clm {f : ι → E → F} (hf : PolynomialJets D f)
    (L : F →L[ℝ] G) : PolynomialJets D (fun i x => L (f i x)) := by
  refine ⟨fun i => L.contDiff.comp_contDiffOn (hf.smooth i), ?_⟩
  intro N
  obtain ⟨C, hC, m, hm⟩ := hf.bound N
  refine ⟨(‖L‖ + 1) * C, ?_, m, ?_⟩
  · nlinarith [norm_nonneg L]
  intro i n hn x hx
  have he := L.iteratedFDeriv_comp_left
    ((hf.smooth i).contDiffAt ((D.isOpen i).mem_nhds hx)) (nat_le_infty n)
  change ‖iteratedFDeriv ℝ n (L ∘ f i) x‖ ≤ _
  rw [he]
  calc
    _ ≤ ‖L‖ * ‖iteratedFDeriv ℝ n (f i) x‖ := L.norm_compContinuousMultilinearMap_le _
    _ ≤ ‖L‖ * (C * D.scale i ^ m) :=
      mul_le_mul_of_nonneg_left (hm i n hn x hx) (norm_nonneg L)
    _ ≤ (‖L‖ + 1) * C * D.scale i ^ m := by
      have := pow_nonneg (le_trans zero_le_one (D.one_le_scale i)) m
      nlinarith

theorem PolynomialJets.add {f g : ι → E → F}
    (hf : PolynomialJets D f) (hg : PolynomialJets D g) :
    PolynomialJets D (fun i x => f i x + g i x) := by
  refine ⟨fun i => (hf.smooth i).add (hg.smooth i), ?_⟩
  intro N
  obtain ⟨A, hA, a, ha⟩ := hf.bound N
  obtain ⟨B, hB, b, hb⟩ := hg.bound N
  refine ⟨A + B, by linarith, a + b, ?_⟩
  intro i
  apply (JetBounds.FiniteJetBound.add (D.isOpen i)
    ((hf.smooth i).of_le (nat_le_infty N)) ((hg.smooth i).of_le (nat_le_infty N))
    (ha i) (hb i)).mono
  have hsa := pow_le_pow_right₀ (D.one_le_scale i) (Nat.le_add_right a b)
  have hsb := pow_le_pow_right₀ (D.one_le_scale i) (Nat.le_add_left b a)
  nlinarith

theorem PolynomialJets.neg {f : ι → E → F} (hf : PolynomialJets D f) :
    PolynomialJets D (fun i x => -f i x) := by
  simpa using hf.clm (-ContinuousLinearMap.id ℝ F)

theorem PolynomialJets.sub {f g : ι → E → F}
    (hf : PolynomialJets D f) (hg : PolynomialJets D g) :
    PolynomialJets D (fun i x => f i x - g i x) := by
  simpa only [sub_eq_add_neg] using hf.add hg.neg

theorem PolynomialJets.pair {f : ι → E → F} {g : ι → E → G}
    (hf : PolynomialJets D f) (hg : PolynomialJets D g) :
    PolynomialJets D (fun i x => (f i x, g i x)) := by
  simpa using (hf.clm (ContinuousLinearMap.inl ℝ F G)).add
    (hg.clm (ContinuousLinearMap.inr ℝ F G))

theorem PolynomialJets.bilinear {f : ι → E → F} {g : ι → E → G}
    (hf : PolynomialJets D f) (hg : PolynomialJets D g)
    (B : F →L[ℝ] G →L[ℝ] H) :
    PolynomialJets D (fun i x => B (f i x) (g i x)) := by
  refine ⟨fun i => B.isBoundedBilinearMap.contDiff.comp_contDiffOn
    ((hf.smooth i).prodMk (hg.smooth i)), ?_⟩
  intro N
  obtain ⟨A, hA, a, ha⟩ := hf.bound N
  obtain ⟨C, hC, c, hc⟩ := hg.bound N
  refine ⟨(‖B‖ + 1) * 2 ^ N * A * C, ?_, a + c, ?_⟩
  · have hpow : (1 : ℝ) ≤ 2 ^ N := one_le_pow₀ (by norm_num)
    have hba : 1 ≤ (‖B‖ + 1) * 2 ^ N := one_le_mul' (by linarith [norm_nonneg B]) hpow
    exact one_le_mul' (one_le_mul' hba hA) hC
  intro i
  apply (JetBounds.FiniteJetBound.bilinear B (D.isOpen i)
    ((hf.smooth i).of_le (nat_le_infty N)) ((hg.smooth i).of_le (nat_le_infty N))
    (ha i) (hc i)).mono
  rw [pow_add]
  have hs := le_trans zero_le_one (D.one_le_scale i)
  have ha0 : 0 ≤ A := le_trans zero_le_one hA
  have hc0 : 0 ≤ C := le_trans zero_le_one hC
  linarith [mul_nonneg (pow_nonneg (show (0 : ℝ) ≤ 2 by norm_num) N)
    (mul_nonneg (mul_nonneg ha0 hc0) (mul_nonneg (pow_nonneg hs a) (pow_nonneg hs c)))]

theorem PolynomialJets.mul {f g : ι → E → ℝ}
    (hf : PolynomialJets D f) (hg : PolynomialJets D g) :
    PolynomialJets D (fun i x => f i x * g i x) := by
  simpa using hf.bilinear hg (ContinuousLinearMap.mul ℝ ℝ)

theorem PolynomialJets.smul {f : ι → E → ℝ} {g : ι → E → F}
    (hf : PolynomialJets D f) (hg : PolynomialJets D g) :
    PolynomialJets D (fun i x => f i x • g i x) := by
  simpa using hf.bilinear hg (ContinuousLinearMap.lsmul ℝ ℝ)

theorem PolynomialJets.fderiv {f : ι → E → F} (hf : PolynomialJets D f) :
    PolynomialJets D (fun i => fderiv ℝ (f i)) := by
  refine ⟨fun i => (hf.smooth i).fderiv_of_isOpen (D.isOpen i) (by simp), ?_⟩
  intro N
  obtain ⟨C, hC, m, hm⟩ := hf.bound (N + 1)
  exact ⟨C, hC, m, fun i => (hm i).fderiv⟩

theorem PolynomialJets.directional {f : ι → E → F} (hf : PolynomialJets D f) (v : E) :
    PolynomialJets D (fun i x => _root_.fderiv ℝ (f i) x v) :=
  hf.fderiv.clm (ContinuousLinearMap.apply ℝ F v)

/-- Affine coordinates have only a zeroth and first derivative. -/
theorem PolynomialJets.affine (L : E →L[ℝ] F) (c : ι → F) {C : ℝ} {m : ℕ}
    (hC : 1 ≤ C) (hv : ∀ i, ∀ x ∈ D.carrier i, ‖L x + c i‖ ≤ C * D.scale i ^ m) :
    PolynomialJets D (fun i x => L x + c i) := by
  refine ⟨fun _ => L.contDiff.contDiffOn.add contDiffOn_const, ?_⟩
  intro N
  refine ⟨C + ‖L‖, by linarith [norm_nonneg L], m, ?_⟩
  intro i n hn x hx
  have hs : 1 ≤ D.scale i ^ m := one_le_pow₀ (D.one_le_scale i)
  have hfd : _root_.fderiv ℝ (fun y => L y + c i) = fun _ => L := by
    funext y
    exact (L.hasFDerivAt.add_const (c i)).fderiv
  cases n with
  | zero =>
      rw [norm_iteratedFDeriv_zero]
      exact (hv i x hx).trans (by nlinarith [norm_nonneg L])
  | succ n =>
      rw [← norm_iteratedFDeriv_fderiv, hfd]
      cases n with
      | zero =>
          rw [norm_iteratedFDeriv_zero]
          nlinarith [norm_nonneg L]
      | succ n =>
          rw [iteratedFDeriv_succ_const]
          simp only [Pi.zero_apply, norm_zero]
          positivity

theorem norm_jet_comp_linear {f : F → G} {U : Set F}
    (hU : IsOpen U) (hf : ContDiffOn ℝ ∞ f U)
    (L : E →L[ℝ] F) {x : E} (hx : L x ∈ U) (n : ℕ) :
    ‖iteratedFDeriv ℝ n (f ∘ L) x‖ ≤ ‖iteratedFDeriv ℝ n f (L x)‖ * ‖L‖ ^ n := by
  have hp := hU.preimage L.continuous
  have he := L.iteratedFDerivWithin_comp_right hf hU.uniqueDiffOn hp.uniqueDiffOn hx
    (i := n) (nat_le_infty n)
  rw [iteratedFDerivWithin_of_isOpen n hp hx,
    iteratedFDerivWithin_of_isOpen n hU hx] at he
  rw [he]
  simpa using (iteratedFDeriv ℝ n f (L x)).norm_compContinuousLinearMap_le (fun _ => L)

/-- Translations introduce no growth in higher-derivative norms. -/
theorem norm_jet_comp_affine {f : F → G} {U : Set F}
    (hU : IsOpen U) (hf : ContDiffOn ℝ ∞ f U)
    (L : E →L[ℝ] F) (c : F) {x : E} (hx : L x + c ∈ U) (n : ℕ) :
    ‖iteratedFDeriv ℝ n (fun y => f (L y + c)) x‖ ≤
      ‖iteratedFDeriv ℝ n f (L x + c)‖ * ‖L‖ ^ n := by
  let g := fun y => f (y + c)
  have hs : IsOpen ((fun y : F => y + c) ⁻¹' U) := hU.preimage (continuous_id.add continuous_const)
  have hg : ContDiffOn ℝ ∞ g ((fun y : F => y + c) ⁻¹' U) :=
    hf.comp (contDiffOn_id.add contDiffOn_const) (fun _ hy => hy)
  have he := norm_jet_comp_linear hs hg L hx n
  simpa only [g, Function.comp_def, iteratedFDeriv_comp_add_right] using he

theorem PolynomialJets.precomp_affine {D' : Domain ι F} {f : ι → F → G}
    (hf : PolynomialJets D' f) (L : E →L[ℝ] F) (c : ι → F)
    (hscale : ∀ i, D'.scale i = D.scale i)
    (hmap : ∀ i, ∀ x ∈ D.carrier i, L x + c i ∈ D'.carrier i) :
    PolynomialJets D (fun i x => f i (L x + c i)) := by
  refine ⟨fun i => (hf.smooth i).comp
    (L.contDiff.contDiffOn.add contDiffOn_const) (hmap i), ?_⟩
  intro N
  obtain ⟨C, hC, m, hm⟩ := hf.bound N
  refine ⟨C * (‖L‖ + 1) ^ N, one_le_mul' hC (one_le_pow₀ (by linarith [norm_nonneg L])), m, ?_⟩
  intro i n hn x hx
  have hp : ‖L‖ ^ n ≤ (‖L‖ + 1) ^ N :=
    (pow_le_pow_left₀ (norm_nonneg L) (by linarith) n).trans
      (pow_le_pow_right₀ (by linarith [norm_nonneg L]) hn)
  calc
    _ ≤ ‖iteratedFDeriv ℝ n (f i) (L x + c i)‖ * ‖L‖ ^ n :=
      norm_jet_comp_affine (D'.isOpen i) (hf.smooth i) L (c i) (hmap i x hx) n
    _ ≤ (C * D'.scale i ^ m) * (‖L‖ + 1) ^ N :=
      mul_le_mul (hm i n hn _ (hmap i x hx)) hp (by positivity)
        (by have := le_trans zero_le_one (D'.one_le_scale i); positivity)
    _ = _ := by rw [hscale]; ring

theorem compact_jet_bound {g : F → G} {U K : Set F}
    (hU : IsOpen U) (hg : ContDiffOn ℝ ∞ g U) (hK : IsCompact K) (hKU : K ⊆ U)
    (N : ℕ) : ∃ C : ℝ, 1 ≤ C ∧ JetBounds.FiniteJetBound N g K C := by
  have hsingle (k : ℕ) : ∃ C : ℝ, ∀ y ∈ K, ‖iteratedFDeriv ℝ k g y‖ ≤ C := by
    have hc := (hg.continuousOn_iteratedFDerivWithin
      (m := k) (nat_le_infty k) hU.uniqueDiffOn).mono hKU
    have he : ContinuousOn (iteratedFDeriv ℝ k g) K := by
      apply hc.congr
      intro y hy
      exact (iteratedFDerivWithin_of_isOpen k hU (hKU hy)).symm
    exact hK.exists_bound_of_continuousOn he
  induction N with
  | zero =>
      obtain ⟨C, hC⟩ := hsingle 0
      refine ⟨max 1 C, le_max_left _ _, ?_⟩
      intro k hk y hy
      have : k = 0 := by omega
      subst k
      exact (hC y hy).trans (le_max_right _ _)
  | succ N ih =>
      obtain ⟨C, hC, hc⟩ := ih
      obtain ⟨B, hB⟩ := hsingle (N + 1)
      refine ⟨max C B, hC.trans (le_max_left _ _), ?_⟩
      intro k hk y hy
      by_cases hkN : k ≤ N
      · exact (hc k hkN y hy).trans (le_max_left _ _)
      · have : k = N + 1 := by omega
        subst k
        exact (hB y hy).trans (le_max_right _ _)

/-- The higher chain rule is quantitative: compactness is applied only to the
fixed outer function, never to the varying band or to its derivatives. -/
theorem PolynomialJets.compact_comp {f : ι → E → F} (hf : PolynomialJets D f)
    {g : F → G} {U K : Set F} (hU : IsOpen U) (hg : ContDiffOn ℝ ∞ g U)
    (hK : IsCompact K) (hKU : K ⊆ U)
    (hmap : ∀ i, MapsTo (f i) (D.carrier i) K) :
    PolynomialJets D (fun i x => g (f i x)) := by
  have hmapU (i) : MapsTo (f i) (D.carrier i) U := fun x hx => hKU (hmap i hx)
  refine ⟨fun i => hg.comp (hf.smooth i) (hmapU i), ?_⟩
  intro N
  obtain ⟨A, hA, m, ha⟩ := hf.bound N
  obtain ⟨C, hC, hc⟩ := compact_jet_bound hU hg hK hKU N
  refine ⟨(N.factorial : ℝ) * C * A ^ N, ?_, m * N, ?_⟩
  · have hfac : (1 : ℝ) ≤ N.factorial := by exact_mod_cast Nat.factorial_pos N
    exact one_le_mul' (one_le_mul' hfac hC) (one_le_pow₀ hA)
  intro i n hn x hx
  have hs : 1 ≤ D.scale i ^ m := one_le_pow₀ (D.one_le_scale i)
  have hD : 1 ≤ A * D.scale i ^ m := one_le_mul' hA hs
  have h := norm_iteratedFDerivWithin_comp_le hg (hf.smooth i) (nat_le_infty n)
    hU.uniqueDiffOn (D.isOpen i).uniqueDiffOn (hmapU i) hx
    (C := C) (D := A * D.scale i ^ m) (fun k hk => ?_) (fun k hk hkn => ?_)
  · rw [iteratedFDerivWithin_of_isOpen n (D.isOpen i) hx] at h
    change ‖iteratedFDeriv ℝ n (g ∘ f i) x‖ ≤ _
    calc
      _ ≤ (n.factorial : ℝ) * C * (A * D.scale i ^ m) ^ n := h
      _ ≤ (N.factorial : ℝ) * C * (A * D.scale i ^ m) ^ N := by
        apply mul_le_mul
        · exact mul_le_mul_of_nonneg_right
            (by exact_mod_cast Nat.factorial_le hn) (le_trans zero_le_one hC)
        · exact pow_le_pow_right₀ hD hn
        · positivity
        · positivity
      _ = _ := by rw [mul_pow, ← pow_mul]; ring
  · rw [iteratedFDerivWithin_of_isOpen k hU (hmapU i hx)]
    exact hc k (hk.trans hn) (f i x) (hmap i hx)
  · rw [iteratedFDerivWithin_of_isOpen k (D.isOpen i) hx]
    exact (ha i k (hkn.trans hn) x hx).trans
      (by simpa using pow_le_pow_right₀ hD hk)

end Calculus

section Algebra

variable {ι E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable [NormedAddCommGroup F] [InnerProductSpace ℝ F]
variable {D : Domain ι E}

theorem PolynomialJets.inner {f g : ι → E → F}
    (hf : PolynomialJets D f) (hg : PolynomialJets D g) :
    PolynomialJets D (fun i x => ⟪f i x, g i x⟫_ℝ) := by
  exact hf.bilinear hg (innerSL ℝ)

theorem PolynomialJets.norm_sq {f : ι → E → F} (hf : PolynomialJets D f) :
    PolynomialJets D (fun i x => ‖f i x‖ ^ 2) := by
  simpa only [real_inner_self_eq_norm_sq] using hf.inner hf

theorem PolynomialJets.pow {f : ι → E → ℝ} (hf : PolynomialJets D f) (n : ℕ) :
    PolynomialJets D (fun i x => f i x ^ n) := by
  induction n with
  | zero => simpa using (PolynomialJets.const_fixed (D := D) (1 : ℝ))
  | succ n ih => simpa only [pow_succ] using ih.mul hf

theorem PolynomialJets.div_const {f : ι → E → ℝ} (hf : PolynomialJets D f) (c : ℝ) :
    PolynomialJets D (fun i x => f i x / c) := by
  simpa only [div_eq_mul_inv] using hf.mul (PolynomialJets.const_fixed c⁻¹)

/-- Inversion is used only on a uniformly separated compact range. -/
theorem PolynomialJets.inv {f : ι → E → ℝ} (hf : PolynomialJets D f)
    {b M : ℝ} (hb : 0 < b)
    (hlower : ∀ i, ∀ x ∈ D.carrier i, b ≤ |f i x|)
    (hupper : ∀ i, ∀ x ∈ D.carrier i, |f i x| ≤ M) :
    PolynomialJets D (fun i x => (f i x)⁻¹) := by
  let K : Set ℝ := Metric.closedBall 0 M ∩ {r | b ≤ |r|}
  have hK : IsCompact K := (isCompact_closedBall 0 M).inter_right
    (isClosed_le continuous_const continuous_abs)
  have hKU : K ⊆ {r : ℝ | r ≠ 0} := by
    intro r hr he
    have h : b ≤ |r| := hr.2
    simp only [he, abs_zero] at h
    linarith
  apply hf.compact_comp (isClosed_singleton.isOpen_compl)
    (contDiffOn_id.inv (fun _ h => h)) hK hKU
  intro i x hx
  exact ⟨by
      simpa only [Metric.mem_closedBall, dist_zero_right, Real.norm_eq_abs] using hupper i x hx,
    hlower i x hx⟩

end Algebra

/-- Plane: an abbreviation for `MovingFrameODE.Plane`. -/
abbrev Plane := MovingFrameODE.Plane
/-- Space: an abbreviation for `MovingFrameODE.Space`. -/
abbrev Space := MovingFrameODE.Space
/-- Slow: an abbreviation for `PhaseCalculus.Slow`. -/
abbrev Slow := PhaseCalculus.Slow

/-- Regular normals, given by `{n | MovingFrameODE.tail n ≠ 0}`. -/
def regularNormals : Set Space := {n | MovingFrameODE.tail n ≠ 0}

/-- Normal range, given by `Metric.closedBall 0 M ∩ {n | b ≤ ‖MovingFrameODE.tail n‖}`. -/
def normalRange (b M : ℝ) : Set Space :=
  Metric.closedBall 0 M ∩ {n | b ≤ ‖MovingFrameODE.tail n‖}

theorem regularNormals_isOpen : IsOpen regularNormals :=
  isClosed_singleton.isOpen_compl.preimage MovingFrameODE.tailCLM.continuous

theorem normalRange_isCompact (b M : ℝ) : IsCompact (normalRange b M) :=
  (isCompact_closedBall 0 M).inter_right
    (isClosed_le continuous_const MovingFrameODE.tailCLM.continuous.norm)

theorem normalRange_regular {b M : ℝ} (hb : 0 < b) : normalRange b M ⊆ regularNormals := by
  intro n hn he
  have h : b ≤ ‖MovingFrameODE.tail n‖ := hn.2
  simp only [he, norm_zero] at h
  linarith

section Geometry

variable {ι E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {D : Domain ι E} {n nDot : ι → E → Space}

/-- All normalized geometric quantities needed in the moving-frame ODE.
Their jets are conclusions of `normalGeometry_jets`, not assumptions there. -/
structure NormalGeometryJets (D : Domain ι E) (n nDot : ι → E → Space) : Prop where
  scale : PolynomialJets D (fun i x => MovingFrameODE.normalScale (n i x))
  invScale : PolynomialJets D (fun i x => (MovingFrameODE.normalScale (n i x))⁻¹)
  rho : PolynomialJets D (fun i x => MovingFrameODE.radialSlope (n i x))
  invDenom : PolynomialJets D (fun i x => (1 + MovingFrameODE.radialSlope (n i x) ^ 2)⁻¹)
  K : PolynomialJets D (fun i x => MovingFrameODE.normalDirection (n i x))
  N : PolynomialJets D (fun i x => MovingFrameODE.quarterTurn (MovingFrameODE.normalDirection (n i
      x)))
  betaDot : PolynomialJets D (fun i x => PhaseEstimates.scaleDerivative (n i x) (nDot i x))
  rhoDot : PolynomialJets D (fun i x => PhaseEstimates.slopeDerivative (n i x) (nDot i x))
  directionDot : PolynomialJets D (fun i x => PhaseEstimates.directionDerivative (n i x) (nDot i x))
  rotation : PolynomialJets D (fun i x => PhaseEstimates.angularVelocity (n i x) (nDot i x))

theorem normalGeometry_jets (hn : PolynomialJets D n) (hd : PolynomialJets D nDot)
    {b M : ℝ} (hb : 0 < b)
    (hlower : ∀ i, ∀ x ∈ D.carrier i, b ≤ ‖MovingFrameODE.tail (n i x)‖)
    (hupper : ∀ i, ∀ x ∈ D.carrier i, ‖n i x‖ ≤ M) :
    NormalGeometryJets D n nDot := by
  have hmap : ∀ i, MapsTo (n i) (D.carrier i) (normalRange b M) := by
    intro i x hx
    exact ⟨by simpa only [Metric.mem_closedBall, dist_zero_right] using hupper i x hx,
      hlower i x hx⟩
  have hs : ContDiffOn ℝ ∞ MovingFrameODE.normalScale regularNormals := by
    intro z hz
    exact (MovingFrameODE.contDiffAt_normalScale contDiffAt_id hz).contDiffWithinAt
  have hr : ContDiffOn ℝ ∞ MovingFrameODE.radialSlope regularNormals := by
    intro z hz
    exact (MovingFrameODE.contDiffAt_radialSlope contDiffAt_id hz).contDiffWithinAt
  have hk : ContDiffOn ℝ ∞ MovingFrameODE.normalDirection regularNormals := by
    intro z hz
    exact (MovingFrameODE.contDiffAt_normalDirection contDiffAt_id hz).contDiffWithinAt
  have hsinv : ContDiffOn ℝ ∞ (fun z => (MovingFrameODE.normalScale z)⁻¹) regularNormals :=
    hs.inv (fun z hz => (MovingFrameODE.normalScale_pos hz).ne')
  have hdinv : ContDiffOn ℝ ∞ (fun z => (1 + MovingFrameODE.radialSlope z ^ 2)⁻¹)
      regularNormals := (contDiffOn_const.add (hr.pow 2)).inv (fun z _ => by positivity)
  have pscale := hn.compact_comp regularNormals_isOpen hs (normalRange_isCompact b M)
    (normalRange_regular hb) hmap
  have pinv := hn.compact_comp regularNormals_isOpen hsinv (normalRange_isCompact b M)
    (normalRange_regular hb) hmap
  have prho := hn.compact_comp regularNormals_isOpen hr (normalRange_isCompact b M)
    (normalRange_regular hb) hmap
  have pdenom := hn.compact_comp regularNormals_isOpen hdinv (normalRange_isCompact b M)
    (normalRange_regular hb) hmap
  have pk := hn.compact_comp regularNormals_isOpen hk (normalRange_isCompact b M)
    (normalRange_regular hb) hmap
  have pn := pk.clm MovingFrameODE.quarterTurn
  have pt : PolynomialJets D (fun i x => MovingFrameODE.tail (n i x)) := hn.clm
      MovingFrameODE.tailCLM
  have ptd : PolynomialJets D (fun i x => MovingFrameODE.tail (nDot i x)) := hd.clm
      MovingFrameODE.tailCLM
  have prd := hd.clm (PiLp.proj 2 (fun _ : Fin 3 => ℝ) 0)
  have psd : PolynomialJets D (fun i x => PhaseEstimates.scaleDerivative (n i x) (nDot i x)) := by
    simpa only [PhaseEstimates.scaleDerivative, div_eq_mul_inv]
      using (pt.inner ptd).mul pinv
  have prhod : PolynomialJets D (fun i x => PhaseEstimates.slopeDerivative (n i x) (nDot i x)) := by
    simpa only [PhaseEstimates.slopeDerivative, PiLp.proj_apply, div_eq_mul_inv]
      using (prd.sub (prho.mul psd)).mul pinv
  have pkd : PolynomialJets D (fun i x => PhaseEstimates.directionDerivative (n i x) (nDot i x)) :=
      by
    simpa only [PhaseEstimates.directionDerivative]
      using pinv.smul (ptd.sub (psd.smul pk))
  exact ⟨pscale, pinv, prho, pdenom, pk, pn, psd, prhod, pkd, pn.inner pkd⟩

end Geometry

section Phase

variable {ι : Type*}

/-- Uniform normalized base-field jets are a sufficient input.  The bound is
on the base field itself, before any normal or frame is constructed. -/
theorem polynomialJets_of_uniform {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
    {D : Domain ι E} {f : ι → E → F}
    (hf : ∀ i, ContDiffOn ℝ ∞ (f i) (D.carrier i))
    (hbound : ∀ N : ℕ, ∃ C : ℝ, 1 ≤ C ∧
      ∀ i, JetBounds.FiniteJetBound N (f i) (D.carrier i) C) : PolynomialJets D f := by
  refine ⟨hf, ?_⟩
  intro N
  obtain ⟨C, hC, hc⟩ := hbound N
  exact ⟨C, hC, 0, by simpa only [pow_zero, mul_one] using hc⟩

/-- Slot, bundling `scale`, `carrier`, `isOpen`, `one_le_scale`. -/
noncomputable def Domain.slot (D : Domain ι Slow) (V : ι → Set ℝ) (hV : ∀ i, IsOpen (V i)) :
    Domain ι (Slow × ℝ) where
  scale := D.scale
  carrier i := D.carrier i ×ˢ V i
  isOpen i := (D.isOpen i).prod (hV i)
  one_le_scale := D.one_le_scale

theorem PolynomialJets.lift_slot {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {D : Domain ι Slow} {f : ι → Slow → F} (hf : PolynomialJets D f)
    (V : ι → Set ℝ) (hV : ∀ i, IsOpen (V i)) :
    PolynomialJets (D.slot V hV) (fun i z => f i z.1) := by
  simpa only [ContinuousLinearMap.coe_fst', add_zero] using
    hf.precomp_affine (D := D.slot V hV) (ContinuousLinearMap.fst ℝ Slow ℝ)
      (fun _ => 0) (fun _ => rfl) (fun _ _ hz => by simpa using hz.1)

theorem PolynomialJets.vec2 {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {D : Domain ι E} {f g : ι → E → ℝ}
    (hf : PolynomialJets D f) (hg : PolynomialJets D g) :
    PolynomialJets D (fun i x => (!₂[f i x, g i x] : Plane)) :=
  (hf.pair hg).clm MovingFrameODE.pairCLM

theorem PolynomialJets.vec3 {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {D : Domain ι E} {f g h : ι → E → ℝ}
    (hf : PolynomialJets D f) (hg : PolynomialJets D g) (hh : PolynomialJets D h) :
    PolynomialJets D (fun i x => (!₂[f i x, g i x, h i x] : Space)) :=
  (hf.pair (hg.vec2 hh)).clm MovingFrameODE.packCLM

/-- The explicit normal has polynomial jets.  No inverse power of epsilon
occurs in this formula, although it occurs in the phase itself. -/
theorem explicitNormal_polynomial {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {D : Domain ι E} {ε p pz x0 R v FR GR FZ GZ : ι → E → ℝ}
    (hε : PolynomialJets D ε) (hp : PolynomialJets D p) (hpz : PolynomialJets D pz)
    (hx : PolynomialJets D x0) (hRi : PolynomialJets D (fun i x => (R i x)⁻¹))
    (hv : PolynomialJets D v) (hFR : PolynomialJets D FR) (hGR : PolynomialJets D GR)
    (hFZ : PolynomialJets D FZ) (hGZ : PolynomialJets D GZ) :
    PolynomialJets D (fun i z => PhaseEstimates.explicitNormal (ε i z) (p i z) (pz i z)
      (x0 i z) (R i z) (v i z) (FR i z) (GR i z) (FZ i z) (GZ i z)) := by
  simpa only [PhaseEstimates.explicitNormal, div_eq_mul_inv] using
    (hx.sub (hv.mul ((hp.mul hFR).add (hpz.mul hGR)))).vec3 (hp.mul hRi)
      (hpz.sub ((hε.mul hv).mul ((hp.mul hFZ).add (hpz.mul hGZ))))

theorem normalVelocity_polynomial {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {D : Domain ι E} {ε p pz FR GR FZ GZ : ι → E → ℝ}
    (hε : PolynomialJets D ε) (hp : PolynomialJets D p) (hpz : PolynomialJets D pz)
    (hFR : PolynomialJets D FR) (hGR : PolynomialJets D GR)
    (hFZ : PolynomialJets D FZ) (hGZ : PolynomialJets D GZ) :
    PolynomialJets D (fun i z => PhaseEstimates.normalVelocity (ε i z) (p i z) (pz i z)
      (FR i z) (GR i z) (FZ i z) (GZ i z)) := by
  simpa only [PhaseEstimates.normalVelocity, neg_mul] using
    ((hp.mul hFR).add (hpz.mul hGR)).neg.vec3 (PolynomialJets.const_fixed 0)
      (hε.mul ((hp.mul hFZ).add (hpz.mul hGZ))).neg

/-- Discrete label data.  In particular, `p` is held fixed when a jet is taken;
it may be the nonzero rounded frequency from `PhaseEstimates`. -/
structure PhaseFamily (ι : Type*) where
  /-- Epsilon of `PhaseFamily`, of type `ι → ℝ`. -/
  epsilon : ι → ℝ
  /-- P of `PhaseFamily`, of type `ι → ℝ`. -/
  p : ι → ℝ
  /-- Pz of `PhaseFamily`, of type `ι → ℝ`. -/
  pz : ι → ℝ
  /-- X0 of `PhaseFamily`, of type `ι → ℝ`. -/
  x0 : ι → ℝ
  /-- Theta of `PhaseFamily`, of type `ι → ℝ`. -/
  theta : ι → ℝ
  /-- F of `PhaseFamily`, of type `ι → Slow → ℝ`. -/
  F : ι → Slow → ℝ
  /-- Geometric data of `PhaseFamily`, of type `ι → Slow → ℝ`. -/
  G : ι → Slow → ℝ

/-- Normal, given by `PhaseCalculus.phaseNormal (a.epsilon i) (a.p i) (a.pz i) (a.x0 i) (a.F i)
(a.G i) (z.1, (a.theta i, z.2))`. -/
noncomputable def PhaseFamily.normal (a : PhaseFamily ι) (i : ι) (z : Slow × ℝ) : Space :=
  PhaseCalculus.phaseNormal (a.epsilon i) (a.p i) (a.pz i) (a.x0 i) (a.F i) (a.G i)
    (z.1, (a.theta i, z.2))

/-- Velocity, given by `PhaseCalculus.normalSlotDerivative (a.epsilon i) (a.p i) (a.pz i) (a.F
i) (a.G i) z.1`. -/
noncomputable def PhaseFamily.velocity (a : PhaseFamily ι) (i : ι) (z : Slow × ℝ) : Space :=
  PhaseCalculus.normalSlotDerivative (a.epsilon i) (a.p i) (a.pz i) (a.F i) (a.G i) z.1

/-- Shear, given by `PhaseEstimates.shearVector (a.F i) (a.G i) z.1`. -/
noncomputable def PhaseFamily.shear (a : PhaseFamily ι) (i : ι) (z : Slow × ℝ) : Plane :=
  PhaseEstimates.shearVector (a.F i) (a.G i) z.1

/-- Actual phase-normal and shear jets derived from the base fields.  The
slot can have length of order S; the cylindrical radius stays in an annulus.
No derivatives of the normal, frame, or ODE coefficients are inputs. -/
theorem PhaseFamily.polynomial_jets (a : PhaseFamily ι) (D : Domain ι Slow)
    (V : ι → Set ℝ) (hV : ∀ i, IsOpen (V i))
    (hF : PolynomialJets D a.F) (hG : PolynomialJets D a.G)
    {r M : ℝ} (hr : 0 < r) (hM : 1 ≤ M)
    (hconstant : ∀ i, |a.epsilon i| ≤ M ∧ |a.p i| ≤ M ∧ |a.pz i| ≤ M ∧ |a.x0 i| ≤ M)
    (heps : ∀ i, a.epsilon i ≠ 0)
    (hR : ∀ i, ∀ q ∈ D.carrier i, r ≤ |q.1| ∧ |q.1| ≤ M)
    (hslot : ∀ i, ∀ v ∈ V i, |v| ≤ M * D.scale i) :
    PolynomialJets (D.slot V hV) a.normal ∧
      PolynomialJets (D.slot V hV) a.velocity ∧
      PolynomialJets (D.slot V hV) a.shear := by
  have hpε : PolynomialJets (D.slot V hV) (fun i _ => a.epsilon i) :=
    PolynomialJets.const_uniform _ hM (fun i => by simpa using (hconstant i).1)
  have hpp : PolynomialJets (D.slot V hV) (fun i _ => a.p i) :=
    PolynomialJets.const_uniform _ hM (fun i => by simpa using (hconstant i).2.1)
  have hppz : PolynomialJets (D.slot V hV) (fun i _ => a.pz i) :=
    PolynomialJets.const_uniform _ hM (fun i => by simpa using (hconstant i).2.2.1)
  have hpx : PolynomialJets (D.slot V hV) (fun i _ => a.x0 i) :=
    PolynomialJets.const_uniform _ hM (fun i => by simpa using (hconstant i).2.2.2)
  have hpR : PolynomialJets D (fun _ q => q.1) := by
    simpa only [ContinuousLinearMap.coe_fst', add_zero] using
      (PolynomialJets.affine (D := D) (ContinuousLinearMap.fst ℝ ℝ (ℝ × ℝ))
        (fun _ => 0) (m := 0) hM (fun i q hq => by simpa using (hR i q hq).2))
  have hpRi := (hpR.inv hr (fun i q hq => (hR i q hq).1)
    (fun i q hq => (hR i q hq).2)).lift_slot V hV
  have hpv : PolynomialJets (D.slot V hV) (fun _ z => z.2) := by
    simpa only [ContinuousLinearMap.coe_snd', add_zero] using
      (PolynomialJets.affine (D := D.slot V hV) (ContinuousLinearMap.snd ℝ Slow ℝ)
        (fun _ => 0) (m := 1) hM (fun i z hz => by simpa [Domain.slot] using hslot i z.2 hz.2))
  have hFR := (hF.directional (1, (0, 0))).lift_slot V hV
  have hGR := (hG.directional (1, (0, 0))).lift_slot V hV
  have hFZ := (hF.directional (0, (1, 0))).lift_slot V hV
  have hGZ := (hG.directional (0, (1, 0))).lift_slot V hV
  have hexp := explicitNormal_polynomial hpε hpp hppz hpx hpRi hpv hFR hGR hFZ hGZ
  have hn : PolynomialJets (D.slot V hV) a.normal := by
    apply hexp.congr
    intro i z hz
    exact (PhaseEstimates.phaseNormal_eq_explicit (a.epsilon i) (a.p i) (a.pz i) (a.x0 i)
      (a.F i) (a.G i) (z.1, (a.theta i, z.2)) (heps i)
      (((hF.smooth i).contDiffAt ((D.isOpen i).mem_nhds hz.1)).differentiableAt (by simp))
      (((hG.smooth i).contDiffAt ((D.isOpen i).mem_nhds hz.1)).differentiableAt (by simp))).symm
  have hd : PolynomialJets (D.slot V hV) a.velocity :=
    normalVelocity_polynomial hpε hpp hppz hFR hGR hFZ hGZ
  have hg : PolynomialJets (D.slot V hV) a.shear :=
    ((hpR.lift_slot V hV).mul hFR).vec2 hGR
  exact ⟨hn, hd, hg⟩

end Phase

section Coefficients

variable {ι : Type*} {Q : Type} [NormedAddCommGroup Q] [NormedSpace ℝ Q]
variable {D : Domain ι (Q × ℝ)}

/-- Intermediate algebraic data used to assemble the *defined* modal
coefficient.  `frameJets_ofNormalLocal` proves these from phase-normal jets. -/
structure FrameJets (D : Domain ι (Q × ℝ)) (d : ι → PrimaryODE.FrameData Q) : Prop where
  beta : PolynomialJets D (fun i => (d i).beta)
  betaDot : PolynomialJets D (fun i => (d i).betaDot)
  rho : PolynomialJets D (fun i => (d i).rho)
  rhoDot : PolynomialJets D (fun i => (d i).rhoDot)
  rotation : PolynomialJets D (fun i => (d i).rotation)
  F : PolynomialJets D (fun i => (d i).F)
  shear : PolynomialJets D (fun i => (d i).shear)
  K : PolynomialJets D (fun i z => (d i).frame z 0)
  N : PolynomialJets D (fun i z => (d i).frame z 1)
  invDenom : PolynomialJets D (fun i z => (1 + (d i).rho z ^ 2)⁻¹)
  eigenvalue : PolynomialJets D (fun i => (d i).eigenvalue)
  eigenvector : PolynomialJets D (fun i => (d i).eigenvector)
  invEigenvector : PolynomialJets D (fun i z => ((d i).eigenvector z)⁻¹)
  eigenRate : PolynomialJets D (fun i => (d i).eigenRate)
  viscosity : PolynomialJets D (fun i => (d i).viscosity)
  eigenvector_ne_zero : ∀ i, ∀ z ∈ D.carrier i, (d i).eigenvector z ≠ 0

theorem FrameJets.smoothOn {d : ι → PrimaryODE.FrameData Q} (h : FrameJets D d) (i : ι) :
    (d i).SmoothOn (D.carrier i) := by
  refine ⟨h.beta.smooth i, h.betaDot.smooth i, h.rho.smooth i, h.rhoDot.smooth i,
    h.rotation.smooth i, h.F.smooth i, h.shear.smooth i, ?_, h.eigenvalue.smooth i,
    h.eigenvector.smooth i, h.eigenRate.smooth i, h.viscosity.smooth i, h.eigenvector_ne_zero i⟩
  intro k
  fin_cases k
  · exact h.K.smooth i
  · exact h.N.smooth i

theorem FrameJets.errorA {d : ι → PrimaryODE.FrameData Q} (h : FrameJets D d) :
    PolynomialJets D (fun i => (d i).errorA) := by
  unfold PrimaryODE.FrameData.errorA
  simpa only [PrimaryODE.FrameData.errorA, MovingFrameODE.coeff11, div_eq_mul_inv] using
    (h.rho.mul ((h.K.inner h.shear).sub h.rhoDot)).mul h.invDenom

theorem FrameJets.errorB {d : ι → PrimaryODE.FrameData Q} (h : FrameJets D d) :
    PolynomialJets D (fun i => (d i).errorB) := by
  have hNt := h.N.clm (PiLp.proj 2 (fun _ : Fin 2 => ℝ) 0)
  unfold PrimaryODE.FrameData.errorB
  simpa only [PrimaryODE.FrameData.errorB, MovingFrameODE.coeff12,
    PiLp.proj_apply, div_eq_mul_inv] using
    ((((PolynomialJets.const_fixed (D := D) (2 : ℝ)).mul h.F).mul hNt).sub
      (h.rho.mul h.rotation)).mul h.invDenom |>.sub (h.eigenvalue.mul h.invEigenvector)

theorem FrameJets.errorC {d : ι → PrimaryODE.FrameData Q} (h : FrameJets D d) :
    PolynomialJets D (fun i => (d i).errorC) := by
  have hNt := h.N.clm (PiLp.proj 2 (fun _ : Fin 2 => ℝ) 0)
  unfold PrimaryODE.FrameData.errorC
  simpa only [PrimaryODE.FrameData.errorC, MovingFrameODE.coeff21, PiLp.proj_apply] using
    (((((PolynomialJets.const_fixed (D := D) (2 : ℝ)).mul h.F).mul hNt).add
      (h.N.inner h.shear)).neg.add (h.rho.mul h.rotation)).sub
        (h.eigenvalue.mul h.eigenvector)

theorem FrameJets.modal_errors {d : ι → PrimaryODE.FrameData Q} (h : FrameJets D d) :
    PolynomialJets D (fun i => (d i).error11) ∧
    PolynomialJets D (fun i => (d i).error12) ∧
    PolynomialJets D (fun i => (d i).error21) ∧
    PolynomialJets D (fun i => (d i).error22) := by
  have hb := h.eigenvector.mul h.errorB
  have hc := h.errorC.mul h.invEigenvector
  refine ⟨?_, ?_, ?_, ?_⟩
  · unfold PrimaryODE.FrameData.error11
    simpa only [PrimaryODE.FrameData.error11, MovingFrameODE.modal11, div_eq_mul_inv] using
      (((h.errorA.add hb).add hc).sub h.eigenRate).div_const 2
  · unfold PrimaryODE.FrameData.error12
    simpa only [PrimaryODE.FrameData.error12, MovingFrameODE.modal12, div_eq_mul_inv] using
      (((h.errorA.sub hb).add hc).add h.eigenRate).div_const 2
  · unfold PrimaryODE.FrameData.error21
    simpa only [PrimaryODE.FrameData.error21, MovingFrameODE.modal21, div_eq_mul_inv] using
      (((h.errorA.add hb).sub hc).add h.eigenRate).div_const 2
  · unfold PrimaryODE.FrameData.error22
    simpa only [PrimaryODE.FrameData.error22, MovingFrameODE.modal22, div_eq_mul_inv] using
      (((h.errorA.sub hb).sub hc).sub h.eigenRate).div_const 2

theorem FrameJets.coefficient {d : ι → PrimaryODE.FrameData Q} (h : FrameJets D d) (j : ℤ) :
    PolynomialJets D (fun i => (d i).coefficient j) := by
  obtain ⟨h11, h12, h21, h22⟩ := h.modal_errors
  have hd := (PolynomialJets.const_fixed (D := D) ((j : ℝ) ^ 2)).mul h.viscosity
  have hh := (((((h.eigenvalue.sub hd).add h11).smul
    (PolynomialJets.const_fixed (GrowingMode.modalOperator 0 0 1 0 0 0))).add
      (h12.smul (PolynomialJets.const_fixed (GrowingMode.modalOperator 0 0 0 1 0 0)))).add
        (h21.smul (PolynomialJets.const_fixed (GrowingMode.modalOperator 0 0 0 0 1 0)))).add
          (((h.eigenvalue.neg.sub hd).add h22).smul
            (PolynomialJets.const_fixed (GrowingMode.modalOperator 0 0 0 0 0 1)))
  apply hh.congr
  intro i z _
  ext w k
  fin_cases k <;> simp [PrimaryODE.FrameData.coefficient, PrimaryODE.FrameData.damping,
    GrowingMode.modalOperator]

/-- The actual projection and eigenbasis conversion of a supplied source
preserve polynomial jets.  A scalar weight on the source can be carried
separately using linearity; no Gaussian source estimate is assumed here. -/
theorem FrameJets.forcing {d : ι → PrimaryODE.FrameData Q} (h : FrameJets D d)
    {f : ι → Q × ℝ → Space} (hf : PolynomialJets D f) :
    PolynomialJets D (fun i => (d i).forcing (f i)) := by
  have ht : PolynomialJets D (fun i x => MovingFrameODE.tail (f i x)) := hf.clm
      MovingFrameODE.tailCLM
  have hr := hf.clm (PiLp.proj 2 (fun _ : Fin 3 => ℝ) 0)
  have hx : PolynomialJets D (fun i => (d i).forceX (f i)) := by
    unfold PrimaryODE.FrameData.forceX
    simpa only [PrimaryODE.FrameData.forceX, PiLp.proj_apply, div_eq_mul_inv] using
      ((hr.sub (h.rho.mul (h.K.inner ht))).neg.mul h.invDenom)
  have hy : PolynomialJets D (fun i => (d i).forceY (f i)) := (h.N.inner ht).neg
  have hdiv := hy.mul h.invEigenvector
  unfold PrimaryODE.FrameData.forcing
  simpa only [PrimaryODE.FrameData.forcing, div_eq_mul_inv] using
    ((hx.add hdiv).div_const 2).vec2 ((hx.sub hdiv).div_const 2)

/-- This theorem connects the proved normal estimates to the exact local
frame used by `PrimaryODE`, including normal motion and viscosity. -/
theorem frameJets_ofNormalLocal
    {n nDot : ι → Q × ℝ → Space} {F : ι → Q × ℝ → ℝ} {g : ι → Q × ℝ → Plane}
    {lam h rate ν : ι → Q × ℝ → ℝ}
    (hn : PolynomialJets D n) (hd : PolynomialJets D nDot)
    (hF : PolynomialJets D F) (hg : PolynomialJets D g)
    (hlam : PolynomialJets D lam) (hh : PolynomialJets D h)
    (hrate : PolynomialJets D rate) (hν : PolynomialJets D ν)
    {b M bh H : ℝ} (hb : 0 < b) (hbh : 0 < bh)
    (hnlow : ∀ i, ∀ z ∈ D.carrier i, b ≤ ‖MovingFrameODE.tail (n i z)‖)
    (hnup : ∀ i, ∀ z ∈ D.carrier i, ‖n i z‖ ≤ M)
    (hhlow : ∀ i, ∀ z ∈ D.carrier i, bh ≤ |h i z|)
    (hhup : ∀ i, ∀ z ∈ D.carrier i, |h i z| ≤ H) :
    FrameJets D (fun i => PrimaryODE.FrameData.ofNormalLocal
      (n i) (nDot i) (F i) (g i) (lam i) (h i) (rate i) (ν i)) := by
  have hgeom := normalGeometry_jets hn hd hb hnlow hnup
  have hne (i) (z) (hz : z ∈ D.carrier i) : MovingFrameODE.tail (n i z) ≠ 0 :=
    norm_pos_iff.mp (lt_of_lt_of_le hb (hnlow i z hz))
  refine ⟨hgeom.scale, hgeom.betaDot, hgeom.rho, hgeom.rhoDot, hgeom.rotation, hF, hg,
    ?_, ?_, hgeom.invDenom, hlam, hh, hh.inv hbh hhlow hhup, hrate, hν.mul hn.norm_sq, ?_⟩
  · apply hgeom.K.congr
    intro i z hz
    simp only [PrimaryODE.FrameData.ofNormalLocal, PrimaryODE.localFrame_eq (hne i z hz),
      MovingFrameODE.normalFrame_zero]
  · apply hgeom.N.congr
    intro i z hz
    simp only [PrimaryODE.FrameData.ofNormalLocal, PrimaryODE.localFrame_eq (hne i z hz),
      MovingFrameODE.normalFrame_one]
  · intro i z hz he
    have hbnd := hhlow i z hz
    change h i z = 0 at he
    rw [he, abs_zero] at hbnd
    linarith

/-- The form consumed by `PrimaryODE.norm_iteratedFDeriv_solution_le_polynomial`
and `WeightedODEJets`: all parameter jets at fixed slot time share one
constant and one power of S.  The constant is independent of the slot time. -/
theorem PolynomialJets.parameter_bound {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {f : ι → Q × ℝ → F} (hf : PolynomialJets D f) (N : ℕ) :
    ∃ C : ℝ, 1 ≤ C ∧ ∃ m : ℕ, ∀ i p v, (p, v) ∈ D.carrier i →
      ∀ k ≤ N, ‖iteratedFDeriv ℝ k (fun q => f i (q, v)) p‖ ≤ C * D.scale i ^ m := by
  obtain ⟨C, hC, m, hm⟩ := hf.bound N
  let L := ContinuousLinearMap.inl ℝ Q ℝ
  refine ⟨C * (‖L‖ + 1) ^ N,
    one_le_mul' hC (one_le_pow₀ (by linarith [norm_nonneg L])), m, ?_⟩
  intro i p v hp k hk
  have hmap : L p + (0, v) ∈ D.carrier i := by simpa [L] using hp
  have hjet := norm_jet_comp_affine (D.isOpen i) (hf.smooth i) L (0, v) hmap k
  have hfac : ‖L‖ ^ k ≤ (‖L‖ + 1) ^ N :=
    (pow_le_pow_left₀ (norm_nonneg L) (by linarith) k).trans
      (pow_le_pow_right₀ (by linarith [norm_nonneg L]) hk)
  calc
    _ ≤ ‖iteratedFDeriv ℝ k (f i) (p, v)‖ * ‖L‖ ^ k := by simpa [L] using hjet
    _ ≤ (C * D.scale i ^ m) * (‖L‖ + 1) ^ N :=
      mul_le_mul (hm i k hk (p, v) hp) hfac (by positivity)
        (by have := le_trans zero_le_one (D.one_le_scale i); positivity)
    _ = _ := by ring

end Coefficients

section ReferenceBounds

variable {ι E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {D : Domain ι E}

omit [NormedSpace ℝ E] in
/-- Quantitative compact-range inputs obtained from the actual normal
comparison proved in `PhaseEstimates`, with no lower bound assumed on n. -/
theorem normal_range_of_reference_close {n : ι → E → Space}
    (B : ι → ℝ) (K : ι → Plane) (s δ : ι → E → ℝ)
    {b M : ℝ} (hb : 0 < b) (hM : 1 ≤ M)
    (hB : ∀ i, 2 * b ≤ B i ∧ B i ≤ M) (hK : ∀ i, ‖K i‖ = 1)
    (hs : ∀ i, ∀ z ∈ D.carrier i, |s i z| ≤ M)
    (hδ : ∀ i, ∀ z ∈ D.carrier i, δ i z ≤ B i / 2)
    (hclose : ∀ i, ∀ z ∈ D.carrier i,
      ‖n i z - MovingFrameODE.pack (B i * s i z) (B i • K i)‖ ≤ δ i z) :
    (∀ i, ∀ z ∈ D.carrier i, b ≤ ‖MovingFrameODE.tail (n i z)‖) ∧
      (∀ i, ∀ z ∈ D.carrier i, ‖n i z‖ ≤ M ^ 2 + 3 * M) := by
  have hBpos (i) : 0 < B i := lt_of_lt_of_le (by linarith) (hB i).1
  constructor
  · intro i z hz
    have h := (PhaseEstimates.normal_lower_bounds (hBpos i) (hK i) (hδ i z hz) (hclose i z hz)).1
    change b ≤ MovingFrameODE.normalScale (n i z)
    linarith [(hB i).1]
  · intro i z hz
    have hc (k : Fin 2) : |K i k| ≤ 1 := by
      simpa only [Real.norm_eq_abs, hK i] using PiLp.norm_apply_le (K i) k
    have href : ‖MovingFrameODE.pack (B i * s i z) (B i • K i)‖ ≤ M ^ 2 + 2 * M := by
      have hh := PhaseEstimates.vec3_norm_le_sum (MovingFrameODE.pack (B i * s i z) (B i • K i))
      change ‖MovingFrameODE.pack (B i * s i z) (B i • K i)‖ ≤
        |B i * s i z| + |B i * K i 0| + |B i * K i 1| at hh
      simp only [abs_mul, abs_of_pos (hBpos i)] at hh
      have h1 := mul_le_mul (hB i).2 (hs i z hz) (abs_nonneg _) (by linarith : 0 ≤ M)
      have h2 := mul_le_mul (hB i).2 (hc 0) (abs_nonneg _) (by linarith : 0 ≤ M)
      have h3 := mul_le_mul (hB i).2 (hc 1) (abs_nonneg _) (by linarith : 0 ≤ M)
      linarith
    have hh := norm_sub_le_norm_sub_add_norm_sub (n i z)
      (MovingFrameODE.pack (B i * s i z) (B i • K i)) 0
    simp only [sub_zero] at hh
    linarith [hclose i z hz, hδ i z hz, (hB i).2]

theorem PolynomialJets.radius {s : ι → E → ℝ} (hs : PolynomialJets D s)
    {M : ℝ} (hbound : ∀ i, ∀ z ∈ D.carrier i, |s i z| ≤ M) :
    PolynomialJets D (fun i z => Real.sqrt (1 + s i z ^ 2)) ∧
      PolynomialJets D (fun i z => (Real.sqrt (1 + s i z ^ 2))⁻¹) ∧
      PolynomialJets D (fun i z => (1 + s i z ^ 2)⁻¹) := by
  have hg : ContDiffOn ℝ ∞ (fun x : ℝ => Real.sqrt (1 + x ^ 2)) univ :=
    (contDiffOn_const.add (contDiffOn_id.pow 2)).sqrt (fun x _ => by positivity)
  have hgi := hg.inv (fun x _ => (Real.sqrt_pos.mpr (by positivity)).ne')
  have hgd : ContDiffOn ℝ ∞ (fun x : ℝ => (1 + x ^ 2)⁻¹) univ :=
    (contDiffOn_const.add (contDiffOn_id.pow 2)).inv (fun x _ => by positivity)
  have hmap : ∀ i, MapsTo (s i) (D.carrier i) (Metric.closedBall 0 M) := by
    intro i z hz
    simpa only [Metric.mem_closedBall, dist_zero_right, Real.norm_eq_abs] using hbound i z hz
  exact ⟨hs.compact_comp isOpen_univ hg (isCompact_closedBall 0 M) (subset_univ _) hmap,
    hs.compact_comp isOpen_univ hgi (isCompact_closedBall 0 M) (subset_univ _) hmap,
    hs.compact_comp isOpen_univ hgd (isCompact_closedBall 0 M) (subset_univ _) hmap⟩

theorem radius_bounds (s : ℝ) : 1 ≤ Real.sqrt (1 + s ^ 2) ∧
    Real.sqrt (1 + s ^ 2) ≤ 1 + |s| := by
  have hpos := Real.sqrt_nonneg (1 + s ^ 2)
  have hsq := Real.sq_sqrt (show 0 ≤ 1 + s ^ 2 by positivity)
  constructor <;> nlinarith [sq_nonneg s, sq_abs s, abs_nonneg s]

end ReferenceBounds

section ReferenceJets

variable {ι Q : Type*} [NormedAddCommGroup Q] [NormedSpace ℝ Q]
variable {D : Domain ι (Q × ℝ)}

/-- The reference eigenbasis is also derived from its explicit formula.
The hypothesis on u/ell is the scale-normalized slot-length bound; all four
parameters are frozen within each label. -/
theorem reference_jets (lam c0 u ell : ι → ℝ)
    {M b : ℝ} (hM : 1 ≤ M) (hb : 0 < b)
    (hlam : ∀ i, |lam i| ≤ M) (hc : ∀ i, b ≤ |c0 i| ∧ |c0 i| ≤ M)
    (hu : ∀ i, |u i| ≤ M) (hrate : ∀ i, |u i / ell i| * D.scale i ≤ M)
    (hslot : ∀ i, ∀ z ∈ D.carrier i, |z.2| ≤ M * D.scale i) :
    PolynomialJets D (fun i z => ViscousPropagator.referenceEigenvalue (lam i) (u i) (ell i) z.2) ∧
    PolynomialJets D (fun i z => PrimaryODE.referenceProfile (c0 i) (u i) (ell i) z.2) ∧
    PolynomialJets D (fun i z => PrimaryODE.referenceProfileRate (u i) (ell i) z.2) ∧
    (∀ i, ∀ z ∈ D.carrier i, b ≤ |PrimaryODE.referenceProfile (c0 i) (u i) (ell i) z.2|) ∧
    (∀ i, ∀ z ∈ D.carrier i,
      |PrimaryODE.referenceProfile (c0 i) (u i) (ell i) z.2| ≤ M * (1 + M + M ^ 2)) := by
  have hq (i) : |u i / ell i| ≤ M := by
    nlinarith [hrate i, D.one_le_scale i, abs_nonneg (u i / ell i)]
  have pu := PolynomialJets.const_uniform (D := D) u hM (fun i => by simpa using hu i)
  have pq := PolynomialJets.const_uniform (D := D) (fun i => u i / ell i) hM
    (fun i => by simpa only [Real.norm_eq_abs] using hq i)
  have plam := PolynomialJets.const_uniform (D := D) lam hM (fun i => by simpa using hlam i)
  have pc := PolynomialJets.const_uniform (D := D) c0 hM (fun i => by simpa using (hc i).2)
  have pv : PolynomialJets D (fun _ z => z.2) := by
    simpa only [ContinuousLinearMap.coe_snd', add_zero] using
      (PolynomialJets.affine (D := D) (ContinuousLinearMap.snd ℝ Q ℝ)
        (fun _ => 0) (m := 1) hM (fun i z hz => by simpa using hslot i z hz))
  have heq (i) (z : Q × ℝ) : u i / 2 + (u i / ell i) * z.2 =
      PulseGrowth.slotMagnitude (u i) (ell i) z.2 := by
    unfold PulseGrowth.slotMagnitude
    ring
  have ps : PolynomialJets D (fun i z => PulseGrowth.slotMagnitude (u i) (ell i) z.2) :=
    ((pu.div_const 2).add (pq.mul pv)).congr (fun i z _ => heq i z)
  have hsb (i) (z : Q × ℝ) (hz : z ∈ D.carrier i) :
      |PulseGrowth.slotMagnitude (u i) (ell i) z.2| ≤ M + M ^ 2 := by
    rw [← heq i z]
    have h1 : |u i / 2| ≤ M := by rw [abs_div]; norm_num; linarith [hu i]
    have h2 : |(u i / ell i) * z.2| ≤ M ^ 2 := by
      rw [abs_mul]
      have hh := mul_le_mul_of_nonneg_left (hslot i z hz) (abs_nonneg (u i / ell i))
      have hh' := mul_le_mul_of_nonneg_right (hrate i) (show 0 ≤ M by linarith)
      linarith
    exact (abs_add_le _ _).trans (by linarith)
  obtain ⟨pr, pri, pdi⟩ := ps.radius hsb
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · simpa only [ViscousPropagator.referenceEigenvalue, div_eq_mul_inv] using plam.mul pri
  · exact pc.mul pr
  · simpa only [PrimaryODE.referenceProfileRate, div_eq_mul_inv] using (ps.mul pq).mul pdi
  · intro i z _
    have h := (radius_bounds (PulseGrowth.slotMagnitude (u i) (ell i) z.2)).1
    simp only [PrimaryODE.referenceProfile, abs_mul, abs_of_nonneg (Real.sqrt_nonneg _)]
    nlinarith [(hc i).1, abs_nonneg (c0 i)]
  · intro i z hz
    have h := (radius_bounds (PulseGrowth.slotMagnitude (u i) (ell i) z.2)).2.trans
      (add_le_add_right (hsb i z hz) 1)
    simp only [PrimaryODE.referenceProfile, abs_mul, abs_of_nonneg (Real.sqrt_nonneg _)]
    have hh := mul_le_mul (hc i).2 h (Real.sqrt_nonneg _) (show 0 ≤ M by linarith)
    linarith

end ReferenceJets

section Assembly

variable {ι : Type*}

/-- The actual phase-derived frame with the explicit reference eigenbasis.
Only the band/representative labels enter the frozen scalar choices. -/
noncomputable def PhaseFamily.frameData (a : PhaseFamily ι)
    (lam c0 u ell ν : ι → ℝ) (i : ι) : PrimaryODE.FrameData Slow :=
  PrimaryODE.FrameData.ofNormalLocal (a.normal i) (a.velocity i)
    (fun z => a.F i z.1) (a.shear i)
    (fun z => ViscousPropagator.referenceEigenvalue (lam i) (u i) (ell i) z.2)
    (fun z => PrimaryODE.referenceProfile (c0 i) (u i) (ell i) z.2)
    (fun z => PrimaryODE.referenceProfileRate (u i) (ell i) z.2)
    (fun _ => ν i)

/-- Assembly from actual base jets, frozen representative bounds, and the
zeroth-order phase comparison.  That comparison is the conclusion of
`PhaseEstimates.actual_phase_estimates`; smallness follows from its large-band
theorems.  The lower bound on the *actual* normal is derived inside this proof. -/
theorem PhaseFamily.frameData_jets_of_phase_comparison
    (a : PhaseFamily ι) (D : Domain ι Slow) (V : ι → Set ℝ) (hV : ∀ i, IsOpen (V i))
    (lam c0 u ell ν B : ι → ℝ) (K : ι → Plane) (s δ : ι → Slow × ℝ → ℝ)
    (hF : PolynomialJets D a.F) (hG : PolynomialJets D a.G)
    {r b M : ℝ} (hr : 0 < r) (hb : 0 < b) (hM : 1 ≤ M)
    (hconstant : ∀ i, |a.epsilon i| ≤ M ∧ |a.p i| ≤ M ∧ |a.pz i| ≤ M ∧ |a.x0 i| ≤ M)
    (heps : ∀ i, a.epsilon i ≠ 0)
    (hR : ∀ i, ∀ q ∈ D.carrier i, r ≤ |q.1| ∧ |q.1| ≤ M)
    (hslot : ∀ i, ∀ v ∈ V i, |v| ≤ M * D.scale i)
    (hlam : ∀ i, |lam i| ≤ M) (hc : ∀ i, b ≤ |c0 i| ∧ |c0 i| ≤ M)
    (hu : ∀ i, |u i| ≤ M) (hrate : ∀ i, |u i / ell i| * D.scale i ≤ M)
    (hν : ∀ i, |ν i| ≤ M)
    (hB : ∀ i, 2 * b ≤ B i ∧ B i ≤ M) (hK : ∀ i, ‖K i‖ = 1)
    (hs : ∀ i, ∀ z ∈ (D.slot V hV).carrier i, |s i z| ≤ M)
    (hδ : ∀ i, ∀ z ∈ (D.slot V hV).carrier i, δ i z ≤ B i / 2)
    (hclose : ∀ i, ∀ z ∈ (D.slot V hV).carrier i,
      ‖a.normal i z - MovingFrameODE.pack (B i * s i z) (B i • K i)‖ ≤ δ i z) :
    FrameJets (D.slot V hV) (a.frameData lam c0 u ell ν) := by
  obtain ⟨hn, hd, hg⟩ := a.polynomial_jets D V hV hF hG hr hM hconstant heps hR hslot
  obtain ⟨hnlow, hnup⟩ := normal_range_of_reference_close (D := D.slot V hV)
    B K s δ hb hM hB hK hs hδ hclose
  obtain ⟨hl, hh, hq, hhlow, hhup⟩ := reference_jets (D := D.slot V hV)
    lam c0 u ell hM hb hlam hc hu hrate (fun i z hz => hslot i z.2 hz.2)
  have hνj := PolynomialJets.const_uniform (D := D.slot V hV) ν hM
    (fun i => by simpa only [Real.norm_eq_abs] using hν i)
  exact frameJets_ofNormalLocal hn hd (hF.lift_slot V hV) hg hl hh hq hνj
    hb hb hnlow hnup hhlow hhup

/-- Direct output in the fixed-slot format used by the ODE jet theorem.
The coefficient is the actual `FrameData.coefficient`, not a comparison ODE. -/
theorem FrameJets.coefficient_parameter_bounds
    {Q : Type} [NormedAddCommGroup Q] [NormedSpace ℝ Q]
    {D : Domain ι (Q × ℝ)} {d : ι → PrimaryODE.FrameData Q}
    (hd : FrameJets D d) (j : ℤ) (N : ℕ) :
    ∃ C : ℝ, 1 ≤ C ∧ ∃ m : ℕ, ∀ i p v, (p, v) ∈ D.carrier i →
      ∀ k ≤ N, ‖iteratedFDeriv ℝ k (fun q => (d i).coefficient j (q, v)) p‖ ≤
        C * D.scale i ^ m :=
  (hd.coefficient j).parameter_bound N

end Assembly

section BandChoices

variable {ι E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {D : Domain ι E}

/-- The genuine nonzero angular rounding preserves uniform boundedness.
It is constant in the chart variables even when it jumps across labels. -/
theorem rounded_frequency_jets (k target : ι → ℝ) {M : ℝ} (hM : 1 ≤ M)
    (hk : ∀ i, 1 ≤ k i) (ht : ∀ i, |target i| ≤ M) :
    PolynomialJets D (fun i _ => PhaseEstimates.roundedFrequency (k i) (target i)) := by
  apply PolynomialJets.const_uniform _ (show 1 ≤ M + 1 by linarith)
  intro i
  have hkpos : 0 < k i := lt_of_lt_of_le zero_lt_one (hk i)
  have herr := PhaseEstimates.roundedFrequency_error hkpos (target i)
  have hinv : 1 / k i ≤ 1 := (div_le_one hkpos).mpr (hk i)
  have hsum := abs_add_le (PhaseEstimates.roundedFrequency (k i) (target i) - target i) (target i)
  rw [sub_add_cancel] at hsum
  rw [Real.norm_eq_abs]
  linarith [ht i]

/-- With the actual carrier choice, the fundamental viscosity factor is a
uniformly bounded label constant.  Thus no factor k is lost in slow jets. -/
theorem band_viscosity_jets (band : ι → ℕ) (h : ℝ) (hh : 0 ≤ h) :
    PolynomialJets D (fun i _ => ChartScales.epsilon h (band i) *
      (ChartScales.carrier h (band i) : ℝ) ^ 2) := by
  apply PolynomialJets.const_uniform _ (by norm_num : (1 : ℝ) ≤ 4)
  intro i
  obtain ⟨hl, hu⟩ := ChartScales.carrier_viscosity_bounds h hh (band i)
  rw [Real.norm_eq_abs, abs_of_nonneg (le_trans zero_le_one hl)]
  exact hu

theorem band_epsilon_jets (band : ι → ℕ) (h : ℝ) (hh : 0 ≤ h) :
    PolynomialJets D (fun i _ => ChartScales.epsilon h (band i)) := by
  apply PolynomialJets.const_uniform _ (le_refl (1 : ℝ))
  intro i
  rw [Real.norm_eq_abs, abs_of_pos (ChartScales.epsilon_pos h (band i))]
  exact ChartScales.epsilon_le_one h hh (band i)

theorem band_rounded_frequency_jets (band : ι → ℕ) (h : ℝ) (target : ι → ℝ)
    {M : ℝ} (hM : 1 ≤ M) (ht : ∀ i, |target i| ≤ M) :
    PolynomialJets D (fun i _ => PhaseEstimates.roundedFrequency
      (ChartScales.carrier h (band i) : ℝ) (target i)) := by
  apply rounded_frequency_jets _ target hM _ ht
  intro i
  have hp : 0 < (ChartScales.carrier h (band i) : ℝ) :=
    Scaling.carrier_frequency_pos (ChartScales.epsilon_pos h (band i))
  have hp' : 0 < ChartScales.carrier h (band i) := by exact_mod_cast hp
  exact_mod_cast hp'

/-- A direct domain constructor with the manuscript's S(n)=n². -/
noncomputable def Domain.ofBands (band : ι → ℕ) (hband : ∀ i, 1 ≤ band i)
    (U : ι → Set E) (hU : ∀ i, IsOpen (U i)) : Domain ι E where
  scale i := ChartScales.S (band i)
  carrier := U
  isOpen := hU
  one_le_scale i := by
    have h : (1 : ℝ) ≤ band i := by exact_mod_cast hband i
    dsimp [ChartScales.S]
    nlinarith

omit [NormedSpace ℝ E] in
/-- The reference logarithmic-rate input follows from a lower slot-length
bound.  In particular `ChartScales.slotLength_bounds` gives c=2r₀. -/
theorem normalized_slot_rate_le {S ell u c M : ℝ} (hS : 0 < S) (hc : 0 < c)
    (hell : c * S ≤ ell) (hu : |u| ≤ M) : |u / ell| * S ≤ M / c := by
  have hellpos : 0 < ell := lt_of_lt_of_le (mul_pos hc hS) hell
  have hM : 0 ≤ M := (abs_nonneg u).trans hu
  rw [abs_div, abs_of_pos hellpos]
  apply (le_div_iff₀ hc).mpr
  rw [div_mul_eq_mul_div, div_mul_eq_mul_div]
  apply (div_le_iff₀ hellpos).mpr
  have h1 := mul_le_mul_of_nonneg_right hu (mul_nonneg hS.le hc.le)
  have h2 := mul_le_mul_of_nonneg_left hell hM
  linarith

end BandChoices

end NavierStokes.PhaseJetBounds

end
end

end

@[expose] public section

noncomputable section

namespace NavierStokes.CurlClassBounds

open Set Filter Function WeightedClasses
open scoped Topology ContDiff BigOperators InnerProductSpace

/-- Real vector: an abbreviation for `ProblemStatement.Space`. -/
abbrev RealVector := ProblemStatement.Space
/-- Complex vector: an abbreviation for `HarmonicCalculus.ComplexVector`. -/
abbrev ComplexVector := HarmonicCalculus.ComplexVector

private theorem nat_le_smooth (m : ℕ) : (m : WithTop ℕ∞) ≤ ∞ :=
  WithTop.coe_le_coe.mpr le_top

section Classes

variable {D E F : Type*} [NormedAddCommGroup D] [NormedSpace ℝ D]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
  {s : StripData D} {w : ℕ → D → ℝ} {α β : ℝ}

theorem class_congr {f g : ℕ → D → E} (hf : MemClass s w α f)
    (hfg : ∀ n, EqOn (f n) (g n) s.domain) : MemClass s w α g := by
  refine ⟨hf.weight_nonneg, fun n => (hf.smooth n).congr (fun x hx => (hfg n hx).symm), ?_⟩
  intro m
  obtain ⟨C, hC, p, hB⟩ := hf.bounds m
  refine ⟨C, hC, p, ?_⟩
  intro n x hx j hj
  have he := iteratedFDerivWithin_congr (𝕜 := ℝ) (hfg n) hx j
  rw [iteratedFDerivWithin_of_isOpen j s.isOpen_domain hx,
    iteratedFDerivWithin_of_isOpen j s.isOpen_domain hx] at he
  rw [← he]
  exact hB n x hx j hj

theorem class_neg {f : ℕ → D → E} (hf : MemClass s w α f) :
    MemClass s w α (fun n x => -f n x) := by
  simpa using hf.map (-ContinuousLinearMap.id ℝ E)

theorem class_sub {f g : ℕ → D → E} (hf : MemClass s w α f) (hg : MemClass s w α g) :
    MemClass s w α (fun n x => f n x - g n x) := by
  simpa only [sub_eq_add_neg] using hf.add (class_neg hg)

theorem class_component {a : ℕ → D → ComplexVector} (ha : MemClass s w α a) (i : Fin 3) :
    MemClass s w α (fun n x => a n x i) := ha.map (ContinuousLinearMap.proj i)

theorem class_vector {a : ℕ → D → ComplexVector}
    (ha : ∀ i : Fin 3, MemClass s w α (fun n x => a n x i)) : MemClass s w α a := by
  have hsum := MemClass.sum (s := s) (w := w) (α := α) Finset.univ
    (fun i n x => (ContinuousLinearMap.single ℝ (fun _ : Fin 3 => ℂ) i) (a n x i))
    (ha 0).weight_nonneg
    (fun i _ => (ha i).map (ContinuousLinearMap.single ℝ (fun _ : Fin 3 => ℂ) i))
  apply class_congr hsum
  intro n x hx
  ext i
  simp

/-- A genuine directional derivative consumes the class of its vector field. -/
theorem class_along {V : ℕ → D → D} {f : ℕ → D → E}
    (hV : UnweightedClass s β V) (hf : MemClass s w α f) :
    MemClass s w (α + β) (fun n => HarmonicCalculus.along (V n) (f n)) := by
  have h := hf.fderiv.bilinear hV (ContinuousLinearMap.apply ℝ E).flip
  simp only [mul_one] at h
  exact h

theorem class_mul_real {r : ℕ → D → ℝ} {f : ℕ → D → E}
    (hr : UnweightedClass s β r) (hf : MemClass s w α f) :
    MemClass s w (β + α) (fun n x => r n x • f n x) := by
  simpa only [one_mul] using hr.smul hf

theorem class_const_complex {f : ℕ → D → ComplexVector} (hf : MemClass s w α f) (c : ℂ) :
    MemClass s w α (fun n x => c • f n x) := by
  simpa using hf.map (c • ContinuousLinearMap.id ℝ ComplexVector)

/-- The phase-jet domain corresponding to the actual strip data. -/
noncomputable def phaseDomain (s : StripData D) : PhaseJetBounds.Domain ℕ D where
  scale := s.slow
  carrier := fun _ => s.domain
  isOpen := fun _ => s.isOpen_domain
  one_le_scale := s.one_le_slow

theorem polynomialJets_unweighted {f : ℕ → D → E}
    (hf : PhaseJetBounds.PolynomialJets (phaseDomain s) f) : UnweightedClass s 0 f := by
  refine ⟨fun _ _ _ => zero_le_one, hf.smooth, ?_⟩
  intro m
  obtain ⟨C, hC, p, hB⟩ := hf.bound m
  refine ⟨C, zero_le_one.trans hC, p, ?_⟩
  intro n x hx j hj
  apply (hB n j hj x hx).trans
  simp only [majorant, Real.rpow_zero, mul_one, phaseDomain]
  exact mul_le_mul_of_nonneg_left
    (pow_le_pow_left₀ (zero_le_one.trans (s.one_le_slow n)) (s.slow_le_growth n x) p)
    (zero_le_one.trans hC)

end Classes

/-- Real vectors embedded coordinatewise in the complex coefficient space. -/
noncomputable def complexify : RealVector →L[ℝ] ComplexVector :=
  ContinuousLinearMap.pi (fun i => Complex.ofRealCLM.comp (EuclideanSpace.proj i))

@[simp] theorem complexify_apply (a : RealVector) (i : Fin 3) : complexify a i = (a i : ℂ) := rfl

/-- Complex cross linear as an element of `ComplexVector →L[ℝ] ComplexVector →L[ℝ]
ComplexVector`. -/
noncomputable def complexCrossLinear : ComplexVector →L[ℝ] ComplexVector →L[ℝ] ComplexVector :=
  (ContinuousLinearMap.proj 1).smulRight
      ((ContinuousLinearMap.proj 2).smulRight (Pi.single 0 (1 : ℂ))) -
  (ContinuousLinearMap.proj 2).smulRight
      ((ContinuousLinearMap.proj 1).smulRight (Pi.single 0 (1 : ℂ))) +
  (ContinuousLinearMap.proj 2).smulRight
      ((ContinuousLinearMap.proj 0).smulRight (Pi.single 1 (1 : ℂ))) -
  (ContinuousLinearMap.proj 0).smulRight
      ((ContinuousLinearMap.proj 2).smulRight (Pi.single 1 (1 : ℂ))) +
  (ContinuousLinearMap.proj 0).smulRight
      ((ContinuousLinearMap.proj 1).smulRight (Pi.single 2 (1 : ℂ))) -
  (ContinuousLinearMap.proj 1).smulRight
      ((ContinuousLinearMap.proj 0).smulRight (Pi.single 2 (1 : ℂ)))

/-- Normal cross, given by `complexCrossLinear (complexify n) a`. -/
noncomputable def normalCross (n : RealVector) (a : ComplexVector) : ComplexVector :=
  complexCrossLinear (complexify n) a

theorem normalCross_apply (n : RealVector) (a : ComplexVector) :
    normalCross n a =
      (n 1 : ℂ) • (a 2 • Pi.single 0 (1 : ℂ)) -
      (n 2 : ℂ) • (a 1 • Pi.single 0 (1 : ℂ)) +
      (n 2 : ℂ) • (a 0 • Pi.single 1 (1 : ℂ)) -
      (n 0 : ℂ) • (a 2 • Pi.single 1 (1 : ℂ)) +
      (n 0 : ℂ) • (a 1 • Pi.single 2 (1 : ℂ)) -
      (n 1 : ℂ) • (a 0 • Pi.single 2 (1 : ℂ)) := rfl

@[simp] theorem normalCross_zero (n : RealVector) (a : ComplexVector) :
    normalCross n a 0 = (n 1 : ℂ) * a 2 - (n 2 : ℂ) * a 1 := by
  rw [normalCross_apply]
  simp

@[simp] theorem normalCross_one (n : RealVector) (a : ComplexVector) :
    normalCross n a 1 = (n 2 : ℂ) * a 0 - (n 0 : ℂ) * a 2 := by
  rw [normalCross_apply]
  simp

@[simp] theorem normalCross_two (n : RealVector) (a : ComplexVector) :
    normalCross n a 2 = (n 0 : ℂ) * a 1 - (n 1 : ℂ) * a 0 := by
  rw [normalCross_apply]
  simp

theorem normalCross_smul (n : RealVector) (a : ComplexVector) (c : ℂ) :
    normalCross n (c • a) = c • normalCross n a := by
  ext i
  fin_cases i <;> simp [mul_sub] <;> ring

theorem normalCross_real_smul (n : RealVector) (a : ComplexVector) (c : ℝ) :
    normalCross n (c • a) = c • normalCross n a := by simp [normalCross]

theorem normalCross_triple (n : RealVector) (a : ComplexVector) :
    normalCross n (normalCross n a) =
      HarmonicCalculus.normalDot n a • complexify n - (‖n‖ ^ 2) • a := by
  have hn : ‖n‖ ^ 2 = n 0 * n 0 + n 1 * n 1 + n 2 * n 2 := by
    rw [← real_inner_self_eq_norm_sq, OscillatoryCurl.inner_coordinates]
  rw [hn]
  ext i
  fin_cases i <;>
    simp [HarmonicCalculus.normalDot, Complex.real_smul, Complex.ofReal_add,
      Complex.ofReal_mul] <;> ring

/-- The actual coefficient in the vector potential (30). -/
noncomputable def normalCoefficient (n : RealVector) (a : ComplexVector) : ComplexVector :=
  (‖n‖ ^ 2)⁻¹ • normalCross n a

theorem normalCross_normalCoefficient {n : RealVector} {a : ComplexVector}
    (hn : n ≠ 0) (ha : HarmonicCalculus.normalDot n a = 0) :
    normalCross n (normalCoefficient n a) = -a := by
  rw [normalCoefficient, normalCross_real_smul, normalCross_triple, ha, zero_smul,
    zero_sub, smul_neg, smul_smul,
    inv_mul_cancel₀ (pow_ne_zero 2 (norm_ne_zero_iff.mpr hn)), one_smul]

section Coefficients

variable {D : Type*} [NormedAddCommGroup D] [NormedSpace ℝ D]
  {s : StripData D} {w : ℕ → D → ℝ} {α : ℝ}

/-- The inverse-square normalization is derived from normal jets and a
separated bounded range. It is not an assumed coefficient estimate. -/
theorem normalInverse_unweighted {N : ℕ → D → RealVector}
    (hN : PhaseJetBounds.PolynomialJets (phaseDomain s) N) {b M : ℝ} (hb : 0 < b)
    (hlower : ∀ n x, x ∈ s.domain → b ≤ ‖N n x‖)
    (hupper : ∀ n x, x ∈ s.domain → ‖N n x‖ ≤ M) :
    UnweightedClass s 0 (fun n x => (‖N n x‖ ^ 2)⁻¹) := by
  apply polynomialJets_unweighted
  apply hN.norm_sq.inv (b := b ^ 2) (M := M ^ 2) (by positivity)
  · intro n x hx
    rw [abs_of_nonneg (sq_nonneg _)]
    exact (sq_le_sq₀ hb.le (norm_nonneg _)).2 (hlower n x hx)
  · intro n x hx
    rw [abs_of_nonneg (sq_nonneg _)]
    exact (sq_le_sq₀ (norm_nonneg _) ((norm_nonneg _).trans (hupper n x hx))).2
      (hupper n x hx)

theorem normalCoefficient_class {N : ℕ → D → RealVector} {a : ℕ → D → ComplexVector}
    (hN : PhaseJetBounds.PolynomialJets (phaseDomain s) N) (ha : MemClass s w α a)
    {b M : ℝ} (hb : 0 < b)
    (hlower : ∀ n x, x ∈ s.domain → b ≤ ‖N n x‖)
    (hupper : ∀ n x, x ∈ s.domain → ‖N n x‖ ≤ M) :
    MemClass s w α (fun n x => normalCoefficient (N n x) (a n x)) := by
  have hcross : MemClass s w α (fun n x => normalCross (N n x) (a n x)) := by
    simpa only [one_mul, zero_add, normalCross] using
      ((polynomialJets_unweighted hN).map complexify).bilinear ha complexCrossLinear
  simpa only [zero_add, normalCoefficient] using
    class_mul_real (normalInverse_unweighted hN hb hlower hupper) hcross

end Coefficients

/-- Actual cylindrical curl, including the frame connection in its axial component. -/
noncomputable def cylindricalCurl {D : Type*} [NormedAddCommGroup D] [NormedSpace ℝ D]
    (R : D → ℝ) (Vr Vθ Vz : D → D) (a : D → ComplexVector) (x : D) : ComplexVector :=
  ![(R x)⁻¹ • HarmonicCalculus.along Vθ (fun y => a y 2) x -
      HarmonicCalculus.along Vz (fun y => a y 1) x,
    HarmonicCalculus.along Vz (fun y => a y 0) x -
      HarmonicCalculus.along Vr (fun y => a y 2) x,
    HarmonicCalculus.along Vr (fun y => a y 1) x + (R x)⁻¹ • a x 1 -
      (R x)⁻¹ • HarmonicCalculus.along Vθ (fun y => a y 0) x]

section CurlClass

variable {D : Type*} [NormedAddCommGroup D] [NormedSpace ℝ D]
  {s : StripData D} {w : ℕ → D → ℝ} {α κ : ℝ}
  {R : D → ℝ} {Vr Vθ Vz : ℕ → D → D} {a : ℕ → D → ComplexVector}

theorem cylindricalCurl_class (ha : MemClass s w α a) (hκ : 0 ≤ κ)
    (hr : UnweightedClass s (-κ) Vr) (hθ : UnweightedClass s 0 Vθ)
    (hz : UnweightedClass s 1 Vz) (hR : UnweightedClass s 0 (fun _ x => (R x)⁻¹)) :
    MemClass s w (α - κ) (fun n => cylindricalCurl R (Vr n) (Vθ n) (Vz n) (a n)) := by
  have hDr (i : Fin 3) : MemClass s w (α - κ)
      (fun n => HarmonicCalculus.along (Vr n) (fun x => a n x i)) := by
    simpa only [sub_eq_add_neg] using class_along hr (class_component ha i)
  have hDz (i : Fin 3) : MemClass s w (α - κ)
      (fun n => HarmonicCalculus.along (Vz n) (fun x => a n x i)) :=
    (class_along hz (class_component ha i)).mono_exponent (by linarith)
  have hDθ (i : Fin 3) : MemClass s w (α - κ)
      (fun n x => (R x)⁻¹ • HarmonicCalculus.along (Vθ n) (fun y => a n y i) x) := by
    apply (class_mul_real hR (class_along hθ (class_component ha i))).mono_exponent
    linarith
  have hconn (i : Fin 3) : MemClass s w (α - κ) (fun n x => (R x)⁻¹ • a n x i) :=
    (class_mul_real hR (class_component ha i)).mono_exponent (by linarith)
  apply class_vector
  intro i
  fin_cases i
  · exact class_sub (hDθ 2) (hDz 1)
  · exact class_sub (hDz 0) (hDr 2)
  · exact class_sub ((hDr 1).add (hconn 1)) (hDθ 0)

theorem strippedDivergence_class (ha : MemClass s w α a) (hκ : 0 ≤ κ)
    (hr : UnweightedClass s (-κ) Vr) (hz : UnweightedClass s 1 Vz)
    (hR : UnweightedClass s 0 (fun _ x => (R x)⁻¹)) :
    MemClass s w (α - κ)
      (fun n => HarmonicCalculus.strippedDivergence R (Vr n) (Vz n) (a n)) := by
  have hDr : MemClass s w (α - κ)
      (fun n => HarmonicCalculus.along (Vr n) (fun x => a n x 0)) := by
    simpa only [sub_eq_add_neg] using class_along hr (class_component ha 0)
  have hDz : MemClass s w (α - κ)
      (fun n => HarmonicCalculus.along (Vz n) (fun x => a n x 2)) :=
    (class_along hz (class_component ha 2)).mono_exponent (by linarith)
  have hconn : MemClass s w (α - κ) (fun n x => (R x)⁻¹ • a n x 0) :=
    (class_mul_real hR (class_component ha 0)).mono_exponent (by linarith)
  exact (hDr.add hconn).add hDz

end CurlClass

/-- The inverse frequency is the only band factor in the stripped curl error. -/
noncomputable def curlRemainder {D : Type*} [NormedAddCommGroup D] [NormedSpace ℝ D]
    (K : ℝ) (R : D → ℝ) (Vr Vθ Vz : D → D) (B : D → ComplexVector) (x : D) : ComplexVector :=
  (1 / K) • (Complex.I • cylindricalCurl R Vr Vθ Vz B x)

section RemainderClasses

variable {D : Type*} [NormedAddCommGroup D] [NormedSpace ℝ D]
  {s : StripData D} {w : ℕ → D → ℝ} {α κ : ℝ}
  {R : D → ℝ} {Vr Vθ Vz : ℕ → D → D} {K : ℕ → ℝ}

theorem curlRemainder_class {B : ℕ → D → ComplexVector} (hB : MemClass s w α B)
    (hκ : 0 ≤ κ) (hr : UnweightedClass s (-κ) Vr) (hθ : UnweightedClass s 0 Vθ)
    (hz : UnweightedClass s 1 Vz) (hR : UnweightedClass s 0 (fun _ x => (R x)⁻¹))
    (hK : BandBound s (1 / 2) (fun n => 1 / K n)) :
    MemClass s w (α + 1 / 2 - κ)
      (fun n => curlRemainder (K n) R (Vr n) (Vθ n) (Vz n) (B n)) := by
  have h := (class_const_complex (cylindricalCurl_class hB hκ hr hθ hz hR) Complex.I).band_smul hK
  have he : α - κ + 1 / 2 = α + 1 / 2 - κ := by ring
  simp only [he] at h
  exact h

/-- The all-jet estimate is derived for the actual normalized vector potential. -/
theorem normalCurlRemainder_class {N : ℕ → D → RealVector} {a : ℕ → D → ComplexVector}
    (hN : PhaseJetBounds.PolynomialJets (phaseDomain s) N) (ha : MemClass s w α a)
    {b M : ℝ} (hb : 0 < b)
    (hlower : ∀ n x, x ∈ s.domain → b ≤ ‖N n x‖)
    (hupper : ∀ n x, x ∈ s.domain → ‖N n x‖ ≤ M)
    (hκ : 0 ≤ κ) (hr : UnweightedClass s (-κ) Vr) (hθ : UnweightedClass s 0 Vθ)
    (hz : UnweightedClass s 1 Vz) (hR : UnweightedClass s 0 (fun _ x => (R x)⁻¹))
    (hK : BandBound s (1 / 2) (fun n => 1 / K n)) :
    MemClass s w (α + 1 / 2 - κ) (fun n =>
      curlRemainder (K n) R (Vr n) (Vθ n) (Vz n)
        (fun x => normalCoefficient (N n x) (a n x))) :=
  curlRemainder_class (normalCoefficient_class hN ha hb hlower hupper) hκ hr hθ hz hR hK

/-- Carrier frequency, given by `Scaling.carrierFrequency (s.epsilon n)`. -/
noncomputable def carrierFrequency (s : StripData D) (n : ℕ) : ℝ :=
  Scaling.carrierFrequency (s.epsilon n)

theorem carrierFrequency_pos (s : StripData D) (n : ℕ) : 0 < carrierFrequency s n :=
  Scaling.carrier_frequency_pos (s.epsilon_pos n)

/-- The rounded frequency itself supplies the half-power gain, uniformly in
any nonzero integer harmonic. -/
theorem harmonic_inverse_bandBound (s : StripData D) (j : ℕ → ℤ) (hj : ∀ n, j n ≠ 0) :
    BandBound s (1 / 2) (fun n => 1 / (carrierFrequency s n * (j n : ℝ))) := by
  refine ⟨1, zero_le_one, 0, ?_⟩
  intro n
  have hk := carrierFrequency_pos s n
  have hjabs : (1 : ℝ) ≤ |(j n : ℝ)| := by exact_mod_cast Int.one_le_abs (hj n)
  have hden : carrierFrequency s n ≤ carrierFrequency s n * |(j n : ℝ)| :=
    le_mul_of_one_le_right hk.le hjabs
  simp only [Real.norm_eq_abs, abs_div, abs_one, abs_mul, abs_of_pos hk, pow_zero, mul_one, one_mul]
  calc
    1 / (carrierFrequency s n * |(j n : ℝ)|) ≤ 1 / carrierFrequency s n :=
      div_le_div_of_nonneg_left zero_le_one hk hden
    _ ≤ Real.sqrt (s.epsilon n) :=
      (Scaling.reciprocal_frequency_bounds (s.epsilon_pos n) (s.epsilon_le_one n)).2
    _ = _ := Real.sqrt_eq_rpow _

theorem graphVector_class {ρ : D → ℝ} {M : ℕ → ℝ}
    (hρ : UnweightedClass s 0 (fun _ => ρ)) (hM : BandBound s (-κ) M) (hκ : 0 ≤ κ)
    (e v : D) :
    UnweightedClass s (-κ) (fun n x => e + M n • (ρ x • v)) := by
  have hv : UnweightedClass s 0 (fun _ x => ρ x • v) := by
    have h := hρ.smul (unweighted_const s v)
    simp only [zero_add, one_mul] at h
    exact h
  have hm : UnweightedClass s (-κ) (fun n x => M n • (ρ x • v)) := by
    have h := hv.band_smul hM
    simp only [zero_add] at h
    exact h
  exact ((unweighted_const s e).mono_exponent (by linarith)).add hm

theorem axialVector_class (s : StripData D) (z : D) :
    UnweightedClass s 1 (fun n _ => s.epsilon n • z) := by
  have h := (unweighted_const s z).band_smul (bandBound_rpow s 1)
  simp only [zero_add, Real.rpow_one] at h
  exact h

end RemainderClasses

section CurlIdentities

variable {D : Type*} [NormedAddCommGroup D] [NormedSpace ℝ D]

theorem cylindricalCurl_contDiffOn {U : Set D} (hU : IsOpen U) {R : D → ℝ}
    {Vr Vθ Vz : D → D} {B : D → ComplexVector}
    (hR : ContDiffOn ℝ ∞ (fun x => (R x)⁻¹) U)
    (hr : ContDiffOn ℝ ∞ Vr U) (hθ : ContDiffOn ℝ ∞ Vθ U) (hz : ContDiffOn ℝ ∞ Vz U)
    (hB : ContDiffOn ℝ ∞ B U) : ContDiffOn ℝ ∞ (cylindricalCurl R Vr Vθ Vz B) U := by
  have hb := contDiffOn_pi.mp hB
  have hDr i := HarmonicCalculus.contDiffOn_along hU hr (hb i)
  have hDθ i := HarmonicCalculus.contDiffOn_along hU hθ (hb i)
  have hDz i := HarmonicCalculus.contDiffOn_along hU hz (hb i)
  apply contDiffOn_pi.mpr
  intro i
  fin_cases i
  · exact (hR.smul (hDθ 2)).sub (hDz 1)
  · exact (hDz 0).sub (hDr 2)
  · exact ((hDr 1).add (hR.smul (hb 1))).sub (hR.smul (hDθ 0))

/-- Every coefficient derivative and cylindrical connection survives stripping. -/
theorem cylindricalCurl_vectorMode (R : D → ℝ) (Vr Vθ Vz : D → D) (K : ℝ)
    {Φ : D → ℝ} {B : D → ComplexVector} {x : D}
    (hΦ : DifferentiableAt ℝ Φ x) (hB : ∀ i, DifferentiableAt ℝ (fun y => B y i) x) :
    cylindricalCurl R Vr Vθ Vz (HarmonicCalculus.vectorMode K Φ B) x =
      fun i => (cylindricalCurl R Vr Vθ Vz B x i + HarmonicCalculus.phaseFactor K *
        normalCross (HarmonicCalculus.phaseNormal R Vr Vθ Vz Φ x) (B x) i) *
          HarmonicCalculus.carrier K Φ x := by
  have hD (V : D → D) (i : Fin 3) :
      HarmonicCalculus.along V (fun y => B y i * HarmonicCalculus.carrier K Φ y) x =
        (HarmonicCalculus.along V (fun y => B y i) x +
          HarmonicCalculus.phaseFactor K * Complex.ofReal (HarmonicCalculus.along V Φ x) * B x i) *
            HarmonicCalculus.carrier K Φ x :=
    HarmonicCalculus.along_mode V K hΦ (hB i)
  ext i
  fin_cases i <;>
    simp [cylindricalCurl, HarmonicCalculus.vectorMode, HarmonicCalculus.mode, hD,
      HarmonicCalculus.phaseNormal, Complex.real_smul] <;> ring

theorem cylindricalCurl_const_smul (R : D → ℝ) (Vr Vθ Vz : D → D) (c : ℂ)
    {B : D → ComplexVector} {x : D} (hB : ∀ i, DifferentiableAt ℝ (fun y => B y i) x) :
    cylindricalCurl R Vr Vθ Vz (fun y => c • B y) x = c • cylindricalCurl R Vr Vθ Vz B x := by
  ext i
  fin_cases i <;>
    simp [cylindricalCurl, Pi.smul_apply, smul_eq_mul,
      HarmonicCalculus.along_const_mul _ c (hB 0),
      HarmonicCalculus.along_const_mul _ c (hB 1),
      HarmonicCalculus.along_const_mul _ c (hB 2), Complex.real_smul] <;> ring

end CurlIdentities

section Divergence

variable {D : Type*} [NormedAddCommGroup D] [NormedSpace ℝ D]

/-- Primitive geometric identities for genuine cylindrical graph directions.
The bracket hypotheses concern derivatives of the direction fields themselves. -/
structure CylindricalGeometry (U : Set D) (R : D → ℝ) (Vr Vθ Vz : D → D) : Prop where
  isOpen : IsOpen U
  radius_smooth : ContDiffOn ℝ ∞ R U
  radius_ne : ∀ x ∈ U, R x ≠ 0
  radial_smooth : ContDiffOn ℝ ∞ Vr U
  angular_smooth : ContDiffOn ℝ ∞ Vθ U
  axial_smooth : ContDiffOn ℝ ∞ Vz U
  radial_radius : ∀ x ∈ U, HarmonicCalculus.along Vr R x = 1
  angular_radius : ∀ x ∈ U, HarmonicCalculus.along Vθ R x = 0
  axial_radius : ∀ x ∈ U, HarmonicCalculus.along Vz R x = 0
  radial_angular : ∀ x ∈ U, fderiv ℝ Vθ x (Vr x) = fderiv ℝ Vr x (Vθ x)
  radial_axial : ∀ x ∈ U, fderiv ℝ Vz x (Vr x) = fderiv ℝ Vr x (Vz x)
  angular_axial : ∀ x ∈ U, fderiv ℝ Vz x (Vθ x) = fderiv ℝ Vθ x (Vz x)

theorem along_commute {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {f : D → F} {V W : D → D} {x : D} (hf : ContDiffAt ℝ ∞ f x)
    (hV : DifferentiableAt ℝ V x) (hW : DifferentiableAt ℝ W x)
    (hbracket : fderiv ℝ W x (V x) = fderiv ℝ V x (W x)) :
    HarmonicCalculus.along V (HarmonicCalculus.along W f) x =
      HarmonicCalculus.along W (HarmonicCalculus.along V f) x := by
  have hf2 : ContDiffAt ℝ 2 f x := hf.of_le (nat_le_smooth 2)
  have hDF := (hf2.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  unfold HarmonicCalculus.along
  rw [fderiv_clm_apply hDF hW, fderiv_clm_apply hDF hV]
  simp only [_root_.add_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.flip_apply]
  rw [hbracket, (hf2.isSymmSndFDerivAt (by norm_num)).eq (V x) (W x)]

theorem along_sub {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (V : D → D) {f g : D → F} {x : D}
    (hf : DifferentiableAt ℝ f x) (hg : DifferentiableAt ℝ g x) :
    HarmonicCalculus.along V (fun y => f y - g y) x =
      HarmonicCalculus.along V f x - HarmonicCalculus.along V g x := by
  simp only [HarmonicCalculus.along, fderiv_fun_sub hf hg, _root_.sub_apply]

theorem along_real_smul (V : D → D) {r : D → ℝ} {f : D → ℂ} {x : D}
    (hr : DifferentiableAt ℝ r x) (hf : DifferentiableAt ℝ f x) :
    HarmonicCalculus.along V (fun y => r y • f y) x =
      HarmonicCalculus.along V r x • f x + r x • HarmonicCalculus.along V f x := by
  simp only [HarmonicCalculus.along, fderiv_fun_smul hr hf, _root_.add_apply,
    _root_.smul_apply, ContinuousLinearMap.smulRight_apply]
  exact add_comm _ _

theorem along_inv (V : D → D) {R : D → ℝ} {x : D}
    (hR : DifferentiableAt ℝ R x) (hne : R x ≠ 0) :
    HarmonicCalculus.along V (fun y => (R y)⁻¹) x =
      (-(R x ^ 2)⁻¹) * HarmonicCalculus.along V R x := by
  have h := (hasDerivAt_inv hne).comp_hasFDerivAt x hR.hasFDerivAt
  dsimp only [Function.comp_def] at h
  unfold HarmonicCalculus.along
  rw [h.fderiv]
  rfl

/-- Divergence of the actual cylindrical curl is zero, including its frame term. -/
theorem divergence_curl_zero {U : Set D} {R : D → ℝ} {Vr Vθ Vz : D → D}
    (G : CylindricalGeometry U R Vr Vθ Vz) {B : D → ComplexVector}
    (hB : ContDiffOn ℝ ∞ B U) {x : D} (hx : x ∈ U) :
    HarmonicCalculus.cylindricalDivergence R Vr Vθ Vz (cylindricalCurl R Vr Vθ Vz B) x = 0 := by
  have hBi := contDiffOn_pi.mp hB
  have hDr i := HarmonicCalculus.contDiffOn_along G.isOpen G.radial_smooth (hBi i)
  have hDθ i := HarmonicCalculus.contDiffOn_along G.isOpen G.angular_smooth (hBi i)
  have hDz i := HarmonicCalculus.contDiffOn_along G.isOpen G.axial_smooth (hBi i)
  have db i := ((hBi i).contDiffAt (G.isOpen.mem_nhds hx)).differentiableAt (by simp)
  have dr i := ((hDr i).contDiffAt (G.isOpen.mem_nhds hx)).differentiableAt (by simp)
  have dθ i := ((hDθ i).contDiffAt (G.isOpen.mem_nhds hx)).differentiableAt (by simp)
  have dz i := ((hDz i).contDiffAt (G.isOpen.mem_nhds hx)).differentiableAt (by simp)
  have dinv := ((G.radius_smooth.inv G.radius_ne).contDiffAt
    (G.isOpen.mem_nhds hx)).differentiableAt (by simp)
  change DifferentiableAt ℝ (fun y => (R y)⁻¹) x at dinv
  have dR := (G.radius_smooth.contDiffAt (G.isOpen.mem_nhds hx)).differentiableAt (by simp)
  have dVr := (G.radial_smooth.contDiffAt (G.isOpen.mem_nhds hx)).differentiableAt (by simp)
  have dVθ := (G.angular_smooth.contDiffAt (G.isOpen.mem_nhds hx)).differentiableAt (by simp)
  have dVz := (G.axial_smooth.contDiffAt (G.isOpen.mem_nhds hx)).differentiableAt (by simp)
  have crθ i := along_commute ((hBi i).contDiffAt (G.isOpen.mem_nhds hx))
    dVr dVθ (G.radial_angular x hx)
  have crz i := along_commute ((hBi i).contDiffAt (G.isOpen.mem_nhds hx))
    dVr dVz (G.radial_axial x hx)
  have cθz i := along_commute ((hBi i).contDiffAt (G.isOpen.mem_nhds hx))
    dVθ dVz (G.angular_axial x hx)
  have hir : HarmonicCalculus.along Vr (fun y => (R y)⁻¹) x = -((R x)⁻¹) ^ 2 := by
    rw [along_inv Vr dR (G.radius_ne x hx), G.radial_radius x hx]
    simp
  have hiz : HarmonicCalculus.along Vz (fun y => (R y)⁻¹) x = 0 := by
    rw [along_inv Vz dR (G.radius_ne x hx), G.axial_radius x hx, mul_zero]
  simp only [HarmonicCalculus.cylindricalDivergence, cylindricalCurl,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons,
        Matrix.tail_cons]
  rw [along_sub Vr (dinv.fun_smul (dθ 2)) (dz 1),
    along_sub Vθ (dz 0) (dr 2),
    along_sub Vz ((dr 1).fun_add (dinv.fun_smul (db 1))) (dinv.fun_smul (dθ 0)),
    HarmonicCalculus.along_add Vz (dr 1) (dinv.fun_smul (db 1)),
    along_real_smul Vr dinv (dθ 2), along_real_smul Vz dinv (db 1),
    along_real_smul Vz dinv (dθ 0), hir, hiz, crθ 2, crz 1, cθz 0]
  simp only [zero_smul, zero_add, Complex.real_smul, Complex.ofReal_neg, Complex.ofReal_pow]
  ring

end Divergence

section ExplicitGraph

variable {A : Type*} [NormedAddCommGroup A] [NormedSpace ℝ A]

/-- Radial field, given by `(1, K x.1 • v)`. -/
noncomputable def radialField (K : ℝ → ℝ) (v : A) (x : ℝ × A) : ℝ × A :=
  (1, K x.1 • v)

theorem radialField_aux_derivative {K : ℝ → ℝ} (v w : A) {x : ℝ × A}
    (hK : DifferentiableAt ℝ K x.1) : fderiv ℝ (radialField K v) x (0, w) = 0 := by
  have hd := (hasFDerivAt_const (1 : ℝ) x).prodMk
    ((hK.hasFDerivAt.comp x hasFDerivAt_fst).smul_const v)
  dsimp only [Function.comp_def] at hd
  change fderiv ℝ (fun y : ℝ × A => (1, K y.1 • v)) x (0, w) = 0
  rw [hd.fderiv]
  simp

/-- Concrete graph directions commute because their radial coefficient only
depends on the radius. No operator commutation is assumed in this constructor. -/
theorem explicitGraph_geometry {U : Set (ℝ × A)} (hU : IsOpen U)
    {K : ℝ → ℝ} (v θ z : A)
    (hK : ∀ x ∈ U, ContDiffAt ℝ ∞ K x.1) (hR : ∀ x ∈ U, x.1 ≠ 0) :
    CylindricalGeometry U Prod.fst (radialField K v)
      (fun _ => (0, θ)) (fun _ => (0, z)) := by
  refine ⟨hU, contDiffOn_fst, hR, ?_, contDiffOn_const, contDiffOn_const,
    ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro x hx
    exact (contDiffAt_const.prodMk (((hK x hx).comp x contDiffAt_fst).smul
      contDiffAt_const)).contDiffWithinAt
  · intro x hx
    change fderiv ℝ (ContinuousLinearMap.fst ℝ ℝ A) x (1, K x.1 • v) = 1
    rw [ContinuousLinearMap.fderiv]
    rfl
  · intro x hx
    change fderiv ℝ (ContinuousLinearMap.fst ℝ ℝ A) x (0, θ) = 0
    rw [ContinuousLinearMap.fderiv]
    rfl
  · intro x hx
    change fderiv ℝ (ContinuousLinearMap.fst ℝ ℝ A) x (0, z) = 0
    rw [ContinuousLinearMap.fderiv]
    rfl
  · intro x hx
    rw [radialField_aux_derivative v θ ((hK x hx).differentiableAt (by simp))]
    simp
  · intro x hx
    rw [radialField_aux_derivative v z ((hK x hx).differentiableAt (by simp))]
    simp
  · intro x hx
    simp

end ExplicitGraph

section Realization

variable {D : Type*} [NormedAddCommGroup D] [NormedSpace ℝ D]

theorem phaseNormal_contDiffOn {U : Set D} {R : D → ℝ} {Vr Vθ Vz : D → D}
    (G : CylindricalGeometry U R Vr Vθ Vz) {Φ : D → ℝ} (hΦ : ContDiffOn ℝ ∞ Φ U) :
    ContDiffOn ℝ ∞ (HarmonicCalculus.phaseNormal R Vr Vθ Vz Φ) U := by
  apply (contDiffOn_piLp 2).mpr
  intro i
  fin_cases i
  · exact HarmonicCalculus.contDiffOn_along G.isOpen G.radial_smooth hΦ
  · exact (HarmonicCalculus.contDiffOn_along G.isOpen G.angular_smooth hΦ).div
      G.radius_smooth G.radius_ne
  · exact HarmonicCalculus.contDiffOn_along G.isOpen G.axial_smooth hΦ

theorem normalCoefficient_contDiffOn {U : Set D} {N : D → RealVector} {a : D → ComplexVector}
    (hN : ContDiffOn ℝ ∞ N U) (ha : ContDiffOn ℝ ∞ a U) (hne : ∀ x ∈ U, N x ≠ 0) :
    ContDiffOn ℝ ∞ (fun x => normalCoefficient (N x) (a x)) U := by
  have hnorm := (contDiff_norm_sq ℝ).comp_contDiffOn hN
  exact (hnorm.inv (fun x hx => pow_ne_zero 2 (norm_ne_zero_iff.mpr (hne x hx)))).smul
    (((hN.continuousLinearMap_comp complexify).continuousLinearMap_comp
        complexCrossLinear).clm_apply ha)

/-- Coefficient, given by `normalCoefficient (HarmonicCalculus.phaseNormal R Vr Vθ Vz Φ x) (a
x)`. -/
noncomputable def coefficient (R : D → ℝ) (Vr Vθ Vz : D → D)
    (Φ : D → ℝ) (a : D → ComplexVector) (x : D) : ComplexVector :=
  normalCoefficient (HarmonicCalculus.phaseNormal R Vr Vθ Vz Φ x) (a x)

/-- Inverse carrier, given by `Complex.I / (K : ℂ)`. -/
noncomputable def inverseCarrier (K : ℝ) : ℂ := Complex.I / (K : ℂ)

theorem inverseCarrier_phaseFactor {K : ℝ} (hK : K ≠ 0) :
    inverseCarrier K * HarmonicCalculus.phaseFactor K = -1 := by
  have hk : (K : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hK
  unfold inverseCarrier HarmonicCalculus.phaseFactor
  calc
    Complex.I / (K : ℂ) * ((K : ℂ) * Complex.I) = Complex.I * Complex.I := by
      field_simp
    _ = -1 := Complex.I_mul_I

theorem curlRemainder_eq (K : ℝ) (R : D → ℝ) (Vr Vθ Vz : D → D)
    (B : D → ComplexVector) (x : D) :
    curlRemainder K R Vr Vθ Vz B x = inverseCarrier K • cylindricalCurl R Vr Vθ Vz B x := by
  ext i
  simp [curlRemainder, inverseCarrier, Complex.real_smul, div_eq_mul_inv,
    mul_comm, mul_left_comm, mul_assoc]

/-- Vector potential, given by `HarmonicCalculus.vectorMode K Φ (fun x => inverseCarrier K •
coefficient R Vr Vθ Vz Φ a x)`. -/
noncomputable def vectorPotential (K : ℝ) (R : D → ℝ) (Vr Vθ Vz : D → D)
    (Φ : D → ℝ) (a : D → ComplexVector) : D → ComplexVector :=
  HarmonicCalculus.vectorMode K Φ (fun x => inverseCarrier K • coefficient R Vr Vθ Vz Φ a x)

/-- Realized coefficient, given by `a x + curlRemainder K R Vr Vθ Vz (coefficient R Vr Vθ Vz Φ
a) x`. -/
noncomputable def realizedCoefficient (K : ℝ) (R : D → ℝ) (Vr Vθ Vz : D → D)
    (Φ : D → ℝ) (a : D → ComplexVector) (x : D) : ComplexVector :=
  a x + curlRemainder K R Vr Vθ Vz (coefficient R Vr Vθ Vz Φ a) x

theorem vectorPotential_contDiffOn {U : Set D} {R : D → ℝ} {Vr Vθ Vz : D → D}
    (G : CylindricalGeometry U R Vr Vθ Vz) (K : ℝ) {Φ : D → ℝ} {a : D → ComplexVector}
    (hΦ : ContDiffOn ℝ ∞ Φ U) (ha : ContDiffOn ℝ ∞ a U)
    (hn : ∀ x ∈ U, HarmonicCalculus.phaseNormal R Vr Vθ Vz Φ x ≠ 0) :
    ContDiffOn ℝ ∞ (vectorPotential K R Vr Vθ Vz Φ a) U := by
  have hB := normalCoefficient_contDiffOn (phaseNormal_contDiffOn G hΦ) ha hn
  apply contDiffOn_pi.mpr
  intro i
  exact HarmonicCalculus.contDiffOn_mode K hΦ
    ((contDiffOn_pi.mp hB i).const_smul (inverseCarrier K))

/-- Formula (30): the actual curl of the vector potential equals the tangent
harmonic plus exactly the displayed coefficient-derivative remainder. -/
theorem cylindricalCurl_vectorPotential {U : Set D} {R : D → ℝ} {Vr Vθ Vz : D → D}
    (G : CylindricalGeometry U R Vr Vθ Vz) {K : ℝ} (hK : K ≠ 0)
    {Φ : D → ℝ} {a : D → ComplexVector} (hΦ : ContDiffOn ℝ ∞ Φ U) (ha : ContDiffOn ℝ ∞ a U)
    (hn : ∀ x ∈ U, HarmonicCalculus.phaseNormal R Vr Vθ Vz Φ x ≠ 0)
    (ht : ∀ x ∈ U, HarmonicCalculus.normalDot (HarmonicCalculus.phaseNormal R Vr Vθ Vz Φ x) (a x) =
        0)
    {x : D} (hx : x ∈ U) :
    cylindricalCurl R Vr Vθ Vz (vectorPotential K R Vr Vθ Vz Φ a) x =
      HarmonicCalculus.vectorMode K Φ (realizedCoefficient K R Vr Vθ Vz Φ a) x := by
  have hB : ContDiffOn ℝ ∞ (coefficient R Vr Vθ Vz Φ a) U :=
    normalCoefficient_contDiffOn (phaseNormal_contDiffOn G hΦ) ha hn
  have db i := ((contDiffOn_pi.mp hB i).contDiffAt (G.isOpen.mem_nhds hx)).differentiableAt (by
      simp)
  have dΦ := (hΦ.contDiffAt (G.isOpen.mem_nhds hx)).differentiableAt (by simp)
  have hcross := normalCross_normalCoefficient (hn x hx) (ht x hx)
  rw [vectorPotential, cylindricalCurl_vectorMode R Vr Vθ Vz K
    (B := fun y => inverseCarrier K • coefficient R Vr Vθ Vz Φ a y) dΦ
    (fun i => (db i).const_smul (inverseCarrier K)),
    cylindricalCurl_const_smul R Vr Vθ Vz (inverseCarrier K) db,
    normalCross_smul]
  change (fun i => ((inverseCarrier K • cylindricalCurl R Vr Vθ Vz (coefficient R Vr Vθ Vz Φ a) x)
      i +
      HarmonicCalculus.phaseFactor K * (inverseCarrier K •
        normalCross (HarmonicCalculus.phaseNormal R Vr Vθ Vz Φ x)
          (normalCoefficient (HarmonicCalculus.phaseNormal R Vr Vθ Vz Φ x) (a x))) i) *
        HarmonicCalculus.carrier K Φ x) = _
  rw [hcross]
  ext i
  simp only [Pi.smul_apply, Pi.neg_apply, smul_eq_mul, HarmonicCalculus.vectorMode,
    HarmonicCalculus.mode, realizedCoefficient, Pi.add_apply, curlRemainder_eq]
  have hc : HarmonicCalculus.phaseFactor K * inverseCarrier K = -1 := by
    rw [mul_comm, inverseCarrier_phaseFactor hK]
  calc
    _ = (inverseCarrier K * cylindricalCurl R Vr Vθ Vz (coefficient R Vr Vθ Vz Φ a) x i -
        (HarmonicCalculus.phaseFactor K * inverseCarrier K) * a x i) *
          HarmonicCalculus.carrier K Φ x := by ring
    _ = _ := by rw [hc]; ring

theorem cylindricalDivergence_congr {U : Set D} (hU : IsOpen U) (R : D → ℝ) (Vr Vθ Vz : D → D)
    {a b : D → ComplexVector} (hab : EqOn a b U) {x : D} (hx : x ∈ U) :
    HarmonicCalculus.cylindricalDivergence R Vr Vθ Vz a x =
      HarmonicCalculus.cylindricalDivergence R Vr Vθ Vz b x := by
  have hcomp i : EqOn (fun y => a y i) (fun y => b y i) U :=
    fun y hy => congrFun (hab hy) i
  unfold HarmonicCalculus.cylindricalDivergence
  rw [HarmonicCalculus.along_congr hU (hcomp 0) hx,
    HarmonicCalculus.along_congr hU (hcomp 1) hx,
    HarmonicCalculus.along_congr hU (hcomp 2) hx, hab hx]

theorem realizedCoefficient_divergence {U : Set D} {R : D → ℝ} {Vr Vθ Vz : D → D}
    (G : CylindricalGeometry U R Vr Vθ Vz) {K : ℝ} (hK : K ≠ 0)
    {Φ : D → ℝ} {a : D → ComplexVector} (hΦ : ContDiffOn ℝ ∞ Φ U) (ha : ContDiffOn ℝ ∞ a U)
    (hn : ∀ x ∈ U, HarmonicCalculus.phaseNormal R Vr Vθ Vz Φ x ≠ 0)
    (ht : ∀ x ∈ U, HarmonicCalculus.normalDot (HarmonicCalculus.phaseNormal R Vr Vθ Vz Φ x) (a x) =
        0)
    {x : D} (hx : x ∈ U) :
    HarmonicCalculus.cylindricalDivergence R Vr Vθ Vz
      (HarmonicCalculus.vectorMode K Φ (realizedCoefficient K R Vr Vθ Vz Φ a)) x = 0 := by
  rw [cylindricalDivergence_congr G.isOpen R Vr Vθ Vz
    (fun y hy => (cylindricalCurl_vectorPotential G hK hΦ ha hn ht hy).symm) hx]
  exact divergence_curl_zero G (vectorPotential_contDiffOn G K hΦ ha hn) hx

end Realization

section Longitudinal

variable {D : Type*} [NormedAddCommGroup D] [NormedSpace ℝ D]

/-- Solving the actual harmonic divergence identity gives the same inverse
carrier as in the curl remainder. This equality includes normal derivatives
when differentiated; there is no pointwise-only estimate here. -/
theorem longitudinal_eq_inverseCarrier (R : D → ℝ) (Vr Vθ Vz : D → D)
    {K : ℝ} (hK : K ≠ 0) {Φ : D → ℝ} {a : D → ComplexVector} {x : D}
    (hΦ : DifferentiableAt ℝ Φ x) (ha : ∀ i, DifferentiableAt ℝ (fun y => a y i) x)
    (hθ : HarmonicCalculus.along Vθ (fun y => a y 1) x = 0)
    (hdiv : HarmonicCalculus.cylindricalDivergence R Vr Vθ Vz
      (HarmonicCalculus.vectorMode K Φ a) x = 0) :
    HarmonicCalculus.normalDot (HarmonicCalculus.phaseNormal R Vr Vθ Vz Φ x) (a x) =
      inverseCarrier K * HarmonicCalculus.strippedDivergence R Vr Vz a x := by
  have h := congrArg (fun z : ℂ => inverseCarrier K * z)
    (HarmonicCalculus.longitudinal_identity R Vr Vθ Vz K hΦ ha hθ hdiv)
  rw [← mul_assoc, inverseCarrier_phaseFactor hK] at h
  simpa only [neg_one_mul, mul_neg, neg_inj] using h

variable {s : StripData D} {w : ℕ → D → ℝ} {α κ : ℝ}
  {R : D → ℝ} {Vr Vθ Vz : ℕ → D → D} {K : ℕ → ℝ}
  {Φ : ℕ → D → ℝ} {a : ℕ → D → ComplexVector}

/-- Actual all-order longitudinal contraction bounds from harmonic
solenoidality and primitive coefficient/direction classes. -/
theorem longitudinal_class (ha : MemClass s w α a) (hκ : 0 ≤ κ)
    (hr : UnweightedClass s (-κ) Vr) (hz : UnweightedClass s 1 Vz)
    (hR : UnweightedClass s 0 (fun _ x => (R x)⁻¹))
    (hK : ∀ n, K n ≠ 0) (hfreq : BandBound s (1 / 2) (fun n => 1 / K n))
    (hΦ : ∀ n, DifferentiableOn ℝ (Φ n) s.domain)
    (hθ : ∀ n x, x ∈ s.domain → HarmonicCalculus.along (Vθ n) (fun y => a n y 1) x = 0)
    (hdiv : ∀ n x, x ∈ s.domain → HarmonicCalculus.cylindricalDivergence R
      (Vr n) (Vθ n) (Vz n) (HarmonicCalculus.vectorMode (K n) (Φ n) (a n)) x = 0) :
    MemClass s w (α + 1 / 2 - κ) (fun n x => HarmonicCalculus.normalDot
      (HarmonicCalculus.phaseNormal R (Vr n) (Vθ n) (Vz n) (Φ n) x) (a n x)) := by
  have hS := strippedDivergence_class ha hκ hr hz hR
  have hI := (hS.map (Complex.I • ContinuousLinearMap.id ℝ ℂ)).band_smul hfreq
  have he : α - κ + 1 / 2 = α + 1 / 2 - κ := by ring
  rw [he] at hI
  apply class_congr hI
  intro n x hx
  dsimp only
  rw [longitudinal_eq_inverseCarrier R (Vr n) (Vθ n) (Vz n) (hK n)
    ((hΦ n x hx).differentiableAt (s.isOpen_domain.mem_nhds hx))
    (fun i => ((class_component ha i).contDiffAt n hx 1).differentiableAt (by norm_num))
    (hθ n x hx) (hdiv n x hx)]
  simp [inverseCarrier, Complex.real_smul, div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc]

/-- The divergence premise is discharged by a genuine smooth vector
potential. Equality is required on the open strip so all derivatives transfer. -/
theorem longitudinal_from_curl_class (ha : MemClass s w α a) (hκ : 0 ≤ κ)
    (hr : UnweightedClass s (-κ) Vr) (hz : UnweightedClass s 1 Vz)
    (hR : UnweightedClass s 0 (fun _ x => (R x)⁻¹))
    (hK : ∀ n, K n ≠ 0) (hfreq : BandBound s (1 / 2) (fun n => 1 / K n))
    (hΦ : ∀ n, DifferentiableOn ℝ (Φ n) s.domain)
    (hθ : ∀ n x, x ∈ s.domain → HarmonicCalculus.along (Vθ n) (fun y => a n y 1) x = 0)
    (G : ∀ n, CylindricalGeometry s.domain R (Vr n) (Vθ n) (Vz n))
    (A : ℕ → D → ComplexVector) (hA : ∀ n, ContDiffOn ℝ ∞ (A n) s.domain)
    (hreal : ∀ n, EqOn (HarmonicCalculus.vectorMode (K n) (Φ n) (a n))
      (cylindricalCurl R (Vr n) (Vθ n) (Vz n) (A n)) s.domain) :
    MemClass s w (α + 1 / 2 - κ) (fun n x => HarmonicCalculus.normalDot
      (HarmonicCalculus.phaseNormal R (Vr n) (Vθ n) (Vz n) (Φ n) x) (a n x)) := by
  apply longitudinal_class ha hκ hr hz hR hK hfreq hΦ hθ
  intro n x hx
  rw [cylindricalDivergence_congr s.isOpen_domain R (Vr n) (Vθ n) (Vz n) (hreal n) hx]
  exact divergence_curl_zero (G n) (hA n) hx

end Longitudinal

section WaveClasses

variable {D : Type*} [NormedAddCommGroup D] [NormedSpace ℝ D]
  {s : StripData D} {P : ℕ → D → ℝ} {α κ : ℝ}
  {R : D → ℝ} {Vr Vθ Vz : ℕ → D → D} {K : ℕ → ℝ}
  {Φ : ℕ → D → ℝ} {a : ℕ → D → ComplexVector}

/-- Lemma 9.2's curl remainder, with the original wave weight unchanged. -/
theorem curlRemainder_waveClass
    (hN : PhaseJetBounds.PolynomialJets (phaseDomain s)
      (fun n => HarmonicCalculus.phaseNormal R (Vr n) (Vθ n) (Vz n) (Φ n)))
    (ha : WaveClass s P α a) {b M : ℝ} (hb : 0 < b)
    (hlower : ∀ n x, x ∈ s.domain → b ≤ ‖HarmonicCalculus.phaseNormal R (Vr n) (Vθ n) (Vz n) (Φ n)
        x‖)
    (hupper : ∀ n x, x ∈ s.domain → ‖HarmonicCalculus.phaseNormal R (Vr n) (Vθ n) (Vz n) (Φ n) x‖ ≤
        M)
    (hκ : 0 ≤ κ) (hr : UnweightedClass s (-κ) Vr) (hθ : UnweightedClass s 0 Vθ)
    (hz : UnweightedClass s 1 Vz) (hR : UnweightedClass s 0 (fun _ x => (R x)⁻¹))
    (hK : BandBound s (1 / 2) (fun n => 1 / K n)) :
    WaveClass s P (α + 1 / 2 - κ) (fun n =>
      curlRemainder (K n) R (Vr n) (Vθ n) (Vz n)
        (coefficient R (Vr n) (Vθ n) (Vz n) (Φ n) (a n))) :=
  normalCurlRemainder_class hN ha hb hlower hupper hκ hr hθ hz hR hK

theorem realizedCoefficient_waveClass
    (hN : PhaseJetBounds.PolynomialJets (phaseDomain s)
      (fun n => HarmonicCalculus.phaseNormal R (Vr n) (Vθ n) (Vz n) (Φ n)))
    (ha : WaveClass s P α a) {b M : ℝ} (hb : 0 < b)
    (hlower : ∀ n x, x ∈ s.domain → b ≤ ‖HarmonicCalculus.phaseNormal R (Vr n) (Vθ n) (Vz n) (Φ n)
        x‖)
    (hupper : ∀ n x, x ∈ s.domain → ‖HarmonicCalculus.phaseNormal R (Vr n) (Vθ n) (Vz n) (Φ n) x‖ ≤
        M)
    (hκ : 0 ≤ κ) (hκhalf : κ ≤ 1 / 2)
    (hr : UnweightedClass s (-κ) Vr) (hθ : UnweightedClass s 0 Vθ)
    (hz : UnweightedClass s 1 Vz) (hR : UnweightedClass s 0 (fun _ x => (R x)⁻¹))
    (hK : BandBound s (1 / 2) (fun n => 1 / K n)) :
    WaveClass s P α (fun n => realizedCoefficient (K n) R (Vr n) (Vθ n) (Vz n) (Φ n) (a n)) := by
  have hrem := curlRemainder_waveClass hN ha hb hlower hupper hκ hr hθ hz hR hK
  exact ha.add (hrem.mono_exponent (by linarith))

end WaveClasses

section Support

variable {D : Type*} [NormedAddCommGroup D] [NormedSpace ℝ D]

theorem coefficient_tsupport_subset (R : D → ℝ) (Vr Vθ Vz : D → D)
    (Φ : D → ℝ) (a : D → ComplexVector) :
    tsupport (coefficient R Vr Vθ Vz Φ a) ⊆ tsupport a := by
  apply closure_mono
  intro x hx ha
  apply hx
  simp [coefficient, normalCoefficient, normalCross, ha]

theorem cylindricalCurl_tsupport_subset (R : D → ℝ) (Vr Vθ Vz : D → D)
    (B : D → ComplexVector) : tsupport (cylindricalCurl R Vr Vθ Vz B) ⊆ tsupport B := by
  apply closure_minimal _ isClosed_closure
  intro x hx
  by_contra hn
  have he : B =ᶠ[𝓝 x] fun _ => 0 := notMem_tsupport_iff_eventuallyEq.mp hn
  have hval : B x = 0 := he.eq_of_nhds
  have hderiv (i : Fin 3) : fderiv ℝ (fun y => B y i) x = 0 := by
    have hei : (fun y => B y i) =ᶠ[𝓝 x] fun _ => 0 := by
      filter_upwards [he] with y hy
      exact congrFun hy i
    rw [hei.fderiv_eq]
    simp
  apply hx
  ext i
  fin_cases i <;> simp [cylindricalCurl, HarmonicCalculus.along, hderiv, hval]

theorem vectorPotential_tsupport_subset (K : ℝ) (R : D → ℝ) (Vr Vθ Vz : D → D)
    (Φ : D → ℝ) (a : D → ComplexVector) :
    tsupport (vectorPotential K R Vr Vθ Vz Φ a) ⊆ tsupport a := by
  apply closure_mono
  intro x hx ha
  apply hx
  ext i
  simp [vectorPotential, HarmonicCalculus.vectorMode, HarmonicCalculus.mode,
    coefficient, normalCoefficient, normalCross, ha]

theorem realizedWave_tsupport_subset (K : ℝ) (R : D → ℝ) (Vr Vθ Vz : D → D)
    (Φ : D → ℝ) (a : D → ComplexVector) :
    tsupport (cylindricalCurl R Vr Vθ Vz (vectorPotential K R Vr Vθ Vz Φ a)) ⊆ tsupport a :=
  (cylindricalCurl_tsupport_subset R Vr Vθ Vz _).trans
    (vectorPotential_tsupport_subset K R Vr Vθ Vz Φ a)

end Support

section PhysicalCurl

open ProblemStatement

variable {s : StripData SpaceTime} {w : ℕ → SpaceTime → ℝ} {α : ℝ}
  {B : ℕ → VelocityField} {K : ℕ → ℝ}

/-- Direct compatibility with the actual Euclidean spatial curl. All input
jets here are physical spacetime jets, so no separate graph factor occurs. -/
theorem physicalCurl_class (hB : MemClass s w α B) :
    MemClass s w α (fun n => SpatialCurl.spatialCurl (B n)) := by
  apply class_congr (hB.fderiv.map
    (SpatialCurl.curlLinear.comp (ResidualStability.spaceRestriction Space)))
  intro n x hx
  change SpatialCurl.curlLinear (ResidualStability.spaceRestriction Space (fderiv ℝ (B n) x)) =
    SpatialCurl.curlLinear (fderiv ℝ (fun y => B n (x.1, y)) x.2)
  rw [ResidualStability.space_fderiv_eq_full ((hB.contDiffAt n hx 1).differentiableAt (by
      norm_num))]

theorem physical_strippedRemainder_class (hB : MemClass s w α B)
    (hK : BandBound s (1 / 2) (fun n => 1 / K n)) :
    MemClass s w (α + 1 / 2) (fun n => OscillatoryCurl.strippedRemainder (K n) (B n)) :=
  (physicalCurl_class hB).band_smul hK

theorem physical_normalCoefficient_class {N a : ℕ → VelocityField}
    (hN : PhaseJetBounds.PolynomialJets (phaseDomain s) N) (ha : MemClass s w α a)
    {b M : ℝ} (hb : 0 < b)
    (hlower : ∀ n x, x ∈ s.domain → b ≤ ‖N n x‖)
    (hupper : ∀ n x, x ∈ s.domain → ‖N n x‖ ≤ M) :
    MemClass s w α (fun n x => OscillatoryCurl.normalCoefficient (N n x) (a n x)) := by
  have hcross : MemClass s w α (fun n x => OscillatoryCurl.cross (N n x) (a n x)) := by
    simpa only [one_mul, zero_add, OscillatoryCurl.cross] using
      (polynomialJets_unweighted hN).bilinear ha OscillatoryCurl.crossLinear
  simpa only [zero_add, OscillatoryCurl.normalCoefficient] using
    class_mul_real (normalInverse_unweighted hN hb hlower hupper) hcross

/-- The remainder in the existing physical exact-curl theorem belongs to the
claimed class once its actual normal and amplitude jets are supplied. -/
theorem physical_actualRemainder_class {Φ : ℕ → PressureField} {a : ℕ → VelocityField}
    (hN : PhaseJetBounds.PolynomialJets (phaseDomain s) (fun n => OscillatoryCurl.phaseNormal (Φ
        n)))
    (ha : MemClass s w α a) {b M : ℝ} (hb : 0 < b)
    (hlower : ∀ n x, x ∈ s.domain → b ≤ ‖OscillatoryCurl.phaseNormal (Φ n) x‖)
    (hupper : ∀ n x, x ∈ s.domain → ‖OscillatoryCurl.phaseNormal (Φ n) x‖ ≤ M)
    (hK : BandBound s (1 / 2) (fun n => 1 / K n)) :
    MemClass s w (α + 1 / 2) (fun n =>
      OscillatoryCurl.strippedRemainder (K n) (OscillatoryCurl.coefficient (Φ n) (a n))) :=
  physical_strippedRemainder_class (physical_normalCoefficient_class hN ha hb hlower hupper) hK

end PhysicalCurl

end NavierStokes.CurlClassBounds
