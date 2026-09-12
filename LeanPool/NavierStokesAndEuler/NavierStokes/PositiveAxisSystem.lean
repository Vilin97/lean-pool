/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.NavierStokes.SlowDivergence
public import LeanPool.NavierStokesAndEuler.NavierStokes.VolterraParity
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.Complex.RealDeriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-!
# Explicit positive-order axis matrices

The matrices are obtained by splitting the positive-order convolutions into
their two endpoint terms and their strictly lower-order source. No matrix
identity or existence of a transformed system is assumed.
-/

@[expose] public section


noncomputable section

open Set
open scoped BigOperators ContDiff

namespace NavierStokes.PositiveAxisSystem

/-- Jet data, collecting `value`, `radial`, `radial2`, `parameter`. -/
structure Jet (K : Type*) where
  /-- Value of `Jet`, of type `K`. -/
  value : K
  /-- Radial of `Jet`, of type `K`. -/
  radial : K
  /-- Radial2 of `Jet`, of type `K`. -/
  radial2 : K
  /-- Parameter of `Jet`, of type `K`. -/
  parameter : K

/-- Base jet data, collecting `phi`, `axial`, `beta`. -/
structure BaseJet (K : Type*) where
  /-- Phi of `BaseJet`, of type `Jet K`. -/
  phi : Jet K
  /-- Axial of `BaseJet`, of type `Jet K`. -/
  axial : Jet K
  /-- Beta of `BaseJet`, of type `K`. -/
  beta : K

/-- The first two entries are the lower-order convective sums minus the
known preceding axial diffusion. The last two give the lower pressure
convolution and the smooth quotient `Ω_(n-1)/X`. -/
structure SourceJet (K : Type*) where
  /-- Angular of `SourceJet`, of type `K`. -/
  angular : K
  /-- Axial of `SourceJet`, of type `K`. -/
  axial : K
  /-- Pressure product of `SourceJet`, of type `K`. -/
  pressureProduct : K
  /-- Omega quotient of `SourceJet`, of type `K`. -/
  omegaQuotient : K

section Algebra

variable {K : Type*} [Field K] [CharZero K]

/-- A, given by `1 / 2 + h`. -/
noncomputable def a (h : K) : K := 1 / 2 + h
/-- D scale, given by `1 / 2 - h`. -/
noncomputable def dScale (h : K) : K := 1 / 2 - h
/-- Edge, given by `1 - eta ^ 2`. -/
noncomputable def edge (eta : K) : K := 1 - eta ^ 2
/-- Ell, given by `1 - 2 * h * eta ^ 2`. -/
noncomputable def ell (h eta : K) : K := 1 - 2 * h * eta ^ 2
/-- Angular power, given by `-a h - 1 / 2`. -/
noncomputable def angularPower (h : K) : K := -a h - 1 / 2
/-- Axial power, given by `-a h`. -/
noncomputable def axialPower (h : K) : K := -a h
/-- Inverse square, given by `(C ^ 2)⁻¹`. -/
noncomputable def inverseSquare (C : K) : K := (C ^ 2)⁻¹

/-- Time value, given by `(-power * j.value + dScale h * eta * j.parameter + X * j.radial) / ell
h eta`. -/
noncomputable def timeValue (h power eta X : K) (j : Jet K) : K :=
  (-power * j.value + dScale h * eta * j.parameter + X * j.radial) / ell h eta

/-- Axial value, given by `(2 * eta * power * j.value + edge eta * j.parameter - 2 * eta * X *
j.radial) / ell h eta`. -/
noncomputable def axialValue (h power eta X : K) (j : Jet K) : K :=
  (2 * eta * power * j.value + edge eta * j.parameter - 2 * eta * X * j.radial) / ell h eta

/-- The quotient `V_n/X` obtained from (21) with `Ubar_n=U_n+K_n`. -/
noncomputable def betaValue (h lam eta : K) (u k : Jet K) : K :=
  (2 * eta * (a h - lam) * u.value - 2 * eta * (dScale h + lam) * k.value -
    edge eta * (u.parameter + k.parameter)) / ell h eta

/-- Pressure source, given by `inverseSquare C * s.pressureProduct - s.omegaQuotient / 2`. -/
noncomputable def pressureSource (C : K) (s : SourceJet K) : K :=
  inverseSquare C * s.pressureProduct - s.omegaQuotient / 2

/-- Pressure value, given by `2 * inverseSquare C * b.phi.value * phi.value + pressureSource C
s`. -/
noncomputable def pressureValue (C : K) (b : BaseJet K) (s : SourceJet K) (phi : Jet K) : K :=
  2 * inverseSquare C * b.phi.value * phi.value + pressureSource C s

/-- Angular RHS, constructed using `timeValue`. -/
noncomputable def angularRHS (h lam eta X : K) (b : BaseJet K) (s : SourceJet K)
    (phi u k : Jet K) : K :=
  timeValue h (angularPower h + lam) eta X phi +
  b.beta * (X * phi.radial + phi.value) +
  betaValue h lam eta u k * (X * b.phi.radial + b.phi.value) +
  b.axial.value * axialValue h (angularPower h + lam) eta X phi +
  u.value * axialValue h (angularPower h) eta X b.phi + s.angular

/-- Axial RHS, constructed using `timeValue`. -/
noncomputable def axialRHS (h lam eta X : K) (b : BaseJet K) (s : SourceJet K)
    (_phi u k p : Jet K) : K :=
  timeValue h (axialPower h + lam) eta X u + b.beta * X * u.radial +
  betaValue h lam eta u k * X * b.axial.radial +
  b.axial.value * axialValue h (axialPower h + lam) eta X u +
  u.value * axialValue h (axialPower h) eta X b.axial +
  axialValue h (-2 * a h + lam) eta X p + s.axial

/-- The four equations remaining after the first two components of W have
been defined as radial derivatives. These are the expanded (21)--(22). -/
def ExpandedEquations (h lam C eta X : K) (b : BaseJet K) (s : SourceJet K)
    (phi u k p : Jet K) : Prop :=
  X * (u.radial + k.radial) + k.value = 0 ∧
  p.radial = pressureValue C b s phi ∧
  2 * (X * phi.radial2 + 2 * phi.radial) = angularRHS h lam eta X b s phi u k ∧
  2 * (X * u.radial2 + u.radial) = axialRHS h lam eta X b s phi u k p

/-- Diagonal, given by `![0, 0, 2, 0, 3, 1]`. -/
noncomputable def diagonal : Fin 6 → K := ![0, 0, 2, 0, 3, 1]

/-- Jet vector, given by `![phi.value, u.value, k.value, p.value, 2 * r * phi.radial, 2 * r *
u.radial]`. -/
noncomputable def jetVector (r : K) (phi u k p : Jet K) : Fin 6 → K :=
  ![phi.value, u.value, k.value, p.value, 2 * r * phi.radial, 2 * r * u.radial]

/-- Radial jet vector as an element of `Fin 6 → K`. -/
noncomputable def radialJetVector (r : K) (phi u k p : Jet K) : Fin 6 → K :=
  ![2 * r * phi.radial, 2 * r * u.radial, 2 * r * k.radial, 2 * r * p.radial,
    2 * phi.radial + 4 * r ^ 2 * phi.radial2,
    2 * u.radial + 4 * r ^ 2 * u.radial2]

/-- Only the first four parameter derivatives enter the system. -/
noncomputable def parameterJetVector (phi u k p : Jet K) (q₄ q₅ : K) : Fin 6 → K :=
  ![phi.parameter, u.parameter, k.parameter, p.parameter, q₄, q₅]

/-- A0 as an element of `Matrix (Fin 6) (Fin 6) K`. -/
noncomputable def A0 (h lam C r eta : K) (b : BaseJet K) : Matrix (Fin 6) (Fin 6) K :=
  let M := 1 - 2 * eta * b.axial.value
  let R := M / ell h eta + b.beta
  let Gphi := r ^ 2 * b.phi.radial + b.phi.value
  let Gu := r ^ 2 * b.axial.radial
  !![0, 0, 0, 0, 1, 0;
     0, 0, 0, 0, 0, 1;
     0, 0, 0, 0, 0, -1;
     4 * r * inverseSquare C * b.phi.value, 0, 0, 0, 0, 0;
     2 * (b.beta - (angularPower h + lam) * M / ell h eta),
       2 * (axialValue h (angularPower h) eta (r ^ 2) b.phi +
         2 * eta * (a h - lam) * Gphi / ell h eta),
       -4 * eta * (dScale h + lam) * Gphi / ell h eta, 0, r * R, 0;
     -8 * eta * r ^ 2 * inverseSquare C * b.phi.value / ell h eta,
       2 * (-(axialPower h + lam) * M / ell h eta +
         axialValue h (axialPower h) eta (r ^ 2) b.axial +
         2 * eta * (a h - lam) * Gu / ell h eta),
       -4 * eta * (dScale h + lam) * Gu / ell h eta,
       4 * eta * (-2 * a h + lam) / ell h eta, 0, r * R]

/-- A1 as an element of `Matrix (Fin 6) (Fin 6) K`. -/
noncomputable def A1 (h r eta : K) (b : BaseJet K) : Matrix (Fin 6) (Fin 6) K :=
  let H := dScale h * eta + edge eta * b.axial.value
  let Gphi := r ^ 2 * b.phi.radial + b.phi.value
  let Gu := r ^ 2 * b.axial.radial
  !![0, 0, 0, 0, 0, 0;
     0, 0, 0, 0, 0, 0;
     0, 0, 0, 0, 0, 0;
     0, 0, 0, 0, 0, 0;
     2 * H / ell h eta, -2 * edge eta * Gphi / ell h eta,
       -2 * edge eta * Gphi / ell h eta, 0, 0, 0;
     0, 2 * (H - edge eta * Gu) / ell h eta,
       -2 * edge eta * Gu / ell h eta, 2 * edge eta / ell h eta, 0, 0]

/-- Forcing, given by `![0, 0, 0, 2 * r * pressureSource C s, 2 * s.angular, 2 * s.axial - 4 *
eta * r ^ 2 * pressureSource C s / ell h eta]`. -/
noncomputable def forcing (h C r eta : K) (s : SourceJet K) : Fin 6 → K :=
  ![0, 0, 0, 2 * r * pressureSource C s, 2 * s.angular,
    2 * s.axial - 4 * eta * r ^ 2 * pressureSource C s / ell h eta]

/-- Matrix RHS, given by `(A0 h lam C r eta b).mulVec w + (A1 h r eta b).mulVec v + forcing h C
r eta s`. -/
noncomputable def matrixRHS (h lam C r eta : K) (b : BaseJet K) (s : SourceJet K)
    (w v : Fin 6 → K) : Fin 6 → K :=
  (A0 h lam C r eta b).mulVec w + (A1 h r eta b).mulVec v + forcing h C r eta s

/-- Jet system as an element of `Prop`. -/
def JetSystem (h lam C r eta : K) (b : BaseJet K) (s : SourceJet K)
    (phi u k p : Jet K) (q₄ q₅ : K) : Prop :=
  (fun i => radialJetVector r phi u k p i + diagonal i / r * jetVector r phi u k p i) =
    matrixRHS h lam C r eta b s (jetVector r phi u k p) (parameterJetVector phi u k p q₄ q₅)

omit [CharZero K] in
theorem A1_shape (h r eta : K) (b : BaseJet K) (i j : Fin 6)
    (hij : i.val < 4 ∨ 4 ≤ j.val) : A1 h r eta b i j = 0 := by
  rcases hij with hi | hj
  · have hi' : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 := by omega
    have hzero : (![0, 0, 0, 0, 0, 0] : Fin 6 → K) j = 0 := by fin_cases j <;> rfl
    rcases hi' with rfl | rfl | rfl | rfl <;> exact hzero
  · have hj' : j = 4 ∨ j = 5 := by omega
    rcases hj' with rfl | rfl <;> fin_cases i <;> rfl

omit [CharZero K] in
theorem A1_high_parameters_irrelevant (h r eta : K) (b : BaseJet K)
    (phi u k p : Jet K) (q₄ q₅ q₄' q₅' : K) :
    (A1 h r eta b).mulVec (parameterJetVector phi u k p q₄ q₅) =
      (A1 h r eta b).mulVec (parameterJetVector phi u k p q₄' q₅') := by
  ext i
  fin_cases i <;> simp [A1, parameterJetVector, Matrix.mulVec, dotProduct, Fin.sum_univ_succ]

/-- Direct multiplication of the displayed matrices reproduces the expanded
right sides, with the pressure radial derivative explicitly substituted. -/
theorem matrixRHS_jet (h lam C r eta : K) (b : BaseJet K) (s : SourceJet K)
    (phi u k p : Jet K) (q₄ q₅ : K) :
    matrixRHS h lam C r eta b s (jetVector r phi u k p) (parameterJetVector phi u k p q₄ q₅) =
      ![2 * r * phi.radial, 2 * r * u.radial, -2 * r * u.radial,
        2 * r * pressureValue C b s phi,
        2 * angularRHS h lam eta (r ^ 2) b s phi u k,
        2 * axialRHS h lam eta (r ^ 2) b s phi u k {p with radial := pressureValue C b s phi}] := by
  ext i
  fin_cases i <;>
    simp only [matrixRHS, A0, A1, forcing, jetVector, parameterJetVector,
      pressureValue, pressureSource, angularRHS, axialRHS, timeValue, axialValue,
      betaValue, div_eq_mul_inv, Matrix.mulVec_cons, Matrix.mulVec_empty,
      Pi.add_apply, Pi.smul_apply, Function.comp_apply, Matrix.cons_val,
      Matrix.head_cons, Matrix.tail_cons, smul_eq_mul, Fin.reduceFinMk, Fin.isValue,
      Nat.succ_eq_add_one, Nat.reduceAdd, add_zero, zero_add, mul_zero,
      mul_one, neg_mul, mul_neg, neg_add_rev] <;> ring

private theorem average_row_iff {r : K} (hr : r ≠ 0) (ux kx kv : K) :
    2 * r * kx + 2 / r * kv = -(2 * r * ux) ↔ r ^ 2 * (ux + kx) + kv = 0 := by
  constructor
  · intro h
    field_simp [hr] at h
    linear_combination h
  · intro h
    field_simp [hr]
    linear_combination h

private theorem second_row_iff {r : K} (hr : r ≠ 0) (v vx rhs : K) (c : K) :
    2 * v + 4 * r ^ 2 * vx + c / r * (2 * r * v) = 2 * rhs ↔
      2 * (r ^ 2 * vx + ((c + 1) / 2) * v) = rhs := by
  have he : c / r * (2 * r * v) = 2 * c * v := by field_simp
  rw [he]
  constructor
  · intro h
    linear_combination (norm := ring_nf) (1 / 2 : K) * h
  · intro h
    linear_combination (norm := ring_nf) (2 : K) * h

/-- Equivalence with the expanded profile equations, including the average
row and the pressure-row substitution. Only the change of radial coordinate
requires `r≠0`; the matrices themselves are nonsingular at the axis. -/
theorem jetSystem_iff_expanded {h lam C r eta : K} (hr : r ≠ 0)
    (b : BaseJet K) (s : SourceJet K) (phi u k p : Jet K) (q₄ q₅ : K) :
    JetSystem h lam C r eta b s phi u k p q₄ q₅ ↔
      ExpandedEquations h lam C eta (r ^ 2) b s phi u k p := by
  unfold JetSystem
  rw [matrixRHS_jet]
  constructor
  · intro hh
    have h2 := congrFun hh 2
    have h3 := congrFun hh 3
    have h4 := congrFun hh 4
    have h5 := congrFun hh 5
    simp only [radialJetVector, Fin.isValue, Matrix.cons_val, diagonal, jetVector,
        Nat.succ_eq_add_one,
      Nat.reduceAdd, neg_mul, zero_div, zero_mul, add_zero, mul_eq_mul_left_iff, mul_eq_zero,
          OfNat.ofNat_ne_zero,
      false_or, one_div] at h2 h3 h4 h5
    have hk := (average_row_iff hr _ _ _).mp h2
    have hp : p.radial = pressureValue C b s phi := by
      exact h3.resolve_right hr
    have hphi := (second_row_iff hr phi.radial phi.radial2
      (angularRHS h lam eta (r ^ 2) b s phi u k) 3).mp h4
    have hu := (second_row_iff hr u.radial u.radial2
      (axialRHS h lam eta (r ^ 2) b s phi u k {p with radial := pressureValue C b s phi}) 1).mp (by
          simpa only [one_div] using h5)
    have hpjet : {p with radial := pressureValue C b s phi} = p := by
      cases p
      simp_all
    rw [hpjet] at hu
    refine ⟨hk, hp, ?_, ?_⟩
    · convert! hphi using 1; norm_num
    · convert! hu using 1; norm_num
  · rintro ⟨hk, hp, hphi, hu⟩
    have hpjet : {p with radial := pressureValue C b s phi} = p := by
      cases p
      simp_all
    ext i
    fin_cases i
    · simp [radialJetVector, diagonal, jetVector]
    · simp [radialJetVector, diagonal, jetVector]
    · simpa [radialJetVector, diagonal, jetVector] using (average_row_iff hr _ _ _).mpr hk
    · simp [radialJetVector, diagonal, jetVector, hp]
    · simpa [radialJetVector, diagonal, jetVector] using
        (second_row_iff hr phi.radial phi.radial2 (angularRHS h lam eta (r ^ 2) b s phi u k) 3).mpr
          (by convert! hphi using 1; norm_num)
    · rw [hpjet]
      simpa [radialJetVector, diagonal, jetVector] using
        (second_row_iff hr u.radial u.radial2 (axialRHS h lam eta (r ^ 2) b s phi u k p) 1).mpr
          (by convert! hu using 1; norm_num)


/-- Slow exponent at order `n`. -/
noncomputable def slowPower (h : K) (n : ℕ) : K := 2 * (n : K) * h

/-- The coefficient of a Cauchy product at the indicated order. -/
noncomputable def convolution (n : ℕ) (F : ℕ → ℕ → K) : K :=
  ∑ i ∈ Finset.range (n + 1), F i (n - i)

/-- Both indices in this sum are strictly below a positive order `n`. -/
noncomputable def lowerConvolution (n : ℕ) (F : ℕ → ℕ → K) : K :=
  ∑ i ∈ Finset.range (n - 1), F (i + 1) (n - (i + 1))

omit [CharZero K] in
theorem convolution_split {n : ℕ} (hn : 0 < n) (F : ℕ → ℕ → K) :
    convolution n F = F 0 n + F n 0 + lowerConvolution n F := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hn)
  unfold convolution lowerConvolution
  rw [Finset.sum_range_succ']
  simp only [Nat.succ_sub_one]
  rw [Finset.sum_range_succ]
  simp only [Nat.sub_self, Nat.sub_zero]
  ring

theorem lower_indices {n i : ℕ} (hi : i ∈ Finset.range (n - 1)) :
    0 < i + 1 ∧ i + 1 < n ∧ 0 < n - (i + 1) ∧ n - (i + 1) < n := by
  have := Finset.mem_range.mp hi
  omega

omit [CharZero K] in
theorem lowerConvolution_congr {n : ℕ} {F G : ℕ → ℕ → K}
    (h : ∀ i, i < n → ∀ j, j < n → F i j = G i j) :
    lowerConvolution n F = lowerConvolution n G := by
  apply Finset.sum_congr rfl
  intro i hi
  have hidx := lower_indices hi
  exact h _ hidx.2.1 _ hidx.2.2.2

/-- Angular convection, given by `beta i * (X * (phi j).radial + (phi j).value) + (u i).value *
axialValue h (angularPower h + slowPower h j) eta X (phi j)`. -/
noncomputable def angularConvection (h eta X : K) (phi u : ℕ → Jet K)
    (beta : ℕ → K) (i j : ℕ) : K :=
  beta i * (X * (phi j).radial + (phi j).value) +
    (u i).value * axialValue h (angularPower h + slowPower h j) eta X (phi j)

/-- Axial convection, given by `beta i * X * (u j).radial + (u i).value * axialValue h
(axialPower h + slowPower h j) eta X (u j)`. -/
noncomputable def axialConvection (h eta X : K) (u : ℕ → Jet K)
    (beta : ℕ → K) (i j : ℕ) : K :=
  beta i * X * (u j).radial +
    (u i).value * axialValue h (axialPower h + slowPower h j) eta X (u j)

/-- The known functions supplied here are exactly the previous-order axial
viscosities and the smooth extension of the previous radial residual divided
by `X`; no current-order unknown occurs in this source. -/
noncomputable def lowerSource (h eta X : K) (n : ℕ) (phi u : ℕ → Jet K)
    (beta : ℕ → K) (previousAngularDiffusion previousAxialDiffusion omegaQuotient : K) :
    SourceJet K where
  angular := lowerConvolution n (angularConvection h eta X phi u beta) - previousAngularDiffusion
  axial := lowerConvolution n (axialConvection h eta X u beta) - previousAxialDiffusion
  pressureProduct := lowerConvolution n (fun i j => (phi i).value * (phi j).value)
  omegaQuotient := omegaQuotient

/-- Base at order zero, given by `⟨phi 0, u 0, beta 0⟩`. -/
noncomputable def baseAtOrderZero (phi u : ℕ → Jet K) (beta : ℕ → K) : BaseJet K :=
  ⟨phi 0, u 0, beta 0⟩

/-- The beta formula is precisely (21), with `Ubar=U+K`. -/
theorem betaValue_eq_average_formula (h lam eta : K) (u k : Jet K) :
    betaValue h lam eta u k =
      (2 * eta * u.value - 2 * eta * (dScale h + lam) * (u.value + k.value) -
        edge eta * (u.parameter + k.parameter)) / ell h eta := by
  unfold betaValue a dScale
  congr 1
  ring

omit [CharZero K] in
/-- Replacing `V=X beta` in the angular convection is exact away from the axis. -/
theorem angularConvection_radial_term {X : K} (hX : X ≠ 0) (beta f fx : K) :
    beta * (X * fx + f) = (X * beta) * (fx + f / X) := by
  field_simp

omit [CharZero K] in
/-- Endpoint extraction, including the exact lower-order sums. -/
theorem angularRHS_eq_convolution (h eta X : K) {n : ℕ} (hn : 0 < n)
    (phi u : ℕ → Jet K) (beta : ℕ → K) (k : Jet K)
    (previousAngularDiffusion previousAxialDiffusion omegaQuotient : K)
    (hbeta : beta n = betaValue h (slowPower h n) eta (u n) k) :
    angularRHS h (slowPower h n) eta X (baseAtOrderZero phi u beta)
      (lowerSource h eta X n phi u beta previousAngularDiffusion previousAxialDiffusion
          omegaQuotient)
      (phi n) (u n) k =
    timeValue h (angularPower h + slowPower h n) eta X (phi n) +
      convolution n (angularConvection h eta X phi u beta) - previousAngularDiffusion := by
  rw [convolution_split hn]
  simp only [angularRHS, baseAtOrderZero, lowerSource, angularConvection, slowPower,
    Nat.cast_zero, mul_zero, zero_mul, add_zero, hbeta]
  ring

omit [CharZero K] in
theorem axialRHS_eq_convolution (h eta X : K) {n : ℕ} (hn : 0 < n)
    (phi u : ℕ → Jet K) (beta : ℕ → K) (k p : Jet K)
    (previousAngularDiffusion previousAxialDiffusion omegaQuotient : K)
    (hbeta : beta n = betaValue h (slowPower h n) eta (u n) k) :
    axialRHS h (slowPower h n) eta X (baseAtOrderZero phi u beta)
      (lowerSource h eta X n phi u beta previousAngularDiffusion previousAxialDiffusion
          omegaQuotient)
      (phi n) (u n) k p =
    timeValue h (axialPower h + slowPower h n) eta X (u n) +
      convolution n (axialConvection h eta X u beta) +
      axialValue h (-2 * a h + slowPower h n) eta X p - previousAxialDiffusion := by
  rw [convolution_split hn]
  simp only [axialRHS, baseAtOrderZero, lowerSource, axialConvection, slowPower,
    Nat.cast_zero, mul_zero, zero_mul, add_zero, hbeta]
  ring

theorem pressureValue_eq_convolution (h C eta X : K) {n : ℕ} (hn : 0 < n)
    (phi u : ℕ → Jet K) (beta : ℕ → K)
    (previousAngularDiffusion previousAxialDiffusion omegaQuotient : K) :
    pressureValue C (baseAtOrderZero phi u beta)
      (lowerSource h eta X n phi u beta previousAngularDiffusion previousAxialDiffusion
          omegaQuotient)
      (phi n) =
    inverseSquare C * convolution n (fun i j => (phi i).value * (phi j).value) - omegaQuotient / 2
        := by
  rw [convolution_split hn]
  simp only [pressureValue, pressureSource, baseAtOrderZero, lowerSource]
  ring


/-- Positive-order equations (22) before extraction of the endpoint terms.
The average relation is the derivative of `X Ubar = ∫₀ˣ U`, with `K=Ubar-U`.
The beta hypothesis in the equivalence below is the second identity of (21). -/
def PositiveOrderEquations (h C eta X : K) (n : ℕ) (phi u : ℕ → Jet K)
    (beta : ℕ → K) (k p : Jet K)
    (previousAngularDiffusion previousAxialDiffusion omegaQuotient : K) : Prop :=
  X * ((u n).radial + k.radial) + k.value = 0 ∧
  p.radial = inverseSquare C * convolution n (fun i j => (phi i).value * (phi j).value) -
    omegaQuotient / 2 ∧
  2 * (X * (phi n).radial2 + 2 * (phi n).radial) =
    timeValue h (angularPower h + slowPower h n) eta X (phi n) +
      convolution n (angularConvection h eta X phi u beta) - previousAngularDiffusion ∧
  2 * (X * (u n).radial2 + (u n).radial) =
    timeValue h (axialPower h + slowPower h n) eta X (u n) +
      convolution n (axialConvection h eta X u beta) +
      axialValue h (-2 * a h + slowPower h n) eta X p - previousAxialDiffusion

theorem expanded_iff_positiveOrder (h C eta X : K) {n : ℕ} (hn : 0 < n)
    (phi u : ℕ → Jet K) (beta : ℕ → K) (k p : Jet K)
    (previousAngularDiffusion previousAxialDiffusion omegaQuotient : K)
    (hbeta : beta n = betaValue h (slowPower h n) eta (u n) k) :
    ExpandedEquations h (slowPower h n) C eta X (baseAtOrderZero phi u beta)
      (lowerSource h eta X n phi u beta previousAngularDiffusion previousAxialDiffusion
          omegaQuotient)
      (phi n) (u n) k p ↔
    PositiveOrderEquations h C eta X n phi u beta k p
      previousAngularDiffusion previousAxialDiffusion omegaQuotient := by
  unfold ExpandedEquations PositiveOrderEquations
  rw [angularRHS_eq_convolution h eta X hn phi u beta k _ _ _ hbeta,
    axialRHS_eq_convolution h eta X hn phi u beta k p _ _ _ hbeta,
    pressureValue_eq_convolution h C eta X hn phi u beta]

theorem jetSystem_iff_positiveOrder (h C r eta : K) (hr : r ≠ 0) {n : ℕ} (hn : 0 < n)
    (phi u : ℕ → Jet K) (beta : ℕ → K) (k p : Jet K) (q₄ q₅ : K)
    (previousAngularDiffusion previousAxialDiffusion omegaQuotient : K)
    (hbeta : beta n = betaValue h (slowPower h n) eta (u n) k) :
    JetSystem h (slowPower h n) C r eta (baseAtOrderZero phi u beta)
      (lowerSource h eta (r ^ 2) n phi u beta previousAngularDiffusion previousAxialDiffusion
          omegaQuotient)
      (phi n) (u n) k p q₄ q₅ ↔
    PositiveOrderEquations h C eta (r ^ 2) n phi u beta k p
      previousAngularDiffusion previousAxialDiffusion omegaQuotient :=
  (jetSystem_iff_expanded hr _ _ _ _ _ _ _ _).trans
    (expanded_iff_positiveOrder h C eta (r ^ 2) hn phi u beta k p _ _ _ hbeta)

end Algebra


section ActualProfiles

open SimilarityProfile

/-- Jets here are actual Fréchet partial derivatives of real profiles. -/
noncomputable def actualJet (f : InnerProfile) (w : InnerPoint) : Jet ℝ :=
  ⟨f w, partialX f w, partialX (partialX f) w, partialEta f w⟩

theorem timeValue_actualJet (h b : ℝ) (f : InnerProfile) (w : InnerPoint) :
    timeValue h b w.2 w.1 (actualJet f w) = T h b f w := rfl

theorem axialValue_actualJet (h b : ℝ) (f : InnerProfile) (w : InnerPoint) :
    axialValue h b w.2 w.1 (actualJet f w) = Z h b f w := rfl

theorem partialX_contDiffAt {f : InnerProfile} {w : InnerPoint}
    (hf : ContDiffAt ℝ 2 f w) : ContDiffAt ℝ 1 (partialX f) w := by
  exact (hf.fderiv_right (by norm_num : (1 : WithTop ℕ∞) + 1 ≤ 2)).clm_apply contDiffAt_const

theorem hasDerivAt_squareProfile {f : InnerProfile} {r eta : ℝ}
    (hf : DifferentiableAt ℝ f (r ^ 2, eta)) :
    HasDerivAt (fun s => f (s ^ 2, eta)) (2 * r * partialX f (r ^ 2, eta)) r := by
  have hc := hf.hasFDerivAt.comp_hasDerivAt r
    (((hasDerivAt_id r).pow 2).prodMk (hasDerivAt_const r eta))
  convert! hc using 1
  simp [fderiv_inner_apply]
  ring

theorem hasDerivAt_parameterProfile {f : InnerProfile} {X eta : ℝ}
    (hf : DifferentiableAt ℝ f (X, eta)) :
    HasDerivAt (fun z => f (X, z)) (partialEta f (X, eta)) eta := by
  have hc := hf.hasFDerivAt.comp_hasDerivAt eta
    ((hasDerivAt_const eta X).prodMk (hasDerivAt_id eta))
  simpa [fderiv_inner_apply, Function.comp_def] using hc

theorem hasDerivAt_squareProfile_radial {f : InnerProfile} {r eta : ℝ}
    (hf : ContDiffAt ℝ 2 f (r ^ 2, eta)) :
    HasDerivAt (fun s => 2 * s * partialX f (s ^ 2, eta))
      (2 * partialX f (r ^ 2, eta) + 4 * r ^ 2 * partialX (partialX f) (r ^ 2, eta)) r := by
  have hc := ((hasDerivAt_id r).const_mul 2).mul
    (hasDerivAt_squareProfile ((partialX_contDiffAt hf).differentiableAt (by norm_num)))
  convert! hc using 1
  simp only [id_eq]
  ring

/-- Profile vector, given by `jetVector r (actualJet phi (r ^ 2, eta)) (actualJet u (r ^ 2,
eta)) (actualJet k (r ^ 2, eta)) (actualJet p (r ^ 2, eta))`. -/
noncomputable def profileVector (phi u k p : InnerProfile) (r eta : ℝ) : Fin 6 → ℝ :=
  jetVector r (actualJet phi (r ^ 2, eta)) (actualJet u (r ^ 2, eta))
    (actualJet k (r ^ 2, eta)) (actualJet p (r ^ 2, eta))

theorem profileVector_radial {phi u k p : InnerProfile} {r eta : ℝ}
    (hphi : ContDiffAt ℝ 2 phi (r ^ 2, eta)) (hu : ContDiffAt ℝ 2 u (r ^ 2, eta))
    (hk : DifferentiableAt ℝ k (r ^ 2, eta)) (hp : DifferentiableAt ℝ p (r ^ 2, eta)) :
    (fun i => deriv (fun s => profileVector phi u k p s eta i) r) =
      radialJetVector r (actualJet phi (r ^ 2, eta)) (actualJet u (r ^ 2, eta))
        (actualJet k (r ^ 2, eta)) (actualJet p (r ^ 2, eta)) := by
  have hphi' := hphi.differentiableAt (by norm_num)
  have hu' := hu.differentiableAt (by norm_num)
  ext i
  fin_cases i <;> simp only [profileVector, jetVector, actualJet, radialJetVector]
  · exact (hasDerivAt_squareProfile hphi').deriv
  · exact (hasDerivAt_squareProfile hu').deriv
  · exact (hasDerivAt_squareProfile hk).deriv
  · exact (hasDerivAt_squareProfile hp).deriv
  · exact (hasDerivAt_squareProfile_radial hphi).deriv
  · exact (hasDerivAt_squareProfile_radial hu).deriv

theorem profileVector_parameter {phi u k p : InnerProfile} {r eta : ℝ}
    (hphi : DifferentiableAt ℝ phi (r ^ 2, eta)) (hu : DifferentiableAt ℝ u (r ^ 2, eta))
    (hk : DifferentiableAt ℝ k (r ^ 2, eta)) (hp : DifferentiableAt ℝ p (r ^ 2, eta)) :
    (fun i => deriv (fun z => profileVector phi u k p r z i) eta) =
      parameterJetVector (actualJet phi (r ^ 2, eta)) (actualJet u (r ^ 2, eta))
        (actualJet k (r ^ 2, eta)) (actualJet p (r ^ 2, eta))
        (deriv (fun z => profileVector phi u k p r z 4) eta)
        (deriv (fun z => profileVector phi u k p r z 5) eta) := by
  ext i
  fin_cases i <;> simp only [profileVector, jetVector, actualJet, parameterJetVector]
  · exact (hasDerivAt_parameterProfile hphi).deriv
  · exact (hasDerivAt_parameterProfile hu).deriv
  · exact (hasDerivAt_parameterProfile hk).deriv
  · exact (hasDerivAt_parameterProfile hp).deriv
  · rfl
  · rfl

/-- The displayed first-order system uses actual derivatives of the actual
profiles, not independent formal jet variables. -/
def ProfileSystem (h lam C r eta : ℝ) (b : BaseJet ℝ) (s : SourceJet ℝ)
    (phi u k p : InnerProfile) : Prop :=
  (fun i => deriv (fun q => profileVector phi u k p q eta i) r +
    diagonal i / r * profileVector phi u k p r eta i) =
      matrixRHS h lam C r eta b s (profileVector phi u k p r eta)
        (fun i => deriv (fun z => profileVector phi u k p r z i) eta)

theorem profileSystem_iff_expanded {h lam C r eta : ℝ} (hr : r ≠ 0)
    (b : BaseJet ℝ) (s : SourceJet ℝ) {phi u k p : InnerProfile}
    (hphi : ContDiffAt ℝ 2 phi (r ^ 2, eta)) (hu : ContDiffAt ℝ 2 u (r ^ 2, eta))
    (hk : DifferentiableAt ℝ k (r ^ 2, eta)) (hp : DifferentiableAt ℝ p (r ^ 2, eta)) :
    ProfileSystem h lam C r eta b s phi u k p ↔
      ExpandedEquations h lam C eta (r ^ 2) b s (actualJet phi (r ^ 2, eta))
        (actualJet u (r ^ 2, eta)) (actualJet k (r ^ 2, eta)) (actualJet p (r ^ 2, eta)) := by
  unfold ProfileSystem
  rw [profileVector_parameter (hphi.differentiableAt (by norm_num))
    (hu.differentiableAt (by norm_num)) hk hp]
  have hdr := profileVector_radial hphi hu hk hp
  simp_rw [show ∀ i, deriv (fun q => profileVector phi u k p q eta i) r =
      radialJetVector r (actualJet phi (r ^ 2, eta)) (actualJet u (r ^ 2, eta))
        (actualJet k (r ^ 2, eta)) (actualJet p (r ^ 2, eta)) i from congrFun hdr]
  exact jetSystem_iff_expanded hr b s _ _ _ _ _ _




/-- The preceding axial viscosity uses the actual similarity operator twice.
The negative-order term at order zero is zero. -/
noncomputable def precedingDiffusion (h power : ℝ) (F : ℕ → InnerProfile) (n : ℕ) : InnerProfile :=
  if n = 0 then fun _ => 0 else
    Z h (power + slowPower h (n - 1) - dScale h)
      (Z h (power + slowPower h (n - 1)) (F (n - 1)))

theorem precedingDiffusion_congr (h power : ℝ) {F G : ℕ → InnerProfile} {n : ℕ}
    (hFG : ∀ j, j < n → F j = G j) :
    precedingDiffusion h power F n = precedingDiffusion h power G n := by
  cases n with
  | zero => rfl
  | succ k => simp [precedingDiffusion, hFG k (Nat.lt_succ_self k)]

/-- Fully specified source from lower-order profile jets and a supplied
regular representative of the preceding `Ω/X`. -/
noncomputable def actualLowerSource (h : ℝ) (n : ℕ) (phi u beta : ℕ → InnerProfile)
    (omegaQuotient : InnerProfile) (w : InnerPoint) : SourceJet ℝ :=
  lowerSource h w.2 w.1 n (fun j => actualJet (phi j) w) (fun j => actualJet (u j) w)
    (fun j => beta j w) (precedingDiffusion h (angularPower h) phi n w)
    (precedingDiffusion h (axialPower h) u n w) (omegaQuotient w)

theorem actualLowerSource_congr (h : ℝ) {n : ℕ}
    {phi u beta phi' u' beta' : ℕ → InnerProfile} (omegaQuotient : InnerProfile)
    (hphi : ∀ j, j < n → phi j = phi' j)
    (hu : ∀ j, j < n → u j = u' j) (hbeta : ∀ j, j < n → beta j = beta' j)
    (w : InnerPoint) :
    actualLowerSource h n phi u beta omegaQuotient w =
      actualLowerSource h n phi' u' beta' omegaQuotient w := by
  have ha : lowerConvolution n (angularConvection h w.2 w.1
      (fun j => actualJet (phi j) w) (fun j => actualJet (u j) w) (fun j => beta j w)) =
      lowerConvolution n (angularConvection h w.2 w.1
      (fun j => actualJet (phi' j) w) (fun j => actualJet (u' j) w) (fun j => beta' j w)) := by
    apply lowerConvolution_congr
    intro i hi j hj
    simp only [angularConvection, hphi j hj, hu i hi, hbeta i hi]
  have hb : lowerConvolution n (axialConvection h w.2 w.1
      (fun j => actualJet (u j) w) (fun j => beta j w)) =
      lowerConvolution n (axialConvection h w.2 w.1
      (fun j => actualJet (u' j) w) (fun j => beta' j w)) := by
    apply lowerConvolution_congr
    intro i hi j hj
    simp only [axialConvection, hu i hi, hu j hj, hbeta i hi]
  have hc : lowerConvolution n (fun i j => (actualJet (phi i) w).value * (actualJet (phi j)
      w).value) =
      lowerConvolution n (fun i j => (actualJet (phi' i) w).value * (actualJet (phi' j) w).value)
          := by
    apply lowerConvolution_congr
    intro i hi j hj
    rw [hphi i hi, hphi j hj]
  simp only [actualLowerSource, lowerSource, ha, hb, hc,
    precedingDiffusion_congr h (angularPower h) hphi,
    precedingDiffusion_congr h (axialPower h) hu]

theorem actualLowerSource_update (h : ℝ) (n : ℕ) (phi u beta : ℕ → InnerProfile)
    (phiNew uNew betaNew omegaQuotient : InnerProfile) (w : InnerPoint) :
    actualLowerSource h n (Function.update phi n phiNew) (Function.update u n uNew)
      (Function.update beta n betaNew) omegaQuotient w =
        actualLowerSource h n phi u beta omegaQuotient w := by
  apply actualLowerSource_congr
  all_goals intro j hj; exact Function.update_of_ne (Nat.ne_of_lt hj) _ _

theorem baseAtOrderZero_update {n : ℕ} (hn : 0 < n) (phi u beta : ℕ → InnerProfile)
    (phiNew uNew betaNew : InnerProfile) (w : InnerPoint) :
    baseAtOrderZero (fun j => actualJet (Function.update phi n phiNew j) w)
      (fun j => actualJet (Function.update u n uNew j) w)
      (fun j => Function.update beta n betaNew j w) =
    baseAtOrderZero (fun j => actualJet (phi j) w)
      (fun j => actualJet (u j) w) (fun j => beta j w) := by
  simp only [baseAtOrderZero, Function.update_of_ne (Nat.ne_of_lt hn)]

/-- End-to-end equivalence from the actual profile derivatives to the
positive-order convolution equations, with all finite source terms displayed. -/
theorem profileSystem_iff_positiveOrder {h C r eta : ℝ} (hr : r ≠ 0)
    {n : ℕ} (hn : 0 < n) (phi u beta : ℕ → InnerProfile) (k p omegaQuotient : InnerProfile)
    (hphi : ContDiffAt ℝ 2 (phi n) (r ^ 2, eta)) (hu : ContDiffAt ℝ 2 (u n) (r ^ 2, eta))
    (hk : DifferentiableAt ℝ k (r ^ 2, eta)) (hp : DifferentiableAt ℝ p (r ^ 2, eta))
    (hbeta : beta n (r ^ 2, eta) = betaValue h (slowPower h n) eta
      (actualJet (u n) (r ^ 2, eta)) (actualJet k (r ^ 2, eta))) :
    ProfileSystem h (slowPower h n) C r eta
      (baseAtOrderZero (fun j => actualJet (phi j) (r ^ 2, eta))
        (fun j => actualJet (u j) (r ^ 2, eta)) (fun j => beta j (r ^ 2, eta)))
      (actualLowerSource h n phi u beta omegaQuotient (r ^ 2, eta)) (phi n) (u n) k p ↔
    PositiveOrderEquations h C eta (r ^ 2) n
      (fun j => actualJet (phi j) (r ^ 2, eta)) (fun j => actualJet (u j) (r ^ 2, eta))
      (fun j => beta j (r ^ 2, eta)) (actualJet k (r ^ 2, eta)) (actualJet p (r ^ 2, eta))
      (precedingDiffusion h (angularPower h) phi n (r ^ 2, eta))
      (precedingDiffusion h (axialPower h) u n (r ^ 2, eta)) (omegaQuotient (r ^ 2, eta)) :=
  (profileSystem_iff_expanded hr _ _ hphi hu hk hp).trans
    (expanded_iff_positiveOrder h C eta (r ^ 2) hn _ _ _ _ _ _ _ _ hbeta)

/-- The actual radial-average difference, with its regular value at the axis. -/
noncomputable def averageDefect (u : InnerProfile) : InnerProfile :=
  fun w => ProfileHistories.average u w - u w

theorem averageDefect_smooth (Ω : ProfileHistories.RadialDomain) {u : InnerProfile}
    (hu : ContDiffOn ℝ ∞ u Ω.carrier) : ContDiffOn ℝ ∞ (averageDefect u) Ω.carrier :=
  (ProfileHistories.average_smooth Ω hu).sub hu

theorem averageDefect_radial (Ω : ProfileHistories.RadialDomain) {u : InnerProfile}
    (hu : ContDiffOn ℝ ∞ u Ω.carrier) {w : InnerPoint} (hw : w ∈ Ω.carrier) :
    w.1 * (partialX u w + partialX (averageDefect u) w) + averageDefect u w = 0 := by
  have hua := (hu.contDiffAt (Ω.isOpen.mem_nhds hw)).differentiableAt (by simp)
  have haa := ((ProfileHistories.average_smooth Ω hu).contDiffAt
    (Ω.isOpen.mem_nhds hw)).differentiableAt (by simp)
  have hdx : partialX (averageDefect u) w =
      partialX (ProfileHistories.average u) w - partialX u w := by
    change (fderiv ℝ (fun v => ProfileHistories.average u v - u v) w) (1, 0) = _
    rw [fderiv_fun_sub haa hua]
    rfl
  have hd := (hasDerivAt_id w.1).fun_mul
    (ProfileHistories.radialPartial_hasDerivAt Ω (ProfileHistories.average_smooth Ω hu) hw)
  have hp := ProfileHistories.primitive_hasDerivAt Ω hu hw
  have heq : (fun x => x * ProfileHistories.average u (x, w.2)) =
      (fun x => ProfileHistories.primitive u (x, w.2)) := by
    funext x
    exact (ProfileHistories.primitive_eq_mul_average u (x, w.2)).symm
  simp only [id_eq] at hd
  rw [heq] at hd
  have hh := hd.unique hp
  rw [hdx]
  change w.1 * (partialX u w + (partialX (ProfileHistories.average u) w - partialX u w)) +
    (ProfileHistories.average u w - u w) = 0
  change 1 * ProfileHistories.average u (w.1, w.2) +
    w.1 * partialX (ProfileHistories.average u) w = u w at hh
  simp only [one_mul, Prod.eta] at hh
  linear_combination hh

theorem betaValue_averageDefect (Ω : ProfileHistories.RadialDomain) {u : InnerProfile}
    (hu : ContDiffOn ℝ ∞ u Ω.carrier) (h lam : ℝ) {w : InnerPoint}
    (hw : w ∈ Ω.carrier) (hX : w.1 ≠ 0) :
    betaValue h lam w.2 (actualJet u w) (actualJet (averageDefect u) w) =
      SlowDivergence.radialFlux h lam u w / w.1 := by
  have hua := (hu.contDiffAt (Ω.isOpen.mem_nhds hw)).differentiableAt (by simp)
  have haa := ((ProfileHistories.average_smooth Ω hu).contDiffAt
    (Ω.isOpen.mem_nhds hw)).differentiableAt (by simp)
  have hde : partialEta (averageDefect u) w =
      partialEta (ProfileHistories.average u) w - partialEta u w := by
    change (fderiv ℝ (fun v => ProfileHistories.average u v - u v) w) (0, 1) = _
    rw [fderiv_fun_sub haa hua]
    rfl
  rw [betaValue_eq_average_formula, SlowDivergence.radialFlux_div_radial h lam u hX]
  simp only [actualJet]
  rw [hde]
  simp only [averageDefect, dScale, edge, ell, CoordinateAlgebra.D,
    CoordinateAlgebra.d, CoordinateAlgebra.L]
  simp only [div_eq_mul_inv]
  ring

/-- Both identities in (21) hold for the same actual reconstructed flux. -/
theorem averageDefect_divergence (Ω : ProfileHistories.RadialDomain) {u : InnerProfile}
    (hu : ContDiffOn ℝ ∞ u Ω.carrier) (h lam : ℝ) {w : InnerPoint}
    (hw : w ∈ Ω.carrier) (hL : ell h w.2 ≠ 0) :
    partialX (SlowDivergence.radialFlux h lam u) w =
      -axialValue h (-a h + lam) w.2 w.1 (actualJet u w) :=
  SlowDivergence.partialX_radialFlux Ω hu h lam hw hL


/-- The regular average row also recovers the actual radial average. Thus a
smooth solution's third component cannot be an independent auxiliary field. -/
theorem averageDefect_unique (Ω : ProfileHistories.RadialDomain) {u k : InnerProfile}
    (hu : ContDiffOn ℝ ∞ u Ω.carrier) (hk : ContDiffOn ℝ ∞ k Ω.carrier)
    (hrow : ∀ w ∈ Ω.carrier, w.1 * (partialX u w + partialX k w) + k w = 0)
    {w : InnerPoint} (hw : w ∈ Ω.carrier) : k w = averageDefect u w := by
  by_cases hX : w.1 = 0
  · have hk0 := hrow w hw
    have hw0 : w = (0, w.2) := by ext <;> simp [hX]
    rw [hw0] at hk0 ⊢
    simpa [averageDefect, ProfileHistories.average_at_axis] using hk0
  have hd : ∀ x ∈ uIcc (0 : ℝ) w.1,
      HasDerivAt (fun y => y * (u (y, w.2) + k (y, w.2))) (u (x, w.2)) x := by
    intro x hx
    have hxΩ := Ω.segment_mem hw hx
    have hdu := ProfileHistories.radialPartial_hasDerivAt Ω hu hxΩ
    have hdk := ProfileHistories.radialPartial_hasDerivAt Ω hk hxΩ
    apply ((hasDerivAt_id x).fun_mul (hdu.fun_add hdk)).congr_deriv
    have he := hrow (x, w.2) hxΩ
    change x * (ProfileHistories.radialPartial u (x, w.2) +
      ProfileHistories.radialPartial k (x, w.2)) + k (x, w.2) = 0 at he
    simp only [id_eq]
    linear_combination he
  have hi := intervalIntegral.integral_eq_sub_of_hasDerivAt hd
    (ProfileHistories.radial_slice_intervalIntegrable Ω hu hw)
  have hi' : ProfileHistories.primitive u w = w.1 * (u w + k w) := by
    simpa only [ProfileHistories.primitive, zero_mul, sub_zero, Prod.eta] using hi
  rw [ProfileHistories.primitive_eq_mul_average] at hi'
  have he := mul_left_cancel₀ hX hi'
  unfold averageDefect
  linarith

end ActualProfiles


section ComplexCoefficients

open VolterraAnalyticBounds VolterraParity

/-- The eleven finite input jets are, in order:
`φ₀, ∂Xφ₀, ∂ηφ₀, U₀, ∂XU₀, ∂ηU₀, β₀`, followed by the angular source,
axial source, lower pressure product, and regular quotient `Ω_(n-1)/X`.
Regularity is required of these actual finite jets, not inferred from
separate smoothness of a lower-order profile. -/
abbrev CoefficientData := Fin 11 → ℝ × ℂ → ℂ

/-- Coefficient base, given by `⟨⟨F 0 (X, z), F 1 (X, z), 0, F 2 (X, z)⟩, ⟨F 3 (X, z), F 4 (X,
z), 0, F 5 (X, z)⟩, F 6 (X, z)⟩`. -/
noncomputable def coefficientBase (F : CoefficientData) (X : ℝ) (z : ℂ) : BaseJet ℂ :=
  ⟨⟨F 0 (X, z), F 1 (X, z), 0, F 2 (X, z)⟩,
    ⟨F 3 (X, z), F 4 (X, z), 0, F 5 (X, z)⟩, F 6 (X, z)⟩

/-- Coefficient source, given by `⟨F 7 (X, z), F 8 (X, z), F 9 (X, z), F 10 (X, z)⟩`. -/
noncomputable def coefficientSource (F : CoefficientData) (X : ℝ) (z : ℂ) : SourceJet ℂ :=
  ⟨F 7 (X, z), F 8 (X, z), F 9 (X, z), F 10 (X, z)⟩

/-- Coefficient0, defined pointwise by `A0 h lam C (r : ℂ) z (coefficientBase F (r ^ 2) z)`. -/
noncomputable def coefficient0 (h lam C : ℂ) (F : CoefficientData) : Coeff :=
  fun r z => A0 h lam C (r : ℂ) z (coefficientBase F (r ^ 2) z)

/-- Coefficient1, defined pointwise by `A1 h (r : ℂ) z (coefficientBase F (r ^ 2) z)`. -/
noncomputable def coefficient1 (h : ℂ) (F : CoefficientData) : Coeff :=
  fun r z => A1 h (r : ℂ) z (coefficientBase F (r ^ 2) z)

/-- Source field, defined pointwise by `forcing h C (r : ℂ) z (coefficientSource F (r ^ 2) z)`. -/
noncomputable def sourceField (h C : ℂ) (F : CoefficientData) : Field :=
  fun r z => forcing h C (r : ℂ) z (coefficientSource F (r ^ 2) z)

theorem coefficient1_shape (h : ℂ) (F : CoefficientData) :
    DerivativeShape (coefficient1 h F) := by
  intro r z i j hij
  exact A1_shape h (r : ℂ) z _ i j hij

theorem diagonal_eq_exponent (i : Fin 6) :
    (diagonal i : ℂ) = (exponent i : ℂ) := by
  fin_cases i <;> norm_num [diagonal, exponent]

theorem coefficient0_parity (h lam C : ℂ) (F : CoefficientData) :
    CoefficientParity (coefficient0 h lam C F) := by
  intro r z i j
  simp only [coefficient0, neg_sq, Complex.ofReal_neg]
  fin_cases i <;> fin_cases j <;>
    simp only [A0, mul_neg, neg_mul, axialValue, even_two, Even.neg_pow, neg_add_rev, Fin.zero_eta,
      Fin.isValue, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
      Matrix.cons_val_fin_one, paritySign, Nat.ofNat_pos, ite_true, mul_one, mul_zero, Fin.mk_one,
      Matrix.cons_val_one, Nat.one_lt_ofNat, Fin.reduceFinMk, Matrix.cons_val, Nat.reduceLT,
      Nat.lt_add_one, lt_self_iff_false, neg_neg, one_mul, ite_false]

theorem coefficient1_parity (h : ℂ) (F : CoefficientData) :
    CoefficientParity (coefficient1 h F) := by
  intro r z i j
  simp only [coefficient1, neg_sq, Complex.ofReal_neg]
  fin_cases i <;> fin_cases j <;>
    simp only [A1, neg_mul, even_two, Even.neg_pow, Fin.zero_eta, Fin.isValue, Matrix.of_apply,
      Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_fin_one, paritySign, Nat.ofNat_pos,
      ite_true, mul_one, mul_zero, Fin.mk_one, Matrix.cons_val_one, Nat.one_lt_ofNat,
      Fin.reduceFinMk, Matrix.cons_val, Nat.reduceLT, Nat.lt_add_one, lt_self_iff_false, mul_neg,
      neg_neg, one_mul, ite_false]

theorem sourceField_parity (h C : ℂ) (F : CoefficientData) :
    ForcingParity (sourceField h C F) := by
  intro r z i
  simp only [sourceField, neg_sq, Complex.ofReal_neg]
  fin_cases i <;> simp [forcing, paritySign]

private theorem data_square_contDiffAt {n : WithTop ℕ∞} {F : CoefficientData}
    {w : ℝ × ℂ} (hF : ∀ i, ContDiffAt ℝ n (F i) (w.1 ^ 2, w.2)) (i : Fin 11) :
    ContDiffAt ℝ n (fun v : ℝ × ℂ => F i (v.1 ^ 2, v.2)) w :=
  (hF i).comp w ((contDiffAt_fst.pow 2).prodMk contDiffAt_snd)

theorem inverse_ell_contDiffAt {n : WithTop ℕ∞} {h : ℂ} {w : ℝ × ℂ}
    (hL : ell h w.2 ≠ 0) :
    ContDiffAt ℝ n (fun v : ℝ × ℂ => (ell h v.2)⁻¹) w := by
  change 1 - 2 * h * w.2 ^ 2 ≠ 0 at hL
  exact (contDiffAt_const.sub (contDiffAt_const.mul (contDiffAt_snd.pow 2))).inv hL

theorem inverse_ell_analyticAt {h z : ℂ} (hL : ell h z ≠ 0) :
    AnalyticAt ℂ (fun v => (ell h v)⁻¹) z := by
  change 1 - 2 * h * z ^ 2 ≠ 0 at hL
  exact (analyticAt_const.sub (analyticAt_const.mul (analyticAt_id.pow 2))).inv hL

theorem coefficient0_contDiffAt_of_pullback {n : WithTop ℕ∞} {h lam C : ℂ} {F : CoefficientData}
    {w : ℝ × ℂ} (hF : ∀ i, ContDiffAt ℝ n (fun v : ℝ × ℂ => F i (v.1 ^ 2, v.2)) w)
    (hL : ell h w.2 ≠ 0) (i j : Fin 6) :
    ContDiffAt ℝ n (fun v : ℝ × ℂ => coefficient0 h lam C F v.1 v.2 i j) w := by
  have hdata := hF
  have hlinv := inverse_ell_contDiffAt (n := n) (w := w) hL
  have hcoe : ContDiffAt ℝ n (fun v : ℝ × ℂ => (v.1 : ℂ)) w :=
    Complex.ofRealCLM.contDiff.contDiffAt.comp w contDiffAt_fst
  fin_cases i <;>
    simp only [coefficient0, A0, Matrix.of_apply, Fin.zero_eta, Fin.isValue,
      Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_fin_one, Fin.mk_one,
      Matrix.cons_val_one, Fin.reduceFinMk, Matrix.cons_val] <;>
    (first | exact contDiffAt_const | skip) <;>
    fin_cases j <;>
    simp only [coefficientBase, Fin.isValue, ell, div_eq_mul_inv, axialValue,
        edge, neg_mul, neg_add_rev, Fin.zero_eta,
            Matrix.cons_val_zero, Fin.mk_one, Matrix.cons_val_one,
                Fin.reduceFinMk, Matrix.cons_val] <;>
    (repeat' first
      | exact contDiffAt_const
      | exact hdata _
      | exact contDiffAt_snd
      | exact hcoe
      | exact hlinv
      | apply ContDiffAt.add
      | apply ContDiffAt.sub
      | apply ContDiffAt.mul
      | apply ContDiffAt.neg)

theorem coefficient1_contDiffAt_of_pullback {n : WithTop ℕ∞} {h : ℂ} {F : CoefficientData}
    {w : ℝ × ℂ} (hF : ∀ i, ContDiffAt ℝ n (fun v : ℝ × ℂ => F i (v.1 ^ 2, v.2)) w)
    (hL : ell h w.2 ≠ 0) (i j : Fin 6) :
    ContDiffAt ℝ n (fun v : ℝ × ℂ => coefficient1 h F v.1 v.2 i j) w := by
  have hdata := hF
  have hlinv := inverse_ell_contDiffAt (n := n) (w := w) hL
  have hcoe : ContDiffAt ℝ n (fun v : ℝ × ℂ => (v.1 : ℂ)) w :=
    Complex.ofRealCLM.contDiff.contDiffAt.comp w contDiffAt_fst
  have hphi : ContDiffAt ℝ n (fun v : ℝ × ℂ =>
      (v.1 : ℂ) ^ 2 * F 1 (v.1 ^ 2, v.2) + F 0 (v.1 ^ 2, v.2)) w :=
    ((hcoe.pow 2).mul (hdata 1)).add (hdata 0)
  have hu : ContDiffAt ℝ n (fun v : ℝ × ℂ =>
      (v.1 : ℂ) ^ 2 * F 4 (v.1 ^ 2, v.2)) w := (hcoe.pow 2).mul (hdata 4)
  have htransport : ContDiffAt ℝ n (fun v : ℝ × ℂ =>
      dScale h * v.2 + (1 - v.2 ^ 2) * F 3 (v.1 ^ 2, v.2)) w :=
    (contDiffAt_const.mul contDiffAt_snd).add
      ((contDiffAt_const.sub (contDiffAt_snd.pow 2)).mul (hdata 3))
  fin_cases i <;>
    simp only [coefficient1, A1, Matrix.of_apply, Fin.zero_eta, Fin.isValue,
      Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_fin_one, Fin.mk_one,
      Matrix.cons_val_one, Fin.reduceFinMk, Matrix.cons_val] <;>
    (first | exact contDiffAt_const | skip) <;>
    fin_cases j <;>
    simp only [edge, coefficientBase, Fin.isValue, ell, div_eq_mul_inv, neg_mul,
        Fin.zero_eta, Matrix.cons_val_zero,
            Fin.mk_one, Matrix.cons_val_one, Fin.reduceFinMk,
                Matrix.cons_val] <;>
    (repeat' first
      | exact contDiffAt_const
      | exact hphi
      | exact hu
      | exact htransport
      | exact hdata _
      | exact contDiffAt_snd
      | exact hcoe
      | exact hlinv
      | apply ContDiffAt.add
      | apply ContDiffAt.sub
      | apply ContDiffAt.mul
      | apply ContDiffAt.neg)

theorem sourceField_contDiffAt_of_pullback {n : WithTop ℕ∞} {h C : ℂ} {F : CoefficientData}
    {w : ℝ × ℂ} (hF : ∀ i, ContDiffAt ℝ n (fun v : ℝ × ℂ => F i (v.1 ^ 2, v.2)) w)
    (hL : ell h w.2 ≠ 0) (i : Fin 6) :
    ContDiffAt ℝ n (fun v : ℝ × ℂ => sourceField h C F v.1 v.2 i) w := by
  have hdata := hF
  have hlinv := inverse_ell_contDiffAt (n := n) (w := w) hL
  have hcoe : ContDiffAt ℝ n (fun v : ℝ × ℂ => (v.1 : ℂ)) w :=
    Complex.ofRealCLM.contDiff.contDiffAt.comp w contDiffAt_fst
  fin_cases i <;>
    simp only [sourceField, forcing, pressureSource, coefficientSource, Fin.isValue,
        div_eq_mul_inv, ell, Fin.zero_eta, Matrix.cons_val_zero, Fin.mk_one, Matrix.cons_val_one,
            Fin.reduceFinMk, Matrix.cons_val] <;>
    (repeat' first
      | exact contDiffAt_const
      | exact hdata _
      | exact contDiffAt_snd
      | exact hcoe
      | exact hlinv
      | apply ContDiffAt.add
      | apply ContDiffAt.sub
      | apply ContDiffAt.mul)

theorem coefficient0_analyticAt {h lam C : ℂ} {F : CoefficientData} {r : ℝ} {z : ℂ}
    (hF : ∀ i, AnalyticAt ℂ (fun v => F i (r ^ 2, v)) z) (hL : ell h z ≠ 0) (i j : Fin 6) :
    AnalyticAt ℂ (fun v => coefficient0 h lam C F r v i j) z := by
  have hlinv := inverse_ell_analyticAt hL
  fin_cases i <;>
    simp only [coefficient0, A0, Matrix.of_apply, Fin.zero_eta, Fin.isValue,
      Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_fin_one, Fin.mk_one,
      Matrix.cons_val_one, Fin.reduceFinMk, Matrix.cons_val] <;>
    (first | exact analyticAt_const | skip) <;>
    fin_cases j <;>
    simp only [coefficientBase, Fin.isValue, ell, div_eq_mul_inv, axialValue,
        edge, neg_mul, neg_add_rev, Fin.zero_eta,
            Matrix.cons_val_zero, Fin.mk_one, Matrix.cons_val_one,
                Fin.reduceFinMk, Matrix.cons_val] <;>
    (repeat' first
      | exact analyticAt_const
      | exact hF _
      | exact analyticAt_id
      | exact hlinv
      | apply AnalyticAt.fun_add
      | apply AnalyticAt.fun_sub
      | apply AnalyticAt.fun_mul
      | apply AnalyticAt.fun_neg)

theorem coefficient1_analyticAt {h : ℂ} {F : CoefficientData} {r : ℝ} {z : ℂ}
    (hF : ∀ i, AnalyticAt ℂ (fun v => F i (r ^ 2, v)) z) (hL : ell h z ≠ 0) (i j : Fin 6) :
    AnalyticAt ℂ (fun v => coefficient1 h F r v i j) z := by
  have hlinv := inverse_ell_analyticAt hL
  fin_cases i <;>
    simp only [coefficient1, A1, Matrix.of_apply, Fin.zero_eta, Fin.isValue,
      Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_fin_one, Fin.mk_one,
      Matrix.cons_val_one, Fin.reduceFinMk, Matrix.cons_val] <;>
    (first | exact analyticAt_const | skip) <;>
    fin_cases j <;>
    simp only [edge, coefficientBase, Fin.isValue, ell, div_eq_mul_inv, neg_mul,
        Fin.zero_eta, Matrix.cons_val_zero,
            Fin.mk_one, Matrix.cons_val_one, Fin.reduceFinMk,
                Matrix.cons_val] <;>
    (repeat' first
      | exact analyticAt_const
      | exact hF _
      | exact analyticAt_id
      | exact hlinv
      | apply AnalyticAt.fun_add
      | apply AnalyticAt.fun_sub
      | apply AnalyticAt.fun_mul
      | apply AnalyticAt.fun_neg)

theorem sourceField_analyticAt {h C : ℂ} {F : CoefficientData} {r : ℝ} {z : ℂ}
    (hF : ∀ i, AnalyticAt ℂ (fun v => F i (r ^ 2, v)) z) (hL : ell h z ≠ 0) (i : Fin 6) :
    AnalyticAt ℂ (fun v => sourceField h C F r v i) z := by
  have hlinv := inverse_ell_analyticAt hL
  fin_cases i <;>
    simp only [sourceField, forcing, pressureSource, coefficientSource, Fin.isValue,
        div_eq_mul_inv, ell, Fin.zero_eta, Matrix.cons_val_zero, Fin.mk_one, Matrix.cons_val_one,
            Fin.reduceFinMk, Matrix.cons_val] <;>
    (repeat' first
      | exact analyticAt_const
      | exact hF _
      | exact analyticAt_id
      | exact hlinv
      | apply AnalyticAt.fun_add
      | apply AnalyticAt.fun_sub
      | apply AnalyticAt.fun_mul)


/-- One-sided smooth X data suffice for a smooth signed square pullback. -/
theorem square_pullback_contDiffAt {n : WithTop ℕ∞} {f : ℝ × ℂ → ℂ} {w : ℝ × ℂ}
    (hf : ContDiffWithinAt ℝ n f (Ici (0 : ℝ) ×ˢ (univ : Set ℂ)) (w.1 ^ 2, w.2)) :
    ContDiffAt ℝ n (fun v : ℝ × ℂ => f (v.1 ^ 2, v.2)) w := by
  change ContDiffWithinAt ℝ n _ univ _
  apply hf.comp w ((contDiffAt_fst.pow 2).prodMk contDiffAt_snd).contDiffWithinAt
  intro v _hv
  exact ⟨sq_nonneg v.1, Set.mem_univ _⟩

theorem coefficient0_contDiffAt {n : WithTop ℕ∞} {h lam C : ℂ} {F : CoefficientData}
    {w : ℝ × ℂ} (hF : ∀ i, ContDiffAt ℝ n (F i) (w.1 ^ 2, w.2))
    (hL : ell h w.2 ≠ 0) (i j : Fin 6) :
    ContDiffAt ℝ n (fun v : ℝ × ℂ => coefficient0 h lam C F v.1 v.2 i j) w :=
  coefficient0_contDiffAt_of_pullback (data_square_contDiffAt hF) hL i j

theorem coefficient1_contDiffAt {n : WithTop ℕ∞} {h : ℂ} {F : CoefficientData}
    {w : ℝ × ℂ} (hF : ∀ i, ContDiffAt ℝ n (F i) (w.1 ^ 2, w.2))
    (hL : ell h w.2 ≠ 0) (i j : Fin 6) :
    ContDiffAt ℝ n (fun v : ℝ × ℂ => coefficient1 h F v.1 v.2 i j) w :=
  coefficient1_contDiffAt_of_pullback (data_square_contDiffAt hF) hL i j

theorem sourceField_contDiffAt {n : WithTop ℕ∞} {h C : ℂ} {F : CoefficientData}
    {w : ℝ × ℂ} (hF : ∀ i, ContDiffAt ℝ n (F i) (w.1 ^ 2, w.2))
    (hL : ell h w.2 ≠ 0) (i : Fin 6) :
    ContDiffAt ℝ n (fun v : ℝ × ℂ => sourceField h C F v.1 v.2 i) w :=
  sourceField_contDiffAt_of_pullback (data_square_contDiffAt hF) hL i

theorem coefficient0_contDiffOn_of_pullback {n : WithTop ℕ∞} {h lam C : ℂ}
    {F : CoefficientData} {S : Set (ℝ × ℂ)}
    (hF : ∀ w ∈ S, ∀ i, ContDiffAt ℝ n (fun v : ℝ × ℂ => F i (v.1 ^ 2, v.2)) w)
    (hL : ∀ w ∈ S, ell h w.2 ≠ 0) (i j : Fin 6) :
    ContDiffOn ℝ n (fun v : ℝ × ℂ => coefficient0 h lam C F v.1 v.2 i j) S :=
  fun w hw => (coefficient0_contDiffAt_of_pullback (hF w hw) (hL w hw) i j).contDiffWithinAt

theorem coefficient1_contDiffOn_of_pullback {n : WithTop ℕ∞} {h : ℂ}
    {F : CoefficientData} {S : Set (ℝ × ℂ)}
    (hF : ∀ w ∈ S, ∀ i, ContDiffAt ℝ n (fun v : ℝ × ℂ => F i (v.1 ^ 2, v.2)) w)
    (hL : ∀ w ∈ S, ell h w.2 ≠ 0) (i j : Fin 6) :
    ContDiffOn ℝ n (fun v : ℝ × ℂ => coefficient1 h F v.1 v.2 i j) S :=
  fun w hw => (coefficient1_contDiffAt_of_pullback (hF w hw) (hL w hw) i j).contDiffWithinAt

theorem sourceField_contDiffOn_of_pullback {n : WithTop ℕ∞} {h C : ℂ}
    {F : CoefficientData} {S : Set (ℝ × ℂ)}
    (hF : ∀ w ∈ S, ∀ i, ContDiffAt ℝ n (fun v : ℝ × ℂ => F i (v.1 ^ 2, v.2)) w)
    (hL : ∀ w ∈ S, ell h w.2 ≠ 0) (i : Fin 6) :
    ContDiffOn ℝ n (fun v : ℝ × ℂ => sourceField h C F v.1 v.2 i) S :=
  fun w hw => (sourceField_contDiffAt_of_pullback (hF w hw) (hL w hw) i).contDiffWithinAt

theorem coefficient0_contDiffOn {n : WithTop ℕ∞} {h lam C : ℂ} {F : CoefficientData}
    {S : Set (ℝ × ℂ)}
    (hF : ∀ w ∈ S, ∀ i, ContDiffAt ℝ n (F i) (w.1 ^ 2, w.2))
    (hL : ∀ w ∈ S, ell h w.2 ≠ 0) (i j : Fin 6) :
    ContDiffOn ℝ n (fun v : ℝ × ℂ => coefficient0 h lam C F v.1 v.2 i j) S :=
  fun w hw => (coefficient0_contDiffAt (hF w hw) (hL w hw) i j).contDiffWithinAt

theorem coefficient1_contDiffOn {n : WithTop ℕ∞} {h : ℂ} {F : CoefficientData}
    {S : Set (ℝ × ℂ)}
    (hF : ∀ w ∈ S, ∀ i, ContDiffAt ℝ n (F i) (w.1 ^ 2, w.2))
    (hL : ∀ w ∈ S, ell h w.2 ≠ 0) (i j : Fin 6) :
    ContDiffOn ℝ n (fun v : ℝ × ℂ => coefficient1 h F v.1 v.2 i j) S :=
  fun w hw => (coefficient1_contDiffAt (hF w hw) (hL w hw) i j).contDiffWithinAt

theorem sourceField_contDiffOn {n : WithTop ℕ∞} {h C : ℂ} {F : CoefficientData}
    {S : Set (ℝ × ℂ)}
    (hF : ∀ w ∈ S, ∀ i, ContDiffAt ℝ n (F i) (w.1 ^ 2, w.2))
    (hL : ∀ w ∈ S, ell h w.2 ≠ 0) (i : Fin 6) :
    ContDiffOn ℝ n (fun v : ℝ × ℂ => sourceField h C F v.1 v.2 i) S :=
  fun w hw => (sourceField_contDiffAt (hF w hw) (hL w hw) i).contDiffWithinAt

end ComplexCoefficients


section RealOutput

open VolterraAnalyticBounds

/-- Complex jet, given by `⟨j.value, j.radial, j.radial2, j.parameter⟩`. -/
noncomputable def complexJet (j : Jet ℝ) : Jet ℂ :=
  ⟨j.value, j.radial, j.radial2, j.parameter⟩

/-- Complex base, given by `⟨complexJet b.phi, complexJet b.axial, b.beta⟩`. -/
noncomputable def complexBase (b : BaseJet ℝ) : BaseJet ℂ :=
  ⟨complexJet b.phi, complexJet b.axial, b.beta⟩

/-- Complex source, given by `⟨s.angular, s.axial, s.pressureProduct, s.omegaQuotient⟩`. -/
noncomputable def complexSource (s : SourceJet ℝ) : SourceJet ℂ :=
  ⟨s.angular, s.axial, s.pressureProduct, s.omegaQuotient⟩

theorem A0_ofReal (h lam C r eta : ℝ) (b : BaseJet ℝ) :
    A0 (h : ℂ) (lam : ℂ) (C : ℂ) (r : ℂ) (eta : ℂ) (complexBase b) =
      (A0 h lam C r eta b).map Complex.ofReal := by
  -- Normalize casts once before splitting into the 36 matrix entries.
  simp only [A0, complexBase, complexJet, angularPower, axialPower,
    axialValue, inverseSquare, a, dScale, ell, edge,
    ← Complex.ofReal_zero, ← Complex.ofReal_one, ← Complex.ofReal_ofNat,
    ← Complex.ofReal_add, ← Complex.ofReal_sub, ← Complex.ofReal_mul,
    ← Complex.ofReal_div, ← Complex.ofReal_neg, ← Complex.ofReal_pow,
    ← Complex.ofReal_inv]
  apply Matrix.ext
  intro i j
  fin_cases i <;> fin_cases j <;> rfl

theorem A1_ofReal (h r eta : ℝ) (b : BaseJet ℝ) :
    A1 (h : ℂ) (r : ℂ) (eta : ℂ) (complexBase b) =
      (A1 h r eta b).map Complex.ofReal := by
  simp only [A1, complexBase, complexJet, dScale, ell, edge,
    ← Complex.ofReal_zero, ← Complex.ofReal_one, ← Complex.ofReal_ofNat,
    ← Complex.ofReal_add, ← Complex.ofReal_sub, ← Complex.ofReal_mul,
    ← Complex.ofReal_div, ← Complex.ofReal_neg, ← Complex.ofReal_pow]
  apply Matrix.ext
  intro i j
  fin_cases i <;> fin_cases j <;> rfl

theorem forcing_ofReal (h C r eta : ℝ) (s : SourceJet ℝ) :
    forcing (h : ℂ) (C : ℂ) (r : ℂ) (eta : ℂ) (complexSource s) =
      fun i => ((forcing h C r eta s i : ℝ) : ℂ) := by
  ext i
  fin_cases i <;>
    simp [forcing, complexSource, pressureSource, inverseSquare, ell]

theorem diagonal_ofReal (i : Fin 6) :
    (diagonal i : ℂ) = ((diagonal i : ℝ) : ℂ) := by
  fin_cases i <;> norm_num [diagonal]

/-- Taking real parts commutes with the explicit system at real input jets. -/
theorem matrixRHS_realPart (h lam C r eta : ℝ) (b : BaseJet ℝ) (s : SourceJet ℝ)
    (w v : Vec) (i : Fin 6) :
    (matrixRHS (h : ℂ) (lam : ℂ) (C : ℂ) (r : ℂ) (eta : ℂ)
      (complexBase b) (complexSource s) w v i).re =
    matrixRHS h lam C r eta b s (fun j => (w j).re) (fun j => (v j).re) i := by
  simp only [matrixRHS, A0_ofReal, A1_ofReal, forcing_ofReal, Pi.add_apply, Complex.add_re]
  simp [Matrix.mulVec, dotProduct, Matrix.map, Complex.mul_re]

/-- Real trace, given by `(W r (eta : ℂ) i).re`. -/
noncomputable def realTrace (W : Field) (r eta : ℝ) (i : Fin 6) : ℝ :=
  (W r (eta : ℂ) i).re

/-- A complex solution with real coefficients yields a real solution by
componentwise real part. Both radial and parameter derivatives in the result
are actual real derivatives; no reality of the chosen complex solution is assumed. -/
theorem realTrace_solves_system (h lam C r eta : ℝ) (b : BaseJet ℝ) (s : SourceJet ℝ)
    (W : Field)
    (hr : ∀ i, DifferentiableAt ℝ (fun q => W q (eta : ℂ) i) r)
    (hz : ∀ i, DifferentiableAt ℂ (fun z => W r z i) (eta : ℂ))
    (hW : ∀ i, deriv (fun q => W q (eta : ℂ) i) r +
      (diagonal i : ℂ) / (r : ℂ) * W r (eta : ℂ) i =
      matrixRHS (h : ℂ) (lam : ℂ) (C : ℂ) (r : ℂ) (eta : ℂ)
        (complexBase b) (complexSource s) (W r (eta : ℂ))
        (fun j => deriv (fun z => W r z j) (eta : ℂ)) i) :
    ∀ i, deriv (fun q => realTrace W q eta i) r +
      (diagonal i : ℝ) / r * realTrace W r eta i =
      matrixRHS h lam C r eta b s (realTrace W r eta)
        (fun j => deriv (fun z => realTrace W r z j) eta) i := by
  have hrd (i : Fin 6) : deriv (fun q => realTrace W q eta i) r =
      (deriv (fun q => W q (eta : ℂ) i) r).re := by
    exact (Complex.reCLM.hasFDerivAt.comp_hasDerivAt r (hr i).hasDerivAt).deriv
  have hzd (i : Fin 6) : deriv (fun z => realTrace W r z i) eta =
      (deriv (fun z => W r z i) (eta : ℂ)).re :=
    (hz i).hasDerivAt.real_of_complex.deriv
  intro i
  have he := congrArg Complex.re (hW i)
  have hc : (diagonal i : ℂ) / (r : ℂ) = (((diagonal i : ℝ) / r : ℝ) : ℂ) := by
    rw [diagonal_ofReal, Complex.ofReal_div]
  rw [Complex.add_re, hc, Complex.mul_re, matrixRHS_realPart] at he
  rw [hrd i]
  simp_rw [hzd]
  simp only [Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero] at he
  exact he

end RealOutput

end NavierStokes.PositiveAxisSystem
