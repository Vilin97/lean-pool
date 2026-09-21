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

import LeanPool.PoincareGeometry.BonnetMyers.IntrinsicGeodesic

/-!
# Tangent-valued local covariant acceleration

The coordinate ODE used for local geodesics has an `E`-valued acceleration.
This file packages the same expression as a vector in the actual tangent
fibre.  The packaging is deliberately parameterized by a germ of global frame
extensions: the covariant-derivative API is local for section germs, and the
first theorem below records that the resulting tangent vector is independent
of which such global extensions are used.

This is the layer needed before comparing coordinate calculations from two
overlapping charts.  It does not yet assert a chart-transition theorem.
-/

noncomputable section

open Bundle Manifold Set
open scoped Manifold ContDiff ENNReal Topology

namespace BonnetMyersEntry

universe u v w

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type v} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [I.Boundaryless]
  {M : Type w} [TopologicalSpace M] [ChartedSpace H M]
  [T2Space M] [SigmaCompactSpace M] [IsManifold I ∞ M]

local notation "TM" => (TangentSpace I : M → Type _)

namespace IntrinsicAcceleration

variable [RiemannianBundle (TangentSpace I : M → Type _)]

abbrev FrameIndex (E : Type u) [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] := Fin (Module.finrank ℝ E)

/-- The tangent vector represented by the model vector `u` in the local frame
of the tangent-bundle trivialization based at `x₀`. -/
def coordinateFrameVector
    (x₀ : M) (b : Module.Basis (FrameIndex E) ℝ E)
    (u : E) (y : M) : TM y :=
  LocalGeodesicData.coordinateFrameCombination (I := I) (M := M)
    (x₀ := x₀) b u y

lemma coordinateFrameVector_add
    (x₀ : M) (b : Module.Basis (FrameIndex E) ℝ E)
    (u v : E) (y : M) :
    coordinateFrameVector (I := I) (M := M) x₀ b (u + v) y =
      coordinateFrameVector (I := I) (M := M) x₀ b u y +
        coordinateFrameVector (I := I) (M := M) x₀ b v y := by
  simp only [coordinateFrameVector, LocalGeodesicData.coordinateFrameCombination,
    map_add, Finsupp.add_apply, add_smul]
  rw [Finset.sum_add_distrib]

lemma coordinateFrameVector_smul
    (x₀ : M) (b : Module.Basis (FrameIndex E) ℝ E)
    (r : ℝ) (u : E) (y : M) :
    coordinateFrameVector (I := I) (M := M) x₀ b (r • u) y =
      r • coordinateFrameVector (I := I) (M := M) x₀ b u y := by
  simp only [coordinateFrameVector, LocalGeodesicData.coordinateFrameCombination,
    map_smul, Finsupp.smul_apply, smul_eq_mul]
  rw [Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  rw [smul_smul]

/-- The linear map induced by a local tangent frame at a fixed point. -/
noncomputable def coordinateFrameLinear
    (x₀ : M) (b : Module.Basis (FrameIndex E) ℝ E) (y : M) : E →ₗ[ℝ] TM y where
  toFun u := coordinateFrameVector (I := I) (M := M) x₀ b u y
  map_add' u v := coordinateFrameVector_add (I := I) (M := M) x₀ b u v y
  map_smul' r u := coordinateFrameVector_smul (I := I) (M := M) x₀ b r u y

@[simp] lemma coordinateFrameLinear_apply
    (x₀ : M) (b : Module.Basis (FrameIndex E) ℝ E) (u : E) (y : M) :
    coordinateFrameLinear (I := I) (M := M) x₀ b y u =
      coordinateFrameVector (I := I) (M := M) x₀ b u y := rfl

@[simp] lemma coordinateFrameLinear_apply_basis
    (x₀ : M) (b : Module.Basis (FrameIndex E) ℝ E)
    (i : FrameIndex E) (y : M) :
    coordinateFrameLinear (I := I) (M := M) x₀ b y (b i) =
      (trivializationAt E TM x₀).localFrame b i y := by
  classical
  change coordinateFrameVector (I := I) (M := M) x₀ b (b i) y = _
  simp only [coordinateFrameVector, LocalGeodesicData.coordinateFrameCombination,
    Module.Basis.repr_self]
  rw [Finset.sum_eq_single i]
  · simp
  · intro j hj hji
    simp [hji]
  · simp

/-- The connection part of the acceleration in a chosen local tangent frame.
The vector fields in `S` are global extensions; only their germs at `y`
enter the definition. -/
def frameConnectionTerm
    (cov : CovariantDerivative I E TM) (x₀ : M)
    (b : Module.Basis (FrameIndex E) ℝ E)
    (S : FrameIndex E → (Π y : M, TM y))
    (u : E) (y : M) : TM y :=
  ∑ i, (∑ j, ∑ k,
    (b.repr u j) * (b.repr u k) *
      (trivializationAt E TM x₀).localFrameCoeff I b i y
        (cov (S j) y (S k y))) •
    (trivializationAt E TM x₀).localFrame b i y

/-- A tangent-valued covariant-acceleration expression.  The first summand
is the time derivative of the frame coefficients; the second is the
connection contribution. -/
def frameCovariantAcceleration
    (cov : CovariantDerivative I E TM) (x₀ : M)
    (b : Module.Basis (FrameIndex E) ℝ E)
    (S : FrameIndex E → (Π y : M, TM y))
    (u a : E) (y : M) : TM y :=
  coordinateFrameVector (I := I) (M := M) x₀ b a y +
    frameConnectionTerm (I := I) (M := M) cov x₀ b S u y

/-- A time-dependent tangent-vector field and a separately supplied time
derivative field.  Keeping the time derivative explicit avoids pretending
that a derivative of a bundle-valued family has already been constructed. -/
abbrev TimeDependentTangentField := ℝ → (Π y : M, TM y)

/-- The coordinate-free acceleration of a time-dependent extension at a
point.  When `X` extends the velocity of a curve and `A` is its time
derivative, this is the usual `∂ₜ X + ∇_X X` expression. -/
def accelerationOfTimeField
    (cov : CovariantDerivative I E TM)
    (X A : TimeDependentTangentField (I := I) (M := M))
    (t : ℝ) (y : M) : TM y :=
  A t y + cov (X t) y (X t y)

/-- A change of extension which preserves the spatial germ of the velocity
field and the pointwise time derivative preserves acceleration. -/
theorem accelerationOfTimeField_congr_of_germ
    (cov : CovariantDerivative I E TM)
    (X A Y B : TimeDependentTangentField (I := I) (M := M))
    {t : ℝ} {y : M}
    (hX : MDiffAt (T% (X t)) y) (hY : MDiffAt (T% (Y t)) y)
    (hXY : ∀ᶠ z in 𝓝 y, X t z = Y t z) (hAB : A t y = B t y) :
    accelerationOfTimeField (I := I) (M := M) cov X A t y =
      accelerationOfTimeField (I := I) (M := M) cov Y B t y := by
  have hcov : cov (X t) y = cov (Y t) y :=
    IsCovariantDerivativeOn.congr_of_eventuallyEq cov.isCovariantDerivativeOn
      hX hY Filter.univ_mem hXY
  have hvalue : X t y = Y t y :=
    Filter.Eventually.self_of_nhds (p := fun z : M => X t z = Y t z) hXY
  simp only [accelerationOfTimeField, hAB, hcov, hvalue]

/-- The time-dependent field obtained by using time-varying coefficients in
a fixed family of frame extensions. -/
def timeFrameField
    (b : Module.Basis (FrameIndex E) ℝ E)
    (S : FrameIndex E → (Π y : M, TM y)) (u : ℝ → E)
    (t : ℝ) (y : M) : TM y :=
  ∑ i, (b.repr (u t) i) • S i y

/-- Equal frame germs give equal time-dependent frame fields. -/
theorem timeFrameField_congr_of_eventuallyEq
    (b : Module.Basis (FrameIndex E) ℝ E)
    (S T : FrameIndex E → (Π y : M, TM y)) (u : ℝ → E)
    {t : ℝ} {y : M}
    (hST : ∀ i, ∀ᶠ z in 𝓝 y, S i z = T i z) :
    ∀ᶠ z in 𝓝 y,
      timeFrameField (I := I) (M := M) b S u t z =
        timeFrameField (I := I) (M := M) b T u t z := by
  have hAll : ∀ᶠ z in 𝓝 y,
      ∀ i ∈ (Finset.univ : Finset (FrameIndex E)), S i z = T i z := by
    exact (Finset.eventually_all Finset.univ).2 fun i hi => hST i
  filter_upwards [hAll] with z hz
  simp only [timeFrameField]
  apply Finset.sum_congr rfl
  intro i hi
  rw [hz i (Finset.mem_univ i)]

/-- The spatial vector field obtained from fixed frame coefficients. -/
def frameField
    (b : Module.Basis (FrameIndex E) ℝ E)
    (S : FrameIndex E → (Π y : M, TM y)) (u : E) : Π y : M, TM y :=
  fun y ↦ ∑ i, (b.repr u i) • S i y

lemma mdiffAt_frameField
    (b : Module.Basis (FrameIndex E) ℝ E)
    (S : FrameIndex E → (Π y : M, TM y)) (u : E) {y : M}
    (hS : ∀ i, MDiffAt (T% (S i)) y) :
    MDiffAt (T% (frameField (I := I) (M := M) b S u)) y := by
  classical
  let f : FrameIndex E → (Π z : M, TM z) :=
    fun i ↦ (b.repr u i) • S i
  have hf : ∀ i, MDiffAt (T% (f i)) y := by
    intro i
    exact mdifferentiableAt_const.smul_section (hS i)
  have hsum : ∀ s : Finset (FrameIndex E),
      MDiffAt (T% (∑ i ∈ s, f i)) y := by
    intro s
    induction s using Finset.induction_on with
    | empty =>
        change MDiffAt (zeroSection E TM) y
        exact mdifferentiableAt_zeroSection ..
    | insert i s hi hs =>
        rw [Finset.sum_insert hi]
        exact mdifferentiableAt_add_section (hf i) hs
  simpa [frameField, f] using hsum Finset.univ

/-- Covariant differentiation of a fixed-coefficient frame field expands
linearly in the frame extensions. -/
lemma cov_frameField_eq_sum
    (cov : CovariantDerivative I E TM)
    (b : Module.Basis (FrameIndex E) ℝ E)
    (S : FrameIndex E → (Π y : M, TM y)) (u : E) {y : M}
    (hS : ∀ i, MDiffAt (T% (S i)) y) :
    cov (frameField (I := I) (M := M) b S u) y =
      ∑ i, (b.repr u i) • cov (S i) y := by
  classical
  let f : FrameIndex E → (Π z : M, TM z) :=
    fun i ↦ (b.repr u i) • S i
  have hf : ∀ i, MDiffAt (T% (f i)) y := by
    intro i
    exact mdifferentiableAt_const.smul_section (hS i)
  have hsum : ∀ s : Finset (FrameIndex E),
      MDiffAt (T% (∑ i ∈ s, f i)) y := by
    intro s
    induction s using Finset.induction_on with
    | empty =>
        change MDiffAt (zeroSection E TM) y
        exact mdifferentiableAt_zeroSection ..
    | insert i s hi hs =>
        rw [Finset.sum_insert hi]
        exact mdifferentiableAt_add_section (hf i) hs
  have hcovsum : ∀ s : Finset (FrameIndex E),
      cov (∑ i ∈ s, f i) y = ∑ i ∈ s, cov (f i) y := by
    intro s
    induction s using Finset.induction_on with
    | empty =>
        simpa using (IsCovariantDerivativeOn.zero cov.isCovariantDerivativeOn (x := y))
    | insert i s hi hs =>
        rw [Finset.sum_insert hi, cov.isCovariantDerivativeOn.add (hf i) (hsum s), hs,
          Finset.sum_insert hi]
  calc
    cov (frameField (I := I) (M := M) b S u) y =
        cov (∑ i ∈ (Finset.univ : Finset (FrameIndex E)), f i) y := by
          congr 1
          funext z
          simp [frameField, f]
    _ = ∑ i ∈ (Finset.univ : Finset (FrameIndex E)), cov (f i) y := hcovsum Finset.univ
    _ = ∑ i, (b.repr u i) • cov (S i) y := by
      apply Finset.sum_congr rfl
      intro i hi
      exact IsCovariantDerivativeOn.smul_const cov.isCovariantDerivativeOn
        (b.repr u i) (hS i)

/-- The connection contribution written directly as a tangent vector, without
passing through coordinates of the output fibre. -/
def directFrameConnectionTerm
    (cov : CovariantDerivative I E TM)
    (b : Module.Basis (FrameIndex E) ℝ E)
    (S : FrameIndex E → (Π y : M, TM y))
    (u : E) (y : M) : TM y :=
  ∑ j, ∑ k, ((b.repr u j) * (b.repr u k)) • cov (S k) y (S j y)

lemma cov_frameField_apply_eq_directFrameConnectionTerm
    (cov : CovariantDerivative I E TM)
    (b : Module.Basis (FrameIndex E) ℝ E)
    (S : FrameIndex E → (Π y : M, TM y)) (u : E) {y : M}
    (hS : ∀ i, MDiffAt (T% (S i)) y) :
    cov (frameField (I := I) (M := M) b S u) y
      (frameField (I := I) (M := M) b S u y) =
      directFrameConnectionTerm (I := I) (M := M) cov b S u y := by
  rw [cov_frameField_eq_sum (I := I) (M := M) cov b S u hS]
  simp only [frameField, directFrameConnectionTerm, map_sum, map_smul]
  apply Finset.sum_congr rfl
  intro j hj
  rw [ContinuousLinearMap.sum_apply, Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro k hk
  simp only [ContinuousLinearMap.smul_apply, smul_smul]

/-- The tangent-valued acceleration obtained by differentiating the frame
coefficients and then applying the connection directly in the tangent fibre. -/
def directFrameCovariantAcceleration
    (cov : CovariantDerivative I E TM)
    (b : Module.Basis (FrameIndex E) ℝ E)
    (S : FrameIndex E → (Π y : M, TM y))
    (u a : E) (y : M) : TM y :=
  frameField (I := I) (M := M) b S a y +
    directFrameConnectionTerm (I := I) (M := M) cov b S u y

/-- The coordinate-free time-dependent-field expression specializes to the
direct frame acceleration when the two supplied coefficient families are the
velocity coefficients and their time derivative, respectively.  The theorem
only uses their values at `t`; the assertion that the second family really is
the derivative of the first is kept as a separate analytic obligation. -/
theorem accelerationOfTimeFrameField_eq_directFrameCovariantAcceleration
    (cov : CovariantDerivative I E TM)
    (b : Module.Basis (FrameIndex E) ℝ E)
    (S : FrameIndex E → (Π y : M, TM y))
    (u a : ℝ → E) {t : ℝ} {y : M}
    (hS : ∀ i, MDiffAt (T% (S i)) y) :
    accelerationOfTimeField (I := I) (M := M) cov
      (timeFrameField (I := I) (M := M) b S u)
      (timeFrameField (I := I) (M := M) b S a) t y =
      directFrameCovariantAcceleration (I := I) (M := M) cov b S (u t) (a t) y := by
  change frameField (I := I) (M := M) b S (a t) y +
      cov (frameField (I := I) (M := M) b S (u t)) y
        (frameField (I := I) (M := M) b S (u t) y) = _
  rw [cov_frameField_apply_eq_directFrameConnectionTerm (I := I) (M := M)
    cov b S (u t) hS]
  rfl

/-- The direct connection term may equivalently be indexed by the section
being differentiated first.  This is only a finite reindexing; it does not
use a torsion or symmetry assumption on the connection. -/
lemma directFrameConnectionTerm_eq_sum_covariantFirst
    (cov : CovariantDerivative I E TM)
    (b : Module.Basis (FrameIndex E) ℝ E)
    (S : FrameIndex E → (Π y : M, TM y)) (u : E) (y : M) :
    directFrameConnectionTerm (I := I) (M := M) cov b S u y =
      ∑ j, ∑ k, ((b.repr u j) * (b.repr u k)) • cov (S j) y (S k y) := by
  rw [directFrameConnectionTerm, Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j hj
  apply Finset.sum_congr rfl
  intro k hk
  rw [mul_comm]

/-- On the base set of the chart trivialization, the direct tangent-fibre
connection term is exactly the earlier coordinate-frame expression.  This is
the algebraic bridge which makes the coordinate ODE an intrinsic connection
calculation, rather than merely an equation in the model vector space. -/
theorem directFrameConnectionTerm_eq_frameConnectionTerm
    (cov : CovariantDerivative I E TM) (x₀ : M)
    (b : Module.Basis (FrameIndex E) ℝ E)
    (S : FrameIndex E → (Π y : M, TM y)) (u : E) {y : M}
    (hy : y ∈ (trivializationAt E TM x₀).baseSet) :
    directFrameConnectionTerm (I := I) (M := M) cov b S u y =
      frameConnectionTerm (I := I) (M := M) cov x₀ b S u y := by
  classical
  calc
    directFrameConnectionTerm (I := I) (M := M) cov b S u y =
        ∑ j, ∑ k, ((b.repr u j) * (b.repr u k)) • cov (S j) y (S k y) :=
      directFrameConnectionTerm_eq_sum_covariantFirst (I := I) (M := M) cov b S u y
    _ = ∑ j, ∑ k, ((b.repr u j) * (b.repr u k)) •
        (∑ i, (trivializationAt E TM x₀).localFrameCoeff I b i y
          (cov (S j) y (S k y)) •
          (trivializationAt E TM x₀).localFrame b i y) := by
      apply Finset.sum_congr rfl
      intro j hj
      apply Finset.sum_congr rfl
      intro k hk
      exact congrArg (fun v : TM y => ((b.repr u j) * (b.repr u k)) • v)
        ((trivializationAt E TM x₀).eq_sum_localFrameCoeff_smul
          (I := I) (b := b) (s := fun z => cov (S j) z (S k z)) hy)
    _ = ∑ j, ∑ k, ∑ i,
        (((b.repr u j) * (b.repr u k)) *
          (trivializationAt E TM x₀).localFrameCoeff I b i y
            (cov (S j) y (S k y))) •
          (trivializationAt E TM x₀).localFrame b i y := by
      simp only [Finset.smul_sum, smul_smul]
    _ = ∑ j, ∑ i, ∑ k,
        (((b.repr u j) * (b.repr u k)) *
          (trivializationAt E TM x₀).localFrameCoeff I b i y
            (cov (S j) y (S k y))) •
          (trivializationAt E TM x₀).localFrame b i y := by
      apply Finset.sum_congr rfl
      intro j hj
      rw [Finset.sum_comm]
    _ = ∑ i, ∑ j, ∑ k,
        (((b.repr u j) * (b.repr u k)) *
          (trivializationAt E TM x₀).localFrameCoeff I b i y
            (cov (S j) y (S k y))) •
          (trivializationAt E TM x₀).localFrame b i y := by
      rw [Finset.sum_comm]
    _ = frameConnectionTerm (I := I) (M := M) cov x₀ b S u y := by
      unfold frameConnectionTerm
      apply Finset.sum_congr rfl
      intro i hi
      calc
        ∑ j, ∑ k,
            (((b.repr u j) * (b.repr u k)) *
              (trivializationAt E TM x₀).localFrameCoeff I b i y
                (cov (S j) y (S k y))) •
              (trivializationAt E TM x₀).localFrame b i y =
            ∑ j, (∑ k,
              ((b.repr u j) * (b.repr u k)) *
                (trivializationAt E TM x₀).localFrameCoeff I b i y
                  (cov (S j) y (S k y))) •
                (trivializationAt E TM x₀).localFrame b i y := by
              apply Finset.sum_congr rfl
              intro j hj
              rw [Finset.sum_smul]
        _ = (∑ j, ∑ k,
              ((b.repr u j) * (b.repr u k)) *
                (trivializationAt E TM x₀).localFrameCoeff I b i y
                  (cov (S j) y (S k y))) •
                (trivializationAt E TM x₀).localFrame b i y := by
              rw [Finset.sum_smul]

/-- If a family of global frame extensions has the chart-frame values at a
point, its direct tangent-fibre acceleration agrees there with the
coordinate-frame acceleration.  The value condition is deliberately explicit:
global extensions supplied by `smoothExtend` agree with a local frame only on
a neighbourhood, not on an entire chart domain. -/
theorem directFrameCovariantAcceleration_eq_frameCovariantAcceleration
    (cov : CovariantDerivative I E TM) (x₀ : M)
    (b : Module.Basis (FrameIndex E) ℝ E)
    (S : FrameIndex E → (Π y : M, TM y)) (u a : E) {y : M}
    (hy : y ∈ (trivializationAt E TM x₀).baseSet)
    (hS : ∀ i, S i y = (trivializationAt E TM x₀).localFrame b i y) :
    directFrameCovariantAcceleration (I := I) (M := M) cov b S u a y =
      frameCovariantAcceleration (I := I) (M := M) cov x₀ b S u a y := by
  unfold directFrameCovariantAcceleration frameCovariantAcceleration
  rw [directFrameConnectionTerm_eq_frameConnectionTerm (I := I) (M := M)
    cov x₀ b S u hy]
  congr 1
  unfold frameField coordinateFrameVector LocalGeodesicData.coordinateFrameCombination
  apply Finset.sum_congr rfl
  intro i hi
  rw [hS i]

/-- The coordinate covariant acceleration, transported back to the tangent
fibre over the inverse-chart point. -/
def coordinateCovariantAccelerationVector
    (cov : CovariantDerivative I E TM) (x₀ : M)
    (b : Module.Basis (FrameIndex E) ℝ E)
    (z u a : E) : TM ((extChartAt I x₀).symm z) :=
  coordinateFrameVector (I := I) (M := M) x₀ b
    (LocalGeodesicData.coordinateCovariantAcceleration (I := I) (M := M)
      cov x₀ b z u a)
    ((extChartAt I x₀).symm z)

/-- Replacing every frame extension by a section with the same germ does not
change the connection term.  This is the exact locality principle supplied by
`CovariantDerivative.IsCovariantDerivativeOn`; no global choice of extension
is hidden in the result. -/
theorem frameConnectionTerm_congr_of_eventuallyEq
    (cov : CovariantDerivative I E TM) (x₀ : M)
    (b : Module.Basis (FrameIndex E) ℝ E)
    (S T : FrameIndex E → (Π y : M, TM y))
    {y : M} (hS : ∀ j, MDiffAt (T% (S j)) y)
    (hT : ∀ j, MDiffAt (T% (T j)) y)
    (hST : ∀ j, ∀ᶠ z in 𝓝 y, S j z = T j z) (u : E) :
    frameConnectionTerm (I := I) (M := M) cov x₀ b S u y =
      frameConnectionTerm (I := I) (M := M) cov x₀ b T u y := by
  have hcov : ∀ j, cov (S j) y = cov (T j) y := by
    intro j
    exact IsCovariantDerivativeOn.congr_of_eventuallyEq cov.isCovariantDerivativeOn
      (hS j) (hT j) Filter.univ_mem (hST j)
  have hvalue : ∀ j, S j y = T j y := by
    intro j
    exact Filter.Eventually.self_of_nhds (p := fun z : M => S j z = T j z) (hST j)
  unfold frameConnectionTerm
  apply Finset.sum_congr rfl
  intro i hi
  congr 1
  apply Finset.sum_congr rfl
  intro j hj
  apply Finset.sum_congr rfl
  intro k hk
  rw [hcov j, hvalue k]

/-- The full tangent-valued acceleration is likewise independent of the
chosen global extensions of one local frame germ. -/
theorem frameCovariantAcceleration_congr_of_eventuallyEq
    (cov : CovariantDerivative I E TM) (x₀ : M)
    (b : Module.Basis (FrameIndex E) ℝ E)
    (S T : FrameIndex E → (Π y : M, TM y))
    {y : M} (hS : ∀ j, MDiffAt (T% (S j)) y)
    (hT : ∀ j, MDiffAt (T% (T j)) y)
    (hST : ∀ j, ∀ᶠ z in 𝓝 y, S j z = T j z) (u a : E) :
    frameCovariantAcceleration (I := I) (M := M) cov x₀ b S u a y =
      frameCovariantAcceleration (I := I) (M := M) cov x₀ b T u a y := by
  simp only [frameCovariantAcceleration]
  rw [frameConnectionTerm_congr_of_eventuallyEq (I := I) (M := M)
    cov x₀ b S T hS hT hST u]

/-- In the chart based at `x₀`, the `E`-valued coordinate expression and the
tangent-valued expression agree exactly.  The latter uses the canonical
smooth extensions already used to define the connection coefficients. -/
theorem coordinateCovariantAccelerationVector_eq_frameCovariantAcceleration
    (cov : CovariantDerivative I E TM) (x₀ : M)
    (b : Module.Basis (FrameIndex E) ℝ E)
    {y : M} (hy : y ∈ (extChartAt I x₀).source) (u a : E) :
    coordinateCovariantAccelerationVector (I := I) (M := M) cov x₀ b
      (extChartAt I x₀ y) u a =
      frameCovariantAcceleration (I := I) (M := M) cov x₀ b
        (fun j => LocalGeodesicData.smoothFrame (I := I) (M := M) (E := E) x₀ b j)
        u a y := by
  have hsymm : (extChartAt I x₀).symm (extChartAt I x₀ y) = y :=
    (extChartAt I x₀).left_inv hy
  change coordinateFrameVector (I := I) (M := M) x₀ b
      (LocalGeodesicData.coordinateCovariantAcceleration (I := I) (M := M)
        cov x₀ b (extChartAt I x₀ y) u a)
      ((extChartAt I x₀).symm (extChartAt I x₀ y)) = _
  rw [hsymm]
  change coordinateFrameLinear (I := I) (M := M) x₀ b y
      (LocalGeodesicData.coordinateCovariantAcceleration (I := I) (M := M)
        cov x₀ b (extChartAt I x₀ y) u a) = _
  rw [LocalGeodesicData.coordinateCovariantAcceleration]
  rw [map_add, LocalGeodesicData.coordinateConnectionTerm, map_sum]
  simp only [LinearMap.map_smul, coordinateFrameLinear_apply_basis,
    frameCovariantAcceleration, frameConnectionTerm, coordinateFrameVector,
    LocalGeodesicData.coordinateFrameCombination,
    LocalGeodesicData.connectionCoefficient]
  rw [hsymm]
  rfl

/-- On a point where the canonical global frame extensions have the local-frame
values, the coordinate acceleration is the direct tangent-fibre covariant
acceleration. -/
theorem coordinateCovariantAccelerationVector_eq_directFrameCovariantAcceleration_smoothFrame
    (cov : CovariantDerivative I E TM) (x₀ : M)
    (b : Module.Basis (FrameIndex E) ℝ E)
    {y : M} (hy : y ∈ (extChartAt I x₀).source)
    (hframe : ∀ i,
      LocalGeodesicData.smoothFrame (I := I) (M := M) (E := E) x₀ b i y =
        (trivializationAt E TM x₀).localFrame b i y)
    (u a : E) :
    coordinateCovariantAccelerationVector (I := I) (M := M) cov x₀ b
      (extChartAt I x₀ y) u a =
      directFrameCovariantAcceleration (I := I) (M := M) cov b
        (fun i => LocalGeodesicData.smoothFrame (I := I) (M := M) (E := E) x₀ b i)
        u a y := by
  rw [coordinateCovariantAccelerationVector_eq_frameCovariantAcceleration
    (I := I) (M := M) cov x₀ b hy u a]
  symm
  exact directFrameCovariantAcceleration_eq_frameCovariantAcceleration
    (I := I) (M := M) cov x₀ b
    (fun i => LocalGeodesicData.smoothFrame (I := I) (M := M) (E := E) x₀ b i)
    u a (by simpa using hy) hframe

/-- The coordinate and direct tangent-fibre accelerations agree on an actual
neighbourhood of the chart centre.  This is the correct scope for the
canonical `smoothExtend` frames, whose agreement with the local chart frame
is local rather than global on the chart source. -/
theorem coordinateCovariantAccelerationVector_eventuallyEq_directFrameCovariantAcceleration
    (cov : CovariantDerivative I E TM) (x₀ : M)
    (b : Module.Basis (FrameIndex E) ℝ E) (u a : E) :
    ∀ᶠ y in 𝓝 x₀,
      coordinateCovariantAccelerationVector (I := I) (M := M) cov x₀ b
        (extChartAt I x₀ y) u a =
      directFrameCovariantAcceleration (I := I) (M := M) cov b
        (fun i => LocalGeodesicData.smoothFrame (I := I) (M := M) (E := E) x₀ b i)
        u a y := by
  have hframes : ∀ᶠ y in 𝓝 x₀,
      ∀ i ∈ (Finset.univ : Finset (FrameIndex E)),
        LocalGeodesicData.smoothFrame (I := I) (M := M) (E := E) x₀ b i y =
          (trivializationAt E TM x₀).localFrame b i y := by
    exact (Finset.eventually_all Finset.univ).2 fun i hi =>
      LocalGeodesicData.smoothFrame_eventuallyEq_localFrame
        (I := I) (M := M) (E := E) x₀ b i
  filter_upwards [hframes, extChartAt_source_mem_nhds (I := I) x₀] with y hframe hy
  exact coordinateCovariantAccelerationVector_eq_directFrameCovariantAcceleration_smoothFrame
    (I := I) (M := M) cov x₀ b hy (fun i => hframe i (Finset.mem_univ i)) u a

/-- The canonical global extensions of a local tangent frame are
manifold-differentiable at every point. -/
lemma mdiffAt_smoothFrame
    (x₀ : M) (b : Module.Basis (FrameIndex E) ℝ E)
    (i : FrameIndex E) (y : M) :
    MDiffAt (T% (LocalGeodesicData.smoothFrame (I := I) (M := M) (E := E) x₀ b i)) y := by
  have hframe : ContMDiff I (I.prod 𝓘(ℝ, E)) 2
      (fun z ↦ TotalSpace.mk' E (E := TM) z
        (LocalGeodesicData.smoothFrame (I := I) (M := M) (E := E) x₀ b i z)) := by
    simpa [LocalGeodesicData.smoothFrame] using
      (CovariantDerivative.smoothExtend_contMDiff_two
        (I := I) (F := E) (V := TM) x₀
          ((trivializationAt E TM x₀).localFrame b i x₀))
  simpa only [ModelWithCorners.tangent] using
    (hframe.contMDiffAt : ContMDiffAt I (I.prod 𝓘(ℝ, E)) 2 _ y).mdifferentiableAt
      (by norm_num)

/-- The neighbourhood on which the canonical global extensions agree with
the local chart frame.  It is retained explicitly, since equality is not
available on the whole chart source. -/
def smoothFrameAgreementSet
    (x₀ : M) (b : Module.Basis (FrameIndex E) ℝ E) : Set M :=
  {y | y ∈ (extChartAt I x₀).source ∧ ∀ i,
    LocalGeodesicData.smoothFrame (I := I) (M := M) (E := E) x₀ b i y =
      (trivializationAt E TM x₀).localFrame b i y}

theorem smoothFrameAgreementSet_mem_nhds
    (x₀ : M) (b : Module.Basis (FrameIndex E) ℝ E) :
    smoothFrameAgreementSet (I := I) (M := M) x₀ b ∈ 𝓝 x₀ := by
  have hframes : ∀ᶠ y in 𝓝 x₀,
      ∀ i ∈ (Finset.univ : Finset (FrameIndex E)),
        LocalGeodesicData.smoothFrame (I := I) (M := M) (E := E) x₀ b i y =
          (trivializationAt E TM x₀).localFrame b i y := by
    exact (Finset.eventually_all Finset.univ).2 fun i hi =>
      LocalGeodesicData.smoothFrame_eventuallyEq_localFrame
        (I := I) (M := M) (E := E) x₀ b i
  filter_upwards [hframes, extChartAt_source_mem_nhds (I := I) x₀] with y hframe hy
  exact ⟨hy, fun i => hframe i (Finset.mem_univ i)⟩

theorem coordinateCovariantAccelerationVector_eq_directFrameCovariantAcceleration_of_mem_agreement
    (cov : CovariantDerivative I E TM) (x₀ : M)
    (b : Module.Basis (FrameIndex E) ℝ E) {y : M}
    (hy : y ∈ smoothFrameAgreementSet (I := I) (M := M) x₀ b) (u a : E) :
    coordinateCovariantAccelerationVector (I := I) (M := M) cov x₀ b
      (extChartAt I x₀ y) u a =
      directFrameCovariantAcceleration (I := I) (M := M) cov b
        (fun i => LocalGeodesicData.smoothFrame (I := I) (M := M) (E := E) x₀ b i)
        u a y :=
  coordinateCovariantAccelerationVector_eq_directFrameCovariantAcceleration_smoothFrame
    (I := I) (M := M) cov x₀ b hy.1 hy.2 u a

/-- A coordinate-geodesic certificate makes the corresponding tangent-valued
acceleration vanish in the actual tangent fibre. -/
theorem coordinateCovariantAccelerationVector_eq_zero
    (cov : CovariantDerivative I E TM) (x₀ : M)
    (b : Module.Basis (FrameIndex E) ℝ E) {v₀ : E}
    (sol : LocalChartSecondOrderSolution I
      (LocalGeodesicData.coordinateAcceleration (I := I) (M := M) cov x₀ b) x₀ v₀)
    (hsol : LocalGeodesicData.IsCoordinateGeodesic
      (cov := cov) (x₀ := x₀) (b := b) sol)
    {t : ℝ} (ht : t ∈ Ioo (-sol.radius) sol.radius) :
    coordinateCovariantAccelerationVector (I := I) (M := M) cov x₀ b
      (sol.coordinate t) (sol.velocity t) (deriv sol.velocity t) = 0 := by
  unfold coordinateCovariantAccelerationVector
  rw [hsol ht]
  unfold coordinateFrameVector LocalGeodesicData.coordinateFrameCombination
  simp only [map_zero, Finsupp.zero_apply]
  apply Finset.sum_eq_zero
  intro j hj
  exact zero_smul _ _

/-- A coordinate geodesic has vanishing direct tangent-fibre acceleration
whenever its manifold curve lies in the neighbourhood where the canonical
frame extensions agree with the chart frame. -/
theorem local_solution_directFrameCovariantAcceleration_eq_zero_of_mem_agreement
    (cov : CovariantDerivative I E TM) (x₀ : M)
    (b : Module.Basis (FrameIndex E) ℝ E) {v₀ : E}
    (sol : LocalChartSecondOrderSolution I
      (LocalGeodesicData.coordinateAcceleration (I := I) (M := M) cov x₀ b) x₀ v₀)
    (hsol : LocalGeodesicData.IsCoordinateGeodesic
      (cov := cov) (x₀ := x₀) (b := b) sol)
    {t : ℝ} (ht : t ∈ Ioo (-sol.radius) sol.radius)
    (hmem : LocalChartSecondOrderSolution.curve sol t ∈
      smoothFrameAgreementSet (I := I) (M := M) x₀ b) :
    directFrameCovariantAcceleration (I := I) (M := M) cov b
      (fun i => LocalGeodesicData.smoothFrame (I := I) (M := M) (E := E) x₀ b i)
      (sol.velocity t) (deriv sol.velocity t)
      (LocalChartSecondOrderSolution.curve sol t) = 0 := by
  have hzero := coordinateCovariantAccelerationVector_eq_zero
    (I := I) (M := M) cov x₀ b sol hsol ht
  rw [← LocalChartSecondOrderSolution.curve_eq_chart sol ht] at hzero
  exact (coordinateCovariantAccelerationVector_eq_directFrameCovariantAcceleration_of_mem_agreement
    (I := I) (M := M) cov x₀ b hmem (sol.velocity t) (deriv sol.velocity t)).symm.trans hzero

/-- The manifold curve of a local coordinate solution remains in the
smooth-frame agreement neighbourhood for all sufficiently small times. -/
theorem local_solution_eventually_mem_smoothFrameAgreementSet
    (x₀ : M) (b : Module.Basis (FrameIndex E) ℝ E) {F : E → E → E} {v₀ : E}
    (sol : LocalChartSecondOrderSolution I F x₀ v₀) :
    ∀ᶠ t in 𝓝 (0 : ℝ), LocalChartSecondOrderSolution.curve sol t ∈
      smoothFrameAgreementSet (I := I) (M := M) x₀ b := by
  have hzero : (0 : ℝ) ∈ Ioo (-sol.radius) sol.radius := by
    constructor <;> linarith [sol.radius_pos]
  have hcont : ContinuousAt (LocalChartSecondOrderSolution.curve sol) 0 :=
    (LocalChartSecondOrderSolution.curve_hasMFDerivAt (I := I) (M := M)
      (E := E) (H := H) sol hzero).continuousAt
  have hset : smoothFrameAgreementSet (I := I) (M := M) x₀ b ∈
      𝓝 (LocalChartSecondOrderSolution.curve sol 0) := by
    rw [LocalChartSecondOrderSolution.curve_initial (I := I) (M := M)
      (E := E) (H := H) sol]
    exact smoothFrameAgreementSet_mem_nhds (I := I) (M := M) x₀ b
  exact hcont.preimage_mem_nhds hset

/-- Therefore the direct tangent-fibre acceleration of every local coordinate
geodesic vanishes on a neighbourhood of its initial time. -/
theorem local_solution_eventually_directFrameCovariantAcceleration_eq_zero
    (cov : CovariantDerivative I E TM) (x₀ : M)
    (b : Module.Basis (FrameIndex E) ℝ E) {v₀ : E}
    (sol : LocalChartSecondOrderSolution I
      (LocalGeodesicData.coordinateAcceleration (I := I) (M := M) cov x₀ b) x₀ v₀)
    (hsol : LocalGeodesicData.IsCoordinateGeodesic
      (cov := cov) (x₀ := x₀) (b := b) sol) :
    ∀ᶠ t in 𝓝 (0 : ℝ),
      directFrameCovariantAcceleration (I := I) (M := M) cov b
        (fun i => LocalGeodesicData.smoothFrame (I := I) (M := M) (E := E) x₀ b i)
        (sol.velocity t) (deriv sol.velocity t)
        (LocalChartSecondOrderSolution.curve sol t) = 0 := by
  have hinterval : Ioo (-sol.radius) sol.radius ∈ 𝓝 (0 : ℝ) := by
    exact Ioo_mem_nhds (by linarith [sol.radius_pos])
      (by linarith [sol.radius_pos])
  filter_upwards [hinterval,
    local_solution_eventually_mem_smoothFrameAgreementSet (I := I) (M := M)
      (E := E) (H := H) x₀ b sol] with t ht hmem
  exact local_solution_directFrameCovariantAcceleration_eq_zero_of_mem_agreement
    (I := I) (M := M) cov x₀ b sol hsol ht hmem

/-- The preceding zero equation can be presented through the coordinate-free
time-dependent-field expression `A + ∇_X X`, with the coefficient derivative
of the ODE supplied as `A`.  Establishing that this supplied term is the
bundle derivative along the curve is the remaining analytic identification. -/
theorem local_solution_eventually_accelerationOfTimeFrameField_eq_zero
    (cov : CovariantDerivative I E TM) (x₀ : M)
    (b : Module.Basis (FrameIndex E) ℝ E) {v₀ : E}
    (sol : LocalChartSecondOrderSolution I
      (LocalGeodesicData.coordinateAcceleration (I := I) (M := M) cov x₀ b) x₀ v₀)
    (hsol : LocalGeodesicData.IsCoordinateGeodesic
      (cov := cov) (x₀ := x₀) (b := b) sol) :
    ∀ᶠ t in 𝓝 (0 : ℝ),
      accelerationOfTimeField (I := I) (M := M) cov
        (timeFrameField (I := I) (M := M) b
          (fun i => LocalGeodesicData.smoothFrame (I := I) (M := M) (E := E) x₀ b i)
          sol.velocity)
        (timeFrameField (I := I) (M := M) b
          (fun i => LocalGeodesicData.smoothFrame (I := I) (M := M) (E := E) x₀ b i)
          (fun s => deriv sol.velocity s))
        t (LocalChartSecondOrderSolution.curve sol t) = 0 := by
  filter_upwards [local_solution_eventually_directFrameCovariantAcceleration_eq_zero
    (I := I) (M := M) cov x₀ b sol hsol] with t hzero
  rw [accelerationOfTimeFrameField_eq_directFrameCovariantAcceleration
    (I := I) (M := M) cov b
    (fun i => LocalGeodesicData.smoothFrame (I := I) (M := M) (E := E) x₀ b i)
    sol.velocity (fun s => deriv sol.velocity s)
    (fun i => mdiffAt_smoothFrame (I := I) (M := M) x₀ b i
      (LocalChartSecondOrderSolution.curve sol t))]
  exact hzero

end IntrinsicAcceleration

namespace IntrinsicGeodesic.LocalGeodesic

variable [RiemannianBundle (TangentSpace I : M → Type _)]
variable {cov : CovariantDerivative I E TM} {x₀ : M} {v₀ : TM x₀}

/-- The manifold-valued local geodesic wrapper carries a vanishing
tangent-valued acceleration certificate, rather than only an equation in the
model fibre. -/
theorem coordinateCovariantAccelerationVector_eq_zero
    {cov : CovariantDerivative I E TM} {x₀ : M} {v₀ : TM x₀}
    (γ : IntrinsicGeodesic.LocalGeodesic (I := I) (M := M) cov x₀ v₀)
    {t : ℝ} (ht : t ∈ Ioo (-γ.solution.radius) γ.solution.radius) :
    IntrinsicAcceleration.coordinateCovariantAccelerationVector (I := I) (M := M)
      cov x₀ (IntrinsicGeodesic.canonicalBasis (E := E))
      (γ.solution.coordinate t) (γ.solution.velocity t) (deriv γ.solution.velocity t) = 0 := by
  exact IntrinsicAcceleration.coordinateCovariantAccelerationVector_eq_zero
    (I := I) (M := M) cov x₀ (IntrinsicGeodesic.canonicalBasis (E := E))
    γ.solution γ.isGeodesic ht

end IntrinsicGeodesic.LocalGeodesic

end BonnetMyersEntry
