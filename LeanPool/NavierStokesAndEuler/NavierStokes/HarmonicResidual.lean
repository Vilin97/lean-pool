/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.NavierStokes.CorrectionState
public import LeanPool.NavierStokesAndEuler.NavierStokes.LinearWaveResidual
public import LeanPool.NavierStokesAndEuler.NavierStokes.HarmonicFields

@[expose] public section

/-!
# Finite harmonic extraction of the actual cylindrical residual

The coefficient operations below reconstruct genuine differential fields.
Excluded errors remain explicit inputs with field-evaluation witnesses.
-/

noncomputable section

namespace NavierStokes.HarmonicResidual

open Set Function Filter MeasureTheory
open HarmonicFields HarmonicCalculus
open scoped Topology ContDiff BigOperators ComplexConjugate


variable {D : Type} [NormedAddCommGroup D] [NormedSpace ℝ D]

abbrev Coefficients (D : Type) := HarmonicFields.Coefficients D
abbrev VectorCoefficients (D : Type) := Fin 3 → Coefficients D

noncomputable def liftDomain (U : Set D) : Set (D × ℝ) := U ×ˢ univ

omit [NormedSpace ℝ D] in
theorem liftDomain_open {U : Set D} (hU : IsOpen U) : IsOpen (liftDomain U) :=
  hU.prod isOpen_univ

noncomputable def liftDirection (V : D → D) (p : D × ℝ) : D × ℝ := (V p.1, 0)
noncomputable def angularDirection (_p : D × ℝ) : D × ℝ := (0, 1)

/-- Smoothness is required of actual coefficient functions. -/
def SmoothCoefficients (U : Set D) (c : Coefficients D) : Prop :=
  ∀ j : ℤ, ContDiffOn ℝ ∞ (c j) U

theorem smoothCoefficients_zero (U : Set D) : SmoothCoefficients U 0 := fun _ => contDiffOn_const

theorem SmoothCoefficients.add {U : Set D} {c d : Coefficients D}
    (hc : SmoothCoefficients U c) (hd : SmoothCoefficients U d) : SmoothCoefficients U (c + d) :=
  fun j => (hc j).add (hd j)

theorem SmoothCoefficients.neg {U : Set D} {c : Coefficients D}
    (hc : SmoothCoefficients U c) : SmoothCoefficients U (-c) := fun j => (hc j).neg

theorem SmoothCoefficients.sub {U : Set D} {c d : Coefficients D}
    (hc : SmoothCoefficients U c) (hd : SmoothCoefficients U d) : SmoothCoefficients U (c - d) :=
  fun j => (hc j).sub (hd j)

theorem SmoothCoefficients.mul {U : Set D} {c d : Coefficients D}
    (hc : SmoothCoefficients U c) (hd : SmoothCoefficients U d) : SmoothCoefficients U (c * d) := by
  intro j
  have he : (c * d) j = fun x => ∑ i ∈ c.support, c i x * d (j - i) x := by
    funext x
    exact HarmonicFields.convolution_apply c d j x
  rw [he]
  exact ContDiffOn.sum (fun i _ => (hc i).mul (hd (j - i)))

theorem smoothCoefficients_constant {U : Set D} {f : D → ℂ}
    (hf : ContDiffOn ℝ ∞ f U) : SmoothCoefficients U (constantCoefficient f) := by
  intro j
  by_cases hj : j = 0
  · simpa [constantCoefficient, hj] using hf
  · change ContDiffOn ℝ ∞ ((Finsupp.single (0 : ℤ) f) j) U
    rw [Finsupp.single_eq_of_ne hj]
    exact contDiffOn_const

theorem SmoothCoefficients.differentiate {U : Set D} (hU : IsOpen U)
    {V : D → D} {Φ : D → ℝ} (hV : ContDiffOn ℝ ∞ V U) (hΦ : ContDiffOn ℝ ∞ Φ U)
    (k : ℝ) {c : Coefficients D} (hc : SmoothCoefficients U c) :
    SmoothCoefficients U (differentiate V k Φ c) :=
  fun j => derivativeCoefficient_contDiffOn hU hV hΦ (hc j) k j

theorem SmoothCoefficients.angular {U : Set D} {c : Coefficients D}
    (hc : SmoothCoefficients U c) (kp : ℤ) : SmoothCoefficients U (angularDifferentiate kp c) :=
  fun j => contDiffOn_const.mul (hc j)

omit [NormedAddCommGroup D] [NormedSpace ℝ D] in
@[simp] theorem field_add (c d : Coefficients D) (k : ℝ) (Φ : D → ℝ) (kp : ℤ) (p : D × ℝ) :
    field (c + d) k Φ kp p = field c k Φ kp p + field d k Φ kp p :=
  evaluate_add c d p.1 _

omit [NormedAddCommGroup D] [NormedSpace ℝ D] in
@[simp] theorem field_zero (k : ℝ) (Φ : D → ℝ) (kp : ℤ) (p : D × ℝ) :
    field (0 : Coefficients D) k Φ kp p = 0 := evaluate_zero _ _

omit [NormedAddCommGroup D] [NormedSpace ℝ D] in
@[simp] theorem field_neg (c : Coefficients D) (k : ℝ) (Φ : D → ℝ) (kp : ℤ) (p : D × ℝ) :
    field (-c) k Φ kp p = -field c k Φ kp p := (evaluateHom p.1 _).map_neg c

omit [NormedAddCommGroup D] [NormedSpace ℝ D] in
@[simp] theorem field_sub (c d : Coefficients D) (k : ℝ) (Φ : D → ℝ) (kp : ℤ) (p : D × ℝ) :
    field (c - d) k Φ kp p = field c k Φ kp p - field d k Φ kp p := (evaluateHom p.1 _).map_sub c d

omit [NormedAddCommGroup D] [NormedSpace ℝ D] in
@[simp] theorem field_constant (f : D → ℂ) (k : ℝ) (Φ : D → ℝ) (kp : ℤ) (p : D × ℝ) :
    field (constantCoefficient f) k Φ kp p = f p.1 := by
  unfold field constantCoefficient
  rw [evaluate_single, character_zero, mul_one]

theorem field_smoothOn {U : Set D} {c : Coefficients D} (hc : SmoothCoefficients U c)
    {Φ : D → ℝ} (hΦ : ContDiffOn ℝ ∞ Φ U) (k : ℝ) (kp : ℤ) :
    ContDiffOn ℝ ∞ (field c k Φ kp) (liftDomain U) := by
  have hfst : MapsTo (Prod.fst : D × ℝ → D) (liftDomain U) U := fun _ hp => hp.1
  have hphase : ContDiffOn ℝ ∞ (fun p : D × ℝ => k * Φ p.1 + (kp : ℝ) * p.2) (liftDomain U) :=
    (contDiffOn_const.mul (hΦ.comp contDiffOn_fst hfst)).add
      (contDiffOn_const.mul contDiffOn_snd)
  unfold field evaluate HarmonicFields.Coefficients.sum Finsupp.sum
  apply ContDiffOn.sum
  intro j _
  apply ((hc j).comp contDiffOn_fst hfst).mul
  unfold character
  exact ((contDiffOn_const.mul (Complex.ofRealCLM.contDiff.comp_contDiffOn hphase)).mul
    contDiffOn_const).cexp

theorem along_liftDirection {f : D × ℝ → ℂ} {x : D} {θ : ℝ}
    (hf : DifferentiableAt ℝ f (x, θ)) (V : D → D) :
    along (liftDirection V) f (x, θ) = along V (fun y => f (y, θ)) x := by
  have hi : HasFDerivAt (fun y : D => (y, θ))
      ((ContinuousLinearMap.id ℝ D).prod (0 : D →L[ℝ] ℝ)) x :=
    (hasFDerivAt_id x).prodMk (hasFDerivAt_const θ x)
  have hd := hf.hasFDerivAt.comp x hi
  simp only [Function.comp_def] at hd
  unfold along liftDirection
  rw [hd.fderiv]
  rfl

theorem along_angularDirection {f : D × ℝ → ℂ} {x : D} {θ : ℝ}
    (hf : DifferentiableAt ℝ f (x, θ)) :
    along angularDirection f (x, θ) = deriv (fun t => f (x, t)) θ := by
  have hi : HasDerivAt (fun t : ℝ => (x, t)) (0, 1) θ :=
    (hasDerivAt_const θ x).prodMk (hasDerivAt_id θ)
  have hd := hf.hasFDerivAt.comp_hasDerivAt θ hi
  exact hd.deriv.symm

theorem field_differentiate {U : Set D} (hU : IsOpen U) {c : Coefficients D}
    (hc : SmoothCoefficients U c) {Φ : D → ℝ} (hΦ : ContDiffOn ℝ ∞ Φ U)
    (V : D → D) (k : ℝ) (kp : ℤ) {p : D × ℝ} (hp : p ∈ liftDomain U) :
    field (differentiate V k Φ c) k Φ kp p = along (liftDirection V) (field c k Φ kp) p := by
  rcases p with ⟨x, θ⟩
  have hd := ((field_smoothOn hc hΦ k kp).contDiffAt ((liftDomain_open hU).mem_nhds
    hp)).differentiableAt (by simp)
  rw [along_liftDirection hd]
  exact (along_field_slow V k Φ kp c θ
    ((hΦ.contDiffAt (hU.mem_nhds hp.1)).differentiableAt (by simp))
    (fun j _ => ((hc j).contDiffAt (hU.mem_nhds hp.1)).differentiableAt (by simp))).symm

theorem field_angularDifferentiate {U : Set D} (hU : IsOpen U) {c : Coefficients D}
    (hc : SmoothCoefficients U c) {Φ : D → ℝ} (hΦ : ContDiffOn ℝ ∞ Φ U)
    (k : ℝ) (kp : ℤ) {p : D × ℝ} (hp : p ∈ liftDomain U) :
    field (angularDifferentiate kp c) k Φ kp p = along angularDirection (field c k Φ kp) p := by
  rcases p with ⟨x, θ⟩
  have hd := ((field_smoothOn hc hΦ k kp).contDiffAt ((liftDomain_open hU).mem_nhds
    hp)).differentiableAt (by simp)
  rw [along_angularDirection hd]
  exact (field_hasDerivAt_angle c k Φ kp x θ).deriv.symm

/-- The directions and the cylindrical radius of one normalized graph. -/
structure Frame (D : Type) where
  radius : D → ℝ
  radial : D → D
  axial : D → D
  time : D → D
  viscosity : ℝ

noncomputable def vectorField (a : VectorCoefficients D) (k : ℝ) (Φ : D → ℝ)
    (kp : ℤ) (p : D × ℝ) : ComplexVector := fun i => field (a i) k Φ kp p

noncomputable def rotate (a : VectorCoefficients D) : VectorCoefficients D := ![-a 1, a 0, 0]

omit [NormedAddCommGroup D] [NormedSpace ℝ D] in
@[simp] theorem vectorField_rotate (a : VectorCoefficients D) (k : ℝ) (Φ : D → ℝ)
    (kp : ℤ) (p : D × ℝ) :
    vectorField (rotate a) k Φ kp p = angularGenerator (vectorField a k Φ kp p) := by
  ext i
  fin_cases i <;> simp [vectorField, rotate, angularGenerator]

noncomputable def scalarLaplacian (g : Frame D) (k : ℝ) (Φ : D → ℝ) (kp : ℤ)
    (c : Coefficients D) : Coefficients D :=
  differentiate g.radial k Φ (differentiate g.radial k Φ c) +
    constantCoefficient (fun x => ((g.radius x)⁻¹ : ℝ) : D → ℂ) * differentiate g.radial k Φ c +
    constantCoefficient (fun x => (((g.radius x) ^ 2)⁻¹ : ℝ) : D → ℂ) *
      angularDifferentiate kp (angularDifferentiate kp c) +
    differentiate g.axial k Φ (differentiate g.axial k Φ c)

noncomputable def vectorLaplacian (g : Frame D) (k : ℝ) (Φ : D → ℝ) (kp : ℤ)
    (a : VectorCoefficients D) : VectorCoefficients D := fun i =>
  scalarLaplacian g k Φ kp (a i) +
    constantCoefficient (fun x => (((g.radius x) ^ 2)⁻¹ : ℝ) : D → ℂ) *
      (constantCoefficient (fun _ : D => (2 : ℂ)) * rotate (fun j => angularDifferentiate kp (a j))
        i +
        rotate (rotate a) i)

noncomputable def transport (g : Frame D) (k : ℝ) (Φ : D → ℝ) (kp : ℤ)
    (a b : VectorCoefficients D) : VectorCoefficients D := fun i =>
  a 0 * differentiate g.radial k Φ (b i) +
    (a 1 * constantCoefficient (fun x => ((g.radius x : ℂ)⁻¹))) *
      (angularDifferentiate kp (b i) + rotate b i) +
    a 2 * differentiate g.axial k Φ (b i)

noncomputable def gradient (g : Frame D) (k : ℝ) (Φ : D → ℝ) (kp : ℤ)
    (p : Coefficients D) : VectorCoefficients D :=
  ![differentiate g.radial k Φ p,
    constantCoefficient (fun x => ((g.radius x)⁻¹ : ℝ) : D → ℂ) * angularDifferentiate kp p,
    differentiate g.axial k Φ p]

/-- Literal coefficient formula for the differentiated linearized PDE. -/
noncomputable def linearResidual (g : Frame D) (k : ℝ) (Φ : D → ℝ) (kp : ℤ)
    (B a : VectorCoefficients D) (p : Coefficients D) : VectorCoefficients D := fun i =>
  differentiate g.time k Φ (a i) + transport g k Φ kp B a i + transport g k Φ kp a B i +
    gradient g k Φ kp p i -
    constantCoefficient (fun _ : D => (g.viscosity : ℂ)) * vectorLaplacian g k Φ kp a i

noncomputable def nonlinearResidual (g : Frame D) (k : ℝ) (Φ : D → ℝ) (kp : ℤ)
    (B a : VectorCoefficients D) (p : Coefficients D) : VectorCoefficients D := fun i =>
  linearResidual g k Φ kp B a p i + transport g k Φ kp a a i

theorem field_secondDerivative {U : Set D} (hU : IsOpen U) {c : Coefficients D}
    (hc : SmoothCoefficients U c) {Φ : D → ℝ} (hΦ : ContDiffOn ℝ ∞ Φ U)
    {V : D → D} (hV : ContDiffOn ℝ ∞ V U) (k : ℝ) (kp : ℤ)
    {p : D × ℝ} (hp : p ∈ liftDomain U) :
    field (differentiate V k Φ (differentiate V k Φ c)) k Φ kp p =
      along (liftDirection V) (along (liftDirection V) (field c k Φ kp)) p := by
  rw [field_differentiate hU (hc.differentiate hU hV hΦ k) hΦ V k kp hp]
  exact along_congr (liftDomain_open hU)
    (fun _ hy => field_differentiate hU hc hΦ V k kp hy) hp

theorem field_secondAngular {U : Set D} (hU : IsOpen U) {c : Coefficients D}
    (hc : SmoothCoefficients U c) {Φ : D → ℝ} (hΦ : ContDiffOn ℝ ∞ Φ U)
    (k : ℝ) (kp : ℤ) {p : D × ℝ} (hp : p ∈ liftDomain U) :
    field (angularDifferentiate kp (angularDifferentiate kp c)) k Φ kp p =
      along angularDirection (along angularDirection (field c k Φ kp)) p := by
  rw [field_angularDifferentiate hU (hc.angular kp) hΦ k kp hp]
  exact along_congr (liftDomain_open hU)
    (fun _ hy => field_angularDifferentiate hU hc hΦ k kp hy) hp

theorem field_scalarLaplacian {U : Set D} (hU : IsOpen U) (g : Frame D)
    (hr : ContDiffOn ℝ ∞ g.radial U) (hz : ContDiffOn ℝ ∞ g.axial U)
    {c : Coefficients D} (hc : SmoothCoefficients U c)
    {Φ : D → ℝ} (hΦ : ContDiffOn ℝ ∞ Φ U) (k : ℝ) (kp : ℤ)
    {p : D × ℝ} (hp : p ∈ liftDomain U) :
    field (scalarLaplacian g k Φ kp c) k Φ kp p =
      cylindricalLaplacian (fun q => g.radius q.1) (liftDirection g.radial)
        angularDirection (liftDirection g.axial) (field c k Φ kp) p := by
  simp only [scalarLaplacian, field_add, HarmonicFields.field_mul, field_constant,
    field_secondDerivative hU hc hΦ hr k kp hp,
    field_secondDerivative hU hc hΦ hz k kp hp,
    field_differentiate hU hc hΦ g.radial k kp hp,
    field_secondAngular hU hc hΦ k kp hp, cylindricalLaplacian, Complex.real_smul]

theorem field_vectorLaplacian {U : Set D} (hU : IsOpen U) (g : Frame D)
    (hr : ContDiffOn ℝ ∞ g.radial U) (hz : ContDiffOn ℝ ∞ g.axial U)
    {a : VectorCoefficients D} (ha : ∀ i, SmoothCoefficients U (a i))
    {Φ : D → ℝ} (hΦ : ContDiffOn ℝ ∞ Φ U) (k : ℝ) (kp : ℤ)
    {p : D × ℝ} (hp : p ∈ liftDomain U) :
    vectorField (vectorLaplacian g k Φ kp a) k Φ kp p =
      cylindricalVectorLaplacian (fun q => g.radius q.1) (liftDirection g.radial)
        angularDirection (liftDirection g.axial) (vectorField a k Φ kp) p := by
  have hang : vectorField (fun i => angularDifferentiate kp (a i)) k Φ kp p =
      fun i => along angularDirection (fun q => vectorField a k Φ kp q i) p := by
    ext i
    exact field_angularDifferentiate hU (ha i) hΦ k kp hp
  ext i
  change field (vectorLaplacian g k Φ kp a i) k Φ kp p = _
  simp only [vectorLaplacian, field_add, HarmonicFields.field_mul, field_constant]
  rw [field_scalarLaplacian hU g hr hz (ha i) hΦ k kp hp]
  change _ + _ * ((2 : ℂ) * vectorField (rotate _) k Φ kp p i +
    vectorField (rotate (rotate a)) k Φ kp p i) = _
  rw [vectorField_rotate, vectorField_rotate, vectorField_rotate, hang]
  rfl

theorem field_transport {U : Set D} (hU : IsOpen U) (g : Frame D)
    (a : VectorCoefficients D) {b : VectorCoefficients D}
    (hb : ∀ i, SmoothCoefficients U (b i))
    {Φ : D → ℝ} (hΦ : ContDiffOn ℝ ∞ Φ U) (k : ℝ) (kp : ℤ)
    {p : D × ℝ} (hp : p ∈ liftDomain U) :
    vectorField (transport g k Φ kp a b) k Φ kp p =
      LinearWaveResidual.transport (fun q => g.radius q.1) (liftDirection g.radial)
        angularDirection (liftDirection g.axial) (vectorField a k Φ kp)
          (vectorField b k Φ kp) p := by
  ext i
  change field (transport g k Φ kp a b i) k Φ kp p = _
  simp only [transport, field_add, HarmonicFields.field_mul, field_constant,
    field_differentiate hU (hb i) hΦ g.radial k kp hp,
    field_differentiate hU (hb i) hΦ g.axial k kp hp,
    field_angularDifferentiate hU (hb i) hΦ k kp hp]
  change _ + (_ * _) * (_ + vectorField (rotate b) k Φ kp p i) + _ = _
  rw [vectorField_rotate]
  rfl

theorem field_gradient {U : Set D} (hU : IsOpen U) (g : Frame D)
    {c : Coefficients D} (hc : SmoothCoefficients U c)
    {Φ : D → ℝ} (hΦ : ContDiffOn ℝ ∞ Φ U) (k : ℝ) (kp : ℤ)
    {p : D × ℝ} (hp : p ∈ liftDomain U) :
    vectorField (gradient g k Φ kp c) k Φ kp p =
      LinearWaveResidual.gradient (fun q => g.radius q.1) (liftDirection g.radial)
        angularDirection (liftDirection g.axial) (field c k Φ kp) p := by
  ext i
  fin_cases i <;> simp [gradient, vectorField, LinearWaveResidual.gradient,
    HarmonicFields.field_mul, field_differentiate hU hc hΦ _ k kp hp,
    field_angularDifferentiate hU hc hΦ k kp hp, Complex.real_smul]

theorem field_linearResidual {U : Set D} (hU : IsOpen U) (g : Frame D)
    (hr : ContDiffOn ℝ ∞ g.radial U) (hz : ContDiffOn ℝ ∞ g.axial U)
    {B a : VectorCoefficients D} (hB : ∀ i, SmoothCoefficients U (B i))
    (ha : ∀ i, SmoothCoefficients U (a i)) {c : Coefficients D} (hc : SmoothCoefficients U c)
    {Φ : D → ℝ} (hΦ : ContDiffOn ℝ ∞ Φ U) (k : ℝ) (kp : ℤ)
    {p : D × ℝ} (hp : p ∈ liftDomain U) :
    vectorField (linearResidual g k Φ kp B a c) k Φ kp p =
      LinearWaveResidual.linearResidual g.viscosity (fun q => g.radius q.1)
        (liftDirection g.radial) angularDirection (liftDirection g.axial)
        (liftDirection g.time) (vectorField B k Φ kp) (vectorField a k Φ kp)
        (field c k Φ kp) p := by
  ext i
  change field (linearResidual g k Φ kp B a c i) k Φ kp p = _
  simp only [linearResidual, field_sub, field_add, HarmonicFields.field_mul, field_constant,
    field_differentiate hU (ha i) hΦ g.time k kp hp]
  change _ + vectorField (transport _ _ _ _ _ _) k Φ kp p i +
    vectorField (transport _ _ _ _ _ _) k Φ kp p i +
    vectorField (gradient _ _ _ _ _) k Φ kp p i -
    _ * vectorField (vectorLaplacian _ _ _ _ _) k Φ kp p i = _
  rw [field_transport hU g B ha hΦ k kp hp, field_transport hU g a hB hΦ k kp hp,
    field_gradient hU g hc hΦ k kp hp, field_vectorLaplacian hU g hr hz ha hΦ k kp hp]
  rfl

theorem field_nonlinearResidual {U : Set D} (hU : IsOpen U) (g : Frame D)
    (hr : ContDiffOn ℝ ∞ g.radial U) (hz : ContDiffOn ℝ ∞ g.axial U)
    {B a : VectorCoefficients D} (hB : ∀ i, SmoothCoefficients U (B i))
    (ha : ∀ i, SmoothCoefficients U (a i)) {c : Coefficients D} (hc : SmoothCoefficients U c)
    {Φ : D → ℝ} (hΦ : ContDiffOn ℝ ∞ Φ U) (k : ℝ) (kp : ℤ)
    {p : D × ℝ} (hp : p ∈ liftDomain U) :
    vectorField (nonlinearResidual g k Φ kp B a c) k Φ kp p =
      LinearWaveResidual.linearResidual g.viscosity (fun q => g.radius q.1)
        (liftDirection g.radial) angularDirection (liftDirection g.axial)
        (liftDirection g.time) (vectorField B k Φ kp) (vectorField a k Φ kp)
        (field c k Φ kp) p +
      LinearWaveResidual.transport (fun q => g.radius q.1) (liftDirection g.radial)
        angularDirection (liftDirection g.axial) (vectorField a k Φ kp) (vectorField a k Φ kp) p :=
          by
  ext i
  change field (linearResidual _ _ _ _ _ _ _ i + transport _ _ _ _ _ _ i) _ _ _ _ = _
  rw [field_add]
  exact congrFun (congrArg₂ (· + ·) (field_linearResidual hU g hr hz hB ha hc hΦ k kp hp)
    (field_transport hU g a ha hΦ k kp hp)) i

/-! ## Reality, actual extraction, and harmonic values -/

omit [NormedAddCommGroup D] [NormedSpace ℝ D] in
theorem band_zero (N : ℕ) : BandLimited (0 : Coefficients D) N := by
  intro j hj
  simp at hj

omit [NormedAddCommGroup D] [NormedSpace ℝ D] in
theorem band_neg {c : Coefficients D} {N : ℕ} (hc : BandLimited c N) :
    BandLimited (-c) N := by
  intro j hj
  have hj' : j ∈ (-c.coeff).support := hj
  rw [Finsupp.support_neg] at hj'
  exact hc j hj'

omit [NormedAddCommGroup D] [NormedSpace ℝ D] in
theorem band_sub {c d : Coefficients D} {N : ℕ} (hc : BandLimited c N)
    (hd : BandLimited d N) : BandLimited (c - d) N := by
  simpa only [sub_eq_add_neg] using hc.add (band_neg hd)

omit [NormedAddCommGroup D] [NormedSpace ℝ D] in
theorem band_constant_mul (f : D → ℂ) {c : Coefficients D} {N : ℕ}
    (hc : BandLimited c N) : BandLimited (constantCoefficient f * c) N := by
  simpa only [zero_add] using (band_constantCoefficient f).mul hc

omit [NormedAddCommGroup D] [NormedSpace ℝ D] in
theorem band_mul_constant {c : Coefficients D} {N : ℕ}
    (hc : BandLimited c N) (f : D → ℂ) : BandLimited (c * constantCoefficient f) N := by
  simpa only [add_zero] using hc.mul (band_constantCoefficient f)

omit [NormedAddCommGroup D] [NormedSpace ℝ D] in
theorem band_rotate {a : VectorCoefficients D} {N : ℕ} (ha : ∀ i, BandLimited (a i) N) :
    ∀ i, BandLimited (rotate a i) N := by
  intro i
  fin_cases i
  · exact band_neg (ha 1)
  · exact ha 0
  · exact band_zero N

theorem band_scalarLaplacian (g : Frame D) (k : ℝ) (Φ : D → ℝ) (kp : ℤ)
    {c : Coefficients D} {N : ℕ} (hc : BandLimited c N) :
    BandLimited (scalarLaplacian g k Φ kp c) N := by
  unfold scalarLaplacian
  exact (((hc.differentiate _ _ _).differentiate _ _ _).add
    (band_constant_mul _ (hc.differentiate _ _ _))).add
    (band_constant_mul _ ((hc.angularDifferentiate kp).angularDifferentiate kp)) |>.add
      ((hc.differentiate _ _ _).differentiate _ _ _)

theorem band_vectorLaplacian (g : Frame D) (k : ℝ) (Φ : D → ℝ) (kp : ℤ)
    {a : VectorCoefficients D} {N : ℕ} (ha : ∀ i, BandLimited (a i) N) :
    ∀ i, BandLimited (vectorLaplacian g k Φ kp a i) N := by
  intro i
  exact (band_scalarLaplacian g k Φ kp (ha i)).add
    (band_constant_mul _ ((band_constant_mul _ (band_rotate
      (fun j => (ha j).angularDifferentiate kp) i)).add (band_rotate (band_rotate ha) i)))

theorem band_transport (g : Frame D) (k : ℝ) (Φ : D → ℝ) (kp : ℤ)
    {a b : VectorCoefficients D} {M N : ℕ}
    (ha : ∀ i, BandLimited (a i) M) (hb : ∀ i, BandLimited (b i) N) :
    ∀ i, BandLimited (transport g k Φ kp a b i) (M + N) := by
  intro i
  exact (((ha 0).mul ((hb i).differentiate _ _ _)).add
    ((band_mul_constant (ha 1) _).mul (((hb i).angularDifferentiate kp).add
      (band_rotate hb i)))).add ((ha 2).mul ((hb i).differentiate _ _ _))

theorem band_gradient (g : Frame D) (k : ℝ) (Φ : D → ℝ) (kp : ℤ)
    {c : Coefficients D} {N : ℕ} (hc : BandLimited c N) :
    ∀ i, BandLimited (gradient g k Φ kp c i) N := by
  intro i
  fin_cases i
  · exact hc.differentiate _ _ _
  · exact band_constant_mul _ (hc.angularDifferentiate kp)
  · exact hc.differentiate _ _ _

theorem band_linearResidual (g : Frame D) (k : ℝ) (Φ : D → ℝ) (kp : ℤ)
    {B a : VectorCoefficients D} {c : Coefficients D} {N : ℕ}
    (hB : ∀ i, BandLimited (B i) 0) (ha : ∀ i, BandLimited (a i) N)
    (hc : BandLimited c N) : ∀ i, BandLimited (linearResidual g k Φ kp B a c i) N := by
  intro i
  have hBa : BandLimited (transport g k Φ kp B a i) N := by
    simpa only [zero_add] using band_transport g k Φ kp hB ha i
  have haB : BandLimited (transport g k Φ kp a B i) N := by
    simpa only [add_zero] using band_transport g k Φ kp ha hB i
  exact band_sub ((((ha i).differentiate _ _ _).add hBa).add haB |>.add
    (band_gradient g k Φ kp hc i))
    (band_constant_mul _ (band_vectorLaplacian g k Φ kp ha i))

/-- The bound concerns harmonic values `|j|`, not the number of terms. -/
theorem band_nonlinearResidual (g : Frame D) (k : ℝ) (Φ : D → ℝ) (kp : ℤ)
    {B a : VectorCoefficients D} {c : Coefficients D} {N : ℕ}
    (hB : ∀ i, BandLimited (B i) 0) (ha : ∀ i, BandLimited (a i) N)
    (hc : BandLimited c N) :
    ∀ i, BandLimited (nonlinearResidual g k Φ kp B a c i) (N + N) := by
  intro i
  exact ((band_linearResidual g k Φ kp hB ha hc i).mono (Nat.le_add_right _ _)).add
    (band_transport g k Φ kp ha ha i)

omit [NormedAddCommGroup D] [NormedSpace ℝ D] in
theorem band_conjugateReverse {c : Coefficients D} {N : ℕ} (hc : BandLimited c N) :
    BandLimited (conjugateReverse c) N := by
  intro j hj
  have hj' : -j ∈ c.support := by
    by_contra hh
    have he : c (-j) = 0 := Finsupp.notMem_support_iff.mp hh
    apply (Finsupp.mem_support_iff.mp hj)
    ext x
    simp [he]
  simpa only [Int.natAbs_neg] using hc (-j) hj'

/-- Canonical real projection, with exactly the conjugate negative harmonics. -/
noncomputable def realCoefficients (c : Coefficients D) : Coefficients D :=
  constantCoefficient (fun _ : D => (2 : ℂ)⁻¹) * (c + conjugateReverse c)

omit [NormedAddCommGroup D] [NormedSpace ℝ D] in
@[simp] theorem realCoefficients_apply (c : Coefficients D) (j : ℤ) (x : D) :
    realCoefficients c j x = (2 : ℂ)⁻¹ * (c j x + conj (c (-j) x)) := by
  rw [realCoefficients, constantCoefficient, AddMonoidAlgebra.coeff_single_zero_mul]
  rfl

omit [NormedAddCommGroup D] [NormedSpace ℝ D] in
theorem realCoefficients_conjugate (c : Coefficients D) :
    ConjugateSymmetric (realCoefficients c) := by
  intro j x
  have htwo : conj (2 : ℂ) = (2 : ℂ) := Complex.conj_ofReal 2
  simp [realCoefficients_apply, map_mul, map_add, htwo, add_comm]

omit [NormedAddCommGroup D] [NormedSpace ℝ D] in
theorem realCoefficients_eq_self {c : Coefficients D} (hc : ConjugateSymmetric c) :
    realCoefficients c = c := by
  ext j x
  rw [realCoefficients_apply, hc j x]
  simp
  ring

omit [NormedAddCommGroup D] [NormedSpace ℝ D] in
theorem field_realCoefficients (c : Coefficients D) (k : ℝ) (Φ : D → ℝ)
    (kp : ℤ) (p : D × ℝ) :
    field (realCoefficients c) k Φ kp p = ((field c k Φ kp p).re : ℂ) := by
  simp only [realCoefficients, HarmonicFields.field_mul, field_constant, field_add]
  rw [show field (conjugateReverse c) k Φ kp p = conj (field c k Φ kp p) from
    evaluate_conjugateReverse c p.1 _]
  rw [Complex.add_conj]
  push_cast
  ring

omit [NormedAddCommGroup D] [NormedSpace ℝ D] in
theorem band_realCoefficients {c : Coefficients D} {N : ℕ} (hc : BandLimited c N) :
    BandLimited (realCoefficients c) N :=
  band_constant_mul _ (hc.add (band_conjugateReverse hc))

theorem SmoothCoefficients.conjugateReverse {U : Set D} {c : Coefficients D}
    (hc : SmoothCoefficients U c) : SmoothCoefficients U (conjugateReverse c) :=
  fun j => Complex.conjCLE.contDiff.comp_contDiffOn (hc (-j))

theorem SmoothCoefficients.realCoefficients {U : Set D} {c : Coefficients D}
    (hc : SmoothCoefficients U c) : SmoothCoefficients U (realCoefficients c) :=
  (smoothCoefficients_constant contDiffOn_const).mul (hc.add hc.conjugateReverse)

/-- Extraction is integration against the conjugate carrier, including its slow phase. -/
noncomputable def extract (f : D × ℝ → ℂ) (k : ℝ) (Φ : D → ℝ) (kp j : ℤ)
    (x : D) : ℂ :=
  angularMean (fun θ => f (x, θ) *
    field (AddMonoidAlgebra.single (-j) (fun _ : D => (1 : ℂ))) k Φ kp (x, θ))

omit [NormedAddCommGroup D] [NormedSpace ℝ D] in
theorem extract_field (c : Coefficients D) (k : ℝ) (Φ : D → ℝ)
    {kp : ℤ} (hkp : kp ≠ 0) (j : ℤ) (x : D) :
    extract (field c k Φ kp) k Φ kp j x = c j x := by
  unfold extract
  simp_rw [← HarmonicFields.field_mul]
  rw [angularMean_field _ k Φ hkp x]
  change (c * AddMonoidAlgebra.single (-j) (fun _ : D => (1 : ℂ))).coeff 0 x = _
  rw [AddMonoidAlgebra.coeff_mul_single_apply]
  simp

omit [NormedAddCommGroup D] [NormedSpace ℝ D] in
/-- For a nonzero angular frequency the coefficients are uniquely determined by the field. -/
theorem coefficients_unique {c d : Coefficients D} (k : ℝ) (Φ : D → ℝ)
    {kp : ℤ} (hkp : kp ≠ 0) (he : field c k Φ kp = field d k Φ kp) : c = d := by
  ext j x
  rw [← extract_field c k Φ hkp j x, he, extract_field d k Φ hkp j x]

noncomputable def nonconstant (c : Coefficients D) : Coefficients D := c.erase 0

omit [NormedAddCommGroup D] [NormedSpace ℝ D] in
theorem nonconstant_eq_sub (c : Coefficients D) :
    nonconstant c = c - constantCoefficient (c 0) := by
  ext j x
  change c.erase 0 j x = c j x - Finsupp.single 0 (c 0) j x
  by_cases hj : j = 0
  · subst j
    simp []
  · simp [ Finsupp.erase_ne hj,
      hj]

omit [NormedAddCommGroup D] [NormedSpace ℝ D] in
theorem field_nonconstant (c : Coefficients D) (k : ℝ) (Φ : D → ℝ)
    (kp : ℤ) (p : D × ℝ) :
    field (nonconstant c) k Φ kp p = field c k Φ kp p - c 0 p.1 := by
  rw [nonconstant_eq_sub, field_sub, field_constant]

omit [NormedAddCommGroup D] [NormedSpace ℝ D] in
theorem angularMean_nonconstant (c : Coefficients D) (k : ℝ) (Φ : D → ℝ)
    {kp : ℤ} (hkp : kp ≠ 0) (x : D) :
    angularMean (fun θ => field (nonconstant c) k Φ kp (x, θ)) = 0 := by
  rw [angularMean_field _ k Φ hkp x]
  simp [nonconstant]

omit [NormedAddCommGroup D] [NormedSpace ℝ D] in
theorem nonconstant_conjugate {c : Coefficients D} (hc : ConjugateSymmetric c) :
    ConjugateSymmetric (nonconstant c) := by
  intro j x
  by_cases hj : j = 0
  · simp [nonconstant, hj]
  · simp [nonconstant, Finsupp.erase_ne hj, Finsupp.erase_ne (neg_ne_zero.mpr hj), hc j x]

omit [NormedAddCommGroup D] [NormedSpace ℝ D] in
theorem band_nonconstant {c : Coefficients D} {N : ℕ} (hc : BandLimited c N) :
    BandLimited (nonconstant c) N := by
  intro j hj
  exact hc j ((Finset.mem_erase.mp (show j ∈ c.support.erase 0 by
    simpa only [nonconstant, HarmonicFields.Coefficients.support, AddMonoidAlgebra.coeff_erase,
      Finsupp.support_erase] using hj)).2)

omit [NormedAddCommGroup D] [NormedSpace ℝ D] in
theorem nonconstant_support {c : Coefficients D} {j : ℤ}
    (hj : j ∈ (nonconstant c).support) : j ≠ 0 := by
  exact (Finset.mem_erase.mp (show j ∈ c.support.erase 0 by
    simpa only [nonconstant, HarmonicFields.Coefficients.support, AddMonoidAlgebra.coeff_erase,
      Finsupp.support_erase] using hj)).1

theorem SmoothCoefficients.nonconstant {U : Set D} {c : Coefficients D}
    (hc : SmoothCoefficients U c) : SmoothCoefficients U (nonconstant c) := by
  rw [nonconstant_eq_sub]
  exact hc.sub (smoothCoefficients_constant (hc 0))

namespace Actual

theorem angularGenerator_add (a b : ComplexVector) :
    angularGenerator (a + b) = angularGenerator a + angularGenerator b := by
  ext i
  fin_cases i <;> simp [angularGenerator]
  abel

theorem transport_add_left (R : D → ℝ) (Vr Vθ Vz : D → D)
    (a b v : D → ComplexVector) (x : D) :
    LinearWaveResidual.transport R Vr Vθ Vz (a + b) v x =
      LinearWaveResidual.transport R Vr Vθ Vz a v x + LinearWaveResidual.transport R Vr Vθ Vz b v x
        := by
  ext i
  simp only [LinearWaveResidual.transport, Pi.add_apply]
  ring

theorem transport_add_right (R : D → ℝ) (Vr Vθ Vz : D → D)
    (u a b : D → ComplexVector) {x : D}
    (ha : ∀ i, DifferentiableAt ℝ (fun y => a y i) x)
    (hb : ∀ i, DifferentiableAt ℝ (fun y => b y i) x) :
    LinearWaveResidual.transport R Vr Vθ Vz u (a + b) x =
      LinearWaveResidual.transport R Vr Vθ Vz u a x + LinearWaveResidual.transport R Vr Vθ Vz u b x
        := by
  ext i
  simp only [LinearWaveResidual.transport, Pi.add_apply, angularGenerator_add,
    along_add _ (ha i) (hb i)]
  ring

theorem twiceAlong_add {U : Set D} (hU : IsOpen U) {V : D → D}
    (hV : ContDiffOn ℝ ∞ V U) {f g : D → ℂ}
    (hf : ContDiffOn ℝ ∞ f U) (hg : ContDiffOn ℝ ∞ g U)
    {x : D} (hx : x ∈ U) :
    along V (along V (f + g)) x = along V (along V f) x + along V (along V g) x := by
  have heq : EqOn (along V (f + g)) (along V f + along V g) U := by
    intro y hy
    exact along_add V ((hf.contDiffAt (hU.mem_nhds hy)).differentiableAt (by simp))
      ((hg.contDiffAt (hU.mem_nhds hy)).differentiableAt (by simp))
  rw [along_congr hU heq hx]
  exact along_add V
    (((contDiffOn_along hU hV hf).contDiffAt (hU.mem_nhds hx)).differentiableAt (by simp))
    (((contDiffOn_along hU hV hg).contDiffAt (hU.mem_nhds hx)).differentiableAt (by simp))

theorem cylindricalLaplacian_add {U : Set D} (hU : IsOpen U) (R : D → ℝ)
    {Vr Vθ Vz : D → D} (hr : ContDiffOn ℝ ∞ Vr U)
    (hθ : ContDiffOn ℝ ∞ Vθ U) (hz : ContDiffOn ℝ ∞ Vz U)
    {f g : D → ℂ} (hf : ContDiffOn ℝ ∞ f U) (hg : ContDiffOn ℝ ∞ g U)
    {x : D} (hx : x ∈ U) :
    cylindricalLaplacian R Vr Vθ Vz (f + g) x =
      cylindricalLaplacian R Vr Vθ Vz f x + cylindricalLaplacian R Vr Vθ Vz g x := by
  have df := (hf.contDiffAt (hU.mem_nhds hx)).differentiableAt (by simp)
  have dg := (hg.contDiffAt (hU.mem_nhds hx)).differentiableAt (by simp)
  have hfirst : along Vr (f + g) x = along Vr f x + along Vr g x := along_add Vr df dg
  simp only [cylindricalLaplacian, twiceAlong_add hU hr hf hg hx,
    twiceAlong_add hU hθ hf hg hx, twiceAlong_add hU hz hf hg hx,
    hfirst, smul_add]
  abel

theorem cylindricalVectorLaplacian_add {U : Set D} (hU : IsOpen U) (R : D → ℝ)
    {Vr Vθ Vz : D → D} (hr : ContDiffOn ℝ ∞ Vr U)
    (hθ : ContDiffOn ℝ ∞ Vθ U) (hz : ContDiffOn ℝ ∞ Vz U)
    {a b : D → ComplexVector}
    (ha : ∀ i, ContDiffOn ℝ ∞ (fun y => a y i) U)
    (hb : ∀ i, ContDiffOn ℝ ∞ (fun y => b y i) U)
    {x : D} (hx : x ∈ U) :
    cylindricalVectorLaplacian R Vr Vθ Vz (a + b) x =
      cylindricalVectorLaplacian R Vr Vθ Vz a x +
        cylindricalVectorLaplacian R Vr Vθ Vz b x := by
  have hL i : cylindricalLaplacian R Vr Vθ Vz (fun y => a y i + b y i) x =
      cylindricalLaplacian R Vr Vθ Vz (fun y => a y i) x +
        cylindricalLaplacian R Vr Vθ Vz (fun y => b y i) x :=
    cylindricalLaplacian_add hU R hr hθ hz (ha i) (hb i) hx
  have hD i := along_add Vθ
    (((ha i).contDiffAt (hU.mem_nhds hx)).differentiableAt (by simp))
    (((hb i).contDiffAt (hU.mem_nhds hx)).differentiableAt (by simp))
  ext i
  fin_cases i <;>
    simp [cylindricalVectorLaplacian, angularGenerator, hL 0, hL 1, hL 2,
      hD 0, hD 1, Complex.real_smul] <;> ring

theorem gradient_add (R : D → ℝ) (Vr Vθ Vz : D → D)
    {p q : D → ℂ} {x : D} (hp : DifferentiableAt ℝ p x)
    (hq : DifferentiableAt ℝ q x) :
      LinearWaveResidual.gradient R Vr Vθ Vz (p + q) x = LinearWaveResidual.gradient R Vr Vθ Vz p x
        + LinearWaveResidual.gradient R Vr Vθ Vz q x := by
  have hd (V : D → D) : along V (p + q) x = along V p x + along V q x := along_add V hp hq
  ext i
  fin_cases i <;> simp [LinearWaveResidual.gradient, hd, smul_add]

theorem linearResidual_add {U : Set D} (hU : IsOpen U) (ε : ℝ) (R : D → ℝ)
    {Vr Vθ Vz : D → D} (Vt : D → D) (hr : ContDiffOn ℝ ∞ Vr U)
    (hθ : ContDiffOn ℝ ∞ Vθ U) (hz : ContDiffOn ℝ ∞ Vz U)
    (B a b : D → ComplexVector) (p q : D → ℂ)
    (ha : ∀ i, ContDiffOn ℝ ∞ (fun y => a y i) U)
    (hb : ∀ i, ContDiffOn ℝ ∞ (fun y => b y i) U)
    (hp : ContDiffOn ℝ ∞ p U) (hq : ContDiffOn ℝ ∞ q U)
    {x : D} (hx : x ∈ U) :
    LinearWaveResidual.linearResidual ε R Vr Vθ Vz Vt B (a + b) (p + q) x =
      LinearWaveResidual.linearResidual ε R Vr Vθ Vz Vt B a p x + LinearWaveResidual.linearResidual
        ε R Vr Vθ Vz Vt B b q x := by
  have da i := ((ha i).contDiffAt (hU.mem_nhds hx)).differentiableAt (by simp)
  have db i := ((hb i).contDiffAt (hU.mem_nhds hx)).differentiableAt (by simp)
  have dp := (hp.contDiffAt (hU.mem_nhds hx)).differentiableAt (by simp)
  have dq := (hq.contDiffAt (hU.mem_nhds hx)).differentiableAt (by simp)
  have hL := cylindricalVectorLaplacian_add hU R hr hθ hz ha hb hx
  ext i
  simp only [LinearWaveResidual.linearResidual, Pi.add_apply, along_add _ (da i) (db i),
    transport_add_left, transport_add_right R Vr Vθ Vz B a b da db,
    gradient_add R Vr Vθ Vz dp dq, hL]
  ring

/-- Exact residual of a perturbation of a fixed base, before the virtual
stress and the separately retained base residual are added. -/
noncomputable def nonlinearResidual (ε : ℝ) (R : D → ℝ) (Vr Vθ Vz Vt : D → D)
    (B a : D → ComplexVector) (p : D → ℂ) (x : D) : ComplexVector :=
  LinearWaveResidual.linearResidual ε R Vr Vθ Vz Vt B a p x + LinearWaveResidual.transport R Vr Vθ
    Vz a a x

theorem nonlinearResidual_add_sub {U : Set D} (hU : IsOpen U) (ε : ℝ) (R : D → ℝ)
    {Vr Vθ Vz : D → D} (Vt : D → D) (hr : ContDiffOn ℝ ∞ Vr U)
    (hθ : ContDiffOn ℝ ∞ Vθ U) (hz : ContDiffOn ℝ ∞ Vz U)
    (B a b : D → ComplexVector) (p q : D → ℂ)
    (ha : ∀ i, ContDiffOn ℝ ∞ (fun y => a y i) U)
    (hb : ∀ i, ContDiffOn ℝ ∞ (fun y => b y i) U)
    (hp : ContDiffOn ℝ ∞ p U) (hq : ContDiffOn ℝ ∞ q U)
    {x : D} (hx : x ∈ U) :
    nonlinearResidual ε R Vr Vθ Vz Vt B (a + b) (p + q) x -
        nonlinearResidual ε R Vr Vθ Vz Vt B a p x =
      LinearWaveResidual.linearResidual ε R Vr Vθ Vz Vt B b q x + LinearWaveResidual.transport R Vr
        Vθ Vz a b x +
        LinearWaveResidual.transport R Vr Vθ Vz b a x + LinearWaveResidual.transport R Vr Vθ Vz b b
          x := by
  have da i := ((ha i).contDiffAt (hU.mem_nhds hx)).differentiableAt (by simp)
  have db i := ((hb i).contDiffAt (hU.mem_nhds hx)).differentiableAt (by simp)
  rw [nonlinearResidual, linearResidual_add hU ε R Vt hr hθ hz B a b p q ha hb hp hq hx,
    transport_add_left, transport_add_right R Vr Vθ Vz a a b da db,
    transport_add_right R Vr Vθ Vz b a b da db, nonlinearResidual]
  abel


theorem transport_zero_of_disjoint (R : D → ℝ) (Vr Vθ Vz : D → D)
    {u v : D → ComplexVector} (hd : Disjoint (tsupport u) (tsupport v)) (x : D) :
    LinearWaveResidual.transport R Vr Vθ Vz u v x = 0 := by
  by_cases hu : u x = 0
  · ext i
    simp [LinearWaveResidual.transport, hu]
  · have hux : x ∈ tsupport u := subset_closure (by simpa only [Function.mem_support] using hu)
    have hvx : x ∉ tsupport v := fun hx => Set.disjoint_left.mp hd hux hx
    have he : v =ᶠ[𝓝 x] 0 := notMem_tsupport_iff_eventuallyEq.mp hvx
    have hv : v x = 0 := he.eq_of_nhds
    have hvd (i : Fin 3) (V : D → D) : along V (fun y => v y i) x = 0 := by
      have hei : (fun y => v y i) =ᶠ[𝓝 x] (fun _ : D => (0 : ℂ)) :=
        he.mono (fun _ hy => congrFun hy i)
      simp only [along, hei.fderiv_eq, fderiv_fun_const, Pi.zero_apply, _root_.zero_apply]
    ext i
    fin_cases i <;> simp [LinearWaveResidual.transport, hv, hvd, angularGenerator]

theorem transport_sum_left {ι : Type*} (s : Finset ι) (R : D → ℝ) (Vr Vθ Vz : D → D)
    (u : ι → D → ComplexVector) (v : D → ComplexVector) (x : D) :
    LinearWaveResidual.transport R Vr Vθ Vz (∑ l ∈ s, u l) v x =
      ∑ l ∈ s, LinearWaveResidual.transport R Vr Vθ Vz (u l) v x := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      ext i
      simp [LinearWaveResidual.transport]
  | @insert l s hl ih =>
      rw [Finset.sum_insert hl, Finset.sum_insert hl, transport_add_left, ih]

theorem transport_sum_right {ι : Type*} (s : Finset ι) (R : D → ℝ) (Vr Vθ Vz : D → D)
    (u : D → ComplexVector) (v : ι → D → ComplexVector) {x : D}
    (hv : ∀ l ∈ s, ∀ i, DifferentiableAt ℝ (fun y => v l y i) x) :
    LinearWaveResidual.transport R Vr Vθ Vz u (∑ l ∈ s, v l) x =
      ∑ l ∈ s, LinearWaveResidual.transport R Vr Vθ Vz u (v l) x := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      ext i
      fin_cases i <;> simp [LinearWaveResidual.transport, along, angularGenerator]
  | @insert l s hl ih =>
      rw [Finset.sum_insert hl, Finset.sum_insert hl]
      have hlv := hv l (Finset.mem_insert_self l s)
      have hsv := fun j hj => hv j (Finset.mem_insert_of_mem hj)
      have hsum (i : Fin 3) : DifferentiableAt ℝ (fun y => (∑ j ∈ s, v j) y i) x := by
        simpa only [Finset.sum_apply] using DifferentiableAt.fun_sum (fun j hj => hsv j hj i)
      rw [transport_add_right R Vr Vθ Vz u (v l) _ hlv hsum, ih hsv]

theorem transport_sum_self {ι : Type*} (s : Finset ι) (R : D → ℝ) (Vr Vθ Vz : D → D)
    (u : ι → D → ComplexVector) {x : D}
    (hu : ∀ l ∈ s, ∀ i, DifferentiableAt ℝ (fun y => u l y i) x)
    (hdisj : ∀ l ∈ s, ∀ j ∈ s, l ≠ j → Disjoint (tsupport (u l)) (tsupport (u j))) :
    LinearWaveResidual.transport R Vr Vθ Vz (∑ l ∈ s, u l) (∑ l ∈ s, u l) x =
      ∑ l ∈ s, LinearWaveResidual.transport R Vr Vθ Vz (u l) (u l) x := by
  classical
  rw [transport_sum_left]
  apply Finset.sum_congr rfl
  intro l hl
  rw [transport_sum_right s R Vr Vθ Vz (u l) u hu]
  apply Finset.sum_eq_single l
  · intro j hj hjl
    exact transport_zero_of_disjoint R Vr Vθ Vz (hdisj l hl j hj (Ne.symm hjl)) x
  · exact fun h => (h hl).elim

theorem linearResidual_sum {ι : Type*} (s : Finset ι) {U : Set D} (hU : IsOpen U)
    (ε : ℝ) (R : D → ℝ) {Vr Vθ Vz : D → D} (Vt : D → D)
    (hr : ContDiffOn ℝ ∞ Vr U) (hθ : ContDiffOn ℝ ∞ Vθ U) (hz : ContDiffOn ℝ ∞ Vz U)
    (B : D → ComplexVector) (u : ι → D → ComplexVector) (p : ι → D → ℂ)
    (hu : ∀ l ∈ s, ∀ i, ContDiffOn ℝ ∞ (fun y => u l y i) U)
    (hp : ∀ l ∈ s, ContDiffOn ℝ ∞ (p l) U) {x : D} (hx : x ∈ U) :
    LinearWaveResidual.linearResidual ε R Vr Vθ Vz Vt B (∑ l ∈ s, u l) (∑ l ∈ s, p l) x =
      ∑ l ∈ s, LinearWaveResidual.linearResidual ε R Vr Vθ Vz Vt B (u l) (p l) x := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      have hzero (V : D → D) : along V (fun _ : D => (0 : ℂ)) = 0 := by
        funext y
        simp [along]
      ext i
      fin_cases i <;>
        simp [LinearWaveResidual.linearResidual, LinearWaveResidual.transport,
          LinearWaveResidual.gradient, cylindricalVectorLaplacian, cylindricalLaplacian,
          hzero, along, angularGenerator]
  | @insert l s hl ih =>
      rw [Finset.sum_insert hl, Finset.sum_insert hl, Finset.sum_insert hl]
      have hlu := hu l (Finset.mem_insert_self l s)
      have hlp := hp l (Finset.mem_insert_self l s)
      have hsu := fun j hj => hu j (Finset.mem_insert_of_mem hj)
      have hsp := fun j hj => hp j (Finset.mem_insert_of_mem hj)
      have hsum (i : Fin 3) : ContDiffOn ℝ ∞ (fun y => (∑ j ∈ s, u j) y i) U := by
        simpa only [Finset.sum_apply] using ContDiffOn.sum (fun j hj => hsu j hj i)
      have hsump : ContDiffOn ℝ ∞ (∑ j ∈ s, p j) U := by
        convert! ContDiffOn.sum hsp using 1
        ext y
        simp only [Finset.sum_apply]
      rw [linearResidual_add hU ε R Vt hr hθ hz B (u l) _ (p l) _ hlu hsum hlp
        hsump hx, ih hsu hsp]

theorem nonlinearResidual_sum {ι : Type*} (s : Finset ι) {U : Set D} (hU : IsOpen U)
    (ε : ℝ) (R : D → ℝ) {Vr Vθ Vz : D → D} (Vt : D → D)
    (hr : ContDiffOn ℝ ∞ Vr U) (hθ : ContDiffOn ℝ ∞ Vθ U) (hz : ContDiffOn ℝ ∞ Vz U)
    (B : D → ComplexVector) (u : ι → D → ComplexVector) (p : ι → D → ℂ)
    (hu : ∀ l ∈ s, ∀ i, ContDiffOn ℝ ∞ (fun y => u l y i) U)
    (hp : ∀ l ∈ s, ContDiffOn ℝ ∞ (p l) U)
    (hdisj : ∀ l ∈ s, ∀ j ∈ s, l ≠ j → Disjoint (tsupport (u l)) (tsupport (u j)))
    {x : D} (hx : x ∈ U) :
    nonlinearResidual ε R Vr Vθ Vz Vt B (∑ l ∈ s, u l) (∑ l ∈ s, p l) x =
      ∑ l ∈ s, nonlinearResidual ε R Vr Vθ Vz Vt B (u l) (p l) x := by
  unfold nonlinearResidual
  rw [linearResidual_sum s hU ε R Vt hr hθ hz B u p hu hp hx,
    transport_sum_self s R Vr Vθ Vz u (fun l hl i =>
      ((hu l hl i).contDiffAt (hU.mem_nhds hx)).differentiableAt (by simp)) hdisj,
    Finset.sum_add_distrib]

theorem linearResidual_base_add (ε : ℝ) (R : D → ℝ) (Vr Vθ Vz Vt : D → D)
    (B M a : D → ComplexVector) (p : D → ℂ) {x : D}
    (hB : ∀ i, DifferentiableAt ℝ (fun y => B y i) x)
    (hM : ∀ i, DifferentiableAt ℝ (fun y => M y i) x) :
    LinearWaveResidual.linearResidual ε R Vr Vθ Vz Vt (B + M) a p x =
      LinearWaveResidual.linearResidual ε R Vr Vθ Vz Vt B a p x +
      LinearWaveResidual.transport R Vr Vθ Vz M a x +
      LinearWaveResidual.transport R Vr Vθ Vz a M x := by
  ext i
  simp only [LinearWaveResidual.linearResidual, transport_add_left,
    transport_add_right R Vr Vθ Vz a B M hB hM, Pi.add_apply]
  ring

theorem nonlinearResidual_mean_add {U : Set D} (hU : IsOpen U)
    (ε : ℝ) (R : D → ℝ) {Vr Vθ Vz : D → D} (Vt : D → D)
    (hr : ContDiffOn ℝ ∞ Vr U) (hθ : ContDiffOn ℝ ∞ Vθ U) (hz : ContDiffOn ℝ ∞ Vz U)
    (B M a : D → ComplexVector) (p q : D → ℂ)
    (hB : ∀ i, ContDiffOn ℝ ∞ (fun y => B y i) U)
    (hM : ∀ i, ContDiffOn ℝ ∞ (fun y => M y i) U)
    (ha : ∀ i, ContDiffOn ℝ ∞ (fun y => a y i) U)
    (hp : ContDiffOn ℝ ∞ p U) (hq : ContDiffOn ℝ ∞ q U)
    {x : D} (hx : x ∈ U) :
    nonlinearResidual ε R Vr Vθ Vz Vt B (M + a) (p + q) x =
      nonlinearResidual ε R Vr Vθ Vz Vt B M p x +
      nonlinearResidual ε R Vr Vθ Vz Vt (B + M) a q x := by
  have he := nonlinearResidual_add_sub hU ε R Vt hr hθ hz B M a p q hM ha hp hq hx
  have hb := linearResidual_base_add ε R Vr Vθ Vz Vt B M a q
    (fun i => ((hB i).contDiffAt (hU.mem_nhds hx)).differentiableAt (by simp))
    (fun i => ((hM i).contDiffAt (hU.mem_nhds hx)).differentiableAt (by simp))
  have hb' : nonlinearResidual ε R Vr Vθ Vz Vt (B + M) a q x =
      LinearWaveResidual.linearResidual ε R Vr Vθ Vz Vt B a q x +
      LinearWaveResidual.transport R Vr Vθ Vz M a x +
      LinearWaveResidual.transport R Vr Vθ Vz a M x +
      LinearWaveResidual.transport R Vr Vθ Vz a a x := by
    change _ + _ = _
    rw [hb]
  rw [hb']
  ext i
  have hei := congrFun he i
  simp only [Pi.sub_apply, Pi.add_apply] at hei ⊢
  linear_combination hei

end Actual

/-- Regularity of the actual graph directions, with the cylindrical radius nonzero. -/
structure Frame.Regular (g : Frame D) (U : Set D) : Prop where
  radius : ContDiffOn ℝ ∞ g.radius U
  radius_ne : ∀ x ∈ U, g.radius x ≠ 0
  radial : ContDiffOn ℝ ∞ g.radial U
  axial : ContDiffOn ℝ ∞ g.axial U
  time : ContDiffOn ℝ ∞ g.time U

theorem liftDirection_smooth {U : Set D} {V : D → D} (hV : ContDiffOn ℝ ∞ V U) :
    ContDiffOn ℝ ∞ (liftDirection V) (liftDomain U) :=
  (hV.comp contDiffOn_fst (fun _ hp => hp.1)).prodMk contDiffOn_const

theorem smooth_rotate {U : Set D} {a : VectorCoefficients D}
    (ha : ∀ i, SmoothCoefficients U (a i)) : ∀ i, SmoothCoefficients U (rotate a i) := by
  intro i
  fin_cases i
  · exact (ha 1).neg
  · exact ha 0
  · exact smoothCoefficients_zero U

theorem Frame.Regular.invRadius {g : Frame D} {U : Set D} (hg : g.Regular U) :
    SmoothCoefficients U (constantCoefficient (fun x => ((g.radius x)⁻¹ : ℝ) : D → ℂ)) :=
  smoothCoefficients_constant (Complex.ofRealCLM.contDiff.comp_contDiffOn (hg.radius.inv
    hg.radius_ne))

theorem Frame.Regular.invSquare {g : Frame D} {U : Set D} (hg : g.Regular U) :
    SmoothCoefficients U (constantCoefficient (fun x => (((g.radius x) ^ 2)⁻¹ : ℝ) : D → ℂ)) :=
  smoothCoefficients_constant (Complex.ofRealCLM.contDiff.comp_contDiffOn
    ((hg.radius.pow 2).inv (fun x hx => pow_ne_zero 2 (hg.radius_ne x hx))))

theorem smooth_scalarLaplacian {U : Set D} (hU : IsOpen U) {g : Frame D} (hg : g.Regular U)
    {Φ : D → ℝ} (hΦ : ContDiffOn ℝ ∞ Φ U) (k : ℝ) (kp : ℤ)
    {c : Coefficients D} (hc : SmoothCoefficients U c) :
    SmoothCoefficients U (scalarLaplacian g k Φ kp c) :=
  (((hc.differentiate hU hg.radial hΦ k).differentiate hU hg.radial hΦ k).add
    (hg.invRadius.mul (hc.differentiate hU hg.radial hΦ k))).add
    (hg.invSquare.mul ((hc.angular kp).angular kp)) |>.add
    ((hc.differentiate hU hg.axial hΦ k).differentiate hU hg.axial hΦ k)

theorem smooth_vectorLaplacian {U : Set D} (hU : IsOpen U) {g : Frame D} (hg : g.Regular U)
    {Φ : D → ℝ} (hΦ : ContDiffOn ℝ ∞ Φ U) (k : ℝ) (kp : ℤ)
    {a : VectorCoefficients D} (ha : ∀ i, SmoothCoefficients U (a i)) :
    ∀ i, SmoothCoefficients U (vectorLaplacian g k Φ kp a i) := fun i =>
  (smooth_scalarLaplacian hU hg hΦ k kp (ha i)).add
    (hg.invSquare.mul (((smoothCoefficients_constant contDiffOn_const).mul
      (smooth_rotate (fun j => (ha j).angular kp) i)).add (smooth_rotate (smooth_rotate ha) i)))

theorem smooth_transport {U : Set D} (hU : IsOpen U) {g : Frame D} (hg : g.Regular U)
    {Φ : D → ℝ} (hΦ : ContDiffOn ℝ ∞ Φ U) (k : ℝ) (kp : ℤ)
    {a b : VectorCoefficients D} (ha : ∀ i, SmoothCoefficients U (a i))
    (hb : ∀ i, SmoothCoefficients U (b i)) :
    ∀ i, SmoothCoefficients U (transport g k Φ kp a b i) := by
  have hri : SmoothCoefficients U (constantCoefficient (fun x => (g.radius x : ℂ)⁻¹)) := by
    simpa only [Complex.ofReal_inv] using hg.invRadius
  intro i
  exact (((ha 0).mul ((hb i).differentiate hU hg.radial hΦ k)).add
    (((ha 1).mul hri).mul (((hb i).angular kp).add (smooth_rotate hb i)))).add
      ((ha 2).mul ((hb i).differentiate hU hg.axial hΦ k))

theorem smooth_gradient {U : Set D} (hU : IsOpen U) {g : Frame D} (hg : g.Regular U)
    {Φ : D → ℝ} (hΦ : ContDiffOn ℝ ∞ Φ U) (k : ℝ) (kp : ℤ)
    {c : Coefficients D} (hc : SmoothCoefficients U c) :
    ∀ i, SmoothCoefficients U (gradient g k Φ kp c i) := by
  intro i
  fin_cases i
  · exact hc.differentiate hU hg.radial hΦ k
  · exact hg.invRadius.mul (hc.angular kp)
  · exact hc.differentiate hU hg.axial hΦ k

theorem smooth_nonlinearResidual {U : Set D} (hU : IsOpen U) {g : Frame D} (hg : g.Regular U)
    {Φ : D → ℝ} (hΦ : ContDiffOn ℝ ∞ Φ U) (k : ℝ) (kp : ℤ)
    {B a : VectorCoefficients D} (hB : ∀ i, SmoothCoefficients U (B i))
    (ha : ∀ i, SmoothCoefficients U (a i)) {c : Coefficients D} (hc : SmoothCoefficients U c) :
    ∀ i, SmoothCoefficients U (nonlinearResidual g k Φ kp B a c i) := fun i =>
  (((((ha i).differentiate hU hg.time hΦ k).add (smooth_transport hU hg hΦ k kp hB ha i)).add
    (smooth_transport hU hg hΦ k kp ha hB i)).add (smooth_gradient hU hg hΦ k kp hc i) |>.sub
      ((smoothCoefficients_constant contDiffOn_const).mul (smooth_vectorLaplacian hU hg hΦ k kp ha
        i))).add
    (smooth_transport hU hg hΦ k kp ha ha i)

noncomputable def constantVector (a : D → ComplexVector) : VectorCoefficients D :=
  fun i => constantCoefficient (fun x => a x i)

omit [NormedAddCommGroup D] [NormedSpace ℝ D] in
@[simp] theorem vectorField_constantVector (a : D → ComplexVector) (k : ℝ) (Φ : D → ℝ)
    (kp : ℤ) (p : D × ℝ) : vectorField (constantVector a) k Φ kp p = a p.1 := by
  ext i
  exact field_constant _ _ _ _ _

omit [NormedAddCommGroup D] [NormedSpace ℝ D] in
theorem band_zero_eq_constant {c : Coefficients D} (hc : BandLimited c 0) :
    c = constantCoefficient (c 0) := by
  ext j x
  change c j x = Finsupp.single 0 (c 0) j x
  by_cases hj : j = 0
  · simp [hj]
  · have hnj : j ∉ c.support := by
      intro h
      have hz : j.natAbs = 0 := Nat.eq_zero_of_le_zero (hc j h)
      exact hj (Int.natAbs_eq_zero.mp hz)
    simp [Finsupp.notMem_support_iff.mp hnj, hj]

omit [NormedAddCommGroup D] [NormedSpace ℝ D] in
theorem field_band_zero {c : Coefficients D} (hc : BandLimited c 0)
    (k : ℝ) (Φ : D → ℝ) (kp : ℤ) (p : D × ℝ) : field c k Φ kp p = c 0 p.1 := by
  calc
    _ = field (constantCoefficient (c 0)) k Φ kp p := congrArg (fun a => field a k Φ kp p)
      (band_zero_eq_constant hc)
    _ = _ := field_constant _ _ _ _ _

/-- A label retains its own slow phase and native angular frequency. -/
structure LabelData (D : Type) where
  frequency : ℝ
  phase : D → ℝ
  angularFrequency : ℤ
  velocity : VectorCoefficients D
  pressure : Coefficients D
  gaussian : VectorCoefficients D
  aliasError : VectorCoefficients D

noncomputable def LabelData.wave (d : LabelData D) : D × ℝ → ComplexVector :=
  vectorField d.velocity d.frequency d.phase d.angularFrequency

noncomputable def LabelData.pressureField (d : LabelData D) : D × ℝ → ℂ :=
  field d.pressure d.frequency d.phase d.angularFrequency

noncomputable def LabelData.gaussianField (d : LabelData D) : D × ℝ → ComplexVector :=
  vectorField d.gaussian d.frequency d.phase d.angularFrequency

noncomputable def LabelData.aliasField (d : LabelData D) : D × ℝ → ComplexVector :=
  vectorField d.aliasError d.frequency d.phase d.angularFrequency

structure LabelData.Regular (d : LabelData D) (U : Set D) : Prop where
  phase : ContDiffOn ℝ ∞ d.phase U
  velocity : ∀ i, SmoothCoefficients U (d.velocity i)
  pressure : SmoothCoefficients U d.pressure

noncomputable def meanCoefficients (g : Frame D) (B M : D → ComplexVector) (p : D → ℂ) :
    VectorCoefficients D :=
  nonlinearResidual g 0 (fun _ => 0) 1 (constantVector B) (constantVector M) (constantCoefficient p)

/-- Gaussian and alias fields are subtracted after the actual nonlinear differential residual. -/
noncomputable def LabelData.residualCoefficients (d : LabelData D) (g : Frame D)
    (B M : D → ComplexVector) : VectorCoefficients D := fun i =>
  realCoefficients (nonlinearResidual g d.frequency d.phase d.angularFrequency
    (constantVector (B + M)) d.velocity d.pressure i - d.gaussian i - d.aliasError i)

noncomputable def LabelData.waveResidualCoefficients (d : LabelData D) (g : Frame D)
    (B M : D → ComplexVector) : VectorCoefficients D := fun i =>
  nonconstant (d.residualCoefficients g B M i)

noncomputable def goodResidual {ι : Type*} (labels : Finset ι) (data : ι → LabelData D)
    (g : Frame D) (B M : D → ComplexVector) (p : D → ℂ) (virtual : D → Fin 3 → ℝ)
    (x : D × ℝ) (i : Fin 3) : ℝ :=
  (Actual.nonlinearResidual g.viscosity (fun y => g.radius y.1)
    (liftDirection g.radial) angularDirection (liftDirection g.axial) (liftDirection g.time)
    (fun y => B y.1) ((fun y => M y.1) + ∑ l ∈ labels, (data l).wave)
    ((fun y => p y.1) + ∑ l ∈ labels, (data l).pressureField) x i).re + virtual x.1 i -
      ∑ l ∈ labels, ((data l).gaussianField x i).re -
      ∑ l ∈ labels, ((data l).aliasField x i).re

theorem meanCoefficients_band (g : Frame D) (B M : D → ComplexVector) (p : D → ℂ) :
    ∀ i, BandLimited (meanCoefficients g B M p i) 0 := by
  intro i
  exact band_nonlinearResidual g 0 (fun _ => 0) 1 (fun _ => band_constantCoefficient _)
    (fun _ => band_constantCoefficient _) (band_constantCoefficient _) i

theorem meanCoefficients_field {U : Set D} (hU : IsOpen U) (g : Frame D)
    (hr : ContDiffOn ℝ ∞ g.radial U) (hz : ContDiffOn ℝ ∞ g.axial U)
    (B M : D → ComplexVector) (p : D → ℂ)
    (hB : ∀ i, ContDiffOn ℝ ∞ (fun y => B y i) U)
    (hM : ∀ i, ContDiffOn ℝ ∞ (fun y => M y i) U) (hp : ContDiffOn ℝ ∞ p U)
    {x : D × ℝ} (hx : x ∈ liftDomain U) :
    Actual.nonlinearResidual g.viscosity (fun y => g.radius y.1)
      (liftDirection g.radial) angularDirection (liftDirection g.axial) (liftDirection g.time)
      (fun y => B y.1) (fun y => M y.1) (fun y => p y.1) x =
      fun i => meanCoefficients g B M p i 0 x.1 := by
  have he := field_nonlinearResidual hU g hr hz
    (fun i => smoothCoefficients_constant (hB i)) (fun i => smoothCoefficients_constant (hM i))
    (smoothCoefficients_constant hp) (Φ := fun _ => 0) contDiffOn_const 0 1 hx
  have hconst (a : D → ComplexVector) :
      vectorField (constantVector a) 0 (fun _ => 0) 1 = fun y : D × ℝ => a y.1 := by
    funext y
    exact vectorField_constantVector a _ _ _ y
  have hpconst : field (constantCoefficient p) 0 (fun _ => 0) 1 = fun y : D × ℝ => p y.1 := by
    funext y
    exact field_constant _ _ _ _ _
  change vectorField (meanCoefficients g B M p) 0 (fun _ => 0) 1 x =
    Actual.nonlinearResidual g.viscosity (fun y => g.radius y.1)
      (liftDirection g.radial) angularDirection (liftDirection g.axial) (liftDirection g.time)
      (vectorField (constantVector B) 0 (fun _ => 0) 1)
      (vectorField (constantVector M) 0 (fun _ => 0) 1)
      (field (constantCoefficient p) 0 (fun _ => 0) 1) x at he
  rw [hconst, hconst, hpconst] at he
  rw [← he]
  ext i
  exact field_band_zero (meanCoefficients_band g B M p i) _ _ _ _

theorem LabelData.residualCoefficients_field {U : Set D} (hU : IsOpen U) (g : Frame D)
    (hr : ContDiffOn ℝ ∞ g.radial U) (hz : ContDiffOn ℝ ∞ g.axial U)
    (B M : D → ComplexVector) (hB : ∀ i, ContDiffOn ℝ ∞ (fun y => B y i) U)
    (hM : ∀ i, ContDiffOn ℝ ∞ (fun y => M y i) U)
    (d : LabelData D) (hd : d.Regular U) {x : D × ℝ} (hx : x ∈ liftDomain U) (i : Fin 3) :
    (field (d.residualCoefficients g B M i) d.frequency d.phase d.angularFrequency x).re =
      (Actual.nonlinearResidual g.viscosity (fun y => g.radius y.1)
        (liftDirection g.radial) angularDirection (liftDirection g.axial) (liftDirection g.time)
        ((fun y => B y.1) + (fun y => M y.1)) d.wave d.pressureField x i).re -
          (d.gaussianField x i).re - (d.aliasField x i).re := by
  have he := field_nonlinearResidual hU g hr hz
    (fun i => smoothCoefficients_constant ((hB i).add (hM i))) hd.velocity hd.pressure hd.phase
    d.frequency d.angularFrequency hx
  have hconst : vectorField (constantVector (B + M)) d.frequency d.phase d.angularFrequency =
      (fun y : D × ℝ => B y.1) + (fun y => M y.1) := by
    funext y
    exact vectorField_constantVector (B + M) _ _ _ y
  change vectorField (nonlinearResidual g d.frequency d.phase d.angularFrequency
    (constantVector (B + M)) d.velocity d.pressure) d.frequency d.phase d.angularFrequency x =
    Actual.nonlinearResidual g.viscosity (fun y => g.radius y.1) (liftDirection g.radial)
      angularDirection (liftDirection g.axial) (liftDirection g.time)
      (vectorField (constantVector (B + M)) d.frequency d.phase d.angularFrequency)
      d.wave d.pressureField x at he
  rw [hconst] at he
  simp only [residualCoefficients, field_realCoefficients, Complex.ofReal_re, field_sub,
    Complex.sub_re]
  rw [← he]
  rfl

theorem goodResidual_grouped {ι : Type*} (labels : Finset ι) (data : ι → LabelData D)
    {U : Set D} (hU : IsOpen U) {g : Frame D} (hg : g.Regular U)
    (B M : D → ComplexVector) (p : D → ℂ) (virtual : D → Fin 3 → ℝ)
    (hB : ∀ i, ContDiffOn ℝ ∞ (fun y => B y i) U)
    (hM : ∀ i, ContDiffOn ℝ ∞ (fun y => M y i) U) (hp : ContDiffOn ℝ ∞ p U)
    (hd : ∀ l ∈ labels, (data l).Regular U)
    (hdisj : ∀ l ∈ labels, ∀ j ∈ labels, l ≠ j →
      Disjoint (tsupport (data l).wave) (tsupport (data j).wave))
    {x : D × ℝ} (hx : x ∈ liftDomain U) (i : Fin 3) :
    goodResidual labels data g B M p virtual x i =
      (meanCoefficients g B M p i 0 x.1).re + virtual x.1 i +
      ∑ l ∈ labels, (field ((data l).residualCoefficients g B M i)
        (data l).frequency (data l).phase (data l).angularFrequency x).re := by
  have hlu := liftDomain_open hU
  have hf : MapsTo (Prod.fst : D × ℝ → D) (liftDomain U) U := fun _ hy => hy.1
  have hBl i : ContDiffOn ℝ ∞ (fun y : D × ℝ => B y.1 i) (liftDomain U) :=
    (hB i).comp contDiffOn_fst hf
  have hMl i : ContDiffOn ℝ ∞ (fun y : D × ℝ => M y.1 i) (liftDomain U) :=
    (hM i).comp contDiffOn_fst hf
  have hpl : ContDiffOn ℝ ∞ (fun y : D × ℝ => p y.1) (liftDomain U) :=
    hp.comp contDiffOn_fst hf
  have hvel (l) (hl : l ∈ labels) (j : Fin 3) :
      ContDiffOn ℝ ∞ (fun y => (data l).wave y j) (liftDomain U) :=
    field_smoothOn ((hd l hl).velocity j) (hd l hl).phase _ _
  have hpres (l) (hl : l ∈ labels) :
      ContDiffOn ℝ ∞ (data l).pressureField (liftDomain U) :=
    field_smoothOn (hd l hl).pressure (hd l hl).phase _ _
  have hsumv (j : Fin 3) : ContDiffOn ℝ ∞
      (fun y => (∑ l ∈ labels, (data l).wave) y j) (liftDomain U) := by
    simpa only [Finset.sum_apply] using ContDiffOn.sum (fun l hl => hvel l hl j)
  have hsump : ContDiffOn ℝ ∞ (∑ l ∈ labels, (data l).pressureField) (liftDomain U) := by
    convert! ContDiffOn.sum hpres using 1
    ext y
    simp only [Finset.sum_apply]
  have hm := Actual.nonlinearResidual_mean_add (Vθ := angularDirection) hlu g.viscosity (fun y =>
    g.radius y.1)
    (liftDirection g.time) (liftDirection_smooth hg.radial) contDiffOn_const
    (liftDirection_smooth hg.axial) (fun y => B y.1) (fun y => M y.1)
    (∑ l ∈ labels, (data l).wave) (fun y => p y.1) (∑ l ∈ labels, (data l).pressureField)
    hBl hMl hsumv hpl hsump hx
  have hs := Actual.nonlinearResidual_sum (Vθ := angularDirection) labels hlu g.viscosity (fun y =>
    g.radius y.1)
    (liftDirection g.time) (liftDirection_smooth hg.radial) contDiffOn_const
    (liftDirection_smooth hg.axial) ((fun y => B y.1) + (fun y => M y.1))
    (fun l => (data l).wave) (fun l => (data l).pressureField) hvel hpres hdisj hx
  have hcoef := meanCoefficients_field hU g hg.radial hg.axial B M p hB hM hp hx
  have hsumcoef := Finset.sum_congr (s₁ := labels) (s₂ := labels) rfl (fun l hl =>
    LabelData.residualCoefficients_field hU g hg.radial hg.axial B M hB hM
      (data l) (hd l hl) hx i)
  unfold goodResidual
  rw [hm, hs, hcoef]
  simp only [Pi.add_apply, Finset.sum_apply, Complex.add_re, Complex.re_sum]
  rw [hsumcoef]
  simp only [Finset.sum_sub_distrib]
  ring

theorem LabelData.residualCoefficients_band (d : LabelData D) (g : Frame D)
    (B M : D → ComplexVector) {N E : ℕ}
    (hu : ∀ i, BandLimited (d.velocity i) N) (hp : BandLimited d.pressure N)
    (hg : ∀ i, BandLimited (d.gaussian i) E) (ha : ∀ i, BandLimited (d.aliasError i) E) :
    ∀ i, BandLimited (d.residualCoefficients g B M i) (max (N + N) E) := by
  intro i
  apply band_realCoefficients
  exact band_sub (band_sub ((band_nonlinearResidual g d.frequency d.phase d.angularFrequency
    (fun _ => band_constantCoefficient _) hu hp i).mono (Nat.le_max_left _ _))
      ((hg i).mono (Nat.le_max_right _ _))) ((ha i).mono (Nat.le_max_right _ _))

theorem LabelData.waveResidualCoefficients_band (d : LabelData D) (g : Frame D)
    (B M : D → ComplexVector) {N E : ℕ}
    (hu : ∀ i, BandLimited (d.velocity i) N) (hp : BandLimited d.pressure N)
    (hg : ∀ i, BandLimited (d.gaussian i) E) (ha : ∀ i, BandLimited (d.aliasError i) E) :
    ∀ i, BandLimited (d.waveResidualCoefficients g B M i) (max (N + N) E) :=
  fun i => band_nonconstant (d.residualCoefficients_band g B M hu hp hg ha i)

theorem LabelData.waveResidualCoefficients_values (d : LabelData D) (g : Frame D)
    (B M : D → ComplexVector) {N E : ℕ}
    (hu : ∀ i, BandLimited (d.velocity i) N) (hp : BandLimited d.pressure N)
    (hg : ∀ i, BandLimited (d.gaussian i) E) (ha : ∀ i, BandLimited (d.aliasError i) E)
    (i : Fin 3) (j : ℤ) (hj : j ∈ (d.waveResidualCoefficients g B M i).support) :
    j ≠ 0 ∧ j.natAbs ≤ max (N + N) E :=
  ⟨nonconstant_support hj, d.waveResidualCoefficients_band g B M hu hp hg ha i j hj⟩

theorem LabelData.residualCoefficients_conjugate (d : LabelData D) (g : Frame D)
    (B M : D → ComplexVector) (i : Fin 3) : ConjugateSymmetric (d.residualCoefficients g B M i) :=
  realCoefficients_conjugate _

theorem LabelData.waveResidualCoefficients_conjugate (d : LabelData D) (g : Frame D)
    (B M : D → ComplexVector) (i : Fin 3) : ConjugateSymmetric (d.waveResidualCoefficients g B M i)
      :=
  nonconstant_conjugate (d.residualCoefficients_conjugate g B M i)

theorem LabelData.waveResidualCoefficients_smooth {U : Set D} (hU : IsOpen U)
    {g : Frame D} (hg : g.Regular U) (B M : D → ComplexVector)
    (hB : ∀ i, ContDiffOn ℝ ∞ (fun y => B y i) U)
    (hM : ∀ i, ContDiffOn ℝ ∞ (fun y => M y i) U)
    (d : LabelData D) (hd : d.Regular U)
    (hgaussian : ∀ i, SmoothCoefficients U (d.gaussian i))
    (halias : ∀ i, SmoothCoefficients U (d.aliasError i)) :
    ∀ i, SmoothCoefficients U (d.waveResidualCoefficients g B M i) := by
  intro i
  exact (((smooth_nonlinearResidual hU hg hd.phase d.frequency d.angularFrequency
    (fun i => smoothCoefficients_constant ((hB i).add (hM i))) hd.velocity hd.pressure i).sub
      (hgaussian i)).sub (halias i)).realCoefficients.nonconstant

theorem LabelData.extract_residual (d : LabelData D) (g : Frame D)
    (B M : D → ComplexVector) (hkp : d.angularFrequency ≠ 0) (i : Fin 3) (j : ℤ) (x : D) :
    extract (field (d.residualCoefficients g B M i) d.frequency d.phase d.angularFrequency)
      d.frequency d.phase d.angularFrequency j x = d.residualCoefficients g B M i j x :=
  extract_field _ _ _ hkp _ _

noncomputable def realAngularMean (f : ℝ → ℝ) : ℝ :=
  (∫ θ in (0 : ℝ)..period, f θ) / period

theorem realAngularMean_const (a : ℝ) : realAngularMean (fun _ => a) = a := by
  simp only [realAngularMean, intervalIntegral.integral_const, sub_zero, smul_eq_mul]
  field_simp [period_ne_zero]

theorem realAngularMean_add {f g : ℝ → ℝ} (hf : Continuous f) (hg : Continuous g) :
    realAngularMean (fun θ => f θ + g θ) = realAngularMean f + realAngularMean g := by
  simp only [realAngularMean]
  rw [intervalIntegral.integral_add (hf.intervalIntegrable _ _) (hg.intervalIntegrable _ _),
    add_div]

theorem realAngularMean_sum {ι : Type*} (s : Finset ι) (f : ι → ℝ → ℝ)
    (hf : ∀ l ∈ s, Continuous (f l)) :
    realAngularMean (fun θ => ∑ l ∈ s, f l θ) = ∑ l ∈ s, realAngularMean (f l) := by
  simp only [realAngularMean]
  rw [intervalIntegral.integral_finsetSum (fun l hl => (hf l hl).intervalIntegrable _ _),
    Finset.sum_div]

omit [NormedAddCommGroup D] [NormedSpace ℝ D] in
theorem realAngularMean_field (c : Coefficients D) (k : ℝ) (Φ : D → ℝ)
    {kp : ℤ} (hkp : kp ≠ 0) (x : D) :
    realAngularMean (fun θ => (field c k Φ kp (x, θ)).re) = (c 0 x).re := by
  have hi := Complex.reCLM.intervalIntegral_comp_comm (μ := volume)
    ((field_angular_continuous c k Φ kp x).intervalIntegrable (0 : ℝ) period)
  have he := congrArg Complex.re (angularMean_field c k Φ hkp x)
  simp only [Complex.reCLM_apply] at hi
  simp only [angularMean, ← Complex.ofReal_inv, Complex.mul_re, Complex.ofReal_re,
    Complex.ofReal_im, zero_mul, sub_zero] at he
  rw [← hi] at he
  simpa only [realAngularMean, div_eq_mul_inv, mul_comm] using he

noncomputable def meanResidualValue {ι : Type*} (labels : Finset ι) (data : ι → LabelData D)
    (g : Frame D) (B M : D → ComplexVector) (p : D → ℂ) (virtual : D → Fin 3 → ℝ)
    (x : D) (i : Fin 3) : ℝ :=
  (meanCoefficients g B M p i 0 x).re + virtual x i +
    ∑ l ∈ labels, (data l |>.residualCoefficients g B M i 0 x).re

theorem goodResidual_angularMean {ι : Type*} (labels : Finset ι) (data : ι → LabelData D)
    {U : Set D} (hU : IsOpen U) {g : Frame D} (hg : g.Regular U)
    (B M : D → ComplexVector) (p : D → ℂ) (virtual : D → Fin 3 → ℝ)
    (hB : ∀ i, ContDiffOn ℝ ∞ (fun y => B y i) U)
    (hM : ∀ i, ContDiffOn ℝ ∞ (fun y => M y i) U) (hp : ContDiffOn ℝ ∞ p U)
    (hd : ∀ l ∈ labels, (data l).Regular U)
    (hdisj : ∀ l ∈ labels, ∀ j ∈ labels, l ≠ j →
      Disjoint (tsupport (data l).wave) (tsupport (data j).wave))
    (hkp : ∀ l ∈ labels, (data l).angularFrequency ≠ 0) {x : D} (hx : x ∈ U) (i : Fin 3) :
    realAngularMean (fun θ => goodResidual labels data g B M p virtual (x, θ) i) =
      meanResidualValue labels data g B M p virtual x i := by
  have he : (fun θ => goodResidual labels data g B M p virtual (x, θ) i) =
      fun θ => (meanCoefficients g B M p i 0 x).re + virtual x i +
        ∑ l ∈ labels, (field ((data l).residualCoefficients g B M i)
          (data l).frequency (data l).phase (data l).angularFrequency (x, θ)).re := by
    funext θ
    exact goodResidual_grouped labels data hU hg B M p virtual hB hM hp hd hdisj ⟨hx, mem_univ θ⟩ i
  let F : ι → ℝ → ℝ := fun l θ => (field ((data l).residualCoefficients g B M i)
    (data l).frequency (data l).phase (data l).angularFrequency (x, θ)).re
  have hF (l : ι) : Continuous (F l) :=
    Complex.continuous_re.comp (field_angular_continuous _ _ _ _ _)
  rw [he]
  change realAngularMean (fun θ => (meanCoefficients g B M p i 0 x).re + virtual x i +
    ∑ l ∈ labels, F l θ) = _
  rw [realAngularMean_add (f := fun _ => (meanCoefficients g B M p i 0 x).re + virtual x i)
    (g := fun θ => ∑ l ∈ labels, F l θ) continuous_const
    (continuous_finsetSum labels (fun l _ => hF l)),
    realAngularMean_const, realAngularMean_sum labels F (fun l _ => hF l)]
  congr 1
  apply Finset.sum_congr rfl
  intro l hl
  exact realAngularMean_field _ _ _ (hkp l hl) x

noncomputable def goodWaveResidual {ι : Type*} (labels : Finset ι) (data : ι → LabelData D)
    (g : Frame D) (B M : D → ComplexVector) (p : D → ℂ) (virtual : D → Fin 3 → ℝ)
    (x : D × ℝ) (i : Fin 3) : ℝ :=
  goodResidual labels data g B M p virtual x i -
    realAngularMean (fun θ => goodResidual labels data g B M p virtual (x.1, θ) i)

/-- Exact reconstruction of the good nonconstant PDE residual by native-label blocks. -/
theorem goodWaveResidual_grouped {ι : Type*} (labels : Finset ι) (data : ι → LabelData D)
    {U : Set D} (hU : IsOpen U) {g : Frame D} (hg : g.Regular U)
    (B M : D → ComplexVector) (p : D → ℂ) (virtual : D → Fin 3 → ℝ)
    (hB : ∀ i, ContDiffOn ℝ ∞ (fun y => B y i) U)
    (hM : ∀ i, ContDiffOn ℝ ∞ (fun y => M y i) U) (hp : ContDiffOn ℝ ∞ p U)
    (hd : ∀ l ∈ labels, (data l).Regular U)
    (hdisj : ∀ l ∈ labels, ∀ j ∈ labels, l ≠ j →
      Disjoint (tsupport (data l).wave) (tsupport (data j).wave))
    (hkp : ∀ l ∈ labels, (data l).angularFrequency ≠ 0) {x : D × ℝ}
    (hx : x ∈ liftDomain U) (i : Fin 3) :
    goodWaveResidual labels data g B M p virtual x i =
      ∑ l ∈ labels, (field ((data l).waveResidualCoefficients g B M i)
        (data l).frequency (data l).phase (data l).angularFrequency x).re := by
  rw [goodWaveResidual, goodResidual_grouped labels data hU hg B M p virtual hB hM hp hd hdisj hx i,
    goodResidual_angularMean labels data hU hg B M p virtual hB hM hp hd hdisj hkp hx.1 i]
  simp only [meanResidualValue, LabelData.waveResidualCoefficients, field_nonconstant,
    Complex.sub_re,
    Finset.sum_sub_distrib]
  ring

/-! ## The stored correction state and its actual grouped residual -/

noncomputable def contextFrame (c : CorrectionState.Context D) (n : ℕ) : Frame D where
  radius := c.operators.radius
  radial := fun x => c.operators.eR +
    (c.operators.radialFrequency n * c.operators.radialProfile x) • c.operators.vR
  axial := fun _ => c.operators.epsilon n • c.operators.eZ
  time := fun _ => c.operators.fastCoefficient n • c.operators.vT - c.operators.epsilon n •
    c.operators.eT
  viscosity := c.operators.epsilon n

noncomputable def contextBase (c : CorrectionState.Context D) (n : ℕ) (x : D) : ComplexVector :=
  ![(c.base.radial n x : ℂ), (c.base.angular n x : ℂ), (c.base.axial n x : ℂ)]

noncomputable def stateMean (s : CorrectionState.State D) (n : ℕ) (x : D) : ComplexVector :=
  ![(s.mean.radial n x : ℂ), (s.mean.angular n x : ℂ), (s.mean.axial n x : ℂ)]

noncomputable def statePerturbation (s : CorrectionState.State D) (n : ℕ) (x : D × ℝ) :
  ComplexVector :=
  ![(s.mean.radial n x.1 + s.oscillation n x 0 : ℝ),
    (s.mean.angular n x.1 + s.oscillation n x 1 : ℝ),
    (s.mean.axial n x.1 + s.oscillation n x 2 : ℝ)]

noncomputable def statePressure (s : CorrectionState.State D) (n : ℕ) (x : D × ℝ) : ℂ :=
  (s.totalPressureIncrement n x : ℝ)

noncomputable def contextVirtual (c : CorrectionState.Context D) (n : ℕ) (x : D) : Fin 3 → ℝ :=
  ![0, -(c.operators.radialDiv 2 c.virtualTheta n x), -(c.operators.radialDiv 1 c.virtualAxial n x)]

/-- The same full normalized differential field used by the correction cycle. -/
noncomputable def stateFullResidual (c : CorrectionState.Context D) (s : CorrectionState.State D)
    (n : ℕ) (x : D × ℝ) (i : Fin 3) : ℝ :=
  (Actual.nonlinearResidual (contextFrame c n).viscosity (fun y => (contextFrame c n).radius y.1)
    (liftDirection (contextFrame c n).radial) angularDirection
    (liftDirection (contextFrame c n).axial) (liftDirection (contextFrame c n).time)
    (fun y => contextBase c n y.1) (statePerturbation s n) (statePressure s n) x i).re +
    contextVirtual c n x.1 i + s.errors.base n x i

noncomputable def stateGoodResidual (c : CorrectionState.Context D) (s : CorrectionState.State D) :
    CorrectionState.Oscillation D := stateFullResidual c s - s.errors.total

noncomputable def stateGoodWaveResidual (c : CorrectionState.Context D) (s : CorrectionState.State
  D)
    (n : ℕ) (x : D × ℝ) (i : Fin 3) : ℝ :=
  stateGoodResidual c s n x i -
    CorrectionState.angularAverage (fun m y => stateGoodResidual c s m y i) n x.1

abbrev BlockCoefficients (D : Type) := ℕ → VectorCoefficients D

/-- Input blocks are interpreted as their actual real fields. The real projection
does not enlarge the largest harmonic value and is the identity for conjugate data. -/
noncomputable def ofBlock (b : CorrectionState.HarmonicBlock D)
    (gaussian aliasError : BlockCoefficients D) (n : ℕ) : LabelData D where
  frequency := b.frequency n
  phase := b.phase n
  angularFrequency := b.angularFrequency n
  velocity := fun i => realCoefficients (b.velocity n i)
  pressure := realCoefficients (b.pressure n)
  gaussian := gaussian n
  aliasError := aliasError n

omit [NormedAddCommGroup D] [NormedSpace ℝ D] in
theorem ofBlock_wave (b : CorrectionState.HarmonicBlock D)
    (gaussian aliasError : BlockCoefficients D) (n : ℕ) (x : D × ℝ) (i : Fin 3) :
    (ofBlock b gaussian aliasError n).wave x i = (b.oscillation n x i : ℂ) :=
  field_realCoefficients _ _ _ _ _

omit [NormedAddCommGroup D] [NormedSpace ℝ D] in
theorem ofBlock_pressure (b : CorrectionState.HarmonicBlock D)
    (gaussian aliasError : BlockCoefficients D) (n : ℕ) (x : D × ℝ) :
    (ofBlock b gaussian aliasError n).pressureField x = (b.oscillatoryPressure n x : ℂ) :=
  field_realCoefficients _ _ _ _ _

omit [NormedSpace ℝ D] in
theorem ofBlock_tsupport_wave (b : CorrectionState.HarmonicBlock D)
    (gaussian aliasError : BlockCoefficients D) (n : ℕ) :
    tsupport (ofBlock b gaussian aliasError n).wave = tsupport (b.oscillation n) := by
  apply congrArg closure
  ext x
  change (_ ≠ 0) ↔ (_ ≠ 0)
  apply not_congr
  constructor
  · intro h
    ext i
    have hi := congrFun h i
    rw [ofBlock_wave] at hi
    exact Complex.ofReal_eq_zero.mp hi
  · intro h
    ext i
    rw [ofBlock_wave, h]
    rfl

theorem ofBlock_regular {U : Set D} (b : CorrectionState.HarmonicBlock D)
    (gaussian aliasError : BlockCoefficients D) (n : ℕ)
    (hΦ : ContDiffOn ℝ ∞ (b.phase n) U)
    (hv : ∀ i, SmoothCoefficients U (b.velocity n i)) (hp : SmoothCoefficients U (b.pressure n)) :
    (ofBlock b gaussian aliasError n).Regular U :=
  ⟨hΦ, fun i => (hv i).realCoefficients, hp.realCoefficients⟩

/-- Only representations of the stored fields are inputs; no residual identity is assumed.
The finite label set may vary with the band. -/
structure BlockRepresentation {ι : Type*} (labels : ℕ → Finset ι)
    (blocks : ι → CorrectionState.HarmonicBlock D)
    (gaussianCoeffs aliasCoeffs : ι → BlockCoefficients D) (s : CorrectionState.State D) : Prop
      where
  velocity : ∀ n x i, s.oscillation n x i = ∑ l ∈ labels n, (blocks l).oscillation n x i
  pressure : ∀ n x, s.oscillatoryPressure n x = ∑ l ∈ labels n, (blocks l).oscillatoryPressure n x
  gaussian : ∀ n x i, s.errors.gaussian n x i =
    ∑ l ∈ labels n, ((ofBlock (blocks l) (gaussianCoeffs l) (aliasCoeffs l) n).gaussianField x i).re
  aliasError : ∀ n x i, s.errors.aliasError n x i =
    ∑ l ∈ labels n, ((ofBlock (blocks l) (gaussianCoeffs l) (aliasCoeffs l) n).aliasField x i).re

omit [NormedAddCommGroup D] [NormedSpace ℝ D] in
theorem BlockRepresentation.perturbation {ι : Type*} {labels : ℕ → Finset ι}
    {blocks : ι → CorrectionState.HarmonicBlock D} {gaussian aliasError : ι → BlockCoefficients D}
    {s : CorrectionState.State D} (hrep : BlockRepresentation labels blocks gaussian aliasError s)
      (n : ℕ) :
    statePerturbation s n = (fun x => stateMean s n x.1) +
      ∑ l ∈ labels n, (ofBlock (blocks l) (gaussian l) (aliasError l) n).wave := by
  ext x i
  fin_cases i <;>
    simp [statePerturbation, stateMean, Finset.sum_apply, ofBlock_wave, hrep.velocity,
      Complex.ofReal_sum, Complex.ofReal_add]

omit [NormedAddCommGroup D] [NormedSpace ℝ D] in
theorem BlockRepresentation.pressureField {ι : Type*} {labels : ℕ → Finset ι}
    {blocks : ι → CorrectionState.HarmonicBlock D} {gaussian aliasError : ι → BlockCoefficients D}
    {s : CorrectionState.State D} (hrep : BlockRepresentation labels blocks gaussian aliasError s)
      (n : ℕ) :
    statePressure s n = (fun x => (s.pressure n x.1 : ℂ)) +
      ∑ l ∈ labels n, (ofBlock (blocks l) (gaussian l) (aliasError l) n).pressureField := by
  ext x
  simp [statePressure, CorrectionState.State.totalPressureIncrement, Finset.sum_apply,
    ofBlock_pressure, hrep.pressure, Complex.ofReal_sum, Complex.ofReal_add]

/-- The fixed base error cancels literally; Gaussian and alias errors stay additive. -/
theorem BlockRepresentation.goodResidual_eq {ι : Type*} {labels : ℕ → Finset ι}
    {blocks : ι → CorrectionState.HarmonicBlock D} {gaussian aliasError : ι → BlockCoefficients D}
    {s : CorrectionState.State D} (hrep : BlockRepresentation labels blocks gaussian aliasError s)
    (c : CorrectionState.Context D) (n : ℕ) (x : D × ℝ) (i : Fin 3) :
    stateGoodResidual c s n x i = goodResidual (labels n)
      (fun l => ofBlock (blocks l) (gaussian l) (aliasError l) n)
      (contextFrame c n) (contextBase c n) (stateMean s n) (fun y => (s.pressure n y : ℂ))
      (contextVirtual c n) x i := by
  simp only [stateGoodResidual, Pi.sub_apply, stateFullResidual, goodResidual]
  rw [hrep.perturbation n, hrep.pressureField n]
  simp only [CorrectionState.ExcludedErrors.total, Pi.add_apply]
  rw [hrep.gaussian n x i, hrep.aliasError n x i]
  ring

noncomputable def residualBlock (c : CorrectionState.Context D) (s : CorrectionState.State D)
    (b : CorrectionState.HarmonicBlock D) (gaussian aliasError : BlockCoefficients D) :
    CorrectionState.HarmonicBlock D where
  velocity := fun n => (ofBlock b gaussian aliasError n).waveResidualCoefficients
    (contextFrame c n) (contextBase c n) (stateMean s n)
  pressure := fun _ => 0
  frequency := b.frequency
  phase := b.phase
  angularFrequency := b.angularFrequency

theorem BlockRepresentation.goodWaveResidual_eq {ι : Type*} {labels : ℕ → Finset ι}
    {blocks : ι → CorrectionState.HarmonicBlock D} {gaussian aliasError : ι → BlockCoefficients D}
    {s : CorrectionState.State D} (hrep : BlockRepresentation labels blocks gaussian aliasError s)
    (c : CorrectionState.Context D) (n : ℕ) (x : D × ℝ) (i : Fin 3) :
    stateGoodWaveResidual c s n x i = goodWaveResidual (labels n)
      (fun l => ofBlock (blocks l) (gaussian l) (aliasError l) n)
      (contextFrame c n) (contextBase c n) (stateMean s n) (fun y => (s.pressure n y : ℂ))
      (contextVirtual c n) x i := by
  simp only [stateGoodWaveResidual, goodWaveResidual, CorrectionState.angularAverage,
    realAngularMean, period]
  simp_rw [hrep.goodResidual_eq c n]

/-- Conditions on the actual graph, represented fields, and actual closed supports. -/
structure ExtractionRegular {ι : Type*} (U : Set D) (c : CorrectionState.Context D)
    (s : CorrectionState.State D) (labels : ℕ → Finset ι)
    (blockFamily : ι → CorrectionState.HarmonicBlock D)
    (gaussianCoeffs aliasCoeffs : ι → BlockCoefficients D) (n : ℕ) : Prop where
  frame : (contextFrame c n).Regular U
  base : ∀ i, ContDiffOn ℝ ∞ (fun x => contextBase c n x i) U
  mean : ∀ i, ContDiffOn ℝ ∞ (fun x => stateMean s n x i) U
  pressure : ContDiffOn ℝ ∞ (s.pressure n) U
  blocks : ∀ l ∈ labels n, (ofBlock (blockFamily l) (gaussianCoeffs l) (aliasCoeffs l) n).Regular U
  gaussian : ∀ l ∈ labels n, ∀ i, SmoothCoefficients U (gaussianCoeffs l n i)
  aliasError : ∀ l ∈ labels n, ∀ i, SmoothCoefficients U (aliasCoeffs l n i)
  disjoint : ∀ l ∈ labels n, ∀ j ∈ labels n, l ≠ j →
    Disjoint (tsupport ((blockFamily l).oscillation n)) (tsupport ((blockFamily j).oscillation n))
  angular_nonzero : ∀ l ∈ labels n, (blockFamily l).angularFrequency n ≠ 0

theorem ExtractionRegular.dataDisjoint {ι : Type*} {U : Set D} {c : CorrectionState.Context D}
    {s : CorrectionState.State D} {labels : ℕ → Finset ι}
    {blocks : ι → CorrectionState.HarmonicBlock D} {gaussian aliasError : ι → BlockCoefficients D}
      {n : ℕ}
    (h : ExtractionRegular U c s labels blocks gaussian aliasError n) :
    ∀ l ∈ labels n, ∀ j ∈ labels n, l ≠ j →
      Disjoint (tsupport (ofBlock (blocks l) (gaussian l) (aliasError l) n).wave)
        (tsupport (ofBlock (blocks j) (gaussian j) (aliasError j) n).wave) := by
  intro l hl j hj hlj
  simpa only [ofBlock_tsupport_wave] using h.disjoint l hl j hj hlj

/-- The forcing supplied to each copy solve consists of the actual nonconstant
PDE coefficients. Finite active sets can change with `n`. -/
theorem stateGoodWaveResidual_grouped {ι : Type*} {U : Set D} (hU : IsOpen U)
    {c : CorrectionState.Context D} {s : CorrectionState.State D} {labels : ℕ → Finset ι}
    {blocks : ι → CorrectionState.HarmonicBlock D} {gaussian aliasError : ι → BlockCoefficients D}
    (hrep : BlockRepresentation labels blocks gaussian aliasError s) {n : ℕ}
    (h : ExtractionRegular U c s labels blocks gaussian aliasError n)
    {x : D × ℝ} (hx : x ∈ liftDomain U) (i : Fin 3) :
    stateGoodWaveResidual c s n x i =
      ∑ l ∈ labels n, (residualBlock c s (blocks l) (gaussian l) (aliasError l)).oscillation n x i
        := by
  rw [hrep.goodWaveResidual_eq c n x i]
  exact goodWaveResidual_grouped (labels n) _ hU h.frame _ _ _ _ h.base h.mean
    (Complex.ofRealCLM.contDiff.comp_contDiffOn h.pressure) h.blocks h.dataDisjoint
      h.angular_nonzero hx i

noncomputable def stateMeanCoefficientValue {ι : Type*} (labels : ℕ → Finset ι)
    (blocks : ι → CorrectionState.HarmonicBlock D) (gaussian aliasError : ι → BlockCoefficients D)
    (c : CorrectionState.Context D) (s : CorrectionState.State D) (n : ℕ) (x : D) (i : Fin 3) : ℝ :=
  meanResidualValue (labels n) (fun l => ofBlock (blocks l) (gaussian l) (aliasError l) n)
    (contextFrame c n) (contextBase c n) (stateMean s n) (fun y => (s.pressure n y : ℂ))
    (contextVirtual c n) x i

/-- The selected zero mode is the actual angular mean of the stored good residual. -/
theorem stateMeanCoefficientValue_eq_average {ι : Type*} {U : Set D} (hU : IsOpen U)
    {c : CorrectionState.Context D} {s : CorrectionState.State D} {labels : ℕ → Finset ι}
    {blocks : ι → CorrectionState.HarmonicBlock D} {gaussian aliasError : ι → BlockCoefficients D}
    (hrep : BlockRepresentation labels blocks gaussian aliasError s) {n : ℕ}
    (h : ExtractionRegular U c s labels blocks gaussian aliasError n)
    {x : D} (hx : x ∈ U) (i : Fin 3) :
    stateMeanCoefficientValue labels blocks gaussian aliasError c s n x i =
      CorrectionState.angularAverage (fun m y => stateGoodResidual c s m y i) n x := by
  simp only [CorrectionState.angularAverage]
  simp_rw [hrep.goodResidual_eq c n]
  exact (goodResidual_angularMean (labels n) _ hU h.frame _ _ _ _ h.base h.mean
    (Complex.ofRealCLM.contDiff.comp_contDiffOn h.pressure) h.blocks h.dataDisjoint
    h.angular_nonzero hx i).symm

theorem residualBlock_band (c : CorrectionState.Context D) (s : CorrectionState.State D)
    (b : CorrectionState.HarmonicBlock D) (gaussian aliasError : BlockCoefficients D)
    {N E : ℕ} (hb : b.BandLimited N)
    (hg : ∀ n i, BandLimited (gaussian n i) E) (ha : ∀ n i, BandLimited (aliasError n i) E) :
    (residualBlock c s b gaussian aliasError).BandLimited (max (N + N) E) := by
  refine ⟨?_, fun n => band_zero _⟩
  intro n i
  exact (ofBlock b gaussian aliasError n).waveResidualCoefficients_band _ _ _
    (fun j => band_realCoefficients (hb.1 n j)) (band_realCoefficients (hb.2 n)) (hg n) (ha n) i

theorem residualBlock_conjugate (c : CorrectionState.Context D) (s : CorrectionState.State D)
    (b : CorrectionState.HarmonicBlock D) (gaussian aliasError : BlockCoefficients D) (n : ℕ) (i :
      Fin 3) :
    ConjugateSymmetric ((residualBlock c s b gaussian aliasError).velocity n i) :=
  LabelData.waveResidualCoefficients_conjugate _ _ _ _ _

theorem residualBlock_zero_mode (c : CorrectionState.Context D) (s : CorrectionState.State D)
    (b : CorrectionState.HarmonicBlock D) (gaussian aliasError : BlockCoefficients D) (n : ℕ) (i :
      Fin 3) :
    (residualBlock c s b gaussian aliasError).velocity n i 0 = 0 :=
  Finsupp.erase_same

theorem residualBlock_smooth {ι : Type*} {U : Set D} (hU : IsOpen U)
    {c : CorrectionState.Context D} {s : CorrectionState.State D} {labels : ℕ → Finset ι}
    {blocks : ι → CorrectionState.HarmonicBlock D} {gaussian aliasError : ι → BlockCoefficients D}
      {n : ℕ}
    (h : ExtractionRegular U c s labels blocks gaussian aliasError n) {l : ι} (hl : l ∈ labels n) :
    ∀ i, SmoothCoefficients U ((residualBlock c s (blocks l) (gaussian l) (aliasError l)).velocity
      n i) :=
  LabelData.waveResidualCoefficients_smooth hU h.frame _ _ h.base h.mean _
    (h.blocks l hl) (h.gaussian l hl) (h.aliasError l hl)

theorem residualBlock_values (c : CorrectionState.Context D) (s : CorrectionState.State D)
    (b : CorrectionState.HarmonicBlock D) (gaussian aliasError : BlockCoefficients D)
    {N E : ℕ} (hb : b.BandLimited N)
    (hg : ∀ n i, BandLimited (gaussian n i) E) (ha : ∀ n i, BandLimited (aliasError n i) E)
    (n : ℕ) (i : Fin 3) (j : ℤ)
    (hj : j ∈ ((residualBlock c s b gaussian aliasError).velocity n i).support) :
    j ≠ 0 ∧ j.natAbs ≤ max (N + N) E :=
  ⟨nonconstant_support hj, (residualBlock_band c s b gaussian aliasError hb hg ha).1 n i j hj⟩

/-- A fixed stage can have large harmonic values, but the next quadratic stage
has an explicit bound independent of band and label count. -/
theorem residualBlock_stage_band (c : CorrectionState.Context D) (s : CorrectionState.State D)
    (b : CorrectionState.HarmonicBlock D) (gaussian aliasError : BlockCoefficients D)
    (stage : ℕ) (hb : b.BandLimited (2 ^ stage))
    (hg : ∀ n i, BandLimited (gaussian n i) (2 ^ (stage + 1)))
    (ha : ∀ n i, BandLimited (aliasError n i) (2 ^ (stage + 1))) :
    (residualBlock c s b gaussian aliasError).BandLimited (2 ^ (stage + 1)) := by
  have he : 2 ^ stage + 2 ^ stage = 2 ^ (stage + 1) := by omega
  simpa only [he, max_self] using residualBlock_band c s b gaussian aliasError hb hg ha

theorem residualBlock_extract (c : CorrectionState.Context D) (s : CorrectionState.State D)
    (b : CorrectionState.HarmonicBlock D) (gaussian aliasError : BlockCoefficients D)
    (n : ℕ) (hkp : b.angularFrequency n ≠ 0) (i : Fin 3) (j : ℤ) (x : D) :
    extract (fun y => ((residualBlock c s b gaussian aliasError).oscillation n y i : ℂ))
      (b.frequency n) (b.phase n) (b.angularFrequency n) j x =
        (residualBlock c s b gaussian aliasError).velocity n i j x := by
  have he : (fun y => ((residualBlock c s b gaussian aliasError).oscillation n y i : ℂ)) =
      field ((residualBlock c s b gaussian aliasError).velocity n i)
        (b.frequency n) (b.phase n) (b.angularFrequency n) := by
    funext y
    exact field_real (residualBlock_conjugate c s b gaussian aliasError n i) _ _ _ _
  rw [he]
  exact extract_field _ _ _ hkp _ _

theorem residualBlock_mean_zero (c : CorrectionState.Context D) (s : CorrectionState.State D)
    (b : CorrectionState.HarmonicBlock D) (gaussian aliasError : BlockCoefficients D)
    (n : ℕ) (hkp : b.angularFrequency n ≠ 0) (i : Fin 3) (x : D) :
    CorrectionState.angularAverage
      (fun m y => (residualBlock c s b gaussian aliasError).oscillation m y i) n x = 0 := by
  change realAngularMean (fun θ => (field
    ((residualBlock c s b gaussian aliasError).velocity n i)
    (b.frequency n) (b.phase n) (b.angularFrequency n) (x, θ)).re) = 0
  rw [realAngularMean_field _ _ _ hkp x, residualBlock_zero_mode]
  rfl

/-- Reconstruction of the full differentiated residual, with every excluded error restored once. -/
theorem stateFullResidual_reconstructed {ι : Type*} {U : Set D} (hU : IsOpen U)
    {c : CorrectionState.Context D} {s : CorrectionState.State D} {labels : ℕ → Finset ι}
    {blocks : ι → CorrectionState.HarmonicBlock D} {gaussian aliasError : ι → BlockCoefficients D}
    (hrep : BlockRepresentation labels blocks gaussian aliasError s) {n : ℕ}
    (h : ExtractionRegular U c s labels blocks gaussian aliasError n)
    {x : D × ℝ} (hx : x ∈ liftDomain U) (i : Fin 3) :
    stateFullResidual c s n x i =
      (∑ l ∈ labels n, (residualBlock c s (blocks l) (gaussian l) (aliasError l)).oscillation n x
        i) +
      stateMeanCoefficientValue labels blocks gaussian aliasError c s n x.1 i + s.errors.total n x
        i := by
  rw [← stateGoodWaveResidual_grouped hU hrep h hx i,
    stateMeanCoefficientValue_eq_average hU hrep h hx.1 i]
  simp only [stateGoodWaveResidual, stateGoodResidual, Pi.sub_apply]
  ring

/-- The actual graph formula gives smooth directions whenever its primitive radius
and radial profile are smooth on the annular domain. -/
theorem contextFrame_regular {U : Set D} (c : CorrectionState.Context D) (n : ℕ)
    (hR : ContDiffOn ℝ ∞ c.operators.radius U)
    (hRn : ∀ x ∈ U, c.operators.radius x ≠ 0)
    (hprofile : ContDiffOn ℝ ∞ c.operators.radialProfile U) :
    (contextFrame c n).Regular U := by
  refine ⟨hR, hRn, ?_, contDiffOn_const, contDiffOn_const⟩
  exact contDiffOn_const.add ((contDiffOn_const.mul hprofile).smul contDiffOn_const)

end NavierStokes.HarmonicResidual
