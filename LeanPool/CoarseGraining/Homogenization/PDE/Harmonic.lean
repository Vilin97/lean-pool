/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/
module


public import LeanPool.CoarseGraining.Homogenization.Ambient.CoefficientField
public import LeanPool.CoarseGraining.Homogenization.Sobolev.Foundations.MeanZero
public import LeanPool.CoarseGraining.Homogenization.Sobolev.H1.BasicLemmas
public import LeanPool.CoarseGraining.Homogenization.Sobolev.PotentialSolenoidal
public import LeanPool.CoarseGraining.Homogenization.Sobolev.PotentialSolenoidalL2Recovery

/-! # Harmonic -/

@[expose] public section

namespace Homogenization

def IsAHarmonicGradient {d : ℕ} (a : CoeffField d) (U : Set (Vec d)) (f : Vec d → Vec d) : Prop :=
  IsPotentialOn U f ∧ IsSolenoidalOn U (fun x => matVecMul (a x) (f x))

theorem IsAHarmonicGradient.of_ae_eq_coeff {d : ℕ} {a b : CoeffField d}
    {U : Set (Vec d)} {f : Vec d → Vec d}
    (h : a =ᵐ[volumeMeasureOn U] b) (hf : IsAHarmonicGradient a U f) :
    IsAHarmonicGradient b U f := by
  rcases hf with ⟨hpot, hsol⟩
  refine ⟨hpot, ?_⟩
  intro φ
  calc
    ∫ x in U, vecDot (matVecMul (b x) (f x)) (φ.toH1Function.grad x)
        ∂MeasureTheory.volume
        =
      ∫ x in U, vecDot (matVecMul (a x) (f x)) (φ.toH1Function.grad x)
        ∂MeasureTheory.volume := by
          refine MeasureTheory.integral_congr_ae ?_
          exact h.symm.mono fun x hx => by
            simp [hx]
    _ = 0 := hsol φ

def IsAHarmonicPair {d : ℕ} (a : CoeffField d) (U : Set (Vec d))
    (f g : Vec d → Vec d) : Prop :=
  IsPotentialOn U f ∧
    IsSolenoidalOn U g ∧
    ∀ x, g x = matVecMul (a x) (f x)

def IsAdjointHarmonicPair {d : ℕ} (a : CoeffField d) (U : Set (Vec d))
    (f g : Vec d → Vec d) : Prop :=
  IsPotentialOn U f ∧
    IsSolenoidalOn U g ∧
    ∀ x, g x = matVecMul (matTranspose (a x)) (f x)

structure AHarmonicPair {d : ℕ} (a : CoeffField d) (U : Set (Vec d)) where
  grad : Vec d → Vec d
  flux : Vec d → Vec d
  isHarmonicPair : IsAHarmonicPair a U grad flux

structure AHarmonicFunction {d : ℕ} (a : CoeffField d) (U : Set (Vec d)) where
  toH1 : H1Function U
  isHarmonic : IsAHarmonicGradient a U toH1.grad

/-- Integrability of a vector flux paired with every `H10Function` test
gradient. This abbreviation keeps harmonic-combination headers small. -/
abbrev h10FluxIntegrable {d : ℕ} (U : Set (Vec d)) (F : Vec d → Vec d) : Prop :=
  ∀ φ : H10Function U,
    MeasureTheory.IntegrableOn (fun x => vecDot (F x) (φ.toH1Function.grad x)) U

/-- Integrability of the weak flux pairing attached to an `AHarmonicFunction`. -/
abbrev weakFluxIntegrable {d : ℕ} (U : Set (Vec d)) (a : CoeffField d)
    (u : AHarmonicFunction a U) : Prop :=
  h10FluxIntegrable U (fun x => matVecMul (a x) (u.toH1.grad x))

/-- Surface notation for adjoint-harmonic functions. This matches the Chapter-2
notation `𝒜*(U; a)` while reusing the existing `AHarmonicFunction` structure. -/
abbrev AStarHarmonicFunction {d : ℕ} (U : Set (Vec d)) (a : CoeffField d) :=
  AHarmonicFunction (fun x => matTranspose (a x)) U

structure AHarmonicFunctionMeanZero {d : ℕ} (a : CoeffField d) (U : Set (Vec d)) where
  toAHarmonicFunction : AHarmonicFunction a U
  meanZero : MeanZeroOn U toAHarmonicFunction.toH1.toFun

namespace AHarmonicFunctionMeanZero

instance {d : ℕ} {a : CoeffField d} {U : Set (Vec d)} :
    Coe (AHarmonicFunctionMeanZero a U) (AHarmonicFunction a U) where
  coe u := u.toAHarmonicFunction

@[simp] theorem coe_mk {d : ℕ} {a : CoeffField d} {U : Set (Vec d)}
    (u : AHarmonicFunction a U) (hmean : MeanZeroOn U u.toH1.toFun) :
    ((⟨u, hmean⟩ : AHarmonicFunctionMeanZero a U) : AHarmonicFunction a U) = u :=
  rfl

theorem meanZero_coe {d : ℕ} {a : CoeffField d} {U : Set (Vec d)}
    (u : AHarmonicFunctionMeanZero a U) :
    MeanZeroOn U (u : AHarmonicFunction a U).toH1.toFun :=
  u.meanZero

end AHarmonicFunctionMeanZero

private theorem isSolenoidalOn_add_of_integrable {d : ℕ} {U : Set (Vec d)}
    {f g : Vec d → Vec d} (hf : IsSolenoidalOn U f) (hg : IsSolenoidalOn U g)
    (hf_int : h10FluxIntegrable U f) (hg_int : h10FluxIntegrable U g) :
    IsSolenoidalOn U (f + g) := by
  intro φ
  rw [show (fun x => vecDot ((f + g) x) (φ.toH1Function.grad x)) =
      fun x => vecDot (f x) (φ.toH1Function.grad x) + vecDot (g x) (φ.toH1Function.grad x) by
        funext x
        simp [Pi.add_apply, vecDot_add_left]]
  rw [MeasureTheory.integral_add (hf_int φ) (hg_int φ), hf φ, hg φ]
  ring

theorem isAHarmonicGradient_zero {d : ℕ} {a : CoeffField d} {U : Set (Vec d)} :
    IsAHarmonicGradient a U (0 : Vec d → Vec d) := by
  constructor
  · exact isPotentialOn_zero
  · simpa [matVecMul_zero] using! (isSolenoidalOn_zero (U := U))

theorem isAHarmonicGradient_smul {d : ℕ} {a : CoeffField d} {U : Set (Vec d)}
    {f : Vec d → Vec d} (hf : IsAHarmonicGradient a U f) (c : ℝ) :
    IsAHarmonicGradient a U (c • f) := by
  rcases hf with ⟨hpot, hsol⟩
  constructor
  · exact isPotentialOn_smul hpot c
  · simpa [Pi.smul_apply, matVecMul_smul] using! isSolenoidalOn_smul hsol c

theorem isAHarmonicGradient_add_of_integrable {d : ℕ} {a : CoeffField d} {U : Set (Vec d)}
    {f g : Vec d → Vec d} (hf : IsAHarmonicGradient a U f) (hg : IsAHarmonicGradient a U g)
    (hf_int : h10FluxIntegrable U (fun x => matVecMul (a x) (f x)))
    (hg_int : h10FluxIntegrable U (fun x => matVecMul (a x) (g x))) :
    IsAHarmonicGradient a U (f + g) := by
  rcases hf with ⟨hpotf, hsolf⟩
  rcases hg with ⟨hpotg, hsolg⟩
  constructor
  · exact isPotentialOn_add hpotf hpotg
  · have hsum :
        IsSolenoidalOn U
          ((fun x => matVecMul (a x) (f x)) + fun x => matVecMul (a x) (g x)) :=
        isSolenoidalOn_add_of_integrable hsolf hsolg hf_int hg_int
    simpa [Pi.add_apply, matVecMul_add] using! hsum

theorem isAHarmonicPair_zero {d : ℕ} {a : CoeffField d} {U : Set (Vec d)} :
    IsAHarmonicPair a U (0 : Vec d → Vec d) 0 := by
  refine ⟨isPotentialOn_zero, ?_, ?_⟩
  · simpa using (isSolenoidalOn_zero (U := U))
  · intro x
    simp [matVecMul_zero]

theorem isAHarmonicPair_smul {d : ℕ} {a : CoeffField d} {U : Set (Vec d)}
    {f g : Vec d → Vec d} (hfg : IsAHarmonicPair a U f g) (c : ℝ) :
    IsAHarmonicPair a U (c • f) (c • g) := by
  rcases hfg with ⟨hpot, hsol, hflux⟩
  refine ⟨isPotentialOn_smul hpot c, isSolenoidalOn_smul hsol c, ?_⟩
  intro x
  simp [Pi.smul_apply, hflux x, matVecMul_smul]

theorem isAHarmonicPair_add_of_integrable {d : ℕ} {a : CoeffField d} {U : Set (Vec d)}
    {f1 g1 f2 g2 : Vec d → Vec d}
    (h1 : IsAHarmonicPair a U f1 g1) (h2 : IsAHarmonicPair a U f2 g2)
    (hg1_int : h10FluxIntegrable U g1) (hg2_int : h10FluxIntegrable U g2) :
    IsAHarmonicPair a U (f1 + f2) (g1 + g2) := by
  rcases h1 with ⟨hpot1, hsol1, hflux1⟩
  rcases h2 with ⟨hpot2, hsol2, hflux2⟩
  refine ⟨isPotentialOn_add hpot1 hpot2, ?_, ?_⟩
  · exact isSolenoidalOn_add_of_integrable hsol1 hsol2 hg1_int hg2_int
  · intro x
    simp [Pi.add_apply, hflux1 x, hflux2 x, matVecMul_add]

theorem isAHarmonicPair_of_isAHarmonicGradient {d : ℕ} {a : CoeffField d} {U : Set (Vec d)}
    {f : Vec d → Vec d} (hf : IsAHarmonicGradient a U f) :
    IsAHarmonicPair a U f (fun x => matVecMul (a x) (f x)) := by
  rcases hf with ⟨hpot, hsol⟩
  exact ⟨hpot, hsol, fun _ => rfl⟩

theorem isAHarmonicGradient_of_isAHarmonicPair {d : ℕ} {a : CoeffField d} {U : Set (Vec d)}
    {f g : Vec d → Vec d} (hfg : IsAHarmonicPair a U f g) :
    IsAHarmonicGradient a U f := by
  rcases hfg with ⟨hpot, hsol, hflux⟩
  refine ⟨hpot, ?_⟩
  simpa [funext hflux] using hsol

theorem IsAHarmonicGradient.restrict_of_isOpen_of_memVectorL2
    {d : ℕ} {a : CoeffField d} {U V : Set (Vec d)}
    [MeasureTheory.IsFiniteMeasure (volumeMeasureOn V)]
    {f : Vec d → Vec d} (hf : IsAHarmonicGradient a U f) (hU : IsOpen U) (hV : IsOpen V)
    (hVU : V ⊆ U) (hfluxV : MemVectorL2 V (fun x => matVecMul (a x) (f x))) :
    IsAHarmonicGradient a V f := by
  rcases hf with ⟨hpot, hsol⟩
  constructor
  · rcases hpot with ⟨u, hu⟩
    refine ⟨u.restrict hV hVU, ?_⟩
    simpa [H1Function.restrict] using hu
  · exact hsol.restrict_of_isOpen_of_memVectorL2 hU hV hVU hfluxV

theorem IsAHarmonicGradient.restrict_of_isOpen_of_isEllipticFieldOn
    {d : ℕ} {a : CoeffField d} {lam Lam : ℝ} {U V : Set (Vec d)}
    [MeasureTheory.IsFiniteMeasure (volumeMeasureOn V)]
    {f : Vec d → Vec d} (hf : IsAHarmonicGradient a U f) (hU : IsOpen U) (hV : IsOpen V)
    (hVU : V ⊆ U) (hEllV : IsEllipticFieldOn lam Lam V a) :
    IsAHarmonicGradient a V f := by
  rcases hf.1 with ⟨u, hu⟩
  refine hf.restrict_of_isOpen_of_memVectorL2 hU hV hVU ?_
  rw [← hu]
  exact memVectorL2_matVecMul_of_isEllipticFieldOn hEllV (u.restrict hV hVU).grad_memVectorL2

theorem isAdjointHarmonicPair_zero {d : ℕ} {a : CoeffField d} {U : Set (Vec d)} :
    IsAdjointHarmonicPair a U (0 : Vec d → Vec d) 0 := by
  refine ⟨isPotentialOn_zero, ?_, ?_⟩
  · simpa using (isSolenoidalOn_zero (U := U))
  · intro x
    simp [matVecMul_zero]

theorem isAdjointHarmonicPair_smul {d : ℕ} {a : CoeffField d} {U : Set (Vec d)}
    {f g : Vec d → Vec d} (hfg : IsAdjointHarmonicPair a U f g) (c : ℝ) :
    IsAdjointHarmonicPair a U (c • f) (c • g) := by
  rcases hfg with ⟨hpot, hsol, hflux⟩
  refine ⟨isPotentialOn_smul hpot c, isSolenoidalOn_smul hsol c, ?_⟩
  intro x
  simp [Pi.smul_apply, hflux x, matVecMul_smul]

theorem isAdjointHarmonicPair_add_of_integrable {d : ℕ} {a : CoeffField d} {U : Set (Vec d)}
    {f1 g1 f2 g2 : Vec d → Vec d}
    (h1 : IsAdjointHarmonicPair a U f1 g1) (h2 : IsAdjointHarmonicPair a U f2 g2)
    (hg1_int : h10FluxIntegrable U g1) (hg2_int : h10FluxIntegrable U g2) :
    IsAdjointHarmonicPair a U (f1 + f2) (g1 + g2) := by
  rcases h1 with ⟨hpot1, hsol1, hflux1⟩
  rcases h2 with ⟨hpot2, hsol2, hflux2⟩
  refine ⟨isPotentialOn_add hpot1 hpot2, ?_, ?_⟩
  · exact isSolenoidalOn_add_of_integrable hsol1 hsol2 hg1_int hg2_int
  · intro x
    simp [Pi.add_apply, hflux1 x, hflux2 x, matVecMul_add]

namespace AHarmonicPair

@[ext] theorem ext {d : ℕ} {a : CoeffField d} {U : Set (Vec d)}
    {X Y : AHarmonicPair a U} (hgrad : X.grad = Y.grad) (hflux : X.flux = Y.flux) :
    X = Y := by
  cases X
  cases Y
  cases hgrad
  cases hflux
  rfl

instance {d : ℕ} {a : CoeffField d} {U : Set (Vec d)} : Zero (AHarmonicPair a U) where
  zero :=
    { grad := 0
      flux := 0
      isHarmonicPair := isAHarmonicPair_zero }

instance {d : ℕ} {a : CoeffField d} {U : Set (Vec d)} : SMul ℝ (AHarmonicPair a U) where
  smul c X :=
    { grad := c • X.grad
      flux := c • X.flux
      isHarmonicPair := isAHarmonicPair_smul X.isHarmonicPair c }

@[simp] theorem grad_zero {d : ℕ} {a : CoeffField d} {U : Set (Vec d)} :
    (0 : AHarmonicPair a U).grad = 0 :=
  rfl

@[simp] theorem flux_zero {d : ℕ} {a : CoeffField d} {U : Set (Vec d)} :
    (0 : AHarmonicPair a U).flux = 0 :=
  rfl

@[simp] theorem grad_smul {d : ℕ} {a : CoeffField d} {U : Set (Vec d)}
    (c : ℝ) (X : AHarmonicPair a U) :
    (c • X).grad = c • X.grad :=
  rfl

@[simp] theorem flux_smul {d : ℕ} {a : CoeffField d} {U : Set (Vec d)}
    (c : ℝ) (X : AHarmonicPair a U) :
    (c • X).flux = c • X.flux :=
  rfl

def ofGradient {d : ℕ} {a : CoeffField d} {U : Set (Vec d)} {f : Vec d → Vec d}
    (hf : IsAHarmonicGradient a U f) : AHarmonicPair a U :=
  { grad := f
    flux := fun x => matVecMul (a x) (f x)
    isHarmonicPair := isAHarmonicPair_of_isAHarmonicGradient hf }

@[simp] theorem grad_ofGradient {d : ℕ} {a : CoeffField d} {U : Set (Vec d)}
    {f : Vec d → Vec d} (hf : IsAHarmonicGradient a U f) :
    (ofGradient hf).grad = f :=
  rfl

@[simp] theorem flux_ofGradient {d : ℕ} {a : CoeffField d} {U : Set (Vec d)}
    {f : Vec d → Vec d} (hf : IsAHarmonicGradient a U f) :
    (ofGradient hf).flux = fun x => matVecMul (a x) (f x) :=
  rfl

def addOfIntegrable {d : ℕ} {a : CoeffField d} {U : Set (Vec d)}
    (X Y : AHarmonicPair a U) (hX_int : h10FluxIntegrable U X.flux)
    (hY_int : h10FluxIntegrable U Y.flux) :
    AHarmonicPair a U :=
  { grad := X.grad + Y.grad
    flux := X.flux + Y.flux
    isHarmonicPair := isAHarmonicPair_add_of_integrable X.isHarmonicPair Y.isHarmonicPair
      hX_int hY_int }

@[simp] theorem grad_addOfIntegrable {d : ℕ} {a : CoeffField d} {U : Set (Vec d)}
    (X Y : AHarmonicPair a U) (hX_int : h10FluxIntegrable U X.flux)
    (hY_int : h10FluxIntegrable U Y.flux) :
    (addOfIntegrable X Y hX_int hY_int).grad = X.grad + Y.grad :=
  rfl

@[simp] theorem flux_addOfIntegrable {d : ℕ} {a : CoeffField d} {U : Set (Vec d)}
    (X Y : AHarmonicPair a U) (hX_int : h10FluxIntegrable U X.flux)
    (hY_int : h10FluxIntegrable U Y.flux) :
    (addOfIntegrable X Y hX_int hY_int).flux = X.flux + Y.flux :=
  rfl

end AHarmonicPair

def AHarmonicFunction.toPair {d : ℕ} {a : CoeffField d} {U : Set (Vec d)}
    (u : AHarmonicFunction a U) : AHarmonicPair a U :=
  AHarmonicPair.ofGradient u.isHarmonic

namespace AHarmonicFunction

noncomputable def addConst {d : ℕ} {a : CoeffField d} {U : Set (Vec d)}
    [MeasureTheory.IsFiniteMeasure (volumeMeasureOn U)]
    (u : AHarmonicFunction a U) (c : ℝ) : AHarmonicFunction a U :=
  let hgrad : (u.toH1.addConst c).grad = u.toH1.grad := by
    funext x
    simp
  { toH1 := u.toH1.addConst c
    isHarmonic := by
      simpa [hgrad] using u.isHarmonic }

@[simp] theorem toH1_addConst {d : ℕ} {a : CoeffField d} {U : Set (Vec d)}
    [MeasureTheory.IsFiniteMeasure (volumeMeasureOn U)]
    (u : AHarmonicFunction a U) (c : ℝ) :
    (u.addConst c).toH1 = u.toH1.addConst c :=
  rfl

@[simp] theorem grad_addConst {d : ℕ} {a : CoeffField d} {U : Set (Vec d)}
    [MeasureTheory.IsFiniteMeasure (volumeMeasureOn U)]
    (u : AHarmonicFunction a U) (c : ℝ) (x : Vec d) :
    (u.addConst c).toH1.grad x = u.toH1.grad x := by
  simp [AHarmonicFunction.addConst]

@[simp] theorem toPair_addConst {d : ℕ} {a : CoeffField d} {U : Set (Vec d)}
    [MeasureTheory.IsFiniteMeasure (volumeMeasureOn U)]
    (u : AHarmonicFunction a U) (c : ℝ) :
    (u.addConst c).toPair = u.toPair := by
  ext
  · simp [AHarmonicFunction.toPair, AHarmonicPair.ofGradient, AHarmonicFunction.addConst]
  · simp [AHarmonicFunction.toPair, AHarmonicPair.ofGradient, AHarmonicFunction.addConst]

noncomputable def normalizeMeanZero {d : ℕ} {a : CoeffField d} {U : Set (Vec d)}
    [MeasureTheory.IsFiniteMeasure (volumeMeasureOn U)]
    (u : AHarmonicFunction a U) : AHarmonicFunction a U :=
  let hgrad : u.toH1.subAverage.grad = u.toH1.grad := by
    funext x
    simp
  { toH1 := u.toH1.subAverage
    isHarmonic := by
      simpa [hgrad] using u.isHarmonic }

@[simp] theorem toH1_normalizeMeanZero {d : ℕ} {a : CoeffField d} {U : Set (Vec d)}
    [MeasureTheory.IsFiniteMeasure (volumeMeasureOn U)]
    (u : AHarmonicFunction a U) :
    u.normalizeMeanZero.toH1 = u.toH1.subAverage :=
  rfl

theorem meanZeroOn_normalizeMeanZero {d : ℕ} {a : CoeffField d} {U : Set (Vec d)}
    [MeasureTheory.IsFiniteMeasure (volumeMeasureOn U)]
    (u : AHarmonicFunction a U) :
    MeanZeroOn U u.normalizeMeanZero.toH1.toFun := by
  simpa [AHarmonicFunction.normalizeMeanZero] using u.toH1.meanZeroOn_subAverage

@[simp] theorem grad_normalizeMeanZero {d : ℕ} {a : CoeffField d} {U : Set (Vec d)}
    [MeasureTheory.IsFiniteMeasure (volumeMeasureOn U)]
    (u : AHarmonicFunction a U) (x : Vec d) :
    u.normalizeMeanZero.toH1.grad x = u.toH1.grad x := by
  simp [AHarmonicFunction.normalizeMeanZero]

noncomputable def toMeanZero {d : ℕ} {a : CoeffField d} {U : Set (Vec d)}
    [MeasureTheory.IsFiniteMeasure (volumeMeasureOn U)]
    (u : AHarmonicFunction a U) : AHarmonicFunctionMeanZero a U :=
  ⟨u.normalizeMeanZero, u.meanZeroOn_normalizeMeanZero⟩

@[simp] theorem coe_toMeanZero {d : ℕ} {a : CoeffField d} {U : Set (Vec d)}
    [MeasureTheory.IsFiniteMeasure (volumeMeasureOn U)]
    (u : AHarmonicFunction a U) :
    ((u.toMeanZero : AHarmonicFunctionMeanZero a U) : AHarmonicFunction a U) =
      u.normalizeMeanZero :=
  rfl

theorem meanZero_toMeanZero {d : ℕ} {a : CoeffField d} {U : Set (Vec d)}
    [MeasureTheory.IsFiniteMeasure (volumeMeasureOn U)]
    (u : AHarmonicFunction a U) :
    MeanZeroOn U ((u.toMeanZero : AHarmonicFunctionMeanZero a U) : AHarmonicFunction a U).toH1.toFun :=
  u.toMeanZero.meanZero

theorem integrableOn_smul {d : ℕ} {a : CoeffField d} {U : Set (Vec d)}
    (u : AHarmonicFunction a U) (hu_int : weakFluxIntegrable U a u) (c : ℝ) :
    h10FluxIntegrable U (fun x => matVecMul (a x) ((c • u.toH1).grad x)) := by
  intro φ
  change MeasureTheory.Integrable
    (fun x => vecDot (matVecMul (a x) ((c • u.toH1).grad x)) (φ.toH1Function.grad x))
    (MeasureTheory.volume.restrict U)
  rw [show
      (fun x => vecDot (matVecMul (a x) ((c • u.toH1).grad x)) (φ.toH1Function.grad x)) =
        fun x => c * vecDot (matVecMul (a x) (u.toH1.grad x)) (φ.toH1Function.grad x) by
          funext x
          change
            vecDot (matVecMul (a x) (c • u.toH1.grad x)) (φ.toH1Function.grad x) =
              c * vecDot (matVecMul (a x) (u.toH1.grad x)) (φ.toH1Function.grad x)
          rw [matVecMul_smul, vecDot_smul_left]]
  exact (hu_int φ).integrable.const_mul c

noncomputable def restrictOfMemVectorL2 {d : ℕ} {a : CoeffField d} {U V : Set (Vec d)}
    [MeasureTheory.IsFiniteMeasure (volumeMeasureOn V)]
    (u : AHarmonicFunction a U) (hU : IsOpen U) (hV : IsOpen V) (hVU : V ⊆ U)
    (hfluxV : MemVectorL2 V (fun x => matVecMul (a x) (u.toH1.grad x))) :
    AHarmonicFunction a V :=
  { toH1 := u.toH1.restrict hV hVU
    isHarmonic := u.isHarmonic.restrict_of_isOpen_of_memVectorL2 hU hV hVU hfluxV }

@[simp] theorem toH1_restrictOfMemVectorL2 {d : ℕ} {a : CoeffField d} {U V : Set (Vec d)}
    [MeasureTheory.IsFiniteMeasure (volumeMeasureOn V)]
    (u : AHarmonicFunction a U) (hU : IsOpen U) (hV : IsOpen V) (hVU : V ⊆ U)
    (hfluxV : MemVectorL2 V (fun x => matVecMul (a x) (u.toH1.grad x))) :
    (u.restrictOfMemVectorL2 hU hV hVU hfluxV).toH1 = u.toH1.restrict hV hVU :=
  rfl

noncomputable def restrictOfIsEllipticFieldOn {d : ℕ} {a : CoeffField d} {lam Lam : ℝ}
    {U V : Set (Vec d)} [MeasureTheory.IsFiniteMeasure (volumeMeasureOn V)]
    (u : AHarmonicFunction a U) (hU : IsOpen U) (hV : IsOpen V) (hVU : V ⊆ U)
    (hEllV : IsEllipticFieldOn lam Lam V a) :
    AHarmonicFunction a V :=
  u.restrictOfMemVectorL2 hU hV hVU
    (memVectorL2_matVecMul_of_isEllipticFieldOn hEllV (u.toH1.restrict hV hVU).grad_memVectorL2)

@[simp] theorem toH1_restrictOfIsEllipticFieldOn {d : ℕ} {a : CoeffField d} {lam Lam : ℝ}
    {U V : Set (Vec d)} [MeasureTheory.IsFiniteMeasure (volumeMeasureOn V)]
    (u : AHarmonicFunction a U) (hU : IsOpen U) (hV : IsOpen V) (hVU : V ⊆ U)
    (hEllV : IsEllipticFieldOn lam Lam V a) :
    (u.restrictOfIsEllipticFieldOn hU hV hVU hEllV).toH1 = u.toH1.restrict hV hVU :=
  rfl

def addOfIntegrable {d : ℕ} {a : CoeffField d} {U : Set (Vec d)}
    (u v : AHarmonicFunction a U)
    (hu_int : weakFluxIntegrable U a u) (hv_int : weakFluxIntegrable U a v) :
    AHarmonicFunction a U :=
  { toH1 := u.toH1 + v.toH1
    isHarmonic := isAHarmonicGradient_add_of_integrable u.isHarmonic v.isHarmonic hu_int hv_int }

@[simp] theorem toH1_addOfIntegrable {d : ℕ} {a : CoeffField d} {U : Set (Vec d)}
    (u v : AHarmonicFunction a U)
    (hu_int : weakFluxIntegrable U a u) (hv_int : weakFluxIntegrable U a v) :
    (addOfIntegrable u v hu_int hv_int).toH1 = u.toH1 + v.toH1 :=
  rfl

@[simp] theorem grad_addOfIntegrable {d : ℕ} {a : CoeffField d} {U : Set (Vec d)}
    (u v : AHarmonicFunction a U)
    (hu_int : weakFluxIntegrable U a u) (hv_int : weakFluxIntegrable U a v) :
    (addOfIntegrable u v hu_int hv_int).toH1.grad = u.toH1.grad + v.toH1.grad :=
  rfl

def addSMulOfIntegrable {d : ℕ} {a : CoeffField d} {U : Set (Vec d)}
    (u w : AHarmonicFunction a U)
    (hu_int : weakFluxIntegrable U a u) (hw_int : weakFluxIntegrable U a w) (c : ℝ) :
    AHarmonicFunction a U :=
  addOfIntegrable u
    { toH1 := c • w.toH1
      isHarmonic := isAHarmonicGradient_smul w.isHarmonic c }
    hu_int
    (integrableOn_smul w hw_int c)

@[simp] theorem toH1_addSMulOfIntegrable {d : ℕ} {a : CoeffField d} {U : Set (Vec d)}
    (u w : AHarmonicFunction a U)
    (hu_int : weakFluxIntegrable U a u) (hw_int : weakFluxIntegrable U a w) (c : ℝ) :
    (addSMulOfIntegrable u w hu_int hw_int c).toH1 = u.toH1 + c • w.toH1 :=
  rfl

@[simp] theorem grad_addSMulOfIntegrable {d : ℕ} {a : CoeffField d} {U : Set (Vec d)}
    (u w : AHarmonicFunction a U)
    (hu_int : weakFluxIntegrable U a u) (hw_int : weakFluxIntegrable U a w) (c : ℝ) :
    (addSMulOfIntegrable u w hu_int hw_int c).toH1.grad = u.toH1.grad + c • w.toH1.grad :=
  rfl

end AHarmonicFunction

end Homogenization
