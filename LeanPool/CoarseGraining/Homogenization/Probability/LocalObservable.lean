/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/
module


public import LeanPool.CoarseGraining.Homogenization.Probability.RandomCoeffField
public import Mathlib.MeasureTheory.Group.Arithmetic
public import Mathlib.MeasureTheory.Measure.AEMeasurable

/-! # Local Observable -/

@[expose] public section

namespace Homogenization

/-!
Generic measurable local observables on coefficient space.

This file packages the common probability-theoretic pattern:

- a coefficient-space observable is measurable;
- it depends only on the coefficient field inside a deterministic region `U`;
- therefore its law and its Bochner integrals depend only on the restricted
  law `Measure.map (restrictCoeffField U) P`.

Concrete coarse observables such as `Mu U P`, the coarse matrix entries, and
their matrix-valued packages should be bundled as instances of
`MeasurableLocalObservable` in downstream files.
-/

theorem restrictCoeffField_eq_of_forall_mem_eq {d : ℕ} {U : Set (Vec d)}
    {a₁ a₂ : CoeffField d} (h : ∀ x ∈ U, a₁ x = a₂ x) :
    restrictCoeffField U a₁ = restrictCoeffField U a₂ := by
  funext x
  by_cases hx : x ∈ U
  · simp [restrictCoeffField, hx, h x hx]
  · simp [restrictCoeffField, hx]

theorem comp_restrictCoeffField_eq_of_isRestrictionLocalObservable {β : Type*} {d : ℕ}
    {U : Set (Vec d)} {X : CoeffField d → β} (hX : IsRestrictionLocalObservable U X) :
    X ∘ restrictCoeffField U = X := by
  funext a
  exact hX (by
    intro x hx
    simp [restrictCoeffField, hx])

/-- Compatibility spelling for the restriction-local restriction identity. -/
theorem comp_restrictCoeffField_eq_of_isLocalObservable {β : Type*} {d : ℕ}
    {U : Set (Vec d)} {X : CoeffField d → β} (hX : IsLocalObservable U X) :
    X ∘ restrictCoeffField U = X :=
  comp_restrictCoeffField_eq_of_isRestrictionLocalObservable hX

theorem map_eq_map_restrictCoeffField_of_isRestrictionLocalObservable
    {β : Type*} [MeasurableSpace β] {d : ℕ} {U : Set (Vec d)}
    {P : MeasureTheory.Measure (CoeffField d)} {X : CoeffField d → β}
    (hX_meas : Measurable X) (hX_local : IsRestrictionLocalObservable U X) :
    MeasureTheory.Measure.map X (MeasureTheory.Measure.map (restrictCoeffField U) P) =
      MeasureTheory.Measure.map X P := by
  calc
    MeasureTheory.Measure.map X (MeasureTheory.Measure.map (restrictCoeffField U) P) =
        MeasureTheory.Measure.map (X ∘ restrictCoeffField U) P := by
          simpa [Function.comp] using
            (MeasureTheory.Measure.map_map hX_meas (measurable_restrictCoeffField U) (μ := P))
    _ = MeasureTheory.Measure.map X P := by
      rw [comp_restrictCoeffField_eq_of_isRestrictionLocalObservable hX_local]

/-- Compatibility spelling for the restriction-local map identity. -/
theorem map_eq_map_restrictCoeffField_of_isLocalObservable
    {β : Type*} [MeasurableSpace β] {d : ℕ} {U : Set (Vec d)}
    {P : MeasureTheory.Measure (CoeffField d)} {X : CoeffField d → β}
    (hX_meas : Measurable X) (hX_local : IsRestrictionLocalObservable U X) :
    MeasureTheory.Measure.map X (MeasureTheory.Measure.map (restrictCoeffField U) P) =
      MeasureTheory.Measure.map X P :=
  map_eq_map_restrictCoeffField_of_isRestrictionLocalObservable hX_meas hX_local

theorem map_eq_of_map_restrictCoeffField_eq_of_isRestrictionLocalObservable
    {β : Type*} [MeasurableSpace β] {d : ℕ} {U : Set (Vec d)}
    {P Q : MeasureTheory.Measure (CoeffField d)} {X : CoeffField d → β}
    (hX_meas : Measurable X) (hX_local : IsRestrictionLocalObservable U X)
    (hPQ : MeasureTheory.Measure.map (restrictCoeffField U) P =
      MeasureTheory.Measure.map (restrictCoeffField U) Q) :
    MeasureTheory.Measure.map X P = MeasureTheory.Measure.map X Q := by
  calc
    MeasureTheory.Measure.map X P =
        MeasureTheory.Measure.map X (MeasureTheory.Measure.map (restrictCoeffField U) P) := by
          symm
          exact map_eq_map_restrictCoeffField_of_isRestrictionLocalObservable
            (P := P) hX_meas hX_local
    _ = MeasureTheory.Measure.map X (MeasureTheory.Measure.map (restrictCoeffField U) Q) := by
      rw [hPQ]
    _ = MeasureTheory.Measure.map X Q :=
      map_eq_map_restrictCoeffField_of_isRestrictionLocalObservable
        (P := Q) hX_meas hX_local

/-- Compatibility spelling for the restriction-local map comparison. -/
theorem map_eq_of_map_restrictCoeffField_eq_of_isLocalObservable
    {β : Type*} [MeasurableSpace β] {d : ℕ} {U : Set (Vec d)}
    {P Q : MeasureTheory.Measure (CoeffField d)} {X : CoeffField d → β}
    (hX_meas : Measurable X) (hX_local : IsLocalObservable U X)
    (hPQ : MeasureTheory.Measure.map (restrictCoeffField U) P =
      MeasureTheory.Measure.map (restrictCoeffField U) Q) :
    MeasureTheory.Measure.map X P = MeasureTheory.Measure.map X Q :=
  map_eq_of_map_restrictCoeffField_eq_of_isRestrictionLocalObservable hX_meas hX_local hPQ

theorem integral_map_restrictCoeffField_eq_of_isRestrictionLocalObservable
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
    {d : ℕ} {U : Set (Vec d)} {P : MeasureTheory.Measure (CoeffField d)}
    {X : CoeffField d → E}
    (hX_meas : Measurable X) (hX_local : IsRestrictionLocalObservable U X) :
    ∫ a, X a ∂(MeasureTheory.Measure.map (restrictCoeffField U) P) = ∫ a, X a ∂P := by
  rw [MeasureTheory.integral_map (measurable_restrictCoeffField U).aemeasurable]
  · apply MeasureTheory.integral_congr_ae
    exact Filter.Eventually.of_forall <| fun a =>
      congrFun (comp_restrictCoeffField_eq_of_isRestrictionLocalObservable hX_local) a
  · exact hX_meas.aestronglyMeasurable

/-- Compatibility spelling for the restriction-local integral identity. -/
theorem integral_map_restrictCoeffField_eq_of_isLocalObservable
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
    {d : ℕ} {U : Set (Vec d)} {P : MeasureTheory.Measure (CoeffField d)}
    {X : CoeffField d → E}
    (hX_meas : Measurable X) (hX_local : IsLocalObservable U X) :
    ∫ a, X a ∂(MeasureTheory.Measure.map (restrictCoeffField U) P) = ∫ a, X a ∂P :=
  integral_map_restrictCoeffField_eq_of_isRestrictionLocalObservable hX_meas hX_local

theorem integral_eq_of_map_restrictCoeffField_eq_of_isRestrictionLocalObservable
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
    {d : ℕ} {U : Set (Vec d)}
    {P Q : MeasureTheory.Measure (CoeffField d)} {X : CoeffField d → E}
    (hX_meas : Measurable X) (hX_local : IsRestrictionLocalObservable U X)
    (hPQ : MeasureTheory.Measure.map (restrictCoeffField U) P =
      MeasureTheory.Measure.map (restrictCoeffField U) Q) :
    ∫ a, X a ∂P = ∫ a, X a ∂Q := by
  calc
    ∫ a, X a ∂P = ∫ a, X a ∂(MeasureTheory.Measure.map (restrictCoeffField U) P) := by
      symm
      exact integral_map_restrictCoeffField_eq_of_isRestrictionLocalObservable
        (P := P) hX_meas hX_local
    _ = ∫ a, X a ∂(MeasureTheory.Measure.map (restrictCoeffField U) Q) := by
      rw [hPQ]
    _ = ∫ a, X a ∂Q :=
      integral_map_restrictCoeffField_eq_of_isRestrictionLocalObservable
        (P := Q) hX_meas hX_local

/-- Compatibility spelling for the restriction-local integral comparison. -/
theorem integral_eq_of_map_restrictCoeffField_eq_of_isLocalObservable
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
    {d : ℕ} {U : Set (Vec d)}
    {P Q : MeasureTheory.Measure (CoeffField d)} {X : CoeffField d → E}
    (hX_meas : Measurable X) (hX_local : IsLocalObservable U X)
    (hPQ : MeasureTheory.Measure.map (restrictCoeffField U) P =
      MeasureTheory.Measure.map (restrictCoeffField U) Q) :
    ∫ a, X a ∂P = ∫ a, X a ∂Q :=
  integral_eq_of_map_restrictCoeffField_eq_of_isRestrictionLocalObservable hX_meas hX_local hPQ

theorem measurable_of_isRestrictionLocalObservable_restrictionSigma
    {β : Type*} [MeasurableSpace β] {d : ℕ} {U : Set (Vec d)}
    {X : CoeffField d → β}
    (hX_meas : Measurable X) (hX_local : IsRestrictionLocalObservable U X) :
    @Measurable (CoeffField d) β (RestrictionSigma U) _ X := by
  simpa [Function.comp, comp_restrictCoeffField_eq_of_isRestrictionLocalObservable hX_local] using
    hX_meas.comp (measurable_restrictCoeffField_restrictionSigma (d := d) U)

theorem IsRestrictionLocalObservable.mono {β : Type*} {d : ℕ} {U V : Set (Vec d)}
    {X : CoeffField d → β} (hX : IsRestrictionLocalObservable U X) (hUV : U ⊆ V) :
    IsRestrictionLocalObservable V X := by
  intro a₁ a₂ hagree
  exact hX fun x hx => hagree x (hUV hx)

/-- Compatibility spelling for `IsRestrictionLocalObservable.mono`. -/
theorem IsLocalObservable.mono {β : Type*} {d : ℕ} {U V : Set (Vec d)}
    {X : CoeffField d → β} (hX : IsLocalObservable U X) (hUV : U ⊆ V) :
    IsLocalObservable V X :=
  IsRestrictionLocalObservable.mono hX hUV

/-- Compatibility spelling for the restriction-local measurability theorem. -/
theorem measurable_of_isLocalObservable_restrictionSigma
    {β : Type*} [MeasurableSpace β] {d : ℕ} {U : Set (Vec d)}
    {X : CoeffField d → β}
    (hX_meas : Measurable X) (hX_local : IsLocalObservable U X) :
    @Measurable (CoeffField d) β (RestrictionSigma U) _ X :=
  measurable_of_isRestrictionLocalObservable_restrictionSigma hX_meas hX_local

theorem measurable_of_isRestrictionLocalObservable_restrictionSigma_mono
    {β : Type*} [MeasurableSpace β] {d : ℕ} {U V : Set (Vec d)}
    {X : CoeffField d → β} (hX_meas : Measurable X) (hX_local : IsRestrictionLocalObservable U X)
    (hUV : U ⊆ V) :
    @Measurable (CoeffField d) β (RestrictionSigma V) _ X :=
  measurable_of_isRestrictionLocalObservable_restrictionSigma hX_meas (hX_local.mono hUV)

/-- Compatibility spelling for the monotone restriction-local measurability theorem. -/
theorem measurable_of_isLocalObservable_restrictionSigma_mono
    {β : Type*} [MeasurableSpace β] {d : ℕ} {U V : Set (Vec d)}
    {X : CoeffField d → β} (hX_meas : Measurable X) (hX_local : IsLocalObservable U X)
    (hUV : U ⊆ V) :
    @Measurable (CoeffField d) β (RestrictionSigma V) _ X :=
  measurable_of_isRestrictionLocalObservable_restrictionSigma_mono hX_meas hX_local hUV

theorem comp_translateByInt_eq_of_isTranslationCovariant
    {β : Type*} {d : ℕ} {X : Set (Vec d) → CoeffField d → β}
    (hX : IsTranslationCovariant X) (U : Set (Vec d)) (z : Fin d → ℤ) :
    X (translateSet (intVecToRealVec z) U) = X U ∘ translateByInt z := by
  funext a
  exact hX U z a

theorem map_eq_map_translateByInt_of_isTranslationCovariant
    {β : Type*} [MeasurableSpace β] {d : ℕ}
    {P : MeasureTheory.Measure (CoeffField d)}
    {X : Set (Vec d) → CoeffField d → β}
    (hP : IsStationary P) {U : Set (Vec d)} (hX_meas : Measurable (X U))
    (hX_cov : IsTranslationCovariant X) (z : Fin d → ℤ) :
    MeasureTheory.Measure.map (X (translateSet (intVecToRealVec z) U)) P =
      MeasureTheory.Measure.map (X U) P := by
  calc
    MeasureTheory.Measure.map (X (translateSet (intVecToRealVec z) U)) P =
        MeasureTheory.Measure.map ((X U) ∘ translateByInt z) P := by
          rw [comp_translateByInt_eq_of_isTranslationCovariant hX_cov U z]
    _ = MeasureTheory.Measure.map (X U) (MeasureTheory.Measure.map (translateByInt z) P) := by
      symm
      simpa [Function.comp] using
        (MeasureTheory.Measure.map_map hX_meas (measurable_translateByInt z) (μ := P))
    _ = MeasureTheory.Measure.map (X U) P := by
      rw [hP z]

/-- A.e.-measurable version of
`map_eq_map_translateByInt_of_isTranslationCovariant`. -/
theorem map_eq_map_translateByInt_of_isTranslationCovariant_aemeasurable
    {β : Type*} [MeasurableSpace β] {d : ℕ}
    {P : MeasureTheory.Measure (CoeffField d)}
    {X : Set (Vec d) → CoeffField d → β}
    (hP : IsStationary P) {U : Set (Vec d)}
    (hX_aemeas : AEMeasurable (X U) P)
    (hX_cov : IsTranslationCovariant X) (z : Fin d → ℤ) :
    MeasureTheory.Measure.map (X (translateSet (intVecToRealVec z) U)) P =
      MeasureTheory.Measure.map (X U) P := by
  calc
    MeasureTheory.Measure.map (X (translateSet (intVecToRealVec z) U)) P =
        MeasureTheory.Measure.map ((X U) ∘ translateByInt z) P := by
          rw [comp_translateByInt_eq_of_isTranslationCovariant hX_cov U z]
    _ = MeasureTheory.Measure.map (X U) (MeasureTheory.Measure.map (translateByInt z) P) := by
      symm
      exact AEMeasurable.map_map_of_aemeasurable
        (by simpa [hP z] using hX_aemeas)
        (measurable_translateByInt z).aemeasurable
    _ = MeasureTheory.Measure.map (X U) P := by
      rw [hP z]

theorem integral_eq_of_isTranslationCovariant_of_isStationary
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
    {d : ℕ} {P : MeasureTheory.Measure (CoeffField d)}
    {X : Set (Vec d) → CoeffField d → E}
    (hP : IsStationary P) {U : Set (Vec d)} (hX_meas : Measurable (X U))
    (hX_cov : IsTranslationCovariant X) (z : Fin d → ℤ) :
    ∫ a, X (translateSet (intVecToRealVec z) U) a ∂P = ∫ a, X U a ∂P := by
  rw [comp_translateByInt_eq_of_isTranslationCovariant hX_cov U z]
  exact integral_comp_eq_of_map_eq
    (measurable_translateByInt z) (hP z) (X U) hX_meas.aestronglyMeasurable

theorem integral_eq_of_isTranslationCovariant_of_isStationary_aestronglyMeasurable
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
    {d : ℕ} {P : MeasureTheory.Measure (CoeffField d)}
    {X : Set (Vec d) → CoeffField d → E}
    (hP : IsStationary P) {U : Set (Vec d)}
    (hX_aemeas : MeasureTheory.AEStronglyMeasurable (X U) P)
    (hX_cov : IsTranslationCovariant X) (z : Fin d → ℤ) :
    ∫ a, X (translateSet (intVecToRealVec z) U) a ∂P = ∫ a, X U a ∂P := by
  rw [comp_translateByInt_eq_of_isTranslationCovariant hX_cov U z]
  exact integral_comp_eq_of_map_eq
    (measurable_translateByInt z) (hP z) (X U) hX_aemeas

/-- A coefficient-space observable that is both measurable and pointwise
restriction-local on `U`. -/
structure MeasurableLocalObservable (d : ℕ) (U : Set (Vec d)) (β : Type*)
    [MeasurableSpace β] where
  toFun : CoeffField d → β
  measurable_toFun : Measurable toFun
  isLocal_toFun : IsRestrictionLocalObservable U toFun

namespace MeasurableLocalObservable

variable {β : Type*} [MeasurableSpace β] {d : ℕ} {U : Set (Vec d)}

instance : CoeFun (MeasurableLocalObservable d U β) (fun _ => CoeffField d → β) := ⟨toFun⟩

theorem measurable (X : MeasurableLocalObservable d U β) : Measurable X :=
  X.measurable_toFun

theorem isLocal (X : MeasurableLocalObservable d U β) : IsLocalObservable U X :=
  X.isLocal_toFun

/-- The explicit restriction-local spelling of the bundled locality field. -/
theorem isRestrictionLocal (X : MeasurableLocalObservable d U β) :
    IsRestrictionLocalObservable U X :=
  X.isLocal_toFun

theorem measurable_restrictionSigma (X : MeasurableLocalObservable d U β) :
    @Measurable (CoeffField d) β (RestrictionSigma U) _ X :=
  measurable_of_isRestrictionLocalObservable_restrictionSigma X.measurable X.isRestrictionLocal

theorem measurable_restrictionSigma_mono {V : Set (Vec d)}
    (X : MeasurableLocalObservable d U β) (hUV : U ⊆ V) :
    @Measurable (CoeffField d) β (RestrictionSigma V) _ X :=
  measurable_of_isRestrictionLocalObservable_restrictionSigma_mono X.measurable X.isRestrictionLocal hUV

def mono {V : Set (Vec d)} (X : MeasurableLocalObservable d U β) (hUV : U ⊆ V) :
    MeasurableLocalObservable d V β where
  toFun := X
  measurable_toFun := X.measurable
  isLocal_toFun := X.isRestrictionLocal.mono hUV

@[simp] theorem mono_apply {V : Set (Vec d)} (X : MeasurableLocalObservable d U β)
    (hUV : U ⊆ V) (a : CoeffField d) :
    X.mono hUV a = X a :=
  rfl

def const (c : β) : MeasurableLocalObservable d U β where
  toFun := fun _ => c
  measurable_toFun := measurable_const
  isLocal_toFun := by intro _ _ _; rfl

def comp {γ : Type*} [MeasurableSpace γ] (X : MeasurableLocalObservable d U β)
    (f : β → γ) (hf : Measurable f) : MeasurableLocalObservable d U γ where
  toFun := f ∘ X
  measurable_toFun := hf.comp X.measurable
  isLocal_toFun := by
    intro a₁ a₂ hagree
    simpa [Function.comp] using congrArg f (X.isRestrictionLocal hagree)

def prod {γ : Type*} [MeasurableSpace γ]
    (X : MeasurableLocalObservable d U β) (Y : MeasurableLocalObservable d U γ) :
    MeasurableLocalObservable d U (β × γ) where
  toFun := fun a => (X a, Y a)
  measurable_toFun := by
    simpa using (X.measurable).prodMk Y.measurable
  isLocal_toFun := by
    intro a₁ a₂ hagree
    simp [X.isRestrictionLocal hagree, Y.isRestrictionLocal hagree]

def pi {ι : Type*} {γ : ι → Type*} [∀ i, MeasurableSpace (γ i)]
    (X : ∀ i, MeasurableLocalObservable d U (γ i)) :
    MeasurableLocalObservable d U (∀ i, γ i) where
  toFun := fun a i => X i a
  measurable_toFun := by
    rw [measurable_pi_iff]
    intro i
    exact (X i).measurable
  isLocal_toFun := by
    intro a₁ a₂ hagree
    funext i
    exact (X i).isRestrictionLocal hagree

def neg {β : Type*} [MeasurableSpace β] [Neg β] [MeasurableNeg β]
    (X : MeasurableLocalObservable d U β) :
    MeasurableLocalObservable d U β :=
  X.comp (fun x => -x) measurable_neg

def add {β : Type*} [MeasurableSpace β] [Add β] [MeasurableAdd₂ β]
    (X Y : MeasurableLocalObservable d U β) :
    MeasurableLocalObservable d U β where
  toFun := fun a => X a + Y a
  measurable_toFun := X.measurable.add Y.measurable
  isLocal_toFun := by
    intro a₁ a₂ hagree
    simp [X.isRestrictionLocal hagree, Y.isRestrictionLocal hagree]

def sub {β : Type*} [MeasurableSpace β] [Sub β] [MeasurableSub₂ β]
    (X Y : MeasurableLocalObservable d U β) :
    MeasurableLocalObservable d U β where
  toFun := fun a => X a - Y a
  measurable_toFun := X.measurable.sub Y.measurable
  isLocal_toFun := by
    intro a₁ a₂ hagree
    simp [X.isRestrictionLocal hagree, Y.isRestrictionLocal hagree]

def const_smul {M : Type*} [SMul M β] [MeasurableConstSMul M β]
    (c : M) (X : MeasurableLocalObservable d U β) :
    MeasurableLocalObservable d U β where
  toFun := fun a => c • X a
  measurable_toFun := X.measurable.const_smul c
  isLocal_toFun := by
    intro a₁ a₂ hagree
    simp [X.isRestrictionLocal hagree]

def finsetPi {ι : Type*} [DecidableEq ι] {γ : ι → Type*} [∀ i, MeasurableSpace (γ i)]
    (s : Finset ι) {V : ι → Set (Vec d)}
    (X : ∀ i, MeasurableLocalObservable d (V i) (γ i)) :
    MeasurableLocalObservable d (⋃ i ∈ s, V i) (∀ i : s, γ i) where
  toFun := fun a i => X i a
  measurable_toFun := by
    rw [measurable_pi_iff]
    intro i
    exact (X i).measurable
  isLocal_toFun := by
    intro a₁ a₂ hagree
    funext i
    exact (X i).isRestrictionLocal fun x hx => hagree x <| by
      refine Set.mem_iUnion.2 ?_
      refine ⟨(i : ι), ?_⟩
      refine Set.mem_iUnion.2 ?_
      exact ⟨i.property, hx⟩

theorem measurable_subtypeFinsetSum {ι : Type*} (s : Finset ι)
    {γ : Type*} [MeasurableSpace γ] [AddCommMonoid γ] [MeasurableAdd₂ γ] :
    Measurable (fun y : s → γ => ∑ i, y i) := by
  exact Finset.univ.measurable_sum fun i _ => measurable_pi_apply i

noncomputable def finsetSum {ι : Type*} [DecidableEq ι] {γ : Type*}
    [MeasurableSpace γ] [AddCommMonoid γ] [MeasurableAdd₂ γ]
    (s : Finset ι) {V : ι → Set (Vec d)}
    (X : ∀ i, MeasurableLocalObservable d (V i) γ) :
    MeasurableLocalObservable d (⋃ i ∈ s, V i) γ :=
  (finsetPi (d := d) (s := s) X).comp (fun y : s → γ => ∑ i, y i)
    (measurable_subtypeFinsetSum s)

noncomputable def finsetAverage {ι : Type*} [DecidableEq ι] {γ : Type*}
    [MeasurableSpace γ] [AddCommMonoid γ] [MeasurableAdd₂ γ]
    [SMul ℝ γ] [MeasurableConstSMul ℝ γ]
    (s : Finset ι) {V : ι → Set (Vec d)}
    (X : ∀ i, MeasurableLocalObservable d (V i) γ) :
    MeasurableLocalObservable d (⋃ i ∈ s, V i) γ :=
  (finsetSum (d := d) (s := s) X).const_smul ((s.card : ℝ)⁻¹)

theorem comp_restrictCoeffField_eq (X : MeasurableLocalObservable d U β) :
    X ∘ restrictCoeffField U = X :=
  comp_restrictCoeffField_eq_of_isRestrictionLocalObservable X.isRestrictionLocal

theorem map_eq_map_restrictCoeffField
    (X : MeasurableLocalObservable d U β)
    {P : MeasureTheory.Measure (CoeffField d)} :
    MeasureTheory.Measure.map X (MeasureTheory.Measure.map (restrictCoeffField U) P) =
      MeasureTheory.Measure.map X P :=
  map_eq_map_restrictCoeffField_of_isRestrictionLocalObservable X.measurable X.isRestrictionLocal

theorem map_eq_of_map_restrictCoeffField_eq
    (X : MeasurableLocalObservable d U β)
    {P Q : MeasureTheory.Measure (CoeffField d)}
    (hPQ : MeasureTheory.Measure.map (restrictCoeffField U) P =
      MeasureTheory.Measure.map (restrictCoeffField U) Q) :
    MeasureTheory.Measure.map X P = MeasureTheory.Measure.map X Q :=
  map_eq_of_map_restrictCoeffField_eq_of_isRestrictionLocalObservable
    X.measurable X.isRestrictionLocal hPQ

theorem measurable_comp_randomCoeffField
    {Ω : Type*} [MeasurableSpace Ω] (X : MeasurableLocalObservable d U β)
    (A : RandomCoeffField Ω d) :
    Measurable fun ω => X (A ω) :=
  X.measurable.comp A.measurable

theorem measurable_comp_randomCoeffField_restrictionSigma
    {Ω : Type*} [MeasurableSpace Ω] (X : MeasurableLocalObservable d U β)
    (A : RandomCoeffField Ω d) :
    @Measurable Ω β (A.restrictionSigma U) _ (fun ω => X (A ω)) := by
  exact X.measurable_restrictionSigma.comp (A.measurable_restrictionSigma U)

theorem indepFun_of_indep_restrictionSigma
    {γ : Type*} [MeasurableSpace γ] {V : Set (Vec d)}
    {P : MeasureTheory.Measure (CoeffField d)}
    (hP : ProbabilityTheory.Indep (RestrictionSigma U) (RestrictionSigma V) P)
    (X : MeasurableLocalObservable d U β) (Y : MeasurableLocalObservable d V γ) :
    ProbabilityTheory.IndepFun X Y P := by
  exact ProbabilityTheory.indep_of_indep_of_le_right
    (m₃ := MeasurableSpace.comap Y inferInstance)
    (ProbabilityTheory.indep_of_indep_of_le_left
      (m₃ := MeasurableSpace.comap X inferInstance) hP
      (Measurable.comap_le X.measurable_restrictionSigma))
    (Measurable.comap_le Y.measurable_restrictionSigma)

theorem integral_map_restrictCoeffField_eq
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
    {U : Set (Vec d)} (X : MeasurableLocalObservable d U E)
    {P : MeasureTheory.Measure (CoeffField d)} :
    ∫ a, X a ∂(MeasureTheory.Measure.map (restrictCoeffField U) P) = ∫ a, X a ∂P :=
  integral_map_restrictCoeffField_eq_of_isRestrictionLocalObservable X.measurable X.isRestrictionLocal

theorem integral_eq_of_map_restrictCoeffField_eq
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
    {U : Set (Vec d)} (X : MeasurableLocalObservable d U E)
    {P Q : MeasureTheory.Measure (CoeffField d)}
    (hPQ : MeasureTheory.Measure.map (restrictCoeffField U) P =
      MeasureTheory.Measure.map (restrictCoeffField U) Q) :
    ∫ a, X a ∂P = ∫ a, X a ∂Q :=
  integral_eq_of_map_restrictCoeffField_eq_of_isRestrictionLocalObservable
    X.measurable X.isRestrictionLocal hPQ

theorem iIndepFun_of_isRestrictionUnitRangeDependent
    {ι : Type*} [DecidableEq ι] {γ : ι → Type*} [∀ i, MeasurableSpace (γ i)]
    {P : MeasureTheory.Measure (CoeffField d)} [MeasureTheory.IsProbabilityMeasure P]
    {V : ι → Set (Vec d)} (hP : IsRestrictionUnitRangeDependent P)
    (hsep : Pairwise fun i j => AreUnitSeparated (V i) (V j))
    (X : ∀ i, MeasurableLocalObservable d (V i) (γ i)) :
    ProbabilityTheory.iIndepFun (fun i => X i) P := by
  rw [ProbabilityTheory.iIndepFun_iff_iIndep]
  rw [ProbabilityTheory.iIndep_iff]
  intro s f hf
  exact (ProbabilityTheory.iIndep_iff (fun i => RestrictionSigma (V i)) P).1
    (iIndep_restrictionSigma_of_isRestrictionUnitRangeDependent (d := d) hP hsep) s
    (fun i hi => (Measurable.comap_le (X i).measurable_restrictionSigma) (f i) (hf i hi))

theorem indepFun_finset_of_isRestrictionUnitRangeDependent
    {ι : Type*} [DecidableEq ι] {γ : ι → Type*} [∀ i, MeasurableSpace (γ i)]
    {P : MeasureTheory.Measure (CoeffField d)} [MeasureTheory.IsProbabilityMeasure P]
    {V : ι → Set (Vec d)} (hP : IsRestrictionUnitRangeDependent P)
    (hsep : Pairwise fun i j => AreUnitSeparated (V i) (V j))
    (X : ∀ i, MeasurableLocalObservable d (V i) (γ i))
    (S T : Finset ι) (hST : Disjoint S T) :
    ProbabilityTheory.IndepFun (fun a (i : S) => X i a) (fun a (i : T) => X i a) P := by
  exact (iIndepFun_of_isRestrictionUnitRangeDependent (d := d) hP hsep X).indepFun_finset S T hST
    (fun i => (X i).measurable)

theorem indepFun_finsetSum_of_isRestrictionUnitRangeDependent
    {ι : Type*} [DecidableEq ι] {γ : Type*} [MeasurableSpace γ]
    [AddCommMonoid γ] [MeasurableAdd₂ γ]
    {P : MeasureTheory.Measure (CoeffField d)} [MeasureTheory.IsProbabilityMeasure P]
    {V : ι → Set (Vec d)} (hP : IsRestrictionUnitRangeDependent P)
    (hsep : Pairwise fun i j => AreUnitSeparated (V i) (V j))
    (X : ∀ i, MeasurableLocalObservable d (V i) γ)
    (S T : Finset ι) (hST : Disjoint S T) :
    ProbabilityTheory.IndepFun
      (finsetSum (d := d) (s := S) X) (finsetSum (d := d) (s := T) X) P := by
  simpa [finsetSum] using!
    (indepFun_finset_of_isRestrictionUnitRangeDependent (d := d) hP hsep X S T hST).comp
      (measurable_subtypeFinsetSum S) (measurable_subtypeFinsetSum T)

theorem indepFun_finsetAverage_of_isRestrictionUnitRangeDependent
    {ι : Type*} [DecidableEq ι] {γ : Type*} [MeasurableSpace γ]
    [AddCommMonoid γ] [MeasurableAdd₂ γ] [SMul ℝ γ] [MeasurableConstSMul ℝ γ]
    {P : MeasureTheory.Measure (CoeffField d)} [MeasureTheory.IsProbabilityMeasure P]
    {V : ι → Set (Vec d)} (hP : IsRestrictionUnitRangeDependent P)
    (hsep : Pairwise fun i j => AreUnitSeparated (V i) (V j))
    (X : ∀ i, MeasurableLocalObservable d (V i) γ)
    (S T : Finset ι) (hST : Disjoint S T) :
    ProbabilityTheory.IndepFun
      (finsetAverage (d := d) (s := S) X) (finsetAverage (d := d) (s := T) X) P := by
  simpa [finsetAverage] using!
    (indepFun_finsetSum_of_isRestrictionUnitRangeDependent (d := d) hP hsep X S T hST).comp
      (measurable_const_smul ((S.card : ℝ)⁻¹)) (measurable_const_smul ((T.card : ℝ)⁻¹))

theorem iIndepFun_descendantsAtScaleColorClass_of_isRestrictionUnitRangeDependent
    {Q : TriadicCube d} {k : ℤ} (hk : 0 ≤ k) {c : CubeColor d}
    {P : MeasureTheory.Measure (CoeffField d)} [MeasureTheory.IsProbabilityMeasure P]
    {γ :
      {R : TriadicCube d // R ∈ descendantsAtScaleColorClass Q k c} → Type*}
    [∀ R, MeasurableSpace (γ R)]
    (hP : IsRestrictionUnitRangeDependent P)
    (X :
      ∀ R : {R : TriadicCube d // R ∈ descendantsAtScaleColorClass Q k c},
        MeasurableLocalObservable d (cubeSet R.1) (γ R)) :
    ProbabilityTheory.iIndepFun (fun R => X R) P := by
  let I : Type := {R : TriadicCube d // R ∈ descendantsAtScaleColorClass Q k c}
  let V : I → Set (Vec d) := fun R => cubeSet R.1
  have hsep : Pairwise fun R S : I => AreUnitSeparated (V R) (V S) := by
    simpa [I, V] using
      pairwise_areUnitSeparated_cubeSet_subtype_descendantsAtScaleColorClass (Q := Q) hk c
  simpa [I, V] using
    (iIndepFun_of_isRestrictionUnitRangeDependent (d := d) (V := V) hP hsep X)

theorem indepFun_finset_descendantsAtScaleColorClass_of_isRestrictionUnitRangeDependent
    {Q : TriadicCube d} {k : ℤ} (hk : 0 ≤ k) {c : CubeColor d}
    {γ : Type*} [MeasurableSpace γ]
    {P : MeasureTheory.Measure (CoeffField d)} [MeasureTheory.IsProbabilityMeasure P]
    (hP : IsRestrictionUnitRangeDependent P)
    (X :
      ∀ R : {R : TriadicCube d // R ∈ descendantsAtScaleColorClass Q k c},
        MeasurableLocalObservable d (cubeSet R.1) γ)
    (S T : Finset {R : TriadicCube d // R ∈ descendantsAtScaleColorClass Q k c})
    (hST : Disjoint S T) :
    ProbabilityTheory.IndepFun
      (fun a (R : S) => X R a) (fun a (R : T) => X R a) P := by
  let I : Type := {R : TriadicCube d // R ∈ descendantsAtScaleColorClass Q k c}
  let V : I → Set (Vec d) := fun R => cubeSet R.1
  have hsep : Pairwise fun R S : I => AreUnitSeparated (V R) (V S) := by
    simpa [I, V] using
      pairwise_areUnitSeparated_cubeSet_subtype_descendantsAtScaleColorClass (Q := Q) hk c
  simpa [I, V] using
    (indepFun_finset_of_isRestrictionUnitRangeDependent
      (d := d) (V := V) hP hsep X S T hST)

theorem indepFun_finsetSum_descendantsAtScaleColorClass_of_isRestrictionUnitRangeDependent
    {Q : TriadicCube d} {k : ℤ} (hk : 0 ≤ k) {c : CubeColor d}
    {γ : Type*} [MeasurableSpace γ] [AddCommMonoid γ] [MeasurableAdd₂ γ]
    {P : MeasureTheory.Measure (CoeffField d)} [MeasureTheory.IsProbabilityMeasure P]
    (hP : IsRestrictionUnitRangeDependent P)
    (X :
      ∀ R : {R : TriadicCube d // R ∈ descendantsAtScaleColorClass Q k c},
        MeasurableLocalObservable d (cubeSet R.1) γ)
    (S T : Finset {R : TriadicCube d // R ∈ descendantsAtScaleColorClass Q k c})
    (hST : Disjoint S T) :
    ProbabilityTheory.IndepFun
      (finsetSum (d := d) (s := S) X) (finsetSum (d := d) (s := T) X) P := by
  let I : Type := {R : TriadicCube d // R ∈ descendantsAtScaleColorClass Q k c}
  let V : I → Set (Vec d) := fun R => cubeSet R.1
  have hsep : Pairwise fun R S : I => AreUnitSeparated (V R) (V S) := by
    simpa [I, V] using
      pairwise_areUnitSeparated_cubeSet_subtype_descendantsAtScaleColorClass (Q := Q) hk c
  simpa [I, V] using
    (indepFun_finsetSum_of_isRestrictionUnitRangeDependent
      (d := d) (V := V) hP hsep X S T hST)

theorem indepFun_finsetAverage_descendantsAtScaleColorClass_of_isRestrictionUnitRangeDependent
    {Q : TriadicCube d} {k : ℤ} (hk : 0 ≤ k) {c : CubeColor d}
    {γ : Type*} [MeasurableSpace γ] [AddCommMonoid γ] [MeasurableAdd₂ γ]
    [SMul ℝ γ] [MeasurableConstSMul ℝ γ]
    {P : MeasureTheory.Measure (CoeffField d)} [MeasureTheory.IsProbabilityMeasure P]
    (hP : IsRestrictionUnitRangeDependent P)
    (X :
      ∀ R : {R : TriadicCube d // R ∈ descendantsAtScaleColorClass Q k c},
        MeasurableLocalObservable d (cubeSet R.1) γ)
    (S T : Finset {R : TriadicCube d // R ∈ descendantsAtScaleColorClass Q k c})
    (hST : Disjoint S T) :
    ProbabilityTheory.IndepFun
      (finsetAverage (d := d) (s := S) X) (finsetAverage (d := d) (s := T) X) P := by
  let I : Type := {R : TriadicCube d // R ∈ descendantsAtScaleColorClass Q k c}
  let V : I → Set (Vec d) := fun R => cubeSet R.1
  have hsep : Pairwise fun R S : I => AreUnitSeparated (V R) (V S) := by
    simpa [I, V] using
      pairwise_areUnitSeparated_cubeSet_subtype_descendantsAtScaleColorClass (Q := Q) hk c
  simpa [I, V] using
    (indepFun_finsetAverage_of_isRestrictionUnitRangeDependent
      (d := d) (V := V) hP hsep X S T hST)

theorem iIndepFun_descendantsAtScaleScaleColorClass_of_isRestrictionUnitRangeDependent
    {Q : TriadicCube d} {k : ℤ} {c : ScaleColor d k}
    {P : MeasureTheory.Measure (CoeffField d)} [MeasureTheory.IsProbabilityMeasure P]
    {γ :
      {R : TriadicCube d // R ∈ descendantsAtScaleScaleColorClass Q k c} → Type*}
    [∀ R, MeasurableSpace (γ R)]
    (hP : IsRestrictionUnitRangeDependent P)
    (X :
      ∀ R : {R : TriadicCube d // R ∈ descendantsAtScaleScaleColorClass Q k c},
        MeasurableLocalObservable d (cubeSet R.1) (γ R)) :
    ProbabilityTheory.iIndepFun (fun R => X R) P := by
  let I : Type := {R : TriadicCube d // R ∈ descendantsAtScaleScaleColorClass Q k c}
  let V : I → Set (Vec d) := fun R => cubeSet R.1
  have hsep : Pairwise fun R S : I => AreUnitSeparated (V R) (V S) := by
    simpa [I, V] using
      pairwise_areUnitSeparated_cubeSet_subtype_descendantsAtScaleScaleColorClass (Q := Q) c
  simpa [I, V] using
    (iIndepFun_of_isRestrictionUnitRangeDependent (d := d) (V := V) hP hsep X)

theorem indepFun_finset_descendantsAtScaleScaleColorClass_of_isRestrictionUnitRangeDependent
    {Q : TriadicCube d} {k : ℤ} {c : ScaleColor d k}
    {γ : Type*} [MeasurableSpace γ]
    {P : MeasureTheory.Measure (CoeffField d)} [MeasureTheory.IsProbabilityMeasure P]
    (hP : IsRestrictionUnitRangeDependent P)
    (X :
      ∀ R : {R : TriadicCube d // R ∈ descendantsAtScaleScaleColorClass Q k c},
        MeasurableLocalObservable d (cubeSet R.1) γ)
    (S T : Finset {R : TriadicCube d // R ∈ descendantsAtScaleScaleColorClass Q k c})
    (hST : Disjoint S T) :
    ProbabilityTheory.IndepFun
      (fun a (R : S) => X R a) (fun a (R : T) => X R a) P := by
  let I : Type := {R : TriadicCube d // R ∈ descendantsAtScaleScaleColorClass Q k c}
  let V : I → Set (Vec d) := fun R => cubeSet R.1
  have hsep : Pairwise fun R S : I => AreUnitSeparated (V R) (V S) := by
    simpa [I, V] using
      pairwise_areUnitSeparated_cubeSet_subtype_descendantsAtScaleScaleColorClass (Q := Q) c
  simpa [I, V] using
    (indepFun_finset_of_isRestrictionUnitRangeDependent
      (d := d) (V := V) hP hsep X S T hST)

theorem indepFun_finsetSum_descendantsAtScaleScaleColorClass_of_isRestrictionUnitRangeDependent
    {Q : TriadicCube d} {k : ℤ} {c : ScaleColor d k}
    {γ : Type*} [MeasurableSpace γ] [AddCommMonoid γ] [MeasurableAdd₂ γ]
    {P : MeasureTheory.Measure (CoeffField d)} [MeasureTheory.IsProbabilityMeasure P]
    (hP : IsRestrictionUnitRangeDependent P)
    (X :
      ∀ R : {R : TriadicCube d // R ∈ descendantsAtScaleScaleColorClass Q k c},
        MeasurableLocalObservable d (cubeSet R.1) γ)
    (S T : Finset {R : TriadicCube d // R ∈ descendantsAtScaleScaleColorClass Q k c})
    (hST : Disjoint S T) :
    ProbabilityTheory.IndepFun
      (finsetSum (d := d) (s := S) X) (finsetSum (d := d) (s := T) X) P := by
  let I : Type := {R : TriadicCube d // R ∈ descendantsAtScaleScaleColorClass Q k c}
  let V : I → Set (Vec d) := fun R => cubeSet R.1
  have hsep : Pairwise fun R S : I => AreUnitSeparated (V R) (V S) := by
    simpa [I, V] using
      pairwise_areUnitSeparated_cubeSet_subtype_descendantsAtScaleScaleColorClass (Q := Q) c
  simpa [I, V] using
    (indepFun_finsetSum_of_isRestrictionUnitRangeDependent
      (d := d) (V := V) hP hsep X S T hST)

theorem indepFun_finsetAverage_descendantsAtScaleScaleColorClass_of_isRestrictionUnitRangeDependent
    {Q : TriadicCube d} {k : ℤ} {c : ScaleColor d k}
    {γ : Type*} [MeasurableSpace γ] [AddCommMonoid γ] [MeasurableAdd₂ γ]
    [SMul ℝ γ] [MeasurableConstSMul ℝ γ]
    {P : MeasureTheory.Measure (CoeffField d)} [MeasureTheory.IsProbabilityMeasure P]
    (hP : IsRestrictionUnitRangeDependent P)
    (X :
      ∀ R : {R : TriadicCube d // R ∈ descendantsAtScaleScaleColorClass Q k c},
        MeasurableLocalObservable d (cubeSet R.1) γ)
    (S T : Finset {R : TriadicCube d // R ∈ descendantsAtScaleScaleColorClass Q k c})
    (hST : Disjoint S T) :
    ProbabilityTheory.IndepFun
      (finsetAverage (d := d) (s := S) X) (finsetAverage (d := d) (s := T) X) P := by
  let I : Type := {R : TriadicCube d // R ∈ descendantsAtScaleScaleColorClass Q k c}
  let V : I → Set (Vec d) := fun R => cubeSet R.1
  have hsep : Pairwise fun R S : I => AreUnitSeparated (V R) (V S) := by
    simpa [I, V] using
      pairwise_areUnitSeparated_cubeSet_subtype_descendantsAtScaleScaleColorClass (Q := Q) c
  simpa [I, V] using
    (indepFun_finsetAverage_of_isRestrictionUnitRangeDependent
      (d := d) (V := V) hP hsep X S T hST)

end MeasurableLocalObservable

/-- Explicit restriction-local spelling for the unchanged raw coefficient-field
observable bundle. -/
abbrev MeasurableRestrictionLocalObservable (d : ℕ) (U : Set (Vec d)) (β : Type*)
    [MeasurableSpace β] :=
  MeasurableLocalObservable d U β

namespace MeasurableRestrictionLocalObservable

export MeasurableLocalObservable (measurable measurable_restrictionSigma
  measurable_restrictionSigma_mono mono mono_apply const comp prod pi neg add sub const_smul
  finsetPi measurable_subtypeFinsetSum finsetSum finsetAverage comp_restrictCoeffField_eq
  map_eq_map_restrictCoeffField map_eq_of_map_restrictCoeffField_eq
  measurable_comp_randomCoeffField measurable_comp_randomCoeffField_restrictionSigma
  indepFun_of_indep_restrictionSigma integral_map_restrictCoeffField_eq
  integral_eq_of_map_restrictCoeffField_eq iIndepFun_of_isRestrictionUnitRangeDependent
  indepFun_finset_of_isRestrictionUnitRangeDependent
  indepFun_finsetSum_of_isRestrictionUnitRangeDependent
  indepFun_finsetAverage_of_isRestrictionUnitRangeDependent
  iIndepFun_descendantsAtScaleColorClass_of_isRestrictionUnitRangeDependent
  indepFun_finset_descendantsAtScaleColorClass_of_isRestrictionUnitRangeDependent
  indepFun_finsetSum_descendantsAtScaleColorClass_of_isRestrictionUnitRangeDependent
  indepFun_finsetAverage_descendantsAtScaleColorClass_of_isRestrictionUnitRangeDependent
  iIndepFun_descendantsAtScaleScaleColorClass_of_isRestrictionUnitRangeDependent
  indepFun_finset_descendantsAtScaleScaleColorClass_of_isRestrictionUnitRangeDependent
  indepFun_finsetSum_descendantsAtScaleScaleColorClass_of_isRestrictionUnitRangeDependent
  indepFun_finsetAverage_descendantsAtScaleScaleColorClass_of_isRestrictionUnitRangeDependent)

variable {β : Type*} [MeasurableSpace β] {d : ℕ} {U : Set (Vec d)}

/-- The explicit restriction-local spelling of the bundled locality field. -/
theorem isRestrictionLocal (X : MeasurableRestrictionLocalObservable d U β) :
    IsRestrictionLocalObservable U X :=
  MeasurableLocalObservable.isRestrictionLocal X

end MeasurableRestrictionLocalObservable

namespace RandomCoeffField

variable {Ω : Type*} [MeasurableSpace Ω] {d : ℕ} (A : RandomCoeffField Ω d)

@[simp] theorem restrictSet_apply (U : Set (Vec d)) (ω : Ω) :
    A.restrictSet U ω = restrictCoeffField U (A ω) :=
  rfl

theorem law_eq_law_restrictSet_of_isLocalObservable
    {β : Type*} [MeasurableSpace β] (μ : MeasureTheory.Measure Ω)
    {U : Set (Vec d)} {X : CoeffField d → β}
    (hX_meas : Measurable X) (hX_local : IsRestrictionLocalObservable U X) :
    MeasureTheory.Measure.map X ((A.restrictSet U).law μ) =
      MeasureTheory.Measure.map X (A.law μ) := by
  rw [A.law_restrictSet μ U]
  exact map_eq_map_restrictCoeffField_of_isRestrictionLocalObservable
    (P := A.law μ) hX_meas hX_local

theorem integral_comp_restrictSet_eq_of_isLocalObservable
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
    (μ : MeasureTheory.Measure Ω) {U : Set (Vec d)} {X : CoeffField d → E}
    (hX_local : IsRestrictionLocalObservable U X) :
    ∫ ω, X ((A.restrictSet U) ω) ∂μ = ∫ ω, X (A ω) ∂μ := by
  apply MeasureTheory.integral_congr_ae
  exact Filter.Eventually.of_forall <| fun ω => by
    have h := congrFun (comp_restrictCoeffField_eq_of_isRestrictionLocalObservable hX_local) (A ω)
    simpa [A.restrictSet_apply] using h

theorem integral_law_restrictSet_eq_of_isLocalObservable
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
    (μ : MeasureTheory.Measure Ω) {U : Set (Vec d)} {X : CoeffField d → E}
    (hX_meas : Measurable X) (hX_local : IsRestrictionLocalObservable U X) :
    ∫ a, X a ∂((A.restrictSet U).law μ) = ∫ a, X a ∂(A.law μ) := by
  rw [A.law_restrictSet μ U]
  exact integral_map_restrictCoeffField_eq_of_isRestrictionLocalObservable
    (P := A.law μ) hX_meas hX_local

theorem law_eq_law_restrictSet
    {β : Type*} [MeasurableSpace β] (μ : MeasureTheory.Measure Ω)
    {U : Set (Vec d)} (X : MeasurableLocalObservable d U β) :
    MeasureTheory.Measure.map X ((A.restrictSet U).law μ) =
      MeasureTheory.Measure.map X (A.law μ) := by
  rw [A.law_restrictSet μ U]
  exact X.map_eq_map_restrictCoeffField (P := A.law μ)

theorem integral_comp_restrictSet_eq
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
    (μ : MeasureTheory.Measure Ω) {U : Set (Vec d)}
    (X : MeasurableLocalObservable d U E) :
    ∫ ω, X ((A.restrictSet U) ω) ∂μ = ∫ ω, X (A ω) ∂μ := by
  apply MeasureTheory.integral_congr_ae
  exact Filter.Eventually.of_forall <| fun ω => by
    have h := congrFun X.comp_restrictCoeffField_eq (A ω)
    simpa [A.restrictSet_apply] using h

theorem integral_law_restrictSet_eq
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
    (μ : MeasureTheory.Measure Ω) {U : Set (Vec d)}
    (X : MeasurableLocalObservable d U E) :
    ∫ a, X a ∂((A.restrictSet U).law μ) = ∫ a, X a ∂(A.law μ) := by
  rw [A.law_restrictSet μ U]
  exact X.integral_map_restrictCoeffField_eq (P := A.law μ)

theorem indepFun_comp_of_indep_restrictionSigma
    {β γ : Type*} [MeasurableSpace β] [MeasurableSpace γ]
    {μ : MeasureTheory.Measure Ω} {U V : Set (Vec d)}
    (hμ : ProbabilityTheory.Indep (A.restrictionSigma U) (A.restrictionSigma V) μ)
    (X : MeasurableLocalObservable d U β) (Y : MeasurableLocalObservable d V γ) :
    ProbabilityTheory.IndepFun (fun ω => X (A ω)) (fun ω => Y (A ω)) μ := by
  exact ProbabilityTheory.indep_of_indep_of_le_right
    (m₃ := MeasurableSpace.comap (fun ω => Y (A ω)) inferInstance)
    (ProbabilityTheory.indep_of_indep_of_le_left
      (m₃ := MeasurableSpace.comap (fun ω => X (A ω)) inferInstance) hμ
    (Measurable.comap_le (X.measurable_comp_randomCoeffField_restrictionSigma A)))
    (Measurable.comap_le (Y.measurable_comp_randomCoeffField_restrictionSigma A))

theorem iIndepFun_comp_of_iIndep_restrictionSigma
    {ι : Type*} [DecidableEq ι] {β : ι → Type*} [∀ i, MeasurableSpace (β i)]
    {μ : MeasureTheory.Measure Ω} {U : ι → Set (Vec d)}
    (hμ : ProbabilityTheory.iIndep (fun i => A.restrictionSigma (U i)) μ)
    (X : ∀ i, MeasurableLocalObservable d (U i) (β i)) :
    ProbabilityTheory.iIndepFun (fun i => fun ω => X i (A ω)) μ := by
  rw [ProbabilityTheory.iIndepFun_iff_iIndep]
  rw [ProbabilityTheory.iIndep_iff]
  intro s f hf
  exact (ProbabilityTheory.iIndep_iff (fun i => A.restrictionSigma (U i)) μ).1 hμ s
    (fun i hi =>
      (Measurable.comap_le ((X i).measurable_comp_randomCoeffField_restrictionSigma A))
        (f i) (hf i hi))

theorem indepFun_comp_finset_of_iIndep_restrictionSigma
    {ι : Type*} [DecidableEq ι] {β : ι → Type*} [∀ i, MeasurableSpace (β i)]
    {μ : MeasureTheory.Measure Ω} {U : ι → Set (Vec d)}
    (hμ : ProbabilityTheory.iIndep (fun i => A.restrictionSigma (U i)) μ)
    (X : ∀ i, MeasurableLocalObservable d (U i) (β i))
    (S T : Finset ι) (hST : Disjoint S T) :
    ProbabilityTheory.IndepFun
      (fun ω (i : S) => X i (A ω)) (fun ω (i : T) => X i (A ω)) μ := by
  exact (iIndepFun_comp_of_iIndep_restrictionSigma (A := A) hμ X).indepFun_finset S T hST
    (fun i => (X i).measurable_comp_randomCoeffField A)

theorem indepFun_comp_finsetSum_of_iIndep_restrictionSigma
    {ι : Type*} [DecidableEq ι] {β : Type*} [MeasurableSpace β]
    [AddCommMonoid β] [MeasurableAdd₂ β]
    {μ : MeasureTheory.Measure Ω} {U : ι → Set (Vec d)}
    (hμ : ProbabilityTheory.iIndep (fun i => A.restrictionSigma (U i)) μ)
    (X : ∀ i, MeasurableLocalObservable d (U i) β)
    (S T : Finset ι) (hST : Disjoint S T) :
    ProbabilityTheory.IndepFun
      (fun ω => MeasurableLocalObservable.finsetSum (d := d) (s := S) (V := U) X (A ω))
      (fun ω => MeasurableLocalObservable.finsetSum (d := d) (s := T) (V := U) X (A ω)) μ := by
  simpa [MeasurableLocalObservable.finsetSum] using!
    (indepFun_comp_finset_of_iIndep_restrictionSigma (A := A) hμ X S T hST).comp
      (MeasurableLocalObservable.measurable_subtypeFinsetSum S)
      (MeasurableLocalObservable.measurable_subtypeFinsetSum T)

theorem indepFun_comp_finsetAverage_of_iIndep_restrictionSigma
    {ι : Type*} [DecidableEq ι] {β : Type*} [MeasurableSpace β]
    [AddCommMonoid β] [MeasurableAdd₂ β] [SMul ℝ β] [MeasurableConstSMul ℝ β]
    {μ : MeasureTheory.Measure Ω} {U : ι → Set (Vec d)}
    (hμ : ProbabilityTheory.iIndep (fun i => A.restrictionSigma (U i)) μ)
    (X : ∀ i, MeasurableLocalObservable d (U i) β)
    (S T : Finset ι) (hST : Disjoint S T) :
    ProbabilityTheory.IndepFun
      (fun ω => MeasurableLocalObservable.finsetAverage (d := d) (s := S) (V := U) X (A ω))
      (fun ω => MeasurableLocalObservable.finsetAverage (d := d) (s := T) (V := U) X (A ω)) μ := by
  simpa [MeasurableLocalObservable.finsetAverage] using!
    (indepFun_comp_finsetSum_of_iIndep_restrictionSigma (A := A) hμ X S T hST).comp
      (measurable_const_smul ((S.card : ℝ)⁻¹)) (measurable_const_smul ((T.card : ℝ)⁻¹))

end RandomCoeffField

end Homogenization
