/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/
module


public import LeanPool.CoarseGraining.Homogenization.Book.Ch04.SourceLaw
public import Mathlib.MeasureTheory.Constructions.Pi

/-!
# Exact coarse-source local observables

Locality in this file is measurability for the coarse source's integral-only
sigma algebra.  It is intentionally separate from restriction locality.
-/

@[expose] public section

namespace Homogenization.Book.Ch04

open MeasureTheory

private instance instMeasurableSpaceMat (d : ℕ) : MeasurableSpace (Mat d) :=
  inferInstanceAs (MeasurableSpace (Fin d → Fin d → ℝ))

/-- A random variable local for the exact coarse source sigma algebra. -/
def IsSourceLocalRandomVariable {β : Type*} [MeasurableSpace β] {d : ℕ}
    (U : Set (Vec d)) (hU : MeasurableSet U) (X : Source.Coarse.Carrier d → β) : Prop :=
  Source.Coarse.IsLocalObservable U hU X

namespace IsSourceLocalRandomVariable

/-- Enlarge the observation set of a source-local random variable. -/
theorem mono {β : Type*} [MeasurableSpace β] {d : ℕ}
    {U V : Set (Vec d)} {X : Source.Coarse.Carrier d → β}
    (hU : MeasurableSet U) (hV : MeasurableSet V) (hUV : U ⊆ V)
    (hX : IsSourceLocalRandomVariable U hU X) :
    IsSourceLocalRandomVariable V hV X :=
  Measurable.mono hX (Source.Coarse.localSigma_mono hU hV hUV) le_rfl

/-- Constant source-local random variables. -/
theorem const {β : Type*} [MeasurableSpace β] {d : ℕ}
    (U : Set (Vec d)) (hU : MeasurableSet U) (b : β) :
    IsSourceLocalRandomVariable U hU (fun _a : Source.Coarse.Carrier d => b) :=
  measurable_const

/-- Measurable postcomposition preserves source locality. -/
theorem comp_measurable {β γ : Type*} [MeasurableSpace β] [MeasurableSpace γ]
    {d : ℕ} {U : Set (Vec d)} {hU : MeasurableSet U}
    {X : Source.Coarse.Carrier d → β}
    (hX : IsSourceLocalRandomVariable U hU X) {g : β → γ} (hg : Measurable g) :
    IsSourceLocalRandomVariable U hU (fun a => g (X a)) :=
  hg.comp hX

/-- Precomposing a source-local random variable with coefficient translation
translates its observation region by the same integer vector. -/
theorem comp_translate {β : Type*} [MeasurableSpace β] {d : ℕ}
    {U : Set (Vec d)} {hU : MeasurableSet U} {X : Source.Coarse.Carrier d → β}
    (hX : IsSourceLocalRandomVariable U hU X) (z : Fin d → ℤ) :
    IsSourceLocalRandomVariable (translateSet (intVecToRealVec z) U) (by
      rw [← preimage_subRight_eq_translateSet]
      exact hU.preimage (Homeomorph.subRight _).continuous.measurable)
      (X ∘ Source.Coarse.Carrier.translate z) :=
  Source.Coarse.IsLocalObservable.comp_translate hU hX z

/-- Source locality of a vector-valued random variable follows componentwise. -/
theorem vec_of_components {d m : ℕ} {U : Set (Vec d)} {hU : MeasurableSet U}
    {X : Source.Coarse.Carrier d → Vec m}
    (hX : ∀ i : Fin m, IsSourceLocalRandomVariable U hU (fun a => X a i)) :
    IsSourceLocalRandomVariable U hU X := by
  change @Measurable (Source.Coarse.Carrier d) (Vec m) (Source.Coarse.localSigma U hU) _ X
  rw [@measurable_pi_iff (Source.Coarse.Carrier d) (Fin m) (fun _ => ℝ)
    (Source.Coarse.localSigma U hU) (fun _ => inferInstance) X]
  intro i
  exact hX i

/-- Components of a source-local vector-valued random variable are source-local. -/
theorem vec_component {d m : ℕ} {U : Set (Vec d)} {hU : MeasurableSet U}
    {X : Source.Coarse.Carrier d → Vec m}
    (hX : IsSourceLocalRandomVariable U hU X) (i : Fin m) :
    IsSourceLocalRandomVariable U hU (fun a => X a i) := by
  change @Measurable (Source.Coarse.Carrier d) ℝ (Source.Coarse.localSigma U hU) _
    (fun a => X a i)
  exact ((@measurable_pi_iff (Source.Coarse.Carrier d) (Fin m) (fun _ => ℝ)
    (Source.Coarse.localSigma U hU) (fun _ => inferInstance) X).mp hX) i

/-- Source locality of a matrix-valued random variable follows entrywise. -/
theorem mat_of_entries {d m : ℕ} {U : Set (Vec d)} {hU : MeasurableSet U}
    {X : Source.Coarse.Carrier d → Mat m}
    (hX : ∀ i j : Fin m, IsSourceLocalRandomVariable U hU (fun a => X a i j)) :
    IsSourceLocalRandomVariable U hU X := by
  change @Measurable (Source.Coarse.Carrier d) (Mat m) (Source.Coarse.localSigma U hU) _ X
  refine (@measurable_pi_iff (Source.Coarse.Carrier d) (Fin m) (fun _ => Fin m → ℝ)
    (Source.Coarse.localSigma U hU) (fun _ => inferInstance) X).2 fun i => ?_
  refine (@measurable_pi_iff (Source.Coarse.Carrier d) (Fin m) (fun _ => ℝ)
    (Source.Coarse.localSigma U hU) (fun _ => inferInstance) (fun a => X a i)).2 fun j => ?_
  exact hX i j

/-- Entries of a source-local matrix-valued random variable are source-local. -/
theorem mat_entry {d m : ℕ} {U : Set (Vec d)} {hU : MeasurableSet U}
    {X : Source.Coarse.Carrier d → Mat m}
    (hX : IsSourceLocalRandomVariable U hU X) (i j : Fin m) :
    IsSourceLocalRandomVariable U hU (fun a => X a i j) := by
  change @Measurable (Source.Coarse.Carrier d) ℝ (Source.Coarse.localSigma U hU) _
    (fun a => X a i j)
  have hi :
      @Measurable (Source.Coarse.Carrier d) (Fin m → ℝ) (Source.Coarse.localSigma U hU) _
        (fun a => X a i) :=
    ((@measurable_pi_iff (Source.Coarse.Carrier d) (Fin m) (fun _ => Fin m → ℝ)
      (Source.Coarse.localSigma U hU) (fun _ => inferInstance) X).mp hX) i
  exact ((@measurable_pi_iff (Source.Coarse.Carrier d) (Fin m) (fun _ => ℝ)
    (Source.Coarse.localSigma U hU) (fun _ => inferInstance) (fun a => X a i)).mp hi) j

/-- Sum of source-local real random variables. -/
theorem add {d : ℕ} {U : Set (Vec d)} {hU : MeasurableSet U}
    {X Y : Source.Coarse.Carrier d → ℝ}
    (hX : IsSourceLocalRandomVariable U hU X) (hY : IsSourceLocalRandomVariable U hU Y) :
    IsSourceLocalRandomVariable U hU (fun a => X a + Y a) :=
  Measurable.add hX hY

/-- Negation of a source-local real random variable. -/
theorem neg {d : ℕ} {U : Set (Vec d)} {hU : MeasurableSet U}
    {X : Source.Coarse.Carrier d → ℝ}
    (hX : IsSourceLocalRandomVariable U hU X) :
    IsSourceLocalRandomVariable U hU (fun a => -X a) :=
  Measurable.neg hX

/-- Difference of source-local real random variables. -/
theorem sub {d : ℕ} {U : Set (Vec d)} {hU : MeasurableSet U}
    {X Y : Source.Coarse.Carrier d → ℝ}
    (hX : IsSourceLocalRandomVariable U hU X) (hY : IsSourceLocalRandomVariable U hU Y) :
    IsSourceLocalRandomVariable U hU (fun a => X a - Y a) :=
  Measurable.sub hX hY

/-- Product of source-local real random variables. -/
theorem mul {d : ℕ} {U : Set (Vec d)} {hU : MeasurableSet U}
    {X Y : Source.Coarse.Carrier d → ℝ}
    (hX : IsSourceLocalRandomVariable U hU X) (hY : IsSourceLocalRandomVariable U hU Y) :
    IsSourceLocalRandomVariable U hU (fun a => X a * Y a) :=
  Measurable.mul hX hY

/-- Inverse of a source-local real random variable. -/
theorem inv {d : ℕ} {U : Set (Vec d)} {hU : MeasurableSet U}
    {X : Source.Coarse.Carrier d → ℝ}
    (hX : IsSourceLocalRandomVariable U hU X) :
    IsSourceLocalRandomVariable U hU (fun a => (X a)⁻¹) :=
  Measurable.inv hX

/-- Absolute value of a source-local real random variable. -/
theorem abs {d : ℕ} {U : Set (Vec d)} {hU : MeasurableSet U}
    {X : Source.Coarse.Carrier d → ℝ}
    (hX : IsSourceLocalRandomVariable U hU X) :
    IsSourceLocalRandomVariable U hU (fun a => |X a|) :=
  continuous_abs.measurable.comp hX

/-- Finite sums of source-local real random variables are source-local. -/
theorem finset_sum {d : ℕ} {ι : Type*} [Fintype ι]
    {U : Set (Vec d)} {hU : MeasurableSet U} {X : ι → Source.Coarse.Carrier d → ℝ}
    (hX : ∀ i, IsSourceLocalRandomVariable U hU (X i)) :
    IsSourceLocalRandomVariable U hU (fun a => ∑ i, X i a) := by
  classical
  exact Finset.measurable_sum Finset.univ fun i _hi => hX i

end IsSourceLocalRandomVariable

/-- A bundled observable local for the exact coarse source sigma algebra. -/
structure SourceObservable (d : ℕ) (U : Set (Vec d)) (β : Type*)
    [MeasurableSpace β] where
  measurableSet : MeasurableSet U
  toFun : Source.Coarse.Carrier d → β
  isLocal : IsSourceLocalRandomVariable U measurableSet toFun

namespace SourceObservable

variable {d m : ℕ} {U V : Set (Vec d)}

instance {β : Type*} [MeasurableSpace β] :
    CoeFun (SourceObservable d U β) (fun _ => Source.Coarse.Carrier d → β) :=
  ⟨SourceObservable.toFun⟩

/-- Enlarge the observation set of a bundled source observable. -/
def mono {β : Type*} [MeasurableSpace β] (X : SourceObservable d U β)
    (hV : MeasurableSet V) (hUV : U ⊆ V) : SourceObservable d V β where
  measurableSet := hV
  toFun := X
  isLocal := X.isLocal.mono X.measurableSet hV hUV

/-- Constant bundled source observables. -/
def const {β : Type*} [MeasurableSpace β] (U : Set (Vec d)) (hU : MeasurableSet U)
    (b : β) : SourceObservable d U β where
  measurableSet := hU
  toFun := fun _a => b
  isLocal := IsSourceLocalRandomVariable.const U hU b

/-- Measurable postcomposition of a bundled source observable. -/
def comp {β γ : Type*} [MeasurableSpace β] [MeasurableSpace γ]
    (X : SourceObservable d U β) (g : β → γ) (hg : Measurable g) :
    SourceObservable d U γ where
  measurableSet := X.measurableSet
  toFun := fun a => g (X a)
  isLocal := X.isLocal.comp_measurable hg

/-- Translate a bundled source observable together with its observation
region. -/
def translate {β : Type*} [MeasurableSpace β] (X : SourceObservable d U β)
    (z : Fin d → ℤ) :
    SourceObservable d (translateSet (intVecToRealVec z) U) β where
  measurableSet := by
    rw [← preimage_subRight_eq_translateSet]
    exact X.measurableSet.preimage (Homeomorph.subRight _).continuous.measurable
  toFun := X ∘ Source.Coarse.Carrier.translate z
  isLocal := X.isLocal.comp_translate z

@[simp] theorem translate_apply {β : Type*} [MeasurableSpace β]
    (X : SourceObservable d U β) (z : Fin d → ℤ) (a : Source.Coarse.Carrier d) :
    X.translate z a = X (Source.Coarse.Carrier.translate z a) :=
  rfl

/-- Build a vector-valued bundled source observable from bundled components. -/
def vecOfComponents (hU : MeasurableSet U) (X : Fin m → SourceObservable d U ℝ) :
    SourceObservable d U (Vec m) where
  measurableSet := hU
  toFun := fun a i => X i a
  isLocal := IsSourceLocalRandomVariable.vec_of_components (hU := hU) fun i => (X i).isLocal

/-- Extract one component of a vector-valued bundled source observable. -/
def vecComponent (X : SourceObservable d U (Vec m)) (i : Fin m) :
    SourceObservable d U ℝ where
  measurableSet := X.measurableSet
  toFun := fun a => X a i
  isLocal := X.isLocal.vec_component i

/-- Build a matrix-valued bundled source observable from bundled entries. -/
def matOfEntries (hU : MeasurableSet U)
    (X : Fin m → Fin m → SourceObservable d U ℝ) : SourceObservable d U (Mat m) where
  measurableSet := hU
  toFun := fun a i j => X i j a
  isLocal := IsSourceLocalRandomVariable.mat_of_entries (hU := hU) fun i j => (X i j).isLocal

/-- Extract one entry of a matrix-valued bundled source observable. -/
def matEntry (X : SourceObservable d U (Mat m)) (i j : Fin m) : SourceObservable d U ℝ where
  measurableSet := X.measurableSet
  toFun := fun a => X a i j
  isLocal := X.isLocal.mat_entry i j

/-- Sum of bundled source observables. -/
protected def add (X Y : SourceObservable d U ℝ) : SourceObservable d U ℝ where
  measurableSet := X.measurableSet
  toFun := fun a => X a + Y a
  isLocal := X.isLocal.add Y.isLocal

/-- Negation of a bundled source observable. -/
protected def neg (X : SourceObservable d U ℝ) : SourceObservable d U ℝ where
  measurableSet := X.measurableSet
  toFun := fun a => -X a
  isLocal := X.isLocal.neg

/-- Difference of bundled source observables. -/
protected def sub (X Y : SourceObservable d U ℝ) : SourceObservable d U ℝ where
  measurableSet := X.measurableSet
  toFun := fun a => X a - Y a
  isLocal := X.isLocal.sub Y.isLocal

/-- Product of bundled source observables. -/
protected def mul (X Y : SourceObservable d U ℝ) : SourceObservable d U ℝ where
  measurableSet := X.measurableSet
  toFun := fun a => X a * Y a
  isLocal := X.isLocal.mul Y.isLocal

/-- Inverse of a bundled source observable. -/
protected noncomputable def inv (X : SourceObservable d U ℝ) : SourceObservable d U ℝ where
  measurableSet := X.measurableSet
  toFun := fun a => (X a)⁻¹
  isLocal := X.isLocal.inv

/-- Absolute value of a bundled source observable. -/
protected def abs (X : SourceObservable d U ℝ) : SourceObservable d U ℝ where
  measurableSet := X.measurableSet
  toFun := fun a => |X a|
  isLocal := X.isLocal.abs

/-- Finite sum of bundled source observables. -/
def finsetSum {ι : Type*} [Fintype ι] (hU : MeasurableSet U)
    (X : ι → SourceObservable d U ℝ) : SourceObservable d U ℝ where
  measurableSet := hU
  toFun := fun a => ∑ i, X i a
  isLocal := IsSourceLocalRandomVariable.finset_sum (hU := hU) fun i => (X i).isLocal

end SourceObservable

end Homogenization.Book.Ch04
