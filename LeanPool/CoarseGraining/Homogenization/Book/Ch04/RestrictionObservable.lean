/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/
module


public import LeanPool.CoarseGraining.Homogenization.Book.Ch04.Law

/-! # Restriction Observable -/

@[expose] public section

namespace Homogenization
namespace Book
namespace Ch04

open MeasureTheory

/-!
# Local observables (carrier re-type, Packet P3)

`IsRestrictionLocalRandomVariable U hU X` is the permanent Ch4 predicate for
restriction-local random observables.
Following the carrier redesign, observables are functions of the honest-fields
carrier `RegCoeffField d`, and locality is measurability for the carrier
restriction σ-algebra `RestrictionSigmaR U hU` (which needs the observation set to
be measurable — the D7-approved `MeasurableSet` side-condition making
`RestrictionSigmaR` well defined).  Everything downstream should enter
measurability through this predicate and the promotion lemmas in
`Ch04.Measurability`.

Reference: the paper (Armstrong–Kuusi–Loher, to appear).
-/

/-- A random observable depending only on the restriction-local carrier
σ-algebra on the measurable set `U`. -/
def IsRestrictionLocalRandomVariable {β : Type*} [MeasurableSpace β] {d : ℕ}
    (U : Set (Vec d)) (hU : MeasurableSet U) (X : RegCoeffField d → β) : Prop :=
  @Measurable (RegCoeffField d) β (RestrictionSigmaR U hU) _ X

namespace IsRestrictionLocalRandomVariable

/-- Monotonicity of the restriction-local carrier σ-algebra. -/
theorem restrictionSigma_mono {d : ℕ} {U V : Set (Vec d)}
    (hU : MeasurableSet U) (hV : MeasurableSet V) (hUV : U ⊆ V) :
    RestrictionSigmaR U hU ≤ RestrictionSigmaR V hV :=
  RestrictionSigmaR_mono hU hV hUV

/-- A local observable on a smaller observation set is local on any larger one. -/
theorem mono {β : Type*} [MeasurableSpace β] {d : ℕ}
    {U V : Set (Vec d)} {X : RegCoeffField d → β}
    (hU : MeasurableSet U) (hV : MeasurableSet V) (hUV : U ⊆ V)
    (hX : IsRestrictionLocalRandomVariable U hU X) :
    IsRestrictionLocalRandomVariable V hV X := by
  intro s hs
  exact (restrictionSigma_mono (d := d) hU hV hUV) (X ⁻¹' s) (hX hs)

/-- Constant local observables. -/
theorem const {β : Type*} [MeasurableSpace β] {d : ℕ}
    (U : Set (Vec d)) (hU : MeasurableSet U) (b : β) :
    IsRestrictionLocalRandomVariable U hU (fun _a : RegCoeffField d => b) :=
  measurable_const

/-- Compose a local observable with a measurable map. -/
theorem comp_measurable {β γ : Type*} [MeasurableSpace β] [MeasurableSpace γ]
    {d : ℕ} {U : Set (Vec d)} {hU : MeasurableSet U} {X : RegCoeffField d → β}
    (hX : IsRestrictionLocalRandomVariable U hU X) {g : β → γ} (hg : Measurable g) :
    IsRestrictionLocalRandomVariable U hU (fun a => g (X a)) :=
  hg.comp hX

/-- Locality of a vector-valued observable follows componentwise. -/
theorem vec_of_components {d m : ℕ} {U : Set (Vec d)} {hU : MeasurableSet U}
    {X : RegCoeffField d → Vec m}
    (hX : ∀ i : Fin m, IsRestrictionLocalRandomVariable U hU (fun a => X a i)) :
    IsRestrictionLocalRandomVariable U hU X := by
  change @Measurable (RegCoeffField d) (Vec m) (RestrictionSigmaR U hU) _ X
  rw [@measurable_pi_iff (RegCoeffField d) (Fin m) (fun _ => ℝ)
    (RestrictionSigmaR U hU) (fun _ => inferInstance) X]
  intro i
  exact hX i

/-- Components of a vector-valued local observable are local. -/
theorem vec_component {d m : ℕ} {U : Set (Vec d)} {hU : MeasurableSet U}
    {X : RegCoeffField d → Vec m}
    (hX : IsRestrictionLocalRandomVariable U hU X) (i : Fin m) :
    IsRestrictionLocalRandomVariable U hU (fun a => X a i) := by
  change @Measurable (RegCoeffField d) ℝ (RestrictionSigmaR U hU) _ (fun a => X a i)
  exact ((@measurable_pi_iff (RegCoeffField d) (Fin m) (fun _ => ℝ)
    (RestrictionSigmaR U hU) (fun _ => inferInstance) X).mp
    (show @Measurable (RegCoeffField d) (Vec m) (RestrictionSigmaR U hU) _ X from hX)) i

/-- Locality of a matrix-valued observable follows entrywise. -/
theorem mat_of_entries {d m : ℕ} {U : Set (Vec d)} {hU : MeasurableSet U}
    {X : RegCoeffField d → Mat m}
    (hX : ∀ i j : Fin m, IsRestrictionLocalRandomVariable U hU (fun a => X a i j)) :
    IsRestrictionLocalRandomVariable U hU X := by
  change @Measurable (RegCoeffField d) (Mat m) (RestrictionSigmaR U hU) _ X
  refine (@measurable_pi_iff (RegCoeffField d) (Fin m) (fun _ => Fin m → ℝ)
    (RestrictionSigmaR U hU) (fun _ => inferInstance) X).2 ?_
  intro i
  rw [@measurable_pi_iff (RegCoeffField d) (Fin m) (fun _ => ℝ)
    (RestrictionSigmaR U hU) (fun _ => inferInstance) (fun a => X a i)]
  intro j
  exact hX i j

/-- Entries of a matrix-valued local observable are local. -/
theorem mat_entry {d m : ℕ} {U : Set (Vec d)} {hU : MeasurableSet U}
    {X : RegCoeffField d → Mat m}
    (hX : IsRestrictionLocalRandomVariable U hU X) (i j : Fin m) :
    IsRestrictionLocalRandomVariable U hU (fun a => X a i j) := by
  change @Measurable (RegCoeffField d) ℝ (RestrictionSigmaR U hU) _ (fun a => X a i j)
  have hi :
      @Measurable (RegCoeffField d) (Fin m → ℝ) (RestrictionSigmaR U hU) _
        (fun a => X a i) :=
    ((@measurable_pi_iff (RegCoeffField d) (Fin m) (fun _ => Fin m → ℝ)
      (RestrictionSigmaR U hU) (fun _ => inferInstance) X).mp
        (show @Measurable (RegCoeffField d) (Mat m) (RestrictionSigmaR U hU) _ X from hX)) i
  exact ((@measurable_pi_iff (RegCoeffField d) (Fin m) (fun _ => ℝ)
    (RestrictionSigmaR U hU) (fun _ => inferInstance) (fun a => X a i)).mp hi) j

/-- Sum of real-valued local observables. -/
theorem add {d : ℕ} {U : Set (Vec d)} {hU : MeasurableSet U}
    {X Y : RegCoeffField d → ℝ}
    (hX : IsRestrictionLocalRandomVariable U hU X)
    (hY : IsRestrictionLocalRandomVariable U hU Y) :
    IsRestrictionLocalRandomVariable U hU (fun a => X a + Y a) :=
  Measurable.add hX hY

/-- Negation of a real-valued local observable. -/
theorem neg {d : ℕ} {U : Set (Vec d)} {hU : MeasurableSet U}
    {X : RegCoeffField d → ℝ}
    (hX : IsRestrictionLocalRandomVariable U hU X) :
    IsRestrictionLocalRandomVariable U hU (fun a => -X a) :=
  Measurable.neg hX

/-- Difference of real-valued local observables. -/
theorem sub {d : ℕ} {U : Set (Vec d)} {hU : MeasurableSet U}
    {X Y : RegCoeffField d → ℝ}
    (hX : IsRestrictionLocalRandomVariable U hU X)
    (hY : IsRestrictionLocalRandomVariable U hU Y) :
    IsRestrictionLocalRandomVariable U hU (fun a => X a - Y a) :=
  Measurable.sub hX hY

/-- Product of real-valued local observables. -/
theorem mul {d : ℕ} {U : Set (Vec d)} {hU : MeasurableSet U}
    {X Y : RegCoeffField d → ℝ}
    (hX : IsRestrictionLocalRandomVariable U hU X)
    (hY : IsRestrictionLocalRandomVariable U hU Y) :
    IsRestrictionLocalRandomVariable U hU (fun a => X a * Y a) :=
  Measurable.mul hX hY

/-- Inverse of a real-valued local observable. -/
theorem inv {d : ℕ} {U : Set (Vec d)} {hU : MeasurableSet U}
    {X : RegCoeffField d → ℝ}
    (hX : IsRestrictionLocalRandomVariable U hU X) :
    IsRestrictionLocalRandomVariable U hU (fun a => (X a)⁻¹) :=
  Measurable.inv hX

/-- Absolute value of a real-valued local observable. -/
theorem abs {d : ℕ} {U : Set (Vec d)} {hU : MeasurableSet U}
    {X : RegCoeffField d → ℝ}
    (hX : IsRestrictionLocalRandomVariable U hU X) :
    IsRestrictionLocalRandomVariable U hU (fun a => |X a|) :=
  continuous_abs.measurable.comp hX

/-- Finite sums of real-valued local observables. -/
theorem finset_sum {d : ℕ} {ι : Type*} [Fintype ι]
    {U : Set (Vec d)} {hU : MeasurableSet U} {X : ι → RegCoeffField d → ℝ}
    (hX : ∀ i, IsRestrictionLocalRandomVariable U hU (X i)) :
    IsRestrictionLocalRandomVariable U hU (fun a => ∑ i, X i a) := by
  classical
  exact Finset.measurable_sum Finset.univ fun i _hi => hX i

end IsRestrictionLocalRandomVariable

/-- Bundled restriction-local Chapter 4 observable.  This is the canonical
engineering object for whole-restriction locality.  The observation set's
measurability is kept as a field (rather than a type parameter) so the type
signature remains stable. -/
structure RestrictionObservable (d : ℕ) (U : Set (Vec d)) (β : Type*)
    [MeasurableSpace β] where
  measurableSet : MeasurableSet U
  toFun : RegCoeffField d → β
  isLocal : IsRestrictionLocalRandomVariable U measurableSet toFun

namespace RestrictionObservable

variable {d m : ℕ} {U V : Set (Vec d)}

instance {β : Type*} [MeasurableSpace β] :
    CoeFun (RestrictionObservable d U β) (fun _ => RegCoeffField d → β) :=
  ⟨RestrictionObservable.toFun⟩

/-- Explicit accessor for the permanent restriction-locality predicate. -/
theorem isRestrictionLocal {β : Type*} [MeasurableSpace β]
    (X : RestrictionObservable d U β) :
    IsRestrictionLocalRandomVariable U X.measurableSet X.toFun :=
  X.isLocal

/-- Enlarge the observation set of a bundled observable. -/
def mono {β : Type*} [MeasurableSpace β] (X : RestrictionObservable d U β)
    (hV : MeasurableSet V) (hUV : U ⊆ V) : RestrictionObservable d V β where
  measurableSet := hV
  toFun := X
  isLocal := X.isLocal.mono X.measurableSet hV hUV

/-- Constant bundled observables. -/
def const {β : Type*} [MeasurableSpace β] (U : Set (Vec d)) (hU : MeasurableSet U)
    (b : β) : RestrictionObservable d U β where
  measurableSet := hU
  toFun := fun _a => b
  isLocal := IsRestrictionLocalRandomVariable.const U hU b

/-- Measurable postcomposition of a bundled observable. -/
def comp {β γ : Type*} [MeasurableSpace β] [MeasurableSpace γ]
    (X : RestrictionObservable d U β) (g : β → γ) (hg : Measurable g) :
    RestrictionObservable d U γ where
  measurableSet := X.measurableSet
  toFun := fun a => g (X a)
  isLocal := X.isLocal.comp_measurable hg

/-- Build a vector-valued bundled observable from bundled components. -/
def vecOfComponents (hU : MeasurableSet U) (X : Fin m → RestrictionObservable d U ℝ) :
    RestrictionObservable d U (Vec m) where
  measurableSet := hU
  toFun := fun a i => X i a
  isLocal :=
    IsRestrictionLocalRandomVariable.vec_of_components (hU := hU)
      fun i => (X i).isLocal

/-- Extract one component of a vector-valued bundled observable. -/
def vecComponent (X : RestrictionObservable d U (Vec m)) (i : Fin m) :
    RestrictionObservable d U ℝ where
  measurableSet := X.measurableSet
  toFun := fun a => X a i
  isLocal := X.isLocal.vec_component i

/-- Build a matrix-valued bundled observable from bundled entries. -/
def matOfEntries (hU : MeasurableSet U)
    (X : Fin m → Fin m → RestrictionObservable d U ℝ) :
    RestrictionObservable d U (Mat m) where
  measurableSet := hU
  toFun := fun a i j => X i j a
  isLocal :=
    IsRestrictionLocalRandomVariable.mat_of_entries (hU := hU)
      fun i j => (X i j).isLocal

/-- Extract one entry of a matrix-valued bundled observable. -/
def matEntry (X : RestrictionObservable d U (Mat m)) (i j : Fin m) :
    RestrictionObservable d U ℝ where
  measurableSet := X.measurableSet
  toFun := fun a => X a i j
  isLocal := X.isLocal.mat_entry i j

/-- Sum of real-valued bundled observables. -/
protected def add (X Y : RestrictionObservable d U ℝ) : RestrictionObservable d U ℝ where
  measurableSet := X.measurableSet
  toFun := fun a => X a + Y a
  isLocal := X.isLocal.add Y.isLocal

/-- Negation of a real-valued bundled observable. -/
protected def neg (X : RestrictionObservable d U ℝ) : RestrictionObservable d U ℝ where
  measurableSet := X.measurableSet
  toFun := fun a => -X a
  isLocal := X.isLocal.neg

/-- Difference of real-valued bundled observables. -/
protected def sub (X Y : RestrictionObservable d U ℝ) : RestrictionObservable d U ℝ where
  measurableSet := X.measurableSet
  toFun := fun a => X a - Y a
  isLocal := X.isLocal.sub Y.isLocal

/-- Product of real-valued bundled observables. -/
protected def mul (X Y : RestrictionObservable d U ℝ) : RestrictionObservable d U ℝ where
  measurableSet := X.measurableSet
  toFun := fun a => X a * Y a
  isLocal := X.isLocal.mul Y.isLocal

/-- Inverse of a real-valued bundled observable. -/
protected noncomputable def inv (X : RestrictionObservable d U ℝ) : RestrictionObservable d U ℝ where
  measurableSet := X.measurableSet
  toFun := fun a => (X a)⁻¹
  isLocal := X.isLocal.inv

/-- Absolute value of a real-valued bundled observable. -/
protected def abs (X : RestrictionObservable d U ℝ) : RestrictionObservable d U ℝ where
  measurableSet := X.measurableSet
  toFun := fun a => |X a|
  isLocal := X.isLocal.abs

/-- Finite sum of real-valued bundled observables over a finite type. -/
def finsetSum {ι : Type*} [Fintype ι] (hU : MeasurableSet U)
    (X : ι → RestrictionObservable d U ℝ) : RestrictionObservable d U ℝ where
  measurableSet := hU
  toFun := fun a => ∑ i, X i a
  isLocal :=
    IsRestrictionLocalRandomVariable.finset_sum (hU := hU)
      fun i => (X i).isLocal

end RestrictionObservable

end Ch04
end Book
end Homogenization
