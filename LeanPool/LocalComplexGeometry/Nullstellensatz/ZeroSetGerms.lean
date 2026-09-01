/-
Copyright (c) 2026 BochaoKong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BochaoKong
-/

import LeanPool.LocalComplexGeometry.Germs.Basic
import Mathlib.RingTheory.Noetherian.Basic

/-!
# Local zero-set germs and vanishing ideals

Zero sets are predicate-valued germs.  This avoids evaluating an abstract
function germ at points away from the base point.  Only finite intersections
are used; arbitrary intersections would not have a uniform neighborhood.
-/

open Filter
open scoped Topology


namespace LocalComplexGeometry

noncomputable section

/-- Germs at the origin of predicates on `ℂⁿ`. -/
abbrev LocalSetGerm (n : ℕ) :=
  Filter.Germ (𝓝 (0 : ComplexEuclidean n)) Prop

/-- The local zero set of a holomorphic function germ. -/
def germZeroLocus {n : ℕ} (f : HolomorphicGerm n) : LocalSetGerm n :=
  Filter.Germ.map (fun z : ℂ ↦ z = 0) (f : FunctionGerm n)

@[simp]
theorem germZeroLocus_zero (n : ℕ) :
    germZeroLocus (0 : HolomorphicGerm n) = ⊤ := by
  change
    ((fun _ : ComplexEuclidean n ↦ (0 : ℂ) = 0) : LocalSetGerm n) =
      ((fun _ : ComplexEuclidean n ↦ True) : LocalSetGerm n)
  apply Filter.Germ.coe_eq.mpr
  exact Filter.Eventually.of_forall fun _ ↦ propext (by simp)

/-- A common zero of `f` and `g` is a zero of their sum. -/
theorem germZeroLocus_inf_le_add {n : ℕ} (f g : HolomorphicGerm n) :
    germZeroLocus f ⊓ germZeroLocus g ≤ germZeroLocus (f + g) := by
  change
    Filter.Germ.map (fun z : ℂ ↦ z = 0) (f : FunctionGerm n) ⊓
        Filter.Germ.map (fun z : ℂ ↦ z = 0) (g : FunctionGerm n) ≤
      Filter.Germ.map (fun z : ℂ ↦ z = 0)
        ((f : FunctionGerm n) + (g : FunctionGerm n))
  refine Filter.Germ.inductionOn₂ (f : FunctionGerm n) (g : FunctionGerm n) ?_
  intro F G
  change
    ((fun x ↦ F x = 0 ∧ G x = 0) : LocalSetGerm n) ≤
      ((fun x ↦ F x + G x = 0) : LocalSetGerm n)
  rw [Filter.Germ.coe_le]
  exact Filter.Eventually.of_forall fun _ h ↦ by simp [h.1, h.2]

/-- Every zero of `f` is a zero of a left multiple of `f`. -/
theorem germZeroLocus_le_mul {n : ℕ} (a f : HolomorphicGerm n) :
    germZeroLocus f ≤ germZeroLocus (a * f) := by
  change
    Filter.Germ.map (fun z : ℂ ↦ z = 0) (f : FunctionGerm n) ≤
      Filter.Germ.map (fun z : ℂ ↦ z = 0)
        ((a : FunctionGerm n) * (f : FunctionGerm n))
  refine Filter.Germ.inductionOn₂ (a : FunctionGerm n) (f : FunctionGerm n) ?_
  intro A F
  change
    ((fun x ↦ F x = 0) : LocalSetGerm n) ≤
      ((fun x ↦ A x * F x = 0) : LocalSetGerm n)
  rw [Filter.Germ.coe_le]
  exact Filter.Eventually.of_forall fun _ h ↦ by simp [h]

/-- A positive power has exactly the same local zero-set germ. -/
theorem germZeroLocus_pow {n : ℕ} (f : HolomorphicGerm n)
    {k : ℕ} (hk : 0 < k) :
    germZeroLocus (f ^ k) = germZeroLocus f := by
  change
    Filter.Germ.map (fun z : ℂ ↦ z = 0)
        ((f : FunctionGerm n) ^ k) =
      Filter.Germ.map (fun z : ℂ ↦ z = 0) (f : FunctionGerm n)
  refine Filter.Germ.inductionOn (f : FunctionGerm n) ?_
  intro F
  apply Filter.Germ.coe_eq.mpr
  exact Filter.Eventually.of_forall fun x ↦ propext (by
    simpa [Function.comp_apply] using
      (pow_eq_zero_iff hk.ne' : F x ^ k = 0 ↔ F x = 0))

/-- A holomorphic germ vanishes on a full neighborhood exactly when it is the
zero germ. -/
theorem germZeroLocus_eq_top_iff {n : ℕ} (f : HolomorphicGerm n) :
    germZeroLocus f = ⊤ ↔ f = 0 := by
  constructor
  · intro h
    obtain ⟨F, hF, hrep⟩ := HolomorphicGerm.exists_rep f
    have hz : (⊤ : LocalSetGerm n) ≤ germZeroLocus f := h.symm.le
    change
      ((fun _ : ComplexEuclidean n ↦ True) : LocalSetGerm n) ≤
        Filter.Germ.map (fun z : ℂ ↦ z = 0) (f : FunctionGerm n) at hz
    rw [← hrep] at hz
    change
      ((fun _ : ComplexEuclidean n ↦ True) : LocalSetGerm n) ≤
        ((fun x ↦ F x = 0) : LocalSetGerm n) at hz
    rw [Filter.Germ.coe_le] at hz
    apply Subtype.ext
    change (f : FunctionGerm n) = 0
    rw [← hrep, ← Filter.Germ.coe_zero]
    apply Filter.Germ.coe_eq.mpr
    exact hz.mono fun x hx ↦ hx True.intro
  · rintro rfl
    exact germZeroLocus_zero n

/-- Holomorphic germs vanishing on a fixed local set germ form an ideal. -/
def vanishingIdeal {n : ℕ} (Z : LocalSetGerm n) : Ideal (HolomorphicGerm n) where
  carrier := {f | Z ≤ germZeroLocus f}
  zero_mem' := by simp
  add_mem' := by
    intro f g hf hg
    exact (le_inf hf hg).trans (germZeroLocus_inf_le_add f g)
  smul_mem' := by
    intro a f hf
    exact hf.trans (germZeroLocus_le_mul a f)

@[simp]
theorem mem_vanishingIdeal {n : ℕ} {Z : LocalSetGerm n}
    {f : HolomorphicGerm n} :
    f ∈ vanishingIdeal Z ↔ Z ≤ germZeroLocus f :=
  Iff.rfl

/-- The only holomorphic germ vanishing on a full neighborhood is zero. -/
@[simp]
theorem vanishingIdeal_top (n : ℕ) :
    vanishingIdeal (⊤ : LocalSetGerm n) = ⊥ := by
  ext f
  rw [mem_vanishingIdeal, Ideal.mem_bot, top_le_iff,
    germZeroLocus_eq_top_iff]

/-- Common zero set of a finite family of germs. -/
def finiteCommonZeroSet {n : ℕ} (S : Finset (HolomorphicGerm n)) :
    LocalSetGerm n :=
  S.inf germZeroLocus

/-- Common zero-set germ of a finite indexed family.  Unlike a `Finset` of
germs, this retains the indices used by the comparator-facing certificate. -/
def indexedCommonZeroSet {n s : ℕ}
    (f : Fin s → HolomorphicGerm n) : LocalSetGerm n :=
  Finset.univ.inf fun i ↦ germZeroLocus (f i)

/-- Common zero-set germ of a family indexed by an arbitrary finite type. -/
def fintypeCommonZeroSet {n : ℕ} {ι : Type*} [Fintype ι]
    (f : ι → HolomorphicGerm n) : LocalSetGerm n :=
  Finset.univ.inf fun i ↦ germZeroLocus (f i)

private def localSetGermOfFunInfTopHom (n : ℕ) :
    InfTopHom (ComplexEuclidean n → Prop) (LocalSetGerm n) where
  toFun P := (P : LocalSetGerm n)
  map_inf' _ _ := rfl
  map_top' := rfl

/-- The indexed set-germ definition has the expected eventual pointwise
meaning for a concrete representative family. -/
theorem indexedCommonZeroSet_ofFunction {n s : ℕ}
    (f : Fin s → ComplexEuclidean n → ℂ)
    (hf : ∀ i, AnalyticAt ℂ (f i) 0) :
    indexedCommonZeroSet (fun i ↦ HolomorphicGerm.ofFunction (f i) (hf i)) =
      ((fun x ↦ ∀ i, f i x = 0) : LocalSetGerm n) := by
  unfold indexedCommonZeroSet germZeroLocus
  change
    Finset.univ.inf (fun i ↦
      ((fun x ↦ f i x = 0) : LocalSetGerm n)) = _
  calc
    _ = localSetGermOfFunInfTopHom n
        (Finset.univ.inf fun i ↦ fun x ↦ f i x = 0) := by
      exact (map_finset_inf (localSetGermOfFunInfTopHom n) _ _).symm
    _ = ((fun x ↦ ∀ i, f i x = 0) : LocalSetGerm n) := by
      apply Filter.Germ.coe_eq.mpr
      exact Filter.Eventually.of_forall fun x ↦ propext (by
        rw [Finset.inf_eq_iInf]
        simp)

/-- The finite-type common zero set has its expected pointwise meaning for
concrete analytic representatives. -/
theorem fintypeCommonZeroSet_ofFunction {n : ℕ} {ι : Type*} [Fintype ι]
    (f : ι → ComplexEuclidean n → ℂ)
    (hf : ∀ i, AnalyticAt ℂ (f i) 0) :
    fintypeCommonZeroSet
        (fun i ↦ HolomorphicGerm.ofFunction (f i) (hf i)) =
      ((fun x ↦ ∀ i, f i x = 0) : LocalSetGerm n) := by
  unfold fintypeCommonZeroSet germZeroLocus
  change
    Finset.univ.inf (fun i ↦
      ((fun x ↦ f i x = 0) : LocalSetGerm n)) = _
  calc
    _ = localSetGermOfFunInfTopHom n
        (Finset.univ.inf fun i ↦ fun x ↦ f i x = 0) := by
      exact (map_finset_inf (localSetGermOfFunInfTopHom n) _ _).symm
    _ = ((fun x ↦ ∀ i, f i x = 0) : LocalSetGerm n) := by
      apply Filter.Germ.coe_eq.mpr
      exact Filter.Eventually.of_forall fun x ↦ propext (by
        rw [Finset.inf_eq_iInf]
        simp)

/-- Translate a finite-type representative common-zero hypothesis into the
order relation on local set germs. -/
theorem fintypeCommonZeroSet_le_iff_eventually {n : ℕ}
    {ι : Type*} [Fintype ι]
    (f : ι → ComplexEuclidean n → ℂ)
    (hf : ∀ i, AnalyticAt ℂ (f i) 0)
    (g : ComplexEuclidean n → ℂ) (hg : AnalyticAt ℂ g 0) :
    fintypeCommonZeroSet
        (fun i ↦ HolomorphicGerm.ofFunction (f i) (hf i)) ≤
        germZeroLocus (HolomorphicGerm.ofFunction g hg) ↔
      ∀ᶠ x in 𝓝 0, (∀ i, f i x = 0) → g x = 0 := by
  rw [fintypeCommonZeroSet_ofFunction f hf]
  change
    ((fun x ↦ ∀ i, f i x = 0) : LocalSetGerm n) ≤
        ((fun x ↦ g x = 0) : LocalSetGerm n) ↔ _
  exact Filter.Germ.coe_le

/-- A finite set and the family indexed by its subtype define the same common
zero-set germ. -/
theorem finiteCommonZeroSet_eq_fintypeCommonZeroSet_subtype {n : ℕ}
    (S : Finset (HolomorphicGerm n)) :
    finiteCommonZeroSet S =
      fintypeCommonZeroSet (fun f : S ↦ (f : HolomorphicGerm n)) := by
  classical
  unfold finiteCommonZeroSet fintypeCommonZeroSet
  apply le_antisymm
  · apply Finset.le_inf
    intro f hf
    exact Finset.inf_le f.property
  · apply Finset.le_inf
    intro f hf
    exact Finset.inf_le
      (show (⟨f, hf⟩ : S) ∈ (Finset.univ : Finset S) by simp)

/-- Translate the representative-level eventual common-zero hypothesis into
the order relation on local set germs. -/
theorem indexedCommonZeroSet_le_iff_eventually {n s : ℕ}
    (f : Fin s → ComplexEuclidean n → ℂ)
    (hf : ∀ i, AnalyticAt ℂ (f i) 0)
    (g : ComplexEuclidean n → ℂ) (hg : AnalyticAt ℂ g 0) :
    indexedCommonZeroSet (fun i ↦ HolomorphicGerm.ofFunction (f i) (hf i)) ≤
        germZeroLocus (HolomorphicGerm.ofFunction g hg) ↔
      ∀ᶠ x in 𝓝 0, (∀ i, f i x = 0) → g x = 0 := by
  rw [indexedCommonZeroSet_ofFunction f hf]
  change
    ((fun x ↦ ∀ i, f i x = 0) : LocalSetGerm n) ≤
        ((fun x ↦ g x = 0) : LocalSetGerm n) ↔ _
  exact Filter.Germ.coe_le

theorem finiteCommonZeroSet_le_germZeroLocus {n : ℕ}
    (S : Finset (HolomorphicGerm n)) {f : HolomorphicGerm n} (hf : f ∈ S) :
    finiteCommonZeroSet S ≤ germZeroLocus f :=
  Finset.inf_le hf

/-- Every member of the ideal spanned by `S` vanishes on the common zero set of `S`. -/
theorem finiteCommonZeroSet_le_germZeroLocus_of_mem_span {n : ℕ}
    (S : Finset (HolomorphicGerm n)) {f : HolomorphicGerm n}
    (hf : f ∈ Ideal.span (S : Set (HolomorphicGerm n))) :
    finiteCommonZeroSet S ≤ germZeroLocus f := by
  have hspan : Ideal.span (S : Set (HolomorphicGerm n)) ≤
      vanishingIdeal (finiteCommonZeroSet S) := by
    apply Ideal.span_le.mpr
    intro g hg
    exact finiteCommonZeroSet_le_germZeroLocus S hg
  exact hspan hf

/-- Enlarging the generated ideal shrinks the corresponding finite zero set. -/
theorem finiteCommonZeroSet_antitone_span {n : ℕ}
    (S T : Finset (HolomorphicGerm n))
    (h : Ideal.span (S : Set (HolomorphicGerm n)) ≤
      Ideal.span (T : Set (HolomorphicGerm n))) :
    finiteCommonZeroSet T ≤ finiteCommonZeroSet S := by
  apply Finset.le_inf
  intro f hf
  apply finiteCommonZeroSet_le_germZeroLocus_of_mem_span T
  exact h (Ideal.subset_span hf)

/-- The finite common zero-set germ depends only on the generated ideal. -/
theorem finiteCommonZeroSet_eq_of_span_eq {n : ℕ}
    (S T : Finset (HolomorphicGerm n))
    (h : Ideal.span (S : Set (HolomorphicGerm n)) =
      Ideal.span (T : Set (HolomorphicGerm n))) :
    finiteCommonZeroSet S = finiteCommonZeroSet T := by
  apply le_antisymm
  · exact finiteCommonZeroSet_antitone_span T S h.symm.le
  · exact finiteCommonZeroSet_antitone_span S T h.le

/-- A fixed finite generating set selected from Noetherianity. -/
def idealGeneratorFinset {n : ℕ} [IsNoetherianRing (HolomorphicGerm n)]
    (I : Ideal (HolomorphicGerm n)) : Finset (HolomorphicGerm n) :=
  Classical.choose (Ideal.fg_of_isNoetherianRing I)

theorem span_idealGeneratorFinset {n : ℕ}
    [IsNoetherianRing (HolomorphicGerm n)]
    (I : Ideal (HolomorphicGerm n)) :
    Ideal.span (idealGeneratorFinset I : Set (HolomorphicGerm n)) = I :=
  Classical.choose_spec (Ideal.fg_of_isNoetherianRing I)

/-- The zero-set germ of an ideal, defined through a finite generating set. -/
def idealZeroSetGerm {n : ℕ} [IsNoetherianRing (HolomorphicGerm n)]
    (I : Ideal (HolomorphicGerm n)) : LocalSetGerm n :=
  finiteCommonZeroSet (idealGeneratorFinset I)

/-- Generator independence for the ideal zero-set germ. -/
theorem idealZeroSetGerm_eq_of_span_eq {n : ℕ}
    [IsNoetherianRing (HolomorphicGerm n)]
    (I : Ideal (HolomorphicGerm n))
    (S : Finset (HolomorphicGerm n))
    (hS : Ideal.span (S : Set (HolomorphicGerm n)) = I) :
    idealZeroSetGerm I = finiteCommonZeroSet S := by
  unfold idealZeroSetGerm
  apply finiteCommonZeroSet_eq_of_span_eq
  exact (span_idealGeneratorFinset I).trans hS.symm

@[simp]
theorem idealZeroSetGerm_bot {n : ℕ}
    [IsNoetherianRing (HolomorphicGerm n)] :
    idealZeroSetGerm (⊥ : Ideal (HolomorphicGerm n)) = ⊤ := by
  rw [idealZeroSetGerm_eq_of_span_eq
    (⊥ : Ideal (HolomorphicGerm n)) ∅ (by simp)]
  simp [finiteCommonZeroSet]

/-- Every member of an ideal vanishes on its local zero-set germ. -/
theorem idealZeroSetGerm_le_germZeroLocus_of_mem {n : ℕ}
    [IsNoetherianRing (HolomorphicGerm n)]
    (I : Ideal (HolomorphicGerm n)) {f : HolomorphicGerm n} (hf : f ∈ I) :
    idealZeroSetGerm I ≤ germZeroLocus f := by
  unfold idealZeroSetGerm
  apply finiteCommonZeroSet_le_germZeroLocus_of_mem_span
  rw [span_idealGeneratorFinset]
  exact hf

/-- Inclusion of ideals reverses inclusion of their local zero-set germs. -/
theorem idealZeroSetGerm_antitone {n : ℕ}
    [IsNoetherianRing (HolomorphicGerm n)]
    {I J : Ideal (HolomorphicGerm n)} (hIJ : I ≤ J) :
    idealZeroSetGerm J ≤ idealZeroSetGerm I := by
  unfold idealZeroSetGerm
  apply Finset.le_inf
  intro f hf
  apply idealZeroSetGerm_le_germZeroLocus_of_mem J
  apply hIJ
  rw [← span_idealGeneratorFinset I]
  exact Ideal.subset_span hf

end

end LocalComplexGeometry
