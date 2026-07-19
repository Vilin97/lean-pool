/-
Copyright (c) 2026 Anthony Vandikas, Kiarash Sotoudeh. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anthony Vandikas, Kiarash Sotoudeh
-/

import Mathlib.MeasureTheory.Constructions.UnitInterval
import Mathlib.MeasureTheory.Measure.DiracProba
import LeanPool.QuasiBorelSpaces.Hom
import LeanPool.QuasiBorelSpaces.MeasureTheory.Measure
import LeanPool.QuasiBorelSpaces.MeasureTheory.ProbabilityMeasure
import LeanPool.QuasiBorelSpaces.Prop

/-!
# LeanPool.QuasiBorelSpaces.PreProbabilityMeasure

Imported Lean Pool material for `LeanPool.QuasiBorelSpaces.PreProbabilityMeasure`.
-/

open MeasureTheory
open scoped unitInterval

namespace QuasiBorelSpace

variable
  {A : Type*} [QuasiBorelSpace A]
  {B : Type*} [QuasiBorelSpace B]
  {C : Type*} [QuasiBorelSpace C]
  {D : Type*} [QuasiBorelSpace D]

/--
A precursor to the type of probability measures. Intuitively, a
_(quasi-borel) probability measure_ is just a variable applied to a normal
probability measure on `ℝ`. A `PreProbabilityMeasure` holds the underlying
variable and probability measure.
-/
@[ext]
structure PreProbabilityMeasure (A : Type*) [QuasiBorelSpace A] where
  /-- The random variable associated with the probability measure. -/
  eval : ℝ →𝒒 A
  /-- The base `ProbabilityMeasure`. -/
  base : ProbabilityMeasure ℝ

namespace PreProbabilityMeasure

/-- The integral of a function relative to a probability measure. -/
noncomputable def lintegral (f : A → ENNReal) : PreProbabilityMeasure A → ENNReal
  | ⟨φ, μ⟩ => ∫⁻ x, f (φ x) ∂μ

@[simp]
alias lintegral_mk := PreProbabilityMeasure.lintegral.eq_1

/-- TODO -/
noncomputable def measureOf : PreProbabilityMeasure A → Set A → ENNReal
  | ⟨φ, μ⟩, s => μ { x | φ x ∈ s }

@[simp]
alias measureOf_mk := PreProbabilityMeasure.measureOf.eq_1

@[simp]
lemma lintegral_eq_measureOf
    (μ : PreProbabilityMeasure A) (s : Set A) (hp : IsHom (· ∈ s))
    : lintegral (s.indicator 1) μ = measureOf μ s := by
  rcases μ with ⟨φ, μ⟩
  simp only [lintegral_mk, measureOf_mk, ProbabilityMeasure.ennreal_coeFn_eq_coeFn_toMeasure]
  rw [←MeasureTheory.lintegral_indicator_one]
  · simp only [Set.indicator, Set.mem_setOf_eq, Pi.one_apply]
    rfl
  · have := isHom_comp' hp φ.isHom_coe
    simpa only [measurableSet_setOf, isHom_ofMeasurableSpace] using this

/--
A `PreProbabilityMeasure` can be constructed from any `ProbabilityMeasure` on a
standard borel space.
-/
noncomputable def mk'
    [MeasurableSpace A] [MeasurableQuasiBorelSpace A] [StandardBorelSpace A]
    (eval : A →𝒒 B) (base : ProbabilityMeasure A)
    : PreProbabilityMeasure B where
  eval :=
    have : Nonempty A := base.nonempty
    .mk fun x ↦ eval (unpack x)
  base := base.map measurable_pack.aemeasurable

@[simp]
lemma lintegral_mk'
    [MeasurableSpace A] [MeasurableQuasiBorelSpace A] [StandardBorelSpace A]
    {k : B → ENNReal} (hk : IsHom k)
    (φ : A →𝒒 B) (μ : ProbabilityMeasure A)
    : lintegral k (mk' φ μ) = ∫⁻ (x : A), k (φ x) ∂μ.toMeasure := by
  simp only [mk', lintegral_mk, ProbabilityMeasure.toMeasure_map, QuasiBorelHom.coe_mk]
  rw [lintegral_map]
  · simp only [unpack_pack]
  · apply measurable_of_isHom
    fun_prop
  · fun_prop

lemma lintegral_add_left
    {f : A → ENNReal} (hf : IsHom f)
    (g : A → ENNReal) (μ : PreProbabilityMeasure A)
    : lintegral (f + g) μ = lintegral f μ + lintegral g μ := by
  rcases μ with ⟨eval, base⟩
  simp only [lintegral_mk, Pi.add_apply]
  apply MeasureTheory.lintegral_add_left
  apply measurable_of_isHom
  fun_prop

lemma lintegral_add_right
    (f : A → ENNReal)
    {g : A → ENNReal} (hg : IsHom g)
    (μ : PreProbabilityMeasure A)
    : lintegral (f + g) μ = lintegral f μ + lintegral g μ := by
  rcases μ with ⟨eval, base⟩
  simp only [lintegral_mk, Pi.add_apply]
  apply MeasureTheory.lintegral_add_right
  apply measurable_of_isHom
  fun_prop

instance setoid (A : Type*) [QuasiBorelSpace A] : Setoid (PreProbabilityMeasure A) where
  r μ₁ μ₂ := ∀⦃f⦄, IsHom f → μ₁.lintegral f = μ₂.lintegral f
  iseqv := {
    refl _ _ _ := rfl
    symm h₁ _ h₂ := (h₁ h₂).symm
    trans h₁ h₂ _ h₃ := (h₁ h₃).trans (h₂ h₃)
  }

lemma lintegral_mul_left
    (c : ENNReal) {f : A → ENNReal} (hf : IsHom f) (μ : PreProbabilityMeasure A)
    : lintegral (fun x ↦ c * f x) μ = c * lintegral f μ := by
  rcases μ with ⟨eval, base⟩
  simp only [lintegral_mk]
  apply MeasureTheory.lintegral_const_mul
  apply measurable_of_isHom
  fun_prop

lemma lintegral_mul_right
    (c : ENNReal) {f : A → ENNReal} (hf : IsHom f) (μ : PreProbabilityMeasure A)
    : lintegral (fun x ↦ f x * c) μ = lintegral f μ * c := by
  rcases μ with ⟨eval, base⟩
  simp only [lintegral_mk]
  apply MeasureTheory.lintegral_mul_const
  apply measurable_of_isHom
  fun_prop

@[simp]
lemma lintegral_const
    (c : ENNReal) (μ : PreProbabilityMeasure A)
    : lintegral (fun _ ↦ c) μ = c := by
  rcases μ with ⟨eval, base⟩
  simp only [lintegral_mk, MeasureTheory.lintegral_const, measure_univ, mul_one]

@[simp]
lemma lintegral_mono
    {f g : A → ENNReal} (h : f ≤ g) (μ : PreProbabilityMeasure A)
    : lintegral f μ ≤ lintegral g μ := by
  rcases μ with ⟨eval, base⟩
  simpa only [lintegral_mk] using MeasureTheory.lintegral_mono fun a ↦ h _

lemma lintegral_iSup
    (f : ℕ → A → ENNReal) (hf₁ : Monotone f) (hf₂ : ∀ n, IsHom (f n)) (μ : PreProbabilityMeasure A)
    : ⨆n, lintegral (f n) μ = lintegral (⨆n, f n) μ := by
  rcases μ with ⟨eval, base⟩
  simp only [lintegral_mk, iSup_apply]
  rw [MeasureTheory.lintegral_iSup]
  · intro n
    simpa only [isHom_ofMeasurableSpace] using isHom_comp' (hf₂ n) eval.isHom_coe
  · exact fun i j h x ↦ hf₁ h _

lemma lintegral_finset_sum {A}
    (s : Finset A) {f : A → B → ENNReal}
    (hf : ∀ b ∈ s, IsHom (f b)) (μ : PreProbabilityMeasure B) :
    lintegral (fun a ↦ ∑ b ∈ s, f b a) μ = ∑ b ∈ s, lintegral (f b) μ := by
  rcases μ with ⟨eval, base⟩
  simp only [lintegral_mk]
  rw [MeasureTheory.lintegral_finsetSum]
  intro b hb
  simpa only [isHom_ofMeasurableSpace] using isHom_comp' (hf b hb) eval.isHom_coe

lemma lintegral_sub_le
    (f : A → ENNReal)
    {g : A → ENNReal} (hg : IsHom g)
    (μ : PreProbabilityMeasure A)
    : lintegral f μ - lintegral g μ ≤ lintegral (f - g) μ := by
  simp only [lintegral, Pi.sub_apply]
  apply MeasureTheory.lintegral_sub_le
  have : IsHom fun x ↦ g (μ.eval x) := by fun_prop
  simpa only [isHom_ofMeasurableSpace] using this

theorem lintegral_lintegral_swap
    {μ : PreProbabilityMeasure A} {ν : PreProbabilityMeasure B}
    ⦃f : A → B → ENNReal⦄ (hf : IsHom (Function.uncurry f)) :
    lintegral (fun x ↦ lintegral (f x) ν) μ =
    lintegral (fun x ↦ lintegral (f · x) μ) ν := by
  simp only [lintegral]
  rw [MeasureTheory.lintegral_lintegral_swap]
  apply Measurable.aemeasurable
  apply measurable_of_isHom
  fun_prop

@[simp]
lemma measureOf_empty (μ : PreProbabilityMeasure B) : measureOf μ ∅ = 0 := by
  rcases μ
  simp only [
    measureOf_mk, Set.mem_empty_iff_false, Set.setOf_false,
    ProbabilityMeasure.coeFn_empty, ENNReal.coe_zero]

@[simp]
lemma measureOf_mono (μ : PreProbabilityMeasure B) : Monotone (measureOf μ) := by
  intro p q h
  rcases μ
  simp only [measureOf_mk, ProbabilityMeasure.ennreal_coeFn_eq_coeFn_toMeasure]
  exact measure_mono fun r hr ↦ h hr

lemma measureOf_iUnion_le {ι : Type*} [Countable ι]
    (μ : PreProbabilityMeasure A) (s : ι → Set A)
    : μ.measureOf (⋃ i, s i) ≤ ∑' (i : ι), μ.measureOf (s i) := by
  rcases μ
  simp only [
    measureOf_mk, Set.mem_iUnion, Set.setOf_exists,
    ProbabilityMeasure.ennreal_coeFn_eq_coeFn_toMeasure]
  apply measure_iUnion_le

@[simp]
lemma setoid_r (μ₁ μ₂ : PreProbabilityMeasure A) : (setoid A).r μ₁ μ₂ ↔ μ₁ ≈ μ₂ := by rfl

lemma equiv_def (μ₁ μ₂ : PreProbabilityMeasure A)
    : μ₁ ≈ μ₂ ↔ (∀{f}, IsHom f → μ₁.lintegral f = μ₂.lintegral f) := by
  rfl

lemma equiv_def' (μ₁ μ₂ : PreProbabilityMeasure A)
    : μ₁ ≈ μ₂ ↔ (∀{p}, IsHom (· ∈ p) → μ₁.measureOf p = μ₂.measureOf p) := by
  classical
  apply Iff.intro
  · intro h p hp
    simp (disch := fun_prop) only [← lintegral_eq_measureOf]
    apply h
    simp +unfoldPartialApp only [Set.indicator, Pi.one_apply]
    apply Prop.isHom_ite <;> fun_prop
  · intro h k hk
    rcases μ₁ with ⟨φ₁, μ₁⟩
    rcases μ₂ with ⟨φ₂, μ₂⟩
    simp only [
      ProbabilityMeasure.ennreal_coeFn_eq_coeFn_toMeasure,
      measureOf_mk, lintegral_mk] at ⊢ h
    let := toMeasurableSpace (A := A)
    have (φ : ℝ →𝒒 A) (μ : Measure ℝ)
        : ∫⁻ (x : ℝ), k (φ x) ∂μ
        = ∫⁻ (x : A), k x ∂(μ.map φ) := by
      rw [lintegral_map]
      · intro X hX φ hφ
        have := isHom_comp' hk hφ
        simp only [isHom_ofMeasurableSpace] at this
        apply this hX
      · intro X hX
        apply hX
        fun_prop
    simp only [this]
    have (p : Set A) (hp : IsHom (· ∈ p)) (φ : ℝ →𝒒 A) (μ : Measure ℝ)
        : μ {x | φ x ∈ p}
        = μ.map φ p := by
      rw [Measure.map_apply]
      · simp only [Set.preimage]
      · intro X hX
        apply hX
        simp only [QuasiBorelHom.isHom_coe]
      · intro φ hφ
        have := isHom_comp' hp hφ
        simpa only [Set.preimage, measurableSet_setOf, isHom_ofMeasurableSpace] using this
    simp +contextual only [this] at h
    congr 1
    ext X hX
    apply h
    rw [isHom_def]
    intro φ hφ
    specialize hX hφ
    simpa only [Set.preimage, measurableSet_setOf, isHom_ofMeasurableSpace] using hX

lemma nonempty (μ : PreProbabilityMeasure A) : Nonempty A := ⟨μ.eval 0⟩

/-- The type of variables for probability measures. -/
structure Var (A : Type*) [QuasiBorelSpace A] where
  /-- The random variable associated with each probability measure. -/
  eval : ℝ →𝒒 A
  /-- The family of base `ProbabilityMeasures`. -/
  base : ℝ → ProbabilityMeasure ℝ
  /-- The family of base measures is measurable. -/
  measurable_base : Measurable base := by fun_prop

namespace Var

attribute [fun_prop] measurable_base

/-- Evaluates a `Var`. -/
def apply : Var A → ℝ → PreProbabilityMeasure A
  | ⟨φ, μ, _⟩, r => ⟨φ, μ r⟩

@[simp]
alias measureOf_mk := apply.eq_1

instance : CoeFun (Var A) (fun _ ↦ ℝ → PreProbabilityMeasure A) where
  coe := apply

/-- The constant variable. -/
def const (μ : PreProbabilityMeasure A) : Var A where
  eval := μ.eval
  base _ := μ.base

@[simp]
lemma apply_const (μ : PreProbabilityMeasure A) (r : ℝ) : apply (const μ) r = μ := rfl

/-- Precomposition of variables by measurable functions. -/
def comp {f : ℝ → ℝ} (hf : Measurable f) (φ : Var A) : Var A where
  eval := φ.eval
  base r := φ.base (f r)

@[simp]
lemma apply_comp
    {f : ℝ → ℝ} (hf : Measurable f) (φ : Var A) (r : ℝ)
    : apply (comp hf φ) r = apply φ (f r) :=
  rfl

/-- Gluing of a countable number of variables. -/
noncomputable def cases
    {ix : ℝ → ℕ} (hix : Measurable ix)
    (φ : ℕ → Var A) : Var A where
  eval := {
    toFun r := (φ (unpack r : ℕ × ℝ).1).eval (unpack r : ℕ × ℝ).2
    property := by
      apply isHom_cases
          (ix := fun r ↦ (unpack r : ℕ × ℝ).1)
          (f := fun n r ↦ (φ n).eval (unpack r : ℕ × ℝ).2)
      · fun_prop
      · fun_prop
  }
  base r := ((φ (ix r)).base r).map (f := fun x ↦ pack (ix r, x)) (by fun_prop)
  measurable_base := by
    apply measurable_cases (f := fun n r ↦
        ((φ n).base r).map (f := fun x ↦ pack (n, x)) (by fun_prop))
    · exact hix
    · intro i
      apply Measurable.subtype_mk
      apply Measure.measurable_map'
      · fun_prop
      · apply Measurable.subtype_val
        fun_prop

lemma apply_cases
    {ix : ℝ → ℕ} (hix : Measurable ix)
    (φ : ℕ → Var A) (r : ℝ)
    : apply (cases hix φ) r ≈ φ (ix r) r := by
  simp only [cases, measureOf_mk, equiv_def, lintegral_mk, QuasiBorelHom.coe_mk]
  intro f hf
  simp only [ProbabilityMeasure.toMeasure_map]
  rw [lintegral_map]
  · simp only [unpack_pack]
    simp only [lintegral, apply]
  · apply measurable_cases (f := fun n r ↦ f ((φ n).eval (unpack r : ℕ × ℝ).2))
    · fun_prop
    · intro i
      apply Measurable.fun_comp (g := fun r ↦ f _) (f := fun r ↦ (unpack r : ℕ × ℝ).2)
      · apply measurable_of_isHom
        fun_prop
      · fun_prop
  · fun_prop

end Var

instance : QuasiBorelSpace (PreProbabilityMeasure A) where
  IsVar φ := ∃(ψ : Var A), ∀r, φ r ≈ ψ r
  isVar_const μ := by
    use Var.const μ
    simp only [Var.apply_const, Setoid.refl, implies_true]
  isVar_comp hf := by
    rintro ⟨μ, hμ⟩
    use Var.comp hf μ
    simp only [Var.apply_comp]
    intro r
    apply hμ
  isVar_cases' hix hφ := by
    choose φ hφ using hφ
    use Var.cases hix φ
    simp only
    intro r
    trans
    · apply hφ
    · symm
      apply Var.apply_cases

@[local simp]
lemma isHom_def (φ : ℝ → PreProbabilityMeasure A) : IsHom φ ↔ ∃(ψ : Var A), ∀r, φ r ≈ ψ r := by
  rw [← isVar_iff_isHom]
  rfl

namespace Var

@[simp, fun_prop]
lemma isHom_apply (φ : Var A) : IsHom φ.apply := by
  simp only [isHom_def]
  use φ
  simp only [Setoid.refl, implies_true]

end Var

/-- The variable associated with a `PreProbabilityMeasure` variable. -/
noncomputable def subeval (φ : ℝ → PreProbabilityMeasure A) : ℝ →𝒒 A :=
  open Classical in
  if hφ : IsHom φ
  then (Classical.choose ((isVar_iff_isHom _).2 hφ)).eval
  else .mk fun _ ↦ Classical.choice ((φ 0).nonempty)

/-- The measure associated with a `PreProbabilityMeasure` variable. -/
noncomputable def subbase (φ : ℝ → PreProbabilityMeasure A) : ℝ → ProbabilityMeasure ℝ :=
  open Classical in
  if hφ : IsHom φ
  then (Classical.choose ((isVar_iff_isHom _).2 hφ)).base
  else fun _ ↦ default

@[simp, fun_prop]
lemma measurable_subbase (φ : ℝ → PreProbabilityMeasure A) : Measurable (subbase φ) := by
  by_cases hφ : IsHom φ
  · simp only [subbase, hφ, ↓reduceDIte]
    apply (Classical.choose ((isVar_iff_isHom _).2 hφ)).measurable_base
  · simp only [subbase, hφ, ↓reduceDIte, measurable_const]

lemma sub_eq
    {φ : ℝ → PreProbabilityMeasure A} (hφ : IsHom φ)
    : ∀r, φ r ≈ .mk (subeval φ) (subbase φ r) := by
  simp only [subeval, hφ, ↓reduceDIte, subbase]
  exact Classical.choose_spec ((isVar_iff_isHom _).2 hφ)

@[fun_prop]
lemma isHom_lintegral
    {k : A → B → ENNReal} (hk : IsHom fun (x, y) ↦ k x y)
    {f : A → PreProbabilityMeasure B} (hf : IsHom f)
    : IsHom (fun x ↦ lintegral (k x) (f x)) := by
  rw [QuasiBorelSpace.isHom_def]
  intro φ hφ
  simp only [lintegral, isHom_ofMeasurableSpace]
  have {r} := sub_eq (hf hφ) r (f := k (φ r)) (by fun_prop)
  simp only [lintegral] at this
  simp only [this]
  let κ : ProbabilityTheory.Kernel ℝ ℝ := {
    toFun x := ↑(subbase (fun x ↦ f (φ x)) x)
    measurable' := by
      apply Measurable.subtype_val
      fun_prop
  }
  have : ProbabilityTheory.IsFiniteKernel κ := by
    constructor
    use 1
    simp only [
      ENNReal.one_lt_top, ProbabilityTheory.Kernel.coe_mk,
      measure_univ, le_refl, implies_true, and_self, κ]
  change Measurable fun x ↦ ∫⁻ x, _ ∂κ x
  apply Measurable.lintegral_kernel_prod_left
  unfold Function.uncurry
  dsimp only
  replace hk := hk
    (φ := fun r ↦ (φ (unpack r : ℝ × ℝ).2, ((subeval fun x ↦ f (φ x)) (unpack r : ℝ × ℝ).1)))
    (by fun_prop)
  simp only [isHom_ofMeasurableSpace] at hk
  have := Measurable.fun_comp hk (by fun_prop : Measurable (pack (A := ℝ × ℝ)))
  simp only [unpack_pack] at this
  exact this

@[gcongr]
lemma lintegral_congr
    {k : A → ENNReal} (hk : IsHom k)
    {μ₁ μ₂ : PreProbabilityMeasure A} (hμ : μ₁ ≈ μ₂)
    : lintegral k μ₁ = lintegral k μ₂ := by
  apply hμ hk

@[gcongr]
lemma measureOf_congr
    {p : Set A} (hk : IsHom (· ∈ p))
    {μ₁ μ₂ : PreProbabilityMeasure A} (hμ : μ₁ ≈ μ₂)
    : measureOf μ₁ p = measureOf μ₂ p := by
  rw [equiv_def'] at hμ
  apply hμ hk

@[gcongr]
lemma isHom_congr {f g : A → PreProbabilityMeasure B} (h : ∀ x, f x ≈ g x) : IsHom f ↔ IsHom g := by
  apply Iff.intro <;>
  · intro h'
    rw [QuasiBorelSpace.isHom_def] at ⊢ h'
    simp only [isHom_def] at ⊢ h'
    intro ψ hψ
    rcases h' hψ with ⟨φ, hφ⟩
    use φ
    intro r
    grw [←hφ r, h]

/-- The unit operation, a.k.a. the dirac measure. -/
noncomputable def unit (x : A) : PreProbabilityMeasure A where
  eval := .mk (fun _ ↦ x)
  base := default

@[simp]
lemma lintegral_unit (f : A → ENNReal) (x : A) : lintegral f (unit x) = f x := by
  simp only [
    unit, lintegral_mk, QuasiBorelHom.coe_mk,
    MeasureTheory.lintegral_const, measure_univ, mul_one]

namespace Var

/-- The dirac measure, lifted to variables. -/
noncomputable def unit {φ : ℝ → A} (hφ : IsHom φ) : Var A where
  eval := .mk φ hφ
  base := diracProba
  measurable_base := by
    apply Measurable.subtype_mk
    fun_prop

@[simp]
lemma apply_unit
    {φ : ℝ → A} (hφ : IsHom φ) (r : ℝ)
    : apply (unit hφ) r ≈ PreProbabilityMeasure.unit (φ r) := by
  intro ψ hψ
  simp only [unit, measureOf_mk, diracProba, lintegral_mk, ProbabilityMeasure.coe_mk,
    QuasiBorelHom.coe_mk, lintegral_dirac, lintegral_unit]

end Var

@[fun_prop]
lemma isHom_unit : IsHom (unit (A := A)) := by
  rw [QuasiBorelSpace.isHom_def]
  simp only [isHom_def]
  intro φ hφ
  use Var.unit hφ
  intro r
  symm
  simp only [Var.apply_unit]

/-- The monadic bind operation for probability measures. -/
noncomputable def bind
    (f : A → PreProbabilityMeasure B) (μ : PreProbabilityMeasure A)
    : PreProbabilityMeasure B where
  eval := subeval (f ∘ μ.eval)
  base := ProbabilityMeasure.bind μ.base (subbase (f ∘ μ.eval))

@[simp]
lemma lintegral_bind
    {f : B → ENNReal} (hf : IsHom f)
    {g : A → PreProbabilityMeasure B} (hg : IsHom g)
    (μ : PreProbabilityMeasure A)
    : lintegral f (bind g μ) = lintegral (fun x ↦ lintegral f (g x)) μ := by
  simp only [lintegral, bind]
  rw [ProbabilityMeasure.lintegral_bind]
  · have : IsHom (g ∘ μ.eval) := by fun_prop
    congr 1
    ext r
    replace := sub_eq this r hf
    simp only [lintegral, Function.comp_apply] at this
    rw [this]
  · fun_prop
  · apply measurable_of_isHom
    fun_prop

@[gcongr]
lemma bind_congr
    {f : A → PreProbabilityMeasure B} (hf : IsHom f)
    {g : A → PreProbabilityMeasure B} (hg : IsHom g)
    (h₁ : ∀ x, f x ≈ g x)
    {μ ν : PreProbabilityMeasure A} (h₂ : μ ≈ ν)
    : bind f μ ≈ bind g ν := by
  intro k hk
  rw [lintegral_bind, lintegral_bind]
  · trans
    · apply h₂
      fun_prop
    · congr
      ext x
      apply h₁ x hk
  · exact hk
  · exact hg
  · exact hk
  · exact hf

namespace Var

/-- The monadic bind, lifted to variables. -/
noncomputable def bind (f : A → PreProbabilityMeasure B) (φ : Var A) : Var B where
  eval := subeval fun x ↦ f (φ.eval x)
  base := fun r ↦ (φ.base r).bind (subbase fun x ↦ f (φ.eval x))

lemma apply_bind {f : A → PreProbabilityMeasure B} (hf : IsHom f) (φ : Var A) (r : ℝ)
    : apply (bind f φ) r ≈ PreProbabilityMeasure.bind f (φ r) := by
  intro k hk
  simp only [bind, measureOf_mk, lintegral_mk]
  rw [lintegral_bind, ProbabilityMeasure.lintegral_bind]
  · congr 1
    ext x
    have : IsHom (fun x ↦ f (φ.eval x)) := by fun_prop
    simp only [sub_eq this x hk, lintegral_mk]
  · fun_prop
  · apply measurable_of_isHom
    fun_prop
  · fun_prop
  · fun_prop

end Var

@[fun_prop]
lemma isHom_bind {f : A → PreProbabilityMeasure B} (hf : IsHom f) : IsHom (bind f) := by
  rw [QuasiBorelSpace.isHom_def]
  simp only [isHom_def]
  intro φ ⟨ψ, hψ⟩
  use Var.bind f ψ
  intro r
  grw [Var.apply_bind, hψ]
  · fun_prop

/-- The functorial `str`ength operation. -/
def str (x : A) (μ : PreProbabilityMeasure B) : PreProbabilityMeasure (A × B) where
  eval := .mk fun r ↦ (x, μ.eval r)
  base := μ.base

@[simp]
lemma lintegral_str
    (k : A × B → ENNReal)
    (x : A) (μ : PreProbabilityMeasure B)
    : lintegral k (str x μ) = lintegral (fun y ↦ k (x, y)) μ := by
  simp only [lintegral, str, QuasiBorelHom.coe_mk]

@[gcongr]
lemma str_congr (x : A) {μ₁ μ₂ : PreProbabilityMeasure B} (hμ : μ₁ ≈ μ₂) : str x μ₁ ≈ str x μ₂ := by
  intro k hk
  simp only [lintegral_str]
  apply hμ
  fun_prop

namespace Var

/-- The functorial `str`ength operation, lifted to variables. -/
noncomputable def str {φ : ℝ → A} (hφ : IsHom φ) (ψ : Var B) : Var (A × B) where
  eval := .mk fun r ↦ (φ (unpack r : ℝ × ℝ).1, ψ.eval (unpack r : ℝ × ℝ).2)
  base r := (ψ r).base.map (f := fun x ↦ pack (r, x)) (by fun_prop)
  measurable_base := by
    apply Measurable.subtype_mk
    apply Measure.measurable_map'
    · fun_prop
    · apply Measurable.subtype_val
      fun_prop

lemma apply_str
    {φ : ℝ → A} (hφ : IsHom φ) (ψ : Var B) (r : ℝ)
    : apply (str hφ ψ) r ≈ PreProbabilityMeasure.str (φ r) (ψ r) := by
  intro χ hχ
  simp only [
    str, measureOf_mk, lintegral_mk, ProbabilityMeasure.toMeasure_map,
    QuasiBorelHom.coe_mk, lintegral_str]
  rw [MeasureTheory.lintegral_map]
  · rcases ψ
    simp only [measureOf_mk, unpack_pack, lintegral_mk]
  · apply measurable_of_isHom
    fun_prop
  · fun_prop

end Var

@[fun_prop, simp]
lemma isHom_str : IsHom (fun x : A × PreProbabilityMeasure B ↦ str x.1 x.2) := by
  rw [QuasiBorelSpace.isHom_def]
  simp only [Prod.isHom_iff, isHom_def, and_imp, forall_exists_index]
  intro φ hφ ψ hψ
  have : IsHom (fun x ↦ (φ x).1) := by fun_prop
  use Var.str this ψ
  intro r
  grw [Var.apply_str, hψ]

/-- The Bernoulli measure. -/
noncomputable def coin (p : I) : PreProbabilityMeasure Bool where
  eval := {
    toFun := fun r ↦ r = 0
    property := by
      apply Prop.isHom_decide
      simp only [isHom_ofMeasurableSpace]
      change Measurable fun x ↦ x ∈ ({0} : Set ℝ)
      simp only [measurable_mem, MeasurableSet.singleton]
  }
  base := {
    val :=
      ENNReal.ofReal p • Measure.dirac 0 +
      ENNReal.ofReal (σ p) • Measure.dirac 1
    property := by
      constructor
      rcases p with ⟨p, hp⟩
      simp only [Set.mem_Icc] at hp
      simp only [unitInterval.coe_symm_eq, hp, ENNReal.ofReal_sub, ENNReal.ofReal_one,
        Measure.coe_add, Measure.coe_smul, Pi.add_apply, Pi.smul_apply, measure_univ, smul_eq_mul,
        mul_one, ENNReal.ofReal_le_one, add_tsub_cancel_of_le]
  }

@[simp]
lemma lintegral_coin
    (k : Bool → ENNReal) (p : I)
    : lintegral k (coin p) = ENNReal.ofReal p * k true + ENNReal.ofReal (1 - p) * k false := by
  simp only [coin, unitInterval.coe_symm_eq, lintegral_mk, ProbabilityMeasure.coe_mk,
    QuasiBorelHom.coe_mk, lintegral_add_measure, lintegral_smul_measure, lintegral_dirac,
    decide_true, smul_eq_mul, one_ne_zero, decide_false]

end QuasiBorelSpace.PreProbabilityMeasure
