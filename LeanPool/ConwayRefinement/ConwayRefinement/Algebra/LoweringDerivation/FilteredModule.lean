/-
Copyright (c) 2026 Dan Abramov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dan Abramov
-/
module

public import LeanPool.ConwayRefinement.ConwayRefinement.Algebra.LoweringDerivation.Mu
public import Mathlib.LinearAlgebra.Basis.VectorSpace
public import Mathlib.LinearAlgebra.TensorProduct.Tower

import Mathlib.LinearAlgebra.TensorProduct.Finiteness
import Mathlib.RingTheory.TensorProduct.Free
import Mathlib.Algebra.BigOperators.Group.Finset.Preimage

/-!
# Freeness over the finite-degree part

Let `A` (Lean `R`) be a `NatOrdinal`-graded algebra over a field `E` with a lowering derivation
`∂` (Lean `Δ`), and let `A_{<ω} = ⨁_{n < ω} A_n` be its finite-degree part. For a graded
`E`-linear section `s : A/I → A` of the quotient map `π`, the `A_{<ω}`-linear map

`μ_s : A_{<ω} ⊗_E A/I → A`, `B ⊗ C ↦ B s(C)`,

is bijective and carries `(A_{<ω})_{≥j} ⊗_E A/I` onto `I_{≥j}` for every `j`:

* injectivity: writing a kernel element as a sum of pieces in the `A_n ⊗ A/I`, the piece of least
  degree `d` gives a relation in the kernel of `μ_d`, which is injective;
* surjectivity onto `I_{≥j}`: a homogeneous element of `I_{≥j}` is, modulo `I_{≥j+1}`, the image
  of a tensor in `A_j ⊗ A/I`, and `I_{≥j} ∩ A_δ = 0` once `j` exceeds the finite part of `δ`.

In particular `A` is a free `A_{<ω}`-module. A homogeneous `E`-basis `𝓒` of `A/I` (through the
grading of `A/I`) with homogeneous lifts `s(C)` of its vectors determines such a graded section,
and the lifts `s(C)`, `C ∈ 𝓒`, form the basis of `A` over `A_{<ω}` corresponding under `μ_s` to
the basis `1 ⊗ C` of `A_{<ω} ⊗_E A/I`.
-/

universe u v

open scoped DirectSum TensorProduct

public noncomputable section

namespace LoweringDerivation

variable {E : Type u} {R : Type v} [Field E] [CommRing R] [Algebra E R]
variable (𝒜 : NatOrdinal → Submodule E R) [GradedAlgebra 𝒜]

/-! ### The finite-degree part `A_{<ω}` -/

/-- The submodule `⨁_{n < ω} A_n` spanned by the finite degrees. -/
def finiteDegreeSubmodule : Submodule E R := ⨆ n : ℕ, 𝒜 (n : NatOrdinal)

omit [GradedAlgebra 𝒜] in
theorem mem_finiteDegreeSubmodule_of_mem {n : ℕ} {x : R} (hx : x ∈ 𝒜 (n : NatOrdinal)) :
    x ∈ finiteDegreeSubmodule 𝒜 :=
  Submodule.mem_iSup_of_mem n hx

omit [GradedAlgebra 𝒜] in
theorem finiteDegreeSubmodule_induction {p : (x : R) → x ∈ finiteDegreeSubmodule 𝒜 → Prop}
    (mem : ∀ (n : ℕ) (x) (hx : x ∈ 𝒜 (n : NatOrdinal)), p x (mem_finiteDegreeSubmodule_of_mem 𝒜 hx))
    (zero : p 0 (zero_mem _))
    (add : ∀ x y hx hy, p x hx → p y hy → p (x + y) (add_mem hx hy))
    {x : R} (hx : x ∈ finiteDegreeSubmodule 𝒜) : p x hx :=
  Submodule.iSup_induction' (motive := p) _ mem zero add hx

/-- Membership in `⨁_{n < ω} A_n`: every non-zero homogeneous component has finite degree. -/
theorem mem_finiteDegreeSubmodule_iff (x : R) :
    x ∈ finiteDegreeSubmodule 𝒜 ↔
      ∀ α, (DirectSum.decompose 𝒜 x α : R) ≠ 0 → ∃ n : ℕ, α = n := by
  constructor
  · intro hx
    refine finiteDegreeSubmodule_induction 𝒜 (p := fun x _ ↦ ∀ α,
      (DirectSum.decompose 𝒜 x α : R) ≠ 0 → ∃ n : ℕ, α = n) ?_ ?_ ?_ hx
    · intro n y hy α hα
      by_contra hne
      exact hα (DirectSum.decompose_of_mem_ne 𝒜 hy fun h ↦ hne ⟨n, h.symm⟩)
    · intro α hα
      exact absurd (by rw [DirectSum.decompose_zero]; rfl) hα
    · intro y z _ _ hy hz α hα
      by_contra hne
      apply hα
      rw [DirectSum.decompose_add, DirectSum.add_apply, Submodule.coe_add]
      have h1 : (DirectSum.decompose 𝒜 y α : R) = 0 := by
        by_contra h; exact hne (hy α h)
      have h2 : (DirectSum.decompose 𝒜 z α : R) = 0 := by
        by_contra h; exact hne (hz α h)
      rw [h1, h2, add_zero]
  · intro hx
    classical
    rw [← DirectSum.sum_support_decompose 𝒜 x]
    refine Submodule.sum_mem _ fun α hα ↦ ?_
    obtain ⟨n, rfl⟩ := hx α (by
      intro h
      exact (DFinsupp.mem_support_iff.mp hα) (Subtype.ext h))
    exact mem_finiteDegreeSubmodule_of_mem 𝒜 (DirectSum.decompose 𝒜 x (n : NatOrdinal)).2

/-- The finite-degree part `A_{<ω} = ⨁_{n < ω} A_n`, a subalgebra of `A` since `m ⊕ n = m + n` for
finite `m, n`. -/
def finiteDegreePart : Subalgebra E R where
  carrier := finiteDegreeSubmodule 𝒜
  add_mem' := add_mem
  zero_mem' := zero_mem _
  algebraMap_mem' r := mem_finiteDegreeSubmodule_of_mem 𝒜 (n := 0) (by
    rw [Nat.cast_zero]
    exact SetLike.algebraMap_mem_graded 𝒜 r)
  mul_mem' {x y} hx hy := by
    refine finiteDegreeSubmodule_induction 𝒜 (p := fun x _ ↦ x * y ∈ finiteDegreeSubmodule 𝒜)
      ?_ ?_ ?_ hx
    · intro m a ha
      refine finiteDegreeSubmodule_induction 𝒜 (p := fun y _ ↦ a * y ∈ finiteDegreeSubmodule 𝒜)
        ?_ ?_ ?_ hy
      · intro n b hb
        exact mem_finiteDegreeSubmodule_of_mem 𝒜 (n := m + n)
          (by rw [Nat.cast_add]; exact SetLike.mul_mem_graded ha hb)
      · rw [mul_zero]; exact zero_mem _
      · intro b c _ _ hb hc
        rw [mul_add]; exact add_mem hb hc
    · rw [zero_mul]; exact zero_mem _
    · intro a b _ _ ha hb
      rw [add_mul]; exact add_mem ha hb

theorem mem_finiteDegreePart_iff (x : R) :
    x ∈ finiteDegreePart 𝒜 ↔ x ∈ finiteDegreeSubmodule 𝒜 := Iff.rfl

theorem mem_finiteDegreePart_of_mem {n : ℕ} {x : R} (hx : x ∈ 𝒜 (n : NatOrdinal)) :
    x ∈ finiteDegreePart 𝒜 :=
  mem_finiteDegreeSubmodule_of_mem 𝒜 hx

/-- The degree-`n` component of an element of `A_{<ω}`. -/
def finiteDegreeComponent (n : ℕ) (a : finiteDegreePart 𝒜) : 𝒜 (n : NatOrdinal) :=
  DirectSum.decompose 𝒜 (a : R) (n : NatOrdinal)

theorem coe_finiteDegreeComponent (n : ℕ) (a : finiteDegreePart 𝒜) :
    (finiteDegreeComponent 𝒜 n a : R) = DirectSum.decompose 𝒜 (a : R) (n : NatOrdinal) := (rfl)

theorem finiteDegreeComponent_add (n : ℕ) (a b : finiteDegreePart 𝒜) :
    finiteDegreeComponent 𝒜 n (a + b) =
      finiteDegreeComponent 𝒜 n a + finiteDegreeComponent 𝒜 n b := by
  simp only [finiteDegreeComponent, Subalgebra.coe_add, DirectSum.decompose_add,
    DirectSum.add_apply]

theorem finiteDegreeComponent_mem_idealGE (n : ℕ) (a : finiteDegreePart 𝒜) :
    (finiteDegreeComponent 𝒜 n a : R) ∈ idealGE 𝒜 n :=
  mem_idealGE_of_mem 𝒜 le_rfl (finiteDegreeComponent 𝒜 n a).2

/-- The finite degrees at which an element of `A_{<ω}` has a non-zero component. -/
def finiteDegreeSupport (a : finiteDegreePart 𝒜) : Finset ℕ := by
  classical
  exact (DirectSum.decompose 𝒜 (a : R)).support.preimage Nat.cast
    (Nat.cast_injective.injOn)

theorem mem_finiteDegreeSupport_iff (a : finiteDegreePart 𝒜) (n : ℕ) :
    n ∈ finiteDegreeSupport 𝒜 a ↔ finiteDegreeComponent 𝒜 n a ≠ 0 := by
  classical
  rw [finiteDegreeSupport, Finset.mem_preimage, DFinsupp.mem_support_iff]
  rfl

/-- An element of `A_{<ω}` is the sum of its homogeneous components. -/
theorem sum_finiteDegreeComponent (a : finiteDegreePart 𝒜) :
    ∑ n ∈ finiteDegreeSupport 𝒜 a, (finiteDegreeComponent 𝒜 n a : R) = a := by
  classical
  conv_rhs => rw [← DirectSum.sum_support_decompose 𝒜 (a : R)]
  rw [finiteDegreeSupport]
  refine Finset.sum_preimage (Nat.cast : ℕ → NatOrdinal) _ _
    (fun α ↦ (DirectSum.decompose 𝒜 (a : R) α : R)) ?_
  intro α hα hnot
  exfalso
  obtain ⟨n, rfl⟩ := (mem_finiteDegreeSubmodule_iff 𝒜 a).mp a.2 α
    (fun h ↦ (DFinsupp.mem_support_iff.mp hα) (Subtype.ext h))
  exact hnot ⟨n, rfl⟩

theorem sum_finiteDegreeComponent_of_subset (a : finiteDegreePart 𝒜) {t : Finset ℕ}
    (ht : finiteDegreeSupport 𝒜 a ⊆ t) :
    ∑ n ∈ t, (finiteDegreeComponent 𝒜 n a : R) = a := by
  rw [← sum_finiteDegreeComponent 𝒜 a]
  symm
  refine Finset.sum_subset ht fun n _ hn ↦ ?_
  rw [mem_finiteDegreeSupport_iff, not_not] at hn
  rw [hn, Submodule.coe_zero]

theorem eq_zero_of_finiteDegreeComponent_eq_zero {a : finiteDegreePart 𝒜}
    (h : ∀ n, finiteDegreeComponent 𝒜 n a = 0) : a = 0 := by
  apply Subtype.ext
  rw [← sum_finiteDegreeComponent 𝒜 a]
  simp [h]

theorem finiteDegreeComponent_eq_self {n : ℕ} (a : finiteDegreePart 𝒜)
    (ha : (a : R) ∈ 𝒜 (n : NatOrdinal)) : (finiteDegreeComponent 𝒜 n a : R) = a :=
  DirectSum.decompose_of_mem_same 𝒜 ha

theorem finiteDegreeComponent_eq_zero_of_ne {m n : ℕ} (a : finiteDegreePart 𝒜)
    (ha : (a : R) ∈ 𝒜 (m : NatOrdinal)) (h : m ≠ n) : (finiteDegreeComponent 𝒜 n a : R) = 0 :=
  DirectSum.decompose_of_mem_ne 𝒜 ha (by exact_mod_cast h)

/-- The inclusion `A_j → A_{<ω}`. -/
def natInclusion (j : ℕ) : 𝒜 (j : NatOrdinal) →ₗ[E] finiteDegreePart 𝒜 where
  toFun a := ⟨a, mem_finiteDegreePart_of_mem 𝒜 a.2⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem coe_natInclusion (j : ℕ) (a : 𝒜 (j : NatOrdinal)) :
    (natInclusion 𝒜 j a : R) = a := (rfl)

/-- An element of `A_{<ω}` is the sum of its homogeneous components, in `A_{<ω}`. -/
theorem sum_natInclusion_finiteDegreeComponent (a : finiteDegreePart 𝒜) {t : Finset ℕ}
    (ht : finiteDegreeSupport 𝒜 a ⊆ t) :
    ∑ n ∈ t, natInclusion 𝒜 n (finiteDegreeComponent 𝒜 n a) = a := by
  apply Subtype.ext
  rw [AddSubmonoidClass.coe_finsetSum]
  simp only [coe_natInclusion]
  exact sum_finiteDegreeComponent_of_subset 𝒜 a ht

/-! ### A homogeneous basis `𝓒` of `A/I` and its homogeneous lifts -/

/-- The index type of the chosen homogeneous basis `𝓒` of `A/I`: a degree `β` together with a
basis index of `(A/I)_β`. -/
abbrev QuotientBasisIndex :=
  Σ β : NatOrdinal, Module.Basis.ofVectorSpaceIndex E (fibreGrade 𝒜 β)

/-- The degree of a basis index. -/
abbrev quotientBasisDegree (i : QuotientBasisIndex 𝒜) : NatOrdinal := i.1

/-- A chosen homogeneous `E`-basis `𝓒` of `A/I`. -/
def fibreBasis : Module.Basis (QuotientBasisIndex 𝒜) E (Fibre 𝒜) :=
  (fibreGrade_isInternal 𝒜).collectedBasis fun β ↦ Module.Basis.ofVectorSpace E (fibreGrade 𝒜 β)

theorem fibreBasis_mem (i : QuotientBasisIndex 𝒜) :
    fibreBasis 𝒜 i ∈ fibreGrade 𝒜 (quotientBasisDegree 𝒜 i) :=
  (fibreGrade_isInternal 𝒜).collectedBasis_mem _ i

/-- The expansion in `𝓒` of a homogeneous element of `A/I` involves only basis vectors of its
degree. -/
theorem fibreBasis_repr_eq_zero {β : NatOrdinal} {c : Fibre 𝒜} (hc : c ∈ fibreGrade 𝒜 β)
    (i : QuotientBasisIndex 𝒜) (hi : quotientBasisDegree 𝒜 i ≠ β) : (fibreBasis 𝒜).repr c i = 0 :=
  (fibreGrade_isInternal 𝒜).collectedBasis_repr_of_mem_ne _ (Ne.symm hi) hc

/-- A chosen homogeneous lift `s(C) ∈ A` of each basis vector `C ∈ 𝓒`. -/
def quotientBasisLift (i : QuotientBasisIndex 𝒜) : R :=
  (exists_mem_of_mem_fibreGrade 𝒜 (fibreBasis_mem 𝒜 i)).choose

theorem quotientBasisLift_mem (i : QuotientBasisIndex 𝒜) : quotientBasisLift 𝒜 i ∈ 𝒜
    (quotientBasisDegree 𝒜 i) :=
  (exists_mem_of_mem_fibreGrade 𝒜 (fibreBasis_mem 𝒜 i)).choose_spec.1

theorem fibreMap_quotientBasisLift (i : QuotientBasisIndex 𝒜) : fibreMap 𝒜 (quotientBasisLift 𝒜 i) =
    fibreBasis 𝒜 i :=
  (exists_mem_of_mem_fibreGrade 𝒜 (fibreBasis_mem 𝒜 i)).choose_spec.2

theorem quotientBasisLift_ne_zero (i : QuotientBasisIndex 𝒜) : quotientBasisLift 𝒜 i ≠ 0 := fun h ↦
  (fibreBasis 𝒜).ne_zero i (by rw [← fibreMap_quotientBasisLift, h, map_zero])

/-- The graded `E`-linear section `s : A/I → A` of `π` sending each `C ∈ 𝓒` to its chosen lift
`s(C)`. -/
def fibreSection : Fibre 𝒜 →ₗ[E] R := (fibreBasis 𝒜).constr E (quotientBasisLift 𝒜)

theorem fibreSection_basis (i : QuotientBasisIndex 𝒜) :
    fibreSection 𝒜 (fibreBasis 𝒜 i) = quotientBasisLift 𝒜 i :=
  (fibreBasis 𝒜).constr_basis E _ i

theorem fibreMap_fibreSection (c : Fibre 𝒜) : fibreMap 𝒜 (fibreSection 𝒜 c) = c := by
  have h : (fibreMap 𝒜).toLinearMap ∘ₗ fibreSection 𝒜 = LinearMap.id :=
    (fibreBasis 𝒜).ext fun i ↦ by
      rw [LinearMap.comp_apply, fibreSection_basis, AlgHom.toLinearMap_apply,
          fibreMap_quotientBasisLift,
        LinearMap.id_apply]
  exact LinearMap.congr_fun h c

/-- The section `s` is graded: `s((A/I)_β) ⊆ A_β`. -/
theorem fibreSection_mem {β : NatOrdinal} {c : Fibre 𝒜} (hc : c ∈ fibreGrade 𝒜 β) :
    fibreSection 𝒜 c ∈ 𝒜 β := by
  rw [fibreSection, Module.Basis.constr_apply, Finsupp.sum]
  refine Submodule.sum_mem _ fun i hi ↦ Submodule.smul_mem _ _ ?_
  have hgrade : quotientBasisDegree 𝒜 i = β := by
    by_contra hne
    exact (Finsupp.mem_support_iff.mp hi) (fibreBasis_repr_eq_zero 𝒜 hc i hne)
  rw [← hgrade]
  exact quotientBasisLift_mem 𝒜 i

/-! ### The filtered `A_{<ω}`-module `A` -/

/-- A graded `E`-linear section `s : A/I → A` of the quotient map `π`: `π ∘ s = id` and `s`
carries `(A/I)_β` into `A_β`. -/
structure IsGradedFibreSection (s : Fibre 𝒜 →ₗ[E] R) : Prop where
  /-- `π ∘ s = id`. -/
  fibreMap_apply : ∀ c, fibreMap 𝒜 (s c) = c
  /-- `s` is graded. -/
  mem : ∀ {β : NatOrdinal} {c : Fibre 𝒜}, c ∈ fibreGrade 𝒜 β → s c ∈ 𝒜 β

/-- The chosen section `fibreSection` is a graded section of `π`. -/
theorem fibreSection_isGradedFibreSection : IsGradedFibreSection 𝒜 (fibreSection 𝒜) where
  fibreMap_apply := fibreMap_fibreSection 𝒜
  mem := fibreSection_mem 𝒜

/-- The paper's `μ_s : A_{<ω} ⊗_E A/I → A`, `B ⊗ C ↦ B s(C)`, as an `A_{<ω}`-linear map. -/
def muOfSection (s : Fibre 𝒜 →ₗ[E] R) :
    finiteDegreePart 𝒜 ⊗[E] Fibre 𝒜 →ₗ[finiteDegreePart 𝒜] R :=
  TensorProduct.AlgebraTensorModule.lift
    (LinearMap.toSpanSingleton (finiteDegreePart 𝒜) (Fibre 𝒜 →ₗ[E] R) s)

theorem muOfSection_tmul (s : Fibre 𝒜 →ₗ[E] R) (a : finiteDegreePart 𝒜) (c : Fibre 𝒜) :
    muOfSection 𝒜 s (a ⊗ₜ[E] c) = (a : R) * s c := by
  rw [muOfSection, TensorProduct.AlgebraTensorModule.lift_tmul,
    LinearMap.toSpanSingleton_apply, LinearMap.smul_apply, Subalgebra.smul_def, smul_eq_mul]

/-- The restriction of `μ_s` to `A_j ⊗ A/I`, `B ⊗ C ↦ B s(C)`. -/
def gradeSectionMul (s : Fibre 𝒜 →ₗ[E] R) (j : ℕ) : 𝒜 (j : NatOrdinal) ⊗[E] Fibre 𝒜 →ₗ[E] R :=
  TensorProduct.lift ((LinearMap.mul E R).compl₁₂ (𝒜 (j : NatOrdinal)).subtype s)

omit [GradedAlgebra 𝒜] in
theorem gradeSectionMul_tmul (s : Fibre 𝒜 →ₗ[E] R) (j : ℕ) (a : 𝒜 (j : NatOrdinal))
    (c : Fibre 𝒜) : gradeSectionMul 𝒜 s j (a ⊗ₜ[E] c) = (a : R) * s c := by
  rw [gradeSectionMul, TensorProduct.lift.tmul]
  rfl

theorem muOfSection_rTensor_natInclusion (s : Fibre 𝒜 →ₗ[E] R) (j : ℕ)
    (T : 𝒜 (j : NatOrdinal) ⊗[E] Fibre 𝒜) :
    muOfSection 𝒜 s ((natInclusion 𝒜 j).rTensor _ T) = gradeSectionMul 𝒜 s j T := by
  induction T with
  | zero => rw [map_zero, map_zero, map_zero]
  | tmul a c =>
    rw [LinearMap.rTensor_tmul, muOfSection_tmul, gradeSectionMul_tmul, coe_natInclusion]
  | add x y hx hy => rw [map_add, map_add, hx, hy, map_add]

omit [GradedAlgebra 𝒜] in
theorem gradeSectionMul_mem_idealGE (s : Fibre 𝒜 →ₗ[E] R) (j : ℕ)
    (T : 𝒜 (j : NatOrdinal) ⊗[E] Fibre 𝒜) : gradeSectionMul 𝒜 s j T ∈ idealGE 𝒜 j := by
  induction T with
  | zero => rw [map_zero]; exact zero_mem _
  | tmul a c =>
    rw [gradeSectionMul_tmul]
    exact Ideal.mul_mem_right _ _ (mem_idealGE_of_mem 𝒜 le_rfl a.2)
  | add x y hx hy => rw [map_add]; exact add_mem hx hy

/-- For a section `s` of `π`, `μ_s(T)` represents `μ_j(T)`: its class modulo `I_{≥j+1}` is
`μ_j(T)`. -/
theorem mk_gradeSectionMul {s : Fibre 𝒜 →ₗ[E] R} (hs : IsGradedFibreSection 𝒜 s) (j : ℕ)
    (T : 𝒜 (j : NatOrdinal) ⊗[E] Fibre 𝒜) :
    (Submodule.Quotient.mk (gradeSectionMul 𝒜 s j T) : R ⧸ idealGE 𝒜 (j + 1)) =
      mu 𝒜 j T := by
  induction T with
  | zero => rw [map_zero, map_zero, Submodule.Quotient.mk_zero]
  | tmul a c =>
    rw [gradeSectionMul_tmul, ← hs.fibreMap_apply c, mu_tmul, hs.fibreMap_apply]
  | add x y hx hy => rw [map_add, map_add, Submodule.Quotient.mk_add, hx, hy]

/-- For a graded section, `μ_s` carries `A_j ⊗ (A/I)_β` into `A_{j ⊕ β}`. -/
theorem gradeSectionMul_lTensor_mem {s : Fibre 𝒜 →ₗ[E] R} (hs : IsGradedFibreSection 𝒜 s)
    (j : ℕ) (β : NatOrdinal) (T : 𝒜 (j : NatOrdinal) ⊗[E] fibreGrade 𝒜 β) :
    gradeSectionMul 𝒜 s j ((fibreGrade 𝒜 β).subtype.lTensor _ T) ∈ 𝒜 ((j : NatOrdinal) + β) := by
  induction T with
  | zero => rw [map_zero, map_zero]; exact zero_mem _
  | tmul a c =>
    rw [LinearMap.lTensor_tmul, gradeSectionMul_tmul, Submodule.subtype_apply]
    exact SetLike.mul_mem_graded a.2 (hs.mem c.2)
  | add x y hx hy => rw [map_add, map_add]; exact add_mem hx hy

/-- The submodule `(A_{<ω})_{≥j} ⊗_E A/I = ∑_{n ≥ j} A_n ⊗ A/I` of `A_{<ω} ⊗_E A/I`. -/
def tensorIdealGEFiltration (j : ℕ) : Submodule E (finiteDegreePart 𝒜 ⊗[E] Fibre 𝒜) :=
  ⨆ (e : ℕ) (_ : j ≤ e), LinearMap.range ((natInclusion 𝒜 e).rTensor (Fibre 𝒜))

theorem rTensor_natInclusion_mem_tensorIdealGEFiltration {j e : ℕ} (hje : j ≤ e)
    (T : 𝒜 (e : NatOrdinal) ⊗[E] Fibre 𝒜) :
    (natInclusion 𝒜 e).rTensor _ T ∈ tensorIdealGEFiltration 𝒜 j :=
  Submodule.mem_iSup_of_mem e (Submodule.mem_iSup_of_mem hje ⟨T, rfl⟩)

theorem tensorIdealGEFiltration_antitone {i j : ℕ} (hij : i ≤ j) :
    tensorIdealGEFiltration 𝒜 j ≤ tensorIdealGEFiltration 𝒜 i :=
  iSup₂_le fun e hje ↦ le_iSup₂_of_le e (hij.trans hje) le_rfl

/-- `μ_s` carries `(A_{<ω})_{≥j} ⊗_E A/I` into `I_{≥j}`. -/
theorem muOfSection_mem_idealGE (s : Fibre 𝒜 →ₗ[E] R) {j : ℕ}
    {u : finiteDegreePart 𝒜 ⊗[E] Fibre 𝒜} (hu : u ∈ tensorIdealGEFiltration 𝒜 j) :
    muOfSection 𝒜 s u ∈ idealGE 𝒜 j := by
  have hle : tensorIdealGEFiltration 𝒜 j ≤
      ((idealGE 𝒜 j).restrictScalars E).comap ((muOfSection 𝒜 s).restrictScalars E) := by
    refine iSup₂_le fun e hje ↦ ?_
    rintro _ ⟨T, rfl⟩
    rw [Submodule.mem_comap, LinearMap.restrictScalars_apply, Submodule.restrictScalars_mem,
      muOfSection_rTensor_natInclusion]
    exact idealGE_antitone 𝒜 hje (gradeSectionMul_mem_idealGE 𝒜 s e T)
  exact hle hu

/-- Every homogeneous element of `I_{≥j}` lies in `μ_s((A_{<ω})_{≥j} ⊗_E A/I)`: descending
induction on `j`, using the surjectivity of `μ_j` and the vanishing `I_{≥j} ∩ A_δ = 0` for `j`
beyond the finite part of `δ`. -/
theorem mem_map_tensorIdealGEFiltration_of_mem_idealGE {s : Fibre 𝒜 →ₗ[E] R}
    (hs : IsGradedFibreSection 𝒜 s) {δ : NatOrdinal} (d : ℕ) :
    ∀ j : ℕ, δ.constantCoeff + 1 ≤ j + d → ∀ H ∈ 𝒜 δ, H ∈ idealGE 𝒜 j →
      H ∈ (tensorIdealGEFiltration 𝒜 j).map ((muOfSection 𝒜 s).restrictScalars E) := by
  induction d with
  | zero =>
    intro j hj H hHδ hH
    rw [eq_zero_of_mem_idealGE_of_constantCoeff_lt 𝒜 hHδ hH (by omega)]
    exact zero_mem _
  | succ d ih =>
    intro j hj H hHδ hH
    by_cases hjδ : δ.constantCoeff < j
    · rw [eq_zero_of_mem_idealGE_of_constantCoeff_lt 𝒜 hHδ hH hjδ]
      exact zero_mem _
    obtain ⟨T, hT⟩ := exists_mu_lTensor_eq 𝒜 hHδ hH
    set G := gradeSectionMul 𝒜 s j ((fibreGrade 𝒜 (δ.removeNat j)).subtype.lTensor _ T) with hG
    have hsum : (j : NatOrdinal) + δ.removeNat j = δ := by
      rw [add_comm]
      exact NatOrdinal.removeNat_add_natCast (by omega)
    have hGδ : G ∈ 𝒜 δ := hsum ▸ gradeSectionMul_lTensor_mem 𝒜 hs j _ T
    have hdiff : H - G ∈ idealGE 𝒜 (j + 1) := by
      rw [← mk_gradeSectionMul 𝒜 hs] at hT
      exact (Submodule.Quotient.eq _).mp hT.symm
    have h1 := ih (j + 1) (by omega) _ (sub_mem hHδ hGδ) hdiff
    have h2 : G ∈ (tensorIdealGEFiltration 𝒜 j).map ((muOfSection 𝒜 s).restrictScalars E) :=
      ⟨_, rTensor_natInclusion_mem_tensorIdealGEFiltration 𝒜 le_rfl _,
        by rw [LinearMap.restrictScalars_apply, muOfSection_rTensor_natInclusion]⟩
    have h1' := Submodule.map_mono (tensorIdealGEFiltration_antitone 𝒜 (Nat.le_succ j)) h1
    simpa using add_mem h1' h2

/-- `μ_s` carries `(A_{<ω})_{≥j} ⊗_E A/I` onto `I_{≥j}`. -/
theorem map_tensorIdealGEFiltration {s : Fibre 𝒜 →ₗ[E] R} (hs : IsGradedFibreSection 𝒜 s)
    (j : ℕ) :
    (tensorIdealGEFiltration 𝒜 j).map ((muOfSection 𝒜 s).restrictScalars E) =
      (idealGE 𝒜 j).restrictScalars E := by
  classical
  apply le_antisymm
  · rintro _ ⟨u, hu, rfl⟩
    rw [LinearMap.restrictScalars_apply, Submodule.restrictScalars_mem]
    exact muOfSection_mem_idealGE 𝒜 s hu
  · intro H hH
    rw [Submodule.restrictScalars_mem] at hH
    rw [← DirectSum.sum_support_decompose 𝒜 H]
    refine Submodule.sum_mem _ fun δ _ ↦ ?_
    exact mem_map_tensorIdealGEFiltration_of_mem_idealGE 𝒜 hs (δ.constantCoeff + 1) j
      (by omega) _ (DirectSum.decompose 𝒜 H δ).2 (idealGE_isHomogeneous 𝒜 j δ hH)

/-- Every tensor in `A_{<ω} ⊗_E A/I` is a finite sum of pieces `(ι_n ⊗ 1) t_n` with
`t_n ∈ A_n ⊗ A/I`, `ι_n : A_n → A_{<ω}` the inclusion. -/
theorem exists_eq_sum_rTensor_natInclusion (u : finiteDegreePart 𝒜 ⊗[E] Fibre 𝒜) :
    ∃ (N : Finset ℕ) (t : ∀ n : ℕ, 𝒜 (n : NatOrdinal) ⊗[E] Fibre 𝒜),
      u = ∑ n ∈ N, (natInclusion 𝒜 n).rTensor _ (t n) := by
  classical
  obtain ⟨P, rfl⟩ := TensorProduct.exists_finset u
  refine ⟨P.biUnion fun p ↦ finiteDegreeSupport 𝒜 p.1,
    fun n ↦ ∑ p ∈ P, finiteDegreeComponent 𝒜 n p.1 ⊗ₜ[E] p.2,
    ?_⟩
  have : ∀ p ∈ P, p.1 ⊗ₜ[E] p.2 = ∑ n ∈ P.biUnion fun p ↦ finiteDegreeSupport 𝒜 p.1,
      natInclusion 𝒜 n (finiteDegreeComponent 𝒜 n p.1) ⊗ₜ[E] p.2 := fun p hp ↦ by
    rw [← TensorProduct.sum_tmul, sum_natInclusion_finiteDegreeComponent 𝒜 p.1
      fun n hn ↦ Finset.mem_biUnion.mpr ⟨p, hp, hn⟩]
  rw [Finset.sum_congr rfl this, Finset.sum_comm]
  exact Finset.sum_congr rfl fun n _ ↦ by simp only [map_sum, LinearMap.rTensor_tmul]

/-- `μ_s` is injective: in a kernel element, the piece of least finite degree `d` gives a
relation in the kernel of `μ_d`. -/
theorem muOfSection_injective (h0 : GradeZeroScalars 𝒜) {Δ : R →ₗ[E] FunAtZeroMinus R}
    (hΔ : IsLoweringDerivation 𝒜 Δ) {s : Fibre 𝒜 →ₗ[E] R} (hs : IsGradedFibreSection 𝒜 s) :
    Function.Injective (muOfSection 𝒜 s) := by
  classical
  rw [injective_iff_map_eq_zero]
  intro u hu
  obtain ⟨N, t, rfl⟩ := exists_eq_sum_rTensor_natInclusion 𝒜 u
  by_contra hne
  -- a least finite degree `d` with a non-zero piece
  have hex : ∃ n ∈ N, t n ≠ 0 := by
    by_contra hall
    push Not at hall
    exact hne (Finset.sum_eq_zero fun n hn ↦ by rw [hall n hn, map_zero])
  obtain ⟨d, hdN, hdmin⟩ := (N.filter fun n ↦ t n ≠ 0).exists_min_image id
    (by obtain ⟨n, hn, hn'⟩ := hex; exact ⟨n, Finset.mem_filter.mpr ⟨hn, hn'⟩⟩)
  simp only [id, Finset.mem_filter] at hdmin
  obtain ⟨hdN', hd0⟩ := Finset.mem_filter.mp hdN
  -- the remaining pieces lie in `I_{≥d+1}`
  have hrest : ∑ n ∈ N.erase d, gradeSectionMul 𝒜 s n (t n) ∈ idealGE 𝒜 (d + 1) := by
    refine Submodule.sum_mem _ fun n hn ↦ ?_
    by_cases hn0 : t n = 0
    · rw [hn0, map_zero]; exact zero_mem _
    · have hdn : d < n := lt_of_le_of_ne (hdmin n ⟨Finset.mem_of_mem_erase hn, hn0⟩)
        (Finset.ne_of_mem_erase hn).symm
      exact idealGE_antitone 𝒜 hdn (gradeSectionMul_mem_idealGE 𝒜 s n (t n))
  have hlead : gradeSectionMul 𝒜 s d (t d) ∈ idealGE 𝒜 (d + 1) := by
    have hsum : ∑ n ∈ N, gradeSectionMul 𝒜 s n (t n) = 0 := by
      rw [← hu, map_sum]
      exact Finset.sum_congr rfl fun n _ ↦ (muOfSection_rTensor_natInclusion 𝒜 s n _).symm
    rw [← Finset.add_sum_erase N _ hdN'] at hsum
    rw [eq_neg_of_add_eq_zero_left hsum]
    exact neg_mem hrest
  have hchar : mu 𝒜 d (t d) = 0 := by
    rw [← mk_gradeSectionMul 𝒜 hs, Submodule.Quotient.mk_eq_zero]
    exact hlead
  exact hd0 ((injective_iff_map_eq_zero _).mp (hΔ.mu_injective h0 d) _ hchar)

/-- `μ_s` is bijective for every graded section `s` of `π`. -/
theorem muOfSection_bijective (h0 : GradeZeroScalars 𝒜) {Δ : R →ₗ[E] FunAtZeroMinus R}
    (hΔ : IsLoweringDerivation 𝒜 Δ) {s : Fibre 𝒜 →ₗ[E] R} (hs : IsGradedFibreSection 𝒜 s) :
    Function.Bijective (muOfSection 𝒜 s) := by
  refine ⟨muOfSection_injective 𝒜 h0 hΔ hs, fun y ↦ ?_⟩
  have hy : y ∈ (idealGE 𝒜 0).restrictScalars E := by
    rw [Submodule.restrictScalars_mem, idealGE_zero]
    exact Submodule.mem_top
  rw [← map_tensorIdealGEFiltration 𝒜 hs 0] at hy
  obtain ⟨u, -, hu⟩ := hy
  exact ⟨u, hu⟩

/-! ### The basis of `A` over `A_{<ω}` -/

/-- The chosen homogeneous lifts `s(C)`, `C ∈ 𝓒`, form a basis of `A` over `A_{<ω}`: the image
under `μ_s`, for the section `s = fibreSection`, of the basis `1 ⊗ C` of `A_{<ω} ⊗_E A/I` over
`A_{<ω}`. -/
def basisOverFiniteDegreePart (h0 : GradeZeroScalars 𝒜) {Δ : R →ₗ[E] FunAtZeroMinus R}
    (hΔ : IsLoweringDerivation 𝒜 Δ) :
    Module.Basis (QuotientBasisIndex 𝒜) (finiteDegreePart 𝒜) R :=
  (Algebra.TensorProduct.basis (finiteDegreePart 𝒜) (fibreBasis 𝒜)).map
    (LinearEquiv.ofBijective (muOfSection 𝒜 (fibreSection 𝒜))
      (muOfSection_bijective 𝒜 h0 hΔ (fibreSection_isGradedFibreSection 𝒜)))

theorem basisOverFiniteDegreePart_apply (h0 : GradeZeroScalars 𝒜) {Δ : R →ₗ[E] FunAtZeroMinus R}
    (hΔ : IsLoweringDerivation 𝒜 Δ) (i : QuotientBasisIndex 𝒜) :
    basisOverFiniteDegreePart 𝒜 h0 hΔ i = quotientBasisLift 𝒜 i := by
  rw [basisOverFiniteDegreePart, Module.Basis.map_apply, Algebra.TensorProduct.basis_apply,
    LinearEquiv.ofBijective_apply, muOfSection_tmul, OneMemClass.coe_one, one_mul,
    fibreSection_basis]

end LoweringDerivation
