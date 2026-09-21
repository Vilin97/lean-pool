/-
Copyright (c) 2026 Dan Abramov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dan Abramov
-/
module

public import LeanPool.ConwayRefinement.ConwayRefinement.Algebra.LoweringDerivation.FilteredModule
public import LeanPool.ConwayRefinement.ConwayRefinement.Algebra.Valuation.FiltrationDegree
public import Mathlib.RingTheory.TensorProduct.Basic

import LeanPool.ConwayRefinement.ConwayRefinement.Algebra.Valuation.BasisOver

/-!
# The associated graded ring `gr_{I_•} A`

The ideals `I_{≥j}` of a `NatOrdinal`-graded algebra `A` (Lean `R`) with a lowering derivation
form a decreasing multiplicative filtration which is separated, so it defines a max-additive
degree valued in `ℕᵒᵈ` and an associated graded ring `gr_{I_•} A = ⨁_j I_{≥j}/I_{≥j+1}`. The
finite-degree part `A_{<ω}` maps to `gr_{I_•} A` by sending a homogeneous element of degree
`j < ω` to its class in `I_{≥j}/I_{≥j+1}`, and the quotient `A/I` is the degree-zero part
`I_{≥0}/I_{≥1}`. Multiplication induces an isomorphism of `E`-algebras

`A_{<ω} ⊗_E A/I ≃ gr_{I_•} A`

whose degree-`j` component is `μ_j`: surjectivity is the surjectivity of the `μ_j`, and
injectivity follows from their injectivity by reading off the components of the image of a tensor
written as a sum of pieces in the `A_j ⊗ A/I`.
-/

universe u v

open scoped DirectSum TensorProduct

public noncomputable section

namespace LoweringDerivation

variable {E : Type u} {R : Type v} [Field E] [CommRing R] [Algebra E R]
variable (𝒜 : NatOrdinal → Submodule E R) [GradedAlgebra 𝒜]

/-! ### The degree attached to the filtration `I_{≥•}` -/

/-- The filtration `I_{≥•}` is separated, `⋂_j I_{≥j} = 0`: a non-zero element leaves `I_{≥j}`
once `j` exceeds the finite parts of its degrees. -/
theorem idealGE_isSeparatedFiltration : IsSeparatedFiltration (idealGE 𝒜) where
  antitone _ _ h := idealGE_antitone 𝒜 h
  top := idealGE_zero 𝒜
  mul_le := idealGE_mul_le 𝒜
  exists_not_mem {x} hx := by
    classical
    refine ⟨(DirectSum.decompose 𝒜 x).support.sup (fun δ ↦ δ.constantCoeff) + 1, fun hmem ↦ ?_⟩
    apply hx
    rw [← DirectSum.sum_support_decompose 𝒜 x]
    refine Finset.sum_eq_zero fun δ hδ ↦ ?_
    refine eq_zero_of_mem_idealGE_of_constantCoeff_lt 𝒜 (DirectSum.decompose 𝒜 x δ).2
      (idealGE_isHomogeneous 𝒜 _ δ hmem) ?_
    exact Nat.lt_succ_of_le (Finset.le_sup (f := fun δ ↦ δ.constantCoeff) hδ)

/-- The max-additive degree attached to `I_{≥•}`, valued in `ℕᵒᵈ`: its weak filtration at `j` is
`I_{≥j}`. -/
def filtrationIndex : MaxAddDegree R (OrderDual ℕ) :=
  (idealGE_isSeparatedFiltration 𝒜).degree

/-- The associated graded ring `gr_{I_•} A = ⨁_j I_{≥j}/I_{≥j+1}`. -/
abbrev IdealGEGraded := (filtrationIndex 𝒜).AssociatedGraded

theorem mem_filtrationIndex_filtrationLE_iff (j : ℕ) (x : R) :
    x ∈ (filtrationIndex 𝒜).filtrationLE (OrderDual.toDual j) ↔ x ∈ idealGE 𝒜 j :=
  (idealGE_isSeparatedFiltration 𝒜).mem_degree_filtrationLE_iff j x

theorem filtrationIndex_isSeparated : (filtrationIndex 𝒜).IsSeparated :=
  (idealGE_isSeparatedFiltration 𝒜).degree_isSeparated

/-- An element of `I_{≥j}`, as an element of the weak filtration at `j`. -/
def idealGEFiltrationMk (j : ℕ) {x : R} (hx : x ∈ idealGE 𝒜 j) :
    (filtrationIndex 𝒜).filtrationLE (OrderDual.toDual j) :=
  ⟨x, (mem_filtrationIndex_filtrationLE_iff 𝒜 j x).mpr hx⟩

theorem coe_idealGEFiltrationMk (j : ℕ) {x : R} (hx : x ∈ idealGE 𝒜 j) :
    (idealGEFiltrationMk 𝒜 j hx : R) = x := (rfl)

/-- The class in `I_{≥j}/I_{≥j+1}` of an element of `I_{≥j}`, as an element of `gr_{I_•} A`. -/
def idealGEMk (j : ℕ) {x : R} (hx : x ∈ idealGE 𝒜 j) : IdealGEGraded 𝒜 :=
  (filtrationIndex 𝒜).homogeneousMk (OrderDual.toDual j) (idealGEFiltrationMk 𝒜 j hx)

/-- The class in `I_{≥j}/I_{≥j+1}` is the direct-sum element concentrated in degree `j`. -/
theorem idealGEMk_eq_of (j : ℕ) {x : R} (hx : x ∈ idealGE 𝒜 j) :
    idealGEMk 𝒜 j hx = DirectSum.of (filtrationIndex 𝒜).Component (OrderDual.toDual j)
      ((filtrationIndex 𝒜).componentMk (OrderDual.toDual j) (idealGEFiltrationMk 𝒜 j hx)) :=
  (filtrationIndex 𝒜).homogeneousMk_apply _ _

theorem idealGEMk_eq_zero_iff (j : ℕ) {x : R} (hx : x ∈ idealGE 𝒜 j) :
    idealGEMk 𝒜 j hx = 0 ↔ x ∈ idealGE 𝒜 (j + 1) := by
  rw [idealGEMk, MaxAddDegree.homogeneousMk_eq_zero_iff, coe_idealGEFiltrationMk,
    filtrationIndex, IsSeparatedFiltration.degree_apply]
  exact (idealGE_isSeparatedFiltration 𝒜).value_lt_toDual_iff x j

theorem idealGEMk_add (j : ℕ) {x y : R} (hx : x ∈ idealGE 𝒜 j) (hy : y ∈ idealGE 𝒜 j) :
    idealGEMk 𝒜 j (add_mem hx hy) = idealGEMk 𝒜 j hx + idealGEMk 𝒜 j hy := by
  rw [idealGEMk, idealGEMk, idealGEMk, ← map_add]
  rfl

theorem idealGEMk_mul {i j : ℕ} {x y : R} (hx : x ∈ idealGE 𝒜 i) (hy : y ∈ idealGE 𝒜 j) :
    idealGEMk 𝒜 (i + j) (mul_mem_idealGE 𝒜 hx hy) = idealGEMk 𝒜 i hx * idealGEMk 𝒜 j hy := by
  rw [idealGEMk, idealGEMk, idealGEMk]
  exact (filtrationIndex 𝒜).homogeneousMk_mul_of_coe_eq rfl _ _ _ rfl

theorem idealGEMk_congr (j : ℕ) {x y : R} (hx : x ∈ idealGE 𝒜 j) (hy : y ∈ idealGE 𝒜 j)
    (h : x - y ∈ idealGE 𝒜 (j + 1)) : idealGEMk 𝒜 j hx = idealGEMk 𝒜 j hy := by
  have := (idealGEMk_eq_zero_iff 𝒜 j (sub_mem hx hy)).mpr h
  rw [idealGEMk, idealGEMk, ← sub_eq_zero, ← map_sub]
  exact this

theorem mem_idealGE_zero (x : R) : x ∈ idealGE 𝒜 0 := by
  rw [idealGE_zero]; exact Submodule.mem_top

theorem idealGEMk_one : idealGEMk 𝒜 0 (mem_idealGE_zero 𝒜 1) = 1 := by
  rw [idealGEMk, MaxAddDegree.homogeneousMk_apply, DirectSum.one_def]
  congr 1
  rw [show GradedMonoid.GOne.one = (filtrationIndex 𝒜).componentOne from rfl,
    MaxAddDegree.componentOne_eq_componentMk]
  rfl

/-- A sum of classes in distinct `I_{≥n}/I_{≥n+1}` vanishes only if each does. -/
theorem idealGEMk_eq_zero_of_sum_eq_zero {s : Finset ℕ} {x : ℕ → R}
    (hx : ∀ n, x n ∈ idealGE 𝒜 n) (h : ∑ n ∈ s, idealGEMk 𝒜 n (hx n) = 0) :
    ∀ n ∈ s, idealGEMk 𝒜 n (hx n) = 0 := by
  classical
  intro n hn
  have := congrArg (fun g : IdealGEGraded 𝒜 ↦ g (OrderDual.toDual n)) h
  simp only [DirectSum.sum_apply, DirectSum.zero_apply] at this
  rw [Finset.sum_eq_single n] at this
  · rw [idealGEMk, MaxAddDegree.homogeneousMk_apply, DirectSum.of_eq_same] at this
    rw [idealGEMk, MaxAddDegree.homogeneousMk_apply, this, map_zero]
  · intro m _ hmn
    rw [idealGEMk, MaxAddDegree.homogeneousMk_apply, DirectSum.of_eq_of_ne]
    exact fun h' ↦ hmn (OrderDual.toDual.injective h').symm
  · intro h'; exact absurd hn h'

/-- The class in `I_{≥j}/I_{≥j+1}` of a finite sum is the sum of the classes. -/
theorem idealGEMk_sum {ι : Type*} (s : Finset ι) (j : ℕ) {x : ι → R}
    (hx : ∀ i, x i ∈ idealGE 𝒜 j) (hs : ∑ i ∈ s, x i ∈ idealGE 𝒜 j) :
    idealGEMk 𝒜 j hs = ∑ i ∈ s, idealGEMk 𝒜 j (hx i) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    conv_rhs => rw [Finset.sum_empty]
    exact (idealGEMk_eq_zero_iff 𝒜 j _).mpr (by rw [Finset.sum_empty]; exact zero_mem _)
  | insert i s hi ih =>
    have hs' : ∑ i ∈ s, x i ∈ idealGE 𝒜 j := Submodule.sum_mem _ fun i _ ↦ hx i
    conv_rhs => rw [Finset.sum_insert hi, ← ih hs', ← idealGEMk_add]
    exact idealGEMk_congr 𝒜 j _ _ (by rw [Finset.sum_insert hi, sub_self]; exact zero_mem _)

theorem idealGEMk_congr_index {i j : ℕ} (h : i = j) {x : R} (hx : x ∈ idealGE 𝒜 i) :
    idealGEMk 𝒜 i hx = idealGEMk 𝒜 j (h ▸ hx) := by
  subst h
  rfl

theorem idealGEMk_zero (j : ℕ) : idealGEMk 𝒜 j (zero_mem _) = 0 :=
  (idealGEMk_eq_zero_iff 𝒜 j _).mpr (zero_mem _)

/-! ### The degree-zero part: `A/I` -/

/-- The class in `I_{≥0}/I_{≥1}`, as a ring homomorphism `A → gr_{I_•} A`. -/
def idealGEZeroHom : R →+* IdealGEGraded 𝒜 where
  toFun x := idealGEMk 𝒜 0 (mem_idealGE_zero 𝒜 x)
  map_one' := idealGEMk_one 𝒜
  map_mul' x y := idealGEMk_mul 𝒜 (mem_idealGE_zero 𝒜 x) (mem_idealGE_zero 𝒜 y)
  map_zero' := idealGEMk_zero 𝒜 0
  map_add' x y := idealGEMk_add 𝒜 0 (mem_idealGE_zero 𝒜 x) (mem_idealGE_zero 𝒜 y)

theorem idealGEZeroHom_apply (x : R) :
    idealGEZeroHom 𝒜 x = idealGEMk 𝒜 0 (mem_idealGE_zero 𝒜 x) := (rfl)

/-- The `E`-algebra structure on `gr_{I_•} A`, through the classes of the scalars in degree zero. -/
instance : Algebra E (IdealGEGraded 𝒜) := ((idealGEZeroHom 𝒜).comp (algebraMap E R)).toAlgebra

theorem idealGEGraded_algebraMap_apply (e : E) :
    algebraMap E (IdealGEGraded 𝒜) e = idealGEZeroHom 𝒜 (algebraMap E R e) := (rfl)

/-- The quotient `A/I = I_{≥0}/I_{≥1}` maps to degree zero of `gr_{I_•} A`. -/
def fibreInitialHom : Fibre 𝒜 →+* IdealGEGraded 𝒜 :=
  Ideal.Quotient.lift (fibreIdeal 𝒜) (idealGEZeroHom 𝒜) fun _ hx ↦
    (idealGEMk_eq_zero_iff 𝒜 0 _).mpr hx

theorem fibreInitialHom_fibreMap (x : R) :
    fibreInitialHom 𝒜 (fibreMap 𝒜 x) = idealGEMk 𝒜 0 (mem_idealGE_zero 𝒜 x) :=
  Ideal.Quotient.lift_mk _ _ _

/-- The map `A/I → gr_{I_•} A` onto degree zero, as an `E`-algebra homomorphism. -/
def fibreInitialAlgHom : Fibre 𝒜 →ₐ[E] IdealGEGraded 𝒜 :=
  { fibreInitialHom 𝒜 with
    commutes' := fun e ↦ by
      change fibreInitialHom 𝒜 (fibreMap 𝒜 (algebraMap E R e)) = _
      rw [fibreInitialHom_fibreMap]
      rfl }

theorem fibreInitialAlgHom_fibreMap (x : R) :
    fibreInitialAlgHom 𝒜 (fibreMap 𝒜 x) = idealGEMk 𝒜 0 (mem_idealGE_zero 𝒜 x) :=
  fibreInitialHom_fibreMap 𝒜 x

/-! ### The finite degrees -/

/-- The class in `gr_{I_•} A` of a homogeneous element of degree `α`: its class in
`I_{≥n}/I_{≥n+1}` when `α = n < ω`, and zero otherwise. -/
def gradeInitial (α : NatOrdinal) : 𝒜 α →+ IdealGEGraded 𝒜 :=
  if h : α = (α.constantCoeff : NatOrdinal) then
    { toFun := fun a ↦ idealGEMk 𝒜 α.constantCoeff
        (mem_idealGE_of_mem 𝒜 le_rfl (show (a : R) ∈ 𝒜 (α.constantCoeff : NatOrdinal) from
          h ▸ a.2))
      map_zero' := idealGEMk_zero 𝒜 _
      map_add' := fun _ _ ↦ idealGEMk_add 𝒜 _ _ _ }
  else 0

theorem gradeInitial_natCast (n : ℕ) (a : 𝒜 (n : NatOrdinal)) :
    gradeInitial 𝒜 (n : NatOrdinal) a = idealGEMk 𝒜 n (mem_idealGE_of_mem 𝒜 le_rfl a.2) := by
  have h : (n : NatOrdinal) = ((n : NatOrdinal).constantCoeff : NatOrdinal) := by
    rw [NatOrdinal.constantCoeff_natCast]
  rw [gradeInitial, dif_pos h]
  exact idealGEMk_congr_index 𝒜 (NatOrdinal.constantCoeff_natCast n) _

theorem gradeInitial_of_not_natCast {α : NatOrdinal} (hα : ¬ ∃ n : ℕ, α = n) (a : 𝒜 α) :
    gradeInitial 𝒜 α a = 0 := by
  rw [gradeInitial, dif_neg fun h ↦ hα ⟨_, h⟩]
  rfl

/-- The sum of the classes in `gr_{I_•} A` of the homogeneous components of finite degree. -/
def finiteDegreeInitialAdd : R →+ IdealGEGraded 𝒜 :=
  (DirectSum.toAddMonoid (gradeInitial 𝒜)).comp (DirectSum.decomposeAddEquiv 𝒜).toAddMonoidHom

theorem finiteDegreeInitialAdd_coe {α : NatOrdinal} (a : 𝒜 α) :
    finiteDegreeInitialAdd 𝒜 a = gradeInitial 𝒜 α a := by
  rw [finiteDegreeInitialAdd, AddMonoidHom.comp_apply, AddEquiv.coe_toAddMonoidHom,
    DirectSum.decomposeAddEquiv_apply, DirectSum.decompose_coe, DirectSum.toAddMonoid_of]

theorem finiteDegreeInitialAdd_of_mem {n : ℕ} {x : R} (hx : x ∈ 𝒜 (n : NatOrdinal)) :
    finiteDegreeInitialAdd 𝒜 x = idealGEMk 𝒜 n (mem_idealGE_of_mem 𝒜 le_rfl hx) :=
  (finiteDegreeInitialAdd_coe 𝒜 (⟨x, hx⟩ : 𝒜 (n : NatOrdinal))).trans (gradeInitial_natCast 𝒜 n _)

theorem finiteDegreeInitialAdd_of_mem_of_not_natCast {α : NatOrdinal} (hα : ¬ ∃ n : ℕ, α = n)
    {x : R}
    (hx : x ∈ 𝒜 α) : finiteDegreeInitialAdd 𝒜 x = 0 :=
  (finiteDegreeInitialAdd_coe 𝒜 (⟨x, hx⟩ : 𝒜 α)).trans (gradeInitial_of_not_natCast 𝒜 hα _)

/-- The finite-degree part `A_{<ω}` maps to `gr_{I_•} A`, a homogeneous element of degree `j`
going to its class in `I_{≥j}/I_{≥j+1}`. -/
def finiteDegreeInitialHom : finiteDegreePart 𝒜 →+* IdealGEGraded 𝒜 where
  toFun a := finiteDegreeInitialAdd 𝒜 a
  map_zero' := by rw [Subalgebra.coe_zero, map_zero]
  map_add' a b := by rw [Subalgebra.coe_add, map_add]
  map_one' := by
    rw [Subalgebra.coe_one, finiteDegreeInitialAdd_of_mem 𝒜 (n := 0)
      (by rw [Nat.cast_zero]; exact SetLike.one_mem_graded 𝒜)]
    exact idealGEMk_one 𝒜
  map_mul' a b := by
    rw [Subalgebra.coe_mul]
    refine finiteDegreeSubmodule_induction 𝒜
      (p := fun x _ ↦
        finiteDegreeInitialAdd 𝒜 (x * b) = finiteDegreeInitialAdd 𝒜 x * finiteDegreeInitialAdd 𝒜 b)
      ?_ ?_ ?_ ((mem_finiteDegreePart_iff 𝒜 _).mp a.2)
    · intro m x hx
      refine finiteDegreeSubmodule_induction 𝒜
        (p := fun y _ ↦
          finiteDegreeInitialAdd 𝒜 (x * y) =
            finiteDegreeInitialAdd 𝒜 x * finiteDegreeInitialAdd 𝒜 y)
        ?_ ?_ ?_ ((mem_finiteDegreePart_iff 𝒜 _).mp b.2)
      · intro n y hy
        have hxy : x * y ∈ 𝒜 ((m + n : ℕ) : NatOrdinal) := by
          rw [Nat.cast_add]; exact SetLike.mul_mem_graded hx hy
        rw [finiteDegreeInitialAdd_of_mem 𝒜 hxy, finiteDegreeInitialAdd_of_mem 𝒜 hx,
          finiteDegreeInitialAdd_of_mem 𝒜 hy, ← idealGEMk_mul]
      · rw [mul_zero, map_zero, mul_zero]
      · intro y z _ _ hy hz
        rw [mul_add, map_add, map_add, hy, hz, mul_add]
    · rw [zero_mul, map_zero, zero_mul]
    · intro x y _ _ hx hy
      rw [add_mul, map_add, map_add, hx, hy, add_mul]

theorem finiteDegreeInitialHom_apply (a : finiteDegreePart 𝒜) :
    finiteDegreeInitialHom 𝒜 a = finiteDegreeInitialAdd 𝒜 a := (rfl)

/-- The map `A_{<ω} → gr_{I_•} A`, as an `E`-algebra homomorphism. -/
def finiteDegreeInitialAlgHom : finiteDegreePart 𝒜 →ₐ[E] IdealGEGraded 𝒜 :=
  { finiteDegreeInitialHom 𝒜 with
    commutes' := fun e ↦ by
      change finiteDegreeInitialAdd 𝒜 (algebraMap E R e) = _
      rw [finiteDegreeInitialAdd_of_mem 𝒜 (n := 0)
        (by rw [Nat.cast_zero]; exact SetLike.algebraMap_mem_graded 𝒜 e)]
      rfl }

theorem finiteDegreeInitialAlgHom_apply (a : finiteDegreePart 𝒜) :
    finiteDegreeInitialAlgHom 𝒜 a = finiteDegreeInitialAdd 𝒜 a := (rfl)

/-! ### The multiplication map `A_{<ω} ⊗_E A/I → gr_{I_•} A` -/

/-- Multiplication of the classes, `A_{<ω} ⊗_E A/I →ₐ[E] gr_{I_•} A`; the paper's `⨁_j μ_j`. -/
def idealGETensorHom : finiteDegreePart 𝒜 ⊗[E] Fibre 𝒜 →ₐ[E] IdealGEGraded 𝒜 :=
  Algebra.TensorProduct.productMap (finiteDegreeInitialAlgHom 𝒜) (fibreInitialAlgHom 𝒜)

theorem idealGETensorHom_tmul (a : finiteDegreePart 𝒜) (c : Fibre 𝒜) :
    idealGETensorHom 𝒜 (a ⊗ₜ[E] c) = finiteDegreeInitialAlgHom 𝒜 a * fibreInitialAlgHom 𝒜 c :=
  Algebra.TensorProduct.productMap_apply_tmul _ _ _ _

theorem idealGETensorHom_natInclusion_tmul (j : ℕ) (a : 𝒜 (j : NatOrdinal)) (b : R) :
    idealGETensorHom 𝒜 (natInclusion 𝒜 j a ⊗ₜ[E] fibreMap 𝒜 b) =
      idealGEMk 𝒜 j (Ideal.mul_mem_right b _ (mem_idealGE_of_mem 𝒜 le_rfl a.2)) := by
  rw [idealGETensorHom_tmul, finiteDegreeInitialAlgHom_apply, coe_natInclusion,
    finiteDegreeInitialAdd_of_mem 𝒜 a.2, fibreInitialAlgHom_fibreMap, ← idealGEMk_mul]
  exact idealGEMk_congr_index 𝒜 (Nat.add_zero j) _

/-- Tensors in `A_j ⊗ A/I` map to degree `j`, compatibly with `μ_j`. -/
theorem exists_idealGETensorHom_rTensor_eq (j : ℕ) (T : 𝒜 (j : NatOrdinal) ⊗[E] Fibre 𝒜) :
    ∃ x, ∃ hx : x ∈ idealGE 𝒜 j,
      mu 𝒜 j T = (Submodule.Quotient.mk x : R ⧸ idealGE 𝒜 (j + 1)) ∧
        idealGETensorHom 𝒜 ((natInclusion 𝒜 j).rTensor _ T) = idealGEMk 𝒜 j hx := by
  induction T with
  | zero =>
    exact ⟨0, zero_mem _, by rw [map_zero, Submodule.Quotient.mk_zero],
      by rw [map_zero, map_zero, idealGEMk_zero]⟩
  | tmul a c =>
    obtain ⟨b, rfl⟩ := fibreMap_surjective 𝒜 c
    exact ⟨(a : R) * b, Ideal.mul_mem_right _ _ (mem_idealGE_of_mem 𝒜 le_rfl a.2),
      mu_tmul 𝒜 j a b, by rw [LinearMap.rTensor_tmul, idealGETensorHom_natInclusion_tmul]⟩
  | add x y hx hy =>
    obtain ⟨x', hx', hcx, hwx⟩ := hx
    obtain ⟨y', hy', hcy, hwy⟩ := hy
    exact ⟨x' + y', add_mem hx' hy', by rw [map_add, hcx, hcy, Submodule.Quotient.mk_add],
      by rw [map_add, map_add, hwx, hwy, idealGEMk_add]⟩

/-- The class in `I_{≥j}/I_{≥j+1}` of any element of `I_{≥j}` is in the image of
`A_{<ω} ⊗_E A/I`. -/
theorem exists_idealGETensorHom_eq_idealGEMk (j : ℕ) {x : R} (hx : x ∈ idealGE 𝒜 j) :
    ∃ u, idealGETensorHom 𝒜 u = idealGEMk 𝒜 j hx := by
  obtain ⟨T, hT⟩ := exists_mu_eq 𝒜 hx
  obtain ⟨x', hx', hcx, hwx⟩ := exists_idealGETensorHom_rTensor_eq 𝒜 j T
  refine ⟨_, hwx.trans (idealGEMk_congr 𝒜 j hx' hx ?_)⟩
  rw [hT] at hcx
  exact (Submodule.Quotient.eq _).mp hcx.symm

theorem idealGETensorHom_surjective : Function.Surjective (idealGETensorHom 𝒜) := by
  intro g
  induction g using DirectSum.induction_on with
  | zero => exact ⟨0, map_zero _⟩
  | of j c =>
    induction c using MaxAddDegree.componentInductionOn with
    | _ x =>
      obtain ⟨u, hu⟩ := exists_idealGETensorHom_eq_idealGEMk 𝒜 (OrderDual.ofDual j)
        ((mem_filtrationIndex_filtrationLE_iff 𝒜 _ x).mp x.2)
      refine ⟨u, hu.trans ?_⟩
      rw [idealGEMk, MaxAddDegree.homogeneousMk_apply]
      rfl
  | add x y hx hy =>
    obtain ⟨u, rfl⟩ := hx
    obtain ⟨v, rfl⟩ := hy
    exact ⟨u + v, map_add _ _ _⟩

/-- Injectivity: write `u = ∑_n (ι_n ⊗ 1) t_n` with `t_n ∈ A_n ⊗ A/I`; the degree-`n` component
of the image is the class of a lift of `μ_n(t_n)`, so it vanishes only if `μ_n(t_n) = 0`, that is,
`t_n = 0`. -/
theorem idealGETensorHom_injective (h0 : GradeZeroScalars 𝒜) {Δ : R →ₗ[E] FunAtZeroMinus R}
    (hΔ : IsLoweringDerivation 𝒜 Δ) : Function.Injective (idealGETensorHom 𝒜) := by
  rw [injective_iff_map_eq_zero]
  intro u hu
  obtain ⟨N, t, rfl⟩ := exists_eq_sum_rTensor_natInclusion 𝒜 u
  choose x hx hchar hw using fun n ↦ exists_idealGETensorHom_rTensor_eq 𝒜 n (t n)
  rw [map_sum, Finset.sum_congr rfl fun n _ ↦ hw n] at hu
  refine Finset.sum_eq_zero fun n hn ↦ ?_
  have hW := (idealGEMk_eq_zero_iff 𝒜 n (hx n)).mp (idealGEMk_eq_zero_of_sum_eq_zero 𝒜 hx hu n hn)
  have hT : mu 𝒜 n (t n) = 0 := by
    rw [hchar n, Submodule.Quotient.mk_eq_zero]
    exact hW
  rw [(injective_iff_map_eq_zero _).mp (hΔ.mu_injective h0 n) _ hT, map_zero]

/-- Multiplication induces a graded `E`-algebra isomorphism `A_{<ω} ⊗_E A/I ≃ gr_{I_•} A`. -/
def idealGETensorEquiv (h0 : GradeZeroScalars 𝒜) {Δ : R →ₗ[E] FunAtZeroMinus R}
    (hΔ : IsLoweringDerivation 𝒜 Δ) :
    finiteDegreePart 𝒜 ⊗[E] Fibre 𝒜 ≃ₐ[E] IdealGEGraded 𝒜 :=
  AlgEquiv.ofBijective (idealGETensorHom 𝒜)
    ⟨idealGETensorHom_injective 𝒜 h0 hΔ, idealGETensorHom_surjective 𝒜⟩

theorem coe_idealGETensorEquiv (h0 : GradeZeroScalars 𝒜) {Δ : R →ₗ[E] FunAtZeroMinus R}
    (hΔ : IsLoweringDerivation 𝒜 Δ) :
    ⇑(idealGETensorEquiv 𝒜 h0 hΔ) = ⇑(idealGETensorHom 𝒜) := (rfl)

end LoweringDerivation
