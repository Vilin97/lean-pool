/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/

import LeanPool.ClassFieldTheory.GaloisCohomology.Cyclic.Herbrand.NormalBasisLattice
import LeanPool.ClassFieldTheory.GaloisCohomology.Cyclic.Herbrand.HerbrandLowDegree.Basic
import Mathlib.FieldTheory.Galois.NormalBasis
import Mathlib.LinearAlgebra.Quotient.Pi
/-! Provides the public declarations in the `LocalClassFieldTheory.ClassFormation.NormalBasis` Lean module. -/

namespace LocalClassFieldTheory

open LocalFieldTheory

open CyclicCohomology

noncomputable section

universe u

open scoped ValuativeRel

variable (K L : Type u) [Field K] [ValuativeRel K] [Field L]
  [Algebra K L] [FiniteDimensional K L] [IsGalois K L]

/-- The two descriptions of the standard lattice use the same normal-basis orbit. -/
theorem span_normalBasis_eq_chosenNormalBasisIntegerLattice :
    Submodule.span 𝒪[K] (Set.range (IsGalois.normalBasis K L)) =
      chosenNormalBasisIntegerLattice K L := by
  rw [chosenNormalBasisIntegerLattice_eq_span]
  congr 1
  ext y
  constructor
  · rintro ⟨σ, rfl⟩
    exact ⟨σ, (IsGalois.normalBasis_apply (K := K) (L := L) σ).symm⟩
  · rintro ⟨σ, rfl⟩
    exact ⟨σ, IsGalois.normalBasis_apply (K := K) (L := L) σ⟩

/-- The normal-basis orbit is an `𝒪_K`-basis of the standard lattice `M`.
This is the coordinate source for the induced-module calculation in the local
class-field-axiom proof. -/
noncomputable def chosenNormalBasisIntegerLatticeBasis :
    Module.Basis Gal(L / K) 𝒪[K] (chosenNormalBasisIntegerLattice K L) :=
  ((IsGalois.normalBasis K L).restrictScalars 𝒪[K]).map
    (LinearEquiv.ofEq _ _
      (span_normalBasis_eq_chosenNormalBasisIntegerLattice K L))

/-- The integral lattice basis has the same underlying vectors as the chosen normal basis. -/
@[simp]
theorem chosenNormalBasisIntegerLatticeBasis_apply (σ : Gal(L/K)) :
    ((chosenNormalBasisIntegerLatticeBasis K L σ :
      chosenNormalBasisIntegerLattice K L) : L) = IsGalois.normalBasis K L σ := by
  simp [chosenNormalBasisIntegerLatticeBasis, LinearEquiv.coe_ofEq_apply]

section GradedCoordinates

variable [TopologicalSpace K] [IsNonarchimedeanLocalField K]

/-- Multiplication by `π_K^n`, from the normal-basis lattice onto its
`n`-th dilate. -/
def chosenNormalBasisIntegerLatticeMulPowLinearMap (n : Nat) :
    chosenNormalBasisIntegerLattice K L →ₗ[𝒪[K]]
      chosenBaseUniformizerPowSubmodule K L n (chosenNormalBasisIntegerLattice K L) where
  toFun x :=
    ⟨algebraMap 𝒪[K] L (chosenIntegerRingUniformizer K ^ n) * (x : L),
      (mem_chosenBaseUniformizerPowSubmodule_iff
        (K := K) (L := L) n (chosenNormalBasisIntegerLattice K L) _).2
        ⟨x, x.2, rfl⟩⟩
  map_add' := by
    intro x y
    ext
    exact mul_add _ _ _
  map_smul' := by
    intro a x
    ext
    simp [Algebra.smul_def, mul_assoc, mul_comm, mul_left_comm]

/-- Uniformizer-power scaling bijects the integral lattice with its scaled copy. -/
theorem chosenNormalBasisIntegerLatticeMulPowLinearMap_bijective (n : Nat) :
    Function.Bijective (chosenNormalBasisIntegerLatticeMulPowLinearMap K L n) := by
  constructor
  · intro x y hxy
    apply Subtype.ext
    have hxy' := congrArg Subtype.val hxy
    change algebraMap 𝒪[K] L (chosenIntegerRingUniformizer K ^ n) * (x : L) =
      algebraMap 𝒪[K] L (chosenIntegerRingUniformizer K ^ n) * (y : L) at hxy'
    have hπ : chosenIntegerRingUniformizer K ^ n ≠ 0 :=
      pow_ne_zero n (chosenIntegerRingUniformizer_irreducible K).ne_zero
    have hπL : algebraMap 𝒪[K] L (chosenIntegerRingUniformizer K ^ n) ≠ 0 := by
      change algebraMap K L
          ((chosenIntegerRingUniformizer K ^ n : 𝒪[K]) : K) ≠ 0
      apply (map_ne_zero (algebraMap K L)).2
      intro h
      exact hπ ((IsFractionRing.injective 𝒪[K] K) h)
    exact mul_left_cancel₀ hπL hxy'
  · intro x
    rcases (mem_chosenBaseUniformizerPowSubmodule_iff
      (K := K) (L := L) n (chosenNormalBasisIntegerLattice K L) (x : L)).1 x.2 with
      ⟨y, hy, hxy⟩
    refine ⟨⟨y, hy⟩, ?_⟩
    apply Subtype.ext
    exact hxy

/-- Multiplication by `π_K^n` as an `𝒪_K`-linear equivalence of the
normal-basis lattice with its `n`-th dilate. -/
noncomputable def chosenNormalBasisIntegerLatticeMulPowLinearEquiv (n : Nat) :
    chosenNormalBasisIntegerLattice K L ≃ₗ[𝒪[K]]
      chosenBaseUniformizerPowSubmodule K L n (chosenNormalBasisIntegerLattice K L) :=
  LinearEquiv.ofBijective (chosenNormalBasisIntegerLatticeMulPowLinearMap K L n)
    (chosenNormalBasisIntegerLatticeMulPowLinearMap_bijective K L n)

/-- The scaling equivalence acts by multiplication by the chosen uniformizer power. -/
@[simp]
theorem chosenNormalBasisIntegerLatticeMulPowLinearEquiv_apply
    (n : Nat) (x : chosenNormalBasisIntegerLattice K L) :
    ((chosenNormalBasisIntegerLatticeMulPowLinearEquiv K L n x :
      chosenBaseUniformizerPowSubmodule K L n (chosenNormalBasisIntegerLattice K L)) : L) =
      algebraMap 𝒪[K] L (chosenIntegerRingUniformizer K ^ n) * (x : L) :=
  rfl

/-- The first uniformizer layer `π_K M`, regarded as a submodule of the
normal-basis lattice `M`. -/
def chosenNormalBasisIntegerLatticeUniformizerSubmodule :
    Submodule 𝒪[K] (chosenNormalBasisIntegerLattice K L) :=
  (chosenBaseUniformizerPowSubmodule K L 1
      (chosenNormalBasisIntegerLattice K L)).comap
    (chosenNormalBasisIntegerLattice K L).subtype

/-- Membership in the lattice uniformizer submodule is detected after coercion to the field. -/
@[simp]
theorem mem_chosenNormalBasisIntegerLatticeUniformizerSubmodule_iff
    (x : chosenNormalBasisIntegerLattice K L) :
    x ∈ chosenNormalBasisIntegerLatticeUniformizerSubmodule K L ↔
      (x : L) ∈ chosenBaseUniformizerPowSubmodule K L 1
        (chosenNormalBasisIntegerLattice K L) :=
  Iff.rfl

/-- Scaling maps the uniformizer submodule onto the next normal-basis lattice. -/
theorem chosenNormalBasisIntegerLatticeUniformizerSubmodule_map_mulPow
    (n : Nat) :
    (chosenNormalBasisIntegerLatticeUniformizerSubmodule K L).map
        (chosenNormalBasisIntegerLatticeMulPowLinearEquiv K L n :
          chosenNormalBasisIntegerLattice K L →ₗ[𝒪[K]]
            chosenBaseUniformizerPowSubmodule K L n
              (chosenNormalBasisIntegerLattice K L)) =
      chosenNormalBasisLatticeSuccSubmodule K L n := by
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    change algebraMap 𝒪[K] L (chosenIntegerRingUniformizer K ^ n) * (y : L) ∈
      chosenBaseUniformizerPowSubmodule K L (n + 1)
        (chosenNormalBasisIntegerLattice K L)
    rcases (mem_chosenBaseUniformizerPowSubmodule_iff
      (K := K) (L := L) 1 (chosenNormalBasisIntegerLattice K L) (y : L)).1 hy with
      ⟨z, hz, hzy⟩
    refine (mem_chosenBaseUniformizerPowSubmodule_iff
      (K := K) (L := L) (n + 1) (chosenNormalBasisIntegerLattice K L) _).2
      ⟨z, hz, ?_⟩
    rw [← hzy]
    simp only [pow_succ, pow_zero, map_mul, one_mul]
    ring
  · intro hx
    change (x : L) ∈ chosenBaseUniformizerPowSubmodule K L (n + 1)
      (chosenNormalBasisIntegerLattice K L) at hx
    rcases (mem_chosenBaseUniformizerPowSubmodule_iff
      (K := K) (L := L) (n + 1) (chosenNormalBasisIntegerLattice K L) (x : L)).1 hx with
      ⟨z, hz, hzx⟩
    let y : chosenNormalBasisIntegerLattice K L :=
      ⟨algebraMap 𝒪[K] L (chosenIntegerRingUniformizer K) * z, by
        simpa [Algebra.smul_def] using
          (chosenNormalBasisIntegerLattice K L).smul_mem
            (chosenIntegerRingUniformizer K) hz⟩
    have hy : y ∈ chosenNormalBasisIntegerLatticeUniformizerSubmodule K L := by
      refine (mem_chosenBaseUniformizerPowSubmodule_iff
        (K := K) (L := L) 1 (chosenNormalBasisIntegerLattice K L) (y : L)).2
        ⟨z, hz, ?_⟩
      simp [y]
    refine ⟨y, hy, ?_⟩
    apply Subtype.ext
    change algebraMap 𝒪[K] L (chosenIntegerRingUniformizer K ^ n) * (y : L) =
      (x : L)
    rw [← hzx]
    simp only [y, pow_succ, map_mul]
    ring

/-- Removing the common factor `π_K^n` identifies the `n`-th lattice graded
piece with the fixed quotient `M / π_K M`. -/
noncomputable def chosenNormalBasisLatticeSuccQuotToIntegerLatticeQuotLinearEquiv
    (n : Nat) :
    chosenNormalBasisLatticeSuccQuot K L n ≃ₗ[𝒪[K]]
      (chosenNormalBasisIntegerLattice K L ⧸
        chosenNormalBasisIntegerLatticeUniformizerSubmodule K L) :=
  (chosenNormalBasisLatticeSuccQuotConcreteLinearEquiv K L n).trans
    (Submodule.Quotient.equiv
      (chosenNormalBasisIntegerLatticeUniformizerSubmodule K L)
      (chosenNormalBasisLatticeSuccSubmodule K L n)
      (chosenNormalBasisIntegerLatticeMulPowLinearEquiv K L n)
      (chosenNormalBasisIntegerLatticeUniformizerSubmodule_map_mulPow K L n)).symm

/-- Removing the common uniformizer power sends a scaled representative to its integral class. -/
@[simp]
theorem chosenNormalBasisLatticeSuccQuotToIntegerLatticeQuotLinearEquiv_mk_mulPow
    (n : Nat) (x : chosenNormalBasisIntegerLattice K L) :
    chosenNormalBasisLatticeSuccQuotToIntegerLatticeQuotLinearEquiv K L n
        (chosenNormalBasisLatticeSuccQuotMk K L n
          (chosenNormalBasisIntegerLatticeMulPowLinearEquiv K L n x)) =
      Submodule.Quotient.mk x := by
  let e := Submodule.Quotient.equiv
    (chosenNormalBasisIntegerLatticeUniformizerSubmodule K L)
    (chosenNormalBasisLatticeSuccSubmodule K L n)
    (chosenNormalBasisIntegerLatticeMulPowLinearEquiv K L n)
    (chosenNormalBasisIntegerLatticeUniformizerSubmodule_map_mulPow K L n)
  change
    e.symm
        (chosenNormalBasisLatticeSuccQuotConcreteLinearEquiv K L n
          (chosenNormalBasisLatticeSuccQuotMk K L n
            (chosenNormalBasisIntegerLatticeMulPowLinearEquiv K L n x))) =
      Submodule.Quotient.mk x
  rw [chosenNormalBasisLatticeSuccQuotConcreteLinearEquiv_mk]
  apply e.injective
  rw [LinearEquiv.apply_symm_apply]
  rfl

/-- Coordinate functions all of whose values lie in the maximal ideal of
`𝒪_K`. -/
def chosenNormalBasisCoordinateMaximalSubmodule :
    Submodule 𝒪[K] (Gal(L / K) → 𝒪[K]) :=
  Submodule.pi Set.univ (fun _ => (𝓂[K] : Ideal 𝒪[K]))

omit [FiniteDimensional K L] [IsGalois K L] in
/-- A coordinate function lies in the maximal submodule exactly when every value is nonunit. -/
@[simp]
theorem mem_chosenNormalBasisCoordinateMaximalSubmodule_iff
    (f : Gal(L / K) → 𝒪[K]) :
    f ∈ chosenNormalBasisCoordinateMaximalSubmodule K L ↔
      ∀ σ : Gal(L / K), f σ ∈ (𝓂[K] : Ideal 𝒪[K]) := by
  simp [chosenNormalBasisCoordinateMaximalSubmodule]

/-- Normal-basis coordinates identify the uniformizer submodule with pointwise maximal-ideal values. -/
theorem chosenNormalBasisIntegerLatticeUniformizerSubmodule_map_equivFun :
    (chosenNormalBasisIntegerLatticeUniformizerSubmodule K L).map
        ((chosenNormalBasisIntegerLatticeBasis K L).equivFun :
          chosenNormalBasisIntegerLattice K L →ₗ[𝒪[K]] (Gal(L / K) → 𝒪[K])) =
      chosenNormalBasisCoordinateMaximalSubmodule K L := by
  ext f
  constructor
  · rintro ⟨x, hx, rfl⟩
    rw [chosenNormalBasisCoordinateMaximalSubmodule, Submodule.mem_pi]
    intro σ _
    rcases (mem_chosenBaseUniformizerPowSubmodule_iff
      (K := K) (L := L) 1 (chosenNormalBasisIntegerLattice K L) (x : L)).1 hx with
      ⟨z, hz, hzx⟩
    let zM : chosenNormalBasisIntegerLattice K L := ⟨z, hz⟩
    have hx_eq : x = chosenIntegerRingUniformizer K • zM := by
      apply Subtype.ext
      simpa [Algebra.smul_def, zM] using hzx.symm
    rw [chosenIntegerRingUniformizer_maximalIdeal_eq,
      Ideal.mem_span_singleton']
    refine ⟨(chosenNormalBasisIntegerLatticeBasis K L).equivFun zM σ, ?_⟩
    rw [hx_eq]
    simp [mul_comm]
  · intro hf
    have hf' : ∀ σ : Gal(L / K),
        ∃ c : 𝒪[K], c * chosenIntegerRingUniformizer K = f σ := by
      intro σ
      have hσ := (Submodule.mem_pi.mp hf) σ (Set.mem_univ σ)
      rw [chosenIntegerRingUniformizer_maximalIdeal_eq,
        Ideal.mem_span_singleton'] at hσ
      exact hσ
    let c : Gal(L / K) → 𝒪[K] := fun σ => Classical.choose (hf' σ)
    have hc (σ : Gal(L / K)) :
        c σ * chosenIntegerRingUniformizer K = f σ :=
      Classical.choose_spec (hf' σ)
    let z : chosenNormalBasisIntegerLattice K L :=
      (chosenNormalBasisIntegerLatticeBasis K L).equivFun.symm c
    let x : chosenNormalBasisIntegerLattice K L :=
      chosenIntegerRingUniformizer K • z
    have hx : x ∈ chosenNormalBasisIntegerLatticeUniformizerSubmodule K L := by
      refine (mem_chosenBaseUniformizerPowSubmodule_iff
        (K := K) (L := L) 1 (chosenNormalBasisIntegerLattice K L) (x : L)).2
        ⟨z, z.2, ?_⟩
      simp [x, Algebra.smul_def]
    refine ⟨x, hx, ?_⟩
    funext σ
    have hzcoord :
        (chosenNormalBasisIntegerLatticeBasis K L).equivFun z = c :=
      (chosenNormalBasisIntegerLatticeBasis K L).equivFun.apply_symm_apply c
    calc
      (chosenNormalBasisIntegerLatticeBasis K L).equivFun x σ =
          chosenIntegerRingUniformizer K *
            (chosenNormalBasisIntegerLatticeBasis K L).equivFun z σ := by
        simp [x]
      _ = chosenIntegerRingUniformizer K * c σ := by rw [hzcoord]
      _ = f σ := by rw [mul_comm, hc]

/-- Normal-basis coordinates identify `M / π_K M` with the coordinatewise
maximal-ideal quotient. -/
noncomputable def chosenNormalBasisIntegerLatticeQuotCoordinateQuotLinearEquiv :
    (chosenNormalBasisIntegerLattice K L ⧸
        chosenNormalBasisIntegerLatticeUniformizerSubmodule K L) ≃ₗ[𝒪[K]]
      ((Gal(L / K) → 𝒪[K]) ⧸ chosenNormalBasisCoordinateMaximalSubmodule K L) :=
  Submodule.Quotient.equiv
    (chosenNormalBasisIntegerLatticeUniformizerSubmodule K L)
    (chosenNormalBasisCoordinateMaximalSubmodule K L)
    (chosenNormalBasisIntegerLatticeBasis K L).equivFun
    (chosenNormalBasisIntegerLatticeUniformizerSubmodule_map_equivFun K L)

/-- Quotienting coordinate functions by the pointwise maximal ideal is the
function space with values in `𝒪_K / 𝓂_K`. -/
noncomputable def chosenNormalBasisCoordinateQuotPiLinearEquiv :
    ((Gal(L / K) → 𝒪[K]) ⧸ chosenNormalBasisCoordinateMaximalSubmodule K L) ≃ₗ[𝒪[K]]
      (Gal(L / K) → (𝒪[K] ⧸ (𝓂[K] : Ideal 𝒪[K]))) := by
  classical
  exact Submodule.quotientPi (fun _ : Gal(L / K) => (𝓂[K] : Ideal 𝒪[K]))

omit [IsGalois K L] in
/-- The coordinate quotient equivalence sends a representative to its pointwise residue classes. -/
@[simp]
theorem chosenNormalBasisCoordinateQuotPiLinearEquiv_mk
    (f : Gal(L / K) → 𝒪[K]) :
    chosenNormalBasisCoordinateQuotPiLinearEquiv K L
        (Submodule.Quotient.mk f) =
      fun σ : Gal(L / K) => Submodule.Quotient.mk (f σ) :=
  rfl

/-- Apply `𝒪_K / 𝓂_K ≃ 𝓀_K` pointwise and reverse the Galois index.  The
inverse index converts the natural left-regular coordinate rule into the
right-regular convention used in the Herbrand calculation. -/
def chosenNormalBasisPiResidueInverseIndexAddEquiv :
    (Gal(L / K) → (𝒪[K] ⧸ (𝓂[K] : Ideal 𝒪[K]))) ≃+
      (Gal(L / K) → 𝓀[K]) where
  toFun f σ := integerRingModMaximalIdealAddEquivResidue K (f σ⁻¹)
  invFun f σ := (integerRingModMaximalIdealAddEquivResidue K).symm (f σ⁻¹)
  left_inv := by
    intro f
    funext σ
    simp
  right_inv := by
    intro f
    funext σ
    simp
  map_add' := by
    intro f g
    funext σ
    simp

omit [FiniteDimensional K L] [IsGalois K L] in
/-- The inverse-index equivalence evaluates a residue function at the inverse Galois element. -/
@[simp]
theorem chosenNormalBasisPiResidueInverseIndexAddEquiv_apply
    (f : Gal(L / K) → (𝒪[K] ⧸ (𝓂[K] : Ideal 𝒪[K])))
    (σ : Gal(L/K)) :
    chosenNormalBasisPiResidueInverseIndexAddEquiv K L f σ =
      integerRingModMaximalIdealAddEquivResidue K (f σ⁻¹) :=
  rfl

/-- The honest additive normal-basis model of the lattice graded piece
`π_K^n M / π_K^(n+1) M` as the right-regular function module over the residue
field. -/
noncomputable def chosenNormalBasisLatticeSuccQuotRightRegularAddEquiv (n : Nat) :
    chosenNormalBasisLatticeSuccQuot K L n ≃+ (Gal(L / K) → 𝓀[K]) :=
  (chosenNormalBasisLatticeSuccQuotToIntegerLatticeQuotLinearEquiv K L n).toAddEquiv.trans
    ((chosenNormalBasisIntegerLatticeQuotCoordinateQuotLinearEquiv K L).toAddEquiv.trans
      ((chosenNormalBasisCoordinateQuotPiLinearEquiv K L).toAddEquiv.trans
        (chosenNormalBasisPiResidueInverseIndexAddEquiv K L)))

/-- Computes right-regular residue coordinates of a scaled lattice representative. -/
@[simp]
theorem chosenNormalBasisLatticeSuccQuotRightRegularAddEquiv_mk_mulPow
    (n : Nat) (x : chosenNormalBasisIntegerLattice K L) (σ : Gal(L/K)) :
    chosenNormalBasisLatticeSuccQuotRightRegularAddEquiv K L n
        (chosenNormalBasisLatticeSuccQuotMk K L n
          (chosenNormalBasisIntegerLatticeMulPowLinearEquiv K L n x)) σ =
      IsLocalRing.residue 𝒪[K]
        ((chosenNormalBasisIntegerLatticeBasis K L).equivFun x σ⁻¹) := by
  rw [chosenNormalBasisLatticeSuccQuotRightRegularAddEquiv]
  simp [chosenNormalBasisIntegerLatticeQuotCoordinateQuotLinearEquiv,
    chosenNormalBasisCoordinateQuotPiLinearEquiv,
    chosenNormalBasisPiResidueInverseIndexAddEquiv]
  change integerRingModMaximalIdealAddEquivResidue K
      (Ideal.Quotient.mk (𝓂[K] : Ideal 𝒪[K])
        ((chosenNormalBasisIntegerLatticeBasis K L).equivFun x σ⁻¹)) = _
  rfl

/-! ### The actual `Gal(L / K)` action and right-regular equivariance -/

/-- The actual Galois action restricted to the stable normal-basis lattice. -/
def galoisGroupChosenNormalBasisIntegerLatticeLinearEquiv (τ : Gal(L/K)) :
    chosenNormalBasisIntegerLattice K L ≃ₗ[𝒪[K]]
      chosenNormalBasisIntegerLattice K L where
  toFun x := ⟨τ (x : L),
    galoisGroup_apply_mem_chosenNormalBasisIntegerLattice (K := K) (L := L) τ x.2⟩
  invFun x := ⟨τ⁻¹ (x : L),
    galoisGroup_apply_mem_chosenNormalBasisIntegerLattice (K := K) (L := L) τ⁻¹ x.2⟩
  left_inv x := by
    apply Subtype.ext
    exact τ.symm_apply_apply (x : L)
  right_inv x := by
    apply Subtype.ext
    exact τ.apply_symm_apply (x : L)
  map_add' x y := by
    apply Subtype.ext
    exact map_add τ (x : L) (y : L)
  map_smul' a x := by
    apply Subtype.ext
    have ha : τ (algebraMap 𝒪[K] L a) = algebraMap 𝒪[K] L a := by
      change τ (algebraMap K L (a : K)) = algebraMap K L (a : K)
      exact τ.commutes (a : K)
    change τ (((a • x : chosenNormalBasisIntegerLattice K L) : L)) =
      ((a • (⟨τ (x : L), galoisGroup_apply_mem_chosenNormalBasisIntegerLattice
        (K := K) (L := L) τ x.2⟩ : chosenNormalBasisIntegerLattice K L) :
          chosenNormalBasisIntegerLattice K L) : L)
    rw [Submodule.coe_smul, Submodule.coe_smul]
    rw [Algebra.smul_def, Algebra.smul_def]
    rw [map_mul, ha]

omit [TopologicalSpace K] [IsNonarchimedeanLocalField K] in
/-- The restricted lattice equivalence agrees with the ambient Galois action. -/
@[simp]
theorem galoisGroupChosenNormalBasisIntegerLatticeLinearEquiv_apply_coe
    (τ : Gal(L/K)) (x : chosenNormalBasisIntegerLattice K L) :
    ((galoisGroupChosenNormalBasisIntegerLatticeLinearEquiv K L τ x :
      chosenNormalBasisIntegerLattice K L) : L) = τ (x : L) :=
  rfl

omit [TopologicalSpace K] [IsNonarchimedeanLocalField K] in
/-- The identity Galois element acts trivially on the normal-basis lattice. -/
@[simp]
theorem galoisGroupChosenNormalBasisIntegerLatticeLinearEquiv_one_apply
    (x : chosenNormalBasisIntegerLattice K L) :
    galoisGroupChosenNormalBasisIntegerLatticeLinearEquiv K L 1 x = x := by
  apply Subtype.ext
  rfl

omit [TopologicalSpace K] [IsNonarchimedeanLocalField K] in
/-- Multiplication in the Galois group acts by composition on the normal-basis lattice. -/
@[simp]
theorem galoisGroupChosenNormalBasisIntegerLatticeLinearEquiv_mul_apply
    (τ υ : Gal(L/K)) (x : chosenNormalBasisIntegerLattice K L) :
    galoisGroupChosenNormalBasisIntegerLatticeLinearEquiv K L (τ * υ) x =
      galoisGroupChosenNormalBasisIntegerLatticeLinearEquiv K L τ
        (galoisGroupChosenNormalBasisIntegerLatticeLinearEquiv K L υ x) := by
  apply Subtype.ext
  rfl

omit [TopologicalSpace K] [IsNonarchimedeanLocalField K] in

/-- Normal-basis lattice coordinates obey the left-regular rule before the
inverse-index reindexing. -/
theorem chosenNormalBasisIntegerLatticeBasis_equivFun_galoisGroup
    (τ σ : Gal(L/K)) (x : chosenNormalBasisIntegerLattice K L) :
    (chosenNormalBasisIntegerLatticeBasis K L).equivFun
        (galoisGroupChosenNormalBasisIntegerLatticeLinearEquiv K L τ x) σ =
      (chosenNormalBasisIntegerLatticeBasis K L).equivFun x (τ⁻¹ * σ) := by
  let b := chosenNormalBasisIntegerLatticeBasis K L
  let f := galoisGroupChosenNormalBasisIntegerLatticeLinearEquiv K L τ
  let e : Gal(L / K) ≃ Gal(L / K) := Equiv.mulLeft τ⁻¹
  have hbmap : b.map f = b.reindex e := by
    ext ρ
    rw [Module.Basis.map_apply, Module.Basis.reindex_apply]
    have he : e.symm ρ = τ * ρ := by
      simp [e]
    rw [he]
    simp only [f, b, galoisGroupChosenNormalBasisIntegerLatticeLinearEquiv_apply_coe,
      chosenNormalBasisIntegerLatticeBasis_apply]
    rw [IsGalois.normalBasis_apply (K := K) (L := L) (τ * ρ),
      IsGalois.normalBasis_apply (K := K) (L := L) ρ]
    rfl
  have hcoord (ρ : Gal(L / K)) :
      b.equivFun (f x) (τ * ρ) = b.equivFun x ρ := by
    calc
      b.equivFun (f x) (τ * ρ) =
          (b.reindex e).equivFun (f x) ρ := by
            rw [Module.Basis.equivFun_apply, Module.Basis.equivFun_apply,
              Module.Basis.repr_reindex_apply]
            simp [e]
      _ = (b.map f).equivFun (f x) ρ := by rw [hbmap]
      _ = b.equivFun x ρ := by
        rw [Module.Basis.map_equivFun]
        simp [f]
  simpa using hcoord (τ⁻¹ * σ)

/-- The lattice uniformizer submodule is stable under every Galois automorphism. -/
theorem chosenNormalBasisIntegerLatticeUniformizerSubmodule_map_galoisGroup
    (τ : Gal(L/K)) :
    (chosenNormalBasisIntegerLatticeUniformizerSubmodule K L).map
        (galoisGroupChosenNormalBasisIntegerLatticeLinearEquiv K L τ :
          chosenNormalBasisIntegerLattice K L →ₗ[𝒪[K]]
            chosenNormalBasisIntegerLattice K L) =
      chosenNormalBasisIntegerLatticeUniformizerSubmodule K L := by
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    rcases (mem_chosenBaseUniformizerPowSubmodule_iff
      (K := K) (L := L) 1 (chosenNormalBasisIntegerLattice K L) (y : L)).1 hy with
      ⟨z, hz, hzy⟩
    refine (mem_chosenBaseUniformizerPowSubmodule_iff
      (K := K) (L := L) 1 (chosenNormalBasisIntegerLattice K L) _).2
      ⟨τ z, galoisGroup_apply_mem_chosenNormalBasisIntegerLattice
        (K := K) (L := L) τ hz, ?_⟩
    change algebraMap 𝒪[K] L (chosenIntegerRingUniformizer K ^ 1) * τ z = τ (y : L)
    rw [← hzy, map_mul]
    congr 1
    change algebraMap K L
        ((chosenIntegerRingUniformizer K ^ 1 : 𝒪[K]) : K) =
      τ (algebraMap K L
        ((chosenIntegerRingUniformizer K ^ 1 : 𝒪[K]) : K))
    exact (τ.commutes _).symm
  · intro hx
    let y := galoisGroupChosenNormalBasisIntegerLatticeLinearEquiv K L τ⁻¹ x
    have hy : y ∈ chosenNormalBasisIntegerLatticeUniformizerSubmodule K L := by
      rcases (mem_chosenBaseUniformizerPowSubmodule_iff
        (K := K) (L := L) 1 (chosenNormalBasisIntegerLattice K L) (x : L)).1 hx with
        ⟨z, hz, hzx⟩
      refine (mem_chosenBaseUniformizerPowSubmodule_iff
        (K := K) (L := L) 1 (chosenNormalBasisIntegerLattice K L) (y : L)).2
        ⟨τ⁻¹ z, galoisGroup_apply_mem_chosenNormalBasisIntegerLattice
          (K := K) (L := L) τ⁻¹ hz, ?_⟩
      change algebraMap 𝒪[K] L (chosenIntegerRingUniformizer K ^ 1) * τ⁻¹ z =
        τ⁻¹ (x : L)
      rw [← hzx, map_mul]
      congr 1
      change algebraMap K L
          ((chosenIntegerRingUniformizer K ^ 1 : 𝒪[K]) : K) =
        τ⁻¹ (algebraMap K L
          ((chosenIntegerRingUniformizer K ^ 1 : 𝒪[K]) : K))
      exact ((τ⁻¹).commutes _).symm
    refine ⟨y, hy, ?_⟩
    apply Subtype.ext
    exact τ.apply_symm_apply (x : L)

/-- The actual Galois action on the fixed quotient `M / π_K M`. -/
noncomputable def galoisGroupChosenNormalBasisIntegerLatticeQuotLinearEquiv
    (τ : Gal(L/K)) :
    (chosenNormalBasisIntegerLattice K L ⧸
        chosenNormalBasisIntegerLatticeUniformizerSubmodule K L) ≃ₗ[𝒪[K]]
      (chosenNormalBasisIntegerLattice K L ⧸
        chosenNormalBasisIntegerLatticeUniformizerSubmodule K L) :=
  Submodule.Quotient.equiv
    (chosenNormalBasisIntegerLatticeUniformizerSubmodule K L)
    (chosenNormalBasisIntegerLatticeUniformizerSubmodule K L)
    (galoisGroupChosenNormalBasisIntegerLatticeLinearEquiv K L τ)
    (chosenNormalBasisIntegerLatticeUniformizerSubmodule_map_galoisGroup K L τ)

/-- The induced quotient action sends a class to the class of its Galois transform. -/
@[simp]
theorem galoisGroupChosenNormalBasisIntegerLatticeQuotLinearEquiv_mk
    (τ : Gal(L/K)) (x : chosenNormalBasisIntegerLattice K L) :
    galoisGroupChosenNormalBasisIntegerLatticeQuotLinearEquiv K L τ
        (Submodule.Quotient.mk x) =
      Submodule.Quotient.mk
        (galoisGroupChosenNormalBasisIntegerLatticeLinearEquiv K L τ x) :=
  rfl

/-- The actual Galois action on `π_K^n M / π_K^(n+1) M`, transported through
removal of the common factor `π_K^n`. -/
noncomputable def galoisGroupChosenNormalBasisLatticeSuccQuotAddEquiv
    (n : Nat) (τ : Gal(L/K)) :
    chosenNormalBasisLatticeSuccQuot K L n ≃+
      chosenNormalBasisLatticeSuccQuot K L n :=
  (chosenNormalBasisLatticeSuccQuotToIntegerLatticeQuotLinearEquiv K L n).toAddEquiv.trans
    ((galoisGroupChosenNormalBasisIntegerLatticeQuotLinearEquiv K L τ).toAddEquiv.trans
      (chosenNormalBasisLatticeSuccQuotToIntegerLatticeQuotLinearEquiv K L n).symm.toAddEquiv)

/-- The transported Galois action transforms the integral part of a scaled representative. -/
@[simp]
theorem galoisGroupChosenNormalBasisLatticeSuccQuotAddEquiv_mk_mulPow
    (n : Nat) (τ : Gal(L/K)) (x : chosenNormalBasisIntegerLattice K L) :
    galoisGroupChosenNormalBasisLatticeSuccQuotAddEquiv K L n τ
        (chosenNormalBasisLatticeSuccQuotMk K L n
          (chosenNormalBasisIntegerLatticeMulPowLinearEquiv K L n x)) =
      chosenNormalBasisLatticeSuccQuotMk K L n
        (chosenNormalBasisIntegerLatticeMulPowLinearEquiv K L n
          (galoisGroupChosenNormalBasisIntegerLatticeLinearEquiv K L τ x)) := by
  let e := chosenNormalBasisLatticeSuccQuotToIntegerLatticeQuotLinearEquiv K L n
  change e.symm
      (galoisGroupChosenNormalBasisIntegerLatticeQuotLinearEquiv K L τ
        (e (chosenNormalBasisLatticeSuccQuotMk K L n
          (chosenNormalBasisIntegerLatticeMulPowLinearEquiv K L n x)))) = _
  rw [chosenNormalBasisLatticeSuccQuotToIntegerLatticeQuotLinearEquiv_mk_mulPow,
    galoisGroupChosenNormalBasisIntegerLatticeQuotLinearEquiv_mk]
  apply e.injective
  rw [LinearEquiv.apply_symm_apply,
    chosenNormalBasisLatticeSuccQuotToIntegerLatticeQuotLinearEquiv_mk_mulPow]

/-- Removing the common uniformizer power intertwines the two quotient Galois actions. -/
@[simp]
theorem chosenNormalBasisLatticeSuccQuotToIntegerLatticeQuotLinearEquiv_galoisGroup
    (n : Nat) (τ : Gal(L/K))
    (q : chosenNormalBasisLatticeSuccQuot K L n) :
    chosenNormalBasisLatticeSuccQuotToIntegerLatticeQuotLinearEquiv K L n
        (galoisGroupChosenNormalBasisLatticeSuccQuotAddEquiv K L n τ q) =
      galoisGroupChosenNormalBasisIntegerLatticeQuotLinearEquiv K L τ
        (chosenNormalBasisLatticeSuccQuotToIntegerLatticeQuotLinearEquiv K L n q) := by
  let e := chosenNormalBasisLatticeSuccQuotToIntegerLatticeQuotLinearEquiv K L n
  change e (e.symm
    (galoisGroupChosenNormalBasisIntegerLatticeQuotLinearEquiv K L τ (e q))) = _
  exact e.apply_symm_apply _

/-- On representatives, the transported action is multiplication by `π_K^n`
followed by the actual field automorphism. -/
theorem chosenNormalBasisIntegerLatticeMulPowLinearEquiv_galoisGroup_apply_coe
    (n : Nat) (τ : Gal(L/K)) (x : chosenNormalBasisIntegerLattice K L) :
    ((chosenNormalBasisIntegerLatticeMulPowLinearEquiv K L n
      (galoisGroupChosenNormalBasisIntegerLatticeLinearEquiv K L τ x) :
        chosenBaseUniformizerPowSubmodule K L n
          (chosenNormalBasisIntegerLattice K L)) : L) =
      τ ((chosenNormalBasisIntegerLatticeMulPowLinearEquiv K L n x :
        chosenBaseUniformizerPowSubmodule K L n
          (chosenNormalBasisIntegerLattice K L)) : L) := by
  change algebraMap 𝒪[K] L (chosenIntegerRingUniformizer K ^ n) * τ (x : L) =
    τ (algebraMap 𝒪[K] L (chosenIntegerRingUniformizer K ^ n) * (x : L))
  rw [map_mul]
  congr 1
  change algebraMap K L ((chosenIntegerRingUniformizer K ^ n : 𝒪[K]) : K) =
    τ (algebraMap K L ((chosenIntegerRingUniformizer K ^ n : 𝒪[K]) : K))
  exact (τ.commutes _).symm

/-- The additive `Gal(L / K)`-action on the lattice graded piece induced by
the actual action on the extension field. -/
@[implicit_reducible]
noncomputable def galoisGroupChosenNormalBasisLatticeSuccQuotDistribMulAction
    (n : Nat) :
    DistribMulAction Gal(L / K) (chosenNormalBasisLatticeSuccQuot K L n) where
  smul τ q := galoisGroupChosenNormalBasisLatticeSuccQuotAddEquiv K L n τ q
  one_smul := by
    intro q
    change galoisGroupChosenNormalBasisLatticeSuccQuotAddEquiv K L n 1 q = q
    let e := chosenNormalBasisLatticeSuccQuotToIntegerLatticeQuotLinearEquiv K L n
    apply e.injective
    rw [chosenNormalBasisLatticeSuccQuotToIntegerLatticeQuotLinearEquiv_galoisGroup]
    refine Submodule.Quotient.induction_on
      (chosenNormalBasisIntegerLatticeUniformizerSubmodule K L) (e q) ?_
    intro x
    rw [galoisGroupChosenNormalBasisIntegerLatticeQuotLinearEquiv_mk,
      galoisGroupChosenNormalBasisIntegerLatticeLinearEquiv_one_apply]
  mul_smul := by
    intro τ υ q
    change galoisGroupChosenNormalBasisLatticeSuccQuotAddEquiv K L n (τ * υ) q =
      galoisGroupChosenNormalBasisLatticeSuccQuotAddEquiv K L n τ
        (galoisGroupChosenNormalBasisLatticeSuccQuotAddEquiv K L n υ q)
    let e := chosenNormalBasisLatticeSuccQuotToIntegerLatticeQuotLinearEquiv K L n
    apply e.injective
    rw [chosenNormalBasisLatticeSuccQuotToIntegerLatticeQuotLinearEquiv_galoisGroup,
      chosenNormalBasisLatticeSuccQuotToIntegerLatticeQuotLinearEquiv_galoisGroup,
      chosenNormalBasisLatticeSuccQuotToIntegerLatticeQuotLinearEquiv_galoisGroup]
    refine Submodule.Quotient.induction_on
      (chosenNormalBasisIntegerLatticeUniformizerSubmodule K L) (e q) ?_
    intro x
    rw [galoisGroupChosenNormalBasisIntegerLatticeQuotLinearEquiv_mk,
      galoisGroupChosenNormalBasisIntegerLatticeQuotLinearEquiv_mk,
      galoisGroupChosenNormalBasisIntegerLatticeQuotLinearEquiv_mk,
      galoisGroupChosenNormalBasisIntegerLatticeLinearEquiv_mul_apply]
  smul_zero := by
    intro τ
    exact (galoisGroupChosenNormalBasisLatticeSuccQuotAddEquiv K L n τ).map_zero
  smul_add := by
    intro τ q r
    exact (galoisGroupChosenNormalBasisLatticeSuccQuotAddEquiv K L n τ).map_add q r

/-- The graded-piece scalar action applies the Galois automorphism to a scaled representative. -/
@[simp]
theorem galoisGroupChosenNormalBasisLatticeSuccQuotDistribMulAction_smul_mk_mulPow
    (n : Nat) (τ : Gal(L/K)) (x : chosenNormalBasisIntegerLattice K L) :
    letI := galoisGroupChosenNormalBasisLatticeSuccQuotDistribMulAction K L n
    τ • chosenNormalBasisLatticeSuccQuotMk K L n
        (chosenNormalBasisIntegerLatticeMulPowLinearEquiv K L n x) =
      chosenNormalBasisLatticeSuccQuotMk K L n
        (chosenNormalBasisIntegerLatticeMulPowLinearEquiv K L n
          (galoisGroupChosenNormalBasisIntegerLatticeLinearEquiv K L τ x)) :=
  galoisGroupChosenNormalBasisLatticeSuccQuotAddEquiv_mk_mulPow K L n τ x

/-- The inverse-indexed residue coordinates intertwine the Galois
action with the pointwise right-regular action. -/
theorem chosenNormalBasisLatticeSuccQuotRightRegularAddEquiv_commutes
    (n : Nat) (τ : Gal(L / K))
    (q : chosenNormalBasisLatticeSuccQuot K L n) (σ : Gal(L / K)) :
    letI := galoisGroupChosenNormalBasisLatticeSuccQuotDistribMulAction K L n
    chosenNormalBasisLatticeSuccQuotRightRegularAddEquiv K L n (τ • q) σ =
      chosenNormalBasisLatticeSuccQuotRightRegularAddEquiv K L n q (σ * τ) := by
  let := galoisGroupChosenNormalBasisLatticeSuccQuotDistribMulAction K L n
  refine chosenNormalBasisLatticeSuccQuot.inductionOn K L n
    (motive := fun q =>
      chosenNormalBasisLatticeSuccQuotRightRegularAddEquiv K L n (τ • q) σ =
        chosenNormalBasisLatticeSuccQuotRightRegularAddEquiv K L n q (σ * τ))
    q ?_
  intro z
  let x : chosenNormalBasisIntegerLattice K L :=
    (chosenNormalBasisIntegerLatticeMulPowLinearEquiv K L n).symm z
  have hz : chosenNormalBasisIntegerLatticeMulPowLinearEquiv K L n x = z :=
    (chosenNormalBasisIntegerLatticeMulPowLinearEquiv K L n).apply_symm_apply z
  rw [← hz,
    galoisGroupChosenNormalBasisLatticeSuccQuotDistribMulAction_smul_mk_mulPow,
    chosenNormalBasisLatticeSuccQuotRightRegularAddEquiv_mk_mulPow,
    chosenNormalBasisLatticeSuccQuotRightRegularAddEquiv_mk_mulPow,
    chosenNormalBasisIntegerLatticeBasis_equivFun_galoisGroup]
  congr 1

/-- Herbrand `H⁰` vanishes on every additive normal-basis lattice graded
piece. -/
theorem chosenNormalBasisLatticeSuccQuot_herbrandH0_subsingleton (n : Nat) :
    letI := galoisGroupChosenNormalBasisLatticeSuccQuotDistribMulAction K L n
    letI :=
      CyclicCohomology.ProfiniteCohomology.Herbrand.multiplicativeMulDistribMulActionOfDistribMulAction
        Gal(L / K) (chosenNormalBasisLatticeSuccQuot K L n)
    Subsingleton (CyclicCohomology.ProfiniteCohomology.Herbrand.HerbrandH0
      Gal(L / K) (Multiplicative (chosenNormalBasisLatticeSuccQuot K L n))) := by
  let := galoisGroupChosenNormalBasisLatticeSuccQuotDistribMulAction K L n
  exact
    CyclicCohomology.ProfiniteCohomology.Herbrand.herbrandH0_subsingleton_of_addEquiv_rightRegularFunction
      (G := Gal(L / K)) (M := chosenNormalBasisLatticeSuccQuot K L n) (D := 𝓀[K])
      (chosenNormalBasisLatticeSuccQuotRightRegularAddEquiv K L n)
      (chosenNormalBasisLatticeSuccQuotRightRegularAddEquiv_commutes K L n)

/-- Cyclic Herbrand `H⁻¹` vanishes on every additive normal-basis lattice
graded piece. -/
theorem chosenNormalBasisLatticeSuccQuot_herbrandHMinusOne_subsingleton
    (n : Nat) (τ : Gal(L/K))
    (hgen : ∀ g : Gal(L / K), g ∈ Subgroup.zpowers τ) :
    letI := galoisGroupChosenNormalBasisLatticeSuccQuotDistribMulAction K L n
    letI :=
      CyclicCohomology.ProfiniteCohomology.Herbrand.multiplicativeMulDistribMulActionOfDistribMulAction
        Gal(L / K) (chosenNormalBasisLatticeSuccQuot K L n)
    Subsingleton (CyclicCohomology.ProfiniteCohomology.Herbrand.HerbrandHMinusOne
      Gal(L / K) (Multiplicative (chosenNormalBasisLatticeSuccQuot K L n)) τ) := by
  let := galoisGroupChosenNormalBasisLatticeSuccQuotDistribMulAction K L n
  exact
    CyclicCohomology.ProfiniteCohomology.Herbrand.herbrandHMinusOne_subsingleton_of_addEquiv_rightRegularFunction
      (G := Gal(L / K)) (M := chosenNormalBasisLatticeSuccQuot K L n) (D := 𝓀[K])
      τ hgen (chosenNormalBasisLatticeSuccQuotRightRegularAddEquiv K L n)
      (chosenNormalBasisLatticeSuccQuotRightRegularAddEquiv_commutes K L n)

end GradedCoordinates

end
end LocalClassFieldTheory
