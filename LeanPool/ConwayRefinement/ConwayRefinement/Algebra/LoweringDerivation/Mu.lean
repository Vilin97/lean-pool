/-
Copyright (c) 2026 Dan Abramov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dan Abramov
-/
module

public import LeanPool.ConwayRefinement.ConwayRefinement.Algebra.LoweringDerivation.Grading
public import LeanPool.ConwayRefinement.ConwayRefinement.Order.Filter.FunAtZeroMinus

import Mathlib.LinearAlgebra.TensorProduct.RightExactness
import Mathlib.LinearAlgebra.TensorProduct.Finiteness

/-!
# Lowering derivations and the maps `μ_j`

A *lowering derivation* of a `NatOrdinal`-graded algebra `A` (Lean `R`) over a field `E` is an
`E`-linear derivation `∂ : A → Fun_{0⁻}(A)` with values in functions at `0⁻` which lowers the
degree by one — `∂(A_{α+1}) ⊆ Fun_{0⁻}(A_α)`, and `∂(A_α) = 0` for `α` zero or a limit — and is
injective on every `A_{α+1}`. The Lean variable for `∂` is `Δ`.

For such a derivation `∂(I_{≥j}) ⊆ Fun_{0⁻}(I_{≥j-1})` for `j ≥ 1`, and the maps

`μ_j : A_j ⊗_E A/I → I_{≥j}/I_{≥j+1}`, `B ⊗ π(C) ↦ BC + I_{≥j+1}`,

are injective: for `j = 0` this is `I = ker π`, and the inductive step applies `∂` to a relation
and uses the compatibility `μ_{j-1}((∂ ⊗ 1) T) = ∂H + I_{≥j}` for `μ_j(T) = H + I_{≥j+1}`. The
maps `μ_j` are also compatible with the action of `A/I` on the second factor, and they are graded:
a homogeneous element of `I_{≥j} ∩ A_δ` has class in `μ_j(A_j ⊗ (A/I)_β)` for the `β` with
`j ⊕ β = δ`, and conversely every such tensor is the class of a homogeneous element of
`I_{≥j} ∩ A_δ`.
-/

universe u v

open scoped DirectSum TensorProduct
open Filter Topology

public noncomputable section

namespace LoweringDerivation

variable {E : Type u} {R : Type v} [Field E] [CommRing R] [Algebra E R]
variable (𝒜 : NatOrdinal → Submodule E R) [GradedAlgebra 𝒜]

/-- The hypothesis `A_0 = E`: every element of degree zero is a scalar. -/
def GradeZeroScalars : Prop := ∀ x ∈ 𝒜 0, ∃ e : E, x = algebraMap E R e

omit [GradedAlgebra 𝒜] in
theorem gradeZeroScalars_iff :
    GradeZeroScalars 𝒜 ↔ ∀ x ∈ 𝒜 0, ∃ e : E, x = algebraMap E R e := Iff.rfl

/-- A lowering derivation `∂` (Lean `Δ`) of `A`: an `E`-linear derivation with values in functions
at `0⁻` (D1), which lowers the degree by one — it carries each `A_{α+1}` into `Fun_{0⁻}(A_α)` and
vanishes on `A_α` for `α` zero or a limit (D2) — and is injective on every `A_{α+1}` (D3). -/
structure IsLoweringDerivation (Δ : R →ₗ[E] FunAtZeroMinus R) : Prop where
  map_mul : ∀ x y : R, Δ (x * y) = Δ x * (y : FunAtZeroMinus R) + (x : FunAtZeroMinus R) * Δ y
  mem_lower : ∀ {α : NatOrdinal}, 0 < α.constantCoeff → ∀ {x : R}, x ∈ 𝒜 α →
    Δ x ∈ funAtZeroMinusSubmodule (𝒜 (α.removeNat 1))
  eq_zero : ∀ {α : NatOrdinal}, α.constantCoeff = 0 → ∀ {x : R}, x ∈ 𝒜 α → Δ x = 0
  injective : ∀ {α : NatOrdinal}, 0 < α.constantCoeff → ∀ {x : R}, x ∈ 𝒜 α → Δ x = 0 → x = 0

variable {𝒜}
variable {Δ : R →ₗ[E] FunAtZeroMinus R} (hΔ : IsLoweringDerivation 𝒜 Δ)

namespace IsLoweringDerivation

theorem natCast_removeNat_one (j : ℕ) (hj : 1 ≤ j) :
    (j : NatOrdinal).removeNat 1 = ((j - 1 : ℕ) : NatOrdinal) := by
  have hcoeff : 1 ≤ (j : NatOrdinal).constantCoeff := by
    rwa [NatOrdinal.constantCoeff_natCast]
  symm
  apply (NatOrdinal.eq_removeNat_iff_add_natCast_eq hcoeff).mpr
  rw [← Nat.cast_add, Nat.sub_add_cancel hj]

theorem natCast_constantCoeff_pos (j : ℕ) (hj : 1 ≤ j) :
    0 < (j : NatOrdinal).constantCoeff := by
  rw [NatOrdinal.constantCoeff_natCast]
  exact hj

include hΔ

omit [GradedAlgebra 𝒜] in
theorem mem_lower_natCast {j : ℕ} (hj : 1 ≤ j) {x : R} (hx : x ∈ 𝒜 (j : NatOrdinal)) :
    Δ x ∈ funAtZeroMinusSubmodule (𝒜 ((j - 1 : ℕ) : NatOrdinal)) := by
  rw [← natCast_removeNat_one j hj]
  exact hΔ.mem_lower (natCast_constantCoeff_pos j hj) hx

omit [GradedAlgebra 𝒜] in
theorem map_one : Δ 1 = 0 := by
  have h := hΔ.map_mul 1 1
  rw [one_mul] at h
  have h1 : ((1 : R) : FunAtZeroMinus R) = 1 := rfl
  rw [h1, mul_one, one_mul] at h
  exact (add_eq_left.mp h.symm)

end IsLoweringDerivation

/-! ### Functions at `0⁻` with values in an ideal -/

variable (E) in
/-- `Fun_{0⁻}(I)`: the functions at `0⁻` with values in the ideal `I`. -/
abbrev funAtZeroMinusIdeal (I : Ideal R) : Submodule E (FunAtZeroMinus R) :=
  funAtZeroMinusSubmodule (I.restrictScalars E)

theorem coe_mem_funAtZeroMinusIdeal_iff (I : Ideal R) (f : ℝ → R) :
    (f : FunAtZeroMinus R) ∈ funAtZeroMinusIdeal E I ↔ ∀ᶠ γ in 𝓝[<] (0 : ℝ), f γ ∈ I :=
  coe_mem_funAtZeroMinusSubmodule_iff _ f

theorem const_mem_funAtZeroMinusIdeal {I : Ideal R} {x : R} (hx : x ∈ I) :
    (x : FunAtZeroMinus R) ∈ funAtZeroMinusIdeal E I :=
  (coe_mem_funAtZeroMinusIdeal_iff I _).mpr (Eventually.of_forall fun _ ↦ hx)

theorem mul_const_mem_funAtZeroMinusIdeal {I : Ideal R} {g : FunAtZeroMinus R}
    (hg : g ∈ funAtZeroMinusIdeal E I) (y : R) :
    g * (y : FunAtZeroMinus R) ∈ funAtZeroMinusIdeal E I := by
  induction g using Filter.Germ.inductionOn with
  | _ f =>
    rw [coe_mem_funAtZeroMinusIdeal_iff] at hg
    change ((f * fun _ ↦ y : ℝ → R) : FunAtZeroMinus R) ∈ _
    rw [coe_mem_funAtZeroMinusIdeal_iff]
    exact hg.mono fun γ hγ ↦ I.mul_mem_right y hγ

theorem const_mul_mem_funAtZeroMinusIdeal {I : Ideal R} {g : FunAtZeroMinus R}
    (hg : g ∈ funAtZeroMinusIdeal E I) (y : R) :
    (y : FunAtZeroMinus R) * g ∈ funAtZeroMinusIdeal E I := by
  rw [mul_comm]
  exact mul_const_mem_funAtZeroMinusIdeal hg y

theorem mul_mem_funAtZeroMinusIdeal_of_const_mem {I : Ideal R} {y : R} (hy : y ∈ I)
    (g : FunAtZeroMinus R) :
    g * (y : FunAtZeroMinus R) ∈ funAtZeroMinusIdeal E I := by
  induction g using Filter.Germ.inductionOn with
  | _ f =>
    change ((f * fun _ ↦ y : ℝ → R) : FunAtZeroMinus R) ∈ _
    rw [coe_mem_funAtZeroMinusIdeal_iff]
    exact Eventually.of_forall fun γ ↦ I.mul_mem_left (f γ) hy

theorem funAtZeroMinusIdeal_mono {I J : Ideal R} (h : I ≤ J) :
    funAtZeroMinusIdeal E I ≤ funAtZeroMinusIdeal E J :=
  fun _ hg ↦ funAtZeroMinusSubmodule_mono (W := I.restrictScalars E) (W' := J.restrictScalars E)
    (fun _ hx ↦ h hx) hg

omit [GradedAlgebra 𝒜] in
theorem funAtZeroMinusSubmodule_grade_le_funAtZeroMinusIdeal {e j : ℕ} (hje : j ≤ e) :
    funAtZeroMinusSubmodule (𝒜 (e : NatOrdinal)) ≤ funAtZeroMinusIdeal E (idealGE 𝒜 j) :=
  fun _ hg ↦ funAtZeroMinusSubmodule_mono (W := 𝒜 (e : NatOrdinal))
    (W' := (idealGE 𝒜 j).restrictScalars E)
    (fun x hx ↦ (Submodule.restrictScalars_mem E _ x).mpr (mem_idealGE_of_mem 𝒜 hje hx)) hg

namespace IsLoweringDerivation
include hΔ

omit [GradedAlgebra 𝒜] in
/-- The power rule. -/
theorem map_pow_succ (x : R) (n : ℕ) :
    Δ (x ^ (n + 1)) = (n + 1) • (((x ^ n : R) : FunAtZeroMinus R) * Δ x) := by
  induction n with
  | zero =>
    rw [zero_add, pow_one, pow_zero, one_smul]
    change Δ x = (1 : FunAtZeroMinus R) * Δ x
    rw [one_mul]
  | succ n ih =>
    rw [pow_succ, hΔ.map_mul, ih, smul_mul_assoc, mul_assoc]
    have h1 : ((x ^ n : R) : FunAtZeroMinus R) * (x : FunAtZeroMinus R) =
        ((x ^ (n + 1) : R) : FunAtZeroMinus R) := by
      rw [pow_succ]
      rfl
    rw [mul_comm (Δ x) (x : FunAtZeroMinus R), ← mul_assoc, h1, succ_nsmul, succ_nsmul, succ_nsmul]

omit [GradedAlgebra 𝒜] in
/-- `∂(I_{≥j}) ⊆ Fun_{0⁻}(I_{≥j-1})` for `j ≥ 1`. -/
theorem map_mem_funAtZeroMinusIdeal_idealGE {j : ℕ} (hj : 1 ≤ j) {H : R} (hH : H ∈ idealGE 𝒜 j) :
    Δ H ∈ funAtZeroMinusIdeal E (idealGE 𝒜 (j - 1)) := by
  classical
  rw [idealGE_eq_span] at hH
  obtain ⟨n, c, g, rfl⟩ := Submodule.mem_span_set'.mp hH
  rw [map_sum]
  refine Submodule.sum_mem _ fun i _ ↦ ?_
  obtain ⟨e, hje, hge⟩ := (mem_idealGEGenerators_iff 𝒜 j (g i)).mp (g i).2
  rw [smul_eq_mul, hΔ.map_mul]
  refine Submodule.add_mem _ ?_ ?_
  · exact mul_mem_funAtZeroMinusIdeal_of_const_mem
      (mem_idealGE_of_mem 𝒜 (Nat.sub_le j 1 |>.trans hje) hge) _
  · refine const_mul_mem_funAtZeroMinusIdeal ?_ _
    refine funAtZeroMinusSubmodule_grade_le_funAtZeroMinusIdeal (e := e - 1) (by omega) ?_
    exact hΔ.mem_lower_natCast (hj.trans hje) hge

end IsLoweringDerivation

/-! ### The maps `μ_j` -/

section Characteristic

variable (𝒜)

/-- Multiplication by a homogeneous `B ∈ A_j`, descended to a map `A/I → A/I_{≥j+1}`. -/
def muMulLeft (j : ℕ) (a : 𝒜 (j : NatOrdinal)) :
    Fibre 𝒜 →ₗ[E] R ⧸ idealGE 𝒜 (j + 1) :=
  (Submodule.mapQ (fibreIdeal 𝒜) (idealGE 𝒜 (j + 1)) (LinearMap.mulLeft R (a : R))
    fun _ hx ↦ mul_mem_idealGE 𝒜 (mem_idealGE_of_mem 𝒜 le_rfl a.2) hx).restrictScalars E

omit [GradedAlgebra 𝒜] in
theorem fibreMap_eq_mk (b : R) : fibreMap 𝒜 b = Submodule.Quotient.mk b := rfl

theorem muMulLeft_mk (j : ℕ) (a : 𝒜 (j : NatOrdinal)) (b : R) :
    muMulLeft 𝒜 j a (fibreMap 𝒜 b) = Submodule.Quotient.mk ((a : R) * b) := by
  rfl

/-- The bilinear map `A_j × A/I → A/I_{≥j+1}`, `(B, π(C)) ↦ BC + I_{≥j+1}`. -/
def muBilinear (j : ℕ) : 𝒜 (j : NatOrdinal) →ₗ[E] Fibre 𝒜 →ₗ[E] R ⧸ idealGE 𝒜 (j + 1) where
  toFun := muMulLeft 𝒜 j
  map_add' a a' := LinearMap.ext fun c ↦ by
    obtain ⟨b, rfl⟩ := fibreMap_surjective 𝒜 c
    rw [LinearMap.add_apply, muMulLeft_mk, muMulLeft_mk, muMulLeft_mk, Submodule.coe_add,
      add_mul, Submodule.Quotient.mk_add]
  map_smul' e a := LinearMap.ext fun c ↦ by
    obtain ⟨b, rfl⟩ := fibreMap_surjective 𝒜 c
    rw [LinearMap.smul_apply, muMulLeft_mk, muMulLeft_mk, RingHom.id_apply,
      Submodule.coe_smul, Algebra.smul_def, mul_assoc, ← Algebra.smul_def,
      Submodule.Quotient.mk_smul]

/-- The paper's `μ_j : A_j ⊗_E A/I → I_{≥j}/I_{≥j+1}`, `B ⊗ π(C) ↦ BC + I_{≥j+1}`, here with
codomain the quotient `A/I_{≥j+1}`. -/
def mu (j : ℕ) : 𝒜 (j : NatOrdinal) ⊗[E] Fibre 𝒜 →ₗ[E] R ⧸ idealGE 𝒜 (j + 1) :=
  TensorProduct.lift (muBilinear 𝒜 j)

theorem mu_tmul (j : ℕ) (a : 𝒜 (j : NatOrdinal)) (b : R) :
    mu 𝒜 j (a ⊗ₜ[E] fibreMap 𝒜 b) = Submodule.Quotient.mk ((a : R) * b) := by
  rw [mu, TensorProduct.lift.tmul]
  exact muMulLeft_mk 𝒜 j a b

/-- The quotient map `A → A/I_{≥j}`, as an `E`-linear map. -/
def idealGEQuot (j : ℕ) : R →ₗ[E] R ⧸ idealGE 𝒜 j :=
  (idealGE 𝒜 j).mkQ.restrictScalars E

omit [GradedAlgebra 𝒜] in
theorem idealGEQuot_apply (j : ℕ) (x : R) :
    idealGEQuot 𝒜 j x = (Submodule.Quotient.mk x : R ⧸ idealGE 𝒜 j) := (rfl)

omit [GradedAlgebra 𝒜] in
theorem mapLinear_idealGEQuot_coe (j : ℕ) (f : ℝ → R) :
    Filter.Germ.mapLinear (idealGEQuot 𝒜 j) (f : FunAtZeroMinus R) =
      ((fun γ ↦ (Submodule.Quotient.mk (f γ) : R ⧸ idealGE 𝒜 j)) : FunAtZeroMinus _) := by
  rw [Filter.Germ.mapLinear_coe]
  rfl

omit [GradedAlgebra 𝒜] in
theorem mapLinear_idealGEQuot_eq_zero_iff (j : ℕ) (g : FunAtZeroMinus R) :
    Filter.Germ.mapLinear (idealGEQuot 𝒜 j) g = 0 ↔ g ∈ funAtZeroMinusIdeal E (idealGE 𝒜 j) := by
  induction g using Filter.Germ.inductionOn with
  | _ f =>
    rw [mapLinear_idealGEQuot_coe, coe_mem_funAtZeroMinusIdeal_iff,
      show (0 : FunAtZeroMinus (R ⧸ idealGE 𝒜 j)) =
        ((fun _ ↦ (0 : R ⧸ idealGE 𝒜 j) : ℝ → _) : FunAtZeroMinus _) from rfl,
      Filter.Germ.coe_eq]
    exact ⟨fun h ↦ h.mono fun γ hγ ↦ (Submodule.Quotient.mk_eq_zero _).mp hγ,
      fun h ↦ h.mono fun γ hγ ↦ (Submodule.Quotient.mk_eq_zero _).mpr hγ⟩

/-- Compatibility of `μ_j` with the action of `A/I` on the second factor:
`μ_j((1 ⊗ π(B)) T) = μ_j(T) · B`. -/
theorem mu_lTensor_mulLeft (j : ℕ) (B : R) (T : 𝒜 (j : NatOrdinal) ⊗[E] Fibre 𝒜) :
    mu 𝒜 j ((LinearMap.mulLeft E (fibreMap 𝒜 B)).lTensor _ T) =
      mu 𝒜 j T * (Ideal.Quotient.mk (idealGE 𝒜 (j + 1)) B) := by
  induction T using TensorProduct.inductionOn with
  | tmul a c =>
    obtain ⟨b, rfl⟩ := fibreMap_surjective 𝒜 c
    rw [LinearMap.lTensor_tmul, LinearMap.mulLeft_apply, ← map_mul, mu_tmul, mu_tmul]
    change Ideal.Quotient.mk _ ((a : R) * (B * b)) = Ideal.Quotient.mk _ ((a : R) * b) * _
    rw [← map_mul]
    congr 1
    ring
  | add x y hx hy => rw [map_add, map_add, hx, hy, map_add, add_mul]

/-- `μ_j` is onto `I_{≥j}/I_{≥j+1}`: the class of an element of `I_{≥j}` modulo `I_{≥j+1}` is in
the image of `μ_j`. -/
theorem exists_mu_eq {j : ℕ} {H : R} (hH : H ∈ idealGE 𝒜 j) :
    ∃ T : 𝒜 (j : NatOrdinal) ⊗[E] Fibre 𝒜,
      mu 𝒜 j T = (Submodule.Quotient.mk H : R ⧸ idealGE 𝒜 (j + 1)) := by
  classical
  rw [idealGE_eq_span] at hH
  obtain ⟨n, c, g, rfl⟩ := Submodule.mem_span_set'.mp hH
  choose e hje hge using fun i ↦ (mem_idealGEGenerators_iff 𝒜 j (g i)).mp (g i).2
  let a : Fin n → 𝒜 (j : NatOrdinal) := fun i ↦
    if h : e i = j then ⟨g i, h ▸ hge i⟩ else 0
  refine ⟨∑ i ∈ Finset.univ.filter (fun i ↦ e i = j), a i ⊗ₜ[E] fibreMap 𝒜 (c i), ?_⟩
  rw [map_sum, ← Submodule.mkQ_apply, map_sum, Finset.sum_filter]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [Submodule.mkQ_apply, smul_eq_mul]
  by_cases h : e i = j
  · rw [ite_eq_left h, mu_tmul]
    have ha : (a i : R) = g i := by simp [a, h]
    rw [ha, mul_comm]
  · rw [ite_eq_right h, eq_comm, Submodule.Quotient.mk_eq_zero]
    exact Ideal.mul_mem_left _ _ (mem_idealGE_of_mem 𝒜 (by have := hje i; omega) (hge i))

/-- The class of a homogeneous element of `I_{≥j} ∩ A_δ` is in the image of `μ_j` restricted to
`A_j ⊗ (A/I)_β`, where `j ⊕ β = δ` (Lean `β = δ.removeNat j`). -/
theorem exists_mu_lTensor_eq {j : ℕ} {δ : NatOrdinal} {H : R} (hHδ : H ∈ 𝒜 δ)
    (hH : H ∈ idealGE 𝒜 j) :
    ∃ T : 𝒜 (j : NatOrdinal) ⊗[E] fibreGrade 𝒜 (δ.removeNat j),
      mu 𝒜 j ((fibreGrade 𝒜 (δ.removeNat j)).subtype.lTensor _ T) =
        (Submodule.Quotient.mk H : R ⧸ idealGE 𝒜 (j + 1)) := by
  classical
  obtain ⟨κ, _, e, a, b, β, hje, ha, hb, heβ, rfl⟩ := exists_homogeneous_presentation 𝒜 hHδ hH
  have hβ : ∀ k, e k = j → β k = δ.removeNat j := fun k hk ↦ by
    have hc : j ≤ δ.constantCoeff := by
      rw [← heβ k, NatOrdinal.constantCoeff_add, NatOrdinal.constantCoeff_natCast, hk]
      exact Nat.le_add_right _ _
    rw [NatOrdinal.eq_removeNat_iff_add_natCast_eq hc, ← hk, add_comm]
    exact heβ k
  let a' : κ → 𝒜 (j : NatOrdinal) := fun k ↦ if h : e k = j then ⟨a k, h ▸ ha k⟩ else 0
  let b' : κ → fibreGrade 𝒜 (δ.removeNat j) := fun k ↦ if h : e k = j then
    ⟨fibreMap 𝒜 (b k), hβ k h ▸ fibreMap_mem_fibreGrade 𝒜 (hb k)⟩ else 0
  refine ⟨∑ k ∈ Finset.univ.filter (fun k ↦ e k = j), a' k ⊗ₜ[E] b' k, ?_⟩
  rw [map_sum, map_sum, ← Submodule.mkQ_apply, map_sum, Finset.sum_filter]
  refine Finset.sum_congr rfl fun k _ ↦ ?_
  rw [Submodule.mkQ_apply]
  by_cases h : e k = j
  · rw [ite_eq_left h, LinearMap.lTensor_tmul]
    have ha' : (a' k : R) = a k := by simp [a', h]
    have hb' : ((fibreGrade 𝒜 (δ.removeNat j)).subtype (b' k)) = fibreMap 𝒜 (b k) := by
      simp [b', h]
    rw [hb', mu_tmul, ha']
  · rw [ite_eq_right h, eq_comm, Submodule.Quotient.mk_eq_zero]
    exact Ideal.mul_mem_right _ _ (mem_idealGE_of_mem 𝒜 (by have := hje k; omega) (ha k))

/-- Homogeneous lifting: a tensor in `A_j ⊗ (A/I)_β`, `j ⊕ β = α`, is the class modulo `I_{≥j+1}`
of a homogeneous element of `I_{≥j} ∩ A_α`, provided `j` is at most the finite part of `α`. -/
theorem exists_homogeneous_mu_eq {j : ℕ} {α : NatOrdinal} (hj : j ≤ α.constantCoeff)
    (T : 𝒜 (j : NatOrdinal) ⊗[E] fibreGrade 𝒜 (α.removeNat j)) :
    ∃ G ∈ 𝒜 α, G ∈ idealGE 𝒜 j ∧
      mu 𝒜 j ((fibreGrade 𝒜 (α.removeNat j)).subtype.lTensor _ T) =
        (Submodule.Quotient.mk G : R ⧸ idealGE 𝒜 (j + 1)) := by
  classical
  induction T using TensorProduct.inductionOn with
  | tmul a c =>
    obtain ⟨b, hb, hbc⟩ := exists_mem_of_mem_fibreGrade 𝒜 c.2
    refine ⟨(a : R) * b, ?_, Ideal.mul_mem_right _ _ (mem_idealGE_of_mem 𝒜 le_rfl a.2), ?_⟩
    · have h := SetLike.mul_mem_graded a.2 hb
      have hsum : (j : NatOrdinal) + α.removeNat j = α := by
        rw [add_comm]
        exact NatOrdinal.removeNat_add_natCast hj
      rwa [hsum] at h
    · rw [LinearMap.lTensor_tmul, Submodule.subtype_apply, ← hbc]
      exact mu_tmul 𝒜 j a b
  | add x y hx hy =>
    obtain ⟨G, hGα, hGW, hG⟩ := hx
    obtain ⟨G', hG'α, hG'W, hG'⟩ := hy
    exact ⟨G + G', add_mem hGα hG'α, add_mem hGW hG'W, by
      rw [map_add, map_add, hG, hG', Submodule.Quotient.mk_add]⟩

end Characteristic

/-! ### Injectivity of the maps `μ_j` -/

section Injectivity

/-- A finite sum of functions at `0⁻` is the class of the pointwise sum. -/
theorem coe_finset_sum {V : Type*} [AddCommMonoid V] {ι : Type*} (s : Finset ι) (f : ι → ℝ → V) :
    ((fun γ ↦ ∑ i ∈ s, f i γ : ℝ → V) : FunAtZeroMinus V) = ∑ i ∈ s, (f i : FunAtZeroMinus V) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    simp only [Finset.sum_empty]
    rfl
  | insert a s ha ih =>
    simp only [Finset.sum_insert ha]
    rw [← ih]
    rfl

theorem coe_mul_const (f : ℝ → R) (y : R) :
    (f : FunAtZeroMinus R) * (y : FunAtZeroMinus R) =
      ((fun γ ↦ f γ * y : ℝ → R) : FunAtZeroMinus R) := rfl

variable (𝒜) in
/-- The element `1 ∈ A_0`. -/
def gradeZeroOne : 𝒜 ((0 : ℕ) : NatOrdinal) := ⟨1, by simp [SetLike.one_mem_graded 𝒜]⟩

theorem coe_gradeZeroOne : (gradeZeroOne 𝒜 : R) = 1 := (rfl)

namespace IsLoweringDerivation
include hΔ

/-- `∂` on `A_{j+1}`, as a map `A_{j+1} → Fun_{0⁻}(A_j)`. -/
def derivLinear (j : ℕ) :
    𝒜 ((j + 1 : ℕ) : NatOrdinal) →ₗ[E] FunAtZeroMinus (𝒜 (j : NatOrdinal)) :=
  (funAtZeroMinusSubmoduleEquiv (𝒜 (j : NatOrdinal))).symm.toLinearMap.comp
    ((Δ.comp (𝒜 ((j + 1 : ℕ) : NatOrdinal)).subtype).codRestrict _ fun a ↦ by
      simpa using hΔ.mem_lower_natCast (j := j + 1) (Nat.le_add_left 1 j) a.2)

omit [GradedAlgebra 𝒜] in
theorem funAtZeroMinusSubmoduleMap_derivLinear (j : ℕ) (a : 𝒜 ((j + 1 : ℕ) : NatOrdinal)) :
    funAtZeroMinusSubmoduleMap _ (hΔ.derivLinear j a) = Δ a := by
  rw [derivLinear, LinearMap.comp_apply, LinearEquiv.coe_coe,
    ← coe_funAtZeroMinusSubmoduleEquiv_apply, LinearEquiv.apply_symm_apply]
  rfl

omit [GradedAlgebra 𝒜] in
theorem derivLinear_injective (j : ℕ) : Function.Injective (hΔ.derivLinear j) := by
  intro a a' h
  apply Subtype.ext
  refine sub_eq_zero.mp (hΔ.injective (natCast_constantCoeff_pos (j + 1) (Nat.le_add_left 1 j))
    ((𝒜 ((j + 1 : ℕ) : NatOrdinal)).sub_mem a.2 a'.2) ?_)
  rw [map_sub, ← hΔ.funAtZeroMinusSubmoduleMap_derivLinear j,
    ← hΔ.funAtZeroMinusSubmoduleMap_derivLinear j, h, sub_self]

/-- A representative `ℝ → A_j` of `∂(a)` for `a ∈ A_{j+1}`. -/
def derivRep (j : ℕ) (a : 𝒜 ((j + 1 : ℕ) : NatOrdinal)) : ℝ → 𝒜 (j : NatOrdinal) :=
  Quotient.out (hΔ.derivLinear j a)

omit [GradedAlgebra 𝒜] in
theorem coe_derivRep (j : ℕ) (a : 𝒜 ((j + 1 : ℕ) : NatOrdinal)) :
    ((hΔ.derivRep j a : ℝ → 𝒜 (j : NatOrdinal)) : FunAtZeroMinus _) = hΔ.derivLinear j a :=
  Quotient.out_eq _

omit [GradedAlgebra 𝒜] in
theorem map_eq_coe_derivRep (j : ℕ) (a : 𝒜 ((j + 1 : ℕ) : NatOrdinal)) :
    Δ a = ((fun γ ↦ (hΔ.derivRep j a γ : R) : ℝ → R) : FunAtZeroMinus R) := by
  rw [← hΔ.funAtZeroMinusSubmoduleMap_derivLinear j, ← hΔ.coe_derivRep j,
    funAtZeroMinusSubmoduleMap_coe]

omit [GradedAlgebra 𝒜] in
/-- Pointwise form of `∂ ⊗ 1` on a finite sum of pure tensors. -/
theorem funAtZeroMinusTensorId_derivLinear_sum {ι : Type*} (s : Finset ι) (j : ℕ)
    (a : ι → 𝒜 ((j + 1 : ℕ) : NatOrdinal)) (c : ι → Fibre 𝒜) :
    funAtZeroMinusTensorId (hΔ.derivLinear j) (∑ p ∈ s, a p ⊗ₜ[E] c p) =
      ((fun γ ↦ ∑ p ∈ s, hΔ.derivRep j (a p) γ ⊗ₜ[E] c p : ℝ → _) : FunAtZeroMinus _) := by
  rw [map_sum, coe_finset_sum]
  exact Finset.sum_congr rfl fun p _ ↦
    funAtZeroMinusTensorId_tmul_of_eq_coe _ _ _ _ (hΔ.coe_derivRep j (a p)).symm

omit [GradedAlgebra 𝒜] in
/-- `∂` of a finite sum `∑ aₚ bₚ` with `aₚ ∈ A_{j+1}` agrees, modulo `Fun_{0⁻}(I_{≥j+1})`, with
the function `γ ↦ ∑ ∂(aₚ)(γ) bₚ`. -/
theorem map_sum_mul_sub_mem_funAtZeroMinusIdeal {ι : Type*} (s : Finset ι) (j : ℕ)
    (a : ι → 𝒜 ((j + 1 : ℕ) : NatOrdinal)) (b : ι → R) :
    Δ (∑ p ∈ s, (a p : R) * b p) -
      ((fun γ ↦ ∑ p ∈ s, (hΔ.derivRep j (a p) γ : R) * b p : ℝ → R) : FunAtZeroMinus R) ∈
        funAtZeroMinusIdeal E (idealGE 𝒜 (j + 1)) := by
  rw [map_sum]
  simp only [hΔ.map_mul]
  rw [Finset.sum_add_distrib, coe_finset_sum]
  have h2 : ∑ p ∈ s, ((a p : R) : FunAtZeroMinus R) * Δ (b p) ∈
      funAtZeroMinusIdeal E (idealGE 𝒜 (j + 1)) :=
    Submodule.sum_mem _ fun p _ ↦ by
      rw [mul_comm]
      exact mul_mem_funAtZeroMinusIdeal_of_const_mem (mem_idealGE_of_mem 𝒜 le_rfl (a p).2) _
  have h1 : ∑ p ∈ s, Δ (a p : R) * (b p : FunAtZeroMinus R) =
      ∑ p ∈ s, ((fun γ ↦ (hΔ.derivRep j (a p) γ : R) * b p : ℝ → R) : FunAtZeroMinus R) :=
    Finset.sum_congr rfl fun p _ ↦ by rw [hΔ.map_eq_coe_derivRep j (a p), coe_mul_const]
  rw [h1, add_sub_cancel_left]
  exact h2

/-- Compatibility of `μ` with `∂`: if `μ_{j+1}(T) = H + I_{≥j+2}`, then
`μ_j((∂ ⊗ 1) T) = ∂H + I_{≥j+1}` as functions at `0⁻` with values in `A/I_{≥j+1}`. -/
theorem mapLinear_mu_funAtZeroMinusTensorId (j : ℕ) {T : 𝒜 ((j + 1 : ℕ) : NatOrdinal) ⊗[E] Fibre 𝒜}
    {H : R} (hT : mu 𝒜 (j + 1) T = Submodule.Quotient.mk H) :
    Filter.Germ.mapLinear (mu 𝒜 j) (funAtZeroMinusTensorId (hΔ.derivLinear j) T) =
      Filter.Germ.mapLinear (idealGEQuot 𝒜 (j + 1)) (Δ H) := by
  classical
  obtain ⟨S, rfl⟩ := TensorProduct.exists_finset T
  choose b hb using fun p : 𝒜 ((j + 1 : ℕ) : NatOrdinal) × Fibre 𝒜 ↦ fibreMap_surjective 𝒜 p.2
  have hT' : ∑ p ∈ S, p.1 ⊗ₜ[E] p.2 = ∑ p ∈ S, p.1 ⊗ₜ[E] fibreMap 𝒜 (b p) :=
    Finset.sum_congr rfl fun p _ ↦ by rw [hb p]
  rw [hT'] at hT ⊢
  -- `H ≡ ∑ aₚ bₚ` modulo `I_{≥j+2}`
  have hmem : H - ∑ p ∈ S, (p.1 : R) * b p ∈ idealGE 𝒜 (j + 1 + 1) := by
    rw [map_sum] at hT
    simp only [mu_tmul] at hT
    simp only [← Submodule.mkQ_apply, ← map_sum] at hT
    exact (Submodule.Quotient.eq _).mp hT.symm
  have hΔH : Δ H - Δ (∑ p ∈ S, (p.1 : R) * b p) ∈ funAtZeroMinusIdeal E (idealGE 𝒜 (j + 1)) := by
    rw [← map_sub]
    have := hΔ.map_mem_funAtZeroMinusIdeal_idealGE (j := j + 1 + 1) (by omega) hmem
    rwa [Nat.add_sub_cancel] at this
  have hsum := hΔ.map_sum_mul_sub_mem_funAtZeroMinusIdeal S j (fun p ↦ p.1) b
  have hdiff := Submodule.add_mem _ hΔH hsum
  rw [sub_add_sub_cancel, ← mapLinear_idealGEQuot_eq_zero_iff, map_sub, sub_eq_zero] at hdiff
  rw [hdiff, hΔ.funAtZeroMinusTensorId_derivLinear_sum, Filter.Germ.mapLinear_coe,
    mapLinear_idealGEQuot_coe]
  congr 1
  funext γ
  simp only [Function.comp_apply, map_sum, mu_tmul]
  simp only [← Submodule.mkQ_apply, ← map_sum]

/-- The maps `μ_j` are injective. -/
theorem mu_injective (h0 : GradeZeroScalars 𝒜) (j : ℕ) : Function.Injective (mu 𝒜 j) := by
  classical
  induction j with
  | zero =>
    rw [injective_iff_map_eq_zero]
    intro T hT
    obtain ⟨S, rfl⟩ := TensorProduct.exists_finset T
    choose b hb using fun p : 𝒜 ((0 : ℕ) : NatOrdinal) × Fibre 𝒜 ↦ fibreMap_surjective 𝒜 p.2
    choose e he using fun p : 𝒜 ((0 : ℕ) : NatOrdinal) × Fibre 𝒜 ↦
      h0 p.1 (Nat.cast_zero (R := NatOrdinal) ▸ p.1.2)
    have hp : ∀ p : 𝒜 ((0 : ℕ) : NatOrdinal) × Fibre 𝒜, p.1 = e p • gradeZeroOne 𝒜 := fun p ↦
      Subtype.ext (by
        rw [Submodule.coe_smul, coe_gradeZeroOne, ← Algebra.algebraMap_eq_smul_one]
        exact he p)
    have hT' : ∑ p ∈ S, p.1 ⊗ₜ[E] p.2 =
        gradeZeroOne 𝒜 ⊗ₜ[E] fibreMap 𝒜 (∑ p ∈ S, e p • b p) := by
      rw [map_sum, TensorProduct.tmul_sum]
      refine Finset.sum_congr rfl fun p _ ↦ ?_
      rw [hp p, ← hb p, TensorProduct.smul_tmul, map_smul]
    rw [hT'] at hT ⊢
    rw [mu_tmul, Submodule.Quotient.mk_eq_zero, coe_gradeZeroOne, one_mul, zero_add] at hT
    rw [(fibreMap_eq_zero_iff 𝒜 _).mpr hT, TensorProduct.tmul_zero]
  | succ j ih =>
    rw [injective_iff_map_eq_zero]
    intro T hT
    -- `∂H + I_{≥j+1} = 0` for `H = 0` representing `μ_{j+1}(T) = 0`
    have h := hΔ.mapLinear_mu_funAtZeroMinusTensorId j (H := 0)
      (by rw [hT, Submodule.Quotient.mk_zero])
    rw [map_zero, map_zero] at h
    have hzero : funAtZeroMinusTensorId (hΔ.derivLinear j) T = 0 :=
      Filter.Germ.mapLinear_injective (mu 𝒜 j) ih (by rw [h, map_zero])
    exact funAtZeroMinusTensorId_injective_of_injective (E := Fibre 𝒜) _
      (hΔ.derivLinear_injective j) (by rw [hzero, map_zero])

end IsLoweringDerivation

end Injectivity

end LoweringDerivation
