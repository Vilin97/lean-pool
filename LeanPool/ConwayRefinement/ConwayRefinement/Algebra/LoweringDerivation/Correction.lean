/-
Copyright (c) 2026 Dan Abramov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dan Abramov
-/
module

public import LeanPool.ConwayRefinement.ConwayRefinement.Algebra.LoweringDerivation.Mu

import LeanPool.ConwayRefinement.ConwayRefinement.Algebra.GradedRing.HomogeneousZeroDivisors
import Mathlib.Algebra.Module.Torsion.Field
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.RingTheory.Flat.Basic
import Mathlib.Tactic.LinearCombination

/-!
# The correction argument: `A/I` is a domain

Let `A` (Lean `R`) be a `NatOrdinal`-graded domain over a field `E` of characteristic zero with
`A_0 = E` and a lowering derivation `∂` (Lean `Δ`). This file proves that non-zero homogeneous
`ρ, τ ∈ A/I` (the paper's `B, C`) satisfy `ρ^s τ ≠ 0`, hence that `A/I` is a domain.

The proof is a lexicographic induction on `(n, n', s)`, `n, n'` the finite parts of the degrees
`α, β` of `ρ, τ`. Supposing `ρ^(r+1) τ = 0`, one builds homogeneous lifts `x, y` of `ρ, τ` with
`x^(r+1) y ∈ I_{≥j+1}` and `∂x, ∂y ∈ Fun_{0⁻}(I_{≥j})` for `j = 0, …, N`, where `N` is the
smaller of the positive finite parts among `n, n'`. The *correction step* passes from stage `j`
to stage `j + 1`: the Leibniz rule, read through `μ_j` as an identity between tensors,

`(∂ ⊗ 1) ν_{j+1}(x^(r+1) y) = (1 ⊗ m)(ν_j(∂x), ν_j(∂y))`, `m(a, b) = (r+1) ρ^r τ a + ρ^(r+1) b`

(`ν_j(H)` the tensor with `μ_j(ν_j(H)) = H + I_{≥j+1}`), together with the injectivity of
`θ : V ⊗ Fun_{0⁻}(W) → Fun_{0⁻}(V ⊗ W)` and the injectivity of `m` (which is where the induction
hypothesis enters), produces homogeneous corrections `G ∈ I_{≥j+1} ∩ A_α`, `G' ∈ I_{≥j+1} ∩ A_β`
with `(x - G)^(r+1) (y - G') ∈ I_{≥j+2}` and `∂(x - G), ∂(y - G') ∈ Fun_{0⁻}(I_{≥j+1})`. At
stage `N` the derivative of one lift is a function with values in `I_{≥N} ∩ A_{α'}`, `α'` the
degree one below `α`, which vanishes, against the injectivity of `∂` on `A_α`.
-/

universe u v

open scoped DirectSum TensorProduct
open Filter Topology

public noncomputable section

namespace LoweringDerivation

variable {E : Type u} {R : Type v} [Field E] [CommRing R] [Algebra E R]
variable {𝒜 : NatOrdinal → Submodule E R} [GradedAlgebra 𝒜]
variable {Δ : R →ₗ[E] FunAtZeroMinus R} (hΔ : IsLoweringDerivation 𝒜 Δ)

/-! ### Endpoint spaces -/

omit [GradedAlgebra 𝒜] in
theorem lTensor_subtype_lTensor_inclusion {M : Type*} [AddCommGroup M] [Module E M]
    {W W' : Submodule E M} (h : W ≤ W') {U : Type*} [AddCommGroup U] [Module E U]
    (T : U ⊗[E] W) :
    W'.subtype.lTensor U ((Submodule.inclusion h).lTensor U T) = W.subtype.lTensor U T := by
  rw [← LinearMap.comp_apply, ← LinearMap.lTensor_comp, Submodule.subtype_comp_inclusion]

section Endpoint

variable (𝒜)

/-- The paper's `V_α`: for `α = λ + n` with `n > 0`, the degree-`(λ + (n-j-1))` part of `A/I`
(Lean `fibreGrade 𝒜 (α.removeNat (j + 1))`), and `0` when `n = 0`. -/
def endpointSpace (j : ℕ) (α : NatOrdinal) : Submodule E (Fibre 𝒜) :=
  if 0 < α.constantCoeff then fibreGrade 𝒜 (α.removeNat (j + 1)) else ⊥

omit [GradedAlgebra 𝒜] in
theorem endpointSpace_of_pos {j : ℕ} {α : NatOrdinal} (hα : 0 < α.constantCoeff) :
    endpointSpace 𝒜 j α = fibreGrade 𝒜 (α.removeNat (j + 1)) := if_pos hα

omit [GradedAlgebra 𝒜] in
theorem endpointSpace_of_eq_zero {j : ℕ} {α : NatOrdinal} (hα : α.constantCoeff = 0) :
    endpointSpace 𝒜 j α = ⊥ := if_neg (by omega)

omit [GradedAlgebra 𝒜] in
theorem endpointSpace_le (j : ℕ) (α : NatOrdinal) :
    endpointSpace 𝒜 j α ≤ fibreGrade 𝒜 (α.removeNat (j + 1)) := by
  by_cases hα : 0 < α.constantCoeff
  · rw [endpointSpace_of_pos 𝒜 hα]
  · rw [endpointSpace_of_eq_zero 𝒜 (by omega)]
    exact bot_le

omit [GradedAlgebra 𝒜] in
theorem subtype_endpointSpace_of_eq_zero {j : ℕ} {α : NatOrdinal} (hα : α.constantCoeff = 0) :
    (endpointSpace 𝒜 j α).subtype = 0 := by
  ext ⟨x, hx⟩
  rw [endpointSpace_of_eq_zero 𝒜 hα] at hx
  simpa using hx

/-- Homogeneous lifting into `V_α`: a tensor in `A_{j+1} ⊗ V_α` is the class modulo `I_{≥j+2}` of a
homogeneous element of `I_{≥j+1} ∩ A_α`. -/
theorem exists_homogeneous_mu_eq_endpoint {j : ℕ} {α : NatOrdinal}
    (hj : 0 < α.constantCoeff → j + 1 ≤ α.constantCoeff)
    (T : 𝒜 ((j + 1 : ℕ) : NatOrdinal) ⊗[E] endpointSpace 𝒜 j α) :
    ∃ G ∈ 𝒜 α, G ∈ idealGE 𝒜 (j + 1) ∧
      mu 𝒜 (j + 1) ((endpointSpace 𝒜 j α).subtype.lTensor _ T) =
        (Submodule.Quotient.mk G : R ⧸ idealGE 𝒜 (j + 1 + 1)) := by
  by_cases hα : 0 < α.constantCoeff
  · obtain ⟨G, hGα, hGW, hG⟩ := exists_homogeneous_mu_eq 𝒜 (hj hα)
      ((Submodule.inclusion (endpointSpace_le 𝒜 j α)).lTensor _ T)
    refine ⟨G, hGα, hGW, ?_⟩
    rw [← hG, lTensor_subtype_lTensor_inclusion]
  · refine ⟨0, zero_mem _, zero_mem _, ?_⟩
    rw [subtype_endpointSpace_of_eq_zero 𝒜 (by omega), LinearMap.lTensor_zero, LinearMap.zero_apply,
      map_zero, Submodule.Quotient.mk_zero]

end Endpoint

namespace IsLoweringDerivation
include hΔ

/-- For `x ∈ A_α` with `∂x ∈ Fun_{0⁻}(I_{≥j})`, the classes of `∂x` modulo `I_{≥j+1}` have
pointwise representatives in `A_j ⊗ V_α`: the paper's tensor `ν_j(∂x)`. -/
theorem exists_rep_endpoint {j : ℕ} {α : NatOrdinal}
    (hj : 0 < α.constantCoeff → j + 1 ≤ α.constantCoeff) {x : R} (hx : x ∈ 𝒜 α)
    (hΔx : Δ x ∈ funAtZeroMinusIdeal E (idealGE 𝒜 j)) :
    ∃ f : ℝ → R, Δ x = (f : FunAtZeroMinus R) ∧ ∀ γ,
      ∃ T : 𝒜 (j : NatOrdinal) ⊗[E] endpointSpace 𝒜 j α,
        mu 𝒜 j ((endpointSpace 𝒜 j α).subtype.lTensor _ T) =
          (Submodule.Quotient.mk (f γ) : R ⧸ idealGE 𝒜 (j + 1)) := by
  by_cases hα : 0 < α.constantCoeff
  · have hpred := hΔ.mem_lower hα hx
    obtain ⟨f, hf, hfeq⟩ := exists_coe_eq_of_mem_funAtZeroMinusSubmodule _
      (mem_funAtZeroMinusSubmodule_inf _ _ hpred hΔx)
    refine ⟨f, hfeq, fun γ ↦ ?_⟩
    obtain ⟨hf1, hf2⟩ := Submodule.mem_inf.mp (hf γ)
    have hη : (α.removeNat 1).removeNat j = α.removeNat (j + 1) := by
      have := NatOrdinal.removeNat_one_removeNat_pred (delta := α) (j := j + 1)
        (Nat.le_add_left 1 j) (hj hα)
      rwa [Nat.add_sub_cancel] at this
    obtain ⟨T, hT⟩ := exists_mu_lTensor_eq 𝒜 hf1 hf2
    have hle : fibreGrade 𝒜 ((α.removeNat 1).removeNat j) ≤ endpointSpace 𝒜 j α := by
      rw [hη, endpointSpace_of_pos 𝒜 hα]
    refine ⟨(Submodule.inclusion hle).lTensor _ T, ?_⟩
    rw [lTensor_subtype_lTensor_inclusion, hT]
  · refine ⟨fun _ ↦ 0, ?_, fun γ ↦ ⟨0, by simp⟩⟩
    rw [hΔ.eq_zero (by omega) hx]
    rfl

end IsLoweringDerivation

/-! ### The correction map -/

section CorrectionMap

variable (𝒜)

/-- The paper's map `m : V_α ⊕ V_β → A/I`, `(a, b) ↦ z a + w b`. -/
def correctionMap (j : ℕ) (α β : NatOrdinal) (z w : Fibre 𝒜) :
    endpointSpace 𝒜 j α × endpointSpace 𝒜 j β →ₗ[E] Fibre 𝒜 :=
  (LinearMap.mulLeft E z).comp ((endpointSpace 𝒜 j α).subtype.comp (LinearMap.fst E _ _)) +
    (LinearMap.mulLeft E w).comp ((endpointSpace 𝒜 j β).subtype.comp (LinearMap.snd E _ _))

omit [GradedAlgebra 𝒜] in
theorem correctionMap_apply (j : ℕ) (α β : NatOrdinal) (z w : Fibre 𝒜)
    (p : endpointSpace 𝒜 j α × endpointSpace 𝒜 j β) :
    correctionMap 𝒜 j α β z w p = z * p.1 + w * p.2 := (rfl)

omit [GradedAlgebra 𝒜] in
theorem correctionMap_comp_inl (j : ℕ) (α β : NatOrdinal) (z w : Fibre 𝒜) :
    (correctionMap 𝒜 j α β z w).comp (LinearMap.inl E _ _) =
      (LinearMap.mulLeft E z).comp (endpointSpace 𝒜 j α).subtype := by
  ext a
  simp [correctionMap_apply]

omit [GradedAlgebra 𝒜] in
theorem correctionMap_comp_inr (j : ℕ) (α β : NatOrdinal) (z w : Fibre 𝒜) :
    (correctionMap 𝒜 j α β z w).comp (LinearMap.inr E _ _) =
      (LinearMap.mulLeft E w).comp (endpointSpace 𝒜 j β).subtype := by
  ext b
  simp [correctionMap_apply]

omit [GradedAlgebra 𝒜] in
theorem lTensor_fst_lTensor_inl_add_lTensor_inr {U A B : Type*} [AddCommGroup U] [Module E U]
    [AddCommGroup A] [Module E A] [AddCommGroup B] [Module E B] (a : U ⊗[E] A) (b : U ⊗[E] B) :
    (LinearMap.fst E A B).lTensor U
      ((LinearMap.inl E A B).lTensor U a + (LinearMap.inr E A B).lTensor U b) = a := by
  rw [map_add, ← LinearMap.comp_apply (LinearMap.lTensor _ _), ← LinearMap.lTensor_comp,
    LinearMap.fst_comp_inl, LinearMap.lTensor_id, LinearMap.id_apply,
    ← LinearMap.comp_apply (LinearMap.lTensor _ _) (LinearMap.lTensor _ _),
    ← LinearMap.lTensor_comp, LinearMap.fst_comp_inr, LinearMap.lTensor_zero,
    LinearMap.zero_apply, add_zero]

omit [GradedAlgebra 𝒜] in
theorem lTensor_snd_lTensor_inl_add_lTensor_inr {U A B : Type*} [AddCommGroup U] [Module E U]
    [AddCommGroup A] [Module E A] [AddCommGroup B] [Module E B] (a : U ⊗[E] A) (b : U ⊗[E] B) :
    (LinearMap.snd E A B).lTensor U
      ((LinearMap.inl E A B).lTensor U a + (LinearMap.inr E A B).lTensor U b) = b := by
  rw [map_add, ← LinearMap.comp_apply (LinearMap.lTensor _ _), ← LinearMap.lTensor_comp,
    LinearMap.snd_comp_inl, LinearMap.lTensor_zero, LinearMap.zero_apply, zero_add,
    ← LinearMap.comp_apply (LinearMap.lTensor _ _) (LinearMap.lTensor _ _),
    ← LinearMap.lTensor_comp, LinearMap.snd_comp_inr, LinearMap.lTensor_id, LinearMap.id_apply]

end CorrectionMap

namespace IsLoweringDerivation
include hΔ

/-- The Leibniz rule as an identity between tensors,
`(∂ ⊗ 1) ν_{j+1}(x^(r+1) y) = (1 ⊗ m)(ν_j(∂x), ν_j(∂y))` with `m(a, b) = (r+1) ρ^r τ a + ρ^(r+1) b`,
together with representatives: `∂ ⊗ 1` applied to a tensor `T` with
`μ_{j+1}(T) = x^(r+1) y + I_{≥j+2}` is represented by the pointwise images under `1 ⊗ m` of
tensors `t γ` whose two components are classes of representatives `f`, `g` of `∂x` and `∂y`. -/
theorem exists_rep_coordinate_identity (h0 : GradeZeroScalars 𝒜) {j : ℕ} {α β : NatOrdinal}
    (hjα : 0 < α.constantCoeff → j + 1 ≤ α.constantCoeff)
    (hjβ : 0 < β.constantCoeff → j + 1 ≤ β.constantCoeff)
    {x y : R} (hx : x ∈ 𝒜 α) (hy : y ∈ 𝒜 β) (r : ℕ)
    (hΔx : Δ x ∈ funAtZeroMinusIdeal E (idealGE 𝒜 j))
    (hΔy : Δ y ∈ funAtZeroMinusIdeal E (idealGE 𝒜 j))
    {T : 𝒜 ((j + 1 : ℕ) : NatOrdinal) ⊗[E] Fibre 𝒜}
    (hT : mu 𝒜 (j + 1) T = Submodule.Quotient.mk (x ^ (r + 1) * y)) :
    ∃ (f g : ℝ → R)
      (t : ℝ → 𝒜 (j : NatOrdinal) ⊗[E] (endpointSpace 𝒜 j α × endpointSpace 𝒜 j β)),
      Δ x = (f : FunAtZeroMinus R) ∧ Δ y = (g : FunAtZeroMinus R) ∧
      (∀ γ, mu 𝒜 j ((endpointSpace 𝒜 j α).subtype.lTensor _
        ((LinearMap.fst E _ _).lTensor _ (t γ))) = Submodule.Quotient.mk (f γ)) ∧
      (∀ γ, mu 𝒜 j ((endpointSpace 𝒜 j β).subtype.lTensor _
        ((LinearMap.snd E _ _).lTensor _ (t γ))) = Submodule.Quotient.mk (g γ)) ∧
      funAtZeroMinusTensorId (hΔ.derivLinear j) T =
        Filter.Germ.mapLinear ((correctionMap 𝒜 j α β
          (fibreMap 𝒜 ((r + 1) • (x ^ r * y))) (fibreMap 𝒜 (x ^ (r + 1)))).lTensor _)
          (t : FunAtZeroMinus _) := by
  obtain ⟨f, hf, hfT⟩ := hΔ.exists_rep_endpoint hjα hx hΔx
  obtain ⟨g, hg, hgT⟩ := hΔ.exists_rep_endpoint hjβ hy hΔy
  choose tf htf using hfT
  choose tg htg using hgT
  set m := correctionMap 𝒜 j α β (fibreMap 𝒜 ((r + 1) • (x ^ r * y))) (fibreMap 𝒜 (x ^ (r + 1)))
    with hm
  refine ⟨f, g, fun γ ↦ (LinearMap.inl E _ _).lTensor _ (tf γ) +
    (LinearMap.inr E _ _).lTensor _ (tg γ), hf, hg, fun γ ↦ ?_, fun γ ↦ ?_, ?_⟩
  · rw [lTensor_fst_lTensor_inl_add_lTensor_inr, htf]
  · rw [lTensor_snd_lTensor_inl_add_lTensor_inr, htg]
  · apply Filter.Germ.mapLinear_injective (mu 𝒜 j) (mu_injective hΔ h0 j)
    rw [hΔ.mapLinear_mu_funAtZeroMinusTensorId j hT, Filter.Germ.mapLinear_comp,
      Filter.Germ.mapLinear_coe]
    have hΔH : Δ (x ^ (r + 1) * y) =
        ((fun γ ↦ ((r + 1) • (x ^ r * f γ)) * y + x ^ (r + 1) * g γ : ℝ → R) :
          FunAtZeroMinus R) := by
      rw [hΔ.map_mul, hΔ.map_pow_succ, hf, hg]
      rfl
    rw [hΔH, mapLinear_idealGEQuot_coe]
    congr 1
    funext γ
    simp only [Function.comp_apply, LinearMap.comp_apply, map_add]
    rw [← LinearMap.comp_apply (LinearMap.lTensor _ m), ← LinearMap.lTensor_comp, hm,
      correctionMap_comp_inl,
      ← LinearMap.comp_apply (LinearMap.lTensor _ (correctionMap _ _ _ _ _ _)),
      ← LinearMap.lTensor_comp, correctionMap_comp_inr, LinearMap.lTensor_comp,
      LinearMap.lTensor_comp, LinearMap.comp_apply, LinearMap.comp_apply, mu_lTensor_mulLeft,
      mu_lTensor_mulLeft, htf, htg]
    change Ideal.Quotient.mk _ _ = Ideal.Quotient.mk _ (f γ) * Ideal.Quotient.mk _ _ +
      Ideal.Quotient.mk _ (g γ) * Ideal.Quotient.mk _ _
    rw [← RingHom.map_mul, ← RingHom.map_mul, ← RingHom.map_add]
    congr 1
    simp only [nsmul_eq_mul]
    ring

/-- The Leibniz rule as an identity between tensors,
`(∂ ⊗ 1) ν_{j+1}(x^(r+1) y) = (1 ⊗ m)(ν_j(∂x), ν_j(∂y))`: `∂ ⊗ 1` applied to a tensor `T` with
`μ_{j+1}(T) = x^(r+1) y + I_{≥j+2}` is the image under `1 ⊗ m` of a function at `0⁻` with values
in `A_j ⊗ (V_α ⊕ V_β)`. -/
theorem exists_coordinate_identity (h0 : GradeZeroScalars 𝒜) {j : ℕ} {α β : NatOrdinal}
    (hjα : 0 < α.constantCoeff → j + 1 ≤ α.constantCoeff)
    (hjβ : 0 < β.constantCoeff → j + 1 ≤ β.constantCoeff)
    {x y : R} (hx : x ∈ 𝒜 α) (hy : y ∈ 𝒜 β) (r : ℕ)
    (hΔx : Δ x ∈ funAtZeroMinusIdeal E (idealGE 𝒜 j))
    (hΔy : Δ y ∈ funAtZeroMinusIdeal E (idealGE 𝒜 j))
    {T : 𝒜 ((j + 1 : ℕ) : NatOrdinal) ⊗[E] Fibre 𝒜}
    (hT : mu 𝒜 (j + 1) T = Submodule.Quotient.mk (x ^ (r + 1) * y)) :
    ∃ t : ℝ → 𝒜 (j : NatOrdinal) ⊗[E] (endpointSpace 𝒜 j α × endpointSpace 𝒜 j β),
      funAtZeroMinusTensorId (hΔ.derivLinear j) T =
        Filter.Germ.mapLinear ((correctionMap 𝒜 j α β
          (fibreMap 𝒜 ((r + 1) • (x ^ r * y))) (fibreMap 𝒜 (x ^ (r + 1)))).lTensor _)
          (t : FunAtZeroMinus _) :=
  let ⟨_, _, t, _, _, _, _, hid⟩ :=
    hΔ.exists_rep_coordinate_identity h0 hjα hjβ hx hy r hΔx hΔy hT
  ⟨t, hid⟩

end IsLoweringDerivation

/-! ### The correction step -/

omit [Field E] [CommRing R] [Algebra E R] [GradedAlgebra 𝒜] in
/-- The algebra behind the correction: if `x^(r+1) y ≡ (r+1) g x^r y + h x^(r+1)` and the
corrections `g, h` multiply to zero, then `(x - g)^(r+1) (y - h) = 0`. -/
theorem pow_sub_mul_sub_eq_zero {Q : Type*} [CommRing Q] (x y g h : Q) (r : ℕ)
    (hgg : g * g = 0) (hgh : g * h = 0)
    (hcong : x ^ (r + 1) * y = g * ((r + 1) * (x ^ r * y)) + h * x ^ (r + 1)) :
    (x - g) ^ (r + 1) * (y - h) = 0 := by
  have hpow : ∀ n : ℕ, (x - g) ^ (n + 1) = x ^ (n + 1) - (n + 1) * (x ^ n * g) := by
    intro n
    induction n with
    | zero => ring
    | succ n ih =>
      rw [pow_succ, ih]
      push_cast
      linear_combination ((n : Q) + 1) * x ^ n * hgg
  linear_combination (y - h) * hpow r + hcong + (r + 1) * x ^ r * hgh

omit [GradedAlgebra 𝒜] in
theorem lTensor_inl_fst_add_lTensor_inr_snd {U A B : Type*} [AddCommGroup U] [Module E U]
    [AddCommGroup A] [Module E A] [AddCommGroup B] [Module E B] (t : U ⊗[E] (A × B)) :
    (LinearMap.inl E A B).lTensor U ((LinearMap.fst E A B).lTensor U t) +
      (LinearMap.inr E A B).lTensor U ((LinearMap.snd E A B).lTensor U t) = t := by
  rw [← LinearMap.comp_apply, ← LinearMap.lTensor_comp, ← LinearMap.comp_apply,
    ← LinearMap.lTensor_comp, ← LinearMap.add_apply, ← LinearMap.lTensor_add]
  have : (LinearMap.inl E A B).comp (LinearMap.fst E A B) +
      (LinearMap.inr E A B).comp (LinearMap.snd E A B) = LinearMap.id := by
    ext <;> simp
  rw [this, LinearMap.lTensor_id, LinearMap.id_apply]

namespace IsLoweringDerivation

variable (Δ) in
/-- Stage `j` of the correction argument: homogeneous lifts `x, y` of `ρ, τ` with
`x^(r+1) y ∈ I_{≥j+1}` and `∂x, ∂y ∈ Fun_{0⁻}(I_{≥j})`. -/
structure Stage (ρ τ : Fibre 𝒜) (α β : NatOrdinal) (r j : ℕ) (x y : R) : Prop where
  mem_left : x ∈ 𝒜 α
  mem_right : y ∈ 𝒜 β
  map_left : fibreMap 𝒜 x = ρ
  map_right : fibreMap 𝒜 y = τ
  prod_mem : x ^ (r + 1) * y ∈ idealGE 𝒜 (j + 1)
  deriv_left : Δ x ∈ funAtZeroMinusIdeal E (idealGE 𝒜 j)
  deriv_right : Δ y ∈ funAtZeroMinusIdeal E (idealGE 𝒜 j)

include hΔ

omit hΔ [GradedAlgebra 𝒜] in
theorem Stage.correctionMap_eq {ρ τ : Fibre 𝒜} {α β : NatOrdinal} {r j : ℕ} {x y : R}
    (hs : Stage Δ ρ τ α β r j x y) :
    correctionMap 𝒜 j α β (fibreMap 𝒜 ((r + 1) • (x ^ r * y))) (fibreMap 𝒜 (x ^ (r + 1))) =
      correctionMap 𝒜 j α β ((r + 1) • (ρ ^ r * τ)) (ρ ^ (r + 1)) := by
  rw [map_nsmul, _root_.map_mul, map_pow, map_pow, hs.map_left, hs.map_right]

/-- The correction step: stage `j` data can be corrected to stage `j + 1` data, provided the
map `m : V_α ⊕ V_β → A/I` is injective. -/
theorem Stage.exists_succ (h0 : GradeZeroScalars 𝒜) {ρ τ : Fibre 𝒜} {α β : NatOrdinal}
    {r j : ℕ} (hjα : 0 < α.constantCoeff → j + 1 ≤ α.constantCoeff)
    (hjβ : 0 < β.constantCoeff → j + 1 ≤ β.constantCoeff)
    (hinj : Function.Injective (correctionMap 𝒜 j α β ((r + 1) • (ρ ^ r * τ)) (ρ ^ (r + 1))))
    {x y : R} (hs : Stage Δ ρ τ α β r j x y) :
    ∃ x' y', Stage Δ ρ τ α β r (j + 1) x' y' := by
  classical
  -- the class of `x^(r+1) y` and the tensor form of the Leibniz rule
  obtain ⟨T, hT⟩ := exists_mu_eq 𝒜 hs.prod_mem
  obtain ⟨t, hid⟩ := hΔ.exists_coordinate_identity h0 hjα hjβ hs.mem_left hs.mem_right r
    hs.deriv_left hs.deriv_right hT
  set m := correctionMap 𝒜 j α β (fibreMap 𝒜 ((r + 1) • (x ^ r * y))) (fibreMap 𝒜 (x ^ (r + 1)))
    with hm
  have hminj : Function.Injective m := by rw [hm, hs.correctionMap_eq]; exact hinj
  obtain ⟨T', hT'⟩ := exists_eq_lTensor_of_funAtZeroMinusTensorId_eq _
    (hΔ.derivLinear_injective j) m T _ hid
  -- homogeneous lifts of the two components
  obtain ⟨G, hGα, hGW, hG⟩ := exists_homogeneous_mu_eq_endpoint 𝒜 hjα
    ((LinearMap.fst E _ _).lTensor _ T')
  obtain ⟨G', hG'β, hG'W, hG'⟩ := exists_homogeneous_mu_eq_endpoint 𝒜 hjβ
    ((LinearMap.snd E _ _).lTensor _ T')
  -- the congruence `x^(r+1) y ≡ G (r+1) x^r y + G' x^(r+1)` modulo `I_{≥j+2}`
  have hcong : (Submodule.Quotient.mk (x ^ (r + 1) * y) : R ⧸ idealGE 𝒜 (j + 1 + 1)) =
      Submodule.Quotient.mk (G * ((r + 1) • (x ^ r * y)) + G' * x ^ (r + 1)) := by
    rw [← hT, hT', ← lTensor_inl_fst_add_lTensor_inr_snd T', map_add, map_add,
      ← LinearMap.comp_apply (LinearMap.lTensor _ m), ← LinearMap.lTensor_comp, hm,
      correctionMap_comp_inl,
      ← LinearMap.comp_apply (LinearMap.lTensor _ (correctionMap _ _ _ _ _ _)),
      ← LinearMap.lTensor_comp, correctionMap_comp_inr, LinearMap.lTensor_comp,
      LinearMap.lTensor_comp, LinearMap.comp_apply, LinearMap.comp_apply, mu_lTensor_mulLeft,
      mu_lTensor_mulLeft, hG, hG']
    change Ideal.Quotient.mk _ G * Ideal.Quotient.mk _ _ + Ideal.Quotient.mk _ G' *
      Ideal.Quotient.mk _ _ = Ideal.Quotient.mk _ _
    rw [← RingHom.map_mul, ← RingHom.map_mul, ← RingHom.map_add]
  -- the corrected lifts
  have hGG : G * G ∈ idealGE 𝒜 (j + 1 + 1) :=
    idealGE_antitone 𝒜 (by omega) (mul_mem_idealGE 𝒜 hGW hGW)
  have hGG' : G * G' ∈ idealGE 𝒜 (j + 1 + 1) :=
    idealGE_antitone 𝒜 (by omega) (mul_mem_idealGE 𝒜 hGW hG'W)
  have hprod : (x - G) ^ (r + 1) * (y - G') ∈ idealGE 𝒜 (j + 1 + 1) := by
    rw [← Ideal.Quotient.eq_zero_iff_mem, RingHom.map_mul, RingHom.map_pow, RingHom.map_sub,
      RingHom.map_sub]
    refine pow_sub_mul_sub_eq_zero _ _ _ _ r ?_ ?_ ?_
    · rw [← RingHom.map_mul, Ideal.Quotient.eq_zero_iff_mem]; exact hGG
    · rw [← RingHom.map_mul, Ideal.Quotient.eq_zero_iff_mem]; exact hGG'
    · have h := hcong
      simp only [nsmul_eq_mul] at h
      change Ideal.Quotient.mk _ _ = Ideal.Quotient.mk _ _ at h
      simp only [RingHom.map_add, RingHom.map_mul, RingHom.map_pow, map_natCast] at h
      push_cast at h ⊢
      exact h
  have hW1 : idealGE 𝒜 (j + 1) ≤ fibreIdeal 𝒜 := idealGE_antitone 𝒜 (by omega)
  have hs' : Stage Δ ρ τ α β r j (x - G) (y - G') :=
    { mem_left := sub_mem hs.mem_left hGα
      mem_right := sub_mem hs.mem_right hG'β
      map_left := by rw [map_sub, hs.map_left, (fibreMap_eq_zero_iff 𝒜 G).mpr (hW1 hGW), sub_zero]
      map_right := by
        rw [map_sub, hs.map_right, (fibreMap_eq_zero_iff 𝒜 G').mpr (hW1 hG'W), sub_zero]
      prod_mem := idealGE_antitone 𝒜 (by omega) hprod
      deriv_left := by
        rw [map_sub]
        refine sub_mem hs.deriv_left ?_
        have := hΔ.map_mem_funAtZeroMinusIdeal_idealGE (j := j + 1) (by omega) hGW
        rwa [Nat.add_sub_cancel] at this
      deriv_right := by
        rw [map_sub]
        refine sub_mem hs.deriv_right ?_
        have := hΔ.map_mem_funAtZeroMinusIdeal_idealGE (j := j + 1) (by omega) hG'W
        rwa [Nat.add_sub_cancel] at this }
  -- the tensor identity for the corrected lifts has zero left side
  have hT0 : mu 𝒜 (j + 1) (0 : 𝒜 ((j + 1 : ℕ) : NatOrdinal) ⊗[E] Fibre 𝒜) =
      Submodule.Quotient.mk ((x - G) ^ (r + 1) * (y - G')) := by
    rw [map_zero, eq_comm, Submodule.Quotient.mk_eq_zero]
    exact hprod
  obtain ⟨f', g', t', hf', hg', htf', htg', hid'⟩ := hΔ.exists_rep_coordinate_identity h0 hjα
    hjβ hs'.mem_left hs'.mem_right r hs'.deriv_left hs'.deriv_right hT0
  rw [map_zero, hs'.correctionMap_eq] at hid'
  have ht' : ∀ᶠ γ in 𝓝[<] (0 : ℝ), t' γ = 0 := by
    have hinj' := Module.Flat.lTensor_preserves_injective_linearMap
      (M := 𝒜 (j : NatOrdinal)) _ hinj
    have h := Filter.Germ.mapLinear_injective _ hinj' (by rw [← hid', map_zero] :
      Filter.Germ.mapLinear _ (t' : FunAtZeroMinus _) = Filter.Germ.mapLinear _ 0)
    exact Filter.Germ.coe_eq.mp h
  refine ⟨x - G, y - G', { hs' with prod_mem := hprod, deriv_left := ?_, deriv_right := ?_ }⟩
  · rw [hf', coe_mem_funAtZeroMinusIdeal_iff]
    refine ht'.mono fun γ hγ ↦ ?_
    rw [← Submodule.Quotient.mk_eq_zero, ← htf' γ, hγ, map_zero, map_zero, map_zero]
  · rw [hg', coe_mem_funAtZeroMinusIdeal_iff]
    refine ht'.mono fun γ hγ ↦ ?_
    rw [← Submodule.Quotient.mk_eq_zero, ← htg' γ, hγ, map_zero, map_zero, map_zero]

/-! ### Homogeneous nonvanishing -/

omit hΔ in
theorem mem_funAtZeroMinusIdeal_idealGE_zero (g : FunAtZeroMinus R) :
    g ∈ funAtZeroMinusIdeal E (idealGE 𝒜 0) := by
  induction g using Filter.Germ.inductionOn with
  | _ f =>
    rw [coe_mem_funAtZeroMinusIdeal_iff, idealGE_zero]
    exact Eventually.of_forall fun _ ↦ Submodule.mem_top

omit hΔ in
/-- A function at `0⁻` with values in `I_{≥N} ∩ A_η` vanishes when `N` exceeds the finite part of
`η`. -/
theorem eq_zero_of_mem_funAtZeroMinusIdeal_of_mem_funAtZeroMinusSubmodule {N : ℕ} {η : NatOrdinal}
    {g : FunAtZeroMinus R}
    (hg : g ∈ funAtZeroMinusIdeal E (idealGE 𝒜 N)) (hgη : g ∈ funAtZeroMinusSubmodule (𝒜 η))
    (hη : η.constantCoeff < N) : g = 0 := by
  obtain ⟨f, hf, rfl⟩ := exists_coe_eq_of_mem_funAtZeroMinusSubmodule _
    (mem_funAtZeroMinusSubmodule_inf _ _ hgη hg)
  have : f = fun _ ↦ 0 := funext fun γ ↦ by
    obtain ⟨h1, h2⟩ := Submodule.mem_inf.mp (hf γ)
    exact eq_zero_of_mem_idealGE_of_constantCoeff_lt 𝒜 h1 h2 hη
  rw [this]
  rfl

omit hΔ in
theorem nsmul_eq_zero_iff_of_charZero [CharZero E] {V : Type*} [AddCommGroup V] [Module E V]
    (n : ℕ) (v : V) : (n + 1) • v = 0 ↔ v = 0 := by
  rw [← Nat.cast_smul_eq_nsmul E, smul_eq_zero]
  simp [Nat.cast_add_one_ne_zero]

/-- Homogeneous non-vanishing in `A/I`: `ρ^s τ ≠ 0` for non-zero homogeneous `ρ, τ ∈ A/I`. The
proof is a lexicographic induction on `(n, n', s)`, `n, n'` the finite parts of the degrees of
`ρ, τ` (Lean `α.constantCoeff`, `β.constantCoeff`). -/
theorem pow_mul_ne_zero [IsDomain R] [CharZero E] (h0 : GradeZeroScalars 𝒜) (A B s : ℕ) :
    ∀ {α β : NatOrdinal}, α.constantCoeff = A → β.constantCoeff = B →
      ∀ {ρ τ : Fibre 𝒜}, ρ ∈ fibreGrade 𝒜 α → τ ∈ fibreGrade 𝒜 β → ρ ≠ 0 → τ ≠ 0 →
        ρ ^ s * τ ≠ 0 := by
  induction A using Nat.strong_induction_on generalizing B s with
  | _ A ihA =>
  induction B using Nat.strong_induction_on generalizing s with
  | _ B ihB =>
  induction s with
  | zero =>
    intro α β hA hB ρ τ hρ hτ hρ0 hτ0
    simpa using hτ0
  | succ r ihs =>
  intro α β hA hB ρ τ hρ hτ hρ0 hτ0 hcontra
  have hz : ρ ^ r * τ ≠ 0 := ihs hA hB hρ hτ hρ0 hτ0
  have hzmem : ρ ^ r * τ ∈ fibreGrade 𝒜 (r • α + β) :=
    mul_mem_fibreGrade 𝒜 (pow_mem_fibreGrade 𝒜 hρ r) hτ
  -- (i): multiplication by `ρ^r τ` is injective on `(A/I)_{α'}` for `α'` of smaller finite part
  have hi : ∀ j : ℕ, 0 < A → ∀ a ∈ fibreGrade 𝒜 (α.removeNat (j + 1)),
      ρ ^ r * τ * a = 0 → a = 0 := by
    intro j hA0 a ha h
    by_contra ha0
    refine ihA (A - (j + 1)) (by omega) (r • α + β).constantCoeff 1
      (by rw [NatOrdinal.constantCoeff_removeNat, hA]) rfl ha hzmem ha0 hz ?_
    rw [pow_one, mul_comm]
    exact h
  -- (ii): multiplication by `ρ^(r+2)` is injective on `(A/I)_{β'}` for `β'` of smaller finite part
  have hii : ∀ j : ℕ, 0 < B → ∀ b ∈ fibreGrade 𝒜 (β.removeNat (j + 1)),
      ρ ^ (r + 2) * b = 0 → b = 0 := by
    intro j hB0 b hb h
    by_contra hb0
    exact ihB (B - (j + 1)) (by omega) (r + 2) hA
      (by rw [NatOrdinal.constantCoeff_removeNat, hB]) hρ hb hρ0 hb0 h
  -- injectivity of the correction map at every stage
  have hinj : ∀ j : ℕ,
      Function.Injective (correctionMap 𝒜 j α β ((r + 1) • (ρ ^ r * τ)) (ρ ^ (r + 1))) := by
    intro j
    rw [injective_iff_map_eq_zero]
    rintro ⟨a, b⟩ hab
    rw [correctionMap_apply] at hab
    have hb : (b : Fibre 𝒜) = 0 := by
      have h1 := congrArg (ρ * ·) hab
      simp only [mul_add, mul_zero, smul_mul_assoc, mul_smul_comm] at h1
      have h2 : ρ * (ρ ^ r * τ * a) = 0 := by
        rw [← mul_assoc, ← mul_assoc, ← pow_succ', hcontra, zero_mul]
      rw [h2, nsmul_zero, zero_add, ← mul_assoc, ← pow_succ'] at h1
      by_cases hB0 : 0 < B
      · exact hii j hB0 b ((endpointSpace_le 𝒜 j β) b.2) h1
      · exact (Submodule.mem_bot E).mp ((endpointSpace_of_eq_zero 𝒜 (by omega)).le b.2)
    rw [hb, mul_zero, add_zero, smul_mul_assoc, nsmul_eq_zero_iff_of_charZero (E := E)] at hab
    have ha : (a : Fibre 𝒜) = 0 := by
      by_cases hA0 : 0 < A
      · exact hi j hA0 a ((endpointSpace_le 𝒜 j α) a.2) hab
      · exact (Submodule.mem_bot E).mp ((endpointSpace_of_eq_zero 𝒜 (by omega)).le a.2)
    exact Prod.ext (Subtype.ext ha) (Subtype.ext hb)
  -- lifts
  obtain ⟨x, hx, hxρ⟩ := exists_mem_of_mem_fibreGrade 𝒜 hρ
  obtain ⟨y, hy, hyτ⟩ := exists_mem_of_mem_fibreGrade 𝒜 hτ
  have hx0 : x ≠ 0 := fun h ↦ hρ0 (by rw [← hxρ, h, map_zero])
  have hy0 : y ≠ 0 := fun h ↦ hτ0 (by rw [← hyτ, h, map_zero])
  have hprod : x ^ (r + 1) * y ∈ idealGE 𝒜 1 := by
    rw [← fibreMap_eq_zero_iff, _root_.map_mul, map_pow, hxρ, hyτ]
    exact hcontra
  have hprodmem : x ^ (r + 1) * y ∈ 𝒜 ((r + 1) • α + β) :=
    SetLike.mul_mem_graded (SetLike.pow_mem_graded _ hx) hy
  by_cases hAB : A = 0 ∧ B = 0
  · -- both finite parts are zero
    refine mul_ne_zero (pow_ne_zero _ hx0) hy0
      (eq_zero_of_mem_idealGE_of_constantCoeff_lt 𝒜 hprodmem hprod ?_)
    rw [NatOrdinal.constantCoeff_add, NatOrdinal.constantCoeff_nsmul, hA, hB, hAB.1, hAB.2]
    simp
  -- the positive minimum `N` of the non-zero finite parts among `n, n'`
  obtain ⟨N, hNpos, hNA, hNB, hN⟩ : ∃ N : ℕ, 0 < N ∧ (0 < A → N ≤ A) ∧ (0 < B → N ≤ B) ∧
      ((N = A ∧ 0 < A) ∨ (N = B ∧ 0 < B)) := by
    by_cases hA0 : 0 < A
    · by_cases hB0 : 0 < B
      · by_cases hle : A ≤ B
        · exact ⟨A, hA0, fun _ ↦ le_rfl, fun _ ↦ hle, Or.inl ⟨rfl, hA0⟩⟩
        · exact ⟨B, hB0, fun _ ↦ by omega, fun _ ↦ le_rfl, Or.inr ⟨rfl, hB0⟩⟩
      · exact ⟨A, hA0, fun _ ↦ le_rfl, fun h ↦ absurd h hB0, Or.inl ⟨rfl, hA0⟩⟩
    · have hB0 : 0 < B := by omega
      exact ⟨B, hB0, fun h ↦ absurd h hA0, fun _ ↦ le_rfl, Or.inr ⟨rfl, hB0⟩⟩
  -- the stages
  have hstage : ∀ j ≤ N, ∃ x' y', Stage Δ ρ τ α β r j x' y' := by
    intro j
    induction j with
    | zero =>
      intro _
      exact ⟨x, y, ⟨hx, hy, hxρ, hyτ, hprod, mem_funAtZeroMinusIdeal_idealGE_zero _,
        mem_funAtZeroMinusIdeal_idealGE_zero _⟩⟩
    | succ j ih =>
      intro hj
      obtain ⟨x', y', hs⟩ := ih (by omega)
      exact hs.exists_succ hΔ h0 (fun hA0 ↦ by have := hNA (hA ▸ hA0); omega)
        (fun hB0 ↦ by have := hNB (hB ▸ hB0); omega) (hinj j)
  -- termination
  obtain ⟨x', y', hs⟩ := hstage N le_rfl
  rcases hN with ⟨rfl, hA0⟩ | ⟨rfl, hB0⟩
  · have hpred := hΔ.mem_lower (by omega) hs.mem_left
    have hΔ0 : Δ x' = 0 := eq_zero_of_mem_funAtZeroMinusIdeal_of_mem_funAtZeroMinusSubmodule
      hs.deriv_left hpred (by rw [NatOrdinal.constantCoeff_removeNat]; omega)
    have := hΔ.injective (by omega) hs.mem_left hΔ0
    exact hρ0 (by rw [← hs.map_left, this, map_zero])
  · have hpred := hΔ.mem_lower (by omega) hs.mem_right
    have hΔ0 : Δ y' = 0 := eq_zero_of_mem_funAtZeroMinusIdeal_of_mem_funAtZeroMinusSubmodule
      hs.deriv_right hpred (by rw [NatOrdinal.constantCoeff_removeNat]; omega)
    have := hΔ.injective (by omega) hs.mem_right hΔ0
    exact hτ0 (by rw [← hs.map_right, this, map_zero])

/-- `A/I` is a domain: it is graded by the `(A/I)_β`, and by homogeneous non-vanishing it has no
homogeneous zero divisors. -/
theorem fibre_isDomain [IsDomain R] [CharZero E] (h0 : GradeZeroScalars 𝒜) :
    IsDomain (Fibre 𝒜) :=
  GradedRing.isDomain_of_homogeneous_eq_zero_or_eq_zero (fibreGrade 𝒜) fun ⟨_, hρ⟩ ⟨_, hτ⟩ h ↦
    or_iff_not_imp_left.mpr fun hρ0 ↦ by_contra fun hτ0 ↦
      hΔ.pow_mul_ne_zero h0 _ _ 1 rfl rfl hρ hτ hρ0 hτ0 (by rwa [pow_one])

end IsLoweringDerivation

end LoweringDerivation
