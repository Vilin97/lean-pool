/-
Copyright (c) 2026 Shengtong Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shengtong Zhang
-/
module


public import LeanPool.Nikodym.Nikodym.LowerBound.Grid.Reduction

/-!
# Chinese remainder theorem for powers of point ideals

This file implements blueprint node **G02** of the lower-bound side of the sharp finite-field
Nikodym exponent.

* `Nikodym.LowerBound.pointIdeal_sup_eq_top`: the point ideals `𝔪ₓ`, `𝔪ᵧ` of distinct points are
  comaximal, and so are their powers (`pointIdeal_pow_sup_pow_eq_top`);
* `Nikodym.LowerBound.pointIdeal_pow_surjective`, `Nikodym.LowerBound.jets_surjective`: for a
  finite family of pairwise distinct points `x i`, the maps `P_d → ∏ i, P_d ⧸ 𝔪_{x i} ^ r` and
  `P_d → ∏ i, P_d ⧸ (I + 𝔪_{x i} ^ r)` are surjective (Chinese remainder theorem), together with
  the existential forms `exists_pointIdeal_pow_eq`, `exists_jets_eq` and the `K`-linear packaging
  `jetsLinearMap`, `jetsLinearMap_surjective`;
* `Nikodym.LowerBound.gridIdeal_pow_le_pointIdeal_pow`: for the grid polynomials of G01,
  `J ^ r ≤ 𝔪_{ι x} ^ r` for every grid point `x : Fin d → F`;
* `Nikodym.LowerBound.liftGrid_injective`: `x ↦ ι ∘ x` is injective on grid points, and the grid
  version `exists_grid_jets_eq` of the interpolation statement.
-/

@[expose] public section

namespace Nikodym.LowerBound

open MvPolynomial

variable {K : Type*} [Field K] {d : ℕ}

/-! ### Comaximality of point ideals -/

section Comaximal

variable {x y : Fin d → K}

/-- Blueprint G02: the point ideals of two distinct points are comaximal. -/
theorem pointIdeal_sup_eq_top (hxy : x ≠ y) : pointIdeal x ⊔ pointIdeal y = ⊤ := by
  obtain ⟨i, hi⟩ := Function.ne_iff.mp hxy
  have hne : y i - x i ≠ 0 := sub_ne_zero.mpr (Ne.symm hi)
  rw [Ideal.eq_top_iff_one]
  have h1 : (1 : MvPolynomial (Fin d) K) =
      C (y i - x i)⁻¹ * ((X i - C (x i)) - (X i - C (y i))) := by
    rw [sub_sub_sub_cancel_left, ← C_sub, ← C_mul, inv_mul_cancel₀ hne, C_1]
  rw [h1]
  exact Ideal.mul_mem_left _ _ (Submodule.sub_mem _
    (Ideal.mem_sup_left (X_sub_C_mem_pointIdeal x i))
    (Ideal.mem_sup_right (X_sub_C_mem_pointIdeal y i)))

/-- Blueprint G02: powers of the point ideals of two distinct points are comaximal. -/
theorem pointIdeal_pow_sup_pow_eq_top (hxy : x ≠ y) (r s : ℕ) :
    pointIdeal x ^ r ⊔ pointIdeal y ^ s = ⊤ :=
  Ideal.pow_sup_pow_eq_top (pointIdeal_sup_eq_top hxy)

/-- Blueprint G02: powers of the point ideals of two distinct points are coprime. -/
theorem pointIdeal_pow_isCoprime (hxy : x ≠ y) (r s : ℕ) :
    IsCoprime (pointIdeal x ^ r) (pointIdeal y ^ s) :=
  Ideal.isCoprime_iff_sup_eq.mpr (pointIdeal_pow_sup_pow_eq_top hxy r s)

end Comaximal

/-! ### Chinese remainder theorem -/

section CRT

variable {ι : Type*} [Finite ι] {x : ι → Fin d → K}

omit [Finite ι] in
/-- Blueprint G02: for pairwise distinct points `x i`, the ideals `𝔪_{x i} ^ r` are pairwise
coprime. -/
theorem pointIdeal_pow_pairwise_isCoprime (hx : Function.Injective x) (r : ℕ) :
    Pairwise fun i j ↦ IsCoprime (pointIdeal (x i) ^ r) (pointIdeal (x j) ^ r) := fun _ _ hij ↦
  pointIdeal_pow_isCoprime (hx.ne hij) r r

/-- Blueprint G02 (existential form): for pairwise distinct points `x i` and any classes
`w i ∈ P_d ⧸ 𝔪_{x i} ^ r`, there is a single polynomial `f` representing all of them. -/
theorem exists_pointIdeal_pow_eq (hx : Function.Injective x) (r : ℕ)
    (w : ∀ i, MvPolynomial (Fin d) K ⧸ pointIdeal (x i) ^ r) :
    ∃ f : MvPolynomial (Fin d) K, ∀ i, Ideal.Quotient.mk (pointIdeal (x i) ^ r) f = w i := by
  obtain ⟨f, hf⟩ := Ideal.pi_quotient_surjective (pointIdeal_pow_pairwise_isCoprime hx r) w
  exact ⟨f, fun i ↦ hf i⟩

/-- Blueprint G02: the map `P_d → ∏ i, P_d ⧸ 𝔪_{x i} ^ r` is surjective for pairwise distinct
points `x i`. -/
theorem pointIdeal_pow_surjective (hx : Function.Injective x) (r : ℕ) :
    Function.Surjective (RingHom.pi fun i ↦ Ideal.Quotient.mk (pointIdeal (x i) ^ r)) := by
  intro w
  obtain ⟨f, hf⟩ := exists_pointIdeal_pow_eq hx r w
  exact ⟨f, funext hf⟩

variable (I : Ideal (MvPolynomial (Fin d) K))

/-- Blueprint G02 (existential form, with an ambient ideal): for pairwise distinct points `x i` and
any jets `w i ∈ Q_{I, x i}(r) = P_d ⧸ (I + 𝔪_{x i} ^ r)`, there is a single polynomial `f`
representing all of them. -/
theorem exists_jets_eq (hx : Function.Injective x) (r : ℕ)
    (w : ∀ i, MvPolynomial (Fin d) K ⧸ jetIdeal I (x i) r) :
    ∃ f : MvPolynomial (Fin d) K, ∀ i, Ideal.Quotient.mk (jetIdeal I (x i) r) f = w i := by
  choose v hv using fun i ↦ Ideal.Quotient.mk_surjective (w i)
  obtain ⟨f, hf⟩ := exists_pointIdeal_pow_eq hx r fun i ↦ Ideal.Quotient.mk _ (v i)
  refine ⟨f, fun i ↦ ?_⟩
  rw [← hv i, Ideal.Quotient.eq]
  exact pointIdeal_pow_le_jetIdeal I (x i) r (Ideal.Quotient.eq.mp (hf i))

/-- Blueprint G02: the map `P_d → ∏ i, Q_{I, x i}(r)` is surjective for pairwise distinct
points `x i`. -/
theorem jets_surjective (hx : Function.Injective x) (r : ℕ) :
    Function.Surjective (RingHom.pi fun i ↦ Ideal.Quotient.mk (jetIdeal I (x i) r)) := by
  intro w
  obtain ⟨f, hf⟩ := exists_jets_eq I hx r w
  exact ⟨f, funext hf⟩

end CRT

/-! ### The jet-collecting linear map -/

section LinearMap

variable {ι : Type*} (I : Ideal (MvPolynomial (Fin d) K)) (x : ι → Fin d → K) (r : ℕ)

/-- Blueprint G02: the `K`-linear map `P_d → ∏ i, Q_{I, x i}(r)` collecting all jets. -/
noncomputable def jetsLinearMap :
    MvPolynomial (Fin d) K →ₗ[K] ∀ i, MvPolynomial (Fin d) K ⧸ jetIdeal I (x i) r where
  toFun f i := Ideal.Quotient.mk (jetIdeal I (x i) r) f
  map_add' f g := by
    ext i
    simp
  map_smul' c f := by
    ext i
    exact Submodule.Quotient.mk_smul _ _ _

@[simp]
theorem jetsLinearMap_apply (f : MvPolynomial (Fin d) K) (i : ι) :
    jetsLinearMap I x r f i = Ideal.Quotient.mk (jetIdeal I (x i) r) f :=
  rfl

variable {x}

/-- Blueprint G02: the jet-collecting linear map is surjective for pairwise distinct points. -/
theorem jetsLinearMap_surjective [Finite ι] (hx : Function.Injective x) :
    Function.Surjective (jetsLinearMap I x r) := by
  intro w
  obtain ⟨f, hf⟩ := exists_jets_eq I hx r w
  exact ⟨f, funext hf⟩

/-- Blueprint G02: the jet-collecting linear map has full range for pairwise distinct points. -/
theorem range_jetsLinearMap [Finite ι] (hx : Function.Injective x) :
    LinearMap.range (jetsLinearMap I x r) = ⊤ :=
  LinearMap.range_eq_top.mpr (jetsLinearMap_surjective I r hx)

end LinearMap

/-! ### The finite grid -/

section Grid

variable {F : Type*} [Field F] [Fintype F] [Algebra F K]

/-- Blueprint G02: the grid ideal is contained in the point ideal of every grid point. -/
theorem gridIdeal_le_pointIdeal (x : Fin d → F) :
    gridIdeal (fun _ ↦ gridPoly F K) ≤ pointIdeal (fun i ↦ algebraMap F K (x i)) := by
  rw [gridIdeal, Ideal.span_le]
  rintro _ ⟨i, rfl⟩
  exact Z_grid_mem_pointIdeal x i

/-- Blueprint G02: `J ^ r ≤ 𝔪_{ι x} ^ r` for every grid point `x`. -/
theorem gridIdeal_pow_le_pointIdeal_pow (x : Fin d → F) (r : ℕ) :
    gridIdeal (fun _ ↦ gridPoly F K) ^ r ≤ pointIdeal (fun i ↦ algebraMap F K (x i)) ^ r :=
  Ideal.pow_right_mono (gridIdeal_le_pointIdeal x) r

omit [Fintype F] in
variable (K) in
/-- Blueprint G02: the embedding `x ↦ ι ∘ x` of the grid `F ^ d` into `K ^ d` is injective. -/
theorem liftGrid_injective :
    Function.Injective (fun x : Fin d → F ↦ fun i ↦ algebraMap F K (x i)) := fun _ _ h ↦
  funext fun i ↦ (algebraMap F K).injective (congr_fun h i)

omit [Fintype F] in
/-- Blueprint G02 (grid form): for any ideal `I`, any `r` and any jets
`w x ∈ Q_{I, ι x}(r)` indexed by the grid points `x : Fin d → F`, there is a single polynomial `f`
representing all of them. -/
theorem exists_grid_jets_eq [Finite F] (I : Ideal (MvPolynomial (Fin d) K)) (r : ℕ)
    (w : ∀ x : Fin d → F, MvPolynomial (Fin d) K ⧸ jetIdeal I (fun i ↦ algebraMap F K (x i)) r) :
    ∃ f : MvPolynomial (Fin d) K, ∀ x : Fin d → F,
      Ideal.Quotient.mk (jetIdeal I (fun i ↦ algebraMap F K (x i)) r) f = w x :=
  exists_jets_eq I (liftGrid_injective K) r w

end Grid

end Nikodym.LowerBound

/- Adapted for Lean Pool: module imports and compatibility with its pinned toolchain. -/
