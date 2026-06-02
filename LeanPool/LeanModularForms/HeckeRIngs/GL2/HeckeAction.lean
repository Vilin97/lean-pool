/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/

import LeanPool.LeanModularForms.HeckeRIngs.GL2.Basic
import LeanPool.LeanModularForms.HeckeRIngs.GLn.TransposeAntiInvolution
import Mathlib.NumberTheory.ModularForms.Basic

/-!
# Hecke Operators on Modular Forms

Defines the action of the Hecke algebra on functions `ℍ → ℂ` via the slash action,
and shows it preserves slash invariance.

## Main definitions

* `glMap` — embedding `GL₂(ℚ) →* GL₂(ℝ)`
* `heckeSlash` — action of a double coset on functions via left coset representatives:
    `T(D) f = Σᵢ f ∣[k] (σᵢδ)ᵀ` where `ΓδΓ = ⊔ Γ(δᵀσᵢᵀ)` (Shimura Prop 3.30)
* `heckeSlashInvariant` — the Hecke operator preserves slash invariance

## Implementation

The slash action on `GL₂(ℚ)` is induced from `GL₂(ℝ)` via `monoidHomSlashAction glMap`,
so `f ∣[k] g` works directly for `g : GL (Fin 2) ℚ` without explicit coercion.

Left coset representatives are obtained by transposing right coset representatives:
if `ΓδΓ = ⊔ᵢ (σᵢδ)Γ`, then `ΓδΓ = ⊔ᵢ Γ(δᵀσᵢᵀ)` since transpose is an
anti-involution preserving `Γ` and fixing every double coset (`GL_pair_onHeckeCoset_eq`).

## References

* Shimura, *Introduction to the Arithmetic Theory of Automorphic Functions*, §3.4, Prop 3.30
-/

open Matrix Matrix.SpecialLinearGroup Subgroup.Commensurable Pointwise
open HeckeRing DoubleCoset HeckeRing.GLn
open scoped Pointwise ModularForm MatrixGroups UpperHalfPlane

namespace HeckeRing.GL2

/-- Embed `GL₂(ℚ)` into `GL₂(ℝ)` via `ℚ ↪ ℝ`. -/
noncomputable def glMap : GL (Fin 2) ℚ →* GL (Fin 2) ℝ :=
  GeneralLinearGroup.map (algebraMap ℚ ℝ)

/-- Slash action on `GL₂(ℚ)` induced from `GL₂(ℝ)` via the embedding `ℚ ↪ ℝ`.
    Satisfies `f ∣[k] g = f ∣[k] glMap g` definitionally. -/
noncomputable scoped instance instSlashActionGL2Rat :
    SlashAction ℤ (GL (Fin 2) ℚ) (ℍ → ℂ) :=
  monoidHomSlashAction glMap

section DetPositivity

private lemma glMap_det (g : GL (Fin 2) ℚ) :
    GeneralLinearGroup.det (glMap g) =
    Units.map (algebraMap ℚ ℝ) (GeneralLinearGroup.det g) :=
  GeneralLinearGroup.map_det _ g

private lemma glMap_det_val (g : GL (Fin 2) ℚ) :
    (glMap g).det.val = algebraMap ℚ ℝ g.det.val :=
  congr_arg Units.val (glMap_det g)

private lemma delta_det_pos_real (g : (GLPair 2).Δ) :
    0 < (glMap (g : GL (Fin 2) ℚ)).det.val := by
  rw [glMap_det_val, GeneralLinearGroup.val_det_apply]
  exact Rat.cast_pos.mpr g.prop.2

private lemma SLnZ_det_one_real (σ : (GLPair 2).H) :
    (glMap (σ : GL (Fin 2) ℚ)).det.val = 1 := by
  obtain ⟨s, hs⟩ := σ.prop
  rw [show (σ : GL (Fin 2) ℚ) = mapGL ℚ s from hs.symm,
    glMap_det, det_mapGL s, map_one]
  rfl

private lemma cosetRep_delta_det_pos (σ : (GLPair 2).H) (g : (GLPair 2).Δ) :
    0 < (glMap ((σ : GL (Fin 2) ℚ) * (g : GL (Fin 2) ℚ))).det.val := by
  have hmul : (glMap ((σ : GL (Fin 2) ℚ) * ↑g)).det =
      (glMap ↑σ).det * (glMap ↑g).det := by rw [map_mul, map_mul]
  rw [show (glMap ((σ : GL (Fin 2) ℚ) * ↑g)).det.val =
    ((glMap ↑σ).det * (glMap ↑g).det).val from congrArg Units.val hmul,
    Units.val_mul]
  exact mul_pos (by rw [SLnZ_det_one_real]; exact one_pos) (delta_det_pos_real g)

private lemma delta_cosetRep_det_pos (g : (GLPair 2).Δ) (σ : (GLPair 2).H) :
    0 < (glMap ((g : GL (Fin 2) ℚ) * (σ : GL (Fin 2) ℚ))).det.val := by
  have hmul : (glMap ((g : GL (Fin 2) ℚ) * ↑σ)).det =
      (glMap ↑g).det * (glMap ↑σ).det := by rw [map_mul, map_mul]
  rw [show (glMap ((g : GL (Fin 2) ℚ) * ↑σ)).det.val =
    ((glMap ↑g).det * (glMap ↑σ).det).val from congrArg Units.val hmul,
    Units.val_mul]
  exact mul_pos (delta_det_pos_real g)
    (by rw [SLnZ_det_one_real]; exact one_pos)

private lemma sigma_eq_refl_of_pos_det {g : GL (Fin 2) ℝ} (hg : 0 < g.det.val) :
    UpperHalfPlane.σ g = .refl ℝ ℂ := by
  unfold UpperHalfPlane.σ; simp only [hg, ↓reduceIte]

private lemma glMap_transpose_det_val (g : GL (Fin 2) ℚ) :
    (glMap (GLTransposeEquiv 2 g).unop).det.val = (glMap g).det.val := by
  rw [glMap_det_val, glMap_det_val]
  show (algebraMap ℚ ℝ) ((GLTransposeEquiv 2 g).unop.det : ℚ) = _
  congr 1
  show ((GLTransposeEquiv 2 g).unop.det : ℚ) = (g.det : ℚ)
  rw [GeneralLinearGroup.val_det_apply, GeneralLinearGroup.val_det_apply,
    GL_transposeEquiv_val, Matrix.det_transpose]

private lemma cosetRep_delta_transpose_det_pos (σ : (GLPair 2).H) (g : (GLPair 2).Δ) :
    0 < (glMap (GLTransposeEquiv 2
      ((σ : GL (Fin 2) ℚ) * (g : GL (Fin 2) ℚ))).unop).det.val := by
  rw [glMap_transpose_det_val]; exact cosetRep_delta_det_pos σ g

end DetPositivity

/-- The transposed right-coset representative: `(σᵢ * δ)ᵀ = δᵀ * σᵢᵀ`. -/
noncomputable abbrev tRep (D : HeckeCoset (GLPair 2))
    (i : decompQuot (GLPair 2) (HeckeCoset.rep D)) : GL (Fin 2) ℚ :=
  (GLTransposeEquiv 2
    ((i.out : GL (Fin 2) ℚ) * (HeckeCoset.rep D : GL (Fin 2) ℚ))).unop

/-- The Hecke slash action of a double coset `D` on a function `f : ℍ → ℂ`.

    Uses left coset representatives via transpose (Shimura Prop 3.30):
    `T_k(D)(f) = Σᵢ f ∣[k] (σᵢδ)ᵀ`
    where `ΓδΓ = ⊔ᵢ (σᵢδ)Γ` is the right coset decomposition.
    Each `(σᵢδ)ᵀ = δᵀσᵢᵀ` is a left coset representative, giving
    genuinely distinct terms `f ∣[k] (δᵀσᵢᵀ)`. -/
noncomputable def heckeSlash (k : ℤ) (D : HeckeCoset (GLPair 2)) (f : ℍ → ℂ) : ℍ → ℂ :=
  ∑ i : decompQuot (GLPair 2) (HeckeCoset.rep D), f ∣[k] tRep D i

/-- The Hecke slash action distributes over addition of functions. -/
lemma heckeSlash_add (k : ℤ) (D : HeckeCoset (GLPair 2)) (f g : ℍ → ℂ) :
    heckeSlash k D (f + g) = heckeSlash k D f + heckeSlash k D g := by
  simp only [heckeSlash, SlashAction.add_slash, Finset.sum_add_distrib]

/-- The Hecke slash action sends the zero function to zero. -/
@[simp] lemma heckeSlash_zero (k : ℤ) (D : HeckeCoset (GLPair 2)) : heckeSlash k D 0 = 0 := by
  simp only [heckeSlash, SlashAction.zero_slash, Finset.sum_const_zero]

/-- The Hecke slash action commutes with scalar multiplication. -/
lemma heckeSlash_smul (k : ℤ) (D : HeckeCoset (GLPair 2)) (c : ℂ) (f : ℍ → ℂ) :
    heckeSlash k D (c • f) = c • heckeSlash k D f := by
  simp only [heckeSlash, Finset.smul_sum]
  congr 1; ext i
  change ((c • f) ∣[k] glMap _) _ = (c • (f ∣[k] glMap _)) _
  have hA : 0 < (glMap (tRep D i)).det.val :=
    cosetRep_delta_transpose_det_pos ⟨i.out, SetLike.coe_mem _⟩ (HeckeCoset.rep D)
  rw [ModularForm.smul_slash]; simp [sigma_eq_refl_of_pos_det hA]

section SlashInvariance

private lemma glMap_mapGL_eq (s : SL(2, ℤ)) :
    glMap (mapGL ℚ s) = (mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ) s := by
  apply Units.ext; ext i j
  simp only [glMap, GeneralLinearGroup.map]
  exact (IsScalarTower.algebraMap_apply ℤ ℚ ℝ (s.1 i j)).symm

private lemma glMap_mem_SL (σ : (GLPair 2).H) :
    glMap (σ : GL (Fin 2) ℚ) ∈ 𝒮ℒ := by
  obtain ⟨s, hs⟩ := σ.prop
  exact MonoidHom.mem_range.mpr ⟨s, by rw [← glMap_mapGL_eq, hs]⟩

private lemma mem_SL_exists_H {γ : GL (Fin 2) ℝ} (hγ : γ ∈ 𝒮ℒ) :
    ∃ σ ∈ (GLPair 2).H, glMap σ = γ := by
  obtain ⟨s, rfl⟩ := MonoidHom.mem_range.mp hγ
  exact ⟨mapGL ℚ s, ⟨s, rfl⟩, glMap_mapGL_eq s⟩

private lemma left_coset_disjoint (D : HeckeCoset (GLPair 2))
    (i j : decompQuot (GLPair 2) (HeckeCoset.rep D)) (hij : i ≠ j) :
    ((GLPair 2).H : Set (GL (Fin 2) ℚ)) * {tRep D i} ≠
    ((GLPair 2).H : Set (GL (Fin 2) ℚ)) * {tRep D j} := by
  intro h_eq
  apply decompQuot_coset_diff (GLPair 2) (HeckeCoset.rep D) i j hij
  have hmem : tRep D i ∈ ((GLPair 2).H : Set _) * ({tRep D j} : Set _) := by
    rw [← h_eq]; exact ⟨1, (GLPair 2).H.one_mem, _, rfl, by simp⟩
  obtain ⟨h, hh, _, rfl, heq⟩ := hmem
  have h_key : (i.out : GL (Fin 2) ℚ) * (HeckeCoset.rep D : GL (Fin 2) ℚ) =
      ((j.out : GL (Fin 2) ℚ) * (HeckeCoset.rep D : GL (Fin 2) ℚ)) *
        (GLTransposeEquiv 2 h).unop := by
    have step := GL_transposeEquiv_involutive 2
      ((i.out : GL (Fin 2) ℚ) * (HeckeCoset.rep D : GL (Fin 2) ℚ))
    change (GLTransposeEquiv 2 (tRep D i)).unop = _ at step
    rw [show tRep D i = h * tRep D j from heq.symm] at step
    rw [← step, (GLTransposeEquiv 2).map_mul h (tRep D j),
      MulOpposite.unop_mul, GL_transposeEquiv_involutive]
  calc ({(i.out : GL (Fin 2) ℚ) * (HeckeCoset.rep D : GL _ ℚ)} : Set _) *
          ((GLPair 2).H : Set _)
      = ({((j.out : GL (Fin 2) ℚ) * (HeckeCoset.rep D : GL _ ℚ)) *
          (GLTransposeEquiv 2 h).unop} : Set _) *
          ((GLPair 2).H : Set _) := by rw [h_key]
    _ = ({(j.out : GL (Fin 2) ℚ) * (HeckeCoset.rep D : GL _ ℚ)} : Set _) *
          (({(GLTransposeEquiv 2 h).unop} : Set _) *
          ((GLPair 2).H : Set _)) := by
        rw [← Set.singleton_mul_singleton, mul_assoc]
    _ = ({(j.out : GL (Fin 2) ℚ) * (HeckeCoset.rep D : GL _ ℚ)} : Set _) *
          ((GLPair 2).H : Set _) := by
        have hT : (GLTransposeEquiv 2 h).unop ∈ (GLPair 2).H :=
          GL_transpose_mem_SLnZ 2 hh
        rw [Subgroup.singleton_mul_subgroup hT]

/-- `f ∣[k]_ℚ h = f` for H-elements, via Γ-invariance. -/
private lemma slash_H_eq (k : ℤ) (f : ℍ → ℂ) (hf : ∀ γ ∈ 𝒮ℒ, f ∣[k] γ = f)
    (h : GL (Fin 2) ℚ) (hh : h ∈ (GLPair 2).H) : f ∣[k] h = f :=
  hf (glMap h) (glMap_mem_SL ⟨h, hh⟩)

/-- Left multiplication by an H-element on `decompQuot`. This is well-defined since
    the stabilizer `K = δHδ⁻¹ ∩ H` is invariant under left multiplication by H-elements
    (if `h₂⁻¹h₁ ∈ K` then `(σh₂)⁻¹(σh₁) = h₂⁻¹h₁ ∈ K`). -/
private noncomputable def leftMulQuot (D : HeckeCoset (GLPair 2)) (σ : (GLPair 2).H) :
    decompQuot (GLPair 2) (HeckeCoset.rep D) →
    decompQuot (GLPair 2) (HeckeCoset.rep D) :=
  fun i => ⟦⟨σ * i.out, (GLPair 2).H.mul_mem σ.prop (SetLike.coe_mem _)⟩⟧

private lemma leftMulQuot_injective (D : HeckeCoset (GLPair 2)) (σ : (GLPair 2).H) :
    Function.Injective (leftMulQuot D σ) := by
  intro i₁ i₂ h; simp only [leftMulQuot] at h
  by_contra hne
  have h_K := QuotientGroup.leftRel_apply.mp (Quotient.exact h)
  rw [Subgroup.mem_subgroupOf] at h_K
  -- Extract H-membership from K-membership
  have h_mem : (HeckeCoset.rep D : GL _ ℚ)⁻¹ *
      ((i₁.out : GL _ ℚ)⁻¹ * (i₂.out : GL _ ℚ)) *
      (HeckeCoset.rep D : GL _ ℚ) ∈ (GLPair 2).H := by
    have := h_K
    rw [Subgroup.mem_pointwise_smul_iff_inv_smul_mem, ConjAct.smul_def] at this
    simp only [ConjAct.ofConjAct_toConjAct, map_inv, inv_inv] at this
    convert this using 1
    simp only [Subgroup.coe_mul, Subgroup.coe_inv]; group
  exact decompQuot_coset_diff (GLPair 2) (HeckeCoset.rep D) i₁ i₂ hne
    (leftCoset_eq_of_not_disjoint (GLPair 2).H _ _ (by
      rw [Set.not_disjoint_iff]
      refine ⟨(i₂.out : GL _ ℚ) * (HeckeCoset.rep D : GL _ ℚ), ?_, ?_⟩
      · rw [smul_eq_singleton_mul]
        exact ⟨_, rfl, _, h_mem, by group⟩
      · rw [smul_eq_singleton_mul]
        exact ⟨_, rfl, 1, (GLPair 2).H.one_mem, by group⟩))

/-- Left multiplication by an H-element on `decompQuot` is an equivalence
    (injective endomorphism of a finite type). -/
private noncomputable def leftMulEquiv (D : HeckeCoset (GLPair 2)) (σ : (GLPair 2).H) :
    decompQuot (GLPair 2) (HeckeCoset.rep D) ≃
    decompQuot (GLPair 2) (HeckeCoset.rep D) :=
  Equiv.ofBijective _ ⟨leftMulQuot_injective D σ,
    Finite.surjective_of_injective (leftMulQuot_injective D σ)⟩

/-- Distribute the ℚ-slash over a heckeSlash sum: each summand gets slashed
    individually. -/
private lemma heckeSlash_slash (k : ℤ) (D : HeckeCoset (GLPair 2)) (f : ℍ → ℂ)
    (g : GL (Fin 2) ℚ) : (heckeSlash k D f) ∣[k] g =
    ∑ i : decompQuot (GLPair 2) (HeckeCoset.rep D), (f ∣[k] tRep D i) ∣[k] g := by
  simp only [heckeSlash]
  induction Finset.univ (α := decompQuot (GLPair 2) (HeckeCoset.rep D))
      using Finset.cons_induction with
  | empty => simp [SlashAction.zero_slash]
  | cons a s has ih => simp [Finset.sum_cons, SlashAction.add_slash, ih]

/-- Left multiplication by a transposed H-element preserves the slash action
    under Γ-invariance: `f ∣[k] (hᵀ * g) = f ∣[k] g` when `h ∈ H`. -/
private lemma slash_left_H_transpose_mul (k : ℤ) (f : ℍ → ℂ)
    (hf : ∀ γ ∈ 𝒮ℒ, f ∣[k] γ = f) (h : GL (Fin 2) ℚ)
    (hh : h ∈ (GLPair 2).H) (g : GL (Fin 2) ℚ) :
    f ∣[k] ((GLTransposeEquiv 2 h).unop * g) = f ∣[k] g := by
  change f ∣[k] glMap ((GLTransposeEquiv 2 h).unop * g) =
    f ∣[k] glMap g
  rw [map_mul, SlashAction.slash_mul]; congr 1
  exact hf _ (glMap_mem_SL ⟨_, GL_transpose_mem_SLnZ 2 hh⟩)

/-- The K-correction element `δ⁻¹ * (q.out⁻¹ * h₁) * δ * h₂` lies in `H`.
    This extracts the common membership proof used in both `slash_tRep_of_mem`
    and `slash_tRep_product_eq`. -/
private lemma h_coset_mem_H (D : HeckeCoset (GLPair 2))
    (q : decompQuot (GLPair 2) (HeckeCoset.rep D)) (h₁ : GL (Fin 2) ℚ)
    (hh₁ : h₁ ∈ (GLPair 2).H)
    (h₂ : GL (Fin 2) ℚ) (hh₂ : h₂ ∈ (GLPair 2).H)
    (hq : (⟦q.out⟧ : decompQuot (GLPair 2) (HeckeCoset.rep D)) = ⟦⟨h₁, hh₁⟩⟧) :
    ((HeckeCoset.rep D : GL _ ℚ)⁻¹ * ((q.out : GL _ ℚ)⁻¹ * h₁) *
      (HeckeCoset.rep D : GL _ ℚ) * h₂) ∈ (GLPair 2).H := by
  have h_K := QuotientGroup.leftRel_apply.mp (Quotient.exact hq)
  rw [Subgroup.mem_subgroupOf] at h_K
  rw [Subgroup.mem_pointwise_smul_iff_inv_smul_mem, ConjAct.smul_def] at h_K
  simp only [ConjAct.ofConjAct_toConjAct, map_inv, inv_inv] at h_K
  exact (GLPair 2).H.mul_mem (by convert h_K using 1) hh₂

/-- The transpose round-trip: `(h₁ * δ * h₂)ᵀ = h_cosetᵀ * (q.out * δ)ᵀ`
    where `h_coset = δ⁻¹ * (q.out⁻¹ * h₁) * δ * h₂`. -/
private lemma transpose_decomp_eq (D : HeckeCoset (GLPair 2))
    (q : decompQuot (GLPair 2) (HeckeCoset.rep D))
    (h₁ h₂ : GL (Fin 2) ℚ) :
    (GLTransposeEquiv 2 (h₁ * (HeckeCoset.rep D : GL _ ℚ) * h₂)).unop =
    (GLTransposeEquiv 2 ((HeckeCoset.rep D : GL _ ℚ)⁻¹ *
      ((q.out : GL _ ℚ)⁻¹ * h₁) *
      (HeckeCoset.rep D : GL _ ℚ) * h₂)).unop * tRep D q := by
  simp only [tRep]
  rw [← MulOpposite.unop_mul, ← (GLTransposeEquiv 2).map_mul]
  apply congrArg MulOpposite.unop
  apply congrArg (GLTransposeEquiv 2).toFun
  simp only [mul_assoc, mul_inv_cancel_left]

/-- Slashing by a transpose of `h₁ * delta * h₂` with `h₁, h₂ in H` equals slashing
    by `tRep D ⟦h₁⟧`, using Gamma-invariance to absorb the `H`-elements. -/
lemma slash_tRep_of_mem (k : ℤ) (D : HeckeCoset (GLPair 2))
    (h₁ h₂ : GL (Fin 2) ℚ) (hh₁ : h₁ ∈ (GLPair 2).H)
    (hh₂ : h₂ ∈ (GLPair 2).H) (f : ℍ → ℂ)
    (hf : ∀ γ ∈ 𝒮ℒ, f ∣[k] γ = f) :
    f ∣[k] (GLTransposeEquiv 2
      (h₁ * (HeckeCoset.rep D : GL (Fin 2) ℚ) * h₂)).unop =
    f ∣[k] tRep D ⟦⟨h₁, hh₁⟩⟧ := by
  set q : decompQuot (GLPair 2) (HeckeCoset.rep D) := ⟦⟨h₁, hh₁⟩⟧
  rw [transpose_decomp_eq D q h₁ h₂]
  exact slash_left_H_transpose_mul k f hf _
    (h_coset_mem_H D q h₁ hh₁ h₂ hh₂ (Quotient.out_eq _)) _

/-- Anti-homomorphism: `tRep D i * σ_Q = (σ_Qᵀ * i.out * δ)ᵀ`. -/
private lemma tRep_mul_eq_transpose (D : HeckeCoset (GLPair 2))
    (i : decompQuot (GLPair 2) (HeckeCoset.rep D)) (σ_Q : GL (Fin 2) ℚ) :
    tRep D i * σ_Q = (GLTransposeEquiv 2
      ((GLTransposeEquiv 2 σ_Q).unop * (i.out : GL _ ℚ) *
        (HeckeCoset.rep D : GL _ ℚ))).unop := by
  change (GLTransposeEquiv 2 _).unop * σ_Q = _
  conv_lhs =>
    rw [show σ_Q = (GLTransposeEquiv 2
      (GLTransposeEquiv 2 σ_Q).unop).unop from
      (GL_transposeEquiv_involutive 2 σ_Q).symm,
      ← MulOpposite.unop_mul, ← (GLTransposeEquiv 2).map_mul]
  rw [show (GLTransposeEquiv 2 σ_Q).unop * (i.out : GL _ ℚ) *
      (HeckeCoset.rep D : GL _ ℚ) =
      (GLTransposeEquiv 2 σ_Q).unop *
      ((i.out : GL _ ℚ) * (HeckeCoset.rep D : GL _ ℚ)) from by group]

/-- The Hecke slash action preserves slash-invariance under `SL₂(Z)` (Shimura Prop 3.30). -/
lemma heckeSlash_slash_invariant (k : ℤ) (D : HeckeCoset (GLPair 2)) (f : ℍ → ℂ)
    (hf : ∀ γ ∈ 𝒮ℒ, f ∣[k] γ = f) (γ : GL (Fin 2) ℝ) (hγ : γ ∈ 𝒮ℒ) :
    (heckeSlash k D f) ∣[k] γ = heckeSlash k D f := by
  obtain ⟨σ_Q, hσ_Q, hγ_eq⟩ := mem_SL_exists_H hγ
  set σ_QT : (GLPair 2).H :=
    ⟨(GLTransposeEquiv 2 σ_Q).unop, GL_transpose_mem_SLnZ 2 hσ_Q⟩
  set π := leftMulEquiv D σ_QT
  -- Each term: slash_mul then transpose round-trip via slash_tRep_of_mem
  have h_perm : ∀ i, (f ∣[k] tRep D i) ∣[k] (σ_Q : GL _ ℚ) =
      f ∣[k] tRep D (π i) := by
    intro i
    -- slash_mul for the ℚ-instance: (f ∣[k] a) ∣[k] b = f ∣[k] (a * b)
    rw [(SlashAction.slash_mul k (tRep D i) σ_Q f).symm,
      tRep_mul_eq_transpose,
      show σ_QT.val * ↑i.out * (HeckeCoset.rep D : GL _ ℚ) =
        σ_QT.val * ↑i.out * (HeckeCoset.rep D : GL _ ℚ) * 1 from
        (mul_one _).symm,
      slash_tRep_of_mem k D _ 1
        ((GLPair 2).H.mul_mem σ_QT.prop (SetLike.coe_mem _))
        (GLPair 2).H.one_mem f hf]; rfl
  -- Combine: γ = glMap σ_Q, distribute, rewrite each term, reindex by π
  have hγ_σ : (heckeSlash k D f) ∣[k] γ = (heckeSlash k D f) ∣[k] σ_Q := by
    change _ = (heckeSlash k D f) ∣[k] glMap σ_Q; rw [hγ_eq]
  rw [hγ_σ, heckeSlash_slash,
    Finset.sum_congr rfl (fun i _ => h_perm i),
    Fintype.sum_equiv π _ (fun i => f ∣[k] tRep D i) (fun _ => rfl)]
  rfl

/-- The `SlashInvariantForm` obtained by applying a Hecke operator. -/
noncomputable def heckeSlashInvariant (k : ℤ) (D : HeckeCoset (GLPair 2))
    (f : SlashInvariantForm 𝒮ℒ k) : SlashInvariantForm 𝒮ℒ k where
  toFun := heckeSlash k D f
  slash_action_eq' γ hγ := heckeSlash_slash_invariant k D f
    (fun γ' hγ' => f.slash_action_eq' γ' hγ') γ hγ

/-- The transpose anti-homomorphism applied to the product of two coset reps:
    `tRep D₂ j * tRep D₁ i = (σᵢδ₁ · σⱼδ₂)ᵀ`. -/
lemma tRep_mul_anti (D₁ D₂ : HeckeCoset (GLPair 2))
    (i : decompQuot (GLPair 2) (HeckeCoset.rep D₁))
    (j : decompQuot (GLPair 2) (HeckeCoset.rep D₂)) :
    tRep D₂ j * tRep D₁ i =
    (GLTransposeEquiv 2
      ((i.out : GL _ ℚ) * (HeckeCoset.rep D₁ : GL _ ℚ) *
       ((j.out : GL _ ℚ) * (HeckeCoset.rep D₂ : GL _ ℚ)))).unop := by
  change (GLTransposeEquiv 2 _).unop * (GLTransposeEquiv 2 _).unop = _
  rw [← MulOpposite.unop_mul, ← (GLTransposeEquiv 2).map_mul]

/-- Key term-equality: the product `tRep D₂ j * tRep D₁ i` equals
    `f ∣[k] tRep(D, q)` for some coset representative `q` in
    `decompQuot(mulMap(i,j))`, up to Γ-invariance. -/
private lemma slash_tRep_product_eq (k : ℤ) (D₁ D₂ : HeckeCoset (GLPair 2))
    (i : decompQuot (GLPair 2) (HeckeCoset.rep D₁))
    (j : decompQuot (GLPair 2) (HeckeCoset.rep D₂))
    (f : ℍ → ℂ) (hf : ∀ γ ∈ 𝒮ℒ, f ∣[k] γ = f) :
    ∃ q : decompQuot (GLPair 2)
      (HeckeCoset.rep (mulMap (GLPair 2) (HeckeCoset.rep D₁) (HeckeCoset.rep D₂) (i, j))),
    f ∣[k] (tRep D₂ j * tRep D₁ i) =
    f ∣[k] tRep (mulMap (GLPair 2) (HeckeCoset.rep D₁) (HeckeCoset.rep D₂) (i, j)) q := by
  set D := mulMap (GLPair 2) (HeckeCoset.rep D₁) (HeckeCoset.rep D₂) (i, j)
  have hg_mem : (i.out : GL (Fin 2) ℚ) * (HeckeCoset.rep D₁ : GL _ ℚ) *
      ((j.out : GL _ ℚ) * (HeckeCoset.rep D₂ : GL _ ℚ)) ∈ HeckeCoset.toSet D := by
    change _ ∈ HeckeCoset.toSet (⟦⟨_, _⟩⟧ : HeckeCoset (GLPair 2))
    simp only [HeckeCoset.toSet_mk]; exact DoubleCoset.mem_doubleCoset_self _ _ _
  rw [HeckeCoset.toSet_eq_rep, DoubleCoset.mem_doubleCoset] at hg_mem
  obtain ⟨h₁, hh₁, h₂, hh₂, hg_eq⟩ := hg_mem
  refine ⟨⟦⟨h₁, hh₁⟩⟧, ?_⟩
  rw [tRep_mul_anti, hg_eq]
  exact slash_tRep_of_mem k D h₁ h₂ hh₁ hh₂ f hf

end SlashInvariance

end HeckeRing.GL2
