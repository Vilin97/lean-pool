/-
Copyright (c) 2026 Judith Ludwig, Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Judith Ludwig, Christian Merten
-/
import LeanPool.BruhatTits.Cartan.Existence
import LeanPool.BruhatTits.Utils.Misc
import Mathlib.Data.Fin.Tuple.Sort
import Mathlib.GroupTheory.DoubleCoset

open Module

/-!
# Uniqueness of the Cartan decomposition

Given `K` as the fraction field of a DVR `R` with uniformizer `ϖ`, the Cartan decomposition says
that any matrix `g ∈ GL(n,K)` can be written as a product `k₁ * diag * k₂`, where  `kᵢ ∈ GL(n,R)`
and `diag` is a diagonal matrix with entries decreasing powers of the uniformizer.

In this file we show that the diagonal matrix `diag` is unique, independently of the choice
of a uniformizer `ϖ`. More precisely, if
`k₁ * diag(ϖ, f) * k₂ = m₁ * diag(ϖ', f') * m₂` for two uniformizers `ϖ, ϖ'` and `f` and `f'` are
antitone, then `f = f' (see `cartan_decomposition_unique_uniformizer`).

A form more commonly seen in the literature is the following: `GL₂(K)` admits a decomposition
as a disjoint union of double cosets `GL₂(R) * diag * GL₂(R)` where `diag` is as above. For
completeness, this is stated as `iUnion₂_doset_cartanDiag_eq_univ` and
`disjoint_doset_cartanDiag_of_ne` below.
-/

variable {K : Type*} [Field K]
variable {R : Subring K}

local notation "v" => ValuationRing.valuation R K

variable {k : ℕ+}

open Matrix in
lemma cartanDiag_map_mul {ϖ : R} (hϖ : Irreducible ϖ) {u : Rˣ} (hϖ' : Irreducible (ϖ * u))
    (f : Fin k → ℤ) :
    cartanDiag (ϖ * u.val) hϖ' f =
      (GL.diagonal (fun i ↦ u ^ (f i)) : GL (Fin k) R) * cartanDiag ϖ hϖ f := by
  ext i j
  simp only [val_cartanDiag,
    GL.map, GL.val_diagonal, RingHom.mapMatrix_apply, Subring.coe_subtype,
    ZeroMemClass.coe_zero, diagonal_map, Subring.coe_zpow, Units.inv_eq_val_inv, coe_units_inv,
    Units.val_mul, mul_diagonal]
  by_cases hij : i = j
  · subst hij
    simp [mul_comm, mul_zpow]
  · rw [Matrix.diagonal_apply_ne _ hij, Matrix.diagonal_apply_ne _ hij]
    simp

variable [IsDiscreteValuationRing R] [IsFractionRing R K]

section

variable {ϖ : R} {hϖ : Irreducible ϖ}

lemma cartan_decomposition_unique'_aux (x a : GL (Fin k) R) (f f' : Fin k → ℤ)
    (hax : cartanDiag ϖ hϖ f * a * (cartanDiag ϖ hϖ f')⁻¹ = x) :
    ∃ σ : Equiv.Perm (Fin k), f ∘ σ = f' := by
  have hadetunit : IsUnit a.val.det := Matrix.isUnits_det_units a
  have hxdetunit : IsUnit x.val.det := Matrix.isUnits_det_units x
  have : (cartanDiag ϖ hϖ f * a * (cartanDiag ϖ hϖ f')⁻¹).val.det = x.val.det := by
    rw [hax]
    simp
  simp only [«GL».map, RingHom.mapMatrix_apply, Subring.coe_subtype, Units.inv_eq_val_inv,
    Matrix.coe_units_inv, Units.val_mul, val_cartanDiag, Matrix.det_mul, Matrix.det_diagonal,
    Subring.coe_det, Matrix.det_nonsing_inv, Ring.inverse_eq_inv'] at this
  apply congrArg v at this
  simp only [map_mul] at this
  rw [valuation_isUnit x.val.det hxdetunit, valuation_isUnit a.val.det hadetunit] at this
  simp only [mul_one] at this
  rw [← map_mul, ← Finset.prod_inv_distrib, ← Finset.prod_mul_distrib] at this
  simp_rw [← zpow_neg] at this
  have hϖnezero : ϖ.val ≠ 0 := by
    simp only [ne_eq, ZeroMemClass.coe_eq_zero]
    exact hϖ.ne_zero
  have hsumzero' : Finset.univ.sum (fun i ↦ f i - f' i) = 0 := by
    rw [← valuation_irreducible_zpow_eq_one_iff (hϖ := hϖ)]
    rw [← Finset.prod_zpow_eq_zpow_sum (ha := hϖnezero)]
    rw [← this]
    congr
    ext i
    rw [← zpow_add₀ hϖnezero]
    rfl
  have : ∃ (σ : Equiv.Perm (Fin k)),
      IsUnit ((Equiv.Perm.sign σ) * Finset.univ.prod (fun i ↦ a (σ i) i)) := by
    rw [Matrix.det_apply'] at hadetunit
    obtain ⟨σ, _, hσ⟩ := IsLocalRing.exists_isUnit_of_isUnit_sum hadetunit
    use σ
  have : ∃ (σ : Equiv.Perm (Fin k)), ∀ i, IsUnit (a (σ i) i) := by
    obtain ⟨σ, hσ⟩ := this
    rw [IsUnit.mul_iff] at hσ
    simp_rw [IsUnit.prod_iff] at hσ
    use σ
    intro i
    exact hσ.right i (Finset.mem_univ i)
  obtain ⟨σ, hσ⟩ := this
  have hxij (i j : Fin k) :
      x.val i j = ϖ.val ^ (f i - f' j) * a.val i j := by
    change R.subtype (x.val i j) = _
    rw [← GL.map_apply (f := R.subtype) i j x, ← hax, cartanDiag_inv]
    simp only [GL.map, RingHom.mapMatrix_apply, Subring.coe_subtype, Units.inv_eq_val_inv,
      Matrix.coe_units_inv, Units.val_mul, val_cartanDiag, zpow_neg, Matrix.mul_diagonal,
      Matrix.diagonal_mul, Matrix.map_apply, zpow_sub₀ hϖnezero]
    group
  have hgezero (i : Fin k) : f (σ i) - f' i ≥ 0 := by
    rw [← irreducible_zpow_mem_subring_iff (hϖ := hϖ)]
    have := congrArg v (hxij (σ i) i)
    simp only [map_mul] at this
    rw [valuation_isUnit (a.val (σ i) i) (hσ i)] at this
    simp only [mul_one] at this
    rw [mem_subring_iff_integer, ← this, ← mem_subring_iff_integer]
    exact (x.val (σ i) i).property
  have hsumzero : Finset.univ.sum (fun i ↦ f (σ i) - f' i) = 0 := by
    rw [Finset.sum_sub_distrib, Equiv.Perm.sum_comp]
    · rw [← Finset.sum_sub_distrib]
      exact hsumzero'
    · simp
  have hzero : ∀ i ∈ Finset.univ, f (σ i) - f' i = 0 := by
    rw [← Finset.sum_eq_zero_iff_of_nonneg]
    · exact hsumzero
    · intro i _
      exact hgezero i
  use σ
  ext i
  simpa using Int.eq_of_sub_eq_zero (hzero i (Finset.mem_univ i))

theorem cartan_decomposition_unique' {k₁ k₂ k₁' k₂' : GL (Fin k) R}
    {f f' : Fin k → ℤ}
    (h : k₁ * cartanDiag ϖ hϖ f * k₂ = k₁' * cartanDiag ϖ hϖ f' * k₂') :
    ∃ σ : Equiv.Perm (Fin k), f ∘ σ = f' := by
  let a : GL (Fin k) R := k₂ * k₂'⁻¹
  let x : GL (Fin k) R := k₁⁻¹ * k₁'
  apply cartan_decomposition_unique'_aux x a f f' (ϖ := ϖ) (hϖ := hϖ)
  simp only [x, a]
  rw [GL.map_mul, GL.map_mul, ← mul_assoc]
  calc _ =
    (GL.map R.subtype k₁)⁻¹ * (k₁ * cartanDiag ϖ hϖ f * k₂) * k₂'⁻¹ * (cartanDiag ϖ hϖ f')⁻¹
      := by group
    _ = (GL.map R.subtype k₁)⁻¹ * k₁' * cartanDiag ϖ hϖ f' * k₂' * k₂'⁻¹ * (cartanDiag ϖ hϖ f')⁻¹
      := by rw [h]; group
    _ = k₁⁻¹ * k₁' * cartanDiag ϖ hϖ f' * k₂' * (GL.map R.subtype k₂')⁻¹ * (cartanDiag ϖ hϖ f')⁻¹
      := by rw [GL.map_inv, GL.map_inv]
    _ = k₁⁻¹ * k₁' := by group

lemma eq_of_twist_eq_of_antitone (f g : Fin k → ℤ) (σ : Equiv.Perm (Fin k))
    (hf : Antitone f) (hg : Antitone g) (h : f = g ∘ σ) :
    f = g := by
  subst h
  have : g = g ∘ Equiv.refl _ := rfl
  rw [this] at hg
  nth_rw 2 [this]
  exact Tuple.unique_antitone hf hg

/-- The cartan decomposition is unique. -/
theorem cartan_decomposition_unique {k₁ k₂ k₁' k₂' : GL (Fin k) R}
    {f f' : Fin k → ℤ} (hf : Antitone f) (hf' : Antitone f')
    (h : k₁ * cartanDiag ϖ hϖ f * k₂ = k₁' * cartanDiag ϖ hϖ f' * k₂') :
    f = f' := by
  obtain ⟨σ, hσ⟩ := cartan_decomposition_unique' h
  exact (eq_of_twist_eq_of_antitone f' f σ hf' hf hσ.symm).symm

/-- `GL₂` is the union of the double cosets `GL₂(R) * D * GL₂(R)` where `D` runs through
all diagonal matrices with entries of the form `ϖ ^ n` with descending `n`.
This is a disjoint union (see `disjoint_doset_cartanDiag_of_ne`). -/
lemma iUnion₂_doset_cartanDiag_eq_univ : ⋃ (f : Fin k → ℤ) (_ : Antitone f),
    DoubleCoset.doubleCoset (cartanDiag ϖ hϖ f)
      (Set.range <| GL.map R.subtype)
      (Set.range <| GL.map R.subtype) = Set.univ := by
  classical
  rw [Set.iUnion₂_eq_univ_iff]
  intro g
  obtain ⟨k₁, k₂, f, hf, h⟩ := cartan_decomposition' ϖ hϖ g
  use f, hf
  rw [DoubleCoset.mem_doubleCoset]
  use k₁, ⟨k₁, rfl⟩, k₂, ⟨k₂, rfl⟩, h.symm

open scoped Function in
/-- The double cosets `GL₂(R) * D * GL₂(R)`, where `D` runs through
all diagonal matrices with entries of the form `ϖ ^ n` with descending `n`, are pairwise
disjoint. -/
lemma disjoint_doset_cartanDiag_of_ne :
    Pairwise (Disjoint on fun f : { f : Fin k → ℤ | Antitone f } ↦
      DoubleCoset.doubleCoset (cartanDiag ϖ hϖ f.1) (Set.range <| GL.map R.subtype)
        (Set.range <| GL.map R.subtype)) := by
  intro ⟨f, hf⟩ ⟨g, hg⟩ hfg
  simp only [Function.onFun, Set.disjoint_left]
  intro u hu hu'
  rw [DoubleCoset.mem_doubleCoset] at hu hu'
  obtain ⟨-, ⟨k₁, rfl⟩, -, ⟨k₂, rfl⟩, h⟩ := hu
  obtain ⟨-, ⟨m₁, rfl⟩, -, ⟨m₂, rfl⟩, h'⟩ := hu'
  apply hfg
  rw [h] at h'
  ext : 1
  exact cartan_decomposition_unique hf hg h'

end

/-- The Cartan decomposition is unique, independent of the choice of a uniformizer. -/
theorem cartan_decomposition_unique_uniformizer
    {ϖ ϖ' : R} (hϖ : Irreducible ϖ) (hϖ' : Irreducible ϖ')
    {k₁ k₂ k₁' k₂' : GL (Fin k) R}
    {f f' : Fin k → ℤ} (hf : Antitone f) (hf' : Antitone f')
    (h : k₁ * cartanDiag ϖ hϖ f * k₂ = k₁' * cartanDiag ϖ' hϖ' f' * k₂') :
    f = f' := by
  obtain ⟨u, rfl⟩ := IsDiscreteValuationRing.associated_of_irreducible R hϖ hϖ'
  rw [cartanDiag_map_mul hϖ hϖ', ← mul_assoc, ← GL.map_mul] at h
  exact cartan_decomposition_unique hf hf' h
