/-
Copyright (c) 2026 Christopher Albert. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Albert
-/

module

public import Mathlib.RingTheory.Valuation.Basic
public import Mathlib.RingTheory.Valuation.ValuationSubring
public import Mathlib.RingTheory.LocalRing.ResidueField.Basic
public import Mathlib.RingTheory.Algebraic.Basic
public import Mathlib.RingTheory.IntegralClosure.IsIntegral.Basic
public import Mathlib.FieldTheory.IntermediateField.Adjoin.Defs


/-!
Algebraicity of the divisorial residue field from integral affine models.
-/

@[expose] public section

open IsLocalRing
noncomputable section
universe u v

namespace Stafford38.Geometry.DivisorialVisibleFrameStage4

theorem stage4_residueField_isAlgebraic_of_isIntegral
    {k K : Type u} [Field k] [Field K] [Algebra k K]
    (A : Subalgebra k K) (p : Ideal A)
    (V : ValuationSubring K) [IsLocalRing V.toSubring]
    [Algebra k V.toSubring] [IsScalarTower k V.toSubring K]
    (hAV : ∀ a : A, (a : K) ∈ V.toSubring)
    (hp : ∀ a : A, (⟨a, hAV a⟩ : V.toSubring) ∈ maximalIdeal V.toSubring ↔ a ∈ p)
    (hsurj : ∀ z : ResidueField V.toSubring, ∃ (a b : A), b ∉ p ∧
      z = residue V.toSubring ⟨a, hAV a⟩ / residue V.toSubring ⟨b, hAV b⟩)
    {ι : Type v} (c : ι → K) (hc : ∀ i, c i ∈ A)
    (hint : ∀ a : A, IsIntegral (Algebra.adjoin k (Set.range c)) (a : K)) :
    Algebra.IsAlgebraic
      (IntermediateField.adjoin k (Set.range fun i => residue V.toSubring ⟨c i, hAV ⟨c i, hc i⟩⟩) :
        IntermediateField k (ResidueField V.toSubring))
      (ResidueField V.toSubring) := by
  let C : Subalgebra k K := Algebra.adjoin k (Set.range c)
  have hCA : C ≤ A := by
    apply Algebra.adjoin_le
    rintro z ⟨i, rfl⟩
    exact hc i
  let cV : C →+* V.toSubring :=
    RingHom.codRestrict C.val.toRingHom V.toSubring (fun z => hAV ⟨z, hCA z.property⟩)
  let ρ : V.toSubring →+* ResidueField V.toSubring := residue V.toSubring
  let φ : C →+* ResidueField V.toSubring := ρ.comp cV
  let L : IntermediateField k (ResidueField V.toSubring) :=
    IntermediateField.adjoin k (Set.range fun i => ρ ⟨c i, hAV ⟨c i, hc i⟩⟩)
  have hφL : ∀ z : C, φ z ∈ L := by
    intro z
    apply Algebra.adjoin_induction
      (p := fun x hx => φ ⟨x, hx⟩ ∈ L)
    · intro x hx
      rcases hx with ⟨i, rfl⟩
      exact IntermediateField.subset_adjoin k _ ⟨i, rfl⟩
    · intro a
      have hcV : cV (algebraMap k C a) = algebraMap k V.toSubring a := by
        apply Subtype.ext
        change (algebraMap k K) a =
          (algebraMap V.toSubring K) ((algebraMap k V.toSubring) a)
        exact IsScalarTower.algebraMap_apply k V.toSubring K a
      have hbase : φ (algebraMap k C a) =
          algebraMap k (ResidueField V.toSubring) a := by
        calc
          φ (algebraMap k C a) = ρ (algebraMap k V.toSubring a) := by
            simp only [φ, RingHom.comp_apply, hcV]
          _ = algebraMap k (ResidueField V.toSubring) a := by
            change residue V.toSubring (algebraMap k V.toSubring a) = _
            rw [← ResidueField.algebraMap_eq]
            exact (IsScalarTower.algebraMap_apply k V.toSubring
              (ResidueField V.toSubring) a).symm
      have hmem : φ (algebraMap k C a) ∈ L := by
        rw [hbase]
        exact L.algebraMap_mem a
      have harg : (⟨(algebraMap k K) a, C.algebraMap_mem a⟩ : C) = algebraMap k C a := by
        apply Subtype.ext
        rfl
      simpa [harg] using hmem
    · intro a b haC hbC ha hb
      change φ ((⟨a, haC⟩ : C) + ⟨b, hbC⟩) ∈ L
      rw [map_add]
      exact add_mem ha hb
    · intro a b haC hbC ha hb
      change φ ((⟨a, haC⟩ : C) * ⟨b, hbC⟩) ∈ L
      rw [map_mul]
      exact mul_mem ha hb
  let cL : C →+* L := φ.codRestrict L.toSubring hφL
  let : Algebra C V.toSubring := cV.toAlgebra
  let : Algebra C (ResidueField V.toSubring) := φ.toAlgebra
  let : IsScalarTower C V.toSubring K :=
    IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  let : IsScalarTower C V.toSubring (ResidueField V.toSubring) := by
    constructor
    intro x y z
    change ρ (cV x) * ρ y * z = ρ (cV x) * (ρ y * z)
    exact mul_assoc _ _ _
  let : IsScalarTower C C V.toSubring :=
    IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  let : IsScalarTower C C (ResidueField V.toSubring) :=
    IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  let : Algebra C L := cL.toAlgebra
  let : IsScalarTower C L (ResidueField V.toSubring) := by
    apply IsScalarTower.of_algebraMap_eq
    intro x
    rfl
  have hmap : ∀ a : A, IsIntegral C (ρ ⟨a, hAV a⟩) := by
    intro a
    let av : V.toSubring := ⟨a, hAV a⟩
    have haK : IsIntegral C (a : K) := by simpa [C] using hint a
    have haV : IsIntegral C av := by
      apply (isIntegral_algebraMap_iff (R := C) (A := V.toSubring)
        (B := K)).mp
      change IsIntegral C (a : K)
      exact haK
    let f : V.toSubring →ₐ[C] ResidueField V.toSubring :=
      { ρ with
        commutes' := by
          intro x
          rfl }
    exact IsIntegral.map f haV
  refine ⟨fun z => ?_⟩
  obtain ⟨a, b, hb, hz⟩ := hsurj z
  have ha := hmap a
  have hbin := hmap b
  have hbp : ρ ⟨b, hAV b⟩ ≠ 0 := by
    intro hzero
    have hnotmax : (⟨b, hAV b⟩ : V.toSubring) ∉ maximalIdeal V.toSubring := by
      intro hmem
      exact hb ((hp b).mp hmem)
    exact ((residue_ne_zero_iff_isUnit _).2
      ((notMem_maximalIdeal).1 hnotmax)) hzero
  have haL : IsIntegral L (ρ ⟨a, hAV a⟩) := IsIntegral.tower_top ha
  have hbL : IsIntegral L (ρ ⟨b, hAV b⟩) := IsIntegral.tower_top hbin
  have h_ainv : IsAlgebraic L (ρ ⟨a, hAV a⟩) := haL.isAlgebraic
  have h_binv : IsAlgebraic L (ρ ⟨b, hAV b⟩) := hbL.isAlgebraic
  rw [hz]
  exact h_ainv.mul h_binv.inv


private theorem isAlgebraic_over_larger_intermediateField
    {k E : Type*} [Field k] [Field E] [Algebra k E]
    (L M : IntermediateField k E) (hLM : L ≤ M) [Algebra.IsAlgebraic L E] :
    Algebra.IsAlgebraic M E := by
  let : Algebra L M := (IntermediateField.inclusion hLM).toAlgebra
  let : IsScalarTower L M E := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  exact ⟨fun z => (Algebra.IsAlgebraic.isAlgebraic z).extendScalars
    (IntermediateField.inclusion_injective hLM)⟩

theorem stage4'_isAlgebraic_of_normalized_column
    {k K : Type u} [Field k] [Field K]
    (V : ValuationSubring K) [IsLocalRing V.toSubring] [Algebra k V.toSubring]
    {r : ℕ} (y : Fin r → K) (j : Fin (r + 1)) (hj : j ≠ 0) (s₀ : K)
    (c : Fin (r + 1) → V.toSubring) (hc : ∀ a, (c a : K) = (Fin.cases 1 y a : K) * s₀)
    (hcj : c j = 1)
    (halg : Algebra.IsAlgebraic
      (IntermediateField.adjoin k (Set.range fun a => residue V.toSubring (c a)) :
        IntermediateField k (ResidueField V.toSubring)) (ResidueField V.toSubring))
    (s : K) (q : Fin (r + 1) → V.toSubring) (hq : ∀ a, (q a : K) = s * Fin.cases 1 y a)
    (hq1 : ∃ j', q j' = 1) (hq0 : ¬ IsUnit (q 0)) :
    Algebra.IsAlgebraic
      (IntermediateField.adjoin k
        (Set.range fun b : Fin r => residue V.toSubring (q (Fin.succ b))) :
        IntermediateField k (ResidueField V.toSubring))
      (ResidueField V.toSubring) := by
  classical
  let ρ : V.toSubring →+* ResidueField V.toSubring := residue V.toSubring
  let Lc : IntermediateField k (ResidueField V.toSubring) :=
    IntermediateField.adjoin k (Set.range fun a => ρ (c a))
  let Lq : IntermediateField k (ResidueField V.toSubring) :=
    IntermediateField.adjoin k (Set.range fun b : Fin r => ρ (q (Fin.succ b)))
  let lam : ResidueField V.toSubring := ρ (q j)
  have hcjK : (Fin.cases 1 y j : K) * s₀ = 1 := by
    have := congrArg (fun z : V.toSubring => (z : K)) hcj
    simpa [hc j] using this
  have hprodK (a : Fin (r + 1)) : (q a : K) = (q j : K) * (c a : K) := by
    rw [hq a, hq j, hc a]
    calc
      s * Fin.cases 1 y a = (s * Fin.cases 1 y a) * 1 := by rw [mul_one]
      _ = (s * Fin.cases 1 y a) * ((Fin.cases 1 y j) * s₀) := by rw [hcjK]
      _ = (s * Fin.cases 1 y j) * ((Fin.cases 1 y a) * s₀) := by ring
  have hprodV (a : Fin (r + 1)) : q a = q j * c a := by
    apply Subtype.ext
    exact hprodK a
  have hprod (a : Fin (r + 1)) : ρ (q a) = lam * ρ (c a) := by
    rw [hprodV a, map_mul]
  obtain ⟨j', hj'⟩ := hq1
  have hlam : lam ≠ 0 := by
    intro hzero
    have hqj' : IsUnit (q j') := by rw [hj']; exact isUnit_one
    have hnz : ρ (q j') ≠ 0 := (residue_ne_zero_iff_isUnit _).2 hqj'
    apply hnz
    rw [hprod j', hzero, zero_mul]
  obtain ⟨jt, hjt⟩ := Fin.exists_succ_eq_of_ne_zero hj
  have hlammem : lam ∈ Lq := by
    change ρ (q j) ∈ Lq
    rw [← hjt]
    exact IntermediateField.subset_adjoin k _ ⟨jt, rfl⟩
  have hq0res : ρ (q 0) = 0 := by
    by_contra hnz
    exact hq0 ((residue_ne_zero_iff_isUnit _).1 hnz)
  have hc0res : ρ (c 0) = 0 := by
    have h := hprod 0
    rw [hq0res] at h
    exact (mul_eq_zero.mp h.symm).resolve_left hlam
  have hctail (b : Fin r) : ρ (c (Fin.succ b)) = lam⁻¹ * ρ (q (Fin.succ b)) := by
    calc
      ρ (c (Fin.succ b)) = lam⁻¹ * (lam * ρ (c (Fin.succ b))) := by
        rw [← mul_assoc, inv_mul_cancel₀ hlam, one_mul]
      _ = lam⁻¹ * ρ (q (Fin.succ b)) := by rw [← hprod]
  have hcLq : ∀ a : Fin (r + 1), ρ (c a) ∈ Lq := by
    intro a
    refine Fin.cases ?_ (fun b => ?_) a
    · rw [hc0res]
      exact Lq.zero_mem
    · rw [hctail]
      exact Lq.mul_mem (Lq.inv_mem hlammem)
        (IntermediateField.subset_adjoin k _ ⟨b, rfl⟩)
  have hLcLq : Lc ≤ Lq := by
    intro z hz
    apply IntermediateField.adjoin_induction (F := k)
      (E := ResidueField V.toSubring)
      (s := Set.range fun a => ρ (c a))
      (p := fun x hx => x ∈ Lq)
    · intro x hx
      rcases hx with ⟨a, rfl⟩
      exact hcLq a
    · intro a
      exact Lq.algebraMap_mem a
    · intro a b _ _ ha hb
      simpa only [map_add] using Lq.add_mem ha hb
    · intro a _ ha
      simpa only [map_inv₀] using Lq.inv_mem ha
    · intro a b _ _ ha hb
      simpa only [map_mul] using Lq.mul_mem ha hb
    · exact hz
  exact isAlgebraic_over_larger_intermediateField Lc Lq hLcLq



end Stafford38.Geometry.DivisorialVisibleFrameStage4
